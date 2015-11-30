import algebra.relation
open relation
open eq eq.ops

structure setoido :=
  (carrier : Type)
  (r : carrier → carrier → Prop)
  (iseqv : equivalence r)

attribute setoido.carrier [coercion]

namespace setoido
  variable {A : setoido}

  theorem refl [refl] {a : A} : @setoido.r A a a :=
  and.elim_left (setoido.iseqv A) _

  theorem symm [symm] {a b : A} : @setoido.r A a b → @setoido.r A b a :=
  and.elim_left (and.elim_right (setoido.iseqv A)) _ _

  theorem trans [trans] {a b c : A} : @setoido.r A a b → @setoido.r A b c → @setoido.r A a c :=
  and.elim_right (and.elim_right (setoido.iseqv A)) _ _ _

  namespace ops
    notation H `⁻¹` := symm H
    notation H1 ⬝ H2 := trans H1 H2
    notation H1 ▸ H2 := subst H1 H2
    notation H1 ▹ H2 := eq.rec H2 H1
  end ops

end setoido

structure setoido_map (A B : setoido) :=
  (map : A → B)
  (preserve_eq : ∀ {x y : A}, !setoido.r x y → !setoido.r (map x) (map y))

namespace setoido_map
  definition setoido_map_eq {A B : setoido} (f g : setoido_map A B) : Prop
    := setoido_map.map f = setoido_map.map g

  axiom equal {A B : setoido} {f g : setoido_map A B} :
    setoido_map_eq f g → f = g

end setoido_map

structure category [class] :=
  (obj : Type)
  (hom : obj → obj → Type)
  (id : ∀ {a : obj}, hom a a)
  (comp : ∀ {a b c : obj}, hom b c → hom a b → hom a c)
  (assoc : ∀ {a b c d : obj} {f : hom a b} {g : hom b c} {h : hom c d}, comp (comp h g) f = comp h (comp g f))
  (id_left : ∀ {a b : obj} {f : hom a b}, comp (@id b) f = f)
  (id_right : ∀ {a b : obj} {f : hom a b}, comp f (@id a) = f)

namespace category
  variable {C : category}

  definition dom {a b : @obj C} (f : hom a b) : @obj C := a
  definition cod {a b : @obj C} (f : hom a b) : @obj C := b

  notation g `∘[` C `]` f := @comp C _ _ _ g f

  infixr [parsing_only] `⟶`:25 := hom

  structure iso (a b : @obj C) :=
    (mapr : hom a b)
    (mapl : hom b a)
    (isorl : (mapr ∘[C] mapl) = @id C b)
    (isolr : (mapl ∘[C] mapr) = @id C a)

  notation a `≅[` C `]` b := @iso C a b
  notation a `≅` b := @iso _ a b

  definition op [instance] (C : category) : category := category.mk
    (@obj C)
    (λa b, @hom C b a)
    (@id C)
    (λa b c g f, comp f g)
    (λa b c d f g h, symm !assoc)
    (λa b f, id_right)
    (λa b f, id_left)

  definition Types [instance] : category := category.mk
    Type
    (λa b, a → b)
    (λa x, x)
    (λa b c f g x, f (g x))
    (λa b c d f g h, rfl)
    (λa b f, funext (λx, rfl))
    (λa b f, funext (λx, rfl))

  definition Setoids [instance] : category := category.mk
    setoido
    setoido_map
    (λa, setoido_map.mk (λx, x) (λx y r, r))
    (λa b c g f, setoido_map.mk
      (λx, setoido_map.map g (setoido_map.map f x))
      (λx y xy, setoido_map.preserve_eq g (setoido_map.preserve_eq f xy)))
    (λa b c d f g h, setoido_map.equal rfl)
    (λa b f, setoido_map.equal rfl)
    (λa b f, setoido_map.equal rfl)

end category
open category

structure functor (C : category) (D : category) :=
  (fobj : @obj C → @obj D)
  (fmap : ∀ {a b : @obj C}, @hom C a b → @hom D (fobj a) (fobj b))
  (preserve_id : ∀ {a : @obj C}, fmap (@id C a) = @id D (fobj a))
  (preserve_comp : ∀ {a b c : @obj C} {g : @hom C b c} {f : @hom C a b},
    fmap (g ∘[C] f) = (fmap g ∘[D] fmap f))

namespace functor
  variables {C D E : category}

  definition functor_comp (G : functor D E) (F : functor C D) : functor C E :=
    functor.mk
      (λx, fobj G (fobj F x))
      (λa b f, fmap G (fmap F f))
      (λa, calc
        fmap G (fmap F (@id C a)) = fmap G (@id D (fobj F a)) : preserve_id F
        ... = @id E (fobj G (fobj F a)) : preserve_id G)
      (λa b c g f, calc
        fmap G (fmap F (g ∘[C] f)) = fmap G (fmap F g ∘[D] fmap F f) : preserve_comp F
        ... = (fmap G (fmap F g) ∘[E] fmap G (fmap F f)) : preserve_comp G)

  notation G `∘f` F := functor_comp G F

  definition functor_id : functor C C :=
    functor.mk
      (λx, x)
      (λa b f, f)
      (λa, rfl)
      (λa b c g f, rfl)

  inductive eqArrow {a b : @obj C} (f : @hom C a b) : ∀ {x y : @obj C}, @hom C x y → Type :=
  | arr : ∀ {g : @hom C a b}, f = g → eqArrow f g

  axiom functor_eq {C D : category} (F G : functor C D) :
    (∀ {a b : @obj C} (f : @hom C a b), eqArrow (fmap F f) (fmap G f)) → F = G

end functor
open functor

definition Cat : category :=
  category.mk
    category
    functor
    @functor_id
    @functor_comp
    (λa b c d F G H, functor_eq _ _ (λa b f, !eqArrow.arr (calc
      fmap (H ∘f (G ∘f F)) f = fmap H (fmap G (fmap F f)) : rfl
      ... = fmap ((H ∘f G) ∘f F) f : rfl)))
    (λa b F, functor_eq _ _ (λa b f, !eqArrow.arr rfl))
    (λa b F, functor_eq _ _ (λa b f, !eqArrow.arr rfl))

structure natrans {C D : category} (F G : functor C D) :=
  (component : ∀ (x : @obj C), @hom D (fobj F x) (fobj G x))
  (naturality : ∀ {a b : @obj C} {f : @hom C a b},
    (component b ∘[D] fmap F f) = (fmap G f ∘[D] component a))

namespace natrans
  variables {C D : category} {F G H : functor C D}
  notation F `⇒` G := natrans F G

  definition natrans_comp (ε : G ⇒ H) (η : F ⇒ G) : F ⇒ H :=
    natrans.mk
      (λx, (component ε x ∘[D] component η x))
      (λa b f, calc
        ((component ε b ∘[D] component η b) ∘[D] fmap F f) = (component ε b ∘[D] (component η b ∘[D] fmap F f)) : assoc
        ... = (component ε b ∘[D] (fmap G f ∘[D] component η a)) : naturality η
        ... = ((component ε b ∘[D] fmap G f) ∘[D] component η a) : assoc
        ... = ((fmap H f ∘[D] component ε a) ∘[D] component η a) : naturality ε
        ... = (fmap H f ∘[D] (component ε a ∘[D] component η a)) : assoc)

  definition natrans_id : F ⇒ F :=
    natrans.mk
      (λx, @id D (fobj F x))
      (λa b f, calc
        (@id D (fobj F b) ∘[D] fmap F f) = fmap F f : @id_left
        ... = (fmap F f ∘[D] @id D (fobj F a)) : @id_right)

  axiom natrans_eq {C D : category} {F G : functor C D} (α β : F ⇒ G) :
    (∀ x, eqArrow (component α x) (component β x)) → α = β

end natrans
open natrans

definition homfunctor (C : category) (r : @obj C) : functor (op C) Setoids :=
  functor.mk
    (λx, setoido.mk (@hom C x r) (λf g, f = g)
      (mk_equivalence _ refl (λx y, symm) (λx y z, trans)))
    (λa b f, setoido_map.mk (λk, k ∘[C] f) (λx y xy, xy ▸ rfl))
    (λa, setoido_map.equal (funext (λx, id_right)))
    (λa b c g f, setoido_map.equal (funext (λx, symm !assoc)))

definition homnat (C : category) {a b : @obj C} (f : @hom C a b) : (homfunctor C a) ⇒ (homfunctor C b) :=
  natrans.mk
    (λx, setoido_map.mk (λu, f ∘[C] u) (λx y xy, xy ▸ rfl))
    (λa b f, setoido_map.equal (funext (λx, symm !assoc)))

definition funcat (C D : category) : category :=
  category.mk
    (functor C D)
    natrans
    (λx, natrans_id)
    (λa b c, natrans_comp)
    (λa b c d f g h, natrans_eq _ _ (λx, eqArrow.arr assoc))
    (λa b f, natrans_eq _ _ (λx, eqArrow.arr id_left))
    (λa b f, natrans_eq _ _ (λx, eqArrow.arr id_right))

notation `[` C `,` D `]` := funcat C D
notation `PSh[` C `]` := [ op C, Setoids ]

definition yoneda (C : category) : functor C PSh[C] :=
  functor.mk
    (λx, homfunctor C x)
    (λa b f, homnat C f)
    (λa, natrans_eq _ _ (λx, !eqArrow.arr (setoido_map.equal (funext (λu, id_left)))))
    (λa b d g f, natrans_eq _ _ (λx, !eqArrow.arr (setoido_map.equal (funext (λu, assoc)))))

lemma Yoneda (C : category) (F : functor (op C) Setoids) (r : @obj C) :
  @hom PSh[C] (fobj (yoneda C) r) F ≅[Types] setoido.carrier (fobj F r)
:= iso.mk
  (λα, setoido_map.map (component α r) (@id C r))
  (λx, natrans.mk
    (λu, setoido_map.mk (λf, setoido_map.map (fmap F f) x) (λx y xy, xy ▸ setoido.refl))
    (λa b f, setoido_map.equal (funext (λt, calc
      setoido_map.map (fmap F (t ∘[C] f)) x = setoido_map.map (fmap F f ∘[Setoids] fmap F t) x : congr (congr_arg _ (preserve_comp F)) rfl
      ... = setoido_map.map (fmap F f) (setoido_map.map (fmap F t) x) : rfl))))
  (funext (λu, calc
    setoido_map.map (fmap F (@id C r)) u = setoido_map.map (@id Setoids (fobj F r)) u : congr (congr_arg _ (preserve_id F)) rfl
    ... = u : rfl))
  (funext (λα, natrans_eq _ _ (λx, eqArrow.arr (setoido_map.equal (funext (λu, calc
    setoido_map.map (fmap F u) (setoido_map.map (component α r) id) = setoido_map.map (fmap F u ∘[Setoids] component α r) id : rfl
    ... = setoido_map.map (component α x ∘[Setoids] fmap (fobj (yoneda C) r) u) id : congr (congr_arg _ (naturality α)) rfl
    ... = setoido_map.map (component (id α) x) u : congr_arg _ (@id_left C _ _ _)))))))

