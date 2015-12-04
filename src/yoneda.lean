import category
open category functor natrans
open eq eq.ops

definition homfunctor (C : category) (r : @obj C) : functor C Setoids :=
  functor.mk
    (λx, setoido.mk (@hom C r x) (λf g, f = g)
      (mk_equivalence _ refl (λx y, symm) (λx y z, trans)))
    (λa b f, setoido_map.mk (λk, f ∘[C] k) (λx y xy, xy ▸ rfl))
    (λa, setoido_map.equal (funext (λx, id_left)))
    (λa b c g f, setoido_map.equal (funext (λx, !assoc)))

definition ophomfunctor (C : category) (r : @obj C) : functor (op C) Setoids := homfunctor (op C) r

definition homnat (C : category) {a b : @obj C} (f : @hom C b a) : (homfunctor C a) ⇒ (homfunctor C b) :=
  natrans.mk
    (λx, setoido_map.mk (λu, u ∘[C] f) (λx y xy, xy ▸ rfl))
    (λa b f, setoido_map.equal (funext (λx, !assoc)))

definition ophomnat (C : category) {a b : @obj C} (f : @hom C a b) : (ophomfunctor C a) ⇒ (ophomfunctor C b) :=
  natrans.mk
    (λx, setoido_map.mk (λu, f ∘[C] u) (λx y xy, xy ▸ rfl))
    (λa b f, setoido_map.equal (funext (λx, symm !assoc)))

notation `Hom[` C `][` r `;-]` := homfunctor C r
notation `Hom[` C `][-;` r `]` := ophomfunctor C r
notation `HomNat[` C `][` f `;-]` := homnat C f
notation `HomNat[` C `][-;` f `]` := ophomnat C f

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
    (λx, ophomfunctor C x)
    (λa b f, ophomnat C f)
    (λa, natrans_eq _ _ (λx, !eqArrow.arr (setoido_map.equal (funext (λu, id_left)))))
    (λa b d g f, natrans_eq _ _ (λx, !eqArrow.arr (setoido_map.equal (funext (λu, assoc)))))

lemma Yoneda (C : category) (F : functor (op C) Setoids) (r : @obj C) :
  @hom PSh[C] (fobj (yoneda C) r) F ≃[Types] setoido.carrier (fobj F r)
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

