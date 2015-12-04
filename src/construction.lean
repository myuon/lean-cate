import category
open category functor natrans
open eq eq.ops
open prod

section product
  lemma prod_subst {a a' b b' : Type} (H₁ : a = a') (H₂ : b = b')
    : (a,b) = (a',b') := H₁ ▸ rfl ⬝ H₂ ▸ rfl

  definition prod_category (C D : category) : category := category.mk
    ((@obj C) × (@obj D))
    (λa b, (@hom C (pr₁ a) (pr₁ b)) × (@hom D (pr₂ a) (pr₂ b)))
    (λa, (@id C (pr₁ a), @id D (pr₂ a)))
    (λa b c f g, (pr₁ f ∘[C] pr₁ g, pr₂ f ∘[D] pr₂ g))
    (λa b c d f g h, (@assoc C _ _ _ _ _ _ _) ▸ rfl ⬝ (@assoc D _ _ _ _ _ _ _) ▸ rfl ⬝ rfl)
    (λa b f, prod.cases_on f (λf₁ f₂, (@id_left C _ _ _) ▸ rfl ⬝ (@id_left D _ _ _) ▸ rfl ⬝ rfl))
    (λa b f, prod.cases_on f (λf₁ f₂, (@id_right C _ _ _) ▸ rfl ⬝ (@id_right D _ _ _) ▸ rfl ⬝ rfl))

  notation C `×c` D := prod_category C D

  definition sigma_unique {A : Type} (B : A → Prop) : Type
    := Σ x, B x ∧ ∀y, B y → y = x
  notation `Σ!` binders `, ` r:(scoped P, sigma_unique P) := r

  structure product {C : category} (a b : @obj C) :=
    (prod : @obj C)
    (proj : @hom (C ×c C) (prod,prod) (a,b))
    (universality : ∀ q, ∀ (f : @hom (C ×c C) (q,q) (a,b)), Σ! (h : @hom C q prod), (pr₁ proj ∘[C] h = pr₁ f) ∧ (pr₂ proj ∘[C] h = pr₂ f))

  definition product.mediating {C : category} {a b : @obj C} (p : @product C a b) {q : @obj C} (f : hom q a) (g : hom q b) : @hom C q (product.prod p)
    := sigma.pr1 (product.universality p q (f,g))

  notation `product⟨` f `, ` g `⟩` := product.mediating _ f g

end product

section bifunctor
  definition bifunctor (C D E : category) := functor (C ×c D) E
  variables {C D E : category}

  definition bifunctor.left_obj (F : bifunctor C D E) (r : @obj C) : functor D E :=
    functor.mk
      (λx, fobj F (r,x))
      (λa b f, fmap F (@category.id C _,f))
      (λa, preserve_id F)
      (λa b c g f, calc
        fmap F (@category.id C _, g ∘[D] f) = fmap F (@category.id C _ ∘[C] @category.id C _, g ∘[D] f) : @id_left C _ _ _ ▸ rfl
        ... = (fmap F (@category.id C _, g) ∘[E] fmap F (@category.id C _, f)) : preserve_comp F)

  definition bifunctor.right_obj (F : bifunctor C D E) (r : @obj D) : functor C E :=
    functor.mk
      (λx, fobj F (x,r))
      (λa b f, fmap F (f,@category.id D _))
      (λa, preserve_id F)
      (λa b c g f, calc
        fmap F (g ∘[C] f,@category.id D _) = fmap F (g ∘[C] f,@category.id D _ ∘[D] @category.id D _) : @id_left D _ _ _ ▸ rfl
        ... = (fmap F (g,@category.id D _) ∘[E] fmap F (f,@category.id D _)) : preserve_comp F)

  notation F `f[` a ` ,` `-]` := bifunctor.left_obj F a
  notation F `f[-` ` ,` a `]` := bifunctor.right_obj F a

  definition bifunctor.left_map (F : bifunctor C D E) {a b : @obj C} (f : @hom C a b) : (F f[a,-]) ⇒ (F f[b,-]) :=
    natrans.mk
      (λx, fmap (F f[-,x]) f)
      (λc d g, calc
        (fmap (F f[-,d]) f ∘[E] fmap (F f[a,-]) g) = (fmap F (f,@category.id D _) ∘[E] fmap F (@category.id C _,g)) : rfl
        ... = fmap F ((f ∘[C] @category.id C _),(@category.id D _ ∘[D] g)) : preserve_comp F
        ... = fmap F (f,(@category.id D _ ∘[D] g)) : @id_right C _ _ _ ▸ rfl
        ... = fmap F (f,g) : @id_left D _ _ _ ▸ rfl
        ... = fmap F (@category.id C _ ∘[C] f,g) : (@id_left C _ _ _ ▸ rfl)⁻¹
        ... = fmap F (@category.id C _ ∘[C] f,g ∘[D] @category.id D _) : (@id_right D _ _ _ ▸ rfl)⁻¹
        ... = (fmap F (@category.id C _,g) ∘[E] fmap F (f,@category.id D _)) : preserve_comp F
        ... = (fmap (F f[b,-]) g ∘[E] fmap (F f[-,c]) f) : rfl)

  definition bifunctor.right_map (F : bifunctor C D E) {a b : @obj D} (f : @hom D a b) : (F f[-,a]) ⇒ (F f[-,b]) :=
    natrans.mk
      (λx, fmap (F f[x,-]) f)
      (λc d g, calc
        (fmap (F f[d,-]) f ∘[E] fmap (F f[-,a]) g) = (fmap F (@category.id C _,f) ∘[E] fmap F (g,@category.id D _)) : rfl
        ... = fmap F ((@category.id C _ ∘[C] g),(f ∘[D] @category.id D _)) : preserve_comp F
        ... = fmap F ((@category.id C _ ∘[C] g),f) : @id_right D _ _ _ ▸ rfl
        ... = fmap F (g,f) : (@id_left C _ _ _ ▸ rfl)⁻¹
        ... = fmap F ((g ∘[C] @category.id C _),f) : (@id_right C _ _ _ ▸ rfl)⁻¹
        ... = fmap F ((g ∘[C] @category.id C _),(@category.id D _ ∘[D] f)) : (@id_left D _ _ _ ▸ rfl)⁻¹
        ... = (fmap F (g,@category.id D _) ∘[E] fmap F (@category.id C _,f)) : preserve_comp F
        ... = (fmap (F f[-,b]) g ∘[E] fmap (F f[c,-]) f) : rfl)

  notation F `n[` f ` ,` `-]` := bifunctor.left_map F f
  notation F `n[-` ` ,` f `]` := bifunctor.right_map F f

  definition binat.left {F G : bifunctor C D E} (η : F ⇒ G) (r : @obj C) : (F f[r,-]) ⇒ (G f[r,-]) :=
    natrans.mk
      (λx, (component η _))
      (λa b f, calc
        (component η (r,b) ∘[E] fmap (F f[r,-]) f) = (component η (r,b) ∘[E] fmap F (@category.id C _,f)) : rfl
        ... = (fmap G (@category.id C _,f) ∘[E] component η (r,a)) : naturality η
        ... = (fmap (G f[r,-]) f ∘[E] component η (r,a)) : rfl)

  definition binat.right {F G : bifunctor C D E} (η : F ⇒ G) (r : @obj D) : (F f[-,r]) ⇒ (G f[-,r]) :=
    natrans.mk
      (λx, (component η _))
      (λa b f, calc
        (component η (b,r) ∘[E] fmap (F f[-,r]) f) = (component η (b,r) ∘[E] fmap F (f,@category.id D _)) : rfl
        ... = (fmap G (f,@category.id D _) ∘[E] component η (a,r)) : naturality η
        ... = (fmap (G f[-,r]) f ∘[E] component η (a,r)) : rfl)

end bifunctor

section homfunctor
  definition homLF {C : category} (D : category) (F : functor C D) : functor (op C ×c D) Types :=
    functor.mk
      (λx, @hom D (fobj F (pr₁ x)) (pr₂ x))
      (λa b f x, pr₂ f ∘[D] x ∘[D] fmap F (pr₁ f))
      (λa, funext (λx, calc
        ((pr₂ (id _) ∘[D] x) ∘[D] fmap F (id _)) = ((pr₂ (id _) ∘[D] x) ∘[D] id _) : preserve_id F ▸ rfl
        ... = (pr₂ (@id (op C ×c D) _) ∘[D] x) : id_right
        ... = x : id_left
      ))
      (λa b c g f, funext (λx, calc
        (pr₂ (g ∘[(op C ×c D)] f) ∘[D] x ∘[D] fmap F (pr₁ (g ∘[(op C ×c D)] f))) = (pr₂ g ∘[D] pr₂ f ∘[D] x ∘[D] fmap F (pr₁ f ∘[C] pr₁ g)) : rfl
        ... = (((pr₂ g ∘[D] pr₂ f) ∘[D] x) ∘[D] (fmap F (pr₁ f) ∘[D] fmap F (pr₁ g))) : preserve_comp F ▸ rfl
        ... = ((pr₂ g ∘[D] (pr₂ f ∘[D] x)) ∘[D] (fmap F (pr₁ f) ∘[D] fmap F (pr₁ g))) : assoc ▸ rfl
        ... = (((pr₂ g ∘[D] (pr₂ f ∘[D] x)) ∘[D] fmap F (pr₁ f)) ∘[D] fmap F (pr₁ g)) : assoc ▸ rfl
        ... = (pr₂ g ∘[D] ((pr₂ f ∘[D] x) ∘[D] fmap F (pr₁ f)) ∘[D] fmap F (pr₁ g)) : assoc ▸ rfl
      ))

  definition homRF {D : category} (C : category) (G : functor D C) : functor (op C ×c D) Types :=
    functor.mk
      (λx, @hom C (pr₁ x) (fobj G (pr₂ x)))
      (λa b f x, fmap G (pr₂ f) ∘[C] x ∘[C] pr₁ f)
      (λa, funext (λx, calc
        (fmap G (id _) ∘[C] x ∘[C] id _) = ((id _ ∘[C] x) ∘[C] id _) : preserve_id G ▸ rfl
        ... = (id _ ∘[C] x) : id_right
        ... = x : id_left
      ))
      (λa b c g f, funext (λx, calc
        (fmap G (pr₂ g ∘[D] pr₂ f) ∘[C] x ∘[C] (pr₁ f ∘[C] pr₁ g)) = ((fmap G (pr₂ g) ∘[C] fmap G (pr₂ f)) ∘[C] x ∘[C] (pr₁ f ∘[C] pr₁ g)) : preserve_comp G ▸ rfl
        ... = ((((fmap G (pr₂ g) ∘[C] fmap G (pr₂ f)) ∘[C] x) ∘[C] pr₁ f) ∘[C] pr₁ g) : assoc ▸ rfl
        ... = (((fmap G (pr₂ g) ∘[C] (fmap G (pr₂ f) ∘[C] x)) ∘[C] pr₁ f) ∘[C] pr₁ g) : assoc ▸ rfl
        ... = ((fmap G (pr₂ g) ∘[C] ((fmap G (pr₂ f) ∘[C] x) ∘[C] pr₁ f)) ∘[C] pr₁ g) : assoc ▸ rfl))

  notation `Hom[` D `][` F `-;-]` := homLF D F
  notation `Hom[` C `][-;` G `-]` := homRF C G
end homfunctor

