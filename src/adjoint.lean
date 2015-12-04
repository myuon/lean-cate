import category
import construction
open category functor natrans
open eq eq.ops
open prod

structure adjoint {C D : category} (F : functor C D) (G : functor D C) :=
  (adj_nat : Hom[D][F-;-] ⇒ Hom[C][-;G-])
  (nat_iso : is_natural_iso adj_nat)

namespace adjoint
  notation F `⊣` G := adjoint F G

  definition adjunction {C D : category} {F : functor C D} {G : functor D C} (adj : F ⊣ G) {x : @obj C} {a : @obj D} : @hom D (fobj F x) a ≃[Types] @hom C x (fobj G a) := natural_iso (nat_iso adj)

  definition naturality_left {C D : category} {F : functor C D} {G : functor D C} (adj : F ⊣ G) {x y : @obj C} {a : @obj D} {f : @hom C y x} :
  (component (adj_nat adj) _ ∘[Types] fmap (Hom[D][F-;-] f[-,a]) f) = (fmap (Hom[C][-;G-] f[-,a]) f ∘[Types] component (adj_nat adj) _)
  := naturality (adj_nat adj)

  definition naturality_left_point {C D : category} {F : functor C D} {G : functor D C} (adj : F ⊣ G) {x y : @obj C} {a : @obj D} {f : @hom C y x} (k : @hom D (fobj F x) a) :
  (iso.mapr (adjunction adj) (fmap (Hom[D][F-;-] f[-,a]) f k)) = (fmap (Hom[C][-;G-] f[-,a]) f (iso.mapr (adjunction adj) k))
  := congr_fun (naturality_left adj) k

  definition naturality_right {C D : category} {F : functor C D} {G : functor D C} (adj : F ⊣ G) {x : @obj C} {a b : @obj D} {h : @hom D a b} :
  (component (adj_nat adj) _ ∘[Types] fmap (Hom[D][F-;-] f[x,-]) h) = (fmap (Hom[C][-;G-] f[x,-]) h ∘[Types] component (adj_nat adj) _)
  := naturality (adj_nat adj)

/-
  definition unit {C D : category} {F : functor C D} {G : functor D C} {adj : F ⊣ G} : @functor.id C ⇒ (G ∘f F) := natrans.mk
    (λx, iso.mapr (adjunction adj) (@id D _))
    (λa b f, calc
      (iso.mapr (adjunction adj) (@id D _) ∘[C] fmap functor.id f) = (iso.mapr (adjunction adj) (@id D _) ∘[C] f) : rfl
      ... = (fmap (G ∘f F) f ∘[C] (iso.mapr (adjunction adj) (@id D _))) : _)
-/

end adjoint

