import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CancelField

theorem isIso_jK {R : Type} [CommRing R] [IsDomain R] (hR : IsField R) : IsIso (jK R) := by
  have hb : Function.Bijective (algebraMap R (FractionRing R)) :=
    ⟨IsFractionRing.injective R (FractionRing R), IsFractionRing.surjective_iff_isField.2 hR⟩
  have : IsIso (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  infer_instance

theorem isIso_gp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (hR : IsField R) : IsIso M.gp := by
  haveI := isIso_jK hR
  haveI := M.integral
  haveI := M.proper
  haveI := M.dominant
  haveI : IsClosedImmersion M.gp :=
    isClosedImmersion_of_comp_eq_id (M.π ≫ inv (jK R)) M.gp (by rw [← Category.assoc, M.gp_π, IsIso.hom_inv_id])
  haveI : Surjective M.gp := ⟨by
    have h1 := M.gp.isClosedEmbedding.isClosed_range
    have h2 := M.gp.denseRange
    exact Set.range_eq_univ.1 (h1.closure_eq ▸ h2.closure_range)⟩
  exact isIso_of_isClosedImmersion_of_surjective M.gp

theorem sval_comp {X Y₀ Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (p : Z ⟶ Y) (r : Y ⟶ Y₀) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    sval s (p ≫ r) z J = (p.stalkMap z).hom (sval s r (p z) (fun ψ => J (p ≫ ψ))) := by
  have hJ' : Good L (p z) (fun ψ => J (p ≫ ψ)) := fun ψ => hJ (p ≫ ψ)
  rw [sval_of s (p ≫ r) z J (fun k => J (p ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp p r z _ (hJ'.mem φ r) _

theorem scal_cancel {W : Type} [CommRing W] [IsDomain W] {Y : Scheme.{0}} (f : Y ⟶ Sp W) [Flat f] (y : Y) {b : W}
    (hb : b ≠ 0) {u v : Y.presheaf.stalk y}
    (h : gs (𝟙 Y) y ⊤ (scal f b) * u = gs (𝟙 Y) y ⊤ (scal f b) * v) : u = v := by
  set c : Γ(Sp W, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b with hc
  have e1 : gs (𝟙 Y) y ⊤ (scal f b) = (f.stalkMap y).hom (gs (𝟙 (Sp W)) (f y) ⊤ c) := by
    have := gs_pull (𝟙 Y) f y ⊤ trivial c
    rw [Category.id_comp] at this
    refine this.trans ?_
    have := gs_comp f (𝟙 (Sp W)) y ⊤ trivial c
    rwa [Category.comp_id] at this
  have hc0 : c ≠ 0 := by
    intro h0
    apply hb
    have hi : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv).1
    exact hi (h0.trans (map_zero _).symm)
  have he0 : gs (𝟙 (Sp W)) (f y) ⊤ c ≠ 0 := by
    rw [gs_eq (𝟙 (Sp W)) (f y) ⊤ trivial]
    intro h0
    apply hc0
    have hi := germ_injective_of_isIntegral (Sp W) (U := (𝟙 (Sp W)) ⁻¹ᵁ ⊤) (f y) trivial
    have := hi (h0.trans (map_zero _).symm)
    exact this
  letI := (f.stalkMap y).hom.toAlgebra
  haveI : Module.Flat _ (Y.presheaf.stalk y) := Flat.stalkMap f y
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Y.presheaf.stalk y) (mem_nonZeroDivisors_of_ne_zero he0)
  apply hreg
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  rw [← e1]
  exact h

end GlobalTheory.Mum.CancelField

namespace GlobalTheory.Mum

open GlobalTheory.Mum.CancelField in

theorem cancel_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (b : W) (c : FractionRing R), IsField R → b ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom b) * sval σ p z J = gs p z ⊤ (scal T.G.hom b) * (gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J)) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J := by
  intro R _ _ _ _ D C W _ _ _ T k σ s b c hR hb H Z p p' hp z J hJ
  haveI : IsIso C.α := C.α_cart.1.isIso_fst_of_isIso (isIso_gp C.toModif hR)
  haveI : Smooth C.G.hom := C.semi.smooth
  haveI : Flat C.G.hom := inferInstance
  haveI : Flat T.G.hom := MorphismProperty.of_isPullback (P := @Flat) T.cart.1 inferInstance
  obtain ⟨q, hq⟩ : ∃ q : T.G.left ⟶ C.A.A.left, q ≫ C.α = T.β := ⟨T.β ≫ inv C.α, by simp⟩
  have key : ∀ y J', Good C.P.L.L y J' → sval σ (𝟙 _) y J' = gs q y ⊤ (scal C.A.A.hom c) * sval s q y J' := by
    intro y J' hJ'
    exact scal_cancel T.G.hom y hb (H _ (𝟙 _) q (by rw [hq, Category.id_comp]) y J' hJ')
  obtain rfl : p' = p ≫ q := (cancel_mono C.α).1 (by rw [Category.assoc, hq]; exact hp.symm)
  have hJ' : Good C.P.L.L (p z) (fun ψ => J (p ≫ ψ)) := fun ψ => hJ (p ≫ ψ)
  have e1 := sval_comp σ p (𝟙 _) z J hJ
  rw [Category.comp_id] at e1
  rw [e1, sval_comp s p q z J hJ, gs_comp p q z ⊤ trivial, ← map_mul, key (p z) _ hJ']

end GlobalTheory.Mum
