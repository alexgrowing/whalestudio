import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfComplexPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgebraicSectionOfHolomorphicThetaStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace SameFactor

variable {A : Over (Sp ℂ)} [GrpObj A] {M M' : LB A.left} {g : ℕ}

theorem valAt'_div_g {X : Scheme.{0}} (M M' : LB X) (x : Sp ℂ ⟶ X) (p q : (LB.div M' M).ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((LB.div M' M).U p ⊓ (LB.div M' M).U q)) :
    valAt' x ((LB.div M' M).U p ⊓ (LB.div M' M).U q) ((LB.div M' M).g p q).val =
      valAt' x (M'.U p.1 ⊓ M'.U q.1) (M'.g p.1 q.1).val * (valAt' x (M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2).val)⁻¹ := by
  dsimp only [LB.div] at h ⊢
  rw [Units.val_mul, valAt'_mul, valAt'_units_inv x h, GlobalTheory.HolSecAlg.val_res_unit x _ _ h,
    GlobalTheory.HolSecAlg.val_res_unit x _ _ h]

def divUnif (u : HolUnif A M g) (u' : HolUnif A M' g) (hex : u'.ex = u.ex) : HolUnif A (LB.div M' M) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun p z => u'.fr p.1 z * (u.fr p.2 z)⁻¹
  fr_hol := fun p => by
    have h1 := u'.fr_hol p.1
    rw [hex] at h1
    refine DifferentiableOn.mul (h1.mono fun z hz => ?_)
      (DifferentiableOn.inv ((u.fr_hol p.2).mono fun z hz => ?_) fun z hz => u.fr_ne _ _ ?_)
    · exact ((top_le_preimage_inf _ _ _).1 hz).1
    · exact ((top_le_preimage_inf _ _ _).1 hz).2
    · exact ((top_le_preimage_inf _ _ _).1 hz).2
  fr_ne := fun p z hz => by
    obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
    exact mul_ne_zero (u'.fr_ne _ _ (by rw [hex]; exact h1)) (inv_ne_zero (u.fr_ne _ _ h2))
  fr_compat := fun p q z hz => by
    obtain ⟨hp, hq⟩ := (top_le_preimage_inf _ _ _).1 hz
    obtain ⟨hp1, hp2⟩ := (top_le_preimage_inf _ _ _).1 hp
    obtain ⟨hq1, hq2⟩ := (top_le_preimage_inf _ _ _).1 hq
    have e1 := u'.fr_compat p.1 q.1 z (by rw [hex]; exact (top_le_preimage_inf _ _ _).2 ⟨hp1, hq1⟩)
    rw [hex] at e1
    have e2 := u.fr_compat p.2 q.2 z ((top_le_preimage_inf _ _ _).2 ⟨hp2, hq2⟩)
    rw [valAt'_div_g M M' _ p q hz, e1, e2, mul_inv]
    ring

theorem exists_gen_of_isFn [LocallyOfFiniteType A.hom] (u : HolUnif A M g) (s : M.Sec) (θ : (Fin g → ℂ) → ℂ)
    (hs : u.IsFn s θ) (hθ : ∀ z, θ z ≠ 0) : ∃ t : LB.Gen M, t.IsGen := by

  have hunit : ∀ i, IsUnit (s.f i) := fun i =>
    GlobalTheory.ThetaBundleSym.isUnit_of_complex_points u.ex_onto (s.f i) fun z hz => by
      rw [hs i z hz]
      exact mul_ne_zero (hθ z) (u.fr_ne i z hz)
  refine ⟨⟨fun i => (hunit i).unit⟩, fun i j => Units.ext ?_⟩
  rw [Units.val_mul]
  exact s.compat i j

end SameFactor

theorem lbIso_of_same_factor : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (M M' : LB P.A.left) (u : HolUnif P.A M P.g) (u' : HolUnif P.A M' P.g), M.IsLB → M'.IsLB → u'.ex = u.ex → (∀ (l : u.Λ) i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ M'.U j → u.fr i z * u'.fr j (z + l) = u.fr i (z + l) * u'.fr j z) → LBIso M M' := by
  intro hL hL2 hTh hU P M M' u u' hM hM' hex hfac
  have : LocallyOfFiniteType P.A.hom := by
    have := P.isAb.proper
    infer_instance

  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_algebraic_section_of_holomorphic_theta hL hL2 hTh hU P (LB.div M' M) (SameFactor.divUnif u u' hex) (fun _ => 1)
    (LB.isLB_div hM' hM) (differentiable_const 1) (by
      intro l p z hz
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      have hl : u.ex (z + l) = u.ex z := GlobalTheory.HolSecAlg.ex_add_lattice u z l.2
      have n0 : u.fr p.2 z ≠ 0 := u.fr_ne _ _ h2
      have n1 : u.fr p.2 (z + l) ≠ 0 := u.fr_ne _ _ (by rw [hl]; exact h2)
      have key := hfac l p.2 p.1 z h2 h1
      show (1 : ℂ) * (u'.fr p.1 (z + l) * (u.fr p.2 (z + l))⁻¹) = 1 * (u'.fr p.1 z * (u.fr p.2 z)⁻¹)
      rw [_root_.one_mul, _root_.one_mul, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff n1 n0]
      linear_combination key)
  obtain ⟨t, ht⟩ := SameFactor.exists_gen_of_isFn _ s (fun _ => 1) hs fun _ => one_ne_zero
  exact ⟨t, ht⟩

end GlobalTheory
