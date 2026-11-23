import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointMatrixHalfIdempotentSmulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointIntegralIffDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalScalarPrimeToConjPolarisationLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseOnConjugateHalfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IncASmulMemAdelicCompletionMatrixGroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdPrimesSquarefreeConjugateIdealProdStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

set_option maxHeartbeats 4000000 in

theorem exists_isGen : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ a : AE D, (∃ b : AE D, a * b = e) ∧ GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  have hS : S.gram = 1 := C.m.gS
  obtain ⟨γ, hγ, s, hs, h1, h2'⟩ := GlobalTheory.T.exists_global_scalar_prime_to_conj_polarisationLattice' D T.rank C.X.Λ ΛT hAA (Pg ∪ Q)
  obtain ⟨t, ht, hte⟩ := GlobalTheory.T.exists_integral_inverse_on_conjugate_half D (Pg ∪ Q) e he s hs
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hecinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hinf : ∀ x : WO S T, IsHalf (cA D e) x → IsFinPt x := by
    intro x hx
    ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [← hx i j, map_mul, hecinf, zero_mul]
  have hmulA : ∀ (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, ((s : D.host.E) * c) • v ∈ L2) →
      ∀ x : WO S T, IsHalf (cA D e) x → x ∈ hatA S T (tens (stdL D.host.E S.rank) L1) →
        incA D c • x ∈ hatA S T (tens (stdL D.host.E S.rank) L2) := by
    intro L1 L2 c hc x hx hxm
    have h3 := GlobalTheory.T.incA_smul_mem_adelicCompletionMatrixGroup D S T _ L1 L2 _ hc x hxm
    have h4 := smul_mem_hatA_of_int (fun o y hy => HatLat.smul_mem_tens _ _ o hy) ht h3
    convert h4 using 1
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    have hxij := hx i j
    calc incA D c * x i j = incA D c * (cA D e * x i j) := by rw [hxij]
      _ = (t * incA D (s : D.host.E) * cA D e) * (incA D c * x i j) := by rw [hte]; ring
      _ = t * (incA D (s : D.host.E) * incA D c * (cA D e * x i j)) := by ring
      _ = t * (incA D (s : D.host.E) * incA D c * x i j) := by rw [hxij]
  have hsc : ∀ (I : Ideal (𝓞 D.host.E)) (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, c • v ∈ L2) →
      ∀ v ∈ I • L1, c • v ∈ I • L2 := by
    intro I L1 L2 c hc v hv
    refine Submodule.smul_induction_on hv (fun i hi w hw => ?_) (fun a b ha hb => ?_)
    · rw [smul_comm]
      exact Submodule.smul_mem_smul hi (hc w hw)
    · rw [smul_add]; exact add_mem ha hb
  refine ⟨e * incA D (star γ⁻¹), ⟨e * incA D (star γ), ?_⟩, ?_⟩
  · have hu : incA D (star γ⁻¹) * incA D (star γ) = 1 := by
      rw [← map_mul, star_inv₀, inv_mul_cancel₀ (star_ne_zero.mpr hγ), map_one]
    calc e * incA D (star γ⁻¹) * (e * incA D (star γ)) = (e * e) * (incA D (star γ⁻¹) * incA D (star γ)) :=
          mul_mul_mul_comm _ _ _ _
      _ = e := by rw [hu, mul_one, hee]
  intro x hx
  have hadj : adjA S T βS βT (e * incA D (star γ⁻¹)) x = adjA S T βS βT 1 (incA D γ⁻¹ • x) :=
    GlobalTheory.T.ideleFrameAdjointMatrix_half_idempotent_smul D S T βS βT e γ⁻¹ x hx
  have hy : IsHalf (cA D e) (incA D γ⁻¹ • x) := by
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_left_comm, hx i j]
  have hyf := hinf _ hy
  have hback : incA D γ • (incA D γ⁻¹ • x) = x := by
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ hγ, map_one, one_smul]
  rw [hadj]
  obtain ⟨hsq, hle, hconj⟩ := GlobalTheory.T.prod_primes_squarefree_conjugateIdeal_prod D (Pg ∪ Q)
  have hmem : ∀ (I : Ideal (𝓞 D.host.E)),
      (incA D γ⁻¹ • x ∈ hatA S T (tens (stdL D.host.E S.rank) (I • ΛT)) ↔
        x ∈ hatA S T (tens (stdL D.host.E S.rank) (I • C.X.Λ))) := by
    intro I
    constructor
    · intro hm
      have := hmulA (I • ΛT) (I • C.X.Λ) γ (hsc I ΛT C.X.Λ _ h2') _ hy hm
      rwa [hback] at this
    · intro hm
      exact hmulA (I • C.X.Λ) (I • ΛT) γ⁻¹ (hsc I C.X.Λ ΛT _ h1) x hx hm
  have hctop : conjI (⊤ : Ideal (𝓞 D.host.E)) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    unfold conjI
    exact Ideal.subset_span ⟨1, Submodule.mem_top, by simp⟩
  constructor
  · have hB := GlobalTheory.T.ideleFrameAdjoint_integral_iff_dualLattice D S T hS ΛT hsd βS βT hβT ⊤ (by rw [← Ideal.one_eq_top]; exact squarefree_one) _ hyf
    rw [hctop, Submodule.top_smul] at hB
    have h5 := hmem ⊤
    rw [Submodule.top_smul, Submodule.top_smul] at h5
    rw [← h5, ← hB]
    constructor
    · intro h; exact ⟨h, fun PP hPP => absurd (top_le_iff.mp hPP) PP.isPrime.ne_top⟩
    · intro h; exact h.1
  · have hB := GlobalTheory.T.ideleFrameAdjoint_integral_iff_dualLattice D S T hS ΛT hsd βS βT hβT _ hsq _ hyf
    rw [hconj] at hB
    have hB' : (IsIntM (adjA S T βS βT 1 (incA D γ⁻¹ • x)) ∧ ∀ PP : Formalism.L2.DIV.Pl D.host.E,
        (∏ PP ∈ Pg ∪ Q, PP.asIdeal) ≤ PP.asIdeal → redM PP (adjA S T βS βT 1 (incA D γ⁻¹ • x)) = 0) ↔
        incA D γ⁻¹ • x ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • ΛT)) := hB
    have h5 := hmem (liftI Pg Q)
    rw [← h5, ← hB']
    simp only [hle]

end GlobalTheory.LiftLevel

end
