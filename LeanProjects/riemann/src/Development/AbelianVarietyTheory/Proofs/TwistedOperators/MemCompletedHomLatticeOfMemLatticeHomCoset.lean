import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HostIdealUnitAtPlacesPrimeToLevel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff

noncomputable section
namespace GlobalTheory.CosLatHalf
open GlobalTheory.RowLatChi Formalism.L2.DIV GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun

theorem smul_mem_latO_of_mem_hatMx' {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) {e : AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    (hAA : ∀ w ∈ P, ∃ a ∈ D.host.AA, Valued.v ((algebraMap D.host.E (Kw w)) a) = 1) {u : WO S T}
    (hm : u ∈ hatMx (homLat ΛS ΛT)) : e • u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_smul]
  refine sum_mem fun w hw => ?_
  obtain ⟨a, ha, hv⟩ := hAA w hw
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, Valuation.map_zero] at hv
    exact zero_ne_one hv
  have hc : finPart D (es w * incA D a⁻¹) ∈ intAE D := by
    refine ((comp_toAd D).int (es w * incA D a⁻¹)).2 fun Q => ?_
    show Valued.v (cpt (D := D) Q (toEAf D (es w * incA D a⁻¹))) ≤ 1
    obtain ⟨h1, h2⟩ := cpt_of_isIdemAt (hes w hw)
    rw [RingHom.map_mul, RingHom.map_mul,
      show cpt (D := D) Q (toEAf D (incA D a⁻¹)) = algebraMap D.host.E (Kw Q) a⁻¹ from Comparison₂.cpt_tmul Q a⁻¹]
    rcases eq_or_ne Q w with rfl | hQ
    · rw [h1, one_mul, map_inv₀, map_inv₀, hv, inv_one]
    · rw [h2 Q hQ, zero_mul, Valuation.map_zero]
      exact zero_le
  have e : es w • u = (es w * incA D a⁻¹) • (incA D a • u) := by
    rw [smul_smul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ ha0, RingHom.map_one, mul_one]
  rw [e]
  exact GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hc _ (smul_mem_latO_of_mem_hatMx hS ha hm)

end GlobalTheory.CosLatHalf

open GlobalTheory.CosLatHalf Formalism.L2.DIV in

theorem GlobalTheory.CosLatHalf.mem_latO_of_mem_cosSet : ∀ {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}, IsSelfDualC S ΛS → ∀ {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}, IsIdemSum e P → (∀ w ∈ P, ∃ a ∈ D.host.AA, Valued.v ((algebraMap D.host.E (Kw w)) a) = 1) → ∀ {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos ΛS ΛT 𝔪) {t : WO S T}, t ∈ cosSet e κ → t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T ΛS ΛT hS e P he hAA 𝔪 κ t ht
  obtain ⟨hth, x₀, -, hd⟩ := ht
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  let u : WO S T := Matrix.of fun i j => pairA D.host.F 0 1 ⊗ₜ[D.host.F] (x₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j
  have hu : u ∈ hatMx (homLat ΛS ΛT) := AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact (v.adicCompletionIntegers D.host.F).one_mem, x₀, x₀.2, rfl⟩
  have heu : e • (x₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E).map (incA D) = e • u := by
    refine Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · simp only [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, hinf, zero_mul]
    · simp only [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      rfl
  have hd' : t - e • (x₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E).map (incA D) ∈ hatMx (homLat ΛS ΛT) := by
    refine AddSubgroup.closure_mono ?_ hd
    rintro _ ⟨α, hα, x, hx, rfl⟩
    exact ⟨α, hα, x, Submodule.smul_le_right hx, rfl⟩
  have key : t = e • (t - e • (x₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E).map (incA D)) + e • u := by
    rw [smul_sub, smul_smul, hee, heu, sub_add_cancel]
    exact Matrix.ext fun i j => (hth i j).symm
  rw [key]
  exact add_mem (smul_mem_latO_of_mem_hatMx' hS he hAA hd') (smul_mem_latO_of_mem_hatMx' hS he hAA hu)
