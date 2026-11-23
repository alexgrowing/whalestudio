import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoDefs
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AutomorphicArithmetic.DivisorFrames.ExistsMaxCompactEqFrameGramSplitBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPureTensorSumDatumRouteThroughSmallVertex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.AdelicU in
private theorem splitLat_comp {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n d : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {τ τ' : E →ₐ[F] Fv F v} {L : Submodule (𝓞 E) (Fin d → E)}
    {L' : Submodule (𝓞 E) (Fin n → E)} (f : Fin n → Fin d) {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    (h : ∀ x ∈ L, ∃ x' ∈ L', ∀ i, τ (x (f i)) = s * τ' (x' i)) {u : Fin d → Fv F v} (hu : u ∈ splitLat τ L) :
    (fun i => u (f i)) ∈ splitLat τ' L' := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine latLoc_induction (p := fun y => (fun i => splitVec τ y (f i)) ∈ splitLat τ' L') (fun a ha x hx => ?_) ?_
    (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · obtain ⟨x', hx', e⟩ := h x hx
    exact ⟨_, tmul_mem_latLoc (mul_mem ha hs) hx', funext fun i => by simp [splitVec, e, mul_assoc]⟩
  · have e1 : (fun i => splitVec τ (0 : Fin d → Fv F v ⊗[F] E) (f i)) = 0 := funext fun i => by simp [splitVec]
    rw [e1]; exact zero_mem _
  · rw [splitVec_add]; exact add_mem hy hz
  · have e1 : (fun i => splitVec τ (-y) (f i)) = -fun i => splitVec τ y (f i) := funext fun i => by simp [splitVec]
    rw [e1]; exact neg_mem hy

private theorem unit_inv_mem {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {s : Fv F v}
    (hs : Valued.v s = 1) : s ≠ 0 ∧ s⁻¹ ∈ v.adicCompletionIntegers F := by
  refine ⟨fun h => by simp [h] at hs, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hs, inv_one]

open GlobalTheory.AdelicU GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.LFun GlobalTheory.LFun.SplitTie Formalism.L2.DIV in
theorem UpperTheory.exists_splitBasis_skewLattice_of_frame :
    ∀ (D : D7) (n d : ℕ) (e : Fin d ≃ Fin n) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
        (L : Submodule (𝓞 D.host.E) (Fin d → D.host.E)) (β : GL (Fin n) (EAf D)), Formalism.L2.DIV.IsFrame β Λ →
        (∀ y, y ∈ L ↔ (fun k => y (e.symm k)) ∈ GlobalTheory.SkewLat.scLat D.host.AA Λ) →
        ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.E →ₐ[D.host.F] Fv D.host.F v), AUnit t →
          ∃ c : GL (Fin d) (Fv D.host.F v), IsSplitBasis t L c ∧ c.1 = (β.1.map (evW t)).submatrix e e := by
  intro D n d e Λ L β hβ hL v t hA
  obtain ⟨⟨a, ha, hta⟩, z, hz, htz⟩ := hA
  have h1 := GlobalTheory.FlipMatch.RowChart.isSplitBasis_conj t
    (GlobalTheory.FlipMatch.RowChart.isFrameAt_loc hβ (splitPrime t))
  have e1 : splitLat (t.comp D.sp.cm.sig) (GlobalTheory.TripleSpaceW.conjSub Λ) = splitLat t Λ := by
    refine le_antisymm (GlobalTheory.FlipMatch.RowChart.splitLat_le fun x hx => ⟨star x, hx, fun i => rfl⟩)
      (GlobalTheory.FlipMatch.RowChart.splitLat_le fun x hx => ⟨star x, ?_, fun i => ?_⟩)
    · rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hx
    · change t (x i) = t (star (star (x i)))
      rw [star_star]
  set β' := GeneralLinearGroup.map (complEquiv t (splitPrime_under t)).symm.toRingHom (loc (splitPrime t) β) with hβ'
  have hv : β'.val = β.val.map (GlobalTheory.BotMatch.evW t) := rfl
  have h2 : IsSplitBasis t Λ β' := fun u => by rw [← e1]; exact h1 u
  obtain ⟨ha0, hai⟩ := unit_inv_mem hta
  obtain ⟨hz0, hzi⟩ := unit_inv_mem htz
  have key : ∀ u : Fin d → Fv D.host.F v, u ∈ splitLat t L ↔ (fun k => u (e.symm k)) ∈ splitLat t Λ := fun u => by
    refine ⟨fun hu => splitLat_comp e.symm hzi (fun x hx => ⟨_, (hL x).1 hx z hz, fun i => ?_⟩) hu, fun hu => ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul, map_mul, inv_mul_cancel_left₀ hz0]
    · have := splitLat_comp (τ' := t) (L' := L) e hai
        (fun x hx => ⟨fun i => a * x (e i), (hL _).2 (by
          have := GlobalTheory.BigDat.smul_mem_scLat_of_mem ha hx
          convert this using 1
          funext k
          simp), fun i => by rw [map_mul, inv_mul_cancel_left₀ ha0]⟩) hu
      simpa using this
  refine ⟨⟨β'.val.submatrix e e, (β'⁻¹).val.submatrix e e, ?_, ?_⟩, fun u => ?_, by rw [← hv]⟩
  · rw [submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv]
  · rw [submatrix_mul_equiv, Units.inv_mul, submatrix_one_equiv]
  · rw [key]
    have e2 : (fun k => (β'.val.submatrix e e *ᵥ u) (e.symm k)) = β'.val *ᵥ fun k => u (e.symm k) := by
      funext k
      rw [submatrix_mulVec_equiv]
      simp [Function.comp_def]
    refine Iff.trans ?_ ((h2 fun k => u (e.symm k)).trans (by rw [← e2]))
    exact ⟨fun h k => h _, fun h i => by simpa using h (e i)⟩
