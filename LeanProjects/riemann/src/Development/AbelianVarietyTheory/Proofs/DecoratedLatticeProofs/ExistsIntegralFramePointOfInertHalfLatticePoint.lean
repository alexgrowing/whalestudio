import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameLoc

theorem cA_algebraMap_place (D : D7) (ε : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) ε) = algebraMap (AF D.host.F) (AE D) ε := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  show sigR _ _ _ = _
  simp [sigR]

theorem placeIdem_mul {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (a : AE D) : algebraMap (AF D.host.F) (AE D) ε * a = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v a) := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hα : α = singleFin v 1 := FiniteAdeleRing.ext _ fun u => by
    change evalV D.host.F u α = evalV D.host.F u (singleFin v 1)
    by_cases e : u = v
    · subst e; rw [evalV_singleFin_self, h1]
    · rw [evalV_singleFin_ne e, h0 u e]
  have h2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = GlobalTheory.EmbChart.tensAt D.host.E v 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply, hα, Algebra.TensorProduct.one_def, GlobalTheory.EmbChart.tensAt_tmul]
    rfl
  rw [h2, GlobalTheory.EmbChart.tensAt_mul_right, one_mul]

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem pair_mem_intL (S : HSp D) {s : Fin S.rank → D.host.E} (hs : s ∈ L0c D S)
    {z : Fin S.rank → w.adicCompletion D.host.E} (hz : z ∈ latAt w (frameLat S)) :
    ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * z m ∈
      Formalism.UG.intL (w.adicCompletion D.host.E) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [← map_mul, ← map_sum]
    have hX : ∑ k, s k • S.frame k ∈ S.L0 := hs
    have hY : ∑ m, y m • S.frame m ∈ S.L0 := (mem_frameLat S y).1 hy
    have hd : ∑ m, y m • S.frame m ∈ Formalism.HermitianLatticesTheory.dual S.hT S.L0 := by rw [S.baseLattice_isUnimodular]; exact hY
    have h1 := Submodule.mem_iInf _ |>.1 (Submodule.mem_iInf _ |>.1 hd (∑ k, s k • S.frame k)) hX
    rw [Submodule.mem_comap] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
    have e : ∑ m, (∑ k, star (s k) * S.gram k m) * y m = algebraMap (𝓞 D.host.E) D.host.E o := by
      rw [ho]
      simp only [LinearMap.restrictScalars_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
      simp only [starRingEnd_apply, RingHom.id_apply]
      ring
    rw [e]
    rw [GlobalTheory.InertLoc.mem_intL, GlobalTheory.Idele.valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one w o
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact add_mem hx hy
  | smul c x _ hx =>
    have e : ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * (c • x) m =
        (c : w.adicCompletion D.host.E) * ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * x m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Pi.smul_apply]
      show _ * ((c : w.adicCompletion D.host.E) * x m) = _
      ring
    rw [e]
    exact mul_mem (show Valued.v (c : w.adicCompletion D.host.E) ≤ 1 from c.2) hx

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

def piW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp (compFin D.host.F D.host.E v)

theorem secW_piW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (a : AE D) :
    secW hw h (piW hw h a) = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v a) := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm
    (GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a))) = _
  rw [RingEquiv.symm_apply_apply]

theorem piW_tmul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
    (m : D.host.E) : piW hw h (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) =
      complMap h (evalV D.host.F v α) * algebraMap D.host.E (w.adicCompletion D.host.E) m := rfl

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem latO_frame_int (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {k : w.adicCompletion D.host.E} {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)}
    {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)} (hk : GlobalTheory.InertLoc.IsGen D w k)
    (haS : IsFrameAt w (frameLat S) aS) (haT : IsFrameAt w (frameLat T) aT) {u : WO S T}
    (hu : u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True)) (i : Fin T.rank) (j : Fin S.rank) :
    (k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1)) i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
  induction hu using AddSubgroup.closure_induction generalizing i j with
  | mem x hx =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hx
    let c0 := complMap h (evalV D.host.F v α)
    let t' : Fin T.rank → w.adicCompletion D.host.E := fun l => algebraMap D.host.E _ (t l)
    let r : Fin S.rank → w.adicCompletion D.host.E :=
      fun m => algebraMap D.host.E _ (∑ l, star (s l) * S.gram l m)
    have e1 : Matrix.map (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ l, star (s l) * S.gram l j) :
        WO S T) (piW hw h) = (c0 * algebraMap D.host.E _ a) • vecMulVec t' r := by
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply, piW_tmul, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
        map_mul, map_mul]
      simp only [mul_assoc]
      rfl
    rw [e1, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, smul_smul, Matrix.smul_apply,
      vecMulVec_apply, smul_eq_mul]
    have h1 : c0 ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := complMap_mem h (hα v)
    have h2 : k⁻¹ * algebraMap D.host.E _ a ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := hk.2.2 a ha
    have h3 : ((aT⁻¹).1 *ᵥ t') i ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
      refine (haT ((aT⁻¹).1 *ᵥ t')).2 ?_ i
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact Submodule.subset_span ⟨t, (mem_frameLat T t).2 ht, rfl⟩
    have h4 : (r ᵥ* aS.1) j ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
      have hcol : (fun m => aS.1 m j) ∈ latAt w (frameLat S) := by
        have := (haS (Pi.single j 1)).1 fun l => by
          by_cases e : l = j
          · subst e; simp
          · simp [e]
        rwa [Matrix.mulVec_single_one] at this
      show ∑ m, r m * aS.1 m j ∈ _
      exact pair_mem_intL S hs hcol
    have e2 : k⁻¹ * (c0 * algebraMap D.host.E (w.adicCompletion D.host.E) a) * (((aT⁻¹).1 *ᵥ t') i * (r ᵥ* aS.1) j) =
        c0 * (k⁻¹ * algebraMap D.host.E _ a) * (((aT⁻¹).1 *ᵥ t') i * (r ᵥ* aS.1) j) := by ring
    rw [e2]
    exact mul_mem (mul_mem h1 h2) (mul_mem h3 h4)
  | zero =>
    rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, smul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.add_apply]
    exact add_mem (hx i j) (hy i j)
  | neg x _ hx =>
    rw [Matrix.map_neg _ (map_neg _), Matrix.mul_neg, Matrix.neg_mul, smul_neg, Matrix.neg_apply]
    exact neg_mem (hx i j)

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

theorem exists_uPt_of_half : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ e e', IsPrimeIdem w e e' → ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → ∃ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) ∧ uPt hw h k aS aT x = u := by
  intro D v w hw h S T k aS aT hk haS haT e e' he u hu hhalf
  obtain ⟨ε, hε, -, -, hee⟩ := GlobalTheory.VacFixInert.inert_data (GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw h)
  obtain ⟨rfl, -⟩ := hee e e' he
  rw [h] at hε
  have hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
    rcases hhalf with h1 | h1
    · exact h1
    · rwa [cA_algebraMap_place] at h1
  have hent : ∀ i j, secW hw h (piW hw h (u i j)) = u i j := fun i j => by
    rw [secW_piW, ← placeIdem_mul hε, hh i j]
  refine ⟨k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1), fun i j => latO_frame_int hw h hk haS haT hu i j, ?_⟩
  have e1 : k • ((aT.1 * (k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1))) * (aS⁻¹).1) = u.map (piW hw h) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hk.1, one_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  ext i j
  rw [uPt, e1, Matrix.map_apply, Matrix.map_apply, hent]

end GlobalTheory.InertFrameLoc
