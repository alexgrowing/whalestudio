import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.SplitHalves

open GlobalTheory.LFun GlobalTheory.LFun.SplitTie GlobalTheory.FlipMatch.RowChart

variable {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem eq_zero_of_at {z : AE D} (hz : At (evFin D.host.F v) z) (h1 : piW τ z = 0)
    (h2 : piW (τ.comp D.sp.cm.sig) z = 0) : z = 0 := by
  classical
  set l : AF D.host.F := GlobalTheory.LatVac.liftV v 1 with hl
  have hz1 : z = l • z := by
    have h0 := hz (1 - l) (by rw [map_sub, map_one, hl, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h0
    exact h0
  refine ae_ext ?_ fun Q => ?_
  · have e : infPart D (algebraMap (AF D.host.F) (AE D) l) = 0 := by
      change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    rw [hz1, Algebra.smul_def, RingHom.map_mul, e, zero_mul, map_zero]
  · rw [map_zero, map_zero]
    by_cases h : Q.under (𝓞 D.host.F) = v
    · have hm : Q.asIdeal ∈ v.asIdeal.primesOver (𝓞 D.host.E) := ⟨Q.isPrime, ⟨h ▸ rfl⟩⟩
      rw [primesOver_eq_split (isCMExt_host D) τ] at hm
      rcases hm with e | e
      · obtain rfl : Q = splitPrime τ := HeightOneSpectrum.ext e
        rw [← isPlaceIso_complEquiv τ, h1, map_zero]
      · obtain rfl : Q = splitPrime (τ.comp D.sp.cm.sig) := HeightOneSpectrum.ext e
        rw [← isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), h2, map_zero]
    · have e : cpt (D := D) Q (toEAf D (algebraMap (AF D.host.F) (AE D) l)) =
          GlobalTheory.AdeleBaseChange.locMap D.host.F Q (l.2 (Q.under (𝓞 D.host.F))) := (comp_toAd D).base l Q
      have e2 : l.2 (Q.under (𝓞 D.host.F)) = 0 := GlobalTheory.AdelicU.evalV_singleFin_ne h _
      rw [hz1, Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, e, e2, map_zero, zero_mul]

theorem mul_eq_iff {ε : AE D} (hε : At (evFin D.host.F v) ε) {p q : AE D →+* Fv D.host.F v} (hp : p ε = 1) (hq : q ε = 0)
    (hinj : ∀ z : AE D, At (evFin D.host.F v) z → p z = 0 → q z = 0 → z = 0) (z : AE D) :
    ε * z = z ↔ At (evFin D.host.F v) z ∧ q z = 0 := by
  refine ⟨fun h => ⟨fun a ha => ?_, ?_⟩, fun ⟨h1, h2⟩ => sub_eq_zero.1 (hinj _ (fun a ha => ?_) ?_ ?_)⟩
  · rw [← h, ← smul_mul_assoc, hε a ha, zero_mul]
  · rw [← h, RingHom.map_mul, hq, zero_mul]
  · rw [smul_sub, ← smul_mul_assoc, hε a ha, zero_mul, h1 a ha, sub_zero]
  · rw [RingHom.map_sub, RingHom.map_mul, hp, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_mul, h2, mul_zero, sub_zero]

theorem piW_atPl_one : piW τ (atPl (splitPrime τ) 1) = 1 := by
  classical
  exact (complEquiv τ (splitPrime_under τ)).injective (by
    rw [isPlaceIso_complEquiv τ, (atPl_spec _ _).2, Pi.single_eq_same, map_one])

theorem piW_comp_atPl_one : piW (τ.comp D.sp.cm.sig) (atPl (splitPrime τ) 1) = 0 := by
  classical
  exact (complEquiv (τ.comp D.sp.cm.sig) (splitPrime_under _)).injective (by
    rw [isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), (atPl_spec _ _).2,
      Pi.single_eq_of_ne (splitPrime_comp_ne (isCMExt_host D) τ), map_zero])

theorem isHalf_iff (ε : AE D) {m k d : ℕ} (e : Fin d ≃ Fin k) (Gm : Matrix (Fin m) (Fin m) D.host.E) (hG : Gm.det ≠ 0)
    (u : Matrix (Fin m) (Fin k) (AE D)) :
    IsHalf ε (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔ ∀ a b, ε * u a b = u a b := by
  constructor
  · intro h a b
    have hAB : (Gm⁻¹).map (incA D) * Gm.map (incA D) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hG), Matrix.map_one _ (map_zero _) (map_one _)]
    obtain ⟨b, rfl⟩ := e.surjective b
    exact half_cancel (x := uᵀ.submatrix e id) hAB h b a
  · intro h a b
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc]
    exact congrArg (· * _) (h c (e a))

theorem entries_iff {m k : ℕ} (u : Matrix (Fin m) (Fin k) (AE D)) (q : AE D →+* Fv D.host.F v) :
    (∀ a b, At (evFin D.host.F v) (u a b) ∧ q (u a b) = 0) ↔ At (evFin D.host.F v) u ∧ u.map q = 0 :=
  ⟨fun h => ⟨fun c hc => Matrix.ext fun a b => (h a b).1 c hc, Matrix.ext fun a b => (h a b).2⟩,
    fun h a b => ⟨fun c hc => congrFun (congrFun (h.1 c hc) a) b, congrFun (congrFun h.2 a) b⟩⟩

theorem halves : ∀ {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∀ {m k d : ℕ} (e : Fin d ≃ Fin k) (Gm : Matrix (Fin m) (Fin m) D.host.E), Gm.det ≠ 0 → ∀ u : Matrix (Fin m) (Fin k) (AE D),
      (IsHalf (atPl w 1) (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔
        At (evFin D.host.F v) u ∧ u.map (piW (τ.comp D.sp.cm.sig)) = 0) ∧
      (IsHalf (cA D (atPl w 1)) (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔
        At (evFin D.host.F v) u ∧ u.map (piW τ) = 0) := by
  intro D v τ w hw m k d e Gm hG u
  subst hw
  have hε := at_atPl τ 1
  constructor
  · rw [isHalf_iff _ e Gm hG, ← entries_iff]
    exact forall₂_congr fun a b => mul_eq_iff hε (piW_atPl_one τ) (piW_comp_atPl_one τ)
      (fun z h0 h1 h2 => eq_zero_of_at τ h0 h1 h2) _
  · rw [isHalf_iff _ e Gm hG, ← entries_iff]
    refine forall₂_congr fun a b => mul_eq_iff (p := piW (τ.comp D.sp.cm.sig)) (at_cA hε) ?_ ?_
      (fun z h0 h1 h2 => eq_zero_of_at τ h0 h2 h1) _
    · rw [← piW_cA_eq, GlobalTheory.DualPairCheck.cA_cA, piW_atPl_one]
    · rw [piW_cA_eq, piW_comp_atPl_one]

end GlobalTheory.SplitHalves

end
