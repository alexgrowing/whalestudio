import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralKeepsDoublingDiagonalAdicCompletio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormCmExtensionSplitPlaceEqZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)

noncomputable section

namespace GlobalTheory.ThK.SiegelAbs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ordL_eq_neg {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x y : L} (h : x * y = 1) :
    Formalism.UG.ordL y = -Formalism.UG.ordL x := by
  have h1 := Formalism.UG.P.fIwasawa_ordL_mul (1 : L) 1 one_ne_zero one_ne_zero
  have h2 := Formalism.UG.P.fIwasawa_ordL_mul x y (left_ne_zero_of_mul_eq_one h) (right_ne_zero_of_mul_eq_one h)
  rw [mul_one] at h1
  rw [h] at h2
  omega

omit [NumberField E] in

theorem compFin_conj (u : Pl F) (z : AE F E) : compFin F E u (sigR _ σ z) = sigR _ σ (compFin F E u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem absEv_eq (hcm : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) (x : (Fv F v ⊗[F] E)ˣ) :
    (absEv F E v x : ℝ) =
      (qV F v : ℝ) ^ (-(Formalism.UG.ordL (splitProj t x.1) + Formalism.UG.ordL (splitProj t (sigR _ σ x.1)))) := by
  have hN : Algebra.norm (Fv F v) x.1 = splitProj t x.1 * splitProj (t.comp σ) x.1 := by
    have := congrArg (splitProj t) (algebraMap_norm_eq hcm x.1)
    rw [AlgHom.commutes, map_mul, ← splitProj_comp] at this
    exact this
  have hq0 : (qV F v : ℝ) ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    unfold qV
    exact_mod_cast (by omega)
  rw [← splitProj_comp, absEv_apply, coe_nnnorm, hN, norm_mul, neg_add, zpow_add₀ hq0,
    AbsSplit.norm_eq_zpow v (x.isUnit.map (splitProj t)).ne_zero,
    AbsSplit.norm_eq_zpow v (x.isUnit.map (splitProj (t.comp σ))).ne_zero]

theorem map_det_levi {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) A) (h : ∀ i j, f ((M - 1) i j) = 0) :
    f ((leviMat finSumFinEquiv M).det - 1) = 0 := by
  have e : M.map f = 1 := by
    rw [← Matrix.map_one f (map_zero f) (map_one f)]
    ext i j
    have := h i j
    rwa [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [map_sub, map_one, RingHom.map_det, RingHom.mapMatrix_apply, ← leviMat_map, e,
    ← blkMat_one (finSumFinEquiv (m := n) (n := n)), leviMat_blkMat, Matrix.det_one, sub_self]

theorem absE_aOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (X₂ : Spc F E (n + n)), J.det ≠ 0 → X₂.J = dblGram finSumFinEquiv J → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (p : UA σ X₂.J), p ∈ UAt σ X₂ (evFin F v) → ∀ hp : p ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype, ((absE F E (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype ⟨p, hp⟩) : ℝ≥0) : ℝ) = (qV F v : ℝ) ^ (-(Formalism.UG.ordL (leviMat finSumFinEquiv ((mat p).map (piW t))).det - Formalism.UG.ordL (quotMat finSumFinEquiv ((mat p).map (piW t))).det)) := by
  intro F E _ _ _ _ _ σ hcm n J X₂ hJ hX v t p hat hp
  set a := aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype ⟨p, hp⟩ with ha
  have hv : (a : AE F E) = (leviMat finSumFinEquiv (mat p)).det := val_aOf _
  have hent : ∀ i j, At (evFin F v) ((mat p - 1) i j) := fun i j u hu =>
    congrFun (congrFun (hat u hu) i) j
  have hmem : a ∈ idelesAt E (evFin F v) := by
    rw [mem_idelesAt, hv]
    exact at_evFin_iff.2 ⟨fun w => map_det_levi (compInf F E w) _ fun i j => (at_evFin_iff.1 (hent i j)).1 w,
      fun w hw => map_det_levi (compFin F E w) _ fun i j => (at_evFin_iff.1 (hent i j)).2 w hw⟩
  have hT : X₂.Jᵀ = dblGram finSumFinEquiv Jᵀ := by rw [hX, GlobalTheory.DblIwasawa.transpose_dblGram]
  have hq : sigR (AF F) σ (quotMat finSumFinEquiv (mat p)).det * (a : AE F E) = 1 :=
    sigR_det_quot_mul_aH (R := AF F) (σ := σ) hT (by rwa [Matrix.det_transpose])
      ⟨(GlobalTheory.IwLine.ofGAd σ X₂.J).symm p, hp⟩
  have hq' := congrArg (fun z => piW t (sigR (AF F) σ z)) hq
  simp only [map_mul, map_one, sigR_invol (cm_conj_conj hcm)] at hq'
  have e1 : splitProj t (unitFin F E v a).1 = (leviMat finSumFinEquiv ((mat p).map (piW t))).det := by
    rw [leviMat_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← hv]
    rfl
  have e2 : splitProj t (sigR _ σ (unitFin F E v a).1) = piW t (sigR (AF F) σ (a : AE F E)) :=
    (congrArg (splitProj t) (compFin_conj v (a : AE F E))).symm
  rw [absE_of_mem hmem, absEv_eq hcm t, e1, e2, ordL_eq_neg hq', DblSplit.quotMat_map, ← RingHom.mapMatrix_apply (piW t) (quotMat _ _),
    ← RingHom.map_det, sub_eq_add_neg]

end GlobalTheory.ThK.SiegelAbs

end
