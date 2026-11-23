import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionUnipotentRadicalInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.UnipMixed

variable {D : D7}

theorem mt_mul_frame (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (g : GA D V) (hg : g ∈ NI V C) :
    mt V g * C.map (incA D) = C.map (incA D) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨h, -, -⟩ := hg
    have h' : (mt V g - 1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) * (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = 0 := h
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h'
  | one => rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul]
  | mul g h _ _ hg hh => rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.mul_assoc, hh, hg]
  | inv g _ hg =>
    conv_lhs => rw [← hg]
    rw [← Matrix.mul_assoc, ← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul]

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (S.gram⁻¹.map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D) * x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

theorem symplOH_isoPart_eq_zero (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (t : Mx D W.rank r)
    (δ : WO V W) (hδ : δ * C.map (incA D) = 0) : symplOH V W (isoPart V W C t) δ = 0 := by
  have hh : hO V W (isoPart V W C t) δ = 0 := by
    rw [hO_eq_trace]
    have hP : (adj D C * V.gram).map (incA D) = ((C.map (incA D)).map (cA D))ᵀ * V.gram.map (incA D) := by
      rw [Matrix.map_mul]; rfl
    have hC : ((C.map (incA D)).map (cA D))ᵀ * (δ.map (cA D))ᵀ = 0 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hδ, Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]
    simp only [isoPart]
    rw [hP, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_assoc _ (V.gram.map (incA D)), GlobalTheory.SplitOnto.gram_mul_inv, Matrix.mul_one, hC,
      Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]
  simp only [symplOH, symplO, hh, mul_zero, map_zero]

theorem heisO_add_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (x δ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (hδ : δ.map (incA D) * C.map (incA D) = 0) (t : Mx D W.rank r) :
    heisO ψ V W (x.map (incA D) + δ.map (incA D)) f (isoPart V W C t) =
      heisO ψ V W (x.map (incA D)) f (isoPart V W C t) := by
  have o := symplOH_isoPart_eq_zero V W C t _ hδ
  have ha := GlobalTheory.OrientedFormLaws.symplOH_rat (S := V) (T := W) δ x
  generalize (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat V W δ x)) = a at ha
  have q := hf.quasi δ (isoPart V W C t + x.map (incA D))
  have e : isoPart V W C t + (x.map (incA D) + δ.map (incA D)) = ratW W V δ + (isoPart V W C t + x.map (incA D)) := by
    simp only [ratW]; abel
  have s1 : symplOH V W (ratW W V δ) (isoPart V W C t + x.map (incA D)) = algebraMap D.host.F (AF D.host.F) a := by
    rw [GlobalTheory.FinTranslate.symplOH_add_right, GlobalTheory.FinTranslate.symplOH_skew, ratW, o, neg_zero, zero_add, ha]
  have s2 : ψ (-(algebraMap D.host.F (AF D.host.F) a)) = 1 := by
    rw [← map_neg]; exact hψ.1.2.2.1 (-a)
  simp only [heisO]
  rw [e, q, s1, s2, GlobalTheory.FinTranslate.symplOH_add_right, o, add_zero, one_mul]

theorem res_heisO_unip : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ n ∈ NI V C, n ∈ GQ V → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (n, 1) f)) 0 = res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0 := by
  intro D V V' W r C C' B hs _ _ _ ψ χS χT ω hω μ 𝓨 hcov n hnN hnQ y f hf
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V n = n₀.map (incA D) := by
    obtain ⟨γ', -, e⟩ := hnQ
    exact ⟨γ'.1, (congrArg Units.val e).symm⟩
  set X₀ : Matrix (Fin W.rank) (Fin V.rank) D.host.E := y * (adj D C' * V.gram) with hX₀
  have hx : isoPart V W C' (y.map (incA D)) = X₀.map (incA D) := by
    simp only [isoPart, hX₀, Matrix.map_mul]
  set δ : Matrix (Fin W.rank) (Fin V.rank) D.host.E := X₀ * (n₀ - 1) with hδdef
  have hδ : δ.map (incA D) * C.map (incA D) = 0 := by
    rw [hδdef, Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), ← hn₀, Matrix.mul_assoc,
      Matrix.sub_mul, Matrix.one_mul, mt_mul_frame V C n hnN, sub_self, Matrix.mul_zero]
  have hx' : actO V W n⁻¹ 1 (X₀.map (incA D)) = X₀.map (incA D) + δ.map (incA D) := by
    simp only [actO, inv_inv, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, hn₀, hδdef]
    rw [← Matrix.map_mul, Matrix.mul_sub, Matrix.mul_one, ← Matrix.map_add _ (map_add _), add_sub_cancel]
  have hA : heisO ψ V W (X₀.map (incA D)) (ω (n, 1) f) =
      ω (n, 1) (heisO ψ V W (actO V W n⁻¹ 1 (X₀.map (incA D))) f) := by
    rw [hω.om_heis n 1 _ f hf]
    congr 1
    have := GlobalTheory.AdelicLatMove.actO_actO_inv V W n 1 (X₀.map (incA D))
    rw [inv_one] at this
    exact this.symm
  have hK := GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcov ⟨n, hnN⟩ _
    (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hω.std hf (actO V W n⁻¹ 1 (X₀.map (incA D))))
  rw [hx, hA, show res V V' W C B μ 𝓨 (ω (n, 1) (heisO ψ V W (actO V W n⁻¹ 1 (X₀.map (incA D))) f)) =
    res V V' W C B μ 𝓨 (heisO ψ V W (actO V W n⁻¹ 1 (X₀.map (incA D))) f) from hK, hx']
  have hm : midPart V V' W B 0 = 0 := by simp [midPart]
  simp only [res, hm, add_zero]
  congr 1
  funext t
  exact heisO_add_rat V W C hω.std hf X₀ δ hδ t

end GlobalTheory.UnipMixed
