import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.TopIntegrand

def extId {R : Type} [CommRing R] {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (P : Matrix (Fin n) (Fin m) R)
    (x : Matrix (Fin n) (Fin n) R) : Matrix (Fin m) (Fin m) R := 1 + M * (x - 1) * P

theorem map_emb {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : ℕ} (M : Matrix (Fin m) (Fin n) R)
    (P : Matrix (Fin n) (Fin m) R) (x : Matrix (Fin n) (Fin n) R) :
    (extId M P x).map f = extId (M.map f) (P.map f) (x.map f) := by
  rw [extId, extId, Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub f),
    Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_one _ (map_zero f) (map_one f)]

theorem sum_norm_emb {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (P : Matrix (Fin n) (Fin m) ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Matrix (Fin n) (Fin n) ℂ,
      ∑ i, ∑ j, ‖extId M P x i j‖ ≤ c * (1 + ∑ k, ∑ l, ‖x k l‖) := by
  refine ⟨∑ i, ∑ j, (‖(1 - M * P : Matrix (Fin m) (Fin m) ℂ) i j‖ + ∑ l, ∑ k, ‖M i k‖ * ‖P l j‖), by positivity, fun x => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have e : extId M P x = (1 - M * P) + M * x * P := by
    rw [extId, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
  have hS : 0 ≤ ∑ k, ∑ l, ‖x k l‖ := by positivity
  have hx : ∀ k l, ‖x k l‖ ≤ 1 + ∑ k, ∑ l, ‖x k l‖ := fun k l =>
    ((Finset.single_le_sum (f := fun l => ‖x k l‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun k => ∑ l, ‖x k l‖) (fun _ _ => by positivity) (Finset.mem_univ k))).trans
      (by linarith)
  rw [e, Matrix.add_apply, add_mul]
  refine (norm_add_le _ _).trans (add_le_add (le_mul_of_one_le_right (norm_nonneg _) (by linarith)) ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul, mul_right_comm]
  exact mul_le_mul_of_nonneg_left (hx k l) (by positivity)

variable {D : D7} {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (hι : HSpace.IsIsomEmb B A ι)

abbrev emb : GA D B →* GA D A := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embA D.sp.cm B A ι hι

theorem matHom_emb (h : GA D B) : (matHom A (emb hι h)).1 =
    extId ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat B A ι).map (incA D)) ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat D.sp.cm B A ι).map (incA D))
      (matHom B h).1 := rfl

theorem emb_ker {S : Type} [CommRing S] (f : AF D.host.F ⊗[D.host.F] D.host.E →+* S) (h : GA D B)
    (hh : Formalism.UG.bc f (matHom B h) = 1) : Formalism.UG.bc f (matHom A (emb hι h)) = 1 := by
  have h1 : (matHom B h).1.map f = 1 := congrArg Units.val hh
  refine Units.ext ?_
  change (matHom A (emb hι h)).1.map f = 1
  rw [matHom_emb, map_emb, h1, extId, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem emb_GfC {h : GA D B} (hh : h ∈ GfC B) : emb hι h ∈ GfC A := emb_ker hι _ h hh

theorem emb_GinfC {h : GA D B} (hh : h ∈ GinfC B) : emb hι h ∈ GinfC A := emb_ker hι _ h hh

theorem infMat_emb (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) : ∃ M P, ∀ h : GA D B,
    infMat D.sp.cm.sig A.gram θ (emb hι h) = extId M P (infMat D.sp.cm.sig B.gram θ h) := by
  refine ⟨?_, ?_, fun h => ?_⟩
  rotate_left 2
  change ((matHom A (emb hι h)).1.map
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom).map θ = _
  rw [matHom_emb, map_emb, map_emb]
  rfl

theorem normInf_emb (θ : InfF D) : ∃ c : ℝ, 0 ≤ c ∧ ∀ h : GA D B,
    normInf θ A (emb hι h) ≤ c * (1 + normInf θ B h) := by
  choose M P hMP using fun τ => infMat_emb hι (θ τ)
  choose c hc0 hc using fun τ => sum_norm_emb (M τ) (P τ)
  refine ⟨∑ τ, 2 * c τ, Finset.sum_nonneg fun τ _ => by have := hc0 τ; positivity, fun h => ?_⟩
  rw [Finset.sum_mul, normInf]
  refine Finset.sum_le_sum fun τ _ => ?_
  have h0 : ∑ i, ∑ j, (‖infMat D.sp.cm.sig B.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig B.gram (θ τ) h⁻¹ i j‖) ≤
      normInf θ B h := Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
        (‖infMat D.sp.cm.sig B.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig B.gram (θ τ) h⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  simp only [Finset.sum_add_distrib] at h0 ⊢
  rw [← map_inv, hMP, hMP]
  have h1 := hc τ (infMat D.sp.cm.sig B.gram (θ τ) h)
  have h2 := hc τ (infMat D.sp.cm.sig B.gram (θ τ) h⁻¹)
  have h3 := mul_le_mul_of_nonneg_left h0 (hc0 τ)
  have h4 := mul_nonneg (hc0 τ) (GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) h)
  nlinarith

theorem emb_moderate {θ : InfF D} (hθ : IsInfFam θ) (hc : Continuous (emb hι)) (hQ : ∀ γ ∈ GQ B, emb hι γ ∈ GQ A)
    {φ : GA D A → ℂ} (hφ : IsAutFunSm θ A φ) :
    ∃ (N : ℕ) (C : ℝ), ∀ g, ‖φ (emb hι g)‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ N := by
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  obtain ⟨S, C₀, M, hS⟩ := GlobalTheory.SmoothForms.reduction hθ ((GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ B) (U.comap (emb hι)) (hU.preimage hc)
  obtain ⟨N, hN⟩ := hφ.growth
  choose C hC using hN [] (by simp)
  obtain ⟨c, hc0, hc⟩ := normInf_emb hι θ
  refine ⟨M * N, (∑ x ∈ S, |C (emb hι x)|) * (c * (1 + |C₀|)) ^ N, fun g => ?_⟩
  obtain ⟨γ, hγ, x, hx, a, ha, k, hk, hk', e, hb⟩ := hS g
  rw [← hφ.left _ (hQ γ hγ), ← map_mul, e, map_mul, map_mul, hUφ _ hk (emb_GfC hι hk'), pow_mul, mul_assoc, ← mul_pow]
  have h1 : (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ M :=
    one_le_pow₀ (by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ B g)
  have h2 : normInf θ A (emb hι a) ≤ c * (1 + |C₀|) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ M := by
    refine (hc a).trans ?_
    rw [mul_assoc, add_mul, one_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add h1 (hb.trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans h1)))) hc0
  exact (hC _ _ (emb_GinfC hι ha)).trans (mul_le_mul ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |C (emb hι x)|) (fun _ _ => abs_nonneg _) hx))
    (pow_le_pow_left₀ (GlobalTheory.SmoothForms.normInf_nonneg _) h2 N) (pow_nonneg (GlobalTheory.SmoothForms.normInf_nonneg _) N)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _))

theorem topInt (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) : TopInt D := by
  intro θ hθ A B ι hι μ 𝓕 hq s hs φ φ' hφ hφ'
  obtain rfl : s = emb hι := funext fun h => (GlobalTheory.AutFunCompare.embRel_iff A B ι hι _ _).1 (hs h)
  obtain ⟨s, hc, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D A B ι hι
  have e : ∀ h, emb hι h = s h := fun h => (hrel h _).1 (hs h)
  have hc' : Continuous (emb hι) := by rw [show ⇑(emb hι) = s from funext e]; exact hc
  have hQ' : ∀ γ ∈ GQ B, emb hι γ ∈ GQ A := fun γ hγ => e γ ▸ hQ γ hγ
  obtain ⟨N, C, hC⟩ := emb_moderate hι hθ hc' hQ' hφ
  obtain ⟨K, hK⟩ := (GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hφ'.1 hφ'.2).mul_bounded
    (ψ := fun g => φ (emb hι g)) (fun γ hγ g => by simp only [map_mul]; exact hφ.left _ (hQ' γ hγ) _) hC
  have : BorelSpace (GA D B) := ⟨rfl⟩
  refine Measure.integrableOn_of_bounded (M := K)
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B μ 𝓕 hq.1 hq.2).ne
    (((hφ.cont.comp hc').star.mul hφ'.1.cont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
  rw [norm_mul, norm_star]
  exact hK g

end GlobalTheory.Mem.TopIntegrand

end
