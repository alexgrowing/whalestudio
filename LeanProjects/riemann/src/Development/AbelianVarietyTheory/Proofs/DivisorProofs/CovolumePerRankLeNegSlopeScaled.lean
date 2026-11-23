import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.QuotientMetricDivisors.Statement
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.MeasureFailsForLargeConstant
open NumberField

noncomputable section

namespace GlobalTheory.CovolCore

section Transport

variable {R V W E F : Type} [Ring R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem rk_deg_transport (ρ : V →+ E) (σ : W →+ F) (T : V →+ W) {A : Submodule R V} {B : Submodule R W}
    (hA : Formalism.HN.IsLat ρ A) (hB : Formalism.HN.IsLat σ B)
    (hAB : ∀ y, y ∈ B ↔ ∃ x ∈ A, T x = y) (hn : ∀ x ∈ A, ‖σ (T x)‖ = ‖ρ x‖) :
    Formalism.HN.rk σ B = Formalism.HN.rk ρ A ∧ Formalism.HN.deg σ B = Formalism.HN.deg ρ A := by
  let f : A.toAddSubgroup →+ E := ρ.comp A.toAddSubgroup.subtype
  let g : A.toAddSubgroup →+ F := (σ.comp T).comp A.toAddSubgroup.subtype
  have h1 : ∀ y, y ∈ Formalism.HN.zl ρ A ↔ ∃ m, f m = y :=
    fun y => ⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩
  have h2 : ∀ y, y ∈ Formalism.HN.zl σ B ↔ ∃ m, g m = y := fun y =>
    ⟨fun ⟨m, hm, e⟩ => by
      obtain ⟨x, hx, rfl⟩ := (hAB m).1 hm
      exact ⟨⟨x, hx⟩, e⟩, fun ⟨m, e⟩ => ⟨T m.1, (hAB _).2 ⟨m.1, m.2, rfl⟩, e⟩⟩
  have hn' : ∀ m, ‖f m‖ = ‖g m‖ := fun m => (hn m.1 m.2).symm
  haveI := hA.2
  haveI := hB.2
  refine ⟨?_, ?_⟩
  · have hf : Function.Injective f := fun x y h => Subtype.ext (hA.1 x.2 y.2 h)
    have hg : Function.Injective g := fun x y h =>
      hf (Formalism.HN.QuotientRealization.eq_of_norm_eq g f (fun m => (hn' m).symm) h)
    have e1 : Formalism.HN.zl ρ A = LinearMap.range f.toIntLinearMap := Submodule.ext h1
    have e2 : Formalism.HN.zl σ B = LinearMap.range g.toIntLinearMap := Submodule.ext h2
    unfold Formalism.HN.rk Formalism.F.rk
    rw [e1, e2, ← (LinearEquiv.ofInjective f.toIntLinearMap hf).finrank_eq,
      ← (LinearEquiv.ofInjective g.toIntLinearMap hg).finrank_eq]
  · unfold Formalism.HN.deg Formalism.F.deg
    rw [Formalism.HN.QuotientRealization.covol_eq_of_norm_eq f g _ _ h1 h2 hn']

end Transport

theorem cnorm_smul {ι : Type} [Fintype ι] (s : ℝ) (hs : 0 ≤ s) (u : ι → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm ((s : ℂ) • u) = s * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, mul_pow,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

end GlobalTheory.CovolCore

namespace GlobalTheory.CovolCore

theorem lcv_div_le_neg_slope_sq : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ), GlobalTheory.AllWt.HasGram N →
    ∀ (L : Submodule (𝓞 K) V) (d : ℕ), 0 < d → ∀ (b : Fin d → V), LinearIndependent K b →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range b)) →
    ∀ (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (s : ℝ), 0 < s → s ≤ 1 → (∀ v, IsUnit (X v).det) →
    (∀ v (c : Fin d → K), Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v c = s * N v.embedding (∑ k, c k • b k)) →
    Submodule.IsLattice K (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) →
    Formalism.DivisionValues.lcv X (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) / (d : ℝ) ≤
      -GlobalTheory.AllWt.slope_sq N L := by
  intro K V _ _ _ _ _ _ _ _ N hN L d hd b hb hLb X s hs0 hs1 hX hnorm hM
  set φ := Fintype.linearCombination K b with hφ
  set M := L.comap (φ.restrictScalars (𝓞 K)) with hMdef
  have hφa : ∀ c : Fin d → K, φ c = ∑ k, c k • b k := fun c => Fintype.linearCombination_apply K b c
  let X' : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ := fun v => (s : ℂ) • X v
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hX' : ∀ v, IsUnit (X' v).det := fun v => by
    show IsUnit ((s : ℂ) • X v).det
    rw [Matrix.det_smul]
    exact ((Ne.isUnit hs').pow _).mul (hX v)
  have hfc : ∀ v c, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v c =
      (s : ℂ) • Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X' v c := by
    intro v c
    have e : X' v = (Units.mk0 (s : ℂ) hs') • X v := rfl
    simp only [Formalism.HermitianLatticesTheory.fcoord]
    rw [e, Matrix.inv_smul' (X v) (Units.mk0 (s : ℂ) hs') (hX v), Units.smul_def, Matrix.smul_mulVec, smul_smul,
      Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel₀ hs', one_smul]
  have hOC : GlobalTheory.MeasureLeaf.OneConstant X X' (fun _ => s ^ 2) := fun v =>
    ⟨by positivity, fun x y => by
      simp only [Formalism.HermitianLatticesTheory.majAt, hfc, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_mul', Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring⟩
  have hn' : ∀ v c, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X' v c = N v.embedding (φ c) := by
    intro v c
    have h := hnorm v c
    simp only [Formalism.HermitianLatticesTheory.normAt, hfc, cnorm_smul s hs0.le] at h
    rw [hφa]
    exact mul_left_cancel₀ hs0.ne' h
  have h1 := GlobalTheory.MeasureLeaf.lcv_of_oneConstant hd X X' hX hX' (fun _ => s ^ 2) hOC M hM
  have h2 := Formalism.ExtensionFiltration.lcvMu K d hd X' hX' M hM
  have hlog : 2 / (Module.finrank ℚ K : ℝ) * ∑ v : InfinitePlace K, Real.log (s ^ 2) ≤ 0 := by
    refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun v _ => ?_)
    exact Real.log_nonpos (sq_nonneg _) (by nlinarith)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hMfg : M.FG := hM.fg
  have hML : ∀ y, y ∈ L ↔ ∃ x ∈ M, φ x = y := fun y =>
    ⟨fun hy => by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hLb y hy)
      refine ⟨c, ?_, by rw [hφa, hc]⟩
      show φ c ∈ L
      rw [hφa, hc]; exact hy,
     fun ⟨x, hx, e⟩ => e ▸ hx⟩
  have hLM : L = M.map (φ.restrictScalars (𝓞 K)) := by
    ext y
    rw [hML y, Submodule.mem_map]
    rfl
  have hLfg : L.FG := by rw [hLM]; exact hMfg.map _
  obtain ⟨⟨n, ⟨b0, X0⟩, hG⟩⟩ := id hN
  change GlobalTheory.AllWt.IsGram b0 X0 N at hG
  rw [GlobalTheory.AllWt.slope_sq_eq hG hLfg]
  have hlatM := (Formalism.HN.plLat K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X' hX' M hMfg).1
  have hlatL := (Formalism.HN.plLat K V (Fin n) b0 X0 (fun v => (hG v).1) L hLfg).1
  have hnr : ∀ x ∈ M, ‖Formalism.HermitianLatticesTheory.realize b0 X0 (φ.toAddMonoidHom x)‖ =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin d)) X' x‖ := fun x _ => by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), GlobalTheory.AllWt.norm_realize_sq, GlobalTheory.AllWt.norm_realize_sq]
    exact Finset.sum_congr rfl fun v _ => by rw [(hG v).2, hn' v x]; rfl
  obtain ⟨e1, e2⟩ := rk_deg_transport (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin d)) X')
    (Formalism.HermitianLatticesTheory.realize b0 X0) φ.toAddMonoidHom hlatM hlatL hML hnr
  have key : Formalism.HN.muDef (Pi.basisFun K (Fin d)) X' M = Formalism.HN.muDef b0 X0 L := by
    unfold Formalism.HN.rk at e1
    unfold Formalism.HN.deg at e2
    unfold Formalism.HN.muDef Formalism.HN.slope Formalism.F.slope
    rw [e1, e2]
  have h3 : Formalism.DivisionValues.lcv X' M / (d : ℝ) = -Formalism.HN.muDef (Pi.basisFun K (Fin d)) X' M := by
    rw [h2]; field_simp
  rw [h1, h3, key]
  linarith

end GlobalTheory.CovolCore
