import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerThetaLatticeTranslationStatement
import Development.AutomorphicArithmetic.LocalEmbeddings.LagrForm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

private theorem isUnit_of_mem_closure {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : g ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ)) : IsUnit g := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    rcases hg with (⟨A, hA, rfl⟩ | ⟨C, -, rfl⟩) | rfl
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose]
      exact hA.mul (Matrix.isUnit_nonsing_inv_det A hA)
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₁₂]
      simp
    · refine IsUnit.of_mul_eq_one (Matrix.fromBlocks 0 (-1) 1 0) ?_
      rw [Matrix.fromBlocks_multiply]
      simp
  | one => exact isUnit_one
  | mul g h _ _ hg hh => exact hg.mul hh

private theorem act_sum {F R : Type} [Field F] [CommRing R] [Algebra F R] {κ ι : Type} [Fintype κ] [Fintype ι]
    (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (t : ι → R) (v : ι → κ ⊕ κ → F) :
    GlobalTheory.AdelicSvN.act g (∑ i, t i • ((fun k => algebraMap F R (v i (Sum.inl k))),
      (fun k => algebraMap F R (v i (Sum.inr k))))) =
    ∑ i, t i • ((fun k => algebraMap F R ((g *ᵥ v i) (Sum.inl k))), (fun k => algebraMap F R ((g *ᵥ v i) (Sum.inr k)))) := by
  have key : ∀ m, (g.map (algebraMap F R) *ᵥ Sum.elim
      (∑ i, t i • ((fun k => algebraMap F R (v i (Sum.inl k))), (fun k => algebraMap F R (v i (Sum.inr k))))).1
      (∑ i, t i • ((fun k => algebraMap F R (v i (Sum.inl k))), (fun k => algebraMap F R (v i (Sum.inr k))))).2) m =
      ∑ i, t i * algebraMap F R ((g *ᵥ v i) m) := by
    intro m
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.map_apply,
      Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      map_add, map_sum, map_mul, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    congr 1 <;> (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring)
  ext k
  · rw [GlobalTheory.AdelicSvN.act]
    simp only [Function.comp_apply, key]
    simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
  · rw [GlobalTheory.AdelicSvN.act]
    simp only [Function.comp_apply, key]
    simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]

theorem _root_.GlobalTheory.T.lagrangian_lattice_theta_integral_formula : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (Λ : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F Λ = Fintype.card κ → ∀ (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), (∀ j, u j ∈ Λ) →
    LinearIndependent F (fun j => (u j).1) → (∀ v ∈ Λ, ∃ c : Fin r → F, v.1 = ∑ j, c j • (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ (ι : Type) [Fintype ι] (w : ι → (κ → F) × (κ → F)), (∀ i j, (w i).1 ⬝ᵥ (w j).2 = (w j).1 ⬝ᵥ (w i).2) →
    (∀ c : ι → F, (∀ v ∈ Λ, (∑ i, c i • w i).1 ⬝ᵥ v.2 = v.1 ⬝ᵥ (∑ i, c i • w i).2) → c = 0) →
    ∀ ν : @Measure (ι → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ φ ∈ schA F κ, Integrable (fun t : ι → AF F => ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k)))) (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ) 0 ∂μ) ν := by
  intro F _ _ ψ hψ κ _ Λ hiso hrank r u huΛ hli hsp μ hμ ι _ w _ hnd ν hν φ hφ

  let Φ : ((κ → AF F) → ℂ) → ℂ := fun φ => ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)),
    (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0 ∂μ
  let Φ₀ : schA F κ →ₗ[ℂ] ℂ :=
    { toFun := fun φ => Φ φ
      map_add' := fun φ φ' => by
        refine Eq.trans ?_ (integral_add (UpperTheory.Dv.LagrForm.integrable_schr_zero ψ hψ u hli μ hμ φ.2)
          (UpperTheory.Dv.LagrForm.integrable_schr_zero ψ hψ u hli μ hμ φ'.2))
        simp only [Φ, schr, Submodule.coe_add, Pi.add_apply, mul_add]
      map_smul' := fun c φ => by
        refine Eq.trans ?_ (integral_const_mul c _)
        simp only [Φ, schr, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c] }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend Φ₀
  have hlΦ : ∀ φ ∈ schA F κ, l φ = Φ φ := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  have hadm : l ∈ (adeleClass F).adm κ := by
    intro g hg
    obtain ⟨T, hT⟩ := UpperTheory.Dv.LagrForm.integral_schr_zero ψ hψ u hli μ hμ hg
    exact ⟨T, fun f => (hlΦ _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).trans (hT f)⟩
  have hinv : ∀ (t : AF F), ∀ v ∈ Λ, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun k => algebraMap F (AF F) (v.1 k)), (fun k => algebraMap F (AF F) (v.2 k)))) φ) = l φ := by
    intro t v hv φ hφ
    rw [hlΦ _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), hlΦ φ hφ]
    exact GlobalTheory.T.schrodinger_theta_lattice_translation F ψ κ Λ hiso r u huΛ hsp μ hμ t v hv φ

  obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F κ Λ hiso hrank
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := GlobalTheory.AdelicSvN.realised_of_mem_closure ψ hψ hg
  obtain ⟨l', hl', e⟩ := hSa l hadm
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ l' hl' (fun y φ hφ => by
    have hm : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
    rw [hm, e _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), e φ hφ, hSi _ φ hφ, GlobalTheory.AdelicSvN.act_zero_eq_sum]
    exact GlobalTheory.AdelicSvN.inv_sum ψ hψ Λ hiso l hinv Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))
  obtain ⟨φ', hφ', rfl⟩ := hSs φ hφ

  obtain ⟨h, hgh⟩ := (isUnit_of_mem_closure hg).exists_right_inv
  let v : ι → κ ⊕ κ → F := fun i => h *ᵥ Sum.elim (w i).1 (w i).2
  have hv : ∀ i, g *ᵥ v i = Sum.elim (w i).1 (w i).2 := fun i => by
    rw [Matrix.mulVec_mulVec, hgh, Matrix.one_mulVec]
  let w' : ι → (κ → F) × (κ → F) := fun i => (fun k => v i (Sum.inl k), fun k => v i (Sum.inr k))
  have hw' : LinearIndependent F (fun i => (w' i).1) := by
    refine Fintype.linearIndependent_iff.2 fun a ha i => ?_
    rw [hnd a fun z hz => hiso _ ?_ z hz, Pi.zero_apply]
    have h1 : ∑ i, a i • v i = Sum.elim (0 : κ → F) (fun k => (∑ i, a i • v i) (Sum.inr k)) := by
      funext m
      rcases m with k | k
      · simpa [w', Finset.sum_apply] using congrFun ha k
      · rfl
    have h2 := hgL (fun k => (∑ i, a i • v i) (Sum.inr k))
    rw [← h1, Matrix.mulVec_sum] at h2
    simp only [Matrix.mulVec_smul, hv] at h2
    convert h2 using 1
    ext k <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  refine ((UpperTheory.Dv.LagrForm.integrable_schr_zero ψ hψ w' hw' ν hν hφ').const_mul c).congr
    (Eventually.of_forall fun t => ?_)
  have hact := act_sum g t v
  simp only [hv, Sum.elim_inl, Sum.elim_inr] at hact
  have hm := GlobalTheory.HeisSchA.schr_mem_schA ψ hψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w' i).1 k)),
    (fun k => algebraMap F (AF F) ((w' i).2 k)))) φ' hφ'
  refine ((hc _ hm).symm.trans (e _ hm)).trans ?_
  rw [hSi _ φ' hφ', hact]
  exact hlΦ _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ _ (hS φ' hφ'))
