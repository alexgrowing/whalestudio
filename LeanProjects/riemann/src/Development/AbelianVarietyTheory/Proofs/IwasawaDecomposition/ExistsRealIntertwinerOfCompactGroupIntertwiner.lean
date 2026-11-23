import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompactIntertwiner

theorem hasDerivAt_dual_of_sep {F Z : Type*} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (l : Z → F →ₗ[ℂ] ℂ) (hl : ∀ x, (∀ z, l z x = 0) → x = 0) (c : ℝ → F) (y : F)
    (h : ∀ z, HasDerivAt (fun t => l z (c t)) (l z y) 0) (f : F →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => f (c t)) (f y) 0 := by
  have hsp : Submodule.span ℂ (Set.range l) = ⊤ := by
    have h1 : (Submodule.span ℂ (Set.range l)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_dualCoannihilator] at hx
      exact hl x fun z => hx _ (Submodule.subset_span ⟨z, rfl⟩)
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range l))
    rw [h1, Submodule.dualAnnihilator_bot] at h2
    exact h2.symm
  have hf : f ∈ Submodule.span ℂ (Set.range l) := hsp ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem g hg => obtain ⟨z, rfl⟩ := hg; exact h z
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add g g' _ _ hg hg' => exact hg.fun_add hg'
  | smul a g _ hg => simpa using hg.const_mul a

theorem hasDerivAt_dual_of_sep_sub {E Z : Type*} [AddCommGroup E] [Module ℂ E] (F : Submodule ℂ E)
    [FiniteDimensional ℂ F] (l : Z → E →ₗ[ℂ] ℂ) (hl : ∀ x, (∀ z, l z x = 0) → x = 0) (c : ℝ → E) (y : E)
    (hc : ∀ t, c t ∈ F) (hy : y ∈ F)
    (h : ∀ z, HasDerivAt (fun t => l z (c t)) (l z y) 0) (f : E →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => f (c t)) (f y) 0 :=
  hasDerivAt_dual_of_sep (F := F) (fun z => l z ∘ₗ F.subtype) (fun x hx => Subtype.ext (hl x hx))
    (fun t => ⟨c t, hc t⟩) ⟨y, hy⟩ h (f ∘ₗ F.subtype)

theorem hasDerivAt_bilin {E G : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup G] [Module ℂ G]
    [FiniteDimensional ℂ G] (B : E →ₗ[ℂ] G →ₗ[ℂ] ℂ) (c : ℝ → E) (c' : E) (x : ℝ → G) (x' : G)
    (hc : ∀ f : E →ₗ[ℂ] ℂ, HasDerivAt (fun t => f (c t)) (f c') 0)
    (hx : ∀ f : G →ₗ[ℂ] ℂ, HasDerivAt (fun t => f (x t)) (f x') 0) :
    HasDerivAt (fun t => B (c t) (x t)) (B c' (x 0) + B (c 0) x') 0 := by
  let b := Module.finBasis ℂ G
  have e : ∀ a u, B a u = ∑ i, B.flip (b i) a * b.coord i u := by
    intro a u
    conv_lhs => rw [← b.sum_repr u, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hc (B.flip (b i))).mul (hx (b.coord i))
  simp only [e]
  rw [← Finset.sum_add_distrib]
  exact this

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem ellT_tprod (M : DSModel V S) (w v : ∀ τ, M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, inner ℂ (w τ) (v τ) := by
  simp [ellT]

theorem finite_tensor (M : DSModel V S) (h : ∀ τ, FiniteDimensional ℂ (M.H τ)) :
    FiniteDimensional ℂ (⨂[ℂ] τ, M.H τ) := by
  classical
  exact Module.Finite.of_basis (Basis.piTensorProduct fun τ => Module.finBasis ℂ (M.H τ))

theorem ellT_sep (M : DSModel V S) (h : ∀ τ, FiniteDimensional ℂ (M.H τ)) (x : ⨂[ℂ] τ, M.H τ)
    (hx : ∀ w, ellT M w x = 0) : x = 0 := by
  classical
  let o := fun τ => stdOrthonormalBasis ℂ (M.H τ)
  let b := Basis.piTensorProduct fun τ => (o τ).toBasis
  have key : ∀ i, b.coord i = ellT M fun τ => o τ (i τ) := by
    intro i
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply, ellT_tprod, Module.Basis.coord_apply, b]
    rw [Basis.piTensorProduct_repr_tprod_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [OrthonormalBasis.repr_apply_apply]
  refine b.ext_elem fun i => ?_
  have := hx fun τ => o τ (i τ)
  rw [← key] at this
  simpa using this

theorem inclT_bij (M : DSModel V S) (h : ∀ τ, M.sm τ = ⊤) : Function.Bijective (inclT M) := by
  have : inclT M = (PiTensorProduct.congr fun τ => LinearEquiv.ofTop (M.sm τ) (h τ)).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp [inclT]
  rw [this]
  exact LinearEquiv.bijective _

theorem isUnit_gram (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ) := by
  rw [← M.fr_gram τ]
  refine ((M.fr_unit τ).star.mul ?_).mul (M.fr_unit τ)
  refine IsUnit.of_mul_eq_one (Formalism.REAL.Jm (M.ε τ)) ?_
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem continuous_tprod (M : DSModel V S) (h : ∀ τ, FiniteDimensional ℂ (M.H τ)) (f : (⨂[ℂ] τ, M.H τ) →ₗ[ℂ] ℂ) :
    Continuous fun v : ∀ τ, M.H τ => f (PiTensorProduct.tprod ℂ v) := by
  classical
  let o := fun τ => Module.finBasis ℂ (M.H τ)
  let b := Basis.piTensorProduct o
  have e : ∀ v : ∀ τ, M.H τ, f (PiTensorProduct.tprod ℂ v) = ∑ i, (∏ τ, (o τ).coord (i τ) (v τ)) * f (b i) := by
    intro v
    conv_lhs => rw [← b.sum_repr (PiTensorProduct.tprod ℂ v), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, Basis.piTensorProduct_repr_tprod_apply]
    rfl
  simp only [e]
  exact continuous_finsetSum _ fun i _ => (continuous_finsetProd _ fun τ _ =>
    ((o τ).coord (i τ)).continuous_of_finiteDimensional.comp (continuous_apply τ)).mul continuous_const

theorem one_mem_UH {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH G := by
  simp [Formalism.QuantumDeterminants.UH]

theorem hasDerivAt_pol {σ Z : Type} [Finite σ] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (hpt : Function.Injective pt)
    (c : ℝ → MvPolynomial σ ℂ) (N : ℕ) (hc : ∀ t, (c t).totalDegree ≤ N) (y : MvPolynomial σ ℂ)
    (h : ∀ z, HasDerivAt (fun t => pt (c t) z) (pt y z) 0) (f : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => f (c t)) (f y) 0 :=
  hasDerivAt_dual_of_sep_sub (MvPolynomial.restrictTotalDegree σ ℂ (max N y.totalDegree))
    (fun z => LinearMap.proj z ∘ₗ pt) (fun x hx => hpt (by rw [map_zero]; exact funext hx)) c y
    (fun t => (MvPolynomial.mem_restrictTotalDegree _ _ _).2 ((hc t).trans (le_max_left _ _)))
    ((MvPolynomial.mem_restrictTotalDegree _ _ _).2 (le_max_right _ _)) h f

theorem exists_isItW : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ) (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank) (ρ' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank), IsInfFam θ → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → (∀ τ, FiniteDimensional ℂ (M'.H τ) ∧ M'.sm τ = ⊤) → I ≠ 0 → (∀ τ g φ, (ρ τ g φ).totalDegree ≤ φ.totalDegree) → (∀ τ h φ, (ρ' τ h φ).totalDegree ≤ φ.totalDegree) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ x, I (ρ τ g φ) x = actT M τ g (I φ x)) → (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ x, I (ρ' τ h φ) (actT M' τ h x) = I φ x) → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)), Function.Injective pt → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (pt φ) = pt (ρ τ g φ)) → (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (pt φ) = pt (ρ' τ h φ)) → IsItW θ M M' ω pt It := by
  intro D V W S S' θ M M' I ρ ρ' hθ hM hM' hI hd hd' hρ hρ'
  have fM := finite_tensor M fun τ => (hM τ).1
  have fM' := finite_tensor M' fun τ => (hM' τ).1
  let e := LinearEquiv.ofBijective (inclT M) (inclT_bij M fun τ => (hM τ).2)
  let e' := LinearEquiv.ofBijective (inclT M') (inclT_bij M' fun τ => (hM' τ).2)
  have he : ∀ x, inclT M (e.symm x) = x := fun x => e.apply_symm_apply x
  have he' : ∀ x, inclT M' (e'.symm x) = x := fun x => e'.apply_symm_apply x
  let It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M := (I.compl₂ (inclT M')).compr₂ e.symm.toLinearMap
  have hIt : ∀ φ v, inclT M (It φ v) = I φ (inclT M' v) := fun φ v => he _
  have hinj : Function.Injective (inclT M) := e.injective
  refine ⟨It, fun ω pt hpt hω hω' => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro h0
    refine hI (LinearMap.ext fun φ => LinearMap.ext fun x => ?_)
    have := hIt φ (e'.symm x)
    rw [he', h0] at this
    simpa using this.symm
  · intro φ w
    haveI := fun τ => (hM' τ).1
    let m : MultilinearMap ℂ (fun τ => M'.H τ) ℂ :=
      (ellT M w ∘ₗ I φ).compMultilinearMap (PiTensorProduct.tprod ℂ)
    obtain ⟨c, -, hc⟩ := m.exists_bound_of_continuous (continuous_tprod M' this (ellT M w ∘ₗ I φ))
    refine ⟨c, fun v => ?_⟩
    rw [hIt]
    have := hc fun τ => (v τ : M'.H τ)
    simpa [m, inclT] using this
  · intro τ g hg φ φ' h v
    rw [hω τ g hg] at h
    rw [hpt h, hIt, hIt, hρ τ g hg]
  · intro τ X hX φ φ' h v w
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (isUnit_gram M τ) hX t
    simp only [oneP, hω τ _ (hm _)] at h
    have := hasDerivAt_pol pt hpt (fun t : ℝ => ρ τ (NormedSpace.exp (t • X)) φ) _ (fun t => hd τ _ φ) φ' h
      (ellT M w ∘ₗ I.flip (inclT M' v))
    simp only [hIt, ← hρ τ _ (hm _)]
    exact this
  · intro τ g hg φ φ' v v' h h'
    rw [hω' τ g hg] at h
    apply hinj
    rw [hpt h, hIt, hIt, h', hρ' τ g hg]
  · intro τ X hX φ φ' v v' h h'
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (isUnit_gram M' τ) hX t
    simp only [oneP, hω' τ _ (hm _)] at h
    have h1 : ∀ ψ, ρ' τ 1 ψ = ψ := fun ψ => hpt (by
      rw [← hω' τ 1 (one_mem_UH _), GlobalTheory.PointAtPlaceHom.atTau_one hθ]
      exact congrArg (fun f : Module.End ℂ (WO V W → ℂ) => f (pt ψ)) (map_one ω))
    apply hinj
    rw [map_add, hIt, hIt, map_zero]
    refine ellT_sep M (fun τ => (hM τ).1) _ fun w => ?_
    have hB := hasDerivAt_bilin (I.compr₂ (ellT M w)) (fun t : ℝ => ρ' τ (NormedSpace.exp (t • X)) φ) φ'
      (fun t : ℝ => actT M' τ (NormedSpace.exp (t • X)) (inclT M' v)) (inclT M' v')
      (hasDerivAt_pol pt hpt _ _ (fun t => hd' τ _ φ) φ' h)
      (hasDerivAt_dual_of_sep (ellT M') (ellT_sep M' fun τ => (hM' τ).1) _ _ h')
    simp only [LinearMap.compr₂_apply, hρ' τ _ (hm _), zero_smul, NormedSpace.exp_zero, h1] at hB
    have h2 := hρ' τ 1 (one_mem_UH _) φ' (inclT M' v)
    rw [h1] at h2
    rw [h2] at hB
    rw [map_add]
    exact hB.unique (hasDerivAt_const _ _)

end GlobalTheory.CompactIntertwiner

end
