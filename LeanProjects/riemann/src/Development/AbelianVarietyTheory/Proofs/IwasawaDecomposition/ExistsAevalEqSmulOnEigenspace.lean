import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmooth

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_pow_frob_commute {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {h : IsPlaceOver A w} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ, Commute (ρ (frob h) ^ m) (ρ σ) := by
  have h1 : ∀ τ : Weil h, ∃ m : ℕ, 0 < m ∧ Commute (ρ (frob h) ^ m) (ρ τ) := by
    intro τ
    obtain ⟨m, hm, he⟩ := exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ (frob h)
      (τ * frob h * τ⁻¹) (by simp [deg_mul, deg_inv])
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, ← map_pow, conj_pow] at he
    show _ * _ = _ * _
    rw [← map_pow]
    conv_lhs => rw [he]
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have h2 : ∀ S : Set (End ℂ V), S.Finite → (∀ x ∈ S, ∃ τ, ρ τ = x) →
      ∃ m : ℕ, 0 < m ∧ ∀ x ∈ S, Commute (ρ (frob h) ^ m) x := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨1, one_pos, by simp⟩
    | @insert x S _ _ ih =>
      intro hx
      obtain ⟨m, hm, hc⟩ := ih fun y hy => hx y (Set.mem_insert_of_mem _ hy)
      obtain ⟨τ, rfl⟩ := hx x (Set.mem_insert _ _)
      obtain ⟨n, hn, hc'⟩ := h1 τ
      refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
      rintro y (rfl | hy)
      · rw [mul_comm, pow_mul]; exact hc'.pow_left m
      · rw [pow_mul]; exact (hc y hy).pow_left n
  obtain ⟨m, hm, hc⟩ := h2 _ hρ.finite_range (by rintro _ ⟨σ, rfl⟩; exact ⟨_, rfl⟩)
  refine ⟨m, hm, fun σ => ?_⟩
  have h0 : deg ((frob h ^ deg σ)⁻¹ * σ) = 0 := by
    simp [deg_mul, deg_inv, deg_zpow, deg_frob]
  have h3 : Commute (ρ (frob h) ^ m) (ρ ((frob h ^ deg σ)⁻¹ * σ)) :=
    hc _ ⟨⟨_, deg_eq_zero_iff.mp h0⟩, rfl⟩
  have h4 : Commute (ρ (frob h) ^ m) (ρ (frob h ^ deg σ)) :=
    (((Commute.refl (frob h)).zpow_right _).map ρ).pow_left m
  have := h4.mul_right h3
  rwa [← map_mul, mul_inv_cancel_left] at this

open NumberField IsDedekindDomain Polynomial Module in
private lemma exists_polynomial_eigenspace_smul_lemma {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (f : ℂ → ℂ) :
    ∃ p : ℂ[X], ∀ (α : ℂ) (v : V), v ∈ T.eigenspace α → aeval T p v = f α • v := by
  classical
  have hfin : Set.Finite {μ | T.HasEigenvalue μ} := Module.End.finite_hasEigenvalue T
  refine ⟨Lagrange.interpolate hfin.toFinset id f, fun α v hv => ?_⟩
  by_cases hv0 : v = 0
  · simp [hv0]
  have hev : T.HasEigenvector α v := ⟨hv, hv0⟩
  rw [Module.End.aeval_apply_of_hasEigenvector hev]
  have hnode := Lagrange.eval_interpolate_at_node (s := hfin.toFinset) (v := id) f
    (Set.injOn_id _) (i := α) (by simpa using Module.End.hasEigenvalue_of_hasEigenvector hev)
  simp only [id] at hnode
  rw [hnode]

open NumberField IsDedekindDomain Polynomial Module in
private lemma eq_of_eq_on_eigenspaces_lemma_2 {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (hT : T.IsSemisimple) {g g' : Module.End ℂ V}
    (h : ∀ (α : ℂ) (v : V), v ∈ T.eigenspace α → g v = g' v) : g = g' := by
  have hle : ⨆ α, T.eigenspace α ≤ LinearMap.ker (g - g') :=
    iSup_le fun α v hv => by simp [sub_eq_zero, h α v hv]
  rw [hT.iSup_eigenspace_eq_top] at hle
  ext v
  simpa [sub_eq_zero] using hle (Submodule.mem_top : v ∈ ⊤)

open NumberField IsDedekindDomain Polynomial Module in
private lemma mem_eigenspace_pow_lemma_3 {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) {α : ℂ} {v : V} (hv : v ∈ T.eigenspace α) (m : ℕ) :
    v ∈ (T ^ m).eigenspace (α ^ m) := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

open NumberField IsDedekindDomain Polynomial Module in
private lemma commute_aeval_of_commute_lemma_4 {V : Type} [AddCommGroup V] [Module ℂ V]
    {S T : Module.End ℂ V} (hST : Commute S T) (p : ℂ[X]) : Commute S (aeval T p) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add]; exact hp.add_right hr
  | monomial n x => rw [aeval_monomial]; exact (Algebra.commute_algebraMap_right x S).mul_right (hST.pow_right n)

open NumberField IsDedekindDomain Polynomial Module in

theorem _root_.GlobalTheory.WeilDeligne.WDRep.iso_of_N_eq_smul : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a b : _root_.GlobalTheory.WeilDeligne.WDRep h V) (c : ℂ), c ≠ 0 → a.ρ = b.ρ →
    b.N = c • a.N → a.Iso b := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a b c hc hρ hN
  classical
  set φ := _root_.GlobalTheory.WeilDeligne.frob h with hφ
  set Φ : Module.End ℂ V := a.ρ φ with hΦdef
  have hΦ : Φ.IsSemisimple := a.semisimple φ
  have hq : (1 : ℝ) < (_root_.Formalism.ConjugateSelfDual.normV w : ℝ) := by exact_mod_cast _root_.GlobalTheory.WeilDeligne.one_lt_normV w
  set s : ℂ := Complex.log c / (Real.log (_root_.Formalism.ConjugateSelfDual.normV w : ℝ) : ℂ) with hsdef
  have hlogq : (Real.log (_root_.Formalism.ConjugateSelfDual.normV w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hq).ne'
  have hs : Complex.exp (s * Real.log (_root_.Formalism.ConjugateSelfDual.normV w : ℝ)) = c := by
    rw [hsdef, div_mul_cancel₀ _ hlogq, Complex.exp_log hc]
  set lam : ℂ → ℂ := fun α => Complex.exp (s * Real.log ‖α‖) with hlamdef
  have hlam : ∀ α : ℂ, α ≠ 0 → lam ((_root_.Formalism.ConjugateSelfDual.normV w : ℂ) * α) = c * lam α := by
    intro α hα
    simp only [hlamdef, norm_mul, Complex.norm_natCast]
    rw [Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hα)]
    rw [Complex.ofReal_add, mul_add, Complex.exp_add, hs]
  have hΦinj : ∀ v : V, Φ v = 0 → v = 0 := by
    intro v hv
    have : a.ρ φ⁻¹ (Φ v) = v := by
      rw [hΦdef, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← this, hv, map_zero]
  obtain ⟨p, hp⟩ := exists_polynomial_eigenspace_smul_lemma Φ lam
  obtain ⟨p', hp'⟩ := exists_polynomial_eigenspace_smul_lemma Φ (fun α => (lam α)⁻¹)
  have hgg' : aeval Φ p * aeval Φ p' = 1 := eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
    rw [Module.End.mul_apply, hp' α v hv, map_smul, hp α v hv, smul_smul,
      inv_mul_cancel₀ (Complex.exp_ne_zero _), one_smul, Module.End.one_apply]
  have hg'g : aeval Φ p' * aeval Φ p = 1 := eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
    rw [Module.End.mul_apply, hp α v hv, map_smul, hp' α v hv, smul_smul,
      mul_inv_cancel₀ (Complex.exp_ne_zero _), one_smul, Module.End.one_apply]
  refine ⟨LinearEquiv.ofLinear (aeval Φ p) (aeval Φ p') hgg' hg'g, ?_, ?_⟩
  · intro σ v
    rw [← hρ]
    change aeval Φ p (a.ρ σ v) = a.ρ σ (aeval Φ p v)
    obtain ⟨m, hm, hpow⟩ := _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq E Ω A w h V a.ρ
      a.smooth (σ * φ * σ⁻¹) φ
      (by rw [_root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_inv]; ring)
    rw [← map_pow, conj_pow, map_mul, map_mul, map_pow] at hpow
    have hcomm : Commute (a.ρ σ) (Φ ^ m) := by
      calc a.ρ σ * Φ ^ m = a.ρ σ * Φ ^ m * (a.ρ σ⁻¹ * a.ρ σ) := by
            rw [← map_mul, inv_mul_cancel, map_one, mul_one]
        _ = Φ ^ m * a.ρ σ := by rw [← mul_assoc, hpow]
    obtain ⟨pm, hpm⟩ := exists_polynomial_eigenspace_smul_lemma (Φ ^ m)
      (fun μ => Complex.exp (s * Real.log ‖μ‖ / m))
    have hgm : aeval Φ p = aeval (Φ ^ m) pm := eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
      rw [hp α v hv, hpm (α ^ m) v (mem_eigenspace_pow_lemma_3 Φ hv m)]
      congr 1
      simp only [hlamdef, norm_pow, Real.log_pow]
      congr 1
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    rw [hgm]
    exact (LinearMap.congr_fun (commute_aeval_of_commute_lemma_4 hcomm pm) v).symm
  · intro v
    rw [hN]
    change aeval Φ p (a.N v) =
      c • a.N (aeval Φ p v)
    have key : aeval Φ p * a.N =
        c • (a.N * aeval Φ p) :=
      eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
        rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, hp α v hv, map_smul]
        by_cases hα : α = 0
        · have hv0 : v = 0 := hΦinj v (by
            rw [Module.End.mem_eigenspace_iff] at hv
            rw [hv, hα, zero_smul])
          simp [hv0]
        · rw [hp _ _ (a.map_N_eigenspace
            (_root_.GlobalTheory.WeilDeligne.deg_frob) hv), hlam α hα, smul_smul]
    exact LinearMap.congr_fun key v

end GlobalTheory.WeilDeligne
