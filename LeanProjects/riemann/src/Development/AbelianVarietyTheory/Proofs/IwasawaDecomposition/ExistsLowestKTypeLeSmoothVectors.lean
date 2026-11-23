import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.SmoothLowType

open Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.GardingVec

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_bump (n : ℕ) (ε : Fin n → Bool) (U : Set (UJ ε)) (hU : U ∈ nhds (1 : UJ ε)) :
    ∃ a : Matrix (Fin n) (Fin n) ℂ → ℝ,
      (∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (f : P → Matrix (Fin n) (Fin n) ℂ),
        (∀ i j, ContDiff ℝ ∞ fun p => f p i j) → ContDiff ℝ ∞ fun p => a (f p)) ∧ (∀ y, 0 ≤ a y) ∧ a 1 ≠ 0 ∧
      HasCompactSupport (fun g : UJ ε => a (umat g)) ∧ (∀ g : UJ ε, a (umat g) ≠ 0 → g ∈ U) ∧
      ∀ k ∈ Kset ε, ∀ y, a (k * y) = a (y * k) := by
  obtain ⟨a, ha, h⟩ := GlobalTheory.exists_conjInvariant_bump n ε U hU
  refine ⟨a, fun P _ _ f hf => ha.comp ?_, h⟩
  exact contDiff_pi.2 fun i => contDiff_pi.2 fun j => hf i j
end

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ => x i j := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem garding_smooth {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψc : HasCompactSupport fun g : UJ ε => φ (umat g)) (w : H)
    (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ) (hx : ContDiff ℝ ∞ x) (hxG : ∀ t, x t ∈ UJset ε) :
    ContDiff ℝ ∞ fun t => σ (x t) (∫ g : UJ ε, φ (umat g) • σ (umat g) w ∂(muG ε)) := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  set μ := Formalism.REAL.muG ε
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w := (hcont w).comp_continuous hu hmem
  have hψ : Continuous fun g : Formalism.REAL.UJ ε => φ (umat g) := hφ.continuous.comp hu
  have hint : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • σ (umat g) w) μ :=
    (hψ.smul hb).integrable_of_hasCompactSupport hψc.smul_right
  let y : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun t => Formalism.REAL.Jm ε * (x t)ᴴ * Formalism.REAL.Jm ε
  have hy : ContDiff ℝ ∞ y := (contDiff_const.mul (contDiff_conjTranspose.comp hx)).mul contDiff_const
  have hyx : ∀ t, y t * x t = 1 := fun t => by
    have h : (x t)ᴴ * Formalism.REAL.Jm ε * x t = Formalism.REAL.Jm ε := hxG t
    calc y t * x t = Formalism.REAL.Jm ε * ((x t)ᴴ * Formalism.REAL.Jm ε * x t) := by simp only [y, Matrix.mul_assoc]
      _ = 1 := by rw [h, Formalism.REAL.Jm_mul_self]
  have hxy : ∀ t, x t * y t = 1 := fun t => mul_eq_one_comm.1 (hyx t)
  have hz : ∀ t, ∃ z : UJ ε, umat z = x t := fun t => by
    have : x t ∈ Set.range (fun g : Formalism.REAL.UJ ε => umat g) := by
      rw [show Set.range (fun g : Formalism.REAL.UJ ε => umat g) = _ from hrange]; exact hxG t
    exact this
  have hform : ∀ t, σ (x t) (∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂μ)
      = ∫ g : Formalism.REAL.UJ ε, φ (y t * umat g) • σ (umat g) w ∂μ := by
    intro t
    obtain ⟨z, hz'⟩ := hz t
    rw [← ContinuousLinearMap.integral_comp_comm _ hint,
      ← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => φ (y t * umat g) • σ (umat g) w) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : umat (z * g) = x t * umat g := by rw [← hz']; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul, hmul _ (hxG t) _ (hmem g),
      ContinuousLinearMap.map_smul_of_tower]
    rfl
  simp only [hform]
  refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
  have hC : IsCompact (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1)
      ((fun g : UJ ε => umat g) '' tsupport fun g : UJ ε => φ (umat g))) :=
    ((isCompact_closedBall t₀ 1).image hx.continuous).mul (IsCompact.image hψc hu)
  have hK := hemb.isCompact_preimage hC
  have hs : ContDiff ℝ ∞ fun t => ∫ g in (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹'
      (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1)
        ((fun g : UJ ε => umat g) '' tsupport fun g : UJ ε => φ (umat g))),
      φ (y t * umat g) • σ (umat g) w ∂μ :=
    contDiff_infty.2 fun m => contDiff_setIntegral_nat μ hK (hu.prodMk hb) m
      (fun z : (Fin k → ℝ) × (Matrix (Fin n) (Fin n) ℂ × H) => φ (y z.1 * z.2.1) • z.2.2)
      ((hφ.comp ((hy.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd))).smul
        (contDiff_snd.comp contDiff_snd))
  refine hs.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [Metric.closedBall_mem_nhds t₀ one_pos] with t ht
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
  by_contra hne
  obtain ⟨z, hz'⟩ := hz t
  have e : x t * umat (z⁻¹ * g) = umat g := by
    rw [← hz']
    show umat (z * (z⁻¹ * g)) = _
    rw [mul_inv_cancel_left]
  have e' : umat (z⁻¹ * g) = y t * umat g := by
    rw [← e, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
  refine hg ⟨x t, ⟨t, ht, rfl⟩, umat (z⁻¹ * g), ⟨z⁻¹ * g, subset_tsupport _ fun h => hne ?_, rfl⟩, e⟩
  have h' : φ (umat (z⁻¹ * g)) = 0 := h
  rw [← e', h', zero_smul]

theorem exists_smooth_ktype {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hK : IsKTypeOf ε σ Λ S) :
    ∃ S' : Submodule ℂ H, IsKTypeOf ε σ Λ S' ∧ ∀ v ∈ S', ∀ (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ),
      ContDiff ℝ ∞ x → (∀ t, x t ∈ UJset ε) → ContDiff ℝ ∞ fun t => σ (x t) v := by
  have : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  haveI := hK.1
  obtain ⟨v, hvS, hv0, -⟩ := hK.2.2.2.1
  have humat : Continuous (fun g : UJ ε => umat g) := (isClosedEmbeddingMatrix n ε).1.continuous
  have hcont : ∀ s : H, Continuous (fun g : UJ ε => σ (umat g) s) := fun s =>
    (hσ.2.2 s).comp_continuous humat (fun g => g.2)
  have hre : Continuous (fun g : UJ ε => (⟪v, σ (umat g) v⟫_ℂ).re) :=
    Complex.continuous_re.comp (continuous_const.inner (hcont v))
  have hone : 0 < (⟪v, σ (umat (1 : UJ ε)) v⟫_ℂ).re := by
    have : σ (umat (1 : UJ ε)) = 1 := hσ.1.1
    rw [this]
    exact re_inner_self_pos (𝕜 := ℂ).2 hv0
  obtain ⟨a, ha', ha0, ha1, hac, haU, haK⟩ := exists_bump n ε
    {g | 0 < (⟪v, σ (umat g) v⟫_ℂ).re} ((isOpen_lt continuous_const hre).mem_nhds hone)
  have ha : ContDiff ℝ ∞ a := ha' _ (fun p => p) contDiff_entry
  have hacont : Continuous (fun g : UJ ε => a (umat g)) := ha.continuous.comp humat
  have hacC : Continuous (fun g : UJ ε => (a (umat g) : ℂ)) := Complex.continuous_ofReal.comp hacont
  have hsuppC : HasCompactSupport (fun g : UJ ε => (a (umat g) : ℂ)) :=
    hac.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hint : ∀ s : H, Integrable (fun g : UJ ε => (a (umat g) : ℂ) • σ (umat g) s) (muG ε) :=
    fun s => (hacC.smul (hcont s)).integrable_of_hasCompactSupport hsuppC.smul_right
  let T : S →ₗ[ℂ] H :=
    { toFun := fun s => ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)
      map_add' := by
        intro s t
        rw [← integral_add (hint s) (hint t)]
        simp only [Submodule.coe_add, map_add, smul_add]
      map_smul' := by
        intro c s
        rw [RingHom.id_apply, ← integral_smul]
        simp only [Submodule.coe_smul, map_smul, smul_comm c] }
  have hT : ∀ (s : S) (u : H), ⟪u, T s⟫_ℂ =
      ∫ g : UJ ε, (a (umat g) : ℂ) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro s u
    show ⟪u, ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)⟫_ℂ = _
    rw [← integral_inner (hint s)]
    simp only [inner_smul_right]
  refine ⟨_, GlobalTheory.Dec.FormF.rangeType n ε Λ H σ S H σ (LinearMap.toContinuousLinearMap T) hK ?_ ?_, ?_⟩
  · intro k hk s s' hs'
    have hu : k ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [(isClosedEmbeddingMatrix n ε).2]
      exact (maximal_compact_facts n ε).1 k hk
    obtain ⟨κ, rfl⟩ := hu
    show ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s' ∂(muG ε) =
      σ (umat κ) (∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hint s), hs']
    have e1 : ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) (σ (umat κ) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_right_eq_self
        (fun g : UJ ε => (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (g * κ)) = _ := hσ.1.2 (umat g) g.2 (umat κ) κ.2
      rw [this, mul_inv_cancel_right]
      rfl
    have e2 : ∫ g : UJ ε, σ (umat κ) ((a (umat g) : ℂ) • σ (umat g) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_left_eq_self
        (fun g : UJ ε => (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (κ * g)) = _ := hσ.1.2 (umat κ) κ.2 (umat g) g.2
      rw [this, inv_mul_cancel_left, map_smul]
      rfl
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    funext g
    have hk' : umat κ⁻¹ ∈ Kset ε := (KG ε).inv_mem (x := κ) hk
    have : a (umat (κ⁻¹ * g)) = a (umat (g * κ⁻¹)) := haK _ hk' (umat g)
    rw [this]
  · intro h0
    have hc : T ⟨v, hvS⟩ = 0 := congrArg (fun f : S →L[ℂ] H => f ⟨v, hvS⟩) h0
    have h1 := hT ⟨v, hvS⟩ v
    rw [hc, inner_zero_right] at h1
    have hi : Integrable (fun g : UJ ε => (a (umat g) : ℂ) * ⟪v, σ (umat g) v⟫_ℂ) (muG ε) :=
      (hacC.mul (continuous_const.inner (hcont v))).integrable_of_hasCompactSupport hsuppC.mul_right
    have h2 := congrArg Complex.re h1
    have h3 := integral_re (𝕜 := ℂ) hi
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3
    rw [← h3] at h2
    have h4 : 0 < ∫ g : UJ ε, a (umat g) * (⟪v, σ (umat g) v⟫_ℂ).re ∂(muG ε) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
        (hacont.mul hre) hac.mul_right ?_ (mul_ne_zero ha1 hone.ne')
      intro g
      by_cases h : a (umat g) = 0
      · simp [h]
      · exact mul_nonneg (ha0 _) (le_of_lt (haU g h))
    rw [← h2] at h4
    simp at h4
  · rintro _ ⟨s, rfl⟩ k x hx hxG
    have e : (T s : H) = ∫ g : UJ ε, a (umat g) • σ (umat g) (s : H) ∂(muG ε) := by
      show ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε) = _
      simp only [Complex.coe_smul]
    show ContDiff ℝ ∞ fun t => σ (x t) (T s)
    rw [e]
    exact garding_smooth hσ ha hac s k x hx hxG

theorem exists_smoothVec_ktype {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hK : IsKTypeOf ε σ Λ S)
    {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) :
    ∃ S' : Submodule ℂ H, IsKTypeOf ε σ Λ S' ∧
      ∀ v ∈ S', Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v := by
  obtain ⟨S', hS', hs⟩ := exists_smooth_ktype hσ hK
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  refine ⟨S', hS', fun v hv k Xs hX =>
    hs v hv k _ ((contDiff_const.mul (contDiff_expProd Xs)).mul contDiff_const) fun t => ?_⟩
  refine conj_mem hP h (list_prod_mem _ fun g hg => ?_)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
  exact exp_mem hG (hX i) _

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_lowK_le_sm : ∀ (D : D7) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (τ : D.what₂.Tau),
    ∃ S : Submodule ℂ (M.H τ), IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S ∧ S ≤ M.sm τ := by
  intro D V Sp M τ
  obtain ⟨h1, h2, h3, -, -, ⟨S, hS⟩, -⟩ := M.ds τ
  obtain ⟨S', hS', hs⟩ := exists_smoothVec_ktype h3 hS (M.fr_unit τ) (M.fr_gram τ)
  exact ⟨S', hS', fun v hv => Submodule.subset_span (hs v hv)⟩

end GlobalTheory.SmoothLowType
