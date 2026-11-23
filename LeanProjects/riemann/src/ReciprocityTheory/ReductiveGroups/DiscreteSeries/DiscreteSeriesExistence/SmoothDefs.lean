import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Defs

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsSmoothVecU (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  S7.SmoothOnGV ε (fun g => σ g v)

def dS (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0

def casSg (ε : Fin n → Bool) (p : Fin n × Fin n) : ℂ := if ε p.1 = ε p.2 then 1 else -1

def casWt (p : Fin n × Fin n) : ℂ := if p.1 = p.2 then 1 else 1 / 2

def casGen (ε : Fin n → Bool) (p : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  if p.1 = p.2 then Complex.I • Matrix.single p.1 p.1 1
  else if p.1 < p.2 then Matrix.single p.1 p.2 1 - casSg ε p • Matrix.single p.2 p.1 1
  else Complex.I • (Matrix.single p.2 p.1 1 + casSg ε p • Matrix.single p.1 p.2 1)

def casU (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : H :=
  -∑ p : Fin n × Fin n, (casWt p * casSg ε p) • dS σ (casGen ε p) (dS σ (casGen ε p) v)

def CasOnSmooth (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ v : H, IsSmoothVecU ε σ v → casU ε σ v = ((casVal lam : ℝ) : ℂ) • v

end Defs

section Exists

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Helpers

open scoped ContDiff

variable {ε : Fin n → Bool}

theorem smd_inUJ_one : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp [inUJ]

theorem smd_inUJ_mul {g k : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hk : inUJ ε k) :
    inUJ ε (g * k) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc kᴴ * gᴴ * Jm ε * (g * k) = kᴴ * (gᴴ * Jm ε * g) * k := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hk]

theorem smd_inUJ_of_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : inUJ ε k := by
  obtain ⟨hu, hc⟩ := hk
  have h1 : kᴴ * k = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
  unfold inUJ
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem smd_inG_add_smul {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) (r : ℝ) :
    inG ε (X + (r : ℂ) • Y) := by
  have hs : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  have h0 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h1 : Yᴴ * Jm ε + Jm ε * Y = 0 := hY
  show (X + (r : ℂ) • Y)ᴴ * Jm ε + Jm ε * (X + (r : ℂ) • Y) = 0
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hs, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul]
  calc Xᴴ * Jm ε + (r : ℂ) • (Yᴴ * Jm ε) + (Jm ε * X + (r : ℂ) • (Jm ε * Y))
      = (Xᴴ * Jm ε + Jm ε * X) + (r : ℂ) • (Yᴴ * Jm ε + Jm ε * Y) := by rw [smul_add]; abel
    _ = 0 := by rw [h0, h1, smul_zero, add_zero]

open scoped Matrix.Norms.Operator in
theorem smd_exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by
  have hE := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hE
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL := (⟨L, L.continuous_of_finiteDimensional⟩ :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hE
  exact hL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smd_hasDerivAt_exp (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  simpa [Complex.coe_smul] using smd_exp_entry X i j

def smdRmul (k : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun g := g * k
  map_add' a b := Matrix.add_mul a b k
  map_smul' c a := Matrix.smul_mul c a k

theorem smd_contDiff_rmul (k : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => g * k) := by
  have h := (⟨smdRmul k, (smdRmul k).continuous_of_finiteDimensional⟩ :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ).contDiff (n := ∞)
  exact h

theorem smd_continuous_rmul (k : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => g * k) := (smd_contDiff_rmul k).continuous

private theorem smd_exp_inUJ_lemma {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) : inUJ ε (NormedSpace.exp A) := by
  have hJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have h0 : Aᴴ * Jm ε + Jm ε * A = 0 := hA
  have h2 : Aᴴ * Jm ε = -(Jm ε * A) := eq_neg_of_add_eq_zero_left h0
  have hAh : Aᴴ = Jm ε * -A * Jm ε := by
    calc Aᴴ = Aᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = Jm ε * -A * Jm ε := by rw [h2, Matrix.mul_neg]
  have hc : NormedSpace.exp (Jm ε * -A * Jm ε) = Jm ε * NormedSpace.exp (-A) * Jm ε :=
    Matrix.exp_units_conj ⟨Jm ε, Jm ε, hJ, hJ⟩ (-A)
  unfold inUJ
  rw [← Matrix.exp_conjTranspose, hAh, hc]
  calc Jm ε * NormedSpace.exp (-A) * Jm ε * Jm ε * NormedSpace.exp A
      = Jm ε * (NormedSpace.exp (-A) * NormedSpace.exp A) := by
        rw [Matrix.mul_assoc (Jm ε * _) (Jm ε) (Jm ε), hJ, Matrix.mul_one, Matrix.mul_assoc]
    _ = Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl A).neg_left), neg_add_cancel,
          NormedSpace.exp_zero, Matrix.mul_one]

theorem smd_orbit_deriv {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
    (hv : IsSmoothVecU ε σ v) :
    ∃ D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H, ∀ X, inG ε X →
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (D X) 0 := by
  unfold IsSmoothVecU S7.SmoothOnGV at hv
  obtain ⟨U, F, hU, h1U, hF, hE⟩ := hv 1 smd_inUJ_one
  have hFd : DifferentiableAt ℝ F 1 :=
    (hF.contDiffAt (hU.mem_nhds h1U)).differentiableAt (by simp)
  refine ⟨(fderiv ℝ F 1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] H).toLinearMap, fun X hX => ?_⟩
  have hexp := smd_hasDerivAt_exp X
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp
  have hFd' : HasFDerivAt F (fderiv ℝ F 1) (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [h0]; exact hFd.hasFDerivAt
  have hcomp := hFd'.comp_hasDerivAt (0 : ℝ) hexp
  have hXt : ∀ t : ℝ, inG ε ((t : ℂ) • X) := fun t => by
    have h := smd_inG_add_smul (ε := ε) (X := 0) (by simp [inG]) hX t
    simpa using h
  have hmem : ∀ᶠ t : ℝ in nhds (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hexp.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU.mem_nhds h1U)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with t ht
  exact hE _ ht (smd_exp_inUJ_lemma (hXt t))

end Helpers

section Steps

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isSmoothVecU_zero : IsSmoothVecU ε σ 0 := by
  unfold IsSmoothVecU S7.SmoothOnGV
  intro g₀ _
  refine ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => ?_⟩
  exact map_zero (σ g)

theorem IsSmoothVecU.add {v w : H} (hv : IsSmoothVecU ε σ v) (hw : IsSmoothVecU ε σ w) :
    IsSmoothVecU ε σ (v + w) := by
  unfold IsSmoothVecU S7.SmoothOnGV at *
  intro g₀ hg₀
  obtain ⟨U1, F1, hU1, hg1, hF1, hE1⟩ := hv g₀ hg₀
  obtain ⟨U2, F2, hU2, hg2, hF2, hE2⟩ := hw g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => F1 g + F2 g, hU1.inter hU2, ⟨hg1, hg2⟩,
    (hF1.mono Set.inter_subset_left).add (hF2.mono Set.inter_subset_right), fun g hg hgJ => ?_⟩
  show σ g (v + w) = F1 g + F2 g
  rw [map_add]
  exact congrArg₂ (· + ·) (hE1 g hg.1 hgJ) (hE2 g hg.2 hgJ)

theorem IsSmoothVecU.smul (c : ℂ) {v : H} (hv : IsSmoothVecU ε σ v) : IsSmoothVecU ε σ (c • v) := by
  unfold IsSmoothVecU S7.SmoothOnGV at *
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, hE⟩ := hv g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, hg, hF.const_smul c, fun g hgU hgJ => ?_⟩
  show σ g (c • v) = c • F g
  rw [map_smul]
  exact congrArg (c • ·) (hE g hgU hgJ)

theorem hasDerivAt_dS (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v : H}
    (hv : IsSmoothVecU ε σ v) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dS σ X v) 0 := by
  obtain ⟨D, hD⟩ := smd_orbit_deriv hv
  exact (hD X hX).differentiableAt.hasDerivAt

theorem IsSmoothVecU.kStable (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {v : H} (hv : IsSmoothVecU ε σ v) : IsSmoothVecU ε σ (σ k v) := by
  unfold IsSmoothVecU S7.SmoothOnGV at *
  intro g₀ hg₀
  have hkJ := smd_inUJ_of_Kset hk
  obtain ⟨U, F, hU, hg, hF, hE⟩ := hv (g₀ * k) (smd_inUJ_mul hg₀ hkJ)
  refine ⟨(fun g => g * k) ⁻¹' U, fun g => F (g * k),
    (smd_continuous_rmul k).isOpen_preimage U hU, hg,
    hF.comp (smd_contDiff_rmul k).contDiffOn (Set.mapsTo_preimage _ _), fun g hg' hgJ => ?_⟩
  have hmul := hσ.1.2 g hgJ k hkJ
  calc σ g (σ k v) = σ (g * k) v := by rw [hmul, ContinuousLinearMap.comp_apply]
    _ = F (g * k) := hE (g * k) hg' (smd_inUJ_mul hgJ hkJ)

theorem dS_add_vec (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v w : H}
    (hv : IsSmoothVecU ε σ v) (hw : IsSmoothVecU ε σ w) : dS σ X (v + w) = dS σ X v + dS σ X w := by
  have h := (hasDerivAt_dS hσ hX hv).add (hasDerivAt_dS hσ hX hw)
  show deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v + w)) 0 = _
  have hf : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v + w)) =
      fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v + σ (NormedSpace.exp ((t : ℂ) • X)) w := by
    funext t; exact map_add _ v w
  rw [hf]
  exact h.deriv

theorem dS_smul_vec (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : dS σ X (c • v) = c • dS σ X v := by
  show deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (c • v)) 0 =
    c • deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0
  simp only [map_smul]
  exact deriv_const_smul' (f := fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (x := 0) c

theorem dS_add_smul (hσ : IsURepOn (UJset ε) σ) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y)
    (r : ℝ) {v : H} (hv : IsSmoothVecU ε σ v) :
    dS σ (X + (r : ℂ) • Y) v = dS σ X v + (r : ℂ) • dS σ Y v := by
  obtain ⟨D, hD⟩ := smd_orbit_deriv hv
  have e : ∀ Z, inG ε Z → dS σ Z v = D Z := fun Z hZ => (hD Z hZ).deriv
  rw [e _ (smd_inG_add_smul hX hY r), e X hX, e Y hY, map_add]
  have hY' : ((r : ℂ) • Y) = r • Y := by
    ext a b; simp [Complex.real_smul]
  rw [hY', map_smul]
  exact congrArg (D X + ·) (Complex.coe_smul r (D Y)).symm

end Steps

end Exists

end ReciprocityTheory.ChartRestriction.DS
