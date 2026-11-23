import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothCore
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3.AdjointEquation

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isUnit_of_mem {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : IsUnit g := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hJJ : Jm ε * Jm ε = 1 := by
    delta Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hli : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hJJ]
  exact (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_left_inverse hli)

theorem inG_conj {ε : Fin n → Bool} {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hX : inG ε X) :
    inG ε (g * X * g⁻¹) := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp (isUnit_of_mem hg)
  have hJ : (Jm ε)ᴴ = Jm ε := by
    delta Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    simp only [Pi.star_apply]
    split_ifs <;> simp
  have h1 : gᴴ * Jm ε = Jm ε * g⁻¹ := by
    have h : gᴴ * Jm ε * g * g⁻¹ = Jm ε * g⁻¹ := by rw [hg']
    rw [Matrix.mul_assoc (gᴴ * Jm ε), Matrix.mul_nonsing_inv g hdet, Matrix.mul_one] at h
    exact h
  have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Jm ε * (g * M) = (g⁻¹)ᴴ * (Jm ε * M) := by
    intro M
    have h := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose] at h
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
  show (g * X * g⁻¹)ᴴ * Jm ε + Jm ε * (g * X * g⁻¹) = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [h1, h2, ← Matrix.mul_add, ← Matrix.mul_assoc Xᴴ, ← Matrix.mul_assoc (Jm ε) X, ← Matrix.add_mul, hX',
    Matrix.zero_mul, Matrix.mul_zero]

theorem smooth_translate {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) {v : H} (hv : IsSmoothVecU ε σ v) : IsSmoothVecU ε σ (σ g v) := by
  rw [isSmoothVecU_iff] at hv ⊢
  have hmulUJ : ∀ a : Matrix (Fin n) (Fin n) ℂ, inUJ ε a → inUJ ε (a * g) := by
    intro a ha
    have ha' : aᴴ * Jm ε * a = Jm ε := ha
    have hg' : gᴴ * Jm ε * g = Jm ε := hg
    show (a * g)ᴴ * Jm ε * (a * g) = Jm ε
    rw [Matrix.conjTranspose_mul]
    calc gᴴ * aᴴ * Jm ε * (a * g) = gᴴ * (aᴴ * Jm ε * a) * g := by simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [ha', hg']
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hv (g₀ * g) (hmulUJ g₀ hg₀)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)
  have hL : ∀ a, L a = a * g := fun a => rfl
  refine ⟨L ⁻¹' U, F ∘ L, hU.preimage L.continuous, ?_, hF.comp L.contDiff.contDiffOn (Set.mapsTo_preimage _ _), ?_⟩
  · show L g₀ ∈ U
    rw [hL]
    exact hgU
  · intro h hhU hh
    have hhU' : h * g ∈ U := by
      have := hhU
      simp only [Set.mem_preimage, hL] at this
      exact this
    simp only [Function.comp_apply, hL]
    rw [← hfF (h * g) hhU' (hmulUJ h hh)]
    show (σ h) ((σ g) v) = (σ (h * g)) v
    rw [hσ.1.2 h hh g hg]
    rfl

theorem dS_conj {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {g X : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hX : inG ε X) {v : H} (hv : IsSmoothVecU ε σ v) :
    σ g (dS σ X v) = dS σ (g * X * g⁻¹) (σ g v) := by
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp (isUnit_of_mem hg)
  have h1UJ : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  have key : ∀ t : ℝ, (1 : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g =
      g * NormedSpace.exp ((t : ℂ) • X) := by
    intro t
    have hs : (t : ℂ) • (g * X * g⁻¹) = g * ((t : ℂ) • X) * g⁻¹ := by
      rw [mul_smul_comm, smul_mul_assoc]
    rw [Matrix.one_mul, hs, Matrix.exp_conj g _ (isUnit_of_mem hg), Matrix.mul_assoc (g * _),
      Matrix.nonsing_inv_mul g hdet, Matrix.mul_one]
  rw [orbit_dS hσ hX hv hg, dS_eq_rdV,
    rdV_congr (f' := fun h => σ (h * g) v) (fun h hh => ?_) h1UJ (inG_conj hg hX)]
  · delta ReciprocityTheory.ChartRestriction.DS.S7.RdV
    simp only [key]
  · show (σ h) ((σ g) v) = (σ (h * g)) v
    rw [hσ.1.2 h hh g hg]
    rfl

end PositivityTheory.RgHe3.AdjointEquation

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS AdjointEquation

theorem adjoint_equation_holds : AdEq := by
  delta AdEq ForRep
  intro n ε H _ _ _ ρ hρ g hg
  have hmaps : ∀ x ∈ smD ε ρ, ρ g x ∈ smD ε ρ := by
    intro x hx
    rw [mem_smD_iff] at hx ⊢
    exact smooth_translate hρ hg hx
  have hact : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (w : smD ε ρ),
      ((actM (smE ε ρ) Z w : smD ε ρ) : H) =
        dS ρ (S7.cpart1 ε Z) w + Complex.I • dS ρ (S7.cpart2 ε Z) w := by
    intro Z w
    obtain ⟨h1, h2, hZ, -⟩ := smc_cpart (ε := ε) Z
    have hlin : actM (smE ε ρ) Z =
        actM (smE ε ρ) (S7.cpart1 ε Z) + Complex.I • actM (smE ε ρ) (S7.cpart2 ε Z) := by
      delta actM
      conv_lhs => rw [hZ]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, mul_smul,
        Finset.sum_add_distrib, Finset.smul_sum]
    rw [hlin, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
      ← dS_eq_actM (isDerivedOn_smE hρ) h1, ← dS_eq_actM (isDerivedOn_smE hρ) h2]
  refine ⟨(ρ g).toLinearMap.restrict hmaps, fun x => rfl, fun X x => ?_⟩
  apply Subtype.ext
  have hx : IsSmoothVecU ε ρ (x : H) := (mem_smD_iff ε ρ x).mp x.2
  obtain ⟨h1, h2, hX, -⟩ := smc_cpart (ε := ε) X
  have hc1 := inG_conj hg h1
  have hc2 := inG_conj hg h2
  have hsplit : g * X * g⁻¹ = g * S7.cpart1 ε X * g⁻¹ + Complex.I • (g * S7.cpart2 ε X * g⁻¹) := by
    conv_lhs => rw [hX]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨e1, e2⟩ := smc_cpart_unique hc1 hc2
  change ρ g ((actM (smE ε ρ) X x : smD ε ρ) : H) = _
  rw [hact, hact, hsplit, e1, e2, map_add, map_smul, dS_conj hρ hg h1 hx, dS_conj hρ hg h2 hx]
  rfl

end PositivityTheory.RgHe3
