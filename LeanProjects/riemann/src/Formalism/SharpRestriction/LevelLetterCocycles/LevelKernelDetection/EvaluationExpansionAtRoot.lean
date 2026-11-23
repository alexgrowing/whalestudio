import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.TensorSumSingleEval

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

theorem inverse_unit_mul_X_pow {Ks : Type} [CommRing Ks] (w : (PowerSeries Ks)ˣ) (m : ℕ) :
    Ring.inverse (HahnSeries.ofPowerSeries ℤ Ks ((w : PowerSeries Ks) * PowerSeries.X ^ m)) =
      HahnSeries.ofPowerSeries ℤ Ks (↑w⁻¹ : PowerSeries Ks) * tp Ks (-(m : ℤ)) := by
  have h1 : HahnSeries.ofPowerSeries ℤ Ks (↑w : PowerSeries Ks) *
      HahnSeries.ofPowerSeries ℤ Ks (↑w⁻¹ : PowerSeries Ks) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have ht : tp Ks (m : ℤ) * tp Ks (-(m : ℤ)) = 1 := by
    rw [tp, tp, HahnSeries.single_mul_single, add_neg_cancel, mul_one]
    rfl
  let U : (HahnSeries ℤ Ks)ˣ :=
    { val := HahnSeries.ofPowerSeries ℤ Ks (↑w : PowerSeries Ks) * tp Ks (m : ℤ)
      inv := HahnSeries.ofPowerSeries ℤ Ks (↑w⁻¹ : PowerSeries Ks) * tp Ks (-(m : ℤ))
      val_inv := by linear_combination (tp Ks (m : ℤ) * tp Ks (-(m : ℤ))) * h1 + ht
      inv_val := by linear_combination (tp Ks (m : ℤ) * tp Ks (-(m : ℤ))) * h1 + ht }
  have hU : HahnSeries.ofPowerSeries ℤ Ks ((w : PowerSeries Ks) * PowerSeries.X ^ m) = ↑U := by
    rw [map_mul, HahnSeries.ofPowerSeries_X_pow]
    rfl
  rw [hU, Ring.inverse_unit]
  rfl

theorem evaluation_comm_tensor {LL D ι : Type} [Field LL] [AddCommGroup D] [Module LL D] [Fintype ι]
    [DecidableEq ι] (i : ι) (z : D ⊗[LL] (ι → LL)) :
    evK i (TensorProduct.comm LL D (ι → LL) z) = TensorProduct.piScalarRight LL LL D ι z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul d f =>
    rw [TensorProduct.comm_tmul, evaluation_tmul, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, Pi.add_apply]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

open Classical in

theorem evaluation_expansion_at_root (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (g : Rs LL PD.p s → D) (ζ : Rs LL PD.p s) : evK ζ (toKsD W s D g) = g ζ := by
  rw [toKsD, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, evaluation_comm_tensor,
    LinearEquiv.apply_symm_apply]

theorem rho_product_unit_mul {ell : ℕ}
    (hk1b : ∀ s < ell, ∃ ε : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X)
    (hunits : ∀ s < ell, IsUnit (rhoL hR c s PowerSeries.X) ∧
      ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')))
    (E : ℕ → ℕ) (s : ℕ) (hs : s < ell) :
    ∃ w : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ E s') =
        (w : PowerSeries (KsW W s)) * PowerSeries.X ^ E s := by
  obtain ⟨ε, hε⟩ := hk1b s hs
  have hrest : IsUnit (rhoL hR c s
      (∏ s' ∈ (Finset.range ell).erase s, (baseIdOf hR).Bs.p s' ^ E s')) := by
    rw [map_prod]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun s' hs' => ?_
    rw [map_pow]
    obtain ⟨hne, hlt⟩ := Finset.mem_erase.1 hs'
    exact ((hunits s hs).2 s' (Finset.mem_range.1 hlt) hne).pow _
  obtain ⟨u, hu⟩ := hrest
  refine ⟨ε ^ E s * u, ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), map_mul, ← hu, map_pow, hε]
  push_cast
  ring

open Classical in

theorem levelCond_iff (ell : ℕ)
    (hk1b : ∀ s < ell, ∃ ε : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X)
    (hunits : ∀ s < ell, IsUnit (rhoL hR c s PowerSeries.X) ∧
      ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')))
    (E : ℕ → ℕ) (s : ℕ) (hs : s < ell) (x : C.V) (hx : x ∈ (latOf C).N c)
    (hFil : ∀ s, Antitone (FilD W T c s)) :
    Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s)
        (rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ E s'))) •
      expN Lb s T c ⟨C.t c x, hx⟩ ∈ Xi (KsW W s) (fun i => FilD W T c s (-i)) ↔
    ∀ (ζ : Rs LL PD.p s) (k : ℤ),
      (⟨Lb.levB T c ζ ⟨C.t c x, hx⟩ k, Lb.mem T c ζ ⟨C.t c x, hx⟩ k⟩ : Dc W T c) ∈
        FilD W T c s ((E s : ℤ) - k) := by
  obtain ⟨w, hw⟩ := rho_product_unit_mul hk1b hunits E s hs
  have hX : Monotone fun i : ℤ => FilD W T c s (-i) := fun i j hij => hFil s (neg_le_neg hij)
  rw [hw, inverse_unit_mul_X_pow, xi_unit_tp _ hX _ _ (Units.inv_mul w), xi_iff]
  refine forall_congr' fun ζ => forall_congr' fun k => ?_
  have hc : cf (expN Lb s T c ⟨C.t c x, hx⟩) k = coefN Lb s T c ⟨C.t c x, hx⟩ k := rfl
  rw [hc, coefN, evaluation_expansion_at_root, show -(k + -(E s : ℤ)) = (E s : ℤ) - k by ring]

end Formalism.MainNotions.N.Ln03.K8
