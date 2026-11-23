import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

section GrdComm

variable {LL Ks D : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]

theorem Pf_LvGam_grd_comm (σ τ : Ks ≃ₐ[LL] Ks) (a b : LLˣ) (h : ∀ x, σ (τ x) = τ (σ x))
    (f : Amb LL Ks D) : grd τ b (grd σ a f) = grd σ a (grd τ b f) := by
  apply HahnModule.ext
  funext i
  change cf (grd τ b (grd σ a f)) i = cf (grd σ a (grd τ b f)) i
  rw [SlopeTestRemainingChoices.cf_grd, SlopeTestRemainingChoices.cf_grd, SlopeTestRemainingChoices.cf_grd, SlopeTestRemainingChoices.cf_grd, map_smul, map_smul, smul_smul, smul_smul,
    SlopeTestRemainingChoices.tD_comm σ τ h, mul_comm]

end GrdComm

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem Pf_LvGam_στ (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (s : ℕ) (j : DeltaT PD.p) (x : KsW W s) :
    (levW W uZ ιZ s).σ ((levW W uZ ιZ s).τ j x) = (levW W uZ ιZ s).τ j ((levW W uZ ιZ s).σ x) := by
  funext ζ
  show x (powR LL PD.p s (redU PD.p s j.1) (powR LL PD.p s (redU PD.p s uZ) ζ)) =
    x (powR LL PD.p s (redU PD.p s uZ) (powR LL PD.p s (redU PD.p s j.1) ζ))
  rw [powR_powR, powR_powR, mul_comm]

theorem gamInv_holds (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (T : LocLat G Qp LL O) (c : ZMod n) :
    ∀ (s : ℕ) (f : Amb LL (KsW W s) (Dc W T c)), (levW W uZ ιZ s).Inv f →
      (levW W uZ ιZ s).Inv ((levW W uZ ιZ s).γ f) := by
  intro s f hf j
  show grd ((levW W uZ ιZ s).τ j) ((levW W uZ ιZ s).a j) (grd (levW W uZ ιZ s).σ (levW W uZ ιZ s).u f) =
    grd (levW W uZ ιZ s).σ (levW W uZ ιZ s).u f
  rw [Pf_LvGam_grd_comm _ _ _ _ (Pf_LvGam_στ uZ ιZ s j)]
  exact congrArg (grd (levW W uZ ιZ s).σ (levW W uZ ιZ s).u) (hf j)

theorem Pf_LvGam_coeff_neg {Ks : Type} [CommRing Ks] (x : PowerSeries Ks) (k : ℕ) :
    (HahnSeries.ofPowerSeries ℤ Ks x).coeff (Int.negSucc k) = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
  simp

theorem gamRho_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (c : ZMod n)
    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (hK : W.gamK = W.gam)
    (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL))) :
    ∀ (s : ℕ) (a : PowerSeries O),
      grdB (levW W uZ ιZ s).σ (levW W uZ ιZ s).u (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)) =
        HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s ((baseIdOf hR).Bs.γ a)) := by
  intro s a
  refine HahnSeries.ext (funext fun i => ?_)
  change algebraMap LL (KsW W s) (((levW W uZ ιZ s).u ^ i : LLˣ) : LL) *
    (levW W uZ ιZ s).σ ((HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff i) = _
  rcases i with k | k
  · rw [Int.ofNat_eq_natCast, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff]
    funext ζ
    have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) :=
      (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
    have hv : ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gamK : O) -
        (((redU PD.p s uZ : (ZMod (PD.p ^ (s + 1)))ˣ) : ZMod (PD.p ^ (s + 1))).val : LL)) := by
      rw [hK]
      exact huZ (s + 1)
    have hL := lev_Γ W.gamK c ζ ((powR LL PD.p s (redU PD.p s uZ) ζ : Rs LL PD.p s) : LL) (s + 1) _
      hprim hv rfl (fun _ => (baseIdOf hR).ι a)
    have hR1 : PowerSeries.coeff k (rhoL hR c s ((baseIdOf hR).Bs.γ a)) ζ =
        PowerSeries.coeff k (W.lev c ζ (W.γA W.gamK (fun _ => (baseIdOf hR).ι a))) := by
      rw [rhoL, RingHom.comp_apply, coeff_psPi]
      show PowerSeries.coeff k (W.lev c ζ (fun _ => (baseIdOf hR).ι ((baseIdOf hR).Bs.γ a))) = _
      rw [(baseIdOf hR).ι_γ a]
      rfl
    have hL1 : PowerSeries.coeff k (rhoL hR c s a) (powR LL PD.p s (redU PD.p s uZ) ζ) =
        PowerSeries.coeff k (W.lev c ((powR LL PD.p s (redU PD.p s uZ) ζ : Rs LL PD.p s) : LL)
          (fun _ => (baseIdOf hR).ι a)) := by
      rw [rhoL, RingHom.comp_apply, coeff_psPi]
      rfl
    rw [hR1, hL, PowerSeries.coeff_rescale, ← hL1, hK]
    show (((levW W uZ ιZ s).u ^ (k : ℤ) : LLˣ) : LL) *
      PowerSeries.coeff k (rhoL hR c s a) (powR LL PD.p s (redU PD.p s uZ) ζ) = _
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  · rw [Pf_LvGam_coeff_neg, Pf_LvGam_coeff_neg, map_zero, mul_zero]

end Formalism.MainNotions.N.Ln03.Pf
