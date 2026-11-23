import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

section Grd

variable {LL Ks : Type} [Field LL] [CommRing Ks] [Algebra LL Ks]

theorem Pf_LvEquiv_grdB_supp (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (x : HahnSeries ℤ Ks) :
    (grdB τ a x).support ⊆ x.support := by
  intro i hi h0
  apply hi
  change algebraMap LL Ks ((a ^ i : LLˣ) : LL) * τ (x.coeff i) = 0
  rw [h0, map_zero, mul_zero]

theorem Pf_LvEquiv_grdB_mul (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (x y : HahnSeries ℤ Ks) :
    grdB τ a (x * y) = grdB τ a x * grdB τ a y := by
  ext i
  rw [HahnSeries.coeff_mul (x := grdB τ a x)]
  change algebraMap LL Ks ((a ^ i : LLˣ) : LL) * τ ((x * y).coeff i) = _
  rw [HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
  symm
  refine (Finset.sum_subset (fun ij h => ?_) (fun ij hb hs => ?_)).trans (Finset.sum_congr rfl ?_)
  · rw [Finset.mem_antidiagonal] at h ⊢
    exact ⟨Pf_LvEquiv_grdB_supp τ a x h.1, Pf_LvEquiv_grdB_supp τ a y h.2.1, h.2.2⟩
  · rw [Finset.mem_antidiagonal] at hb hs
    by_cases h1 : ij.1 ∈ (grdB τ a x).support
    · by_cases h2 : ij.2 ∈ (grdB τ a y).support
      · exact absurd ⟨h1, h2, hb.2.2⟩ hs
      · have h0 : (grdB τ a y).coeff ij.2 = 0 := by
          by_contra hc
          exact h2 hc
        rw [h0, mul_zero]
    · have h0 : (grdB τ a x).coeff ij.1 = 0 := by
        by_contra hc
        exact h1 hc
      rw [h0, zero_mul]
  intro ij hij
  obtain ⟨-, -, hsum⟩ := Finset.mem_antidiagonal.1 hij
  change (algebraMap LL Ks ((a ^ ij.1 : LLˣ) : LL) * τ (x.coeff ij.1)) *
    (algebraMap LL Ks ((a ^ ij.2 : LLˣ) : LL) * τ (y.coeff ij.2)) = _
  rw [map_mul τ, ← hsum, zpow_add, Units.val_mul, map_mul]
  ring

theorem Pf_LvEquiv_grdB_one (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) : grdB τ a (1 : HahnSeries ℤ Ks) = 1 := by
  ext i
  change algebraMap LL Ks ((a ^ i : LLˣ) : LL) * τ ((1 : HahnSeries ℤ Ks).coeff i) = _
  simp only [HahnSeries.coeff_one]
  split_ifs with h
  · subst h
    simp
  · simp

end Grd

theorem Pf_LvEquiv_cancel {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (X Y Z : A)
    (E₁ E₂ : M) (hX : IsUnit X) (hinv : Z * Y = 1) (key : Y • E₁ = X • E₂) :
    Ring.inverse X • E₁ = Z • E₂ := by
  calc Ring.inverse X • E₁ = (Ring.inverse X * (Z * Y)) • E₁ := by rw [hinv, mul_one]
    _ = (Ring.inverse X * Z) • (Y • E₁) := by rw [smul_smul, mul_assoc]
    _ = (Ring.inverse X * Z) • (X • E₂) := by rw [key]
    _ = Z • E₂ := by
      rw [smul_smul, mul_comm (Ring.inverse X) Z, mul_assoc, Ring.inverse_mul_cancel _ hX, mul_one]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

open Classical in

def Pf_LvEquiv_Φ (W : LocWach PD LL O v n) (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] :
    KsW W s ⊗[LL] D ≃ₗ[LL] (Rs LL PD.p s → D) :=
  (TensorProduct.comm LL (KsW W s) D).trans (TensorProduct.piScalarRight LL LL D (Rs LL PD.p s))

theorem Pf_LvEquiv_Φ_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (f : Rs LL PD.p s → D) : Pf_LvEquiv_Φ W s D (toKsD W s D f) = f := by
  simp only [Pf_LvEquiv_Φ, toKsD, LinearEquiv.trans_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply]
  rw [← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem Pf_LvEquiv_Φ_rTensor (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (a : (ZMod (PD.p ^ (s + 1)))ˣ) (z : KsW W s ⊗[LL] D) :
    Pf_LvEquiv_Φ W s D (LinearMap.rTensor D (precomp LL PD.p s a).toLinearMap z) =
      fun ζ => Pf_LvEquiv_Φ W s D z (powR LL PD.p s a ζ) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    funext ζ
    simp
  | tmul k d =>
    funext ζ
    simp [Pf_LvEquiv_Φ, TensorProduct.piScalarRightHom_tmul, precomp_apply]
  | add z z' hz hz' =>
    funext ζ
    rw [map_add, map_add, hz, hz', map_add]
    rfl

variable {T : LocLat G Qp LL O} {c : ZMod n}

theorem Pf_LvEquiv_grd_expN (Lb : LevB W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O)
    (hT : IsCrys PD T.ρ)
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL)
      (m a : ℕ), IsPrimitiveRoot ζ (PD.p ^ m) →
      (m : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k =
        (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hK : W.gamK = W.gam)
    (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL)))
    (s : ℕ) (x : ↥(W.N T)) :
    grd (levW W uZ ιZ s).σ (levW W uZ ιZ s).u (expN Lb s T c x) =
      expN Lb s T c ⟨W.γD T W.gamK (x : W.DD T), W.N_Γ T W.gamK _ x.2⟩ := by
  apply HahnModule.ext
  funext i
  change (((levW W uZ ιZ s).u ^ i : LLˣ) : LL) •
      LinearMap.rTensor (Dc W T c) (precomp LL PD.p s (redU PD.p s uZ)).toLinearMap
        (coefN Lb s T c x i) = coefN Lb s T c ⟨W.γD T W.gamK (x : W.DD T), W.N_Γ T W.gamK _ x.2⟩ i
  apply (Pf_LvEquiv_Φ W s (Dc W T c)).injective
  rw [LinearEquiv.map_smul, Pf_LvEquiv_Φ_rTensor]
  simp only [coefN, Pf_LvEquiv_Φ_toKsD]
  funext ζ
  apply Subtype.ext
  simp only [Pi.smul_apply, Submodule.coe_smul]
  have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) :=
    (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
  have hv : ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gamK : O) -
      (((redU PD.p s uZ : (ZMod (PD.p ^ (s + 1)))ˣ) : ZMod (PD.p ^ (s + 1))).val : LL)) := by
    rw [hK]
    exact huZ (s + 1)
  rw [levB_Γ T hT W.gamK c ζ ((powR LL PD.p s (redU PD.p s uZ) ζ : Rs LL PD.p s) : LL) (s + 1) _
    hprim hv rfl x]
  congr 1
  rw [hK, Units.val_zpow_eq_zpow_val]
  rfl

theorem equiv_holds {C : Coord W (baseIdOf hR) T} {ell : ℕ} {Λ κ : PowerSeries O} {r : ℕ}
    {lam : Fin r → Dc W T c} (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (j M g η : ℕ)
    (kind : ℕ → Kind) (b : ℕ → ℕ) (hT : IsCrys PD T.ρ)
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL)
      (m a : ℕ), IsPrimitiveRoot ζ (PD.p ^ m) →
      (m : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k =
        (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hs1 : W.s = 1) (hl : 5 ≤ PD.p)
    (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL))) :
    (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Equiv := by
  have hK : W.gamK = W.gam := W.gamK_eq_one hs1 (by omega)
  intro s _ w hw hγ
  show locM Lb C Hy.delta ell Λ κ Hy.kap Hy.expSemi Hy.locInv ⟨(latOf C).γ c w, hγ⟩ =
    gEL Hy (locM Lb C Hy.delta ell Λ κ Hy.kap Hy.expSemi Hy.locInv ⟨w, hw⟩)
  apply prL_inj
  intro s' hs'
  rw [prL_gEL Hy s' hs', prL_of_lt s' hs', prL_of_lt s' hs']
  have hmL : C.t c (κ • (latOf C).γ c w) ∈ W.N T := Hy.kap _ hγ
  have hmR : C.t c (κ • w) ∈ W.N T := Hy.kap _ hw
  change Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ)) •
      expN Lb s' T c ⟨C.t c (κ • (latOf C).γ c w), hmL⟩ =
    (levW W uZ ιZ s').γ (Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ)) •
      expN Lb s' T c ⟨C.t c (κ • w), hmR⟩)
  by_cases hX : IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ))
  · rw [Level.γ, graded_semilinear_holds,
      Pf_LvEquiv_grd_expN Lb uZ ιZ hT levB_Γ hK huZ s' ⟨C.t c (κ • w), hmR⟩]
    apply Pf_LvEquiv_cancel _ (HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' ((baseIdOf hR).Bs.γ κ)))
      _ _ _ hX
    · rw [← Hy.gamRho s' κ, ← Pf_LvEquiv_grdB_mul, Ring.inverse_mul_cancel _ hX, Pf_LvEquiv_grdB_one]
    · have hN : W.γD T W.gamK (C.t c (κ • w)) ∈ W.N T := W.N_Γ T W.gamK _ hmR
      rw [← Hy.expSemi s' ((baseIdOf hR).Bs.γ κ) ⟨_, hmL⟩ ((W.N T).smul_mem _ hmL),
        ← Hy.expSemi s' κ ⟨_, hN⟩ ((W.N T).smul_mem _ hN)]
      congr 1
      apply Subtype.ext
      change (baseIdOf hR).d ((baseIdOf hR).Bs.γ κ) • C.t c (κ • (latOf C).γ c w) =
        (baseIdOf hR).d κ • W.γD T W.gamK (C.t c (κ • w))
      rw [← t_γ, (latOf C).γ_semi, C.t_smul, C.t_smul]
      exact smul_comm _ _ _
  · rw [Ring.inverse_non_unit _ hX, zero_smul, zero_smul, map_zero]

theorem Pf_LvEquiv_unit_lam (hR : Ring9 W) (c : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (s : ℕ)
    (hp : ∀ s' < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s ((baseIdOf hR).Bs.p s')))) :
    IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell))) := by
  rw [Formalism.ExponentWindows.abelian₂, map_prod, map_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one ?_
  intro x hx
  rw [map_pow, map_pow]
  exact (hp x (Finset.mem_range.1 hx)).pow _

theorem locLIs_holds {C : Coord W (baseIdOf hR) T} {ell : ℕ} {Λ κ : PowerSeries O} {r : ℕ}
    {lam : Fin r → Dc W T c} (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (j M g η : ℕ)
    (kind : ℕ → Kind) (b : ℕ → ℕ) (H : ℕ → ℕ) (hΛ : Λ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell)
    (k1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (unitsAt : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt) :
    (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).LocLIs lam := by
  subst hΛ
  intro s hs y
  have hp : ∀ s' < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s ((baseIdOf hR).Bs.p s'))) := by
    intro s' hs'
    by_cases h : s' = s
    · subst h
      obtain ⟨ε, hε⟩ := k1b s' hs
      have hε' : rhoL hR c s' ((baseIdOf hR).Bs.p s') = (ε : PowerSeries (KsW W s')) * PowerSeries.X :=
        hε
      rw [hε', map_mul, HahnSeries.ofPowerSeries_X]
      refine (ε.isUnit.map _).mul (isUnit_iff_exists_inv.2 ⟨HahnSeries.single (-1 : ℤ) 1, ?_⟩)
      rw [HahnSeries.single_mul_single]
      simp
    · exact ((unitsAt s hs).2 s' hs' h).map _
  have hU := Pf_LvEquiv_unit_lam hR c ell H s hp
  show prL s (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell •
      locLM Hy.delta ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) lam Hy.loclInv y) =
    ∑ k, HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s (y k)) • cstD (KsW W s) (lam k)
  rw [prL_smul, prL_of_lt s hs]
  change HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell)) •
      locLF (hR := hR) (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) lam s y = _
  rw [locLF, smul_smul, Ring.mul_inverse_cancel _ hU, one_smul]

end Formalism.MainNotions.N.Ln03.Pf
