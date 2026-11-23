import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfL

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}
    (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

include hπ0 hΔπ γ0 in
theorem framepf_hhx_ι_Δ (i : ZMod n) (g : PowerSeries O) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γA δ (framepf_ι π' i g) = framepf_ι π' i g := by
  have h := framepf_ι_letγ π' i (hπ0 i) (W.γ₀ δ) (γ0 δ hδ) PowerSeries.X (by simp)
    (by rw [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i))];
        exact congrFun (hΔπ δ hδ) i) g
  rw [PowerSeries.X_subst] at h
  exact h

include hπ0 hΔπ γ0 in
theorem framepf_hhx_vec_mem (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) :
    framepf_vec Bs π' (c - 1) H k ∈ NcS W T (c - 1) := by
  unfold framepf_vec
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [mem_NcS]
  obtain ⟨hN, hΔ⟩ := Bs.mem m
  refine ⟨(W.N T).smul_mem _ hN, fun δ hδ => ?_, ?_⟩
  · rw [gradNPf_γD_smul, framepf_hhx_ι_Δ π' hπ0 hΔπ γ0 _ _ δ hδ, hΔ δ hδ]
  · rw [smul_smul, framepf_letE_ι π' (c - 1) hπ0]

theorem framepf_hhx_mem (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (ℓ : LcQ W T π' c) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ ∈ NcS W T (c - 1) := by
  unfold framepf_hh
  rw [LinearMap.comp_apply, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (framepf_hhx_vec_mem Bs π' c hπ0 hΔπ γ0 H k)

include hπ0 in
theorem framepf_hhx_vec_pow (i : ZMod n) (Hm : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (M : ℕ)
    (k : Fin Bs.r) :
    framepf_vec Bs π' i ((PowerSeries.X : PowerSeries O) ^ M • Hm) k =
      π' ^ M • framepf_vec Bs π' i Hm k := by
  induction M with
  | zero => rw [pow_zero, pow_zero, one_smul, one_smul]
  | succ M ih => rw [pow_succ', mul_smul, framepf_vec_X_smul Bs π' i hπ0, ih, smul_smul, ← pow_succ']

theorem framepf_hhx_apply (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (ℓ : LcQ W T π' c) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ =
      ∑ k, framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu ℓ k • framepf_vec Bs π' (c - 1) H k := by
  unfold framepf_hh
  rw [LinearMap.comp_apply, Fintype.linearCombination_apply]
  rfl

theorem framepf_hhx_γ (Gs : PowerSeries O) (hGs0 : PowerSeries.constantCoeff Gs = 0)
    (hGs : W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) Gs)
    (Γ : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (hΓ : ∀ m, W.γD T W.gam ((letE (c - 1) : LetA O n) • Bs.b m) = framepf_vec Bs π' (c - 1) Γ m)
    (H Km : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (M : ℕ)
    (hH : Γ * H.map (PowerSeries.subst Gs) - H = (PowerSeries.X : PowerSeries O) ^ M • Km)
    (ℓ : LcQ W T π' c) :
    W.γD T W.gam (framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ) - framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ ∈
      PiNS W T π' M := by
  have e : W.γD T W.gam (framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ) -
      framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ = π' ^ M • framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu Km ℓ := by
    rw [framepf_hhx_apply, framepf_hhx_apply, map_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, framepf_γ_vec Bs π' (c - 1) hπ0 Gs hGs0 hGs Γ hΓ, sub_eq_iff_eq_add.1 hH,
      framepf_vec_add Bs π' (c - 1) hπ0, framepf_hhx_vec_pow Bs π' hπ0, smul_add, add_sub_cancel_right,
      smul_comm]
  have hm := (mem_NcS W T (c - 1) _).1 (framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu Km ℓ)
  rw [e, mem_PiNS]
  refine ⟨⟨_, hm.1, rfl⟩, fun δ hδ => ?_⟩
  rw [gradNPf_γD_smul, map_pow, hΔπ δ hδ, hm.2.1 δ hδ]

theorem framepf_hhx_mod (lσ : O) (H Km : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (hH : H = PowerSeries.C lσ • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) • Km)
    (z : W.DD T) (hz : z ∈ NcS W T (c - 1)) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H (mkL W T π' c z hz) - lσ • z ∈ PiNS W T π' 1 := by
  set ℓ := mkL W T π' c z hz with hℓ
  have hv : ∀ k, framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0
      ⟨_, framepf_hhx_vec_mem Bs π' c hπ0 hΔπ γ0 H k⟩ = lσ • Pi.single k 1 := by
    intro k
    have e := framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0 ⟨_, framepf_hhx_vec_mem Bs π' c hπ0 hΔπ γ0 H k⟩
      (fun m => H m k) rfl
    funext m
    rw [framepf_coordL_apply, e, hH]
    by_cases hmk : m = k
    · subst hmk; simp
    · simp [Matrix.one_apply_ne hmk, Pi.single_eq_of_ne hmk]
  have hsum : (⟨_, framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ⟩ : ↥(NcS W T (c - 1))) =
      ∑ k, framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu ℓ k •
        (⟨_, framepf_hhx_vec_mem Bs π' c hπ0 hΔπ γ0 H k⟩ : ↥(NcS W T (c - 1))) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact framepf_hhx_apply Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ
  have key := (framepf_coordL_ker Bs π' c hπ0 hΔπ hR2 γ0 hu
    (⟨_, framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ⟩ - lσ • ⟨z, hz⟩)).1 (by
      rw [map_sub, map_smul, hsum, map_sum, ← framepf_Lbas_mk Bs π' c hπ0 hΔπ hR2 γ0 hu ⟨z, hz⟩]
      simp only [map_smul, hv]
      have : Submodule.Quotient.mk (⟨z, hz⟩ : ↥(NcS W T (c - 1))) = ℓ := rfl
      rw [this, sub_eq_zero]
      funext m
      simp [Finset.sum_apply, Pi.single_apply, mul_comm])
  exact key

end Local

end Formalism.MainNotions.N.Ln34

end
