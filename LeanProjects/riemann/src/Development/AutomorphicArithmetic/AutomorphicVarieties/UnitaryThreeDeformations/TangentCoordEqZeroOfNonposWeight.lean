import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ConjugatePreservesWeightFiltration
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Origin
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ConjPushMat

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem coeff_single_mul {O σ : Type} [CommRing O] (f g : MvPowerSeries σ O) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
        MvPowerSeries.coeff (Finsupp.single i 1) f * MvPowerSeries.constantCoeff g := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map, Finset.Nat.antidiagonal_succ]
  simp

private noncomputable def tan0 {O σ : Type} [CommRing O] [Fintype σ] (d : σ → O) :
    MvPowerSeries σ O →ₐ[O] DualNumber O where
  toFun f := TrivSqZeroExt.inl (MvPowerSeries.constantCoeff f) +
    TrivSqZeroExt.inr (∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * d i)
  map_one' := by
    classical
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [MvPowerSeries.coeff_one]
  map_mul' f g := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [DualNumber.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, add_zero, coeff_single_mul,
        Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' f g := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [add_mul, Finset.sum_add_distrib]
  commutes' a := by
    classical
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [MvPowerSeries.algebraMap_apply, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [MvPowerSeries.algebraMap_apply, TrivSqZeroExt.algebraMap_eq_inl, MvPowerSeries.coeff_C]

private theorem tangent_point_fst {O σ : Type} [CommRing O] [Fintype σ] (d : σ → O) (f : MvPowerSeries σ O) :
    (tan0 d f).fst = MvPowerSeries.constantCoeff f := by
  simp [tan0]

private theorem tangent_point_snd {O σ : Type} [CommRing O] [Fintype σ] (d : σ → O) (f : MvPowerSeries σ O) :
    (tan0 d f).snd = ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * d i := by
  simp [tan0]

private theorem dual_local {O : Type} [CommRing O] [IsLocalRing O] : IsLocalRing (DualNumber O) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

private theorem exists_tan {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R)
    (h0 : W.HasOrigin) (d : W.σ → O)
    (hd : ∀ f, W.π f = 0 → ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * d i = 0) :
    ∃ τ : R →ₐ[O] DualNumber O, ∀ f, τ (W.π f) = tan0 d f := by
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker W.π) (tan0 d) fun f hf => ?_).comp
    (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom, fun f => ?_⟩
  · exact TrivSqZeroExt.ext ((tangent_point_fst d f).trans (h0 f hf)) ((tangent_point_snd d f).trans (hd f hf))
  · have : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π f) = Ideal.Quotient.mk _ f := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
    erw [this]
    rfl

theorem UpperTheory.V.UnitaryThreeInertia.tangent_coord_eq_zero_of_nonpos_weight :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.VanE → ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    ∀ (W : WPres O ℤ R), F.Adapted u W → ∀ j : ℤ, j ≤ 0 → ∀ d : W.σ → O, (∀ i, W.wt i ≠ j → d i = 0) →
      (∀ f, W.π f = 0 → ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * d i = 0) → d = 0 := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hV g₁ hg R _ _ _ u hu W hW j hj d hdw hd
  classical
  obtain ⟨h0, hor⟩ := hasOrigin F hF g₁ hg u hu W hW
  obtain ⟨τ, hτ⟩ := exists_tan W h0 d hd
  haveI : IsLocalRing (DualNumber O) := dual_local
  have hfst : ∀ x, (τ x).fst = W.origin h0 x := fun x => by
    obtain ⟨f, rfl⟩ := W.surj x
    rw [hτ, tangent_point_fst, WPres.origin_π]
  haveI : IsLocalHom τ := ⟨fun x hx => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hfst] at hx
    by_contra hn
    have h1 : res O O (W.origin h0 x) = 0 := by
      rw [res_map, res_eq_zero_iff]; exact hn
    exact (res_eq_zero_iff O O _).1 h1 hx⟩
  have hr : push τ u = F.rz (DualNumber O) := by
    refine eq_rz_of_vanE F hF hV g₁ hg j hj _ (isPt_push F τ g₁ u hu.pt) (fun g a b => ?_) (fun g a b _ hab => ?_)
    · rw [← hor]
      exact hfst _
    · have hm : (u g).mat a b ∈ W.part (wt a b) := by
        rw [hW.part]; exact entry_mem u g a b
      obtain ⟨f, hf, e⟩ := hm
      have e' : W.π f = (u g).mat a b := e
      show (τ ((u g).mat a b)).snd = 0
      rw [← e', hτ, tangent_point_snd]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : W.wt i = j
      · rw [hf _ (by rw [Finsupp.weight_single, one_smul, hi]; exact hab.symm), zero_mul]
      · rw [hdw i hi, mul_zero]
  funext i
  obtain ⟨g, a, b, -, -, hz⟩ := hW.var i
  have h1 : τ (W.z i) = 0 := by
    have h2 : τ ((u g).mat a b) = (F.rz (DualNumber O) g).mat a b := by rw [← hr]; rfl
    rw [hz, map_sub, h2, sub_eq_zero]
    exact (τ.commutes _).symm
  have h3 : (τ (W.z i)).snd = d i := by
    rw [WPres.z, hτ, tangent_point_snd, Finset.sum_eq_single i]
    · simp [MvPowerSeries.coeff_X]
    · intro k _ hk
      rw [MvPowerSeries.coeff_X, if_neg, zero_mul]
      intro e
      exact hk (Finsupp.single_left_injective one_ne_zero e)
    · simp
  rw [← h3, h1]
  rfl
