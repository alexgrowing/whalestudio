import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TriangularConditionAtLOfFirstOrderDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LocAtDeformD
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LocAtDeformU
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MapDiagonalRepMatrixEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.EntInMulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ZetaReducibleRepEqSubInvAndIsUnit

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia.Tan

private theorem mem_max_dual {K : Type} [Field K] (x : DualNumber K) :
    x ∈ maximalIdeal (DualNumber K) ↔ x.fst = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not]

private theorem max_sq_dual {K : Type} [Field K] :
    maximalIdeal (DualNumber K) * maximalIdeal (DualNumber K) = ⊥ := by
  rw [eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [mem_max_dual] at hx hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]

private theorem isCO_dual (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] :
    IsCO O (DualNumber (ResidueField O)) := by
  have : Finite (DualNumber (ResidueField O)) := inferInstanceAs (Finite (_ × _))
  exact
    { complete := inferInstance
      isLocalHom := ⟨fun a ha => by
        rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] at ha
        exact (isUnit_map_iff (residue O) a).1 ha⟩
      res_surj := fun x => by
        obtain ⟨a, ha⟩ := residue_surjective x.fst
        refine ⟨a, ?_⟩
        rw [mem_max_dual, TrivSqZeroExt.fst_sub, ← ha, sub_eq_zero]
        rfl }

private theorem map_eq_zero_of_cc {O A σ : Type} [CommRing O] [CommRing A] [Fintype σ]
    (φ : MvPowerSeries σ O →+* A) (hφ : ∀ i, φ (MvPowerSeries.X i) = 0) (p : MvPowerSeries σ O)
    (hp : MvPowerSeries.constantCoeff p = 0) : φ p = 0 := by
  classical
  have hc : ∀ n : σ →₀ ℕ, n ≠ 0 → ∃ i, n i ≠ 0 := fun n hn => by
    by_contra h
    push Not at h
    exact hn (Finsupp.ext h)
  choose c hc using hc
  let q : σ → MvPowerSeries σ O := fun i n =>
    if h : n ≠ 0 then (if c n h = i then MvPowerSeries.coeff n p else 0) else 0
  have hq : ∀ i n, MvPowerSeries.coeff n (q i) =
      if h : n ≠ 0 then (if c n h = i then MvPowerSeries.coeff n p else 0) else 0 := fun _ _ => rfl
  have hs : p = ∑ i, q i := by
    ext n
    rw [map_sum]
    simp only [hq]
    by_cases h : n ≠ 0
    · simp [dif_pos h]
    · simp only [dif_neg h, Finset.sum_const_zero]
      push Not at h
      subst h
      simpa using hp
  rw [hs, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : MvPowerSeries.X i ∣ q i := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [hq]
    split_ifs with h1 h2
    · exact absurd (h2 ▸ hm) (hc m h1)
    · rfl
    · rfl
  obtain ⟨r, hr⟩ := this
  rw [hr, map_mul, hφ, zero_mul]

private theorem map_eq_cc {O A σ : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype σ]
    (φ : MvPowerSeries σ O →ₐ[O] A) (hφ : ∀ i, φ (MvPowerSeries.X i) = 0) (p : MvPowerSeries σ O) :
    φ p = algebraMap O A (MvPowerSeries.constantCoeff p) := by
  have h := map_eq_zero_of_cc (φ : MvPowerSeries σ O →+* A) hφ
    (p - algebraMap O _ (MvPowerSeries.constantCoeff p)) (by simp [MvPowerSeries.algebraMap_apply])
  rw [map_sub, sub_eq_zero] at h
  exact h.trans (φ.commutes _)

private theorem diagonal_rep_matrix_eq {G C : Type} [Group G] [CommRing C] (η : G →* ℤˣ) (Ψ : G →* Cˣ) (g : G) :
    (r0 η Ψ g).mat = Matrix.diagonal fun i => ((Ψ g ^ wt1 i : Cˣ) : C) := rfl

private theorem exists_norm {G C : Type} [Group G] [CommRing C] (η : G →* ℤˣ) (Ψ : G →* Cˣ) (c g₁ : G)
    (h2 : IsUnit (2 : C)) (hM : Marks η Ψ c g₁) (j : ℤ) (γ : G → Matrix (Fin 3) (Fin 3) C)
    (hw : ∀ g, γ g ∈ gw C j) (hc : IsCoc (r0 η Ψ) γ) :
    ∃ Y ∈ gw C j, NormCoc c g₁ (r0 η Ψ) (γ - cob (r0 η Ψ) Y) := by
  have hne : ¬ η c = 1 := by rw [hM.ηc]; decide
  have hΨs : Ψ (gstar c g₁) = (Ψ g₁)⁻¹ := by simp [gstar, hM.Ψc]
  have hηs : η (gstar c g₁) = 1 := by simp [gstar, hM.ηc, hM.ηg]
  have h1 : γ 1 = 0 := by
    have := hc 1 1
    rw [mul_one, map_one] at this
    simpa using this
  have hcc : ∀ a b, γ c a b = γ c b.rev a.rev := fun a b => by
    have := congrFun (congrFun (hc c c) a) b
    rw [hM.csq, h1, Matrix.add_apply, adRep_baseLift_apply, if_neg hne, hM.Ψc] at this
    simp only [_root_.one_zpow, Units.val_one, one_mul, Matrix.zero_apply] at this
    linear_combination -this
  obtain ⟨hz, hu⟩ := zeta_reducible_rep_eq_sub_inv_and_isUnit η Ψ c g₁ hM
  rw [hz] at hu
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  obtain ⟨w, hw2⟩ := h2.exists_left_inv
  have hab : ((Ψ g₁ : Cˣ) : C) * (((Ψ g₁)⁻¹ : Cˣ) : C) = 1 := Units.mul_inv _
  set p : C := ((Ψ g₁ : Cˣ) : C) with hp
  set q : C := (((Ψ g₁)⁻¹ : Cˣ) : C) with hq
  set s : C := -(v * (γ g₁ 0 1 - γ (gstar c g₁) 0 1)) with hs
  set t : C := v * (γ g₁ 1 0 * p - γ (gstar c g₁) 1 0 * q) with ht
  have hw' : ∀ g a b, wt a b ≠ j → γ g a b = 0 := hw
  refine ⟨!![w * γ c 0 0, s, w * γ c 0 2; t, w * γ c 1 1, γ c 0 1 - s; w * γ c 2 0, γ c 1 0 - t, w * γ c 0 0], ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have e1 := fun g => hw' g a b hab
    have e2 : γ c b.rev a.rev = 0 := by rw [← hcc, e1]
    have e3 : ∀ g, γ g b.rev a.rev = 0 := fun g => hw' g _ _ (by
      have : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
      rwa [this])
    fin_cases a <;> fin_cases b <;> simp [Fin.rev] at e1 e2 e3 <;> simp [hs, ht, e1, e2, e3]
  · ext a b
    rw [Pi.sub_apply, cob, Matrix.sub_apply, Matrix.sub_apply, adRep_baseLift_apply, if_neg hne, hM.Ψc]
    have e := hcc a b
    fin_cases a <;> fin_cases b <;> simp [Fin.rev] at e ⊢ <;>
      first | linear_combination (-γ c 0 0) * hw2 | linear_combination (-γ c 0 2) * hw2 | linear_combination (-γ c 1 1) * hw2 | linear_combination (-γ c 2 0) * hw2 | linear_combination e | linear_combination e - γ c 0 0 * hw2
  · have w0 : wt 0 1 = 1 := by decide
    have w1 : wt1 1 = 0 := by decide
    simp only [zvar, diagonal_rep_matrix_eq, Matrix.sub_apply, Matrix.mul_diagonal, Pi.sub_apply,
      cob, adRep_baseLift_apply, hηs, hM.ηg, if_true, hΨs, w0, w1, zpow_one, zpow_zero, inv_inv, Units.val_one]
    simp only [Matrix.of_apply, Matrix.cons_val, ← hp, ← hq]
    linear_combination (-(γ g₁ 0 1 - γ (gstar c g₁) 0 1)) * hv + (p - q) * hs
  · have w0 : wt 1 0 = -1 := by decide
    have w1 : wt1 0 = 1 := by decide
    simp only [zvar, diagonal_rep_matrix_eq, Matrix.sub_apply, Matrix.mul_diagonal, Pi.sub_apply,
      cob, adRep_baseLift_apply, hηs, hM.ηg, if_true, hΨs, w0, w1, zpow_one, _root_.zpow_neg_one, inv_inv, Units.val_one]
    simp only [Matrix.of_apply, Matrix.cons_val, ← hp, ← hq]
    linear_combination (-(γ g₁ 1 0 * p - γ (gstar c g₁) 1 0 * q)) * hv - (p - q) * ht

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
  {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι]
  (F : Frame O G Γ ι)

private theorem val_ext {k : Type} [CommRing k] {j : ℤ} {X Y : Gb k j} (h : X.val = Y.val) : X = Y :=
  Subtype.ext h

private theorem psibar_lc (hF : F.Ok) : IsLocallyConstant F.Ψbar := by
  have h := (hF.Ψ_cont 1).comp (Ideal.Quotient.lift (maximalIdeal O ^ 1) (residue O)
    (fun a ha => by rwa [pow_one, ← residue_eq_zero_iff] at ha))
  exact IsLocallyConstant.desc F.Ψbar Units.val h Units.val_injective

private theorem gbar_congr (j : ℤ) {g h : Γ} (h1 : F.η g = F.η h) (h2 : F.Ψbar g = F.Ψbar h)
    (Y : Gb (ResidueField O) j) : F.gbar j g Y = F.gbar j h Y := by
  apply val_ext
  ext a b
  rw [gRep_val, gRep_val, adRep_baseLift_apply, adRep_baseLift_apply, h1, h2]

private theorem commAlgFunctorCoboundaryZero_mem_cocyclesOne (hF : F.Ok) (j : ℤ) (Y : Gb (ResidueField O) j) : d0 (F.gbar j) Y ∈ F.selmerCocycles j := by
  have hlc : IsLocallyConstant (d0 (F.gbar j) Y) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [hF.η_cont.eventually_eq x, (psibar_lc F hF).eventually_eq x] with y h1 h2
    rw [amitsur_d0_apply, amitsur_d0_apply, gbar_congr F j h1 h2]
  have hcoc : ∀ g h, d0 (F.gbar j) Y (g * h) = d0 (F.gbar j) Y g + F.gbar j g (d0 (F.gbar j) Y h) := by
    intro g h
    simp only [amitsur_d0_apply, map_mul, map_sub, Module.End.mul_apply]
    abel
  refine ⟨⟨hlc.continuous, hcoc⟩, ?_⟩
  rw [SetLike.mem_coe, Submodule.mem_iInf]
  intro v
  have hloc : Continuous (F.loc v) := hF.π_cont.comp continuous_subtype_val
  refine ⟨⟨hlc.continuous.comp hloc, fun g h => ?_⟩, fun _ s hs => ?_, fun _ _ => ⟨Y, rfl⟩, fun e e' s hs => ?_⟩
  · have := hcoc (F.loc v g) (F.loc v h)
    rw [← map_mul] at this
    exact this
  · show d0 (F.gbar j) Y (F.loc v s) = 0
    rw [amitsur_d0_apply, gbar_congr F j (h := 1) (hs.1.2.trans (map_one _).symm) (hs.2.trans (map_one _).symm)]
    simp
  · show d0 (F.gbar j) Y (F.loc v s) = 0
    have h1 : F.η (F.loc v s) = 1 := hF.η_I v (e ▸ Set.mem_insert _ _) s hs
    rw [amitsur_d0_apply, sub_eq_zero]
    apply val_ext
    ext a b
    rw [gRep_val, adRep_baseLift_apply, if_pos h1]
    by_cases hab : wt a b = j
    · rw [hab.trans e', zpow_zero, Units.val_one, one_mul]
    · have : Y.val a b = 0 := Y.2 a b hab
      rw [this, mul_zero]

private theorem rz_eq (A : Type) [CommRing A] [Algebra O A] :
    F.rz A = r0 F.η ((Units.map (algebraMap O A).toMonoidHom).comp F.Ψ) := by
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor O (F.Ψ g) : Matrix (Fin 3) (Fin 3) O).map (algebraMap O A) = ((tor A _ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map (algebraMap O A).toMonoidHom) (F.Ψ g) (wt1 i))

private theorem psi_dual (g : Γ) (n : ℤ) :
    ((((Units.map (algebraMap O (DualNumber (ResidueField O))).toMonoidHom).comp F.Ψ) g ^ n :
      (DualNumber (ResidueField O))ˣ) : DualNumber (ResidueField O)) =
      TrivSqZeroExt.inl ((F.Ψbar g ^ n : (ResidueField O)ˣ) : ResidueField O) := by
  have e1 := congrArg Units.val (map_zpow (Units.map (algebraMap O (DualNumber (ResidueField O))).toMonoidHom) (F.Ψ g) n)
  have e2 := congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (F.Ψ g) n)
  refine e1.symm.trans ?_
  exact congrArg TrivSqZeroExt.inl e2

private theorem coc_dual (j : ℤ) (y : Γ → Gb (ResidueField O) j) (hy : y ∈ F.selmerCocycles j) :
    IsCoc (F.rz (DualNumber (ResidueField O))) fun g => (y g).val.map TrivSqZeroExt.inr := by
  intro g h
  ext1 a b
  have e : (y (g * h)).val = (y g).val + adRep (r0 F.η F.Ψbar) g (y h).val := congrArg Gb.val (hy.1.2 g h)
  rw [rz_eq, Matrix.add_apply, adRep_baseLift_apply, psi_dual]
  simp only [Matrix.map_apply]
  rw [e, Matrix.add_apply, adRep_baseLift_apply]
  split_ifs <;> ext <;> simp [mul_comm]

private theorem loc_dual (hF : F.Ok) (hV : F.LocVan) (g₁ : Γ) (j : ℤ) (y : Γ → Gb (ResidueField O) j)
    (hy : y ∈ F.selmerCocycles j) (r : Γ →* GG 3 (DualNumber (ResidueField O)))
    (hr : IsDeform (F.rz _) (fun g => (y g).val.map TrivSqZeroExt.inr) r) (v : ι) :
    F.LocAt v (r.comp (F.loc v)) := by
  haveI := isCO_dual O
  have hz : F.IsPt g₁ (F.rz (DualNumber (ResidueField O))) := isPt_rz F hF g₁
  have hf1 : ∀ x ∈ maximalIdeal (DualNumber (ResidueField O)), x * DualNumber.eps = 0 := fun x hx => by
    rw [mem_max_dual] at hx
    ext <;> simp [hx]
  have hf2 : DualNumber.eps ∈ maximalIdeal (DualNumber (ResidueField O)) := (mem_max_dual _).2 rfl
  have hred : Red (F.ηv v) (F.Ψv v) ((F.rz (DualNumber (ResidueField O))).comp (F.loc v)) :=
    ⟨fun g => rfl, fun g => hz.red (F.loc v g)⟩
  have hzl : F.res1 j v y ∈ F.ZL j v := (Submodule.mem_iInf _).1 hy.2 v
  have ho : ∀ g a b, ∃ o : O, residue O o = (F.res1 j v y g).val a b ∧
      ((y (F.loc v g)).val.map TrivSqZeroExt.inr : Matrix _ _ (DualNumber (ResidueField O))) a b =
        o • DualNumber.eps := fun g a b => by
    obtain ⟨o, ho⟩ := residue_surjective ((y (F.loc v g)).val a b)
    refine ⟨o, ho, ?_⟩
    rw [Matrix.map_apply, ← ho]
    ext
    · simp
    · simp [Algebra.smul_def]
      rfl
  have hd : IsDeform ((F.rz (DualNumber (ResidueField O))).comp (F.loc v))
      (fun g => (y (F.loc v g)).val.map TrivSqZeroExt.inr) (r.comp (F.loc v)) := fun g => hr (F.loc v g)
  by_cases h1 : v = F.vl
  · exact triangular_condition_at_l_of_first_order_deformation F hF hV _ hf1 hf2 j v h1 _ _ _ _ hred (hz.loc v) hzl ho hd
  by_cases h2 : v ∈ F.Sb
  · exact locAt_deform_d F hF hV _ hf1 hf2 j v h2 _ _ _ _ hred (hz.loc v) hzl ho hd
  · exact locAt_deform_u F hF hV _ hf1 hf2 j v (fun h => h.elim h1 h2) _ _ _ _ hred (hz.loc v) hzl ho hd

private theorem norm_dual (g₁ : Γ) (j : ℤ) (y : Γ → Gb (ResidueField O) j)
    (hn : NormCoc F.c g₁ (r0 F.η F.Ψbar) fun g => (y g).val) :
    NormCoc F.c g₁ (F.rz (DualNumber (ResidueField O))) fun g => (y g).val.map TrivSqZeroExt.inr := by
  have hv : ∀ a b, zvar F.c g₁ (F.rz (DualNumber (ResidueField O))) (fun g => (y g).val.map TrivSqZeroExt.inr) a b =
      TrivSqZeroExt.inr (zvar F.c g₁ (r0 F.η F.Ψbar) (fun g => (y g).val) a b) := fun a b => by
    rw [rz_eq, zvar, zvar, diagonal_rep_matrix_eq, diagonal_rep_matrix_eq, diagonal_rep_matrix_eq, diagonal_rep_matrix_eq]
    simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.map_apply]
    rw [psi_dual, psi_dual]
    ext <;> simp [mul_comm]
  refine ⟨?_, by rw [hv, hn.z12, TrivSqZeroExt.inr_zero], by rw [hv, hn.z21, TrivSqZeroExt.inr_zero]⟩
  have : (y F.c).val = 0 := hn.atc
  show (y F.c).val.map _ = 0
  rw [this]
  ext <;> simp

private theorem rz_mat_dual (g : Γ) : (F.rz (DualNumber (ResidueField O)) g).mat =
    Matrix.diagonal fun i => TrivSqZeroExt.inl ((F.Ψbar g ^ wt1 i : (ResidueField O)ˣ) : ResidueField O) := by
  rw [rz_eq, diagonal_rep_matrix_eq]
  congr 1
  funext i
  exact psi_dual F g _

private theorem red_deform {A : Type} [CommRing A] [IsLocalRing A] [Algebra O A] (γ : Γ → Matrix (Fin 3) (Fin 3) A)
    (hγ : ∀ g, EntIn (maximalIdeal A) (γ g)) (r : Γ →* GG 3 A) (hr : IsDeform (F.rz A) γ r) : Red F.η F.Ψ r := by
  refine ⟨fun g => (hr g).1, fun g a b => ?_⟩
  have e0 : (F.rz A g).mat = ((r0 F.η F.Ψ g).mat).map (algebraMap O A) := rfl
  rw [(hr g).2, Matrix.add_mul, Matrix.one_mul, ← e0, add_sub_cancel_left, Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hγ g a k)

private theorem lc_dual (hF : F.Ok) (j : ℤ) (y : Γ → Gb (ResidueField O) j)
    (hy : y ∈ F.selmerCocycles j) (r : Γ →* GG 3 (DualNumber (ResidueField O)))
    (hr : IsDeform (F.rz _) (fun g => (y g).val.map TrivSqZeroExt.inr) r) :
    IsLocallyConstant fun g => (r g).mat := by
  have hlc : IsLocallyConstant y := (IsLocallyConstant.iff_continuous y).2 hy.1.1
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [hlc.eventually_eq x, (psibar_lc F hF).eventually_eq x] with z h1 h2
  rw [(hr z).2, (hr x).2, rz_mat_dual, rz_mat_dual, h2]
  beta_reduce
  rw [h1]

private theorem exists_pt (hF : F.Ok) (hV : F.LocVan) (g₁ : Γ) (j : ℤ) (y : Γ → Gb (ResidueField O) j)
    (hy : y ∈ F.selmerCocycles j) (hn : NormCoc F.c g₁ (r0 F.η F.Ψbar) fun g => (y g).val) :
    ∃ r : Γ →* GG 3 (DualNumber (ResidueField O)), F.IsPt g₁ r ∧
      IsDeform (F.rz _) (fun g => (y g).val.map TrivSqZeroExt.inr) r := by
  haveI := isCO_dual O
  have hz : F.IsPt g₁ (F.rz (DualNumber (ResidueField O))) := isPt_rz F hF g₁
  have hent : ∀ g, EntIn (maximalIdeal (DualNumber (ResidueField O))) ((y g).val.map TrivSqZeroExt.inr) :=
    fun g a b => (mem_max_dual _).2 rfl
  obtain ⟨r, hr⟩ := exists_isDeform (maximalIdeal (DualNumber (ResidueField O))) (F.rz (DualNumber (ResidueField O)))
    (fun g => (y g).val.map TrivSqZeroExt.inr) max_sq_dual hent (coc_dual F j y hy)
  have h1 := red_deform F _ hent r hr
  have h2 := loc_dual F hF hV g₁ j y hy r hr
  have h3 := (isDeform_normalised_iff _ _ _ _ _ hz.norm hr).2 (norm_dual F g₁ j y hn)
  have h4 : UnitaryThreeInertia.AdicCont (maximalIdeal (DualNumber (ResidueField O))) r := fun n =>
    (lc_dual F hF j y hy r hr).comp fun X => X.map (Ideal.Quotient.mk (maximalIdeal _ ^ n))
  exact ⟨r, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hr⟩

private theorem eq_zero_of_coord (hF : F.Ok) (hV : F.LocVan) (g₁ : Γ) {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (u : Γ →* GG 3 R) (hu : F.IsUniv g₁ u) (W : WPres O ℤ R) (g : W.σ → Γ) (a b : W.σ → Fin 3)
    (hW : ∀ i, W.z i = (u (g i)).mat (a i) (b i) - (F.rz R (g i)).mat (a i) (b i))
    (j : ℤ) (y : Γ → Gb (ResidueField O) j)
    (hy : y ∈ F.selmerCocycles j) (hn : NormCoc F.c g₁ (r0 F.η F.Ψbar) fun g => (y g).val)
    (h0 : ∀ i, (y (g i)).val (a i) (b i) = 0) : y = 0 := by
  haveI := isCO_dual O
  obtain ⟨r, hp, hr⟩ := exists_pt F hF hV g₁ j y hy hn
  have key : ∀ (r : Γ →* GG 3 (DualNumber (ResidueField O))) (f : R →ₐ[O] DualNumber (ResidueField O)),
      push f u = r → (∀ i, (r (g i)).mat (a i) (b i) = (F.rz _ (g i)).mat (a i) (b i)) →
      ∀ p, f (W.π p) = algebraMap O _ (MvPowerSeries.constantCoeff p) := by
    intro r f hf h
    refine map_eq_cc (f.comp W.π) fun i => ?_
    have e1 : f ((u (g i)).mat (a i) (b i)) = (r (g i)).mat (a i) (b i) :=
      congrArg (fun r : Γ →* GG 3 _ => (r (g i)).mat (a i) (b i)) hf
    have e2 : f ((F.rz R (g i)).mat (a i) (b i)) = (F.rz _ (g i)).mat (a i) (b i) := f.commutes _
    show f (W.z i) = 0
    rw [hW, map_sub, e1, e2, h, sub_self]
  have hm : ∀ s a b, (r s).mat a b = (F.rz _ s).mat a b +
      TrivSqZeroExt.inr ((y s).val a b * ((F.Ψbar s ^ wt1 b : (ResidueField O)ˣ) : ResidueField O)) := by
    intro s a b
    rw [(hr s).2, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, add_right_inj, rz_mat_dual,
      Matrix.mul_diagonal]
    ext <;> simp [mul_comm]
  obtain ⟨f, hf, -⟩ := hu.univ _ r hp
  obtain ⟨f₀, hf₀, -⟩ := hu.univ _ (F.rz (DualNumber (ResidueField O))) (isPt_rz F hF g₁)
  have k1 := key r f hf fun i => by rw [hm, h0, zero_mul, TrivSqZeroExt.inr_zero, add_zero]
  have k2 := key _ f₀ hf₀ fun _ => rfl
  have hff : f = f₀ := AlgHom.ext fun x => by
    obtain ⟨p, rfl⟩ := W.surj x
    rw [k1, k2]
  have hrr : r = F.rz _ := by rw [← hf, hff, hf₀]
  funext s
  apply val_ext
  ext a b
  have := hm s a b
  rw [hrr, left_eq_add] at this
  have h3 := congrArg TrivSqZeroExt.snd this
  rw [TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero, Units.mul_left_eq_zero] at h3
  exact h3

end Main

private theorem finrank_quot_le {k V U : Type} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup U] [Module k U]
    [Module.Finite k U] (B N : Submodule k V) (φ : V →ₗ[k] U) (h1 : ∀ x, ∃ b ∈ B, x + b ∈ N)
    (h2 : ∀ x ∈ N, φ x = 0 → x = 0) : Module.finrank k (V ⧸ B) ≤ Module.finrank k U := by
  have hi : Function.Injective (φ.comp N.subtype) := by
    rw [injective_iff_map_eq_zero]
    exact fun x hx => Subtype.ext (h2 x x.2 hx)
  have : Module.Finite k N := Module.Finite.of_injective _ hi
  have hs : Function.Surjective (B.mkQ.comp N.subtype) := fun q => by
    obtain ⟨x, rfl⟩ := B.mkQ_surjective q
    obtain ⟨b, hb, hx⟩ := h1 x
    refine ⟨⟨_, hx⟩, ?_⟩
    show B.mkQ (x + b) = B.mkQ x
    rw [map_add, Submodule.mkQ_apply B b, (Submodule.Quotient.mk_eq_zero B).2 hb, add_zero]
  exact (LinearMap.finrank_le_finrank_of_surjective hs).trans (LinearMap.finrank_le_finrank_of_injective hi)

end UpperTheory.V.UnitaryThreeInertia.Tan

theorem UpperTheory.V.UnitaryThreeInertia.finrank_H1L_le :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → F.Count → ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    ∀ (W : WPres O ℤ R), F.Adapted u W → ∀ j, Module.finrank (ResidueField O) (F.selmerCohomologyQuotient j) ≤ Nat.card {i // W.wt i = j} := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hV _ g₁ hg R _ _ _ u hu W hW j
  classical
  choose g a b _ hwt hz using hW.var
  have hM : Marks F.η F.Ψbar F.c g₁ :=
    ⟨hF.csq, hF.ηc, by simp [Frame.Ψbar, hF.Ψc], hg.1, by simpa [Frame.Ψbar] using hg.2.map (residue O)⟩
  have h2 : IsUnit (2 : ResidueField O) := by
    have := hF.two.map (residue O)
    rwa [map_ofNat] at this
  let N : Submodule (ResidueField O) (F.selmerCocycles j) :=
    { carrier := {y | NormCoc F.c g₁ (r0 F.η F.Ψbar) fun g => (y.1 g).val}
      add_mem' := fun {y y'} h h' => by
        have e : ∀ s, ((y + y').1 s).val = (y.1 s).val + (y'.1 s).val := fun _ => rfl
        have e' : zvar F.c g₁ (r0 F.η F.Ψbar) (fun g => ((y + y').1 g).val) =
            zvar F.c g₁ (r0 F.η F.Ψbar) (fun g => (y.1 g).val) + zvar F.c g₁ (r0 F.η F.Ψbar) (fun g => (y'.1 g).val) := by
          simp only [zvar, e, Matrix.add_mul]
          abel
        refine ⟨?_, by rw [e', Matrix.add_apply, h.z12, h'.z12, add_zero], by rw [e', Matrix.add_apply, h.z21, h'.z21, add_zero]⟩
        exact (e _).trans ((congrArg₂ (· + ·) h.atc h'.atc).trans (add_zero _))
      zero_mem' := by
        have e : ∀ s, ((0 : F.selmerCocycles j).1 s).val = 0 := fun _ => rfl
        exact ⟨rfl, by simp only [zvar, e, Matrix.zero_mul, sub_zero, Matrix.zero_apply], by simp only [zvar, e, Matrix.zero_mul, sub_zero, Matrix.zero_apply]⟩
      smul_mem' := fun t y h => by
        have e : ∀ s, ((t • y).1 s).val = t • (y.1 s).val := fun _ => rfl
        have e' : zvar F.c g₁ (r0 F.η F.Ψbar) (fun g => ((t • y).1 g).val) =
            t • zvar F.c g₁ (r0 F.η F.Ψbar) (fun g => (y.1 g).val) := by
          simp only [zvar, e, Matrix.smul_mul, smul_sub]
        refine ⟨?_, by rw [e', Matrix.smul_apply, h.z12, smul_zero], by rw [e', Matrix.smul_apply, h.z21, smul_zero]⟩
        exact (e _).trans ((congrArg (t • ·) h.atc).trans (smul_zero _)) }
  let φ : F.selmerCocycles j →ₗ[ResidueField O] ({i // W.wt i = j} → ResidueField O) :=
    { toFun := fun y i => (y.1 (g i)).val (a i) (b i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [Nat.card_eq_fintype_card, ← Module.finrank_fintype_fun_eq_card (ResidueField O)]
  refine Tan.finrank_quot_le _ N φ (fun y => ?_) fun y hy h0 => ?_
  · obtain ⟨Y, hY, hn⟩ := Tan.exists_norm F.η F.Ψbar F.c g₁ h2 hM j (fun s => (y.1 s).val) (fun s => (y.1 s).2)
      fun s t => congrArg Gb.val (y.2.1.2 s t)
    refine ⟨⟨_, Tan.commAlgFunctorCoboundaryZero_mem_cocyclesOne F hF j ⟨Y, hY⟩⟩, ⟨⟨Y, hY⟩, rfl⟩, ?_⟩
    show NormCoc _ _ _ _
    convert hn using 1
    funext s
    show (y.1 s).val + (adRep (r0 F.η F.Ψbar) s Y - Y) = (y.1 s).val - (Y - adRep (r0 F.η F.Ψbar) s Y)
    abel
  · refine Subtype.ext (Tan.eq_zero_of_coord F hF hV g₁ u hu W g a b hz j y.1 y.2 hy fun i => ?_)
    by_cases hi : W.wt i = j
    · exact congrFun h0 ⟨i, hi⟩
    · exact (y.1 (g i)).2 _ _ (hwt i ▸ hi)
