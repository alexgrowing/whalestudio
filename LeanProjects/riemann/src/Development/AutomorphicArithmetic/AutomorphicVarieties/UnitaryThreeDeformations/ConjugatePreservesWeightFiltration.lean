import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefCoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormCob
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ZetaReducibleRepEqSubInvAndIsUnit

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O]

private theorem triangular_eigen_lower_zero (h M : Matrix (Fin 3) (Fin 3) O) (d : Fin 3 → O)
    (e : h * M = Matrix.diagonal d * h) (hM : ∀ a b, wt a b < 0 → M a b = 0) (hu : ∀ a, IsUnit (h a a))
    (h10 : IsUnit (d 1 - d 0)) (h20 : IsUnit (d 2 - d 0)) (h21 : IsUnit (d 2 - d 1)) :
    h 1 0 = 0 ∧ h 2 0 = 0 ∧ h 2 1 = 0 := by
  have m10 := hM 1 0 (by decide)
  have m20 := hM 2 0 (by decide)
  have m21 := hM 2 1 (by decide)
  have E : ∀ a b, h a 0 * M 0 b + h a 1 * M 1 b + h a 2 * M 2 b = d a * h a b := fun a b => by
    have := congrFun (congrFun e a) b
    rwa [Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_three] at this
  have e00 : M 0 0 = d 0 := by
    have := E 0 0
    rw [m10, m20] at this
    exact (hu 0).mul_left_cancel (by linear_combination this)
  have a10 : h 1 0 = 0 := by
    have := E 1 0
    rw [m10, m20, e00] at this
    exact h10.mul_right_eq_zero.1 (by linear_combination -this)
  have a20 : h 2 0 = 0 := by
    have := E 2 0
    rw [m10, m20, e00] at this
    exact h20.mul_right_eq_zero.1 (by linear_combination -this)
  have e11 : M 1 1 = d 1 := by
    have := E 1 1
    rw [a10, m21] at this
    exact (hu 1).mul_left_cancel (by linear_combination this)
  refine ⟨a10, a20, ?_⟩
  have := E 2 1
  rw [a20, m21, e11] at this
  exact h21.mul_right_eq_zero.1 (by linear_combination -this)

private theorem conjugate_preserves_weight_filtration (h M U : Matrix (Fin 3) (Fin 3) O)
    (e : U * h = h * M) (hM : ∀ a b, wt a b < 0 → M a b = 0) (hu : ∀ a, IsUnit (h a a))
    (hh : h 1 0 = 0 ∧ h 2 0 = 0 ∧ h 2 1 = 0) :
    (∀ a b, wt a b < 0 → U a b = 0) ∧ ∀ a, U a a = M a a := by
  have m10 := hM 1 0 (by decide)
  have m20 := hM 2 0 (by decide)
  have m21 := hM 2 1 (by decide)
  obtain ⟨a10, a20, a21⟩ := hh
  have E : ∀ a b, U a 0 * h 0 b + U a 1 * h 1 b + U a 2 * h 2 b =
      h a 0 * M 0 b + h a 1 * M 1 b + h a 2 * M 2 b := fun a b => by
    have := congrFun (congrFun e a) b
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_three] at this
  have u00 : U 0 0 = M 0 0 := by
    have := E 0 0
    rw [m10, m20, a10, a20] at this
    exact (hu 0).mul_left_cancel (by linear_combination this)
  have u10 : U 1 0 = 0 := by
    have := E 1 0
    rw [m10, m20, a10, a20] at this
    exact (hu 0).mul_right_eq_zero.1 (by linear_combination this)
  have u20 : U 2 0 = 0 := by
    have := E 2 0
    rw [m10, m20, a10, a20] at this
    exact (hu 0).mul_right_eq_zero.1 (by linear_combination this)
  have u11 : U 1 1 = M 1 1 := by
    have := E 1 1
    rw [m21, a10, a21, u10] at this
    exact (hu 1).mul_left_cancel (by linear_combination this)
  have u21 : U 2 1 = 0 := by
    have := E 2 1
    rw [m21, a20, a21, u20] at this
    exact (hu 1).mul_right_eq_zero.1 (by linear_combination this)
  have u22 : U 2 2 = M 2 2 := by
    have := E 2 2
    rw [a20, a21, u20, u21] at this
    exact (hu 2).mul_left_cancel (by linear_combination this)
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)
  · fin_cases a <;> assumption

private def mf (X : Matrix (Fin 3) (Fin 3) (DualNumber O)) : Matrix (Fin 3) (Fin 3) O := fun a b => (X a b).fst
private def ms (X : Matrix (Fin 3) (Fin 3) (DualNumber O)) : Matrix (Fin 3) (Fin 3) O := fun a b => (X a b).snd

private theorem mf_mul (X Y : Matrix (Fin 3) (Fin 3) (DualNumber O)) : mf (X * Y) = mf X * mf Y := by
  ext a b
  simp [mf, Matrix.mul_apply, Fin.sum_univ_three]

private theorem ms_mul (X Y : Matrix (Fin 3) (Fin 3) (DualNumber O)) :
    ms (X * Y) = mf X * ms Y + ms X * mf Y := by
  ext a b
  simp [mf, ms, Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem mf_one : mf (1 : Matrix (Fin 3) (Fin 3) (DualNumber O)) = 1 := by
  ext a b
  by_cases h : a = b <;> simp [mf, Matrix.one_apply, h]

private theorem dual_number_maximal_ideal_pow [IsLocalRing O] [IsLocalRing (DualNumber O)] (N : ℕ) :
    ∀ x ∈ maximalIdeal (DualNumber O) ^ (N + 1),
      x.fst ∈ maximalIdeal O ^ (N + 1) ∧ x.snd ∈ maximalIdeal O ^ N := by
  have h0 : ∀ x ∈ maximalIdeal (DualNumber O), x.fst ∈ maximalIdeal O := fun x hx hu =>
    hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
  induction N with
  | zero => intro x hx; rw [zero_add, pow_one] at *; exact ⟨h0 x hx, by simp⟩
  | succ N ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun y hy z hz => ?_) (fun y z hy hz => ?_)
    · obtain ⟨h1, h2⟩ := ih y hy
      refine ⟨?_, ?_⟩
      · rw [TrivSqZeroExt.fst_mul, pow_succ]; exact Ideal.mul_mem_mul h1 (h0 z hz)
      · rw [DualNumber.snd_mul]
        refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) ?_
        rw [pow_succ]; exact Ideal.mul_mem_mul h2 (h0 z hz)
    · exact ⟨by rw [TrivSqZeroExt.fst_add]; exact Ideal.add_mem _ hy.1 hz.1,
        by rw [TrivSqZeroExt.snd_add]; exact Ideal.add_mem _ hy.2 hz.2⟩

private theorem triangular_dual_number_diagonal [IsLocalRing O] [IsLocalRing (DualNumber O)] {D : Type} [Group D] (η : D →* ℤˣ)
    (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 (DualNumber O)) (hm : HasMult η r)
    (hf : ∀ g, mf (r g).mat = Matrix.diagonal fun a => psi Ψ a g)
    (x : D) (hx : η x = 1) (hx2 : IsUnit ((Ψ x : O) ^ 2 - 1))
    (h : GL (Fin 3) (DualNumber O)) (hh : InHat h) (ht : TriIn η Ψ I r h) :
    (∀ s ∈ I, η s = 1 → ∀ a, ((r s).mat a a).snd = 0) ∧
    ∃ Z : Matrix (Fin 3) (Fin 3) O, ∀ g, η g = 1 → ∀ a b, wt a b < 0 →
      ((r g).mat a b).snd = Z a b * (psi Ψ b g - psi Ψ a g) := by
  have hc : ∀ g, η g = 1 → h.val * (conjBy h⁻¹ r g).mat = (r g).mat * h := fun g hg => by
    have : (r g).right = 1 := (hm g).trans hg
    simp [conjBy, GG.mat, this, ← Matrix.mul_assoc]
  have hu : ∀ a, IsUnit (mf h.val a a) := fun a => by
    have h1 := (dual_number_maximal_ideal_pow 0 _ (by rw [zero_add, pow_one]; exact hh a a)).1
    rw [zero_add, pow_one, Matrix.sub_apply, Matrix.one_apply_eq] at h1
    by_contra hn
    have h2 : mf h.val a a ∈ maximalIdeal O := hn
    have h3 := Ideal.sub_mem _ h2 (show mf h.val a a - 1 ∈ maximalIdeal O from h1)
    rw [sub_sub_cancel] at h3
    exact h3 isUnit_one
  have hup : mf h.val 1 0 = 0 ∧ mf h.val 2 0 = 0 ∧ mf h.val 2 1 = 0 := by
    have e := congrArg mf (hc x hx)
    rw [mf_mul, mf_mul, hf] at e
    have p0 : psi Ψ 0 x = Ψ x := by simp [psi, wt1]
    have p1 : psi Ψ 1 x = 1 := by simp [psi, wt1]
    have p2 : psi Ψ 2 x = ((Ψ x)⁻¹ : Oˣ) := by simp [psi, wt1]
    have hi : (Ψ x : O) * ((Ψ x)⁻¹ : Oˣ) = 1 := Units.mul_inv _
    have u1 : IsUnit ((Ψ x : O) - 1) :=
      isUnit_of_mul_isUnit_left (y := (Ψ x : O) + 1) (by convert hx2 using 1; ring)
    refine triangular_eigen_lower_zero _ _ _ e (fun a b hab => ?_) hu ?_ ?_ ?_
    · show ((conjBy h⁻¹ r x).mat a b).fst = 0
      rw [ht.tri x hx a b hab]; rfl
    · rw [p0, p1]; convert u1.neg using 1; ring
    · rw [p0, p2]; convert (hx2.mul (Units.isUnit (Ψ x)⁻¹)).neg using 1
      linear_combination ((Ψ x : O)) * hi
    · rw [p1, p2]; convert (u1.mul (Units.isUnit (Ψ x)⁻¹)).neg using 1
      linear_combination hi
  set h0 := mf h.val with h0d
  set h1 := ms h.val with h1d
  set k0 := mf (h⁻¹).val with k0d
  have hk : h0 * k0 = 1 := by rw [h0d, k0d, ← mf_mul, Units.mul_inv, mf_one]
  have kh : k0 * h0 = 1 := by rw [h0d, k0d, ← mf_mul, Units.inv_mul, mf_one]
  have key : ∀ g, η g = 1 → ∀ U, U = ms (r g).mat + (Matrix.diagonal fun a => psi Ψ a g) * (h1 * k0) -
      (h1 * k0) * (Matrix.diagonal fun a => psi Ψ a g) →
      (∀ a b, wt a b < 0 → U a b = 0) ∧ ∀ a, U a a = ms (conjBy h⁻¹ r g).mat a a := fun g hg U hU => by
    have e0 := congrArg mf (hc g hg)
    have e1 := congrArg ms (hc g hg)
    rw [mf_mul, mf_mul, hf, ← h0d] at e0
    rw [ms_mul, ms_mul, hf, ← h0d, ← h1d] at e1
    refine conjugate_preserves_weight_filtration h0 _ U ?_ (fun a b hab => ?_) hu hup
    · rw [hU, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc h1, kh, Matrix.mul_one,
        Matrix.mul_assoc (h1 * k0), ← e0, Matrix.mul_assoc h1, ← Matrix.mul_assoc k0, kh, Matrix.one_mul,
        sub_eq_iff_eq_add, e1, add_comm]
    · show ((conjBy h⁻¹ r g).mat a b).snd = 0
      rw [ht.tri g hg a b hab]; rfl
  refine ⟨fun s hs hs1 a => ?_, h1 * k0, fun g hg a b hab => ?_⟩
  · have := (key s hs1 _ rfl).2 a
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    have h2 : ms (conjBy h⁻¹ r s).mat a a = 0 := by
      show ((conjBy h⁻¹ r s).mat a a).snd = 0
      rw [ht.ine s hs hs1 a]; rfl
    show ms (r s).mat a a = 0
    linear_combination this + h2
  · have := (key g hg _ rfl).1 a b hab
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    show ms (r g).mat a b = _
    linear_combination this

private theorem exists_cocycle_of_dual_lift {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) (r : Γ →* GG 3 (DualNumber O))
    (hm : HasMult η r) (hf : ∀ g a b, ((r g).mat a b).fst = (r0 η Ψ g).mat a b) :
    ∃ γ : Γ → Matrix (Fin 3) (Fin 3) O, IsCoc (r0 η Ψ) γ ∧
      ∀ g, ms (r g).mat = γ g * (r0 η Ψ g).mat := by
  let Ψ' : Γ →* (DualNumber O)ˣ := (Units.map (algebraMap O (DualNumber O)).toMonoidHom).comp Ψ
  have hp : ∀ g (n : ℤ), ((Ψ' g ^ n : (DualNumber O)ˣ) : DualNumber O) =
      algebraMap O _ ((Ψ g ^ n : Oˣ) : O) := fun g n => by
    show ((Units.map _ (Ψ g) ^ n : (DualNumber O)ˣ) : DualNumber O) = _
    rw [← map_zpow]; rfl
  have h0 : ∀ g a b, (r0 η Ψ' g).mat a b = algebraMap O _ ((r0 η Ψ g).mat a b) := fun g a b => by
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply, hp]
    split_ifs <;> simp
  let I : Ideal (DualNumber O) := RingHom.ker (TrivSqZeroExt.fstHom O O O)
  have hI : ∀ x, x ∈ I ↔ x.fst = 0 := fun x => Iff.rfl
  obtain ⟨γ, h1, h2, h3⟩ := exists_isCoc I (r0 η Ψ') r (by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      rw [hI] at hx hy
      rw [Ideal.mem_bot]
      ext <;> simp [hx, hy]) (by
      refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) (hm g)
      ext a b
      show Ideal.Quotient.mk I ((r g).mat a b) = Ideal.Quotient.mk I ((r0 η Ψ' g).mat a b)
      rw [Ideal.Quotient.eq, hI, TrivSqZeroExt.fst_sub, hf, h0, sub_eq_zero]
      rfl)
  refine ⟨fun g => ms (γ g), fun g h => ?_, fun g => ?_⟩
  · ext a b
    have := congrArg TrivSqZeroExt.snd (congrFun (congrFun (h2 g h) a) b)
    rw [Matrix.add_apply, adRep_baseLift_apply, hp] at this
    rw [Matrix.add_apply, adRep_baseLift_apply]
    refine this.trans ?_
    split_ifs <;> simp [ms, TrivSqZeroExt.algebraMap_eq_inl]
  · have a1 : mf (r0 η Ψ' g).mat = (r0 η Ψ g).mat := by
      ext a b; show ((r0 η Ψ' g).mat a b).fst = _; rw [h0]; rfl
    have a2 : ms (r0 η Ψ' g).mat = 0 := by
      ext a b; show ((r0 η Ψ' g).mat a b).snd = _; rw [h0]; rfl
    have a3 : ms (1 + γ g) = ms (γ g) := by
      ext a b
      by_cases h : a = b <;> simp [ms, Matrix.one_apply, h]
    rw [(h3 g).2, ms_mul, a1, a2, a3, Matrix.mul_zero, zero_add]

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.eq_rz_of_vanE :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.VanE → ∀ g₁, F.Marked g₁ → ∀ [IsLocalRing (DualNumber O)] (j : ℤ), j ≤ 0 → ∀ (r : Γ →* GG 3 (DualNumber O)), F.IsPt g₁ r →
      (∀ g a b, ((r g).mat a b).fst = (r0 F.η F.Ψ g).mat a b) → (∀ g a b, F.η g = 1 → wt a b ≠ j → ((r g).mat a b).snd = 0) → r = F.rz (DualNumber O) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F ok van g₁ mk _ j hj r pt hf hw
  obtain ⟨γ, hcoc, hγ⟩ := exists_cocycle_of_dual_lift F.η F.Ψ r pt.mult hf
  have hd : ∀ g, (r0 F.η F.Ψ g).mat = Matrix.diagonal fun a => psi F.Ψ a g := fun g => rfl
  have hs : ∀ g a b, ((r g).mat a b).snd = γ g a b * psi F.Ψ b g := fun g a b => by
    have := congrFun (congrFun (hγ g) a) b
    rwa [hd, Matrix.mul_diagonal] at this
  have hpu : ∀ b g, IsUnit (psi F.Ψ b g) := fun b g => Units.isUnit _
  have hz : ∀ g a b, ((r g).mat a b).snd = 0 → γ g a b = 0 := fun g a b h =>
    (hpu b g).mul_left_eq_zero.1 ((hs g a b).symm.trans h)
  have hone : ∀ g, (r g).mat = 1 → γ g = 0 := fun g h => by
    ext a b
    refine hz g a b ?_
    rw [h]
    by_cases e : a = b <;> simp [Matrix.one_apply, e]
  have hc : γ F.c = 0 := hone _ pt.norm.atc
  have hgw : ∀ g, γ g ∈ gw O j := fun g => by
    rcases Int.units_eq_one_or (F.η g) with hg | hg
    · exact fun a b hab => hz g a b (hw g a b hg hab)
    · have h1 : F.η (g * F.c) = 1 := by rw [map_mul, hg, ok.ηc]; simp
      have h2 := hcoc g F.c
      rw [hc, map_zero, add_zero] at h2
      rw [← h2]
      exact fun a b hab => hz _ a b (hw _ a b h1 hab)
  have hinv : ∀ g a b, γ g a b = ((r g).mat a b).snd * ((r g⁻¹).mat b b).fst := fun g a b => by
    rw [hs, hf, hd, Matrix.diagonal_apply_eq, mul_assoc, psi, psi, ← Units.val_mul, ← mul_zpow, ← map_mul]
    simp
  have hcont : ∀ a b, Alg.AdicCont (maximalIdeal O) fun g => γ g a b := fun a b N => by
    have c1 := pt.cont (N + 1)
    have c2 := c1.comp_continuous (continuous_inv (G := Γ))
    rw [IsLocallyConstant.iff_eventually_eq] at c1 c2 ⊢
    intro x
    filter_upwards [c1 x, c2 x] with y e1 e2
    have f1 := (dual_number_maximal_ideal_pow N _ (Ideal.Quotient.eq.1 (congrFun (congrFun e1 a) b))).2
    have f2 := Ideal.pow_le_pow_right (Nat.le_succ N)
      (dual_number_maximal_ideal_pow N _ (Ideal.Quotient.eq.1 (congrFun (congrFun e2 b) b))).1
    rw [TrivSqZeroExt.snd_sub] at f1
    rw [TrivSqZeroExt.fst_sub] at f2
    rw [hinv, hinv, map_mul, map_mul, Ideal.Quotient.eq.2 f1, Ideal.Quotient.eq.2 f2]
  have htri : ∀ v ∈ F.Tb, (∀ s ∈ F.Iv v, F.ηv v s = 1 → ∀ a, ((r (F.loc v s)).mat a a).snd = 0) ∧
      ∃ Z : Matrix (Fin 3) (Fin 3) O, ∀ g, F.ηv v g = 1 → ∀ a b, wt a b < 0 →
        ((r (F.loc v g)).mat a b).snd = Z a b * (psi F.Ψ b (F.loc v g) - psi F.Ψ a (F.loc v g)) := fun v hv => by
    obtain ⟨h, hh, ht⟩ : CondT (F.ηv v) (F.Ψv v) (F.Iv v) (r.comp (F.loc v)) := by
      rcases hv with hv | hv
      · exact (pt.loc v).1 hv
      · obtain ⟨h, hh, ht⟩ := (pt.loc v).2.1 hv
        exact ⟨h, hh, ht.toTriIn⟩
    obtain ⟨x, hx, hx2⟩ := ok.x v hv
    exact triangular_dual_number_diagonal (F.ηv v) (F.Ψv v) (F.Iv v) (r.comp (F.loc v)) (fun g => pt.mult _)
      (fun g => by ext a b; exact hf _ a b) x hx hx2 h hh ht
  obtain ⟨t, ht, X, hX⟩ := van j hj γ hgw hcoc hcont
    (fun v hv s hs => hone _ (by
      have : r (F.loc v s) = 1 := (pt.loc v).2.2 hv s hs
      rw [this]; rfl))
    (fun e v hv s hs => by
      ext a b
      by_cases hab : a = b
      · subst hab
        exact hz _ _ _ ((htri v hv).1 s hs (ok.η_I v hv s hs) a)
      · refine hgw _ a b ?_
        rw [e]
        revert a b
        decide)
    (fun e => by
      obtain ⟨Z, hZ⟩ := (htri F.vl (Set.mem_insert _ _)).2
      refine ⟨Matrix.of fun a b => if wt a b = j then Z a b else 0, fun a b hab => if_neg hab, fun g hg => ?_⟩
      ext a b
      have hg' : F.η (F.loc _ g) = 1 := hg
      rw [cob, Matrix.sub_apply, adRep_baseLift_apply, if_pos hg', Matrix.of_apply]
      by_cases hab : wt a b = j
      · simp only [if_pos hab]
        have h1 := hZ g hg a b (hab ▸ e)
        rw [hs] at h1
        have h2 : ((F.Ψ (F.loc _ g) ^ wt a b : Oˣ) : O) * psi F.Ψ b (F.loc _ g) = psi F.Ψ a (F.loc _ g) := by
          rw [psi, psi, ← Units.val_mul, ← _root_.zpow_add, wt, sub_add_cancel]
        refine (hpu b (F.loc _ g)).mul_right_cancel ?_
        linear_combination h1 + Z a b * h2
      · simp only [if_neg hab]
        rw [hgw _ a b hab]; simp)
  have hcob : cob (r0 F.η F.Ψ) X = fun g => t • γ g := funext fun g => (hX g).symm
  have hzv : zvar F.c g₁ (r0 F.η F.Ψ) (fun g => t • γ g) = t • (ms (r g₁).mat - ms (r (gstar F.c g₁)).mat) := by
    rw [zvar, hγ, hγ, smul_sub, Matrix.smul_mul, Matrix.smul_mul]
  have hzz : ∀ a b, zmat F.c g₁ r a b = 0 → zvar F.c g₁ (r0 F.η F.Ψ) (fun g => t • γ g) a b = 0 := fun a b h => by
    have h1 := congrArg TrivSqZeroExt.snd h
    rw [zmat, Matrix.sub_apply, TrivSqZeroExt.snd_sub] at h1
    rw [hzv, Matrix.smul_apply, Matrix.sub_apply]
    exact (congrArg (t • ·) h1).trans (smul_zero _)
  have hlie : X ∈ unitaryThreeTorusLieAlgebra O := (normCoc_cob_iff (r0 F.η F.Ψ) F.c g₁ X ok.two ok.ηc mk.1
    (baseRepGL3_normalised_of_psi_eq_one _ _ _ ok.Ψc) (zeta_reducible_rep_eq_sub_inv_and_isUnit _ _ _ _ ⟨ok.csq, ok.ηc, ok.Ψc, mk.1, mk.2⟩).2).1 (by
      rw [hcob]
      exact ⟨by simp [hc], hzz _ _ pt.norm.z12, hzz _ _ pt.norm.z21⟩)
  obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 hlie
  have hγ0 : ∀ g, γ g = 0 := fun g => by
    refine (smul_eq_zero.1 ((hX g).trans ?_)).resolve_left ht
    ext a b
    rw [cob, Matrix.sub_apply, adRep_baseLift_apply]
    split_ifs <;> fin_cases a <;> fin_cases b <;> simp [wt, wt1, Fin.rev] <;> ring
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) (pt.mult g)
  ext a b
  · exact hf g a b
  · exact (hs g a b).trans (by rw [hγ0]; exact zero_mul _)
