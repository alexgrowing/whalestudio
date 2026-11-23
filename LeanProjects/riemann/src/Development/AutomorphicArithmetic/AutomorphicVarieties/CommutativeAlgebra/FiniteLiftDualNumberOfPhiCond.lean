import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem pullback_fin_relation (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (Γ ι : Type) [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι k) [IsTopologicalGroup Γ]
    [CompactSpace Γ] (hΦ : PhiCond Γ l) (hlc : IsLocallyConstant rbar) :
    Finite {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b} := by
  classical
  letI : Algebra (ZMod l) k := ZMod.algebra k l
  have hHopen : IsOpen (rbar.ker : Set Γ) := by
    have h := hlc.isOpen_fiber 1
    convert h using 1
    ext x
    simp [MonoidHom.mem_ker]
  haveI : Finite (Γ ⧸ rbar.ker) := Subgroup.quotient_finite_of_isOpen _ hHopen
  haveI := hΦ rbar.ker hHopen
  haveI : Finite (Module.Dual (ZMod l) k) :=
    Finite.of_injective (fun f => (f : k → ZMod l)) DFunLike.coe_injective
  haveI : Finite (DualNumber k) := inferInstanceAs (Finite (k × k))
  have hfst : ∀ r : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b},
      ∀ x ∈ rbar.ker, ∀ a b, (r.1 x a b).fst = (1 : Matrix ι ι k) a b := by
    intro r x hx a b
    rw [r.2.1, (MonoidHom.mem_ker).1 hx]
  have key : ∀ r : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b},
      ∀ x ∈ rbar.ker, ∀ y ∈ rbar.ker, ∀ a b,
        (r.1 (x * y) a b).snd = (r.1 x a b).snd + (r.1 y a b).snd := by
    intro r x hx y hy a b
    rw [map_mul, Matrix.mul_apply, TrivSqZeroExt.snd_sum]
    simp only [TrivSqZeroExt.snd_mul, hfst r x hx, hfst r y hy]
    simp [Finset.sum_add_distrib, Matrix.one_apply, ite_smul, add_comm]
  have hone : ∀ r : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b},
      ∀ a b, (r.1 1 a b).snd = 0 := by
    intro r a b
    rw [map_one]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  let φ : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b} →
      ι → ι → Module.Dual (ZMod l) k → (rbar.ker →* Multiplicative (ZMod l)) := fun r a b f =>
    { toFun := fun x => Multiplicative.ofAdd (f (r.1 x a b).snd)
      map_one' := by
        show Multiplicative.ofAdd (f (r.1 1 a b).snd) = 1
        rw [hone r a b, map_zero]
        rfl
      map_mul' := by
        intro x y
        simp only [Subgroup.coe_mul, key r x x.2 y y.2, map_add, ofAdd_add] }
  have hφopen : ∀ r a b f, IsOpen ((φ r a b f).ker : Set rbar.ker) := by
    intro r a b f
    have hlc' : IsLocallyConstant fun x : rbar.ker => φ r a b f x :=
      ((r.2.2 a b).comp_continuous continuous_subtype_val).comp
        (fun z => Multiplicative.ofAdd (f z.snd))
    have h := hlc'.isOpen_fiber 1
    convert h using 1
    ext x
    simp [MonoidHom.mem_ker]
  let F : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b} →
      (Γ ⧸ rbar.ker → Matrix ι ι (DualNumber k)) ×
        (ι → ι → Module.Dual (ZMod l) k →
          {φ : rbar.ker →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set rbar.ker)}) :=
    fun r => (fun q => r.1 q.out, fun a b f => ⟨φ r a b f, hφopen r a b f⟩)
  refine Finite.of_injective F ?_
  intro r s hrs
  have h1 : ∀ q : Γ ⧸ rbar.ker, r.1 q.out = s.1 q.out := fun q => congrFun (congrArg Prod.fst hrs) q
  have h2 : ∀ (a b : ι) (f : Module.Dual (ZMod l) k) (x : rbar.ker), f (r.1 x a b).snd = f (s.1 x a b).snd := by
    intro a b f x
    have h := congrArg (fun p => ((p.2 a b f).1 x)) hrs
    exact Multiplicative.ofAdd.injective h
  have hK : ∀ x ∈ rbar.ker, r.1 x = s.1 x := by
    intro x hx
    refine Matrix.ext fun a b => TrivSqZeroExt.ext ?_ ?_
    · rw [hfst r x hx, hfst s x hx]
    · have h := (Module.forall_dual_apply_eq_zero_iff (ZMod l) ((r.1 x a b).snd - (s.1 x a b).snd)).1
        (fun f => by rw [map_sub, h2 a b f ⟨x, hx⟩, sub_self])
      exact sub_eq_zero.1 h
  apply Subtype.ext
  ext1 g
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul rbar.ker g
  have hg : g = (QuotientGroup.mk g : Γ ⧸ rbar.ker).out * (h : Γ)⁻¹ := by
    rw [hh]
    group
  rw [hg, map_mul, map_mul, h1, hK _ (rbar.ker.inv_mem h.2)]

theorem UpperTheory.finite_lift_dualNumber_of_phiCond :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) [IsTopologicalGroup Γ] [CompactSpace Γ] [IsCO O (DualNumber (ResidueField O))], PhiCond Γ l → IsLocallyConstant rbar → Finite (Lift O rbar (DualNumber (ResidueField O))) := by
  intro l _ O _ _ _ _ Γ ι _ _ _ _ rbar _ _ _ hΦ hlc
  classical
  have hmem : ∀ x : DualNumber (ResidueField O), x ∈ maximalIdeal (DualNumber (ResidueField O)) ↔ x.fst = 0 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
      not_not]
  have hres : ∀ x : DualNumber (ResidueField O), res O (DualNumber (ResidueField O)) x = x.fst := by
    intro x
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective x.fst
    have hx : x = algebraMap O (DualNumber (ResidueField O)) a + TrivSqZeroExt.inr x.snd := by
      rw [TrivSqZeroExt.algebraMap_eq_inl']
      refine TrivSqZeroExt.ext ?_ ?_
      · simp [IsLocalRing.ResidueField.algebraMap_eq, ha]
      · simp
    have hz : res O (DualNumber (ResidueField O)) (TrivSqZeroExt.inr x.snd) = 0 := by
      rw [res_eq_zero_iff, hmem]
      simp
    conv_lhs => rw [hx]
    rw [map_add, hz, add_zero, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, ha]
  have hsq : maximalIdeal (DualNumber (ResidueField O)) ^ 2 = ⊥ := by
    rw [sq, eq_bot_iff]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    rw [hmem] at hx hy
    rw [Ideal.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [hx]
    · simp [TrivSqZeroExt.snd_mul, hx, hy]
  have hinj : Function.Injective (Ideal.Quotient.mk (maximalIdeal (DualNumber (ResidueField O)) ^ 2)) := by
    intro x y hxy
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, hsq, Ideal.mem_bot, sub_eq_zero] at hxy
    exact hxy
  haveI := pullback_fin_relation l (ResidueField O) Γ ι rbar hΦ hlc
  refine Finite.of_injective
    (fun r : Lift O rbar (DualNumber (ResidueField O)) =>
      (⟨r.hom, fun g a b => by rw [← hres]; exact r.red g a b,
        fun a b => IsLocallyConstant.desc _ _ (r.cont a b 2) hinj⟩ :
        {r : Γ →* Matrix ι ι (DualNumber (ResidueField O)) //
          (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b}))
    ?_
  intro r s hrs
  exact Lift.ext (congrArg Subtype.val hrs)
