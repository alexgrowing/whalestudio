import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem eq_zero_of_forall_hom_zmod_eq_zero_of_module_zmod {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] [Module (ZMod l) M] (v : M)
    (hv : ∀ f : M →+ ZMod l, f v = 0) : v = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod l)]
  intro f
  exact hv (LinearMap.toAddMonoidHom f)

theorem UpperTheory.V.Pa.Det.locallyConstant_cocycles_finite_of_phi :
    ∀ (l : ℕ) [Fact l.Prime] {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [AddCommGroup M] [Finite M] (ρ : G →* AddMonoid.End M), PhiCond G l → (∀ m : M, l • m = 0) → (∀ m, IsLocallyConstant fun g => ρ g m) → {z : G → M | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g (z h)}.Finite := by
  intro l _ G M _ _ _ _ _ _ _ ρ hΦ hl hc
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  set S := {z : G → M | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g (z h)} with hS
  have hker : IsOpen (ρ.ker : Set G) := by
    have he : (ρ.ker : Set G) = ⋂ m, {g | ρ g m = m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        ext m
        exact h m
    rw [he]
    exact isOpen_iInter_of_finite fun m => (hc m).isOpen_fiber m
  haveI : Finite (G ⧸ ρ.ker) := Subgroup.quotient_finite_of_isOpen _ hker
  haveI := hΦ ρ.ker hker
  haveI : Finite (M →+ ZMod l) :=
    Finite.of_injective (fun f : M →+ ZMod l => (⇑f : M → ZMod l))
      (fun a b hab => AddMonoidHom.ext (congrFun hab))
  have h1 : ∀ z ∈ S, z 1 = 0 := by
    intro z hz
    have h11 : z 1 = z 1 + z 1 := by
      have := hz.2 1 1
      rw [one_mul, map_one] at this
      exact this
    exact add_left_cancel (h11.symm.trans (add_zero _).symm)
  have hH : ∀ z ∈ S, ∀ a b : G, a ∈ ρ.ker → z (a * b) = z a + z b := by
    intro z hz a b ha
    rw [hz.2, MonoidHom.mem_ker.mp ha]
    rfl
  let φ : ∀ z ∈ S, (M →+ ZMod l) →
      {φ : ρ.ker →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set ρ.ker)} := fun z hz f =>
    ⟨{ toFun := fun h => Multiplicative.ofAdd (f (z h))
       map_one' := by simp [h1 z hz]
       map_mul' := fun a b => by simp [hH z hz a b a.2, ofAdd_add] },
     by
       have hlc : IsLocallyConstant (fun h : ρ.ker => Multiplicative.ofAdd (f (z h))) :=
         (hz.1.comp_continuous continuous_subtype_val).comp _
       exact hlc.isOpen_fiber 1⟩
  let F : S → ((G ⧸ ρ.ker) → M) × ((M →+ ZMod l) →
      {φ : ρ.ker →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set ρ.ker)}) :=
    fun z => (fun q => z.1 (Quotient.out q), φ z.1 z.2)
  have hinj : Function.Injective F := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
    have hq : (fun q : G ⧸ ρ.ker => z (Quotient.out q)) = fun q => z' (Quotient.out q) := congrArg Prod.fst hzz
    have hf : φ z hz = φ z' hz' := congrArg Prod.snd hzz
    have hHeq : ∀ h ∈ ρ.ker, z h = z' h := by
      intro h hh
      rw [← sub_eq_zero]
      apply @eq_zero_of_forall_hom_zmod_eq_zero_of_module_zmod l _ M _ (AddCommGroup.zmodModule hl)
      intro f
      have hx := congrArg (fun p => (p.1 ⟨h, hh⟩ : Multiplicative (ZMod l))) (congrFun hf f)
      change Multiplicative.ofAdd (f (z h)) = Multiplicative.ofAdd (f (z' h)) at hx
      rw [map_sub, sub_eq_zero]
      exact Multiplicative.ofAdd.injective hx
    apply Subtype.ext
    funext g
    show z g = z' g
    obtain ⟨h0, hh0⟩ := QuotientGroup.mk_out_eq_mul ρ.ker g
    have hg : g = Quotient.out (g : G ⧸ ρ.ker) * (h0 : G)⁻¹ := by
      rw [hh0, mul_inv_cancel_right]
    have hr := congrFun hq (g : G ⧸ ρ.ker)
    rw [hg, hz.2, hz'.2, hr, hHeq _ (inv_mem h0.2)]
  exact Set.finite_coe_iff.mp (Finite.of_injective F hinj)
