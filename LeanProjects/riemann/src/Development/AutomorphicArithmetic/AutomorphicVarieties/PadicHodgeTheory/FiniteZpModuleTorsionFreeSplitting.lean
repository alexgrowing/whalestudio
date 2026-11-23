import Mathlib

open Module Topology

theorem UpperTheory.finite_zp_module_torsion_free_splitting :
    ∀ (l : ℕ) [Fact l.Prime] (N : Type) [AddCommGroup N] [Module ℤ_[l] N] [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousSMul ℤ_[l] N] [T2Space N] [Module.Finite ℤ_[l] N], Finite ↥(Submodule.torsion ℤ_[l] N) ∧ ∃ (p : N →ₗ[ℤ_[l]] (Fin (Module.finrank ℤ_[l] N) → ℤ_[l])) (t : N →ₗ[ℤ_[l]] ↥(Submodule.torsion ℤ_[l] N)), Continuous p ∧ IsOpen (LinearMap.ker t : Set N) ∧ (∀ y : ↥(Submodule.torsion ℤ_[l] N), p y = 0 ∧ t y = y) ∧ Function.Bijective (fun y => (p y, t y)) := by
  intro l _ N _ _ _ _ _ _ _
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin' ℤ_[l] N
  have hgc : Continuous g := LinearMap.continuous_on_pi g
  have hq : Topology.IsQuotientMap g := hgc.isClosedMap.isQuotientMap hgc hg
  have hlin : ∀ f : N →ₗ[ℤ_[l]] (Fin (Module.finrank ℤ_[l] N) → ℤ_[l]), Continuous f := by
    intro f
    rw [hq.continuous_iff]
    exact LinearMap.continuous_on_pi (f ∘ₗ g)
  obtain ⟨a, ha, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    (R := ℤ_[l]) (M := Submodule.torsion ℤ_[l] N) Submodule.torsion_isTorsion
  have ha0' : a ≠ 0 := nonZeroDivisors.ne_zero ha0
  have hkill : ∀ y : Submodule.torsion ℤ_[l] N, ((l : ℤ_[l]) ^ a.valuation) • y = 0 := by
    intro y
    have h1 : a • y = 0 := (Submodule.mem_annihilator.mp ha) y trivial
    rw [PadicInt.unitCoeff_spec ha0', mul_smul] at h1
    exact (smul_eq_zero_iff_eq (PadicInt.unitCoeff ha0')).mp (by rwa [Units.smul_def])
  set K := a.valuation
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hopenI : IsOpen ((Ideal.span {(l : ℤ_[l]) ^ K} : Ideal ℤ_[l]) : Set ℤ_[l]) := by
    have : ((Ideal.span {(l : ℤ_[l]) ^ K} : Ideal ℤ_[l]) : Set ℤ_[l])
        = Metric.closedBall 0 ((l : ℝ) ^ (-(K : ℤ))) := by
      ext x
      simp [← PadicInt.norm_le_pow_iff_mem_span_pow]
    rw [this]
    exact IsUltrametricDist.isOpen_closedBall 0 (zpow_ne_zero _ hl0)
  set T := Submodule.torsion ℤ_[l] N with hT
  haveI : Module.IsTorsionFree ℤ_[l] (N ⧸ T) :=
    Submodule.isTorsionFree_iff_torsion_eq_bot.mpr Submodule.QuotientTorsion.torsion_eq_bot
  haveI : Module.Free ℤ_[l] (N ⧸ T) := Module.free_of_finite_type_torsion_free'
  have hrank : Module.finrank ℤ_[l] (N ⧸ T) = Module.finrank ℤ_[l] N := by
    have h := rank_quotient_add_rank_of_isDomain T
    rw [Module.IsTorsion.rank_eq_zero Submodule.torsion_isTorsion, add_zero] at h
    unfold Module.finrank
    rw [h]
  let b := Module.finBasisOfFinrankEq ℤ_[l] (N ⧸ T) hrank
  obtain ⟨s, hs⟩ := Module.projective_lifting_property T.mkQ LinearMap.id T.mkQ_surjective
  have hs' : ∀ q, T.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
  let f : N →ₗ[ℤ_[l]] N := LinearMap.id - s ∘ₗ T.mkQ
  have hsx : ∀ x, f x ∈ T := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    have := hs' (T.mkQ x)
    simp only [Submodule.mkQ_apply] at this
    simp [f, this]
  let t : N →ₗ[ℤ_[l]] T := LinearMap.codRestrict T f hsx
  let p : N →ₗ[ℤ_[l]] (Fin (Module.finrank ℤ_[l] N) → ℤ_[l]) := b.equivFun.toLinearMap ∘ₗ T.mkQ
  have htv : ∀ x, (t x : N) = x - s (T.mkQ x) := fun x => rfl
  have hmk0 : ∀ y : T, T.mkQ (y : N) = 0 := fun y => (Submodule.Quotient.mk_eq_zero T).mpr y.2
  have hker : ∀ c : Fin m → ℤ_[l], (∀ i, c i ∈ Ideal.span {(l : ℤ_[l]) ^ K}) → t (g c) = 0 := by
    intro c hc
    choose c' hc' using fun i => Ideal.mem_span_singleton'.mp (hc i)
    have : c = ((l : ℤ_[l]) ^ K) • c' := funext fun i => by simp [← hc' i, mul_comm]
    rw [this, map_smul, map_smul, hkill]
  refine ⟨?_, p, t, hlin p, ?_, fun y => ⟨?_, ?_⟩, ?_, ?_⟩
  · haveI : NeZero (l ^ K) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    refine Finite.of_surjective (fun d : Fin m → ZMod (l ^ K) => t (g (fun i => ((d i).val : ℤ_[l])))) ?_
    intro y
    obtain ⟨c, hc⟩ := hg (y : N)
    refine ⟨fun i => PadicInt.toZModPow K (c i), ?_⟩
    have h1 : t (g c) = y := by
      apply Subtype.ext
      rw [htv, hc, hmk0, map_zero, sub_zero]
    rw [← h1, ← sub_eq_zero, ← map_sub, ← map_sub]
    apply hker
    intro i
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp [map_sub, ZMod.natCast_zmod_val]
  · refine hq.isCoinducing.isOpen_preimage.mp ?_
    show IsOpen ((LinearMap.ker (t ∘ₗ g) : Submodule ℤ_[l] (Fin m → ℤ_[l])) : Set (Fin m → ℤ_[l]))
    refine Submodule.isOpen_mono (U := Submodule.pi Set.univ (fun _ => Ideal.span {(l : ℤ_[l]) ^ K})) ?_ ?_
    · intro c hc
      exact LinearMap.mem_ker.mpr (hker c (fun i => hc i (Set.mem_univ i)))
    · rw [Submodule.coe_pi]
      exact isOpen_set_pi Set.finite_univ (fun i _ => hopenI)
  · show b.equivFun (T.mkQ y) = 0
    rw [hmk0, map_zero]
  · exact Subtype.ext (by rw [htv, hmk0, map_zero, sub_zero])
  · intro x x' hxx
    simp only [Prod.mk.injEq] at hxx
    obtain ⟨h1, h2⟩ := hxx
    have hq' : T.mkQ x = T.mkQ x' := b.equivFun.injective h1
    have h3 := congrArg Subtype.val h2
    rw [htv, htv, hq'] at h3
    exact sub_left_injective h3
  · rintro ⟨v, y⟩
    refine ⟨s (b.equivFun.symm v) + y, ?_⟩
    have hm : T.mkQ (s (b.equivFun.symm v) + y) = b.equivFun.symm v := by
      rw [map_add, hs', hmk0, add_zero]
    refine Prod.ext ?_ ?_
    · show b.equivFun (T.mkQ _) = v
      rw [hm, LinearEquiv.apply_symm_apply]
    · apply Subtype.ext
      show (t _ : N) = y
      rw [htv, hm]
      abel
