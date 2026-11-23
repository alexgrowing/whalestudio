import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.Base

set_option maxHeartbeats 800000 in

theorem exists_mem_span_red_eq (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop)
    (B : Base p P) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (hG : P k G) (hG' : P k' (G.baseChange k'))
    (ι : Type) (b : Module.Basis ι (WittVector p k) (B.M G hG)) (z : (G.baseChange k').RigExt) :
    ∃ n ∈ Submodule.span (WittVector p k') (Set.range fun i => B.smap hG' hG (G.toBase k') (b i)),
      B.red _ hG' n = z := by
  obtain ⟨x, rfl⟩ := G.liftSemi_rig_bijective k' (CharP.cast_eq_zero k p) (.inl inferInstance) |>.2 z
  induction x with
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [LinearMap.map_zero, LinearMap.map_zero]
  | add x y hx hy =>
    obtain ⟨n, hn, h1⟩ := hx
    obtain ⟨n', hn', h2⟩ := hy
    refine ⟨n + n', add_mem hn hn', ?_⟩
    rw [LinearMap.map_add (B.red _ hG') n n', h1, h2, LinearMap.map_add]
  | tmul r y =>
    obtain ⟨m, rfl⟩ := B.red_surjective G hG y
    obtain ⟨R, rfl⟩ := (WittVector.constantCoeff_surjective p : Function.Surjective
      (WittVector.constantCoeff : WittVector p k' →+* k')) r
    refine ⟨R • B.smap hG' hG (G.toBase k') m, Submodule.smul_mem _ _ ?_, ?_⟩
    · rw [← b.linearCombination_repr m, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
      exact Submodule.sum_mem _ fun i _ => by
        rw [B.smap_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [LinearMap.map_smulₛₗ (B.red _ hG') R, B.red_smap, liftSemi_tmul]

theorem smap_toBase_basis (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop)
    (B : Base p P) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (hG : P k G) (hG' : P k' (G.baseChange k'))
    (ι : Type) [Fintype ι] (b : Module.Basis ι (WittVector p k) (B.M G hG)) :
    ∃ b' : Module.Basis ι (WittVector p k') (B.M (G.baseChange k') hG'),
      ∀ i, b' i = B.smap hG' hG (G.toBase k') (b i) := by
  haveI := B.free G hG
  haveI := B.finite G hG
  haveI := B.free _ hG'
  haveI := B.finite _ hG'
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have hp' : (p : k') = 0 := CharP.cast_eq_zero k' p
  obtain ⟨-, hr⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p) hp
    (B.red G hG) (B.red_surjective G hG) fun m h => (B.red_eq_zero G hG m).1 h
  obtain ⟨-, hr'⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p) hp'
    (B.red _ hG') (B.red_surjective _ hG') fun m h => (B.red_eq_zero _ hG' m).1 h
  have hrank : Module.finrank k' (G.baseChange k').RigExt = Module.finrank k G.RigExt := by
    rw [← (LinearEquiv.ofBijective _ (G.liftSemi_rig_bijective k' hp (.inl inferInstance))).finrank_eq,
      Module.finrank_baseChange]
  have hmax : (p : WittVector p k') ∈ IsLocalRing.maximalIdeal (WittVector p k') := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map (WittVector.constantCoeff : WittVector p k' →+* k')
    rw [map_natCast, hp'] at this
    exact not_isUnit_zero this
  have hspan : ⊤ ≤ Submodule.span (WittVector p k')
      (Set.range fun i => B.smap hG' hG (G.toBase k') (b i)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(p : WittVector p k')})
      Module.Finite.fg_top ((Ideal.span_le.2 (Set.singleton_subset_iff.2 hmax)).trans
        (IsLocalRing.maximalIdeal_le_jacobson _)) fun m _ => ?_
    obtain ⟨n, hn, h1⟩ := exists_mem_span_red_eq p P B k k' G hG hG' ι b (B.red _ hG' m)
    obtain ⟨q, hq⟩ := (B.red_eq_zero _ hG' (m - n)).1 (by
      rw [LinearMap.map_sub (B.red _ hG') m n, h1, sub_self])
    have hm : m = n + (p : WittVector p k') • q := by
      rw [← Nat.cast_smul_eq_nsmul (WittVector p k')] at hq
      rw [← hq, add_sub_cancel]
    rw [hm]
    exact Submodule.add_mem_sup hn (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _)
      Submodule.mem_top)
  have hcard : Fintype.card ι = Module.finrank (WittVector p k') (B.M (G.baseChange k') hG') := by
    rw [← hr', hrank, hr, Module.finrank_eq_card_basis b]
  exact ⟨Module.Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard) hspan,
    fun i => Module.Basis.mk_apply _ _ i⟩

end GlobalTheory.Dieu.Base
