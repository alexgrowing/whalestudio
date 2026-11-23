import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaSysUOfHalves
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KumFix

theorem pow_val_add {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] {ζ : Ω} (h : ζ ^ n = 1) (a b : ZMod n) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) n, pow_add, pow_mul, h, one_pow, mul_one]

theorem isClosed_of_le {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H N U : Subgroup Γ)
    (hH : IsClosed (H : Set Γ)) (hU : IsOpen (U : Set Γ)) (hNH : N ≤ H) (hUN : ∀ s ∈ H, s ∈ U → s ∈ N) :
    IsClosed (N : Set Γ) := by
  have h1 : IsOpen ((U.subgroupOf H : Subgroup H) : Set H) := hU.preimage continuous_subtype_val
  have h2 : IsOpen ((N.subgroupOf H : Subgroup H) : Set H) :=
    Subgroup.isOpen_mono (H₁ := U.subgroupOf H) (fun s hs => hUN s s.2 hs) h1
  have h3 : IsClosed ((N.subgroupOf H : Subgroup H) : Set H) := Subgroup.isClosed_of_isOpen _ h2
  have h4 := hH.isClosedMap_subtype_val _ h3
  convert h4 using 1
  ext s
  constructor
  · intro hs
    exact ⟨⟨s, hNH hs⟩, hs, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ht

theorem exists_eigen {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {n : ℕ} [NeZero n] (H : Subgroup (G ℚ Ω))
    (hH : IsClosed (H : Set (G ℚ Ω))) (ζ : Ω) (hζ : ζ ^ n = 1) (hfix : ∀ s ∈ H, s ζ = ζ) (χ : G ℚ Ω → ZMod n)
    (hχ : ∀ s ∈ H, ∀ t ∈ H, χ (s * t) = χ s + χ t) (U : Subgroup (G ℚ Ω)) (hU : IsOpen (U : Set (G ℚ Ω)))
    (hUχ : ∀ s ∈ H, s ∈ U → χ s = 0) : ∃ w : Ω, w ≠ 0 ∧ ∀ s ∈ H, s w = ζ ^ (χ s).val * w := by
  classical
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne n)] at hζ
    exact zero_ne_one hζ
  have h1 : χ 1 = 0 := by
    have := hχ 1 H.one_mem 1 H.one_mem
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hinv : ∀ s ∈ H, χ s⁻¹ = -χ s := by
    intro s hs
    have := hχ s⁻¹ (H.inv_mem hs) s hs
    rw [inv_mul_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  let N : Subgroup (G ℚ Ω) :=
    { carrier := {s | s ∈ H ∧ χ s = 0}
      mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, by rw [hχ a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨H.one_mem, h1⟩
      inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, by rw [hinv a ha.1, ha.2, neg_zero]⟩ }
  have hNc : IsClosed (N : Set (G ℚ Ω)) :=
    isClosed_of_le H N U hH hU (fun s hs => hs.1) (fun s hs hsU => ⟨hs, hUχ s hs hsU⟩)
  have hNfix : (IntermediateField.fixedField N).fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N, hNc⟩
  let E := IntermediateField.fixedField N
  let ι := {k : ZMod n // ∃ g ∈ H, χ g = k}
  choose r hrH hrχ using fun k : ι => k.2
  let f : ι → (E →* Ω) := fun k =>
    { toFun := fun x => r k (x : Ω)
      map_one' := by simp
      map_mul' := fun x y => by simp }
  have hf : Function.Injective f := by
    intro j k hjk
    have hm : (r j)⁻¹ * r k ∈ N := by
      rw [← hNfix, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have e : r j x = r k x := DFunLike.congr_fun hjk ⟨x, hx⟩
      rw [AlgEquiv.mul_apply, ← e]
      exact (r j).symm_apply_apply x
    have h2 := hm.2
    rw [hχ _ (H.inv_mem (hrH j)) _ (hrH k), hinv _ (hrH j), hrχ, hrχ] at h2
    exact Subtype.ext (neg_add_eq_zero.mp h2)
  have hli := (linearIndependent_monoidHom E Ω).comp f hf
  have hex : ∃ x : E, ∑ k : ι, ζ ^ (-(k : ZMod n)).val * r k (x : Ω) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := Fintype.linearIndependent_iff.mp hli (fun k => ζ ^ (-(k : ZMod n)).val) (by
      funext x
      rw [Finset.sum_apply]
      exact hcon x) ⟨0, 1, H.one_mem, h1⟩
    exact pow_ne_zero _ hζ0 this
  obtain ⟨x, hx⟩ := hex
  refine ⟨_, hx, fun s hs => ?_⟩
  let e : ι ≃ ι :=
    { toFun := fun k => ⟨χ s + k, s * r k, H.mul_mem hs (hrH k), by rw [hχ _ hs _ (hrH k), hrχ]⟩
      invFun := fun k => ⟨-χ s + k, s⁻¹ * r k, H.mul_mem (H.inv_mem hs) (hrH k), by
        rw [hχ _ (H.inv_mem hs) _ (hrH k), hrχ, hinv s hs]⟩
      left_inv := fun k => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }
  rw [map_sum, Finset.mul_sum, ← Equiv.sum_comp e (fun k : ι => ζ ^ (χ s).val * (ζ ^ (-(k : ZMod n)).val * r k (x : Ω)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hm : (r (e k))⁻¹ * (s * r k) ∈ N := by
    refine ⟨H.mul_mem (H.inv_mem (hrH _)) (H.mul_mem hs (hrH k)), ?_⟩
    rw [hχ _ (H.inv_mem (hrH _)) _ (H.mul_mem hs (hrH k)), hinv _ (hrH _), hχ _ hs _ (hrH k), hrχ, hrχ]
    exact neg_add_cancel _
  have hx1 : ((r (e k))⁻¹ * (s * r k)) (x : Ω) = x := (IntermediateField.mem_fixedField_iff N x).mp x.2 _ hm
  have hx2 : s (r k (x : Ω)) = r (e k) (x : Ω) := by
    have := congrArg (r (e k)) hx1
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
    rw [← this]
    exact ((r (e k)).apply_symm_apply _).symm
  rw [map_mul, map_pow, hfix s hs, hx2, ← mul_assoc, ← pow_val_add hζ]
  congr 3
  change -(k : ZMod n) = χ s + -(χ s + k)
  ring

theorem exists_kumVal : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) (H : Subgroup (G ℚ Ω)), IsClosed (H : Set (G ℚ Ω)) → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → (∀ s ∈ H, s ζ = ζ) → ∀ χ : G ℚ Ω → ZMod (l ^ m), (∀ s ∈ H, ∀ t ∈ H, χ (s * t) = χ s + χ t) → ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → (∀ s ∈ H, s ∈ U → χ s = 0) → ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ H, s u = u) ∧ ∀ s ∈ H, GlobalTheory.Col.KumVal (l := l) m ζ u s (χ s) := by
  intro l _ Ω _ _ _ m H hH ζ hζ hfix χ hχ U hU hUχ
  haveI : NeZero (l ^ m) := ⟨(pow_pos (Fact.out : l.Prime).pos m).ne'⟩
  obtain ⟨w, hw0, hw⟩ := exists_eigen H hH ζ hζ.pow_eq_one hfix χ hχ U hU hUχ
  refine ⟨w ^ (l ^ m), pow_ne_zero _ hw0, fun s hs => ?_, fun s hs => ⟨w, rfl, hw s hs⟩⟩
  rw [map_pow, hw s hs, mul_pow, ← pow_mul, mul_comm (χ s).val, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

end GlobalTheory.KumFix
