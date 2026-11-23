import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem levOp_id_mem_inf_fixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K' : Subgroup G) (F : G → ℂ) (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x)
    (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, ρ g v ∈ M) (v : V) (hv : v ∈ M ⊓ fixed ρ K') :
    levOp ρ K K' F LinearMap.id v ∈ M ⊓ fixed ρ K' := by
  obtain ⟨hvM, hvK⟩ := Submodule.mem_inf.1 hv
  have hfix : ∀ k ∈ K', ρ k v = v := fun k hk => by simpa using hvK ⟨k, hk⟩
  set φ : G ⧸ K' → V →ₗ[ℂ] V := fun q => F q.out • (ρ q.out ∘ₗ LinearMap.id) with hφ
  unfold levOp
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  by_cases hs : (Function.support φ).Finite
  · have hs' : (Function.support fun q => φ q v).Finite :=
      hs.subset (fun q hq h => hq (by simp [h]))
    have happ : (∑ᶠ q, φ q) v = ∑ᶠ q, φ q v := map_finsum (LinearMap.applyₗ v) hs
    rw [happ]
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [finsum_eq_sum _ hs']
      exact Submodule.sum_mem _ fun q _ => M.smul_mem _ (hM _ _ hvM)
    · intro k
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      rw [map_finsum (ρ (k : G)) hs']
      have key : ∀ q : G ⧸ K', ρ (k : G) (φ q v) = φ ((k : G) • q) v := by
        intro q
        have hq : ((((k : G) • q).out : G) : G ⧸ K') = ((k : G) * q.out : G) := by
          rw [QuotientGroup.out_eq']
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        have hk2 : ((k : G) * q.out)⁻¹ * ((k : G) • q).out ∈ K' := QuotientGroup.eq.1 hq.symm
        obtain ⟨c, hc, hg'⟩ : ∃ c ∈ K', ((k : G) • q).out = (k : G) * q.out * c := ⟨_, hk2, by group⟩
        simp only [hφ, LinearMap.smul_apply, LinearMap.comp_id, map_smul]
        rw [hg', (hF _ hc _).2, (hF _ k.2 _).1, map_mul, Module.End.mul_apply, hfix _ hc, map_mul,
          Module.End.mul_apply]
      rw [finsum_congr key]
      exact finsum_comp_equiv (MulAction.toPerm (k : G)) (f := fun q => φ q v)
  · rw [finsum_of_infinite_support hs]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_mul_left_eq {w : Pl E} {U : Subgroup (UL n w)} (g : UL n w → ℂ) (hg : ∀ k ∈ U, ∀ x, g (k * x) = g x)
    (a : UL n w) (ha : a ∈ U) (y : GLw n w) : g (toSub (UL n w) (a.1 * y)) = g (toSub (UL n w) y) := by
  unfold toSub
  by_cases hy : y ∈ UL n w
  · rw [dif_pos (mul_mem a.2 hy), dif_pos hy, ← hg a ha ⟨y, hy⟩]
    rfl
  · have : a.1 * y ∉ UL n w := fun h => hy (by simpa using mul_mem (inv_mem a.2) h)
    rw [dif_neg this, dif_neg hy]

theorem toSub_mul_right_eq {w : Pl E} {U : Subgroup (UL n w)} (g : UL n w → ℂ) (hg : ∀ k ∈ U, ∀ x, g (x * k) = g x)
    (a : UL n w) (ha : a ∈ U) (y : GLw n w) : g (toSub (UL n w) (y * a.1)) = g (toSub (UL n w) y) := by
  unfold toSub
  by_cases hy : y ∈ UL n w
  · rw [dif_pos (mul_mem hy a.2), dif_pos hy, ← hg a ha ⟨y, hy⟩]
    rfl
  · have : y * a.1 ∉ UL n w := fun h => hy (by simpa using mul_mem h (inv_mem a.2))
    rw [dif_neg this, dif_neg hy]

theorem mem_globLev_iff (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (k : finU E n) :
    k ∈ globLev S K' ↔ ∀ w ∈ S, ∃ a ∈ K' w, (a : GLw n w) = cLoc w k.1 := by
  simp [globLev, Subgroup.mem_iInf]

theorem globFn_inv (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
    (hf : ∀ w, ∀ k ∈ K' w, ∀ x, f w (k * x) = f w x ∧ f w (x * k) = f w x) :
    ∀ k ∈ globLev S K', ∀ x, globFn S f (k * x) = globFn S f x ∧ globFn S f (x * k) = globFn S f x := by
  intro k hk x
  rw [mem_globLev_iff] at hk
  constructor
  · unfold globFn
    refine finprod_mem_congr rfl fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := hk w hw
    rw [Subgroup.coe_mul, map_mul, ← hae]
    exact toSub_mul_left_eq (f w) (fun k hk x => (hf w k hk x).1) a ha _
  · unfold globFn
    refine finprod_mem_congr rfl fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := hk w hw
    rw [Subgroup.coe_mul, map_mul, ← hae]
    exact toSub_mul_right_eq (f w) (fun k hk x => (hf w k hk x).2) a ha _

end GlobalTheory.BCT

open GlobalTheory.BCT in

theorem GlobalTheory.BCT.hop_mem_inf_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ v ∈ π ⊓ fixed (RF E n) (globLev S K'), hop S K' f v ∈ π ⊓ fixed (RF E n) (globLev S K') := by
  intro E _ _ _ n S _ K' _ f hf π hπ v hv
  exact levOp_id_mem_inf_fixed (RF E n) _ _ _ (globFn_inv S K' f fun w => (hf.1 w).2) π
    (fun g v hv => hπ.stable _ v hv) v hv
