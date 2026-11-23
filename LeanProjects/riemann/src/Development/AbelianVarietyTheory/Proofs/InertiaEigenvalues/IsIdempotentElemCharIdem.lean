import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (mem_fixed)

namespace GlobalTheory.LocGL

section FiniteGroup

variable {G V W X Y : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ W]

theorem charIdem_apply (σ : Representation ℂ G V) (τ : Representation ℂ G W) (v : V) :
    charIdem σ τ v =
      ((Module.finrank ℂ W : ℂ) / Fintype.card G) • ∑ g : G, LinearMap.trace ℂ W (τ g⁻¹) • σ g v := by
  simp [charIdem, LinearMap.sum_apply]

theorem map_charIdem {σ : Representation ℂ G V} {σ' : Representation ℂ G X} (φ : σ.IntertwiningMap σ')
    (τ : Representation ℂ G W) (v : V) : φ (charIdem σ τ v) = charIdem σ' τ (φ v) := by
  simp only [charIdem_apply, map_smul, map_sum, φ.isIntertwining]

theorem charIdem_apply_rep (σ : Representation ℂ G V) (τ : Representation ℂ G W) (h : G) (v : V) :
    charIdem σ τ (σ h v) = σ h (charIdem σ τ v) := by
  simp only [charIdem_apply, map_smul, map_sum]
  congr 1
  refine (Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ fun g => ?_).symm
  have e : LinearMap.trace ℂ W (τ (h * g * h⁻¹)⁻¹) = LinearMap.trace ℂ W (τ g⁻¹) := by
    rw [show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ by group]
    exact τ.char_conj g⁻¹ h
  show _ = LinearMap.trace ℂ W (τ (h * g * h⁻¹)⁻¹) • σ (h * g * h⁻¹) (σ h v)
  rw [e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]

theorem commute_charIdem (σ : Representation ℂ G V) (τ : Representation ℂ G W) (h : G) :
    Commute (charIdem σ τ) (σ h) := LinearMap.ext (charIdem_apply_rep σ τ h)

def coeffMap (σ : Representation ℂ G V) (τ : Representation ℂ G W) (ℓ : Module.Dual ℂ W) (v : V) :
    τ.IntertwiningMap σ where
  toLinearMap := ∑ g : G, (ℓ ∘ₗ τ g⁻¹).smulRight (σ g v)
  isIntertwining' h := LinearMap.ext fun w => by
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul]
    refine (Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_).symm
    simp only [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem charIdem_mem (σ : Representation ℂ G V) (τ : Representation ℂ G W) (v : V) :
    charIdem σ τ v ∈ isotypic σ τ := by
  classical
  let b := Module.finBasis ℂ W
  have key : ∑ g : G, LinearMap.trace ℂ W (τ g⁻¹) • σ g v = ∑ i, coeffMap σ τ (b.coord i) v (b i) := by
    have : ∀ i, coeffMap σ τ (b.coord i) v (b i) = ∑ g : G, b.repr (τ g⁻¹ (b i)) i • σ g v := fun i => by
      show (∑ g : G, (b.coord i ∘ₗ τ g⁻¹).smulRight (σ g v)) (b i) = _
      simp [LinearMap.sum_apply]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b]
    simp [Matrix.trace, LinearMap.toMatrix_apply]
  rw [charIdem_apply, key]
  exact (isotypic σ τ).toSubmodule.smul_mem _ (Submodule.sum_mem _ fun i _ => apply_mem_isotypic _ _)

theorem charIdem_self {τ : Representation ℂ G W} (hτ : τ.IsIrreducible) : charIdem τ τ = 1 := by
  have := Model.nontrivial_of_isIrreducible hτ
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := τ)).2
    ⟨charIdem τ τ, fun g => commute_charIdem τ τ g⟩
  have h1 : charIdem τ τ = c • (1 : Module.End ℂ W) :=
    LinearMap.ext fun w => (congrArg (fun f : τ.IntertwiningMap τ => f w) hc).symm
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have ho := Representation.char_orthonormal τ τ
  rw [if_pos ⟨.refl _⟩, Nat.card_eq_fintype_card] at ho
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h2 : LinearMap.trace ℂ W (charIdem τ τ) = Module.finrank ℂ W := by
    simp only [charIdem, map_smul, map_sum, smul_eq_mul]
    rw [div_eq_mul_inv, mul_assoc]
    refine (congrArg _ (Eq.trans ?_ ho)).trans (mul_one _)
    exact congrArg _ (Finset.sum_congr rfl fun g _ => mul_comm _ _)
  rw [h1, map_smul, LinearMap.trace_one, smul_eq_mul] at h2
  rw [h1, mul_right_cancel₀ hd (h2.trans (one_mul _).symm), one_smul]

theorem charIdem_of_mem {σ : Representation ℂ G V} {τ : Representation ℂ G W} (hτ : τ.IsIrreducible) {v : V}
    (hv : v ∈ isotypic σ τ) : charIdem σ τ v = v := by
  refine Submodule.iSup_induction _ (motive := fun v => charIdem σ τ v = v) hv ?_ (map_zero _) fun x y hx hy => ?_
  · rintro f _ ⟨w, rfl⟩
    exact (map_charIdem f τ w).symm.trans (by rw [charIdem_self hτ]; rfl)
  · rw [map_add, hx, hy]

end FiniteGroup

section Compact

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ G V} {σ : Representation ℂ G W} {H : Subgroup G}

theorem map_idem (hπ : IsSmooth π) (hσ : IsSmooth σ) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) (v : V) :
    f (idem hπ hH v) = idem hσ hH (f v) := by
  obtain ⟨U, -, _, hU⟩ := exists_normal_fix hπ hH v
  letI := Fintype.ofFinite (H ⧸ U)
  rw [idem_eq_cosetSum hπ hH U hU, idem_eq_cosetSum hσ hH U fun u hu => by rw [← f.isIntertwining, hU u hu]]
  simp only [map_smul, map_sum, f.isIntertwining]

theorem map_idem_of_mem (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) {v : V}
    (hv : f v ∈ fixed σ H) : f (idem hπ hH v) = f v := by
  obtain ⟨U, -, _, hU⟩ := exists_normal_fix hπ hH v
  letI := Fintype.ofFinite (H ⧸ U)
  have hc : (Fintype.card (H ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [idem_eq_cosetSum hπ hH U hU]
  simp only [map_smul, map_sum, f.isIntertwining]
  rw [Finset.sum_congr rfl fun q _ => mem_fixed.1 hv _ (q.out : H).2, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem exists_mem_fixed_map_eq (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) {v : V}
    (hv : f v ∈ fixed σ H) : ∃ u ∈ fixed π H, f u = f v :=
  ⟨_, idem_mem hπ hH v, map_idem_of_mem hπ hH f hv⟩

theorem map_fixed_of_surjective (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) {f : π.IntertwiningMap σ}
    (hf : Function.Surjective f) : (fixed π H).map f.toLinearMap = fixed σ H := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact mem_fixed.2 fun u hu => by rw [f.toLinearMap_apply, ← f.isIntertwining, mem_fixed.1 hv u hu]
  · obtain ⟨v, rfl⟩ := hf w
    exact exists_mem_fixed_map_eq hπ hH f hw

end Compact

section LevelZero

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (GL n k) V} {σ : Representation ℂ (GL n k) W}
  {ρ : Representation ℂ (GL n k) X}

@[simp] theorem levelZeroMap_apply (f : π.IntertwiningMap σ) (v : fixed π (KOne k n)) :
    (levelZeroMap f v : W) = f v := rfl

theorem levelZeroMap_injective {f : π.IntertwiningMap σ} (hf : Function.Injective f) :
    Function.Injective (levelZeroMap f) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

theorem levelZeroMap_surjective (hπ : IsSmooth π) {f : π.IntertwiningMap σ} (hf : Function.Surjective f) :
    Function.Surjective (levelZeroMap f) := by
  rintro ⟨x, hx⟩
  obtain ⟨v, rfl⟩ := hf x
  obtain ⟨u, hu, h⟩ := exists_mem_fixed_map_eq hπ (levelPre_bot (k := k) (n := n) ▸ isCompact_levelPre ⊥) f hx
  exact ⟨⟨u, hu⟩, Subtype.ext h⟩

end LevelZero

end GlobalTheory.LocGL
