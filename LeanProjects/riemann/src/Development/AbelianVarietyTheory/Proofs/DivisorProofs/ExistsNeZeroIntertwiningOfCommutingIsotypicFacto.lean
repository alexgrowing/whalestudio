import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.IsotypicFactors

open Representation Module

section One

variable {H W V : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]

theorem finiteDimensional_of_isotypic [FiniteDimensional ℂ V] [Nontrivial V]
    (τ : Representation ℂ H V) (ρ : Representation ℂ H W) (hρ : ρ.IsIrreducible)
    (h : IsIsotypicOf τ ρ) : FiniteDimensional ℂ W := by
  have : ∃ g : IntertwiningMap ρ τ, g ≠ 0 := by
    by_contra hc
    push Not at hc
    have : (⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap) = ⊥ := by
      refine iSup_eq_bot.2 fun f => ?_
      rw [hc f]
      exact LinearMap.range_eq_bot.2 rfl
    exact bot_ne_top (this.symm.trans h)
  obtain ⟨g, hg⟩ := this
  have hi := (IsIrreducible.injective_or_eq_zero g).resolve_right hg
  exact FiniteDimensional.of_injective g.toLinearMap hi

theorem classSum_scalar [Fintype H] [FiniteDimensional ℂ W] (ρ : Representation ℂ H W)
    (hρ : ρ.IsIrreducible) (h : H) : ∃ s : ℂ, ∀ w, (∑ k, ρ (k * h * k⁻¹)) w = s • w := by
  have hT : ∀ g v, (∑ k, ρ (k * h * k⁻¹)) (ρ g v) = ρ g ((∑ k, ρ (k * h * k⁻¹)) v) := by
    intro g v
    simp only [LinearMap.sum_apply, map_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft g)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  obtain ⟨c, hc⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).2
    ((∑ k, ρ (k * h * k⁻¹)).intertwiningMap_of_isIntertwiningMap ρ ρ hT)
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun f : IntertwiningMap ρ ρ => f v) hc
  simpa using this.symm

theorem classSum_of_isotypic [Fintype H] (τ : Representation ℂ H V) (ρ : Representation ℂ H W)
    (hi : IsIsotypicOf τ ρ) (h : H) (s : ℂ) (hs : ∀ w, (∑ k, ρ (k * h * k⁻¹)) w = s • w) :
    (∑ k, τ (k * h * k⁻¹)) = s • (1 : Module.End ℂ V) := by
  have : (⊤ : Submodule ℂ V) ≤ LinearMap.eqLocus (∑ k, τ (k * h * k⁻¹)) (s • (1 : Module.End ℂ V)) := by
    rw [← (show _ = ⊤ from hi)]
    refine iSup_le fun f => ?_
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_eqLocus]
    have e := congrArg f.toLinearMap (hs w)
    simp only [LinearMap.sum_apply, map_sum, map_smul] at e
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.one_apply, ← e]
    exact Finset.sum_congr rfl fun k _ => (f.isIntertwining _ _ _ w).symm
  exact LinearMap.ext fun v => this Submodule.mem_top

theorem card_mul_character {M : Type} [Group M] [Fintype H] (τ : Representation ℂ M V) (f : H →* M)
    (h : H) (s : ℂ) (hs : (∑ k, τ (f (k * h * k⁻¹))) = s • (1 : Module.End ℂ V)) (a : M)
    (ha : ∀ k, Commute (f k) a) :
    (Fintype.card H : ℂ) * τ.character (f h * a) = s * τ.character a := by
  have e := congrArg (fun T => LinearMap.trace ℂ V (T * τ a)) hs
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, one_mul, map_smul, smul_eq_mul] at e
  have e2 : ∀ k, LinearMap.trace ℂ V (τ (f (k * h * k⁻¹)) * τ a) = τ.character (f h * a) := by
    intro k
    rw [← map_mul, ← char_conj τ (f h * a) (f k)]
    have : f (k * h * k⁻¹) * a = f k * (f h * a) * (f k)⁻¹ := by
      rw [map_mul, map_mul, mul_assoc, (ha k⁻¹).eq, map_inv]
      simp only [mul_assoc]
    rw [this]
    rfl
  simp only [e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at e
  exact e

end One

theorem exists_ne_zero {G V W : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [Nontrivial V]
    [Nontrivial W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (h : ∀ g, (finrank ℂ W : ℂ) * ρ.character g = (finrank ℂ V : ℂ) * σ.character g) :
    ∃ f : IntertwiningMap ρ σ, f ≠ 0 := by
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have h1 := card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  have h2 := card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  have h4 : (finrank ℂ W : ℂ) * finrank ℂ (IntertwiningMap ρ ρ)
      = (finrank ℂ V : ℂ) * finrank ℂ (IntertwiningMap ρ σ) := by
    rw [← h1, ← h2, mul_left_comm, mul_left_comm (finrank ℂ V : ℂ),
      Finset.mul_sum _ _ (finrank ℂ V : ℂ), Finset.mul_sum _ _ (finrank ℂ W : ℂ)]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← mul_assoc, ← mul_assoc, h]
  have : Nontrivial (IntertwiningMap ρ ρ) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨⟨IntertwiningMap.id ρ, 0, fun e => hv (congrArg (fun f : IntertwiningMap ρ ρ => f v) e)⟩⟩
  have h5 : finrank ℂ W * finrank ℂ (IntertwiningMap ρ ρ)
      = finrank ℂ V * finrank ℂ (IntertwiningMap ρ σ) := by exact_mod_cast h4
  have h3 : 0 < finrank ℂ (IntertwiningMap ρ σ) := by
    have : 0 < finrank ℂ W * finrank ℂ (IntertwiningMap ρ ρ) :=
      Nat.mul_pos Module.finrank_pos Module.finrank_pos
    rw [h5] at this
    exact Nat.pos_of_mul_pos_left this
  have := Module.nontrivial_of_finrank_pos h3
  exact exists_ne 0

theorem exists_intertwining_ne_zero : ∀ (M : Type) [Group M] [Finite M] (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Group (H c)] [∀ c, Finite (H c)] (f : ∀ c, H c →* M), (⨆ c, (f c).range) = ⊤ → (∀ c c', c ≠ c' → ∀ (x : H c) (y : H c'), Commute (f c x) (f c' y)) → ∀ (W : ι → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)] (ρ : ∀ c, Representation ℂ (H c) (W c)), (∀ c, (ρ c).IsIrreducible) → ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] [Nontrivial V'] (τ : Representation ℂ M V) (τ' : Representation ℂ M V'), (∀ c, IsIsotypicOf (show Representation ℂ (H c) V from τ.comp (f c)) (ρ c)) → (∀ c, IsIsotypicOf (show Representation ℂ (H c) V' from τ'.comp (f c)) (ρ c)) → ∃ T : Representation.IntertwiningMap τ τ', T ≠ 0 := by
  intro M _ _ ι _ H _ _ f htop hcomm W _ _ ρ hρ V V' _ _ _ _ _ _ _ _ τ τ' hτ hτ'
  classical
  have := Fintype.ofFinite ι
  have hcomm' : Pairwise fun i j : ι => ∀ (x : H i) (y : H j), Commute (f i x) (f j y) :=
    fun i j hij => hcomm i j hij
  refine exists_ne_zero τ τ' fun m => ?_
  obtain ⟨h, rfl⟩ : m ∈ (MonoidHom.noncommPiCoprod f hcomm').range := by
    rw [MonoidHom.noncommPiCoprod_range, htop]
    exact Subgroup.mem_top m
  have key : ∀ (S : Finset ι) (comm : (S : Set ι).Pairwise (Function.onFun Commute fun i => f i (h i))),
      (finrank ℂ V' : ℂ) * τ.character (S.noncommProd (fun i => f i (h i)) comm)
        = (finrank ℂ V : ℂ) * τ'.character (S.noncommProd (fun i => f i (h i)) comm) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro comm; simp [mul_comm]
    | insert c S hc ih =>
      intro comm
      have := Fintype.ofFinite (H c)
      have := finiteDimensional_of_isotypic _ _ (hρ c) (hτ c)
      obtain ⟨s, hs⟩ := classSum_scalar (ρ c) (hρ c) (h c)
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hc]
      have ha : ∀ comm k, Commute (f c k) (S.noncommProd (fun i => f i (h i)) comm) := fun comm k =>
        Finset.noncommProd_commute _ _ _ _ fun i hi => hcomm c i (fun e => hc (e ▸ hi)) _ _
      have hcard : (Fintype.card (H c) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      refine mul_left_cancel₀ hcard ?_
      rw [mul_left_comm, card_mul_character τ (f c) (h c) s (classSum_of_isotypic _ _ (hτ c) _ _ hs) _ (ha _),
        mul_left_comm (Fintype.card (H c) : ℂ),
        card_mul_character τ' (f c) (h c) s (classSum_of_isotypic _ _ (hτ' c) _ _ hs) _ (ha _),
        mul_left_comm, ih, mul_left_comm]
  exact key Finset.univ fun _ _ _ _ hij => hcomm' hij _ _

end GlobalTheory.IsotypicFactors
