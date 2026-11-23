import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr

noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

section
variable {H : Type} [Group H] (U : Subgroup H) [Fintype U] (χ : H → ℂ)

def heckeIdem {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V) : Module.End ℂ V :=
  ((Fintype.card U : ℂ))⁻¹ • ∑ u : U, χ (u : H)⁻¹ • τ (u : H)

theorem heckeIdem_apply {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V) (v : V) :
    heckeIdem U χ τ v = ((Fintype.card U : ℂ))⁻¹ • ∑ u : U, χ (u : H)⁻¹ • τ (u : H) v := by
  simp [heckeIdem, LinearMap.sum_apply]

theorem heckeIdem_mem (hm : ∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y)
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V) (v : V) :
    heckeIdem U χ τ v ∈ eig τ (U : Set H) χ := by
  rw [heckeIdem_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [mem_eig]
  intro g hg
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : U)) _ _ ?_
  intro u
  have h1 : χ (u : H)⁻¹ = χ g * χ (g * u)⁻¹ := by
    rw [← hm (g) hg _ (U.inv_mem (U.mul_mem hg u.2))]
    have h2 := hm _ (U.inv_mem (U.mul_mem hg u.2)) g hg
    have h3 := hm (g) hg _ (U.inv_mem (U.mul_mem hg u.2))
    rw [h3, mul_comm (χ g), ← h2]
    simp
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_smul, smul_smul, map_mul, h1]
  rfl

theorem heckeIdem_of_mem (hm : ∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y) (h1 : χ 1 = 1)
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V) (v : V)
    (hv : v ∈ eig τ (U : Set H) χ) : heckeIdem U χ τ v = v := by
  rw [heckeIdem_apply]
  rw [mem_eig] at hv
  have : ∀ u : U, χ (u : H)⁻¹ • τ (u : H) v = v := by
    intro u
    rw [hv u u.2, smul_smul, ← hm _ (U.inv_mem u.2) _ u.2, inv_mul_cancel, h1, one_smul]
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]

theorem heckeIdem_sub {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V)
    (W : Subrepresentation τ) (w : W.toSubmodule) :
    ((heckeIdem U χ W.toRepresentation w : W.toSubmodule) : V) = heckeIdem U χ τ w := by
  rw [heckeIdem_apply, heckeIdem_apply]
  simp [Subrepresentation.toRepresentation]

theorem heckeIdem_comm_of_le_one (hm : ∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ H V)
    (hr : finrank ℂ (eig τ (U : Set H) χ) ≤ 1) (g h : H) (v : V) :
    heckeIdem U χ τ (τ g (heckeIdem U χ τ (τ h (heckeIdem U χ τ v)))) =
      heckeIdem U χ τ (τ h (heckeIdem U χ τ (τ g (heckeIdem U χ τ v)))) := by
  obtain ⟨w0, hw0⟩ := finrank_le_one_iff.mp hr
  have key : ∀ x, ∃ c : ℂ, heckeIdem U χ τ x = c • (w0 : V) := by
    intro x
    obtain ⟨c, hc⟩ := hw0 ⟨_, heckeIdem_mem U χ hm τ x⟩
    exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
  obtain ⟨c, hc⟩ := key v
  obtain ⟨a, ha⟩ := key (τ g w0)
  obtain ⟨b, hb⟩ := key (τ h w0)
  simp only [hc, map_smul, ha, hb, smul_smul]
  congr 1
  ring

theorem heckeIdem_comm [Finite H] (hm : ∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y)
    (hirr : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ H W),
      τ.IsIrreducible → finrank ℂ (eig τ (U : Set H) χ) ≤ 1) (g h : H) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ H V),
      finrank ℂ V = n → ∀ v : V,
    heckeIdem U χ τ (τ g (heckeIdem U χ τ (τ h (heckeIdem U χ τ v)))) =
      heckeIdem U χ τ (τ h (heckeIdem U χ τ (τ g (heckeIdem U χ τ v)))) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ τ hn v
    by_cases hi : τ.IsIrreducible
    · exact heckeIdem_comm_of_le_one U χ hm τ (hirr V τ hi) g h v
    rcases subsingleton_or_nontrivial V with hs | hs
    · exact Subsingleton.elim _ _
    have hex : ∃ W : Subrepresentation τ, W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra hc
      push Not at hc
      apply hi
      haveI : Nontrivial (Subrepresentation τ) := ⟨⊥, ⊤, fun e => by
        have := congrArg Subrepresentation.toSubmodule e
        exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) this⟩
      exact ⟨fun W => by
        by_cases hW : W = ⊥
        · exact Or.inl hW
        · exact Or.inr (hc W hW)⟩
    obtain ⟨W, hb, ht⟩ := hex
    haveI : NeZero (Nat.card H : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
    have hss : τ.IsSemisimpleRepresentation := inferInstance
    obtain ⟨W', hW'⟩ := hss.exists_isCompl W
    have ht' : W' ≠ ⊤ := by
      rintro rfl
      exact hb (by simpa using hW'.disjoint)
    have sub : ∀ X : Subrepresentation τ, X ≠ ⊤ → ∀ v ∈ X.toSubmodule,
        heckeIdem U χ τ (τ g (heckeIdem U χ τ (τ h (heckeIdem U χ τ v)))) =
      heckeIdem U χ τ (τ h (heckeIdem U χ τ (τ g (heckeIdem U χ τ v)))) := by
      intro X hX v hv
      have hlt : finrank ℂ X.toSubmodule < n := by
        rw [← hn]
        refine Submodule.finrank_lt ?_
        intro e
        exact hX (Subrepresentation.toSubmodule_injective e)
      have := congrArg Subtype.val (ih _ hlt X.toSubmodule X.toRepresentation rfl ⟨v, hv⟩)
      have hτ : ∀ (k : H) (x : X.toSubmodule), ((X.toRepresentation k x : X.toSubmodule) : V) = τ k x :=
        fun _ _ => rfl
      simpa only [heckeIdem_sub, hτ] using this
    have hsup : W.toSubmodule ⊔ W'.toSubmodule = ⊤ :=
      congrArg Subrepresentation.toSubmodule hW'.sup_eq_top
    have hv : v ∈ W.toSubmodule ⊔ W'.toSubmodule := hsup ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp hv
    simp only [map_add, sub W ht a ha, sub W' ht' b hb']

end

theorem exists_idem_hecke_comm : ∀ (H : Type) [Group H] [Finite H] (U : Subgroup H) (χ : H → ℂ), (∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y) → χ 1 = 1 → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ H W), τ.IsIrreducible → finrank ℂ (eig τ (U : Set H) χ) ≤ 1) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ H V), ∃ e : Module.End ℂ V, e * e = e ∧ (∀ v ∈ eig τ (U : Set H) χ, e v = v) ∧ (∀ T : Module.End ℂ V, (∀ g, Commute T (τ g)) → Commute T e) ∧ ∀ g h : H, e * τ g * e * τ h * e = e * τ h * e * τ g * e := by
  intro H _ _ U χ hm h1 hirr V _ _ _ τ
  letI : Fintype U := Fintype.ofFinite U
  refine ⟨heckeIdem U χ τ, ?_, heckeIdem_of_mem U χ hm h1 τ, ?_, ?_⟩
  · ext v
    exact heckeIdem_of_mem U χ hm h1 τ _ (heckeIdem_mem U χ hm τ v)
  · intro T hT
    exact Commute.smul_right (Commute.sum_right _ _ _ fun u _ => Commute.smul_right (hT _) _) _
  · intro g h
    ext v
    exact heckeIdem_comm U χ hm hirr g h _ V τ rfl v

end GlobalTheory.FinGL.LeviWh
