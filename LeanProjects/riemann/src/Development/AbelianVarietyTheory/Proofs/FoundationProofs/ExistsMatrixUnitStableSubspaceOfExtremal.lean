import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.ExtremalGen

open GlobalTheory.TensorHW (mem_wt diag_comm)

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def Supp (S : Ix p q → Ix p q → Prop) (Z : Mat p q) : Prop := ∀ a b, ¬ S a b → Z a b = 0

lemma supp_Eab {S : Ix p q → Ix p q → Prop} {a b : Ix p q} (h : S a b) : Supp S (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd h

lemma supp_mul {S : Ix p q → Ix p q → Prop} (hS : Equivalence S) {Y Z : Mat p q}
    (hY : Supp S Y) (hZ : Supp S Z) : Supp S (Y * Z) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : S a c
  · rw [hZ c b (fun hcb => hab (hS.trans hac hcb)), mul_zero]
  · rw [hY a c hac, zero_mul]

lemma supp_comm {S : Ix p q → Ix p q → Prop} (hS : Equivalence S) {Y Z : Mat p q}
    (hY : Supp S Y) (hZ : Supp S Z) : Supp S (Y * Z - Z * Y) := by
  intro a b hab
  rw [Matrix.sub_apply, supp_mul hS hY hZ a b hab, supp_mul hS hZ hY a b hab, sub_zero]

lemma supp_ind {S : Ix p q → Ix p q → Prop} (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (N : Submodule ℂ V) (y : V)
    (h : ∀ a b, S a b → act (Eab a b) y ∈ N) {Z : Mat p q} (hZ : Supp S Z) : act Z y ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  by_cases hab : S a b
  · have : (Matrix.single a b (Z a b) : Mat p q) = Z a b • Eab a b := by
      rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, LinearMap.smul_apply]
    exact N.smul_mem _ (h a b hab)
  · rw [hZ a b hab]
    simp

lemma lie_apply {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (Y Z : Mat p q) (y : V) :
    act Y (act Z y) = act Z (act Y y) + act (Y * Z - Z * Y) y := by
  rw [hL Y Z]
  simp

lemma eig_shift {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (c : Ix p q → ℂ)
    (a b : Ix p q) {t : ℂ} {y : V}
    (hy : y ∈ Module.End.eigenspace (act (Matrix.diagonal c)) t) :
    act (Eab a b) y ∈ Module.End.eigenspace (act (Matrix.diagonal c)) (t + (c a - c b)) := by
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  rw [lie_apply hL, diag_comm, hy, map_smul, map_smul, LinearMap.smul_apply, add_smul]

lemma eig_of_wt {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (c : Ix p q → ℂ) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ wtSub act μ) :
    v ∈ Module.End.eigenspace (act (Matrix.diagonal c)) (∑ a, c a * ((μ a : ℚ) : ℂ)) := by
  rw [mem_wt] at hv
  rw [Module.End.mem_eigenspace_iff]
  have : (Matrix.diagonal c : Mat p q) = ∑ a, c a • Eab a a := by
    ext i j
    simp only [Matrix.sum_apply, Eab, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [this]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hv, Finset.sum_smul,
    mul_smul]

theorem exists_generated :
    ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (r : Ix p q → ℕ), Function.Injective r → ∀ (μ : Ix p q → ℚ) (v : V), v ∈ wtSub act μ → (∀ a b, S a b → r a < r b → act (Eab a b) v = 0) → ∃ U : Submodule ℂ V, v ∈ U ∧ (∀ a b, S a b → ∀ x ∈ U, act (Eab a b) x ∈ U) ∧ (∀ U' : Submodule ℂ V, v ∈ U' → (∀ a b, S a b → r a < r b → ∀ x ∈ U', act (Eab b a) x ∈ U') → U ≤ U') ∧ (∀ x ∈ U, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧ ∀ (ν : Ix p q → ℚ), ∀ x ∈ U, x ≠ 0 → x ∈ wtSub act ν → ν = μ ∨ ∑ a, (r a : ℚ) * μ a < ∑ a, (r a : ℚ) * ν a := by
  intro p q V _ _ act hL S hS r hr μ v hv hup
  have hv' := mem_wt.1 hv
  set F : Set (Submodule ℂ V) :=
    {N | v ∈ N ∧ ∀ a b, S a b → r a < r b → ∀ y ∈ N, act (Eab b a) y ∈ N} with hF
  have hG : sInf F ∈ F := by
    refine ⟨Submodule.mem_sInf.2 fun M hM => hM.1, fun a b hab hlt y hy => ?_⟩
    exact Submodule.mem_sInf.2 fun M hM => hM.2 a b hab hlt y (Submodule.mem_sInf.1 hy M hM)
  have hG' : (sInf F ⊓ ⨅ (Z : Mat p q) (_ : Supp S Z), (sInf F).comap (act Z)) ∈ F := by
    constructor
    · simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
      refine ⟨hG.1, fun Z hZ => supp_ind act _ v (fun a b hab => ?_) hZ⟩
      rcases lt_trichotomy (r a) (r b) with h | h | h
      · rw [hup a b hab h]; exact Submodule.zero_mem _
      · obtain rfl := hr h
        rw [hv']; exact Submodule.smul_mem _ _ hG.1
      · exact hG.2 b a (hS.symm hab) h v hG.1
    · intro a b hab hlt y hy
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hy ⊢
      refine ⟨hG.2 a b hab hlt y hy.1, fun Z hZ => ?_⟩
      have hE := supp_Eab (hS.symm hab)
      rw [lie_apply hL]
      exact Submodule.add_mem _ (hG.2 a b hab hlt _ (hy.2 Z hZ)) (hy.2 _ (supp_comm hS hZ hE))
  set c : Ix p q → ℂ := fun a => (r a : ℂ) with hc
  set h : Module.End ℂ V := act (Matrix.diagonal c) with hh
  have hcast : ∀ ν : Ix p q → ℚ,
      ∑ a, c a * ((ν a : ℚ) : ℂ) = ((∑ a, (r a : ℚ) * ν a : ℚ) : ℂ) := by
    intro ν; simp [hc]
  have heig : ∀ (ν : Ix p q → ℚ) (x : V), x ∈ wtSub act ν →
      x ∈ h.eigenspace ((∑ a, (r a : ℚ) * ν a : ℚ) : ℂ) := by
    intro ν x hx
    rw [← hcast]; exact eig_of_wt c hx
  set m : ℚ := ∑ a, (r a : ℚ) * μ a with hm
  have hvm : v ∈ h.eigenspace (m : ℂ) := heig μ v hv
  set Q : Submodule ℂ V := ⨆ (t : ℚ) (_ : m < t), h.eigenspace (t : ℂ) with hQ
  have hshift : ∀ a b, r a < r b → ∀ t : ℚ, m ≤ t →
      ∀ y ∈ h.eigenspace (t : ℂ), act (Eab b a) y ∈ Q := by
    intro a b hab t ht y hy
    have h1 := eig_shift hL c b a hy
    have h2 : (t : ℂ) + (c b - c a) = ((t + ((r b : ℚ) - (r a : ℚ)) : ℚ) : ℂ) := by simp [hc]
    rw [h2] at h1
    have h3 : (r a : ℚ) < r b := by exact_mod_cast hab
    exact (le_iSup₂_of_le (f := fun (t : ℚ) (_ : m < t) => h.eigenspace (t : ℂ)) _
      (by linarith) le_rfl : _ ≤ Q) h1
  have hlow : ∀ a b, r a < r b → ∀ y ∈ (ℂ ∙ v) ⊔ Q, act (Eab b a) y ∈ Q := by
    intro a b hab
    have : (ℂ ∙ v) ⊔ Q ≤ Q.comap (act (Eab b a)) := by
      refine sup_le ?_ (iSup₂_le fun t ht y hy => hshift a b hab t ht.le y hy)
      rw [Submodule.span_singleton_le_iff_mem]
      exact hshift a b hab m le_rfl v hvm
    exact this
  have hle : sInf F ≤ (ℂ ∙ v) ⊔ Q :=
    sInf_le ⟨Submodule.mem_sup_left (Submodule.mem_span_singleton_self v),
      fun a b _ hab y hy => Submodule.mem_sup_right (hlow a b hab y hy)⟩
  have hQle : ∀ n : ℚ, n ≤ m → Q ≤ ⨆ (j : ℂ) (_ : j ≠ (n : ℂ)), h.eigenspace j := by
    intro n hn
    refine iSup₂_le fun t ht => le_iSup₂_of_le (t : ℂ) ?_ le_rfl
    intro he
    have : t = n := by exact_mod_cast he
    linarith
  have hline : ∀ x ∈ sInf F, x ∈ h.eigenspace (m : ℂ) → ∃ s : ℂ, x = s • v := by
    intro x hx hxm
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hle hx)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hzm : z ∈ h.eigenspace (m : ℂ) := by
      have := Submodule.sub_mem _ hxm (Submodule.smul_mem _ s hvm)
      simpa using this
    have hz0 : z = 0 :=
      Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep h (m : ℂ)) z hzm
        (hQle m le_rfl hz)
    exact ⟨s, by rw [hz0, add_zero]⟩
  refine ⟨sInf F, hG.1, fun a b hab x hx => ?_, fun U' h1 h2 => sInf_le ⟨h1, h2⟩,
    fun x hx hxμ => hline x hx (heig μ x hxμ), fun ν x hx hx0 hxν => ?_⟩
  · have := sInf_le hG' hx
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at this
    exact this.2 _ (supp_Eab hab)
  · have hxn := heig ν x hxν
    set n : ℚ := ∑ a, (r a : ℚ) * ν a with hn
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exact Or.inr hlt
    · left
      rw [← heq] at hxn
      obtain ⟨s, hs⟩ := hline x hx hxn
      have hxμ : x ∈ wtSub act μ := hs ▸ Submodule.smul_mem _ s hv
      funext a
      have h1 := mem_wt.1 hxν a
      rw [mem_wt.1 hxμ a] at h1
      have h2 := smul_left_injective ℂ hx0 h1
      exact_mod_cast h2.symm
    · exfalso
      apply hx0
      refine Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep h (n : ℂ)) x hxn ?_
      refine (sup_le ?_ (hQle n hgt.le) : (ℂ ∙ v) ⊔ Q ≤ _) (hle hx)
      rw [Submodule.span_singleton_le_iff_mem]
      have hne : (m : ℂ) ≠ (n : ℂ) := by exact_mod_cast hgt.ne'
      exact (le_iSup₂_of_le (f := fun (j : ℂ) (_ : j ≠ (n : ℂ)) => h.eigenspace j) (m : ℂ) hne
        le_rfl : _ ≤ _) hvm

end GlobalTheory.ExtremalGen
