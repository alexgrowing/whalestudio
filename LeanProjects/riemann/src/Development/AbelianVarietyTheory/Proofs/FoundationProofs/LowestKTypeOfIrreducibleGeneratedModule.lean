import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixUnitStableSubspaceOfExtremal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LowestWeightGeneratedFiltration
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHighestWeightVectorOfKStable

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.LowestType

open GlobalTheory.TensorHW

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def zc (p q : ℕ) : Mat p q :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => 0))

lemma zc_eq : zc p q = ∑ i : Fin p, Eab (Sum.inl i) (Sum.inl i) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [zc, Eab, Matrix.sum_apply, Matrix.single_apply, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; simp [Finset.filter_eq']
  · rw [if_neg h, eq_comm]
    simp only [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨rfl, rfl⟩
    exact h rfl

lemma act_zc (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x : V) :
    act (zc p q) x = ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) x := by
  rw [zc_eq, map_sum, LinearMap.sum_apply]

lemma zc_comm {X : Mat p q} (hX : IsKC X) : zc p q * X = X * zc p q := by
  ext a b
  rw [zc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rcases a with a | a <;> rcases b with b | b
  · simp
  · simp [hX (.inl a) (.inr b) (by simp [sameBlock])]
  · simp [hX (.inr a) (.inl b) (by simp [sameBlock])]
  · simp

lemma kstable_eig {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (t : ℂ) :
    KStable act (Module.End.eigenspace (act (zc p q)) t) := by
  intro X hX w hw
  rw [Module.End.mem_eigenspace_iff] at hw ⊢
  have h := hL (zc p q) X
  rw [zc_comm hX, sub_self, map_zero, eq_comm, sub_eq_zero] at h
  have h2 := LinearMap.congr_fun h w
  simp only [Module.End.mul_apply] at h2
  rw [h2, hw, map_smul]

lemma kstable_inf {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {A B : Submodule ℂ V}
    (hA : KStable act A) (hB : KStable act B) : KStable act (A ⊓ B) :=
  fun X hX w hw => ⟨hA X hX w hw.1, hB X hX w hw.2⟩

lemma wt_eig {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {x : V}
    (hx : x ∈ wtSub act μ) :
    x ∈ Module.End.eigenspace (act (zc p q)) ((∑ i : Fin p, μ (Sum.inl i) : ℚ) : ℂ) := by
  rw [Module.End.mem_eigenspace_iff, act_zc]
  simp only [mem_wt.1 hx]
  rw [← Finset.sum_smul]
  push_cast
  rfl

lemma eig_le (f : Module.End ℂ V) (c : ℂ) (N : ℕ → Submodule ℂ V) (hN : (⨆ m, N m) = ⊤)
    (h : ∀ m : ℕ, N m ≤ f.eigenspace (c + m)) (t : ℂ) :
    f.eigenspace t ≤ ⨆ m : ℕ, ⨆ _ : c + m = t, N m := by
  intro x hx
  have h1 : (⊤ : Submodule ℂ V) ≤ (⨆ m : ℕ, ⨆ _ : c + m = t, N m) ⊔ ⨆ s, ⨆ _ : s ≠ t, f.eigenspace s := by
    rw [← hN]
    refine iSup_le fun m => ?_
    by_cases hm : c + m = t
    · exact le_sup_of_le_left (le_iSup₂_of_le m hm le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le (c + m) hm (h m))
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h1 (Submodule.mem_top : x ∈ ⊤))
  have ha' : a ∈ f.eigenspace t := by
    refine (iSup₂_le fun m hm => ?_ : (⨆ m : ℕ, ⨆ _ : c + m = t, N m) ≤ f.eigenspace t) ha
    rw [← hm]; exact h m
  have hb' : b ∈ f.eigenspace t := by
    simpa using Submodule.sub_mem _ hx ha'
  have hd := Module.End.eigenspaces_iSupIndep f t
  have : b = 0 := (Submodule.disjoint_def.1 hd) b hb' hb
  simpa [this] using ha

lemma eig_mem (f : Module.End ℂ V) (c : ℂ) (N : ℕ → Submodule ℂ V) (hN : (⨆ m, N m) = ⊤)
    (h : ∀ m : ℕ, N m ≤ f.eigenspace (c + m)) (t : ℂ) {x : V} (hx : x ∈ f.eigenspace t) (h0 : x ≠ 0) :
    ∃ m : ℕ, t = c + m ∧ x ∈ N m := by
  have h1 := eig_le f c N hN h t hx
  by_cases hm : ∃ m : ℕ, c + m = t
  · obtain ⟨m, rfl⟩ := hm
    refine ⟨m, rfl, (iSup₂_le fun k hk => ?_ : (⨆ k : ℕ, ⨆ _ : c + k = c + m, N k) ≤ N m) h1⟩
    have : k = m := by exact_mod_cast add_left_cancel hk
    rw [this]
  · refine absurd ?_ h0
    exact (iSup₂_le fun k hk => absurd ⟨k, hk⟩ hm : (⨆ k : ℕ, ⨆ _ : c + k = t, N k) ≤ ⊥) h1

lemma eig_unique {f : Module.End ℂ V} {s t : ℂ} {x : V} (hs : x ∈ f.eigenspace s)
    (ht : x ∈ f.eigenspace t) (h0 : x ≠ 0) : s = t := by
  rw [Module.End.mem_eigenspace_iff] at hs ht
  exact smul_left_injective ℂ h0 (hs.symm.trans ht)

def rk : Ix p q → ℕ := Sum.elim (fun i => i.1) (fun j => p + j.1)

lemma rk_inj : Function.Injective (rk : Ix p q → ℕ) := by
  rintro (a | a) (b | b) h <;> simp only [rk, Sum.elim_inl, Sum.elim_inr] at h
  · rw [Fin.ext h]
  · have := a.2; omega
  · have := b.2; omega
  · rw [Fin.ext (add_left_cancel h)]

lemma same_equiv : Equivalence (sameBlock : Ix p q → Ix p q → Prop) := by
  refine ⟨same_refl, ?_, ?_⟩
  · rintro (a | a) (b | b) h <;> simp_all [sameBlock]
  · rintro (a | a) (b | b) (c | c) h h' <;> simp_all [sameBlock]

lemma pos_of_rk {a b : Ix p q} (h : sameBlock a b) (hr : rk a < rk b) : posC a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, rk, posC]

lemma hw_irr {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) {W : Submodule ℂ V}
    (hW : KStable act W) (hirr : ∀ N : Submodule ℂ V, N ≤ W → KStable act N → N = ⊥ ∨ N = W)
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ W) (hh : IsHW act μ v) :
    (∀ x ∈ W, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧
    ∀ (ν : Ix p q → ℚ), ∀ x ∈ W, x ≠ 0 → x ∈ wtSub act ν →
      ν = μ ∨ ∑ a, (rk a : ℚ) * μ a < ∑ a, (rk a : ℚ) * ν a := by
  obtain ⟨U, hvU, hS, hmin, h1, h2⟩ := GlobalTheory.ExtremalGen.exists_generated p q V act hL sameBlock same_equiv rk rk_inj μ v hh.2.1
    (fun a b hab hr => by
      have := hh.2.2
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, SetLike.mem_coe] at this
      exact this a b (pos_of_rk hab hr))
  have hUW : U ≤ W := hmin W hv fun a b hab _ x hx => hW _ (isKC_Eab (same_equiv.symm hab)) x hx
  have hU : U = W := by
    refine (hirr U hUW fun X hX w hw => kc_ind act U w (fun a b hab => hS a b hab w hw) hX).resolve_left ?_
    rintro rfl
    exact hh.1 (by simpa using hvU)
  subst hU
  exact ⟨h1, h2⟩

theorem lowest : ∀ (p q : ℕ) (M : GKMod p q) (Λ : Ix p q → ℚ) (W : Submodule ℂ M.V), IrrGK M → FiniteDimensional ℂ W → KStable M.act W → (∀ N : Submodule ℂ M.V, N ≤ W → KStable M.act N → N = ⊥ ∨ N = W) → (∃ e ∈ W, IsHW M.act Λ e) → (∀ e ∈ W, KilledByLower M.act e) → genSub M.act (W : Set M.V) = ⊤ → IsLowestType M Λ W ∧ Module.finrank ℂ ↥(hwSub M.act Λ) = 1 ∧ ∃ N : ℕ → Submodule ℂ M.V, (∀ m, FiniteDimensional ℂ (N m)) ∧ (⨆ m, N m) = ⊤ ∧ ∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = (((∑ i : Fin p, Λ (Sum.inl i) : ℚ) : ℂ) + m) • x := by
  intro p q M Λ W hM hfd hW hirr hex hlow hgen
  obtain ⟨e, heW, he⟩ := hex
  set c : ℂ := ((∑ i : Fin p, Λ (Sum.inl i) : ℚ) : ℂ) with hc
  have hWc : W ≤ Module.End.eigenspace (M.act (zc p q)) c := by
    rcases hirr _ inf_le_left (kstable_inf hW (kstable_eig M.lie c)) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h e ⟨heW, wt_eig he.2.1⟩) he.1
    · exact h.ge.trans inf_le_right
  obtain ⟨N, hN0, hNfd, hNtop, hN⟩ := GlobalTheory.FockGrade.exists_grading p q M.V M.act M.lie W c hfd hW hlow
    (fun x hx => by rw [← act_zc]; exact Module.End.mem_eigenspace_iff.1 (hWc hx))
  rw [hgen] at hNtop
  have hNe : ∀ m : ℕ, N m ≤ Module.End.eigenspace (M.act (zc p q)) (c + m) := fun m x hx => by
    rw [Module.End.mem_eigenspace_iff, act_zc]; exact hN m x hx
  have hcW : Module.End.eigenspace (M.act (zc p q)) c ≤ W := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0]; exact W.zero_mem
    obtain ⟨m, hm, hxm⟩ := eig_mem _ c N hNtop hNe c hx h0
    have : m = 0 := by exact_mod_cast left_eq_add.1 hm
    rwa [this, hN0] at hxm
  have hline := hw_irr M.lie hW hirr heW he
  refine ⟨⟨hM, hfd, hW, hirr, ⟨e, heW, he⟩, fun x => ⟨fun hx => ⟨W, hfd, hx, hW, ?_⟩, ?_⟩, hlow, hgen, ?_⟩, ?_,
    N, hNfd, hNtop, hN⟩
  · intro ν w hw hh
    rcases hline.2 ν w hw hh.1 hh.2.1 with h | h
    · exact h
    rcases (hw_irr M.lie hW hirr hw hh).2 Λ e heW he.1 he.2.1 with h' | h'
    · exact h'.symm
    · exact absurd h (not_lt.2 h'.le)
  · rintro ⟨W', hfd', hx, hW', hall⟩
    have h1 := GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub p q M.V M.act W' (fun a y hy => hW' _ (isKC_Eab (same_refl a)) y hy) x hx (M.wts x)
    refine (iSup_le fun μ y hy => ?_ : (⨆ μ : Ix p q → ℚ, W' ⊓ wtSub M.act μ) ≤ W) h1
    by_cases h0 : y = 0
    · rw [h0]; exact W.zero_mem
    have hy2 := wt_eig hy.2
    have := hfd'
    obtain ⟨ν, v, hv, hh⟩ := GlobalTheory.ExistsHW.exists_highestWeight p q M _
      (Submodule.finiteDimensional_of_le inf_le_left) (kstable_inf hW' (kstable_eig M.lie
        ((∑ i : Fin p, μ (Sum.inl i) : ℚ) : ℂ)))
      (fun h => h0 ((Submodule.eq_bot_iff _).1 h y ⟨hy.1, hy2⟩))
    obtain rfl := hall ν v hv.1 hh
    have := eig_unique hv.2 (wt_eig hh.2.1) hh.1
    rw [this] at hy2
    exact hcW hy2
  · intro μ x h0 hx
    obtain ⟨m, hm, hxm⟩ := eig_mem _ c N hNtop hNe _ (wt_eig hx) h0
    refine ⟨m, by rw [hc] at hm; exact_mod_cast hm, ?_, fun hxW => ?_⟩
    · rintro rfl
      rwa [hN0] at hxm
    · have := eig_unique (hWc hxW) (hNe m hxm) h0
      exact_mod_cast left_eq_add.1 this
  · have : hwSub M.act Λ = Submodule.span ℂ {e} := by
      refine le_antisymm (fun x hx => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 he.2)
      obtain ⟨a, rfl⟩ := hline.1 x (hcW (wt_eig hx.1)) hx.1
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
    rw [this]
    exact finrank_span_singleton he.1

end GlobalTheory.LowestType
