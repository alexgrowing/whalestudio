import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

noncomputable section

namespace GlobalTheory.SteepMult.Filt

variable {R S : ℕ}

lemma sameBlock_symm {a b : Ix R S} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

lemma sameBlock_trans {a b c : Ix R S} (h₁ : sameBlock a b) (h₂ : sameBlock b c) : sameBlock a c := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp_all [sameBlock]

lemma comm_single_apply (Z : Mat R S) (a b c d : Ix R S) :
    ((Z * Matrix.single a b (1 : ℂ) - Matrix.single a b 1 * Z : Mat R S)) c d =
      Z c a * (if d = b then 1 else 0) - (if c = a then 1 else 0) * Z b d := by
  by_cases hd : d = b <;> by_cases hc : c = a
  all_goals (try subst hd); (try subst hc); simp [Matrix.sub_apply, *]

lemma bracket_eNC {Z : Mat R S} (hZ : IsKC Z) (x : NC R S) :
    Z * eNC x - eNC x * Z = ∑ y, adP Z y x • eNC y := by
  ext c d
  rw [Matrix.sum_apply]
  simp only [eNC, Eab, Matrix.smul_apply, smul_eq_mul]
  rw [comm_single_apply]
  obtain ⟨⟨a, b⟩, hab⟩ := x
  by_cases h : sameBlock c d
  · rw [Finset.sum_eq_zero]
    · simp only
      by_cases hd : d = b
      · subst hd
        have hca : ¬ sameBlock c a := fun h' => hab (sameBlock_trans (sameBlock_symm h') h)
        by_cases hc : c = a
        · subst hc; exact absurd h hab
        · simp [hZ _ _ hca, hc]
      · by_cases hc : c = a
        · subst hc
          have hbd : ¬ sameBlock b d := fun h' => hab (sameBlock_trans h (sameBlock_symm h'))
          simp [hZ _ _ hbd, hd]
        · simp [hd, hc]
    · intro y _
      have : ¬ (y.1.1 = c ∧ y.1.2 = d) := fun ⟨h1, h2⟩ => y.2 (h1 ▸ h2 ▸ h)
      simp [Matrix.single_apply, this]
  · rw [Finset.sum_eq_single ⟨(c, d), h⟩]
    · simp [adP]
    · intro y _ hy
      have : ¬ (y.1.1 = c ∧ y.1.2 = d) := fun ⟨h1, h2⟩ => hy (Subtype.ext (Prod.ext h1 h2))
      simp [Matrix.single_apply, this]
    · simp

variable {V : Type} [AddCommGroup V] [Module ℂ V]

lemma act_comm_eNC {act : Mat R S →ₗ[ℂ] Module.End ℂ V} (hlie : IsLieAct act) {Z : Mat R S} (hZ : IsKC Z)
    (x : NC R S) (w : V) :
    act Z (act (eNC x) w) = act (eNC x) (act Z w) + ∑ y, adP Z y x • act (eNC y) w := by
  have h := hlie Z (eNC x)
  rw [bracket_eNC hZ x] at h
  have h2 := congrArg (fun T : Module.End ℂ V => T w) h
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.mul_apply] at h2
  rw [h2]; abel

lemma word_zero (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (g : Fin 0 → NC R S) : word act g = 1 := by
  simp [word]

lemma word_cons (act : Mat R S →ₗ[ℂ] Module.End ℂ V) {k : ℕ} (x : NC R S) (g : Fin k → NC R S) :
    word act (Fin.cons x g : Fin (k + 1) → NC R S) = act (eNC x) * word act g := by
  simp [word, List.ofFn_succ]

lemma word_mem_range (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k : ℕ} (g : Fin k → NC R S)
    {n : V} (hn : n ∈ N) : word act g n ∈ LinearMap.range (phiN act N k) := by
  classical
  refine ⟨Pi.single g ⟨n, hn⟩, ?_⟩
  rw [phiN_apply, Finset.sum_eq_single g]
  · simp
  · intro h _ hh; simp [Pi.single_apply, hh]
  · simp

lemma act_eNC_mem_range (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k : ℕ} (x : NC R S) {w : V}
    (hw : w ∈ LinearMap.range (phiN act N k)) : act (eNC x) w ∈ LinearMap.range (phiN act N (k + 1)) := by
  obtain ⟨Ψ, rfl⟩ := hw
  rw [phiN_apply, map_sum]
  refine Submodule.sum_mem _ fun g _ => ?_
  have := word_mem_range act N (Fin.cons x g : Fin (k + 1) → NC R S) (Ψ g).2
  rwa [word_cons, Module.End.mul_apply] at this

lemma kstable_range {act : Mat R S →ₗ[ℂ] Module.End ℂ V} (hlie : IsLieAct act) (N : Submodule ℂ V)
    (hN : KStable act N) (k : ℕ) : KStable act (LinearMap.range (phiN act N k)) := by
  induction k with
  | zero =>
    intro Z hZ w hw
    obtain ⟨Ψ, rfl⟩ := hw
    rw [phiN_apply, map_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    have := word_mem_range act N g (hN Z hZ _ (Ψ g).2)
    simpa [word_zero] using this
  | succ k ih =>
    intro Z hZ w hw
    obtain ⟨Ψ, rfl⟩ := hw
    rw [phiN_apply, map_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    rw [← Fin.cons_self_tail g, word_cons, Module.End.mul_apply, act_comm_eNC hlie hZ]
    have hw' := word_mem_range act N (Fin.tail g) (Ψ (Fin.cons (g 0) (Fin.tail g))).2
    refine add_mem (act_eNC_mem_range act N _ (ih Z hZ _ hw')) (Submodule.sum_mem _ fun y _ => ?_)
    exact Submodule.smul_mem _ _ (act_eNC_mem_range act N _ hw')

theorem filt_basic : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N → ∀ k : ℕ,
    KStable M.act (filt M.act N k) ∧
    filt M.act N (k + 1) = filt M.act N k ⊔ LinearMap.range (phiN M.act N (k + 1)) ∧ filt M.act N 0 ≤ N := by
  intro R S M N hN k
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ w hw
    refine Submodule.iSup_induction (fun j : Fin (k + 1) => LinearMap.range (phiN M.act N j))
      (motive := fun w => M.act Z w ∈ filt M.act N k) hw ?_ ?_ ?_
    · intro j w hw
      exact (le_iSup (fun j : Fin (k + 1) => LinearMap.range (phiN M.act N j)) j)
        (kstable_range M.lie N hN j Z hZ w hw)
    · simp
    · intro a b ha hb; rw [map_add]; exact add_mem ha hb
  · apply le_antisymm
    · refine iSup_le fun j => ?_
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact le_sup_right
      · exact le_sup_of_le_left (le_iSup (fun j : Fin (k + 1) => LinearMap.range (phiN M.act N j)) i)
    · refine sup_le (iSup_le fun i => ?_) ?_
      · exact le_iSup (fun j : Fin (k + 2) => LinearMap.range (phiN M.act N j)) i.castSucc
      · exact le_iSup (fun j : Fin (k + 2) => LinearMap.range (phiN M.act N j)) (Fin.last (k + 1))
  · refine iSup_le fun j => ?_
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    rintro _ ⟨Ψ, rfl⟩
    rw [phiN_apply]
    refine Submodule.sum_mem _ fun g _ => ?_
    have : word M.act g = 1 := by simp [word]
    rw [this]; exact (Ψ g).2

end GlobalTheory.SteepMult.Filt

end
