import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseSat

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.PseBub

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse PositivityTheory.Rg.BcB.N3.PseSat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem comp_injective {n : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {π : Representation ℂ (GL (Fin n) k) V} {ρ : Representation ℂ (GL (Fin n) k) W}
    {τ : Representation ℂ (GL (Fin n) k) U} (hi : π.IsIrreducible) (hsph : IsSpherical π)
    (f : π.IntertwiningMap ρ) (hf : Function.Injective f) (T : ρ.IntertwiningMap τ) (hT : KInj k T) :
    Function.Injective (T.comp f) := by
  classical
  set g := T.comp f with hg
  have hg' : ∀ v, g v = T (f v) := fun v => Representation.IntertwiningMap.comp_apply _ _ _ T f v
  rcases hi.eq_bot_or_eq_top (Representation.IntertwiningMap.ker _ _ g) with h | h
  · intro x y hxy
    have hx : x - y ∈ Representation.IntertwiningMap.ker _ _ g := by
      rw [Representation.IntertwiningMap.mem_ker, map_sub, hxy, sub_self]
    rw [h] at hx
    have hx' : x - y ∈ (⊥ : Submodule ℂ V) := hx
    exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hx')
  · exfalso
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsph
    have hfv : f v ∈ fixed ρ (KO k (Fin n)) := by
      intro h'
      have := hv h'
      rw [← Representation.IntertwiningMap.isIntertwining, this]
      simp
    have hker : v ∈ Representation.IntertwiningMap.ker _ _ g := by
      rw [h]
      exact (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ V))
    rw [Representation.IntertwiningMap.mem_ker, hg'] at hker
    have := hT (f v) hfv hker
    exact hv0 (hf (by rw [this, map_zero]))

def wt {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := ∑ i : Fin n, (i : ℕ) * (σ i : ℕ)

theorem wt_le {n : ℕ} (σ : Equiv.Perm (Fin n)) : wt σ ≤ n * (n * n) := by
  unfold wt
  calc ∑ i : Fin n, (i : ℕ) * (σ i : ℕ) ≤ ∑ _i : Fin n, n * n :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul i.2.le (σ i).2.le
    _ = n * (n * n) := by simp

theorem wt_swap {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : (j : ℕ) = i + 1) (hd : σ j < σ i) :
    wt σ < wt (σ * Equiv.swap i j) := by
  classical
  have hne : i ≠ j := by
    intro h
    subst h
    omega
  unfold wt
  have key : ∀ τ : Equiv.Perm (Fin n), ∑ k : Fin n, (k : ℕ) * (τ k : ℕ) =
      (i : ℕ) * (τ i : ℕ) + ((j : ℕ) * (τ j : ℕ) +
        ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * (τ k : ℕ)) := by
    intro τ
    rw [Finset.add_sum_erase (Finset.univ.erase i) (fun k : Fin n => (k : ℕ) * (τ k : ℕ))
      (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩)]
    rw [Finset.add_sum_erase Finset.univ (fun k : Fin n => (k : ℕ) * (τ k : ℕ)) (Finset.mem_univ i)]
  rw [key σ, key (σ * Equiv.swap i j)]
  have hrest : ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * ((σ * Equiv.swap i j) k : ℕ) =
      ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * (σ k : ℕ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj := Finset.ne_of_mem_erase hk
    have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hrest, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hd' : (σ j : ℕ) < σ i := hd
  rw [hij]
  nlinarith

theorem exists_descent {n : ℕ} (σ : Equiv.Perm (Fin n)) (h1 : σ ≠ 1) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ σ j < σ i := by
  by_contra hne
  push_neg at hne
  apply h1
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    have hs : StrictMono (σ : Fin (m + 1) → Fin (m + 1)) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      have hle := hne i.castSucc i.succ (by simp)
      exact lt_of_le_of_ne hle (fun h => (Fin.castSucc_lt_succ (i := i)).ne (σ.injective h))
    ext x
    have hx := congrFun hs.eq_id x
    simp [hx]

theorem bubble : Bubble k := by
  intro hSL hG2 n ξ hξ σ₀ V _ _ π hi hsph hf₀
  have key : ∀ m : ℕ, ∀ σ : Equiv.Perm (Fin n), n * (n * n) - wt σ = m →
      (∃ f : π.IntertwiningMap (iP (ξ ∘ ⇑σ)), Function.Injective ⇑f) →
        ∃ f : π.IntertwiningMap (iP ξ), Function.Injective ⇑f := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro σ hm hσ
      by_cases h1 : σ = 1
      · subst h1
        exact hσ
      · obtain ⟨i, j, hij, hd⟩ := exists_descent σ h1
        obtain ⟨f, hf⟩ := hσ
        have hle : ‖(((ξ ∘ ⇑σ) i : ℂˣ) : ℂ)‖ ≤ ‖(((ξ ∘ ⇑σ) j : ℂˣ) : ℂ)‖ := hξ _ _ hd.le
        obtain ⟨T0, hT0⟩ := hG2 _ _ hle
        obtain ⟨T, hT⟩ := hSL n (ξ ∘ ⇑σ) i j hij ⟨T0, hT0⟩
        have hinj := comp_injective hi hsph f hf T hT
        have hw := wt_swap σ i j hij hd
        have hwle := wt_le (σ * Equiv.swap i j)
        have hlt : n * (n * n) - wt (σ * Equiv.swap i j) < m := by
          generalize n * (n * n) = N at *
          omega
        exact ih _ hlt (σ * Equiv.swap i j) rfl ⟨T.comp f, hinj⟩
  exact key _ σ₀ rfl hf₀

end PositivityTheory.Rg.BcB.N3.PseBub
