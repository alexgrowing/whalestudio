import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeightStatement

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc.HighestVec

theorem weight_rowW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type, rowDeg]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [rowW]
  · intro b _ hb
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [rowW, Ne.symm hb]
  · simp

def height (N : ℕ) (μ : Fin N → ℕ) : ℕ := ∑ a : Fin N, (N - a.val) * μ a

theorem height_add (N : ℕ) (μ ν : Fin N → ℕ) : height N (μ + ν) = height N μ + height N ν := by
  simp [height, mul_add, Finset.sum_add_distrib]

theorem height_single (N : ℕ) (a : Fin N) : height N (Pi.single a 1) = N - a.val := by
  simp [height, Pi.single_apply]

theorem height_lt_swap (N : ℕ) (μ : Fin N → ℕ) (a b : Fin N) (hab : a < b) (hμ : μ a < μ b) :
    height N μ < height N (μ ∘ Equiv.swap a b) := by
  classical
  unfold height
  have hne : a ≠ b := hab.ne
  rw [← Finset.sum_add_sum_compl {a, b}, ← Finset.sum_add_sum_compl {a, b}
    (fun c => (N - c.val) * (μ ∘ Equiv.swap a b) c)]
  have hrest : ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - c.val) * (μ ∘ Equiv.swap a b) c =
      ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - c.val) * μ c := by
    refine Finset.sum_congr rfl fun c hc => ?_
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    simp [Equiv.swap_apply_of_ne_of_ne hc.1 hc.2]
  rw [hrest, Finset.sum_pair hne, Finset.sum_pair hne]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  apply Nat.add_lt_add_right
  have hlt : N - b.val < N - a.val := by have := b.isLt; have : a.val < b.val := hab; omega
  generalize N - b.val = q at *
  generalize N - a.val = p at *
  nlinarith

theorem isWeightedHomogeneous_rename_rows {k : Type} [Field k] {N : ℕ} (σ : Equiv.Perm (Fin N))
    {v : MvPolynomial (Fin N × Fin N) k} {μ : Fin N → ℕ}
    (hv : IsWeightedHomogeneous (rowW N N) v μ) :
    IsWeightedHomogeneous (rowW N N) (rename (fun x : Fin N × Fin N => (σ x.1, x.2)) v) (μ ∘ σ.symm) := by
  classical
  have hinj : Function.Injective (fun x : Fin N × Fin N => (σ x.1, x.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (σ.injective h.1) h.2
  intro d hd
  have hmem : d ∈ (rename (fun x : Fin N × Fin N => (σ x.1, x.2)) v).support := mem_support_iff.mpr hd
  rw [support_rename_of_injective hinj, Finset.mem_image] at hmem
  obtain ⟨u, hu, rfl⟩ := hmem
  have hw := hv (mem_support_iff.mp hu)
  funext a
  rw [weight_rowW_apply, Function.comp_apply, ← hw, weight_rowW_apply]
  unfold rowDeg
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show ((a, s) : Fin N × Fin N) = (fun x : Fin N × Fin N => (σ x.1, x.2)) (σ.symm a, s) by simp]
  exact Finsupp.mapDomain_apply hinj u _

end GlobalTheory.Alc.HighestVec

open GlobalTheory.Alc.HighestVec in

theorem GlobalTheory.Alc.exists_dominant_highest_vector_of_lt : ∀ (k : Type) [Field k] (N : ℕ)
    (M M' : Submodule k (MvPolynomial (Fin N × Fin N) k)), Good M → Good M' → M < M' →
    (∃ c : ℕ, ∀ f ∈ M', ∀ m ∈ f.support, ∑ a, rowDeg m a ≤ c) →
    ∃ (μ : Fin N → ℕ) (v : MvPolynomial (Fin N × Fin N) k), Antitone μ ∧ v ∈ M' ∧ v ∉ M ∧
      IsWeightedHomogeneous (rowW N N) v μ ∧ ∀ a b, a < b → rowE k N N a b v ∈ M := by
  intro k _ N M M' hM hM' hlt hc
  obtain ⟨c, hc⟩ := hc
  classical
  let S : Set ℕ := {h | ∃ (μ : Fin N → ℕ) (v : MvPolynomial (Fin N × Fin N) k), v ∈ M' ∧ v ∉ M ∧
    IsWeightedHomogeneous (rowW N N) v μ ∧ height N μ = h}
  have hne : S.Nonempty := by
    obtain ⟨f, hfM', hfM⟩ := SetLike.exists_of_lt hlt
    by_contra hcon
    apply hfM
    rw [← sum_weightedHomogeneousComponent (rowW N N) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    refine Submodule.sum_mem _ fun μ _ => ?_
    by_contra hμ
    exact hcon ⟨_, μ, _, hM'.2.1 μ f hfM', hμ,
      weightedHomogeneousComponent_isWeightedHomogeneous μ f, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨N * c, ?_⟩
    rintro h ⟨μ, v, hv', hvM, hvh, rfl⟩
    have hv0 : v ≠ 0 := fun h0 => hvM (h0 ▸ M.zero_mem)
    obtain ⟨m, hm⟩ := ne_zero_iff.mp hv0
    have hw := hvh hm
    have hsum := hc v hv' m (mem_support_iff.mpr hm)
    have hμm : ∀ a, μ a = rowDeg m a := fun a => by rw [← hw, weight_rowW_apply]
    calc height N μ = ∑ a, (N - a.val) * μ a := rfl
      _ ≤ ∑ a, N * μ a := Finset.sum_le_sum fun a _ => Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = N * ∑ a, rowDeg m a := by rw [Finset.mul_sum]; simp only [hμm]
      _ ≤ N * c := Nat.mul_le_mul_left _ hsum
  obtain ⟨μ, v, hv', hvM, hvh, hH⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ (μ' : Fin N → ℕ) (v' : MvPolynomial (Fin N × Fin N) k), v' ∈ M' → v' ∉ M →
      IsWeightedHomogeneous (rowW N N) v' μ' → height N μ' ≤ height N μ := by
    intro μ' v' h1 h2 h3
    rw [hH]
    exact le_csSup hbdd ⟨μ', v', h1, h2, h3, rfl⟩
  refine ⟨μ, v, ?_, hv', hvM, hvh, ?_⟩
  · intro a b hab
    rcases hab.lt_or_eq with hab | rfl
    · by_contra hba
      push_neg at hba
      have h1 : rename (fun x : Fin N × Fin N => (Equiv.swap a b x.1, x.2)) v ∈ M' :=
        hM'.2.2 (Equiv.swap a b) v hv'
      have h2 : rename (fun x : Fin N × Fin N => (Equiv.swap a b x.1, x.2)) v ∉ M := by
        intro h
        apply hvM
        have h' := hM.2.2 (Equiv.swap a b) _ h
        rw [rename_rename] at h'
        have hid : ((fun x : Fin N × Fin N => (Equiv.swap a b x.1, x.2)) ∘
            fun x : Fin N × Fin N => (Equiv.swap a b x.1, x.2)) = id := by
          funext x; simp
        rwa [hid, rename_id_apply] at h'
      have h3 := isWeightedHomogeneous_rename_rows (Equiv.swap a b) hvh
      rw [Equiv.symm_swap] at h3
      have h4 := hmax _ _ h1 h2 h3
      have h5 := height_lt_swap N μ a b hab hba
      omega
    · exact le_rfl
  · intro a b hab
    by_contra hnot
    have hne : a ≠ b := hab.ne
    obtain ⟨_, hE⟩ := GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ v hvh
    obtain ⟨hz, hw⟩ := hE a b hne
    by_cases hb : μ b = 0
    · exact hnot (by rw [hz hb]; exact M.zero_mem)
    · let μ' : Fin N → ℕ := μ + Pi.single a 1 - Pi.single b 1
      have hμ' : μ' + Pi.single b 1 = μ + Pi.single a 1 := by
        funext c
        by_cases hca : c = a
        · subst hca; simp [μ', Pi.single_apply, hne]
        · by_cases hcb : c = b
          · subst hcb; simp [μ', Pi.single_apply, hca]; omega
          · simp [μ', Pi.single_apply, hca, hcb]
      have h3 := hw μ' hμ'
      have h1 : rowE k N N a b v ∈ M' := hM'.1 a b v hv'
      have hle := hmax μ' _ h1 hnot h3
      have hh := congrArg (height N) hμ'
      rw [height_add, height_add, height_single, height_single] at hh
      have : N - b.val < N - a.val := by
        have := b.isLt; have : a.val < b.val := hab; omega
      omega
