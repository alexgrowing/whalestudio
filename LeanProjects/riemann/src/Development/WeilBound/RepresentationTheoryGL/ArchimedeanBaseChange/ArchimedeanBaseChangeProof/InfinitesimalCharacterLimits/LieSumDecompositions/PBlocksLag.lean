import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapE

noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockLagrange

section Abs

variable {M ι Λ : Type} [AddCommGroup M] [Module ℂ M] [DecidableEq ι]

theorem list_prod_apply (l : List (Module.End ℂ M)) (k : Module.End ℂ M → ℂ) (φ : M) (h : ∀ f ∈ l, f φ = k f • φ) :
    l.prod φ = (l.map k).prod • φ := by
  induction l with
  | nil => simp
  | cons f l ih =>
    rw [List.prod_cons, Module.End.mul_apply, ih (fun g hg => h g (List.mem_cons_of_mem _ hg)), map_smul,
      h f List.mem_cons_self, smul_smul, List.map_cons, List.prod_cons, mul_comm]

theorem list_prod_smul (l : List (Module.End ℂ M)) (φ : M) (h : ∀ f ∈ l, ∃ c : ℂ, f φ = c • φ) :
    ∃ c : ℂ, l.prod φ = c • φ := by
  induction l with
  | nil => exact ⟨1, by simp⟩
  | cons f l ih =>
    obtain ⟨c, hc⟩ := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    obtain ⟨d, hd⟩ := h f List.mem_cons_self
    exact ⟨c * d, by rw [List.prod_cons, Module.End.mul_apply, hc, map_smul, hd, smul_smul]⟩

variable (A : Λ → Module.End ℂ M) (χ : ι → Λ → ℂ) (lam : ι → ι → Λ)

def fac (i j : ι) : Module.End ℂ M := (χ i (lam i j) - χ j (lam i j))⁻¹ • (A (lam i j) - χ j (lam i j) • 1)

def proj (SS : Finset ι) (i : ι) : Module.End ℂ M := (((SS.erase i).toList).map (fac A χ lam i)).prod

variable {A χ lam}

omit [DecidableEq ι] in
theorem fac_apply {P : ι → Submodule ℂ M} (hP : ∀ k, ∀ φ ∈ P k, ∀ l, A l φ = χ k l • φ) (i j k : ι) {φ : M}
    (hφ : φ ∈ P k) :
    fac A χ lam i j φ = ((χ i (lam i j) - χ j (lam i j))⁻¹ * (χ k (lam i j) - χ j (lam i j))) • φ := by
  simp only [fac, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hP k φ hφ]
  rw [smul_sub, smul_smul, smul_smul, mul_sub, sub_smul]

theorem proj_self {P : ι → Submodule ℂ M} (hP : ∀ k, ∀ φ ∈ P k, ∀ l, A l φ = χ k l • φ)
    (hlam : ∀ i j, i ≠ j → χ i (lam i j) ≠ χ j (lam i j)) (SS : Finset ι) (i : ι) {φ : M} (hφ : φ ∈ P i) :
    proj A χ lam SS i φ = φ := by
  unfold proj
  rw [list_prod_apply _ (fun _ => 1) φ]
  · simp
  · intro f hf
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf
    rw [one_smul, fac_apply hP i j i hφ]
    have hij : i ≠ j := fun h => by subst h; exact Finset.notMem_erase i SS (Finset.mem_toList.1 hj)
    rw [inv_mul_cancel₀ (sub_ne_zero.2 (hlam i j hij)), one_smul]

theorem proj_other {P : ι → Submodule ℂ M} (hP : ∀ k, ∀ φ ∈ P k, ∀ l, A l φ = χ k l • φ)
    (SS : Finset ι) (i k : ι) (hk : k ∈ SS) (hki : k ≠ i) {φ : M} (hφ : φ ∈ P k) :
    proj A χ lam SS i φ = 0 := by
  unfold proj
  have hmem : fac A χ lam i k ∈ ((SS.erase i).toList).map (fac A χ lam i) :=
    List.mem_map.2 ⟨k, Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hki, hk⟩), rfl⟩
  obtain ⟨l₁, l₂, he⟩ := List.append_of_mem hmem
  have hl₂ : ∀ f ∈ l₂, ∃ c : ℂ, f φ = c • φ := by
    intro f hf
    have hf' : f ∈ ((SS.erase i).toList).map (fac A χ lam i) := by
      rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hf)
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hf'
    exact ⟨_, fac_apply hP i j k hφ⟩
  obtain ⟨c, hc⟩ := list_prod_smul l₂ φ hl₂
  rw [he, List.prod_append, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply, hc, map_smul,
    fac_apply hP i k k hφ, sub_self, mul_zero, zero_smul, smul_zero, map_zero]

theorem proj_decomp {P : ι → Submodule ℂ M} (hP : ∀ k, ∀ φ ∈ P k, ∀ l, A l φ = χ k l • φ)
    (hlam : ∀ i j, i ≠ j → χ i (lam i j) ≠ χ j (lam i j)) (SS : Finset ι) {φ : M} (hφ : φ ∈ ⨆ i ∈ SS, P i) :
    (∀ i, proj A χ lam SS i φ ∈ P i) ∧ ∑ i ∈ SS, proj A χ lam SS i φ = φ := by
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum P φ).1 hφ
  have key : ∀ i, proj A χ lam SS i φ = if i ∈ SS then (μ i : M) else 0 := by
    intro i
    rw [← hμ, map_sum]
    rw [Finset.sum_congr rfl (g := fun k => if k = i then (μ k : M) else 0) (fun k hk => by
      by_cases h : k = i
      · subst h; rw [if_pos rfl, proj_self hP hlam SS k (μ k).2]
      · rw [if_neg h, proj_other hP SS i k hk h (μ k).2])]
    rw [Finset.sum_ite_eq']
  refine ⟨fun i => ?_, ?_⟩
  · rw [key]
    split_ifs
    · exact (μ i).2
    · exact (P i).zero_mem
  · rw [Finset.sum_congr rfl (fun i hi => by rw [key, if_pos hi]), hμ]

theorem proj_commute (SS : Finset ι) (i : ι) (B : Module.End ℂ M) (hB : ∀ l, Commute (A l) B) :
    Commute (proj A χ lam SS i) B := by
  unfold proj
  refine Commute.list_prod_left _ _ fun f hf => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hf
  exact ((hB _).sub_left ((Commute.one_left B).smul_left _)).smul_left _

end Abs

section Sep

theorem exists_ne_prod {m m' : Multiset ℂ} (sh : ℂ) (h : m ≠ m') :
    ∃ w : ℂ, (m.map fun z => w + sh + z).prod ≠ (m'.map fun z => w + sh + z).prod := by
  by_contra hc
  push Not at hc
  have ev : ∀ (n : Multiset ℂ) (w : ℂ), (n.map fun z => w + sh + z).prod =
      ((n.map fun z => -(sh + z)).map fun a => X - C a).prod.eval w := by
    intro n w
    rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun z _ => ?_
    simp
    ring
  have hp : ((m.map fun z => -(sh + z)).map fun a => X - C a).prod =
      ((m'.map fun z => -(sh + z)).map fun a => X - C a).prod :=
    Polynomial.funext fun w => by rw [← ev, ← ev, hc w]
  have hr := congrArg Polynomial.roots hp
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  exact h (Multiset.map_injective (fun x y hxy => by simpa using hxy) hr)

end Sep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem proj_exists {a : ℕ} (L : Submodule ℂ (Sm E a)) (SS : Finset ((E →+* ℂ) → Multiset ℂ)) (sh : ℂ)
    (hL : L ≤ ⨆ σ ∈ SS, BlockCapelli.Eig L σ sh) :
    ∃ z : ((E →+* ℂ) → Multiset ℂ) → Module.End ℂ (Sm E a), (∀ σ (o : Op E a), Commute (z σ) (act o)) ∧
      (∀ σ, ∀ φ ∈ L, z σ φ ∈ BlockCapelli.Eig L σ sh) ∧ ∀ φ ∈ L, ∑ σ ∈ SS, z σ φ = φ := by
  classical
  let A : (E →+* ℂ) × ℂ → Module.End ℂ (Sm E a) := fun l => cap l.1 l.2
  let χ : ((E →+* ℂ) → Multiset ℂ) → (E →+* ℂ) × ℂ → ℂ := fun σ l => ((σ l.1).map fun z => l.2 + sh + z).prod
  have hsep : ∀ σ σ' : (E →+* ℂ) → Multiset ℂ, σ ≠ σ' → ∃ l, χ σ l ≠ χ σ' l := by
    intro σ σ' h
    obtain ⟨τ, hτ⟩ := Function.ne_iff.1 h
    obtain ⟨w, hw⟩ := exists_ne_prod sh hτ
    exact ⟨(τ, w), hw⟩
  let lam : ((E →+* ℂ) → Multiset ℂ) → ((E →+* ℂ) → Multiset ℂ) → (E →+* ℂ) × ℂ := fun σ σ' =>
    if h : σ ≠ σ' then Classical.choose (hsep σ σ' h) else (Classical.arbitrary _, 0)
  have hlam : ∀ σ σ', σ ≠ σ' → χ σ (lam σ σ') ≠ χ σ' (lam σ σ') := by
    intro σ σ' h
    simp only [lam, dif_pos h]
    exact Classical.choose_spec (hsep σ σ' h)
  have hP : ∀ k, ∀ φ ∈ BlockCapelli.Eig L k sh, ∀ l, A l φ = χ k l • φ := fun k φ hφ l => hφ.2 l.1 l.2
  refine ⟨proj A χ lam SS, fun σ o => proj_commute SS σ _ fun l => GlobalTheory.SpehInfChar.cap_commute_act l.1 l.2 o,
    fun σ φ hφ => (proj_decomp hP hlam SS (hL hφ)).1 σ, fun φ hφ => (proj_decomp hP hlam SS (hL hφ)).2⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockLagrange

end
