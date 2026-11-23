import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsJointIntEigenvectorOfStable
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEqMulProdMinors

noncomputable section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH

namespace GlobalTheory.JointHarm

section Blocks

variable {σ : Type} {p r : ℕ}

def BlockHW (z : Fin p × Fin r → σ) (α : ℕ → ℕ) (P : MvPolynomial σ ℂ) : Prop :=
  (∀ a b : Fin p, a < b → rowOp ℂ z a b P = 0) ∧ (∀ k l : Fin r, k < l → colOp ℂ z k l P = 0) ∧
    (∀ a : Fin p, rowOp ℂ z a a P = (α a : ℂ) • P) ∧ ∀ k : Fin r, colOp ℂ z k k P = (α k : ℂ) • P

def minorPoly (z : Fin p × Fin r → σ) (α : ℕ → ℕ) : MvPolynomial σ ℂ :=
  ∏ i : Fin (min p r), (Matrix.of fun a b : Fin (i.val + 1) =>
    (X (z (Fin.castLE (Nat.succ_le_of_lt (lt_of_lt_of_le i.isLt (min_le_left p r))) a,
      Fin.castLE (Nat.succ_le_of_lt (lt_of_lt_of_le i.isLt (min_le_right p r))) b)) :
        MvPolynomial σ ℂ)).det ^ (α i - α (i + 1))

end Blocks

def FnShape (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Prop :=
  ∃ α β γ δ : ℕ → ℕ, Antitone α ∧ Antitone β ∧ Antitone γ ∧ Antitone δ ∧
    (∀ i, min p r ≤ i → α i = 0) ∧ (∀ i, min p s ≤ i → β i = 0) ∧
    (∀ i, min q s ≤ i → γ i = 0) ∧ (∀ i, min q r ≤ i → δ i = 0) ∧
    (∀ i : Fin p, α i = 0 ∨ β i.rev = 0) ∧ (∀ i : Fin q, γ i = 0 ∨ δ i.rev = 0) ∧
    (∀ i : Fin r, α i = 0 ∨ δ i.rev = 0) ∧ (∀ i : Fin s, γ i = 0 ∨ β i.rev = 0) ∧
    (∀ i : Fin p, shiftNu (cPair r s) μ (.inl i) = (α i : ℚ) - β i.rev) ∧
    (∀ i : Fin q, shiftNu (cPair r s) μ (.inr i) = (γ i : ℚ) - δ i.rev) ∧
    (∀ i : Fin r, shiftNu (cPair p q) μ' (.inl i) = (α i : ℚ) - δ i.rev) ∧
    (∀ i : Fin s, shiftNu (cPair p q) μ' (.inr i) = (γ i : ℚ) - β i.rev)

private theorem sum_neg_index_smul_diag_apply_comm {V : Type*} [AddCommGroup V] [Module ℂ V] {k : ℕ}
    (e : Fin k → Fin k → Module.End ℂ V)
    (he : ∀ i j a b, e i j * e a b - e a b * e i j =
      (if j = a then e i b else 0) - (if b = i then e a j else 0))
    (i j : Fin k) (x : V) :
    (∑ a : Fin k, (-((a : ℕ) : ℂ)) • e a a) (e i j x) =
      e i j ((∑ a : Fin k, (-((a : ℕ) : ℂ)) • e a a) x) + (((j : ℕ) : ℂ) - ((i : ℕ) : ℂ)) • e i j x := by
  have h1 : ∀ a, e a a (e i j x) = e i j (e a a x) +
      ((if a = i then e i j x else 0) - (if j = a then e i j x else 0)) := by
    intro a
    have h := LinearMap.congr_fun (he a a i j) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [← sub_eq_iff_eq_add', h]
    by_cases ha : a = i <;> by_cases hb : j = a
    · subst ha; subst hb; simp
    · subst ha; simp [hb]
    · subst hb; simp [ha]
    · simp [ha, hb]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h1, smul_add,
    Finset.sum_add_distrib, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_smul, neg_smul, neg_smul]
  abel

private theorem sum_smul_apply_comm_of_commute {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]
    (T : Module.End ℂ V) (S : ι → Module.End ℂ V) (c : ι → ℂ) (h : ∀ b, Commute T (S b))
    (x : V) : (∑ b, c b • S b) (T x) = T ((∑ b, c b • S b) x) := by
  have hc : Commute T (∑ b, c b • S b) :=
    Commute.sum_right _ _ _ fun b _ => (h b).smul_right (c b)
  exact (LinearMap.congr_fun hc.eq x).symm

private theorem exists_common_eigenvector_of_commuting {V ι : Type*} [AddCommGroup V] [Module ℂ V] (T : ι → Module.End ℂ V)
    (hT : ∀ s t, Commute (T s) (T t)) (s : Finset ι) :
    ∀ U : Submodule ℂ V, FiniteDimensional ℂ U → U ≠ ⊥ → (∀ t, ∀ y ∈ U, T t y ∈ U) →
      ∃ v ∈ U, v ≠ 0 ∧ ∀ t ∈ s, ∃ c : ℂ, T t v = c • v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro U _ hU _
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    exact ⟨v, hv, hv0, by simp⟩
  | insert t s hts ih =>
    intro U hUf hU hTU
    have := hUf
    have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((T t).restrict (hTU t))
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Module.End.hasEigenvalue_iff.mp hc)
    have hu1 : T t (u : V) = c • (u : V) := by
      have h := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hu)
      simpa [LinearMap.restrict_apply] using h
    have hU'0 : U ⊓ Module.End.eigenspace (T t) c ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      refine ⟨u, Submodule.mem_inf.mpr ⟨u.2, Module.End.mem_eigenspace_iff.mpr hu1⟩, ?_⟩
      intro h
      exact hu0 (Subtype.ext h)
    have hU'f : FiniteDimensional ℂ (U ⊓ Module.End.eigenspace (T t) c : Submodule ℂ V) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have hTU' : ∀ r, ∀ y ∈ U ⊓ Module.End.eigenspace (T t) c,
        T r y ∈ U ⊓ Module.End.eigenspace (T t) c := by
      intro r y hy
      obtain ⟨hyU, hyE⟩ := Submodule.mem_inf.mp hy
      refine Submodule.mem_inf.mpr ⟨hTU r y hyU, ?_⟩
      rw [Module.End.mem_eigenspace_iff]
      have h1 : T t y = c • y := Module.End.mem_eigenspace_iff.mp hyE
      have h2 := LinearMap.congr_fun (hT t r).eq y
      simp only [Module.End.mul_apply] at h2
      rw [h2, h1, map_smul]
    obtain ⟨v, hv, hv0, hvs⟩ := ih _ hU'f hU'0 hTU'
    obtain ⟨hvU, hvE⟩ := Submodule.mem_inf.mp hv
    refine ⟨v, hvU, hv0, ?_⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact ⟨c, Module.End.mem_eigenspace_iff.mp hvE⟩
    · exact hvs r hr

private theorem int_lemma_4 {V : Type*} [AddCommGroup V] [Module ℂ V] (g : Module.End ℂ V)
    (hg : ⨆ n : ℤ, Module.End.eigenspace g (n : ℂ) = ⊤) {v : V} (hv : v ≠ 0) {c : ℂ}
    (hc : g v = c • v) : ∃ n : ℤ, c = n := by
  by_contra hne
  push Not at hne
  have hle : (⨆ n : ℤ, Module.End.eigenspace g (n : ℂ)) ≤
      ⨆ (μ : ℂ) (_ : μ ≠ c), Module.End.eigenspace g μ :=
    iSup_le fun n => le_iSup₂_of_le (n : ℂ) (fun h => hne n h.symm) le_rfl
  have hd := (Module.End.eigenspaces_iSupIndep g) c
  rw [hg, top_le_iff] at hle
  rw [hle, disjoint_top] at hd
  have hvm : v ∈ Module.End.eigenspace g c := Module.End.mem_eigenspace_iff.mpr hc
  rw [hd, Submodule.mem_bot] at hvm
  exact hv hvm

theorem exists_highest_pair {V : Type*} [AddCommGroup V] [Module ℂ V] {k l : ℕ}
    (e : Fin k → Fin k → Module.End ℂ V) (f : Fin l → Fin l → Module.End ℂ V)
    (he : ∀ i j a b, e i j * e a b - e a b * e i j =
      (if j = a then e i b else 0) - (if b = i then e a j else 0))
    (hf : ∀ i j a b, f i j * f a b - f a b * f i j =
      (if j = a then f i b else 0) - (if b = i then f a j else 0))
    (hef : ∀ i j a b, Commute (e i j) (f a b))
    (hde : ⨆ κ : Fin k → ℤ, (⨅ i, Module.End.eigenspace (e i i) (κ i : ℂ)) = ⊤)
    (hdf : ⨆ κ : Fin l → ℤ, (⨅ i, Module.End.eigenspace (f i i) (κ i : ℂ)) = ⊤)
    (W : Submodule ℂ V) [FiniteDimensional ℂ W] (hWe : ∀ i j, ∀ w ∈ W, e i j w ∈ W)
    (hWf : ∀ i j, ∀ w ∈ W, f i j w ∈ W) (hW0 : W ≠ ⊥) :
    ∃ v ∈ W, v ≠ 0 ∧ (∀ i j, i < j → e i j v = 0) ∧ (∀ i j, i < j → f i j v = 0) ∧
      ∃ (κ : Fin k → ℤ) (κ' : Fin l → ℤ), (∀ i, e i i v = (κ i : ℂ) • v) ∧
        ∀ i, f i i v = (κ' i : ℂ) • v := by
  classical
  have hHe : ∀ i j (x : V), (∑ a : Fin k, (-((a : ℕ) : ℂ)) • e a a +
      ∑ b : Fin l, (-((b : ℕ) : ℂ)) • f b b) (e i j x) =
      e i j ((∑ a : Fin k, (-((a : ℕ) : ℂ)) • e a a +
        ∑ b : Fin l, (-((b : ℕ) : ℂ)) • f b b) x) + (((j : ℕ) : ℂ) - ((i : ℕ) : ℂ)) • e i j x := by
    intro i j x
    rw [LinearMap.add_apply, LinearMap.add_apply, map_add, sum_neg_index_smul_diag_apply_comm e he,
      sum_smul_apply_comm_of_commute (e i j) (fun b => f b b) _ (fun b => hef i j b b)]
    abel
  have hHf : ∀ i j (x : V), (∑ a : Fin k, (-((a : ℕ) : ℂ)) • e a a +
      ∑ b : Fin l, (-((b : ℕ) : ℂ)) • f b b) (f i j x) =
      f i j ((∑ a : Fin k, (-((a : ℕ) : ℂ)) • e a a +
        ∑ b : Fin l, (-((b : ℕ) : ℂ)) • f b b) x) + (((j : ℕ) : ℂ) - ((i : ℕ) : ℂ)) • f i j x := by
    intro i j x
    rw [LinearMap.add_apply, LinearMap.add_apply, map_add, sum_neg_index_smul_diag_apply_comm f hf,
      sum_smul_apply_comm_of_commute (f i j) (fun a => e a a) _ (fun a => (hef a a i j).symm)]
    abel
  set H : Module.End ℂ V := ∑ a : Fin k, (-((a : ℕ) : ℂ)) • e a a +
      ∑ b : Fin l, (-((b : ℕ) : ℂ)) • f b b with hH
  have hWH : ∀ w ∈ W, H w ∈ W := by
    intro w hw
    rw [hH]
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply]
    exact W.add_mem (W.sum_mem fun a _ => W.smul_mem _ (hWe a a w hw))
      (W.sum_mem fun b _ => W.smul_mem _ (hWf b b w hw))
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  obtain ⟨c0, hc0⟩ := Module.End.exists_eigenvalue (H.restrict hWH)
  obtain ⟨μ, hμ, hmax⟩ := Set.exists_max_image {c | Module.End.HasEigenvalue (H.restrict hWH) c} Complex.re
    (Module.End.finite_hasEigenvalue _) ⟨c0, hc0⟩
  have hkill : ∀ x ∈ W, H x = μ • x → ∀ (T : Module.End ℂ V) (d : ℂ), 0 < d.re →
      (∀ y ∈ W, T y ∈ W) → (∀ y, H (T y) = T (H y) + d • T y) → T x = 0 := by
    intro x hx hHx T d hd hTW hHT
    by_contra hne
    have hev : Module.End.HasEigenvalue (H.restrict hWH) (μ + d) := by
      rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
      refine ⟨⟨T x, hTW x hx⟩, ?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        apply Subtype.ext
        simp only [LinearMap.restrict_apply, SetLike.val_smul]
        rw [hHT, hHx, map_smul, add_smul]
      · intro h0
        exact hne (congrArg Subtype.val h0)
    have h := hmax _ hev
    simp only [Complex.add_re] at h
    linarith
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Module.End.hasEigenvalue_iff.mp hμ)
  have huH : H (u : V) = μ • (u : V) := by
    have h := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hu)
    simpa [LinearMap.restrict_apply] using h
  have hU0 : W ⊓ Module.End.eigenspace H μ ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨u, Submodule.mem_inf.mpr ⟨u.2, Module.End.mem_eigenspace_iff.mpr huH⟩, ?_⟩
    intro h
    exact hu0 (Subtype.ext h)
  have hUf : FiniteDimensional ℂ (W ⊓ Module.End.eigenspace H μ : Submodule ℂ V) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hT : ∀ s t, Commute (Sum.elim (fun a => e a a) (fun b => f b b) s)
      (Sum.elim (fun a => e a a) (fun b => f b b) t) := by
    rintro (a | a) (b | b)
    · show e a a * e b b = e b b * e a a
      rw [← sub_eq_zero, he a a b b]
      by_cases h : a = b
      · subst h; simp
      · simp [h, Ne.symm h]
    · exact hef a a b b
    · exact (hef b b a a).symm
    · show f a a * f b b = f b b * f a a
      rw [← sub_eq_zero, hf a a b b]
      by_cases h : a = b
      · subst h; simp
      · simp [h, Ne.symm h]
  have hTU : ∀ t, ∀ y ∈ W ⊓ Module.End.eigenspace H μ,
      Sum.elim (fun a => e a a) (fun b => f b b) t y ∈ W ⊓ Module.End.eigenspace H μ := by
    rintro (a | b) y hy
    · obtain ⟨hyW, hyE⟩ := Submodule.mem_inf.mp hy
      refine Submodule.mem_inf.mpr ⟨hWe a a y hyW, ?_⟩
      rw [Module.End.mem_eigenspace_iff]
      show H (e a a y) = μ • e a a y
      rw [hHe, Module.End.mem_eigenspace_iff.mp hyE, map_smul, sub_self, zero_smul, add_zero]
    · obtain ⟨hyW, hyE⟩ := Submodule.mem_inf.mp hy
      refine Submodule.mem_inf.mpr ⟨hWf b b y hyW, ?_⟩
      rw [Module.End.mem_eigenspace_iff]
      show H (f b b y) = μ • f b b y
      rw [hHf, Module.End.mem_eigenspace_iff.mp hyE, map_smul, sub_self, zero_smul, add_zero]
  obtain ⟨v, hv, hv0, hvT⟩ := exists_common_eigenvector_of_commuting _ hT Finset.univ _ hUf hU0 hTU
  obtain ⟨hvW, hvE⟩ := Submodule.mem_inf.mp hv
  have hvH : H v = μ • v := Module.End.mem_eigenspace_iff.mp hvE
  have hde1 : ∀ a, ⨆ n : ℤ, Module.End.eigenspace (e a a) (n : ℂ) = ⊤ := by
    intro a
    rw [eq_top_iff, ← hde]
    exact iSup_le fun κ => le_trans (iInf_le _ a)
      (le_iSup (fun n : ℤ => Module.End.eigenspace (e a a) (n : ℂ)) (κ a))
  have hdf1 : ∀ b, ⨆ n : ℤ, Module.End.eigenspace (f b b) (n : ℂ) = ⊤ := by
    intro b
    rw [eq_top_iff, ← hdf]
    exact iSup_le fun κ => le_trans (iInf_le _ b)
      (le_iSup (fun n : ℤ => Module.End.eigenspace (f b b) (n : ℂ)) (κ b))
  have hκ : ∀ a, ∃ n : ℤ, e a a v = (n : ℂ) • v := by
    intro a
    obtain ⟨c, hc⟩ := hvT (Sum.inl a) (Finset.mem_univ _)
    obtain ⟨n, rfl⟩ := int_lemma_4 (e a a) (hde1 a) hv0 hc
    exact ⟨n, hc⟩
  have hκ' : ∀ b, ∃ n : ℤ, f b b v = (n : ℂ) • v := by
    intro b
    obtain ⟨c, hc⟩ := hvT (Sum.inr b) (Finset.mem_univ _)
    obtain ⟨n, rfl⟩ := int_lemma_4 (f b b) (hdf1 b) hv0 hc
    exact ⟨n, hc⟩
  choose κ hκ using hκ
  choose κ' hκ' using hκ'
  refine ⟨v, hvW, hv0, ?_, ?_, κ, κ', hκ, hκ'⟩
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    refine hkill v hvW hvH (e i j) (((j : ℕ) : ℂ) - ((i : ℕ) : ℂ)) ?_ (hWe i j) (hHe i j)
    rw [Complex.sub_re, Complex.natCast_re, Complex.natCast_re, sub_pos]
    exact_mod_cast hij'
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    refine hkill v hvW hvH (f i j) (((j : ℕ) : ℂ) - ((i : ℕ) : ℂ)) ?_ (hWf i j) (hHf i j)
    rw [Complex.sub_re, Complex.natCast_re, Complex.natCast_re, sub_pos]
    exact_mod_cast hij'

theorem iSup_eigenspace_eq_top {σ ι : Type*} (g : ι → Module.End ℂ (MvPolynomial σ ℂ))
    (w : (σ →₀ ℕ) → ι → ℤ) (hg : ∀ m i, g i (monomial m 1) = (w m i : ℂ) • monomial m 1) :
    ⨆ κ : ι → ℤ, (⨅ i, Module.End.eigenspace (g i) (κ i : ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro P _
  rw [P.as_sum]
  refine Submodule.sum_mem _ (fun n _ => ?_)
  refine Submodule.mem_iSup_of_mem (fun i => w n i) ?_
  rw [Submodule.mem_iInf]
  intro i
  rw [Module.End.mem_eigenspace_iff]
  have h : monomial n (coeff n P) = coeff n P • monomial n (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, hg, smul_comm]

theorem colOp_monomial {σ I J : Type*} [Fintype I] (z : I × J → σ) (k : J) (m : σ →₀ ℕ) :
    colOp ℂ z k k (monomial m 1) = ((∑ a, (m (z (a, k)) : ℤ) : ℤ) : ℂ) • monomial m 1 := by
  unfold colOp
  rw [LinearMap.sum_apply]
  simp only [polar, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    MvPolynomial.X_mul_pderiv_monomial]
  rw [← Finset.sum_smul, ← Nat.cast_smul_eq_nsmul ℂ]
  congr 1
  push_cast
  rfl

theorem rowOp_monomial {σ I J : Type*} [Fintype J] (z : I × J → σ) (a : I) (m : σ →₀ ℕ) :
    rowOp ℂ z a a (monomial m 1) = ((∑ k, (m (z (a, k)) : ℤ) : ℤ) : ℂ) • monomial m 1 := by
  unfold rowOp
  rw [LinearMap.sum_apply]
  simp only [polar, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    MvPolynomial.X_mul_pderiv_monomial]
  rw [← Finset.sum_smul, ← Nat.cast_smul_eq_nsmul ℂ]
  congr 1
  push_cast
  rfl

private theorem coeff_apply_of_diagonal_on_monomials {σ : Type*} (g : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)
    (w : (σ →₀ ℕ) → ℂ) (hg : ∀ n, g (monomial n 1) = w n • monomial n 1)
    (P : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : coeff m (g P) = w m * coeff m P := by
  classical
  have hmon : ∀ n, g (monomial n (coeff n P)) = (coeff n P * w n) • monomial n 1 := by
    intro n
    have h : monomial n (coeff n P) = coeff n P • monomial n (1 : ℂ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [h, map_smul, hg, smul_smul]
  conv_lhs => rw [P.as_sum, map_sum]
  simp only [hmon, coeff_sum, coeff_smul, smul_eq_mul]
  simp only [MvPolynomial.coeff_monomial, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · ring
  · rw [notMem_support_iff.mp h, mul_zero]

theorem colOp_eq_smul_iff {σ I J : Type*} [Fintype I] (z : I × J → σ) (k : J)
    (P : MvPolynomial σ ℂ) (c : ℂ) :
    colOp ℂ z k k P = c • P ↔ ∀ m ∈ P.support, ((∑ a, m (z (a, k)) : ℕ) : ℂ) = c := by
  have hw : ∀ n : σ →₀ ℕ, colOp ℂ z k k (monomial n 1) =
      ((∑ a, n (z (a, k)) : ℕ) : ℂ) • monomial n 1 := by
    intro n
    rw [colOp_monomial]
    simp only [Nat.cast_sum, Int.cast_sum, Int.cast_natCast]
  constructor
  · intro h m hm
    have h1 := congrArg (coeff m) h
    rw [coeff_apply_of_diagonal_on_monomials _ _ hw, coeff_smul, smul_eq_mul] at h1
    exact mul_right_cancel₀ (mem_support_iff.mp hm) h1
  · intro h
    ext m
    rw [coeff_apply_of_diagonal_on_monomials _ _ hw, coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ P.support
    · rw [h m hm]
    · rw [notMem_support_iff.mp hm, mul_zero, mul_zero]

theorem rowOp_eq_smul_iff {σ I J : Type*} [Fintype J] (z : I × J → σ) (a : I)
    (P : MvPolynomial σ ℂ) (c : ℂ) :
    rowOp ℂ z a a P = c • P ↔ ∀ m ∈ P.support, ((∑ k, m (z (a, k)) : ℕ) : ℂ) = c := by
  have hw : ∀ n : σ →₀ ℕ, rowOp ℂ z a a (monomial n 1) =
      ((∑ k, n (z (a, k)) : ℕ) : ℂ) • monomial n 1 := by
    intro n
    rw [rowOp_monomial]
    simp only [Nat.cast_sum, Int.cast_sum, Int.cast_natCast]
  constructor
  · intro h m hm
    have h1 := congrArg (coeff m) h
    rw [coeff_apply_of_diagonal_on_monomials _ _ hw, coeff_smul, smul_eq_mul] at h1
    exact mul_right_cancel₀ (mem_support_iff.mp hm) h1
  · intro h
    ext m
    rw [coeff_apply_of_diagonal_on_monomials _ _ hw, coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ P.support
    · rw [h m hm]
    · rw [notMem_support_iff.mp hm, mul_zero, mul_zero]

end GlobalTheory.JointHarm
