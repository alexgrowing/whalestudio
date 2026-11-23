import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MfacMapDomainAdd
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfLatticeInclusion

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem exists_fd_Ljj (j : Fin G.T.t → ℕ) (jp : ℕ) :
    ∃ W : Submodule ℚ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]), FiniteDimensional ℚ_[p] W ∧
      ∀ x ∈ Ljj p (r := r) G j jp, x ∈ W := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  have : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) := Formalism.CountingSumsFrames.pol_finiteDimensional _
  have : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le inf_le_left
  let bY := Module.finBasis ℚ_[p] Yq
  let Ms := xiMons (r := r) G (G.B - jp)
  let fam : Fin (Module.finrank ℚ_[p] Yq) × Ms → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
    fun ab => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY ab.1 : Yq) : _) * monomial (ab.2 : _ →₀ ℕ) 1
  let W := Submodule.span ℚ_[p] (Set.range fam)
  have hsub : ∀ x ∈ Ljj p (r := r) G j jp, x ∈ W := by
    intro x hx
    have hle : Ljj p (r := r) G j jp ≤ W.restrictScalars ℤ_[p] := by
      unfold Ljj
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, g, hg, rfl⟩
      have hyY : y ∈ Yq := (Submodule.mem_inf.1 hy).1
      have hy2 : y ∈ Submodule.span ℚ_[p] (Set.range fun a => ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
        have h3 : (⟨y, hyY⟩ : Yq) ∈ (⊤ : Submodule ℚ_[p] Yq) := Submodule.mem_top
        rw [← bY.span_eq] at h3
        have h4 := Submodule.mem_map_of_mem (f := Yq.subtype) h3
        rw [Submodule.map_span, ← Set.range_comp] at h4
        exact h4
      have hg2 := xi_mem_span p G (G.B - jp) g hg
      show rename (Formalism.GM.M.chainEmb N r G.T.t) y * g ∈ W
      have hy3 : rename (Formalism.GM.M.chainEmb N r G.T.t) y ∈ Submodule.span ℚ_[p]
          (Set.range fun a => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
        have := Submodule.mem_map_of_mem (f := (rename (Formalism.GM.M.chainEmb N r G.T.t) :
          MvPolynomial _ ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial _ ℚ_[p]).toLinearMap) hy2
        rw [Submodule.map_span, ← Set.range_comp] at this
        exact this
      have hmul := Submodule.mul_mem_mul hy3 hg2
      rw [Submodule.span_mul_span] at hmul
      refine Submodule.span_mono ?_ hmul
      rintro _ ⟨u, ⟨a, rfl⟩, v, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨(a, ⟨m, hm⟩), rfl⟩
    exact hle hx
  exact ⟨W, FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range fam), hsub⟩

theorem bePhi_smul_left (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp (c • u) v = c * bePhi p (r := r) G j jp u v := by
  unfold bePhi
  rw [map_smul, fockK_smul_left, mul_div_assoc]

theorem bePhi_sum_left (j : Fin G.T.t → ℕ) (jp : ℕ) {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp (∑ i ∈ s, f i) v = ∑ i ∈ s, bePhi p (r := r) G j jp (f i) v := by
  unfold bePhi
  rw [map_sum, fockK_sum_left, Finset.sum_div]

theorem bePhi_smul_right (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp u (c • v) = c * bePhi p (r := r) G j jp u v := by
  unfold bePhi
  rw [fockK_smul_right, mul_div_assoc]

theorem gcL_bdd (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) :
    BddAbove {n | ∃ x y : Fin n → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      (∀ i, x i ∈ Ljj p (r := r) G j jp) ∧ (∀ i, y i ∈ Ljj p (r := r) G j jp) ∧
      ∀ i k, bePhi p (r := r) G j jp (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0} := by
  classical
  obtain ⟨W, hW, hsub⟩ := exists_fd_Ljj p (r := r) G j jp
  refine ⟨Module.finrank ℚ_[p] W, ?_⟩
  rintro n ⟨x, y, hx, hy, hxy⟩
  have hp0 : (p : ℚ_[p]) ^ D ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hli : LinearIndependent ℚ_[p] (fun i => (⟨x i, hsub _ (hx i)⟩ : W)) := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have h0 : ∑ k ∈ s, g k • x k = 0 := by
      have := congrArg Subtype.val hs
      simpa using this
    have h1 := congrArg (fun u => bePhi p (r := r) G j jp u (y i)) h0
    simp only [bePhi_sum_left, bePhi_smul_left, hxy] at h1
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [if_neg hk, mul_zero]) (fun h => absurd hi h), if_pos rfl] at h1
    have h2 : bePhi p (r := r) G j jp 0 (y i) = 0 := by
      have := bePhi_smul_left p (r := r) G j jp 0 0 (y i)
      simpa using this
    rw [h2] at h1
    exact (mul_eq_zero.1 h1).resolve_right hp0
  have := hli.fintype_card_le_finrank
  simpa using this

theorem xiMons_spec (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n) :
    (∀ v ∈ m.support, ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c) ∧ (∑ c, m (Formalism.GM.M.xiVar N r G.T.t c) = n) ∧
      (∑ v ∈ m.support, m v = n) := by
  classical
  unfold xiMons at hm
  rw [Finset.mem_image] at hm
  obtain ⟨e, he, rfl⟩ := hm
  have hsum := (CountingStatementReduction.mem_Ev e).1 he
  have happ : ∀ c, (∑ d : Fin r, Finsupp.single (Formalism.GM.M.xiVar N r G.T.t d) (e d)) (Formalism.GM.M.xiVar N r G.T.t c) = e c := by
    intro c
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hd (xiVar_inj (r := r) G h)
    · intro h; exact absurd (Finset.mem_univ c) h
  refine ⟨fun v hv => ?_, by simp only [happ]; exact hsum, ?_⟩
  · by_contra hne
    push Not at hne
    apply Finsupp.mem_support_iff.1 hv
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hne d h.symm
  · have : (∑ d : Fin r, Finsupp.single (Formalism.GM.M.xiVar N r G.T.t d) (e d)).sum (fun _ k => k) = ∑ c, e c := by
      rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
      exact Finset.sum_congr rfl fun d _ => Finsupp.sum_single_index rfl
    rw [← hsum, ← this]
    rfl

theorem card_xiMons_eq (n : ℕ) : (xiMons (r := r) G n).card = dXi r n := by
  classical
  unfold xiMons
  rw [Finset.card_image_of_injective]
  · rw [CountingStatementReduction.card_Ev]
    unfold dXi
    have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have e1 : r' + 1 + n - 1 = n + r' := by omega
    have e2 : n + (r' + 1) - 1 = n + r' := by omega
    rw [e1, e2, Nat.add_sub_cancel, Nat.choose_symm_add]
  · intro e e' h
    funext c
    have := congrArg (fun f : Formalism.GM.M.BVar N r G.T.t →₀ ℕ => f (Formalism.GM.M.xiVar N r G.T.t c)) h
    simp only [Finsupp.finsetSum_apply] at this
    rwa [Finset.sum_eq_single c (fun d _ hd => by rw [Finsupp.single_apply, if_neg (fun h => hd (xiVar_inj (r := r) G h))])
      (fun h => absurd (Finset.mem_univ c) h), Finset.sum_eq_single c
      (fun d _ hd => by rw [Finsupp.single_apply, if_neg (fun h => hd (xiVar_inj (r := r) G h))])
      (fun h => absurd (Finset.mem_univ c) h), Finsupp.single_eq_same, Finsupp.single_eq_same] at this

end Level

end Formalism.MainNotions.G.SymmetricFormBlocks

end
