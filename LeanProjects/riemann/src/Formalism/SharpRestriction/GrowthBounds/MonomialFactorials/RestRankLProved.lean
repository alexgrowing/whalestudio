import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestPlusOf
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime]

theorem finrank_zp_le {V : Type} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
    (M : Submodule ℤ_[p] V) (W : Submodule ℚ_[p] V) [FiniteDimensional ℚ_[p] W] (hMW : ∀ x ∈ M, x ∈ W) :
    Module.finrank ℤ_[p] M ≤ Module.finrank ℚ_[p] W := by
  have hr : Module.rank ℤ_[p] M ≤ (Module.finrank ℚ_[p] W : Cardinal) := by
    apply rank_le
    intro s hs
    have h1 : LinearIndependent ℤ_[p] (fun i : s => ((i : M) : V)) :=
      hs.map' M.subtype (Submodule.ker_subtype M)
    have h2 : LinearIndependent ℚ_[p] (fun i : s => ((i : M) : V)) :=
      (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp h1
    have h3 : LinearIndependent ℚ_[p] (fun i : s => (⟨((i : M) : V), hMW _ (i : M).2⟩ : W)) := by
      refine LinearIndependent.of_comp W.subtype ?_
      exact h2
    have := h3.fintype_card_le_finrank
    simpa using this
  exact Module.finrank_le_of_rank_le hr

end Gen

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

open Classical in

def xiMons (n : ℕ) : Finset (Formalism.GM.M.BVar N r G.T.t →₀ ℕ) :=
  (CountingStatementReduction.Ev r n).image (fun e => ∑ c : Fin r, Finsupp.single (Formalism.GM.M.xiVar N r G.T.t c) (e c))

theorem card_xiMons (n : ℕ) : (xiMons (r := r) G n).card ≤ dXi r n := by
  classical
  unfold xiMons
  refine (Finset.card_image_le).trans ?_
  rw [CountingStatementReduction.card_Ev]
  unfold dXi
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have e1 : r' + 1 + n - 1 = n + r' := by omega
  have e2 : n + (r' + 1) - 1 = n + r' := by omega
  rw [e1, e2, Nat.add_sub_cancel, Nat.choose_symm_add]

theorem xiVar_inj : Function.Injective (Formalism.GM.M.xiVar N r G.T.t) := by
  intro c d h
  simp only [Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2

theorem xi_mem_span (n : ℕ) (g : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (hg : g ∈ Formalism.GM.M.XiPolZ p N r G.T.t n) :
    g ∈ Submodule.span ℚ_[p] ((fun m => (monomial m (1 : ℚ_[p]))) '' (xiMons (r := r) G n : Set _)) := by
  classical
  have hs := (Submodule.mem_inf.1 hg).1
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at hs
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hm' := hs hm
  obtain ⟨hsupp, hsum⟩ := hm'
  have hmono : monomial m (coeff m g) = coeff m g • monomial m (1 : ℚ_[p]) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmono]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, ?_, rfl⟩)
  unfold xiMons
  rw [Finset.mem_coe, Finset.mem_image]
  refine ⟨fun c => m (Formalism.GM.M.xiVar N r G.T.t c), (CountingStatementReduction.mem_Ev _).2 hsum, ?_⟩
  ext v
  rw [Finsupp.finsetSum_apply]
  by_cases hv : ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c
  · obtain ⟨c, rfl⟩ := hv
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hd (xiVar_inj G h)
    · intro h; exact absurd (Finset.mem_univ c) h
  · have h0 : m v = 0 := by
      by_contra hne
      exact hv (hsupp v (Finsupp.mem_support_iff.2 hne))
    rw [h0]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hv ⟨c, h.symm⟩

theorem finrank_Ljj_le (j : Fin G.T.t → ℕ) (jp : ℕ) :
    Module.finrank ℤ_[p] (Ljj p (r := r) G j jp) ≤ dimY p (r := r) G j jp * dXi r (G.B - jp) := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  haveI : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) := Formalism.CountingSumsFrames.pol_finiteDimensional _
  haveI : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le inf_le_left
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
  haveI : FiniteDimensional ℚ_[p] W := FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range fam)
  have h1 := finrank_zp_le (Ljj p (r := r) G j jp) W hsub
  have h2 : Module.finrank ℚ_[p] W ≤ Fintype.card (Fin (Module.finrank ℚ_[p] Yq) × Ms) := finrank_range_le_card fam
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at h2
  have h3 := card_xiMons (r := r) G (G.B - jp)
  calc Module.finrank ℤ_[p] (Ljj p (r := r) G j jp) ≤ Module.finrank ℚ_[p] Yq * Ms.card := h1.trans h2
    _ ≤ dimY p (r := r) G j jp * dXi r (G.B - jp) := Nat.mul_le_mul le_rfl h3

end Level

theorem restRankL_proved (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : RestRankL C0 CE1 CE2 X := by
  intro dl _ aTop _ x _
  exact finrank_Ljj_le X.p (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
