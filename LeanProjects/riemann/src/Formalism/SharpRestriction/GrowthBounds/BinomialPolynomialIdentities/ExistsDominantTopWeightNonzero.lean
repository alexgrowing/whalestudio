import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RestSplit

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases

section basic

variable {L : Type} [CommRing L] {n : ℕ}

theorem partialAct_X (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L) (x : ℕ × Fin n) :
    actI isVec i g gi (X x) = if x.1 < i then
      (if isVec x.1 then ∑ b, X (x.1, b) * C (g b x.2) else ∑ b, X (x.1, b) * C (gi x.2 b)) else X x := by
  simp [actI]

theorem partialAct_eq_fullAct_of_vars_lt (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L)
    {P : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ P.vars, x.1 < i) :
    actI isVec i g gi P = actAll isVec g gi P := by
  refine MvPolynomial.hom_congr_vars (f₁ := (actI isVec i g gi).toRingHom)
    (f₂ := (actAll isVec g gi).toRingHom) ?_ ?_ rfl
  · ext r
    simp
  · intro x hx _
    have hxi := hv x hx
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, actI, actAll, MvPolynomial.aeval_X, if_pos hxi]
    split_ifs
    · simp [Matrix.vecMul, dotProduct]
    · simp [Matrix.vecMul, dotProduct]

theorem partialAct_fix_of_vars_ge (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L)
    {Q : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ Q.vars, i ≤ x.1) :
    actI isVec i g gi Q = Q := by
  conv_rhs => rw [← AlgHom.id_apply (R := L) Q]
  refine MvPolynomial.hom_congr_vars (f₁ := (actI isVec i g gi).toRingHom)
    (f₂ := (AlgHom.id L (MvPolynomial (ℕ × Fin n) L)).toRingHom) ?_ ?_ rfl
  · ext r
    simp
  · intro x hx _
    have hxi : ¬ x.1 < i := not_lt.mpr (hv x hx)
    simp [actI, hxi]

theorem partialWeight_eq_torusWeight_of_lt (isVec : ℕ → Bool) (i : ℕ) {e : ℕ × Fin n →₀ ℕ} (h : ∀ x ∈ e.support, x.1 < i) :
    Finsupp.weight (wtI isVec i) e = Finsupp.weight (torusW isVec) e := by
  simp only [Finsupp.weight_apply]
  refine Finsupp.sum_congr (fun x hx => ?_)
  simp [wtI, h x hx]

theorem partialWeight_eq_zero_of_ge (isVec : ℕ → Bool) (i : ℕ) {e : ℕ × Fin n →₀ ℕ} (h : ∀ x ∈ e.support, i ≤ x.1) :
    Finsupp.weight (wtI (n := n) isVec i) e = 0 := by
  simp only [Finsupp.weight_apply]
  refine (Finsupp.sum_congr (g2 := fun _ _ => (0 : Fin n → ℤ)) (fun x hx => ?_)).trans (by simp)
  have hx' : ¬ x.1 < i := not_lt.mpr (h x hx)
  simp [wtI, hx']

theorem fullAct_pathWord_support_dominated (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ) (i : ℕ) (I' : ℤ → Finset (Fin n))
    (g : (Matrix (Fin n) (Fin n) L)ˣ) (hp : IsPath n isVec B μ i) (hI : IsIndex (μ i) I') :
    ∀ e ∈ (actAll isVec (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L)
        (psiPath L isVec μ i I')).support, DomLe (Finsupp.weight (torusW isVec) e) (μ i) := by
  intro e he
  refine (Top.factEV L n i isVec B μ I' g hp hI).1 _ ?_
  intro h0
  have h1 := congrArg (coeff e) h0
  rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at h1
  exact (mem_support_iff.1 he) h1

end basic

theorem restWord : RestWord := by
  classical
  intro L _ n N i isVec B μ I g gi hg hp hI hi e he
  rcases subsingleton_or_nontrivial L with hs | hnt
  · exfalso
    have h0 : actI isVec i g gi (psiPath L isVec μ N I) = 0 := Subsingleton.elim _ _
    rw [h0] at he
    simp at he
  have hpi : IsPath n isVec B μ i :=
    ⟨hp.1, fun j hj => hp.2.1 j (hj.trans hi), fun j hj => hp.2.2 j (lt_of_lt_of_le hj hi)⟩
  let gu : (Matrix (Fin n) (Fin n) L)ˣ := ⟨g, gi, hg, mul_eq_one_comm.1 hg⟩
  obtain ⟨F1, hF1⟩ := A3ev.exists_cols hp
  obtain ⟨F2, hF2⟩ := A3ev.exists_cols hpi
  obtain ⟨F, hF⟩ : ∃ F, F = F1 ∪ F2 := ⟨_, rfl⟩
  have hFN : A3ev.Cols isVec μ N F := fun c hc => hF1 c (fun h => hc (hF ▸ Finset.mem_union_left _ h))
  have hFi : A3ev.Cols isVec μ i F := fun c hc => hF2 c (fun h => hc (hF ▸ Finset.mem_union_right _ h))
  choose Q hQ1 hQ2 using fun c : ℤ => A0.trunc L n i isVec μ c N hi (I c)
  have hexp : psiPath L isVec μ N I = ∑ p ∈ F.pi (fun _ => (univ : Finset (Finset (Fin n)))),
      (∏ c ∈ F, pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) L)) i (A3ev.extF F p c)) *
        (∏ c ∈ F, Q c (A3ev.extF F p c)) := by
    rw [A3ev.psi_eq_prod L hFN hI, Finset.prod_congr rfl (fun c _ => hQ2 c), Finset.prod_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.prod_mul_distrib, ← Finset.prod_attach F]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp [A3ev.extF, x.2]
  rw [hexp, map_sum] at he
  obtain ⟨p, -, hpe⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum he)
  obtain ⟨I', hI'⟩ : ∃ I', I' = A3ev.extF F p := ⟨_, rfl⟩
  rw [← hI'] at hpe
  by_cases hidx : IsIndex (μ i) I'
  · have h1 : ∏ c ∈ F, pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) L)) i (I' c) =
        psiPath L isVec μ i I' := (A3ev.psi_eq_prod L hFi hidx).symm
    rw [h1, map_mul] at hpe
    have hv1 : ∀ x ∈ (psiPath L isVec μ i I').vars, x.1 < i := by
      refine DominanceOrderLemmas.vars_of_polB (N := i) (B := B) ?_
      rw [polB, Submodule.mem_iInf]
      intro j
      exact (pathProductDegrees L n i isVec B μ I' hpi hidx).2 j
    have hv2 : ∀ x ∈ (∏ c ∈ F, Q c (I' c)).vars, i ≤ x.1 := by
      intro x hx
      obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 (vars_prod _ hx)
      exact (mem_supported.1 (hQ1 c (I' c))) (Finset.mem_coe.2 hc)
    rw [partialAct_eq_fullAct_of_vars_lt _ _ _ _ hv1, partialAct_fix_of_vars_ge _ _ _ _ hv2] at hpe
    obtain ⟨e1, he1, e2, he2, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ hpe)
    have hw2 : Finsupp.weight (wtI (n := n) isVec i) e2 = 0 :=
      partialWeight_eq_zero_of_ge isVec i fun x hx => hv2 x ((mem_vars_iff_mem_support x).2 ⟨e2, he2, hx⟩)
    have hw1 : Finsupp.weight (wtI isVec i) e1 = Finsupp.weight (torusW isVec) e1 :=
      partialWeight_eq_torusWeight_of_lt isVec i fun x hx =>
        DominanceOrderLemmas.vars_act isVec g gi hv1 x ((mem_vars_iff_mem_support x).2 ⟨e1, he1, hx⟩)
    rw [map_add, hw2, add_zero, hw1]
    exact fullAct_pathWord_support_dominated isVec B μ i I' gu hpi hidx e1 he1
  · exfalso
    have hz : ∏ c ∈ F, pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) L)) i (I' c) = 0 := by
      obtain ⟨c, hc⟩ := not_forall.1 (show ¬ ∀ c : ℤ, (I' c).card =
        if 1 ≤ c then colHeight (μ i) c else n - colHeight (μ i) c from hidx)
      have hcF : c ∈ F := by
        by_contra hn
        apply hc
        have h1 : I' c = ∅ := by rw [hI']; exact dif_neg hn
        have h2 := A1hw.isIndex_can (μ i) c
        rw [(hFi c hn).2 _ (A1hw.isIndex_can (μ i))] at h2
        rw [h1]
        exact h2
      refine Finset.prod_eq_zero hcF ?_
      by_contra hne
      exact hc (A0.pathWord_card hpi c _ i le_rfl _ hne)
    rw [hz, zero_mul, map_zero] at hpe
    simp at hpe

open A3ev DominanceOrderLemmas in
theorem exists_dominant_top_weight_nonzero (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ)
    (c : PathIdx n N isVec B →₀ k) (x₁ : PathIdx n N isVec B) (hx₁ : x₁ ∈ c.support) :
    ∃ μ₀, Antitone μ₀ ∧ DomLe (x₁.1.1 N) μ₀ ∧
      evC k n isVec μ₀ (c.sum fun x a => a • psiPath k isVec x.1.1 N x.1.2) ≠ 0 := by
  classical
  have hEV : FactEV := Top.factEV
  have hT : (c.support.filter fun x => DomLe (x₁.1.1 N) (x.1.1 N)).Nonempty :=
    ⟨x₁, Finset.mem_filter.2 ⟨hx₁, domLe_refl _⟩⟩
  obtain ⟨x₀, hx₀, hmax⟩ := Finset.exists_max_image _
    (fun x : PathIdx n N isVec B => height (x.1.1 N)) hT
  rw [Finset.mem_filter] at hx₀
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, x₀.1.1 N = μ₀ := ⟨_, rfl⟩
  have hanti : Antitone μ₀ := hμ₀ ▸ x₀.2.1.2.1 N le_rfl
  have hd₀ : DomLe (x₁.1.1 N) μ₀ := hμ₀ ▸ hx₀.2
  refine ⟨μ₀, hanti, hd₀, fun h1 => ?_⟩
  rw [Finsupp.sum, map_sum] at h1
  simp_rw [map_smul] at h1
  have h2 : ∑ x ∈ c.support.filter (fun x => x.1.1 N = μ₀), c x • fam k x = 0 := by
    have h3 := Finset.sum_filter_of_ne (s := c.support)
      (p := fun x : PathIdx n N isVec B => x.1.1 N = μ₀)
      (f := fun x => c x • evC k n isVec μ₀ (psiPath k isVec x.1.1 N x.1.2)) ?_
    · rw [← h1, ← h3]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_filter] at hx
      rw [evC_psi k μ₀ x.2.1 x.2.2.2.1, ← hx.2, (ev_gen hEV k x.2.1 x.2.2.2.1).2]
      unfold fam
      rw [smul_eq_C_mul]
    · intro x hx hne
      have he : evC k n isVec μ₀ (psiPath k isVec x.1.1 N x.1.2) ≠ 0 :=
        fun h => hne (by rw [h, smul_zero])
      rw [evC_psi k μ₀ x.2.1 x.2.2.2.1] at he
      have hd : DomLe μ₀ (x.1.1 N) := (ev_gen hEV k x.2.1 x.2.2.2.1).1 μ₀ he
      refine domLe_eq hd ?_
      rw [← hμ₀]
      exact hmax x (Finset.mem_filter.2 ⟨hx, domLe_trans hd₀ hd⟩)
  exact (Finsupp.mem_support_iff.1 hx₀.1) (linearIndepOn_iff'.1 (fam_li fact_break k n N isVec B μ₀ hanti) _ c
    (fun x hx => (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2) h2 x₀
    (Finset.mem_filter.2 ⟨hx₀.1, hμ₀⟩))

theorem restTop : RestTop := by
  classical
  intro k _ n N isVec B pi G hpi hG hgood
  have hG' : G ∈ Submodule.span k
      (Set.range fun x : PathIdx n N isVec B => psiPath k isVec x.1.1 N x.1.2) := by
    rw [(Top.psiPath_basis n N isVec B k).2]
    exact hG
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hG'
  have key : ∀ x ∈ c.support, x.1.1 N ∈ pi := by
    intro x hx
    obtain ⟨μ₀, ha, hd, hne⟩ := exists_dominant_top_weight_nonzero k n N isVec B c x hx
    rw [hc] at hne
    have hne' : weightedHomogeneousComponent (torusW isVec) μ₀
        (actAll isVec (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
          (map (algebraMap k (GenField k n)) G)) ≠ 0 := hne
    obtain ⟨e, he⟩ := MvPolynomial.ne_zero_iff.1 hne'
    rw [coeff_weightedHomogeneousComponent] at he
    split_ifs at he with hw
    · have hvG : ∀ y ∈ (map (algebraMap k (GenField k n)) G).vars, y.1 < N :=
        fun y hy => DominanceOrderLemmas.vars_of_polB hG y (vars_map G (algebraMap k (GenField k n)) hy)
      have hmem : e ∈ (actI isVec N (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
          (map (algebraMap k (GenField k n)) G)).support := by
        rw [partialAct_eq_fullAct_of_vars_lt _ _ _ _ hvG]
        exact mem_support_iff.2 he
      have hwt : Finsupp.weight (wtI isVec N) e = μ₀ := by
        rw [partialWeight_eq_torusWeight_of_lt]
        · exact hw
        · intro y hy
          exact DominanceOrderLemmas.vars_act isVec _ _ hvG y ((mem_vars_iff_mem_support y).2 ⟨e, mem_support_iff.2 he, hy⟩)
      have h3 := hgood e hmem (by rw [hwt]; exact ha)
      rw [hwt] at h3
      exact hpi μ₀ h3 _ (x.2.1.2.1 N le_rfl) hd
    · exact absurd rfl he
  rw [← hc]
  exact Submodule.sum_mem _ fun x hx =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, key x hx, rfl⟩)

end Formalism.MainNotions.G.ColumnFamilies
