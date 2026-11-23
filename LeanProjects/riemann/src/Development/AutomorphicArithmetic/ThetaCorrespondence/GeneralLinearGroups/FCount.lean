import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleOfClsGLEqSingle

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

private theorem UpperTheory.Lit.Full.count_map_le {α β : Type*} (e : (α →₀ ℤ) →ₗ[ℤ] (β →₀ ℤ)) (A : Set α) (B : Set β)
    (h : ∀ a ∈ A, ∀ b, e (Finsupp.single a 1) b ≠ 0 → b ∈ B) :
    (Finsupp.supported ℤ ℤ A).map e ≤ Finsupp.supported ℤ ℤ B := by
  rw [Finsupp.supported_eq_span_single ℤ A, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  exact (Finsupp.mem_supported ℤ _).2 fun b hb => h a ha b (Finsupp.mem_support_iff.1 hb)

private theorem UpperTheory.Lit.Full.count_equiv {α β : Type*} (e : (α →₀ ℤ) ≃ₗ[ℤ] (β →₀ ℤ)) (A : Set α) (B : Set β)
    (h : ∀ a ∈ A, ∀ b, e (Finsupp.single a 1) b ≠ 0 → b ∈ B)
    (h' : ∀ b ∈ B, ∀ a, e.symm (Finsupp.single b 1) a ≠ 0 → a ∈ A) : Nonempty (A ≃ B) := by
  have h1 := count_map_le e.toLinearMap A B h
  have h2 := count_map_le e.symm.toLinearMap B A h'
  have h3 : (Finsupp.supported ℤ ℤ A).map e.toLinearMap = Finsupp.supported ℤ ℤ B := by
    refine le_antisymm h1 fun y hy => ⟨e.symm y, h2 ⟨y, hy, rfl⟩, by simp⟩
  let f : (A →₀ ℤ) ≃ₗ[ℤ] (B →₀ ℤ) :=
    ((Finsupp.supportedEquivFinsupp (R := ℤ) (M := ℤ) A).symm.trans (e.ofSubmodules _ _ h3)).trans
      (Finsupp.supportedEquivFinsupp (R := ℤ) (M := ℤ) B)
  exact ⟨(Finsupp.basisSingleOne.map f).indexEquiv Finsupp.basisSingleOne⟩

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem UpperTheory.Lit.Full.count_seg_finite (S : Multiset (IrrGL k)) :
    {Δ : Segment k | Δ.ms ≤ S}.Finite := by
  classical
  refine Set.Finite.of_finite_image (f := fun Δ : Segment k => (Δ.first, Δ.len))
    (((S.toFinset.finite_toSet).prod (Set.finite_Iic S.card)).subset ?_) ?_
  · rintro _ ⟨Δ, hΔ, rfl⟩
    refine ⟨?_, ?_⟩
    · have : Δ.first ∈ Δ.ms := Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨0, Δ.len_pos, by simp⟩)
      simpa using Multiset.mem_of_le hΔ this
    · simpa using Multiset.card_le_card (show Δ.ms ≤ S from hΔ)
  · intro Δ _ Δ' _ h
    exact Segment.ext_first (congrArg Prod.fst h) (congrArg Prod.snd h)

private theorem UpperTheory.Lit.Full.count_card_le (𝔪 : Multiset (Segment k)) : 𝔪.card ≤ (msupp 𝔪).card := by
  induction 𝔪 using Multiset.induction_on with
  | empty => simp
  | cons Δ 𝔪 ih =>
    rw [← Multiset.singleton_add, msupp_add, msupp_singleton]
    have := Δ.len_pos
    simp only [Multiset.card_add, Multiset.card_singleton, Segment.card_ms]
    omega

private theorem UpperTheory.Lit.Full.count_mseg_finite (S : Multiset (IrrGL k)) :
    {𝔪 : Multiset (Segment k) | msupp 𝔪 = S}.Finite := by
  classical
  refine (Set.finite_Icc 0 (S.card • (count_seg_finite S).toFinset.val)).subset ?_
  intro 𝔪 h𝔪
  have h𝔪 : msupp 𝔪 = S := h𝔪
  refine ⟨Multiset.zero_le _, Multiset.le_iff_count.2 fun Δ => ?_⟩
  by_cases hΔ : Δ ∈ 𝔪
  · have h1 : Δ.ms ≤ S := by
      obtain ⟨𝔫, rfl⟩ := Multiset.exists_cons_of_mem hΔ
      rw [← h𝔪, ← Multiset.singleton_add, msupp_add, msupp_singleton]
      exact Multiset.le_add_right _ _
    have h2 : Δ ∈ (count_seg_finite S).toFinset := by simpa using h1
    rw [Multiset.count_nsmul, Multiset.count_eq_one_of_mem (Finset.nodup _) h2, mul_one, ← h𝔪]
    exact (Multiset.count_le_card _ _).trans (count_card_le 𝔪)
  · simp [Multiset.count_eq_zero_of_notMem hΔ]

private theorem UpperTheory.Lit.Full.count_msupp (m : Segment k →₀ ℕ) :
    msupp (Finsupp.toMultiset m) = GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum m := by
  induction m using Finsupp.induction_linear with
  | zero => simp [msupp, GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum]
  | add a b ha hb => rw [map_add, msupp_add, ha, hb, GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum_add]
  | single Δ c =>
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum_eq, Finsupp.sum_single_index (zero_smul ℕ Δ.ms), Finsupp.toMultiset_single]
    induction c with
    | zero => simp [msupp]
    | succ c ih => rw [add_smul, add_smul, msupp_add, ih, one_smul, one_smul, msupp_singleton]

end

theorem UpperTheory.Lit.Full.count :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (S : Multiset (IrrGL k)), {x : IrrGL k | HasSupport x.rep S}.Finite ∧ {𝔪 : Multiset (Segment k) | msupp 𝔪 = S}.Finite ∧ {x : IrrGL k | HasSupport x.rep S}.ncard = {𝔪 : Multiset (Segment k) | msupp 𝔪 = S}.ncard := by
  intro hG hBZ hZ k _ _ _ _ S
  classical
  obtain ⟨Z, Ψ, hS, hΨ, hX⟩ := hZ k
  let c := MvPolynomial.basisMonomials (Segment k) ℤ
  let e : (IrrGL k →₀ ℤ) ≃ₗ[ℤ] ((Segment k →₀ ℕ) →₀ ℤ) := Ψ.toIntLinearEquiv.trans c.repr
  have hc : ∀ p m, c.repr p m = MvPolynomial.coeff m p := fun _ _ => rfl
  have hc' : ∀ m, c.repr.symm (Finsupp.single m 1) = MvPolynomial.monomial m 1 := fun m => by
    rw [Module.Basis.repr_symm_single_one]
    simp [c]
  obtain ⟨f⟩ := count_equiv e {x : IrrGL k | HasSupport x.rep S} {m | GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum m = S}
    (fun x hx m hm => GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum_eq_of_coeff_ne hG hBZ hS hΨ hX hx (by rw [← hc]; exact hm))
    (fun m hm z hz => by
      have hm : GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum m = S := hm
      show HasSupport z.rep S
      rw [← hm]
      refine GlobalTheory.LocGL.UnramSupport.hasSupport_of_monomial hS hΨ hX z.2.rep.smooth z.2.rep.irr m ?_
      rw [IrrGL.of_rep, ← hc']
      exact hz)
  let g : {m : Segment k →₀ ℕ | GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum m = S} ≃ {𝔪 : Multiset (Segment k) | msupp 𝔪 = S} :=
    Multiset.toFinsupp.symm.toEquiv.subtypeEquiv fun m => by
      show GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum m = S ↔ msupp (Finsupp.toMultiset m) = S
      rw [count_msupp]
  have hfin := count_mseg_finite S
  haveI := hfin.to_subtype
  exact ⟨Set.finite_coe_iff.1 (Finite.of_equiv _ (f.trans g).symm), hfin, Set.ncard_congr' (f.trans g)⟩
