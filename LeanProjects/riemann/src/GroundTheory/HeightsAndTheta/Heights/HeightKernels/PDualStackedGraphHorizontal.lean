import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedGraph
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopSimpleStacked
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace StackedGraphHorizontal

theorem mul_mem_of_mem_sup {A : Type*} [CommRing A] {I : Ideal A} {g s : A} (hsg : s * g ∈ I) :
    ∀ x ∈ I ⊔ Ideal.span {g}, s * x ∈ I := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  rw [mul_add, show s * (r * g) = r * (s * g) by ring]
  exact I.add_mem (I.mul_mem_left s hy) (I.mul_mem_left r hsg)

theorem length_localized_eq {A : Type*} [CommRing A] {I J W : Ideal A} [W.IsPrime] (hIJ : I ≤ J)
    {s : A} (hs : s ∉ W) (hsJ : ∀ x ∈ J, s * x ∈ I) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ I)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) := by
  let π : (A ⧸ I) →ₗ[A] (A ⧸ J) := Submodule.factor hIJ
  let φ := IsLocalizedModule.map W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ I))
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J)) π
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective J y
    exact ⟨Submodule.mkQ I x, Submodule.factor_mk hIJ x⟩
  have hsurj : Function.Surjective φ := IsLocalizedModule.map_surjective _ _ _ π hπ
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    induction y using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective I m
      have hy' : LocalizedModule.mk (π (Submodule.mkQ I r)) t = 0 := by
        rw [← hy]
        exact (IsLocalizedModule.map_LocalizedModules W.primeCompl π _ t).symm
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hy' ⊢
      obtain ⟨u, hu⟩ := hy'
      refine ⟨⟨s, hs⟩ * u, ?_⟩
      rw [one_smul, smul_zero, smul_zero] at hu ⊢
      rw [Submodule.factor_mk, Submodule.mkQ_apply, Submonoid.smul_def, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, smul_eq_mul] at hu
      have hI : s * (u * r) ∈ I := hsJ _ hu
      rw [Submodule.mkQ_apply, Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul]
      simpa [mul_assoc] using hI
  exact (LinearEquiv.extendScalarsOfIsLocalization W.primeCompl (Localization.AtPrime W)
    (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩)).length_eq

theorem multAt_eq_of_mul_mem {K' : Type} [Fintype K'] {ι : K' → Type} [∀ k, Fintype (ι k)]
    {I J W : Ideal (MRing ι)} (hIJ : I ≤ J) {s : MRing ι} (hs : s ∉ W) (hsJ : ∀ x ∈ J, s * x ∈ I) :
    multAt I W = multAt J W := by
  by_cases hW : W.IsPrime
  · rw [multAt, multAt, dif_pos hW, dif_pos hW]
    exact congrArg ENat.toNat (length_localized_eq hIJ hs hsJ)
  · rw [multAt, multAt, dif_neg hW, dif_neg hW]

theorem sup_le_of_mul_mem {A : Type*} [CommRing A] {I Q : Ideal A} (hQ : Q.IsPrime) {f g s : A} (hs : s ∉ Q)
    (hsg : s * g ∈ I ⊔ Ideal.span {f}) (hle : I ⊔ Ideal.span {f} ≤ Q) : I ⊔ Ideal.span {g} ≤ Q := by
  refine sup_le (le_sup_left.trans hle) ?_
  rw [Ideal.span_singleton_le_iff_mem]
  exact (hQ.mem_or_mem (hle hsg)).resolve_left hs

theorem mem_minimalPrimes_of_mul_mem {A : Type*} [CommRing A] {I W : Ideal A} {f g s s' : A} (hs : s ∉ W)
    (hs' : s' ∉ W) (hsg : s * g ∈ I ⊔ Ideal.span {f}) (hsf : s' * f ∈ I ⊔ Ideal.span {g})
    (hW : W ∈ (I ⊔ Ideal.span {f}).minimalPrimes) : W ∈ (I ⊔ Ideal.span {g}).minimalPrimes :=
  ⟨⟨hW.1.1, sup_le_of_mul_mem hW.1.1 hs hsg hW.1.2⟩, fun _ hQ hQW =>
    hW.2 ⟨hQ.1, sup_le_of_mul_mem hQ.1 (fun h => hs' (hQW h)) hsf hQ.2⟩ hQW⟩

variable {T : Type} [Fintype T] [DecidableEq T]

theorem mul_mem_sup_first (P : Ideal (MRing (dualBlocks T))) (a : T → ℤ) (l t : T) :
    (C (a l) * graphFirst l) * graphSecond t ∈
      graphIdeal P (linForm (stackedDiag a)) ⊔ Ideal.span {C (a t) * graphFirst t} := by
  have h := TopDualSimpleStacked.minor_mem P a l t
  have e : (C (a l) * graphFirst l) * graphSecond t = graphSecond l * (C (a t) * graphFirst t) -
      (graphSecond l * (C (a t) * graphFirst t) - graphSecond t * (C (a l) * graphFirst l)) := by ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_left h)

theorem mul_mem_sup_second (P : Ideal (MRing (dualBlocks T))) (a : T → ℤ) (l t : T) :
    graphSecond l * (C (a t) * graphFirst t) ∈
      graphIdeal P (linForm (stackedDiag a)) ⊔ Ideal.span {graphSecond t} := by
  have h := TopDualSimpleStacked.minor_mem P a l t
  have e : graphSecond l * (C (a t) * graphFirst t) =
      (graphSecond l * (C (a t) * graphFirst t) - graphSecond t * (C (a l) * graphFirst l)) +
        (C (a l) * graphFirst l) * graphSecond t := by ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mem_sup_left h)
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

theorem C_mul_first_not_mem {P : Ideal (MRing (dualBlocks T))} {a : T → ℤ} (ha : ∀ t, a t ≠ 0)
    {W : Ideal (MRing (stackedBlocks T))} (hW : W.IsPrime) (hhor : IsHorizontal W)
    (hΓ : graphIdeal P (linForm (stackedDiag a)) ≤ W) {j l : T} (hj : graphFirst j ∉ W)
    (hl : graphSecond l ∉ W) : C (a l) * graphFirst l ∉ W := by
  have hC : ∀ c : ℤ, c ≠ 0 → (C c : MRing (stackedBlocks T)) ∉ W := by
    intro c hc h
    have h' : c ∈ W.comap (C : ℤ →+* MRing (stackedBlocks T)) := h
    rw [hhor] at h'
    exact hc h'
  intro h
  have hm := hΓ (TopDualSimpleStacked.minor_mem P a l j)
  have h2 : graphSecond l * (C (a j) * graphFirst j) ∈ W := by
    have := W.add_mem hm (W.mul_mem_left (graphSecond j) h)
    rwa [sub_add_cancel] at this
  rcases hW.mem_or_mem h2 with h3 | h3
  · exact hl h3
  · rcases hW.mem_or_mem h3 with h4 | h4
    · exact hC _ (ha j) h4
    · exact hj h4

end StackedGraphHorizontal

open StackedGraphHorizontal in

theorem DualStackedGraphHorizontal.proof : DualStackedGraphHorizontal.Statement := by
  intro K _ _ i F F' T _ _ b b' a _ hab t W hhor
  have ha : ∀ t, a t ≠ 0 := by
    intro t h0
    apply b.ne_zero t
    apply Subtype.ext
    rw [hab t, h0, zero_smul]
    rfl
  have key : W.IsPrime → stackedGraph b' a ≤ W → IsRelevant W →
      ∃ s s' : MRing (stackedBlocks T), s ∉ W ∧ s' ∉ W ∧
        s * (C (a t) * graphFirst (T := T) t) ∈ stackedGraph b' a ⊔ Ideal.span {graphSecond (T := T) t} ∧
        s' * graphSecond (T := T) t ∈ stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst (T := T) t} := by
    intro hW hΓ hrel
    obtain ⟨j, hj⟩ := hrel (Sum.inl ())
    obtain ⟨l, hl⟩ := hrel (Sum.inr ())
    exact ⟨graphSecond (T := T) l, C (a l) * graphFirst (T := T) l, hl, C_mul_first_not_mem ha hW hhor hΓ hj hl,
      mul_mem_sup_second _ a l t, mul_mem_sup_first _ a l t⟩
  refine ⟨⟨fun hW => ?_, fun hW => ?_⟩, fun hW => ?_⟩
  · obtain ⟨s, s', hs, hs', hsg, hsf⟩ := key hW.1.1.1 (le_sup_left.trans hW.1.1.2) hW.2
    exact ⟨mem_minimalPrimes_of_mul_mem hs hs' hsg hsf hW.1, hW.2⟩
  · obtain ⟨s, s', hs, hs', hsg, hsf⟩ := key hW.1.1.1 (le_sup_left.trans hW.1.1.2) hW.2
    exact ⟨mem_minimalPrimes_of_mul_mem hs' hs hsf hsg hW.1, hW.2⟩
  · obtain ⟨s, s', hs, hs', hsg, hsf⟩ := key hW.1.1.1 (le_sup_left.trans hW.1.1.2) hW.2
    rw [multAt_eq_of_mul_mem le_sup_left hs (mul_mem_of_mem_sup hsg),
      multAt_eq_of_mul_mem (le_sup_left : stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst (T := T) t} ≤ _) hs'
        (mul_mem_of_mem_sup hsf), sup_right_comm]

end

end GroundTheory.Heights₂.Heights
