import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthFilterFinRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelCasselmanHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShuffleCountLinearIndependentClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.LocGL.UnramSupport

open MvPolynomial ValuativeRel

theorem exists_uniformizer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  have h0 : x ≠ 0 := by
    rintro rfl
    exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)
  exact ⟨Units.mk0 x h0, by simpa using hx⟩

theorem exists_monomial_of_count_zero (I S : Type 1) (A : Type) [DecidableEq A] [LinearOrder A]
    (Ψ : (I →₀ ℤ) ≃+ MvPolynomial S ℤ) (M : I → List A → ℕ∞) (U : Set S) (ℓ : S → List A)
    (φ : S → GlobalTheory.ShuffleAlgebra ℚ A) (hinj : Set.InjOn ℓ U)
    (hU : ∀ Δ ∈ U, GlobalTheory.IsLyndon (ℓ Δ) ∧ φ Δ = GlobalTheory.ShuffleAlgebra.word ℚ (ℓ Δ))
    (h0 : ∀ Δ ∉ U, φ Δ = 0)
    (H : ∀ m : S →₀ ℕ, 0 ≤ Ψ.symm (MvPolynomial.monomial m 1) ∧ ∃ s : Multiset (List A),
      (∀ w, ((Ψ.symm (MvPolynomial.monomial m 1)).sum fun x a => (a.toNat : ℕ∞) * M x w) =
        (s.count w : ℕ∞)) ∧ (s.map (GlobalTheory.ShuffleAlgebra.word ℚ)).sum = m.prod fun Δ e => φ Δ ^ e)
    (y : I) (hy : ∀ w, M y w = 0) :
    ∃ m : S →₀ ℕ, (∃ Δ ∈ m.support, Δ ∉ U) ∧ Ψ.symm (MvPolynomial.monomial m 1) y ≠ 0 := by
  classical
  choose hpos s hs hsum using H
  by_contra hcon
  push Not at hcon
  obtain ⟨P, hP⟩ : ∃ P, P = Ψ (Finsupp.single y 1) := ⟨_, rfl⟩
  have hPs : Ψ.symm P = Finsupp.single y 1 := by rw [hP, AddEquiv.symm_apply_apply]
  have hdec : Finsupp.single y (1 : ℤ) =
      ∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1) := by
    rw [← hPs]
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← map_zsmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hcnt : ∀ (c : I →₀ ℤ) (t : Multiset (List A)), 0 ≤ c →
      (∀ w, (c.sum fun x a => (a.toNat : ℕ∞) * M x w) = (t.count w : ℕ∞)) → ∀ w,
      (t.count w : ℤ) = Finsupp.linearCombination ℤ (fun x => ((M x w).toNat : ℤ)) c := by
    intro c t hc ht w
    have hc' : ∀ x, 0 ≤ c x := fun x => by simpa using Finsupp.le_def.1 hc x
    have hfin : ∀ x ∈ c.support, M x w ≠ ⊤ := by
      intro x hx htop
      have hcx : c x ≠ 0 := Finsupp.mem_support_iff.1 hx
      have hn : ((c x).toNat : ℕ∞) ≠ 0 := by
        have := hc' x
        exact_mod_cast (by omega : (c x).toNat ≠ 0)
      have hle : ((c x).toNat : ℕ∞) * M x w ≤ c.sum fun x a => (a.toNat : ℕ∞) * M x w :=
        Finset.single_le_sum (f := fun x => ((c x).toNat : ℕ∞) * M x w) (fun _ _ => zero_le) hx
      rw [ht w, htop, ENat.mul_top hn] at hle
      exact ENat.natCast_ne_top _ (top_le_iff.1 hle)
    have h1 := ht w
    rw [Finsupp.sum] at h1
    have h2 : ∑ x ∈ c.support, ((c x).toNat : ℕ∞) * M x w =
        ((∑ x ∈ c.support, (c x).toNat * (M x w).toNat : ℕ) : ℕ∞) := by
      push_cast
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [ENat.natCast_toNat (hfin x hx)]
    rw [h2, Nat.cast_inj] at h1
    rw [Finsupp.linearCombination_apply, Finsupp.sum, ← h1]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [smul_eq_mul, Int.toNat_of_nonneg (hc' x)]
  have hN : ∀ w, ∑ m ∈ P.support, P.coeff m * ((s m).count w : ℤ) = 0 := by
    intro w
    have e1 : ∀ m, ((s m).count w : ℤ) = Finsupp.linearCombination ℤ (fun x => ((M x w).toNat : ℤ))
        (Ψ.symm (MvPolynomial.monomial m 1)) := fun m => hcnt _ _ (hpos m) (hs m) w
    have e2 : ∑ m ∈ P.support, P.coeff m * ((s m).count w : ℤ) =
        Finsupp.linearCombination ℤ (fun x => ((M x w).toNat : ℤ))
          (∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_zsmul, e1 m, smul_eq_mul]
    rw [e2, ← hdec, Finsupp.linearCombination_single, hy w]
    simp
  obtain ⟨Wset, hW⟩ : ∃ Wset : Finset (List A), ∀ m ∈ P.support, (s m).toFinset ⊆ Wset :=
    ⟨P.support.biUnion fun m => (s m).toFinset, fun m hm => Finset.subset_biUnion_of_mem (fun m => (s m).toFinset) hm⟩
  have hsum' : ∀ m ∈ P.support, (m.prod fun Δ e => φ Δ ^ e) =
      ∑ w ∈ Wset, ((s m).count w : ℚ) • GlobalTheory.ShuffleAlgebra.word ℚ w := by
    intro m hm
    rw [← hsum m, Finset.sum_multiset_map_count]
    simp_rw [Nat.cast_smul_eq_nsmul]
    refine Finset.sum_subset (hW m hm) fun w _ hw => ?_
    rw [Multiset.count_eq_zero.2 (by simpa using hw), zero_smul]
  have haeval : MvPolynomial.aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P) = 0 := by
    have hterm : ∀ m ∈ P.support, algebraMap ℚ (GlobalTheory.ShuffleAlgebra ℚ A)
        ((Int.castRingHom ℚ) (P.coeff m)) * (m.prod fun Δ e => φ Δ ^ e) =
        ∑ w ∈ Wset, (((P.coeff m * ((s m).count w : ℤ) : ℤ) : ℚ)) • GlobalTheory.ShuffleAlgebra.word ℚ w := by
      intro m hm
      rw [hsum' m hm, ← Algebra.smul_def, Finset.smul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [smul_smul]
      congr 1
      push_cast
      simp
    conv_lhs => rw [P.as_sum]
    rw [map_sum, map_sum]
    simp only [MvPolynomial.map_monomial, MvPolynomial.aeval_monomial]
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [← Finset.sum_smul]
    have h3 : (∑ m ∈ P.support, (((P.coeff m * ((s m).count w : ℤ)) : ℤ) : ℚ)) = 0 := by
      exact_mod_cast hN w
    rw [h3, zero_smul]
  have hind : AlgebraicIndependent ℚ (fun Δ : U => φ Δ) := by
    have h1 := (GlobalTheory.Published.RadfordShufflePolynomial.algebraicIndependent
      GlobalTheory.Published.radfordShufflePolynomial_holds ℚ A).comp
      (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // GlobalTheory.IsLyndon w}))
      (fun a b h => Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val h)))
    have hfun : (fun Δ : U => φ Δ) = (fun l : {w : List A // GlobalTheory.IsLyndon w} =>
        GlobalTheory.ShuffleAlgebra.word ℚ l.1) ∘ (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // GlobalTheory.IsLyndon w})) :=
      funext fun Δ => (hU Δ Δ.2).2
    rw [hfun]
    exact h1
  have hcoef : ∀ m : S →₀ ℕ, (∀ Δ ∈ m.support, Δ ∈ U) → P.coeff m = 0 := by
    intro m hm
    have := GlobalTheory.ShuffleCount.coeff_eq_zero_of_aeval_eq_zero U φ hind h0 _ haeval m hm
    rw [MvPolynomial.coeff_map] at this
    simpa using this
  have h1 := congrArg (fun f => f y) hdec
  simp only [Finsupp.single_eq_same, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul] at h1
  rw [Finset.sum_eq_zero] at h1
  · exact one_ne_zero h1
  · intro m _
    by_cases hm : ∃ Δ ∈ m.support, Δ ∉ U
    · rw [hcon m hm, mul_zero]
    · push Not at hm
      rw [hcoef m hm, zero_mul]

private theorem hasSupport_segment_class {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)}
    (hS : IsSegmentClass k Z) (Δ : Segment k) :
    HasSupport (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) Δ.ms := by
  have hd : ∑ a, (Δ.term a).1 = Δ.len * Δ.d := by
    rw [Segment.sum_term_fst]; rfl
  obtain ⟨φ, hφ⟩ := ((hS Δ Δ.start.rep Δ.start.cl_rep (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd)
    (Z Δ).rep).1.1 (Z Δ).cl_rep)
  have e := segProdEquiv Δ hd
  have hsq : IsSubquotient (Z Δ).rep.ρ (prodIrr Δ.term hd) :=
    IsSubquotient.trans (IsSubquotient.of_injective φ hφ)
      (IsSubquotient.of_injective e.toIntertwiningMap fun a b h => e.toLinearEquiv.injective h)
  exact hasSupport_of_isSubquotient (Z Δ).rep.irr (fun a => Δ.isCusp_term a) hsq

end GlobalTheory.LocGL.UnramSupport

namespace GlobalTheory.LocGL.UnramSupport

open MvPolynomial ValuativeRel GlobalTheory.LocGL.SupportRing GlobalTheory.SmGL.MultiIrr GlobalTheory.JHMult GlobalTheory.SmGL.Segment

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pos_X {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)}
    {Ψ : GrothGL k ≃+ MvPolynomial (Segment k) ℤ} (hS : IsSegmentClass k Z) (hΨ : IsProductIso k Ψ)
    (hX : ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ) (Δ : Segment k) :
    Pos Ψ (MvPolynomial.X Δ) ∧ Pos Ψ (pc Ψ Δ.ms - MvPolynomial.X Δ) := by
  classical
  set x : IrrGL k := ⟨Δ.len * Δ.d, Z Δ⟩ with hx
  have hb : MvPolynomial.X Δ = bas Ψ x := (hX Δ).symm
  have h1 := pos_pc_sub hΨ (hasSupport_segment_class hS Δ) x.2.rep.smooth x.2.rep.irr
  rw [IrrGL.of_rep] at h1
  rw [hb]
  exact ⟨pos_bas _, h1⟩

theorem pc_nsmul {Ψ : GrothGL k ≃+ MvPolynomial (Segment k) ℤ} (t : Multiset (IrrGL k)) (a : ℕ) :
    pc Ψ (a • t) = pc Ψ t ^ a := by
  unfold pc
  rw [Multiset.map_nsmul, Multiset.prod_nsmul]

theorem hasSupport_of_monomial {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)}
    {Ψ : GrothGL k ≃+ MvPolynomial (Segment k) ℤ} (hS : IsSegmentClass k Z) (hΨ : IsProductIso k Ψ)
    (hX : ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ)
    {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V}
    (hs : IsSmooth π) (hi : π.IsIrreducible) (m : Segment k →₀ ℕ)
    (h : Ψ.symm (MvPolynomial.monomial m 1) (IrrGL.of π hs hi) ≠ 0) :
    HasSupport π (∑ Δ ∈ m.support, m Δ • Δ.ms) := by
  classical
  refine hasSupport_of_coef_ne hΨ ?_ hs hi ?_
  · intro y hy
    obtain ⟨Δ, -, hΔ⟩ := Multiset.mem_sum.1 hy
    have hy' := Multiset.mem_of_mem_nsmul hΔ
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy'
    exact Δ.isCusp_term a
  · have hpow : ∀ (Δ : Segment k) (e : ℕ), Pos Ψ (MvPolynomial.X Δ ^ e) ∧
        Pos Ψ (pc Ψ Δ.ms ^ e - MvPolynomial.X Δ ^ e) := by
      intro Δ e
      have := pos_prod_sub hΨ (Finset.range e) (f := fun _ => MvPolynomial.X Δ)
        (g := fun _ => pc Ψ Δ.ms) (fun _ => (pos_X hS hΨ hX Δ).1) (fun _ => (pos_X hS hΨ hX Δ).2)
      simpa [Finset.prod_const, Finset.card_range] using this
    obtain ⟨h1, h2⟩ := pos_prod_sub hΨ m.support (f := fun Δ => MvPolynomial.X Δ ^ m Δ)
      (g := fun Δ => pc Ψ Δ.ms ^ m Δ) (fun Δ => (hpow Δ (m Δ)).1) (fun Δ => (hpow Δ (m Δ)).2)
    have hpc : pc Ψ (∑ Δ ∈ m.support, m Δ • Δ.ms) = ∏ Δ ∈ m.support, pc Ψ Δ.ms ^ m Δ := by
      rw [pc_sum]
      exact Finset.prod_congr rfl fun Δ _ => pc_nsmul _ _
    have hmono : MvPolynomial.monomial m (1 : ℤ) = ∏ Δ ∈ m.support, MvPolynomial.X Δ ^ m Δ := by
      rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod]
    set y := IrrGL.of π hs hi
    have key : Ψ.symm (pc Ψ (∑ Δ ∈ m.support, m Δ • Δ.ms)) y =
        Ψ.symm (MvPolynomial.monomial m 1) y +
          Ψ.symm (pc Ψ (∑ Δ ∈ m.support, m Δ • Δ.ms) - MvPolynomial.monomial m 1) y := by
      rw [← Finsupp.add_apply, ← map_add, add_sub_cancel]
    have ha : 0 ≤ Ψ.symm (MvPolynomial.monomial m 1) y := by rw [hmono]; exact h1 y
    have hb : 0 ≤ Ψ.symm (pc Ψ (∑ Δ ∈ m.support, m Δ • Δ.ms) - MvPolynomial.monomial m 1) y := by
      rw [hmono, hpc]; exact h2 y
    rw [key]
    omega

end GlobalTheory.LocGL.UnramSupport

namespace GlobalTheory.LocGL.UnramSupport

open ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL.Exponents

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_wordMult_segment_ne {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)}
    (hS : IsSegmentClass k Z) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (z : ℂˣ) {l : ℕ}
    (hl : 0 < l) :
    ∃ w, wordMult (Z (Segment.ofChar (unrChar k z) (isSmoothChar_of_isUnram (isUnram_unrChar k z)) l hl)).rep.ρ w ≠ 0 := by
  classical
  have hχ : IsSmoothChar (unrChar k z) := isSmoothChar_of_isUnram (isUnram_unrChar k z)
  obtain ⟨e⟩ := cl_eq_iff_rep.1 (IsSegmentClass.ofChar hS hχ hl).symm
  have hψu : IsUnram (unrChar k z * absPow k (((l : ℂ) - 1) / 2)) := fun x hx => by
    rw [MonoidHom.mul_apply, isUnram_unrChar k z x hx, isUnram_absPow k _ x hx, mul_one]
  have hu : ∀ s : ℂ, IsUnram (unrChar k z * absPow k (((l : ℂ) - 1) / 2) * absPow k s) :=
    fun s x hx => by rw [MonoidHom.mul_apply, hψu x hx, isUnram_absPow k s x hx, mul_one]
  refine ⟨List.ofFn fun i : Fin (l * 1) => (unrChar k z * absPow k (((l : ℂ) - 1) / 2) *
    absPow k (((i : ℕ) : ℂ) - (((l * 1 : ℕ) : ℂ) - 1) / 2)) ϖ, ?_⟩
  intro h0
  have h1 : wordMult (detRep (Fin (l * 1)) (unrChar k z * absPow k (((l : ℂ) - 1) / 2)))
      (List.ofFn fun i : Fin (l * 1) => (unrChar k z * absPow k (((l : ℂ) - 1) / 2) *
        absPow k (((i : ℕ) : ℂ) - (((l * 1 : ℕ) : ℂ) - 1) / 2)) ϖ) = 0 :=
    (wordMult_congr e _).trans h0
  rw [wordMult_detRep, if_pos] at h1
  · exact one_ne_zero h1
  refine ⟨List.length_ofFn, fun i hi => ?_⟩
  have hg : (List.ofFn fun i : Fin (l * 1) => (unrChar k z * absPow k (((l : ℂ) - 1) / 2) *
      absPow k (((i : ℕ) : ℂ) - (((l * 1 : ℕ) : ℂ) - 1) / 2)) ϖ).getD i 1 =
      (unrChar k z * absPow k (((l : ℂ) - 1) / 2) *
        absPow k ((i : ℂ) - (((l * 1 : ℕ) : ℂ) - 1) / 2)) ϖ := by
    have hi' : i < l := by simpa using hi
    simp [hi']
  rw [hg]
  exact (eq_unrChar (hu _) hϖ).symm

end GlobalTheory.LocGL.UnramSupport

namespace GlobalTheory.LocGL.UnramSupport

open ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL.Exponents GlobalTheory.SmGL.Segment

theorem fixed_iwahori_ne_bot : GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing →
    GlobalTheory.Published.BernsteinZelevinskyFiniteness →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → (∀ s : Multiset (IrrGL k), HasSupport π s → ∀ y ∈ s, y.IsUnramChar) →
      fixed π (iwahori k (Fin n)) ≠ ⊥ := by
  intro hG hZ hB k _ _ _ _ n V _ _ π hs hi hsupp
  classical
  obtain ⟨Z, Ψ, hS, hΨ, hX⟩ := hZ k
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  let _ : LinearOrder ℂˣ := modArgOrder
  have hword : ∃ w, wordMult π w ≠ 0 := by
    by_contra hw0
    push Not at hw0
    set U : Set (Segment k) := {Δ | ∃ (z : ℂˣ) (l : ℕ) (hl : 0 < l),
      Δ = Segment.ofChar (unrChar k z) (isSmoothChar_of_isUnram (isUnram_unrChar k z)) l hl} with hUdef
    have hfirst : ∀ Δ ∈ U, ∃ (z : ℂˣ) (l : ℕ), 0 < l ∧
        Δ.first = IrrGL.ofChar (unrChar k z) (isSmoothChar_of_isUnram (isUnram_unrChar k z)) ∧
        Δ.len = l ∧ ∀ w, wordMult (Z Δ).rep.ρ w =
          (({segWord (absPow k 1 ϖ) z l} : Multiset (List ℂˣ)).count w : ℕ∞) := by
      intro Δ hΔ
      rcases wordMult_segment hϖ hS Δ with ⟨z, l, hl, rfl, h⟩ | h
      · exact ⟨z, l, hl, rfl, rfl, h⟩
      · obtain ⟨z, l, hl, rfl⟩ := hΔ
        obtain ⟨w, hw⟩ := exists_wordMult_segment_ne hS hϖ z hl
        exact absurd (h w) hw
    have hzero : ∀ Δ ∉ U, ∀ w, wordMult (Z Δ).rep.ρ w = 0 := by
      intro Δ hΔ
      rcases wordMult_segment hϖ hS Δ with ⟨z, l, hl, rfl, -⟩ | h
      · exact absurd ⟨z, l, hl, rfl⟩ hΔ
      · exact h
    choose! zf lf hlpos hfst hlen hcount using hfirst
    let ℓ : Segment k → List ℂˣ := fun Δ => segWord (absPow k 1 ϖ) (zf Δ) (lf Δ)
    let φ : Segment k → ShuffleAlgebra ℚ ℂˣ := fun Δ => if Δ ∈ U then ShuffleAlgebra.word ℚ (ℓ Δ) else 0
    have hinj : Set.InjOn ℓ U := by
      intro Δ hΔ Δ' hΔ' h
      obtain ⟨h1, h2⟩ := segWord_inj (hlpos Δ hΔ) h
      exact Segment.ext_first (by rw [hfst Δ hΔ, hfst Δ' hΔ', h1]) (by rw [hlen Δ hΔ, hlen Δ' hΔ', h2])
    have hUl : ∀ Δ ∈ U, IsLyndon (ℓ Δ) ∧ φ Δ = ShuffleAlgebra.word ℚ (ℓ Δ) := fun Δ hΔ =>
      ⟨isLyndon_segWord (norm_absPow_one_lt hϖ) _ (hlpos Δ hΔ), if_pos hΔ⟩
    have h0 : ∀ Δ ∉ U, φ Δ = 0 := fun Δ hΔ => if_neg hΔ
    have hXr : ∀ Δ, Realised Ψ (MvPolynomial.X Δ) (φ Δ) := by
      intro Δ
      have hfl : HasFiniteLength (Z Δ).rep.ρ := hasFiniteLength_of_isIrreducible (Z Δ).rep.irr
      refine ⟨Δ.len * Δ.d, (Z Δ).rep.V, _, _, (Z Δ).rep.ρ, hfl, (Z Δ).rep.smooth, ?_, ?_⟩
      · rw [clsGL_irr (Z Δ).rep hfl, (Z Δ).cl_rep, hX Δ]
      · by_cases hΔ : Δ ∈ U
        · refine ⟨{ℓ Δ}, hcount Δ hΔ, ?_⟩
          rw [Multiset.map_singleton, Multiset.sum_singleton]
          exact (if_pos hΔ).symm
        · refine ⟨0, fun w => by rw [hzero Δ hΔ w]; simp, ?_⟩
          rw [Multiset.map_zero, Multiset.sum_zero]
          exact (if_neg hΔ).symm
    have H : ∀ m : Segment k →₀ ℕ, 0 ≤ Ψ.symm (MvPolynomial.monomial m 1) ∧ ∃ s : Multiset (List ℂˣ),
        (∀ w, ((Ψ.symm (MvPolynomial.monomial m 1)).sum fun x a =>
          (a.toNat : ℕ∞) * wordMult x.2.rep.ρ w) = (s.count w : ℕ∞)) ∧
        (s.map (ShuffleAlgebra.word ℚ)).sum = m.prod fun Δ e => φ Δ ^ e := fun m =>
      (Realised.monomial (hG k).1 (hG k).2 hΨ hXr m).effective
    have hy : ∀ w, wordMult (IrrGL.of π hs hi).2.rep.ρ w = 0 := fun w =>
      (wordMult_congr (IrrGL.equivOf π hs hi) w).symm.trans (hw0 w)
    obtain ⟨m, ⟨Δ, hΔm, hΔU⟩, hm⟩ := exists_monomial_of_count_zero (IrrGL k) (Segment k) ℂˣ Ψ
      (fun x w => wordMult x.2.rep.ρ w) U ℓ φ hinj hUl h0 H _ hy
    have hsp := hasSupport_of_monomial hS hΨ hX hs hi m hm
    have hfm : Δ.first ∈ ∑ Δ ∈ m.support, m Δ • Δ.ms := by
      refine Multiset.mem_sum.2 ⟨Δ, hΔm, Multiset.mem_nsmul.2 ⟨Finsupp.mem_support_iff.1 hΔm, ?_⟩⟩
      rw [Segment.mem_ms, Segment.mem_carrier]
      exact ⟨0, Δ.len_pos, by simp⟩
    obtain ⟨μ, hμ, hμΔ⟩ := hsupp _ hsp _ hfm
    apply hΔU
    refine ⟨μ ϖ, Δ.len, Δ.len_pos, Segment.ext_first ?_ rfl⟩
    rw [hμΔ]
    exact IrrGL.ofChar_inj.2 (eq_unrChar hμ hϖ)
  intro hbot
  obtain ⟨w, hw⟩ := hword
  have hadm : IsAdmissible π := (hB k).1 (Fin n) V π hs hi
  have hbij := GlobalTheory.Published.BorelCasselman_holds k (Fin n) V π hadm
  have hsub : ∀ v : fixed (jacBU π) (torusO k (Fin n)), v = 0 := by
    intro v
    obtain ⟨u, rfl⟩ := hbij.2 v
    have hu : u = 0 := by
      have : (u : V) ∈ (⊥ : Submodule ℂ V) := by rw [← hbot]; exact u.2
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    rw [hu, map_zero]
  unfold wordMult at hw
  split_ifs at hw with hlen
  · have hθ : ∀ t ∈ torusO k (Fin n), torusChar (fun i : Fin n => unrChar k (w.getD i 1)) t = 1 := by
      intro t ht
      rw [torusChar_apply]
      exact Finset.prod_eq_one fun i _ =>
        isUnram_unrChar k _ (t i) ((show ∀ i, valuation k (t i : k) = 1 from ht) i)
    rw [UnramFixed.jhMult_jacB_eq_expMult k n V π hs _ hθ] at hw
    unfold expMult at hw
    obtain ⟨S, f, hf⟩ := GlobalTheory.JHMult.jhMult_ne_zero_iff.1 hw
    obtain ⟨v, hv⟩ := hf 1
    have hv0 : v = 0 := Subtype.ext (hsub _)
    rw [hv0, map_zero] at hv
    exact zero_ne_one hv
  · exact hw rfl

end GlobalTheory.LocGL.UnramSupport
