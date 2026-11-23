import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcReduced
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedGraphHorizontal
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalCycle

section Krull

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem eq_of_le_of_lt {Γ W Q : Ideal A} [hΓ : Γ.IsPrime] {x : A} (hW : W ∈ (Γ ⊔ Ideal.span {x}).minimalPrimes)
    [hQ : Q.IsPrime] (hΓQ : Γ ≤ Q) (hQW : Q < W) : Q = Γ := by
  have hWp : W.IsPrime := hW.1.1
  let f := Ideal.Quotient.mk Γ
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hΓW : Γ ≤ W := hΓQ.trans hQW.le
  have hWf : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rwa [Ideal.mk_ker])
  have hQf : (Q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rwa [Ideal.mk_ker])
  have h1 : (W.map f).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have h_lt : Q.map f < W.map f := (Ideal.map_mono hQW.le).lt_of_not_ge fun e => hQW.not_ge (by
    simpa only [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot, f, Ideal.mk_ker,
      sup_eq_left.mpr hΓQ, sup_eq_left.mpr hΓW] using Ideal.comap_mono (f := f) e)
  have : (W.map f).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have h0 := (Ideal.height_strict_mono_of_isPrime_of_isPrime h_lt).trans_le h1
  rw [Order.lt_one_iff, Ideal.height_eq_zero_iff] at h0
  have hle : Q.map f ≤ ⊥ := h0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
  refine le_antisymm (fun y hy => ?_) hΓQ
  have hy0 : f y = 0 := (Submodule.mem_bot _).mp (hle (Ideal.mem_map_of_mem f hy))
  exact Ideal.Quotient.eq_zero_iff_mem.mp hy0

theorem mem_minimalPrimes_of_le {Γ W B : Ideal A} [Γ.IsPrime] {x y : A}
    (hW : W ∈ (Γ ⊔ Ideal.span {x}).minimalPrimes) (hΓB : Γ ≤ B) (hBW : B ≤ W) (hy : y ∈ B) (hyΓ : y ∉ Γ) :
    W ∈ B.minimalPrimes := by
  refine ⟨⟨hW.1.1, hBW⟩, fun Q hQ hQW => ?_⟩
  by_contra hne
  have := hQ.1
  have e := eq_of_le_of_lt hW (hΓB.trans hQ.2) (lt_of_le_of_ne hQW fun e => hne e.ge)
  apply hyΓ
  rw [← e]
  exact hQ.2 hy

end Krull

section Length

variable {A : Type*} [CommRing A]

theorem multAt_eq_toNat {K' : Type} [Fintype K'] {ι : K' → Type} [∀ k, Fintype (ι k)]
    (J W : Ideal (MRing ι)) [hW : W.IsPrime] :
    multAt J W = (ReciprocityTheory.ChartRestriction.G.AI.locLen (MRing ι ⧸ J) ⟨W, hW⟩).toNat := by
  simp [multAt, hW, ReciprocityTheory.ChartRestriction.G.AI.locLen]

theorem locLen_eq_zero {J W : Ideal A} [hW : W.IsPrime] {s : A} (hs : s ∈ J) (hsW : s ∉ W) :
    ReciprocityTheory.ChartRestriction.G.AI.locLen (A ⧸ J) ⟨W, hW⟩ = 0 := by
  have hz : ∀ z : LocalizedModule W.primeCompl (A ⧸ J), z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective J m
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
      refine ⟨⟨s, hsW⟩, ?_⟩
      rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact J.mul_mem_right r hs
  have : Subsingleton (LocalizedModule W.primeCompl (A ⧸ J)) := ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact Module.length_eq_zero_iff.mpr inferInstance

end Length

section Divisor

variable {K' : Type} [Fintype K'] {ι : K' → Type} [∀ k, Fintype (ι k)]

theorem divCycle_of_mem {V W : Ideal (MRing ι)} {f : MRing ι} (hW : W ∈ divSupp V f) :
    divCycle V f W = multAt (V ⊔ Ideal.span {f}) W := by
  classical
  simp [divCycle, Finsupp.ofSupportFinite_coe, hW]

theorem divCycle_of_not_mem {V W : Ideal (MRing ι)} {f : MRing ι} (hW : W ∉ divSupp V f) :
    divCycle V f W = 0 := by
  classical
  simp [divCycle, Finsupp.ofSupportFinite_coe, hW]

end Divisor

section Graph

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
  [DecidableEq T]

theorem dualIdeal_isPrime (b' : Module.Basis T ℤ (dualLattice F')) : (dualIdeal b').IsPrime := by
  unfold dualIdeal mCoordIdeal
  exact RingHom.ker_isPrime _

theorem C_mul_X_not_mem_dualIdeal (b' : Module.Basis T ℤ (dualLattice F')) {c : ℤ} (hc : c ≠ 0) (t : T) :
    (C c * X ⟨(), t⟩ : MRing (dualBlocks T)) ∉ dualIdeal b' := by
  intro h
  have h0 : mConeMap (dualLatticeCoord b') (C c * X ⟨(), t⟩ : MRing (dualBlocks T)) = 0 := h
  simp only [mConeMap, map_mul, aeval_C, aeval_X, eq_intCast, map_intCast] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact hc (by exact_mod_cast h1)
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · rw [C_eq_zero, DualArithmeticVariety.dualLatticeCoord_eq] at h2
      exact DualArithmeticVariety.evalForm_ne_zero (fun e => b'.ne_zero t (Subtype.ext e)) h2
    · exact X_ne_zero _ h2

theorem stackedGraph_isPrime (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) :
    (stackedGraph b' a).IsPrime := by
  have := dualIdeal_isPrime b'
  unfold stackedGraph graphIdeal
  exact RingHom.ker_isPrime _

theorem first_not_mem (b' : Module.Basis T ℤ (dualLattice F')) {a : T → ℤ} {t : T} (ha : a t ≠ 0) :
    C (a t) * graphFirst t ∉ stackedGraph b' a :=
  TopDualSimpleStacked.first_not_mem (dualIdeal_isPrime b') a (C_mul_X_not_mem_dualIdeal b' ha t)

theorem second_not_mem (b' : Module.Basis T ℤ (dualLattice F')) {a : T → ℤ} {t : T} (ha : a t ≠ 0) :
    graphSecond t ∉ stackedGraph b' a :=
  TopDualSimpleStacked.second_not_mem (dualIdeal_isPrime b') a (C_mul_X_not_mem_dualIdeal b' ha t)

theorem minor_mem (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (s t : T) :
    graphSecond s * (C (a t) * graphFirst t) - graphSecond t * (C (a s) * graphFirst s) ∈ stackedGraph b' a :=
  TopDualSimpleStacked.minor_mem _ a s t

theorem mul_mem_first (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (l t : T) :
    (C (a l) * graphFirst l) * graphSecond t ∈ stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst t} :=
  StackedGraphHorizontal.mul_mem_sup_first _ a l t

theorem mul_mem_second (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (l t : T) :
    graphSecond l * (C (a t) * graphFirst t) ∈ stackedGraph b' a ⊔ Ideal.span {graphSecond t} :=
  StackedGraphHorizontal.mul_mem_sup_second _ a l t

theorem first_mem_base (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (t : T) :
    C (a t) * graphFirst t ∈ stackedBase b' a :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨t, rfl⟩)

end Graph

end StackedExceptionalCycle

open StackedExceptionalCycle StackedGraphHorizontal in

theorem DualStackedExcCycle.proof (hR : DualStackedExcReduced.Statement) : DualStackedExcCycle.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab
  obtain ⟨E, hE, huniq, hmult⟩ := hR K i F F' T b b' a hi hlt hcov hab
  have ha : ∀ t, a t ≠ 0 := by
    intro t h
    apply b.ne_zero t
    apply Subtype.ext
    rw [hab t, h, zero_smul]
    rfl
  have hΓp : (stackedGraph b' a).IsPrime := stackedGraph_isPrime b' a
  have hEp : E.IsPrime := hE.1.1.1
  have hBE : stackedBase b' a ≤ E := hE.1.1.2
  have hΓB : stackedGraph b' a ≤ stackedBase b' a := le_sup_left
  have hnh : ¬ IsHorizontal E := by
    intro hh
    obtain ⟨s, hs⟩ := hE.2 (Sum.inl ())
    rcases hEp.mem_or_mem (hBE (first_mem_base b' a s)) with h2 | h2
    · have h3 : a s ∈ E.comap (C : ℤ →+* MRing (stackedBlocks T)) := h2
      rw [hh] at h3
      exact ha s h3
    · exact hs h2
  have hexc : ∀ (W : Ideal (MRing (stackedBlocks T))) (x : MRing (stackedBlocks T)),
      W ∈ divSupp (stackedGraph b' a) x → stackedBase b' a ≤ W → W = E := by
    intro W x hW hBW
    obtain ⟨j, -⟩ := hW.2 (Sum.inl ())
    exact huniq W ⟨mem_minimalPrimes_of_le hW.1 hΓB hBW (first_mem_base b' a j) (first_not_mem b' (ha j)), hW.2⟩
  refine ⟨E, hE, hnh, fun t => ⟨?_, fun W _ hWE => ?_⟩⟩
  ·
    have hu' : ∃ u : T, graphSecond u ∉ E := hE.2 (Sum.inr ())
    obtain ⟨u, hgu⟩ := hu'
    have hEu : E ∈ (stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u}).minimalPrimes := by
      refine ⟨⟨hEp, sup_le (hΓB.trans hBE) ((Ideal.span_singleton_le_iff_mem _).mpr
        (hBE (first_mem_base b' a u)))⟩, fun Q hQ hQE => ?_⟩
      refine hE.1.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) (Ideal.span_le.mpr ?_)⟩ hQE
      rintro _ ⟨s, rfl⟩
      exact (hQ.1.mem_or_mem (hQ.2 (mul_mem_first b' a s u))).resolve_right fun h => hgu (hQE h)
    have hsupp : ∀ x ∈ E, x ∉ stackedGraph b' a → E ∈ divSupp (stackedGraph b' a) x := fun x hx hxΓ =>
      ⟨mem_minimalPrimes_of_le hEu le_sup_left
        (sup_le (hΓB.trans hBE) ((Ideal.span_singleton_le_iff_mem _).mpr hx))
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)) hxΓ, hE.2⟩

    have hcolon : ∀ x ∈ stackedBase b' a,
        graphSecond u * x ∈ stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u} := by
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      rw [mul_add]
      refine Ideal.add_mem _ (Ideal.mem_sup_left ((stackedGraph b' a).mul_mem_left _ hy)) ?_
      clear hx
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨s, rfl⟩ := hx
        rw [mul_comm (graphSecond u)]
        exact mul_mem_first b' a s u
      | zero => rw [mul_zero]; exact Ideal.zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
      | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ r hx
    have hLu : ReciprocityTheory.ChartRestriction.G.AI.locLen (MRing (stackedBlocks T) ⧸
        (stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u})) ⟨E, hEp⟩ = 1 := by
      have e1 : multAt (stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u}) E = 1 := by
        rw [multAt_eq_of_mul_mem (sup_le hΓB ((Ideal.span_singleton_le_iff_mem _).mpr (first_mem_base b' a u)))
          hgu hcolon, hmult]
      rw [multAt_eq_toNat] at e1
      rw [← ENat.natCast_toNat (ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hEu), e1]
      rfl

    have hLg : ReciprocityTheory.ChartRestriction.G.AI.locLen (MRing (stackedBlocks T) ⧸
        (stackedGraph b' a ⊔ Ideal.span {graphSecond t})) ⟨E, hEp⟩ = (divCycle (stackedGraph b' a) (graphSecond t) E : ℕ∞) := by
      by_cases hgt : graphSecond (T := T) t ∈ E
      · have hs := hsupp _ hgt (second_not_mem b' (ha t))
        rw [divCycle_of_mem hs, multAt_eq_toNat, ENat.natCast_toNat (ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hs.1)]
      · rw [divCycle_of_not_mem (fun h => hgt (h.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))),
          locLen_eq_zero (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) hgt]
        rfl

    have hle : stackedGraph b' a ⊔ Ideal.span {graphSecond t * (C (a u) * graphFirst u)} ≤
        stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst t} := by
      refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      rw [mul_comm (graphSecond t)]
      exact mul_mem_first b' a u t
    have hsg : graphSecond u * (C (a t) * graphFirst t) ∈
        stackedGraph b' a ⊔ Ideal.span {graphSecond t * (C (a u) * graphFirst u)} := by
      have e : graphSecond u * (C (a t) * graphFirst t) =
          (graphSecond u * (C (a t) * graphFirst t) - graphSecond t * (C (a u) * graphFirst u)) +
            graphSecond t * (C (a u) * graphFirst u) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (minor_mem b' a u t))
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have e2 : multAt (stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst t}) E =
        multAt (stackedGraph b' a ⊔ Ideal.span {graphSecond t * (C (a u) * graphFirst u)}) E :=
      (multAt_eq_of_mul_mem hle hgu fun x hx =>
        mul_mem_of_mem_sup hsg x ((sup_le_sup_right le_sup_left _ :
          stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst t} ≤ _) hx)).symm
    have hmul := ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_mul hΓp (second_not_mem b' (ha t)) (C (a u) * graphFirst u) ⟨E, hEp⟩
    rw [hLu, hLg] at hmul
    have hft : C (a t) * graphFirst t ∈ E := hBE (first_mem_base b' a t)
    rw [divCycle_of_mem (hsupp _ hft (first_not_mem b' (ha t))), e2, multAt_eq_toNat, hmul]
    rw [← Nat.cast_one (R := ℕ∞), ← Nat.cast_add, ENat.toNat_coe]
    push_cast
    ring
  ·
    have key : ∀ x, W ∈ divSupp (stackedGraph b' a) x →
        ∃ s s' : MRing (stackedBlocks T), s ∉ W ∧ s' ∉ W ∧
          s * (C (a t) * graphFirst t) ∈ stackedGraph b' a ⊔ Ideal.span {graphSecond t} ∧
          s' * graphSecond t ∈ stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst t} := by
      intro x hW
      have hWp : W.IsPrime := hW.1.1.1
      have hΓW : stackedGraph b' a ≤ W := le_sup_left.trans hW.1.1.2
      have hl' : ∃ l : T, graphSecond l ∉ W := hW.2 (Sum.inr ())
      obtain ⟨l, hgl⟩ := hl'
      have hj : ∃ j, C (a j) * graphFirst j ∉ W := by
        by_contra hno
        push_neg at hno
        refine hWE (hexc W x hW (sup_le hΓW (Ideal.span_le.mpr ?_)))
        rintro _ ⟨s, rfl⟩
        exact hno s
      obtain ⟨j, hj⟩ := hj
      have hfl : C (a l) * graphFirst l ∉ W := by
        intro h
        have h2 : graphSecond l * (C (a j) * graphFirst j) ∈ W := by
          have := W.add_mem (hΓW (minor_mem b' a l j)) (W.mul_mem_left (graphSecond j) h)
          rwa [sub_add_cancel] at this
        rcases hWp.mem_or_mem h2 with h3 | h3
        · exact hgl h3
        · exact hj h3
      exact ⟨graphSecond l, C (a l) * graphFirst l, hgl, hfl, mul_mem_second b' a l t, mul_mem_first b' a l t⟩
    by_cases h1 : W ∈ divSupp (stackedGraph b' a) (C (a t) * graphFirst t)
    · obtain ⟨s, s', hs, hs', hsg, hsf⟩ := key _ h1
      have h2 : W ∈ divSupp (stackedGraph b' a) (graphSecond t) :=
        ⟨mem_minimalPrimes_of_mul_mem hs' hs hsf hsg h1.1, h1.2⟩
      rw [divCycle_of_mem h1, divCycle_of_mem h2,
        multAt_eq_of_mul_mem le_sup_left hs' (mul_mem_of_mem_sup hsf),
        multAt_eq_of_mul_mem (le_sup_left : stackedGraph b' a ⊔ Ideal.span {graphSecond t} ≤ _) hs
          (mul_mem_of_mem_sup hsg), sup_right_comm]
    · by_cases h2 : W ∈ divSupp (stackedGraph b' a) (graphSecond t)
      · obtain ⟨s, s', hs, hs', hsg, hsf⟩ := key _ h2
        exact absurd ⟨mem_minimalPrimes_of_mul_mem hs hs' hsg hsf h2.1, h2.2⟩ h1
      · rw [divCycle_of_not_mem h1, divCycle_of_not_mem h2]

end

end GroundTheory.Heights₂.Heights
