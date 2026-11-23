import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_boundary

section HomogIdeal

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem eval_mConeMap {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : K → Ω) (f : MRing J) :
    MvPolynomial.eval c (mConeMap y f) = MvPolynomial.aeval (fun p : Σ k, J k => y p * c p.1) f := by
  have h : (MvPolynomial.eval c).comp (mConeMap y).toRingHom =
      (MvPolynomial.aeval (fun p : Σ k, J k => y p * c p.1) : MRing J →ₐ[ℤ] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro p; simp [mConeMap]
  exact congrArg (fun φ : MRing J →+* Ω => φ f) h

theorem aeval_eq_eval_map (w : (Σ k, J k) → ℂ) (f : MRing J) :
    MvPolynomial.aeval w f = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]

theorem aeval_eq_zero_of_mem {w : (Σ k, J k) → ℂ} {f : MRing J} (hf : f ∈ mCoordIdeal w) :
    MvPolynomial.aeval w f = 0 := by
  have hf' : mConeMap w f = 0 := hf
  have h := eval_mConeMap w (fun _ => 1) f
  rw [hf', map_zero] at h
  simpa using h.symm

theorem aeval_ratio_eq_zero {Ω : Type} [Field Ω] {x : (Σ k, J k) → Ω} (c : (k : K) → J k) {f : MRing J}
    (hf : f ∈ mCoordIdeal x) : MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) f = 0 := by
  have hf' : mConeMap x f = 0 := hf
  have h := eval_mConeMap x (fun k => (x ⟨k, c k⟩)⁻¹) f
  rw [hf', map_zero] at h
  simpa [div_eq_mul_inv] using h.symm

theorem eq_zero_of_eval_torus {F : MvPolynomial K ℂ}
    (h : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → MvPolynomial.eval c F = 0) : F = 0 := by
  have h2 : F * ∏ k, (MvPolynomial.X k : MvPolynomial K ℂ) = 0 := by
    apply MvPolynomial.funext
    intro c
    rw [map_mul, map_zero, map_prod]
    by_cases hc : ∀ k, c k ≠ 0
    · rw [h c hc, zero_mul]
    · push_neg at hc
      obtain ⟨k, hk⟩ := hc
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk]), mul_zero]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd h3 (Finset.prod_ne_zero_iff.2 fun k _ => MvPolynomial.X_ne_zero k)

theorem le_mCoordIdeal_of_torus {bd : Ideal (MRing J)} {z : (Σ k, J k) → ℂ}
    (h : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ f ∈ bd, MvPolynomial.aeval (fun p : Σ k, J k => z p * c p.1) f = 0) :
    bd ≤ mCoordIdeal z := by
  intro f hf
  show mConeMap z f = 0
  refine eq_zero_of_eval_torus fun c hc => ?_
  rw [eval_mConeMap]
  exact h c hc f hf

theorem exists_algHom_ker_eq {S : Type} [CommRing S] [Algebra ℚ S] [Algebra.FiniteType ℚ S] (m : Ideal S)
    [m.IsMaximal] : ∃ ev : S →ₐ[ℚ] ℂ, RingHom.ker ev = m := by
  let _ : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℚ (S ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m) (Ideal.Quotient.mkₐ_surjective ℚ m)
  haveI : Module.Finite ℚ (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (S ⧸ m)
  haveI : Algebra.IsAlgebraic ℚ (S ⧸ m) := Algebra.IsAlgebraic.of_finite ℚ _
  let φ : (S ⧸ m) →ₐ[ℚ] ℂ := IsAlgClosed.lift
  refine ⟨φ.comp (Ideal.Quotient.mkₐ ℚ m), ?_⟩
  ext s
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_eq_zero_iff φ φ.toRingHom.injective,
    Ideal.Quotient.eq_zero_iff_mem]

theorem cond_of_bd {Ω : Type} [Field Ω] [CharZero Ω] {x : (Σ k, J k) → Ω} {bd : Ideal (MRing J)}
    {c : (k : K) → J k} (hc : ∀ k, x ⟨k, c k⟩ ≠ 0) {S : Subalgebra ℚ Ω} [Algebra.FiniteType ℚ S]
    (hρ : ∀ p : Σ k, J k, x p / x ⟨p.1, c p.1⟩ ∈ S) (q : Ideal S) (hq : q.IsPrime)
    (hbd : ∀ g ∈ bd, ∀ s : S, (s : Ω) = MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) g → s ∈ q) :
    ∀ g ∈ (⨅ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, mCoordIdeal z), ∀ s : S,
      (s : Ω) = MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) g → s ∈ q := by
  intro g hg s hs
  haveI : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := ℚ)
  have hjac : q.jacobson = q := isJacobsonRing_iff_prime_eq.mp inferInstance q hq
  rw [← hjac]
  refine Ideal.mem_sInf.2 ?_
  rintro m ⟨hqm, hm⟩
  obtain ⟨ev, hev⟩ := exists_algHom_ker_eq m
  let ρS : (Σ k, J k) → S := fun p => ⟨_, hρ p⟩
  let w : (Σ k, J k) → ℂ := fun p => ev (ρS p)
  have hval : ∀ f : MRing J, ev (MvPolynomial.aeval ρS f) = MvPolynomial.aeval w f := fun f => by
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, ← AlgHom.coe_toRingHom, MvPolynomial.eval₂_comp_left]
    congr 1 <;> first | rfl | exact RingHom.ext_int _ _
  have hsub : ∀ f : MRing J, ((MvPolynomial.aeval ρS f : S) : Ω) =
      MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) f := fun f => by
    show S.val.toRingHom (MvPolynomial.aeval ρS f) = _
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
    congr 1 <;> first | rfl | exact RingHom.ext_int _ _
  have hwP : w ∈ mcPts (mCoordIdeal x) := by
    refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
    · have h1 : ρS ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
      simp only [w, h1, map_one]
      exact one_ne_zero
    · rw [← aeval_eq_eval_map, ← hval]
      have h1 : MvPolynomial.aeval ρS f = 0 := Subtype.ext (by rw [hsub]; exact aeval_ratio_eq_zero c hf)
      rw [h1, map_zero]
  have hwbd : w ∈ mcPts bd := by
    refine ⟨hwP.1, fun f hf => ?_⟩
    rw [← aeval_eq_eval_map, ← hval, ← RingHom.mem_ker, hev]
    exact hqm (hbd f hf _ (hsub f))
  have hg' : g ∈ mCoordIdeal w := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hg w) ⟨hwP, hwbd⟩
  have hs' : s = MvPolynomial.aeval ρS g := Subtype.ext (hs.trans (hsub g).symm)
  rw [← hev, RingHom.mem_ker, hs', hval]
  exact aeval_eq_zero_of_mem hg'

end HomogIdeal

theorem exists_homogIdeal {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    [CharZero Ω] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)) (hs : Cmp.IsSncModel x n bd)
    (ha : IsArithVar (mCoordIdeal x) (n + 1))
    (ht : ∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) :
    ∃ I : Ideal (MRing J), IsMultiHomogIdeal I ∧ ¬ I ≤ mCoordIdeal x ∧ Cmp.IsSncModel x n I ∧
      mcPts (mCoordIdeal x) ∩ mcPts I = mcPts (mCoordIdeal x) ∩ mcPts bd := by
  classical
  set I : Ideal (MRing J) := ⨅ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, mCoordIdeal z with hIdef
  have hle : bd ≤ I := by
    intro f hf
    refine (Submodule.mem_iInf _).2 fun z => (Submodule.mem_iInf _).2 fun hz => ?_
    refine le_mCoordIdeal_of_torus (fun c hc g hg => ?_) hf
    have e : (fun p : Σ k, J k => z p * c p.1) = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z :=
      funext fun p => mul_comm _ _
    rw [e, aeval_eq_eval_map]
    exact (ht z hz c hc).2.2 g hg
  have hhom : IsMultiHomogIdeal I := by
    refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff I).mp ?_
    intro f hf b
    refine (Submodule.mem_iInf _).2 fun z => (Submodule.mem_iInf _).2 fun hz => ?_
    exact GroundTheory.Heights₂.Heights.CoordinateConeArithVar.component_mem z f
      ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf z) hz) b

  have hrel := ha.2.1.2.2
  have hc0 : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap x (MvPolynomial.X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  choose c hc using hc0
  refine ⟨I, hhom, ?_, ?_, ?_⟩
  · intro hIP
    obtain ⟨m, f, a, -, -, hsum, hl⟩ := hs c hc
    obtain ⟨l, hfl⟩ : ∃ l, f l ≠ 0 := by
      by_contra h
      push_neg at h
      rw [Finset.sum_eq_zero fun l _ => by rw [h l, mul_zero]] at hsum
      exact zero_ne_one hsum
    obtain ⟨-, z, n', -, hli, -, hq⟩ := hl l hfl _ rfl
    have hbot := hq ⊥ Ideal.isPrime_bot
    have hR : ¬ ∃ i : Fin n, (i : ℕ) < n' ∧ z i ∈ (⊥ : Ideal _) := by
      rintro ⟨i, -, hzi⟩
      rw [Ideal.mem_bot] at hzi
      exact hli.ne_zero i (by rw [hzi, map_zero])
    rw [← hbot] at hR
    push_neg at hR
    obtain ⟨g, hg, s, hs1, hs2⟩ := hR
    have hs3 : (s : Ω) ≠ 0 := fun h0 => hs2 ((Ideal.mem_bot).2 (Subtype.ext h0))
    rw [hs1] at hs3
    exact hs3 (aeval_ratio_eq_zero c (hIP (hle hg)))
  · intro c' hc'
    obtain ⟨m, f, a, hf, ha', hsum, hl⟩ := hs c' hc'
    refine ⟨m, f, a, hf, ha', hsum, fun l hfl S hS => ?_⟩
    obtain ⟨hsm, z, n', hn', hli, hsp, hq⟩ := hl l hfl S hS
    refine ⟨hsm, z, n', hn', hli, hsp, fun q hqp => ?_⟩
    rw [← hq q hqp]
    constructor
    · intro h g hg s hs'
      exact h g (hle hg) s hs'
    · intro h
      have hfin : (insert (f l)⁻¹ (Set.range fun p : Σ k, J k => x p / x ⟨p.1, c' p.1⟩)).Finite :=
        (Set.finite_range _).insert _
      haveI : Algebra.FiniteType ℚ S := by
        rw [← Subalgebra.fg_iff_finiteType, hS, ← hfin.coe_toFinset]
        exact Subalgebra.fg_adjoin_finset _
      have hρ : ∀ p : Σ k, J k, x p / x ⟨p.1, c' p.1⟩ ∈ S := fun p => by
        rw [hS]
        exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_range_self p))
      exact cond_of_bd hc' hρ q hqp h
  · ext z
    constructor
    · rintro ⟨hzP, hzI⟩
      exact ⟨hzP, hzI.1, fun f hf => hzI.2 f (hle hf)⟩
    · rintro ⟨hzP, hzb⟩
      refine ⟨hzP, hzP.1, fun f hf => ?_⟩
      rw [← aeval_eq_eval_map]
      exact aeval_eq_zero_of_mem ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf z) ⟨hzP, hzb⟩)

end PositivityTheory.Xgp.c_bm_exists_boundary
