import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsHolomorphicChartAtPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueLocallyRegularFunction
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisAlt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace PositivityTheory.Xgn.NoPoleDisc

open PositivityTheory.Xgn.HolomorphicChart

theorem exists_dvd {P B : Type} [CommRing P] [IsDomain P] [CommRing B] [IsDomain B] [Algebra P B]
    [Algebra.QuasiFinite P B] {c : B} (hc : c ≠ 0) : ∃ q : P, q ≠ 0 ∧ c ∣ algebraMap P B q := by
  by_contra h
  push Not at h
  obtain ⟨Q, hQ, h1, h2⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {c})
    ((nonZeroDivisors P).map (algebraMap P B)) (by
      rw [Set.disjoint_left]
      rintro _ hx ⟨q, hq, rfl⟩
      exact h q (nonZeroDivisors.ne_zero hq) (Ideal.mem_span_singleton.1 hx))
  have h3 : Q.under P = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    by_contra h0
    exact Set.disjoint_left.1 h2 hq ⟨q, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩
  have h4 : (⊥ : Ideal B) = Q := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := P) ⊥ Q bot_le
    (le_antisymm (Ideal.comap_mono bot_le) (h3 ▸ bot_le))
  exact hc (by simpa [← h4] using h1)

theorem exists_point {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A] (σ : K →+* ℂ)
    (p : Ideal A) [hp : p.IsPrime] {b : A} (hb : b ∉ p) :
    ∃ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ ∧ (∀ a ∈ p, ψ a = 0) ∧ ψ b ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.DYhc4.main σ p hb

theorem der_zero_etale {K B : Type} [Field K] [CommRing B] [Algebra K B] {d : ℕ} [Algebra (MvPolynomial (Fin d) K) B]
    [IsScalarTower K (MvPolynomial (Fin d) K) B] [Algebra.FormallyUnramified (MvPolynomial (Fin d) K) B]
    (ψ : B →+* ℂ) (δ : B →+ ℂ) (hmul : ∀ a b, δ (a * b) = ψ a * δ b + ψ b * δ a)
    (hK : ∀ k, δ (algebraMap K B k) = 0)
    (hz : ∀ i, δ (algebraMap (MvPolynomial (Fin d) K) B (MvPolynomial.X i)) = 0) (a : B) : δ a = 0 := by
  have hP : ∀ q : MvPolynomial (Fin d) K, δ (algebraMap _ B q) = 0 := fun q => by
    induction q using MvPolynomial.induction_on with
    | C k => rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, hK]
    | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
    | mul_X p i hp => rw [map_mul, hmul, hp, hz]; simp
  let : Algebra B ℂ := ψ.toAlgebra
  let : Algebra (MvPolynomial (Fin d) K) ℂ := (ψ.comp (algebraMap _ B)).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin d) K) B ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let L : B →ₗ[MvPolynomial (Fin d) K] ℂ :=
    { toFun := δ
      map_add' := δ.map_add
      map_smul' := fun k a => by
        rw [Algebra.smul_def, hmul, hP, mul_zero, add_zero]; rfl }
  let D : Derivation (MvPolynomial (Fin d) K) B ℂ := Derivation.mk' L fun a b => hmul a b
  have := D.liftKaehlerDifferential_comp_D a
  rw [Subsingleton.elim (KaehlerDifferential.D _ B a) 0, map_zero] at this
  exact this.symm

theorem line_ne {d : ℕ} (Q : MvPolynomial (Fin d) ℂ) (hQ : Q ≠ 0) (c : Fin d → ℂ) :
    ∃ v : Fin d → ℂ, ∀ᶠ t : ℂ in 𝓝[≠] 0, MvPolynomial.eval (c + t • v) Q ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w, MvPolynomial.eval w Q ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (MvPolynomial.funext fun x => by simpa using h x)
  refine ⟨w - c, ?_⟩
  let R : Polynomial ℂ := MvPolynomial.aeval (fun i => Polynomial.C (c i) + Polynomial.X * Polynomial.C ((w - c) i)) Q
  have hR : ∀ t, R.eval t = MvPolynomial.eval (c + t • (w - c)) Q := fun t => by
    rw [← Polynomial.coe_aeval_eq_eval, ← MvPolynomial.aeval_eq_eval]
    show ((Polynomial.aeval t).comp (MvPolynomial.aeval _)) Q = _
    congr 1
    ext i
    simp
  have h0 : R ≠ 0 := fun h => hw (by simpa [h] using (hR 1).symm)
  have := (Polynomial.finite_setOfPred_isRoot h0).eventually_cofinite_notMem
  filter_upwards [nhdsNE_le_cofinite (0 : ℂ) this] with t ht
  rw [← hR]
  exact ht

theorem disc_smooth {K B : Type} [Field K] [CommRing B] [IsDomain B] [Algebra K B] (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d K B] (σ : K →+* ℂ) (ψ₀ : B →+* ℂ)
    (h₀ : ψ₀.comp (algebraMap K B) = σ) {c a b : B} (hc : c ≠ 0) (ha : ψ₀ a = 0) (hb : ψ₀ b ≠ 0) :
    ∃ (ψ : (Fin 1 → ℂ) → (B →+* ℂ)) (C : ℝ), IsHolPts (ball 0 1) ψ ∧
      (∀ z ∈ ball (0 : Fin 1 → ℂ) 1, (ψ z).comp (algebraMap K B) = σ) ∧
      ∀ z ∈ punct 1 1 1, ψ z c ≠ 0 ∧ ψ z b ≠ 0 ∧ ‖ψ z a / ψ z b‖ ≤ C * ‖z 0‖ := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d K B
  let := g.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin d) K) B := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have : Algebra.Etale (MvPolynomial (Fin d) K) B := hg
  obtain ⟨q, hq, e, he⟩ := exists_dvd (P := MvPolynomial (Fin d) K) hc
  obtain ⟨O, Φ, oO, mO, a₁, a₂, a₃⟩ := chart_alt_bis d σ ψ₀ h₀ (fun i => algebraMap _ B (MvPolynomial.X (R := K) i))
    (fun δ h1 h2 h3 => der_zero_etale ψ₀ δ h1 h2 h3)
  set c₀ : Fin d → ℂ := fun i => ψ₀ (algebraMap _ B (MvPolynomial.X (R := K) i)) with hc₀
  have e₀ : Φ c₀ = ψ₀ := by
    simpa using a₃ (pure ()) (fun _ => ψ₀) (fun _ => tendsto_const_nhds) (by simpa using h₀)
  obtain ⟨v, hv⟩ := line_ne (MvPolynomial.map σ q)
    (fun h => hq (MvPolynomial.map_injective σ σ.injective (by simpa using h))) c₀
  have ev : ∀ u ∈ O, Φ u (algebraMap _ B q) = MvPolynomial.eval u (MvPolynomial.map σ q) := fun u hu => by
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom]
    show ((Φ u).comp (algebraMap _ B)) q = _
    congr 1
    ext k
    · rw [← (a₁ u hu).1]
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    · simpa using (a₁ u hu).2 k
  let L : ℂ → (Fin d → ℂ) := fun t => c₀ + t • v
  have dL : Differentiable ℂ L := by fun_prop
  have L0 : L 0 = c₀ := by simp [L]
  have nO : O ∈ 𝓝 (L 0) := L0 ▸ oO.mem_nhds mO
  have dΦ : ∀ x, DifferentiableAt ℂ (fun t => Φ (L t) x) 0 := fun x =>
    ((a₂ x).differentiableAt nO).comp 0 (dL 0)
  have b0 : Φ (L 0) b ≠ 0 := by rwa [L0, e₀]
  obtain ⟨C, hC⟩ := ((dΦ a).div (dΦ b) b0).isBigO_sub.bound
  have t₁ : ∀ᶠ t in 𝓝 (0 : ℂ), L t ∈ O := (dL 0).continuousAt.preimage_mem_nhds nO
  have t₂ := (dΦ b).continuousAt.eventually_ne b0
  obtain ⟨ε, ε0, hε⟩ := Metric.mem_nhds_iff.1 (t₁.and (t₂.and (hC.and (eventually_nhdsWithin_iff.1 hv))))
  have εC : (ε : ℂ) ≠ 0 := by exact_mod_cast ε0.ne'
  have nε : ∀ z : Fin 1 → ℂ, ‖(ε : ℂ) * z 0‖ = ε * ‖z 0‖ := fun z => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ε0.le]
  have mε : ∀ z ∈ ball (0 : Fin 1 → ℂ) 1, (ε : ℂ) * z 0 ∈ ball (0 : ℂ) ε := fun z hz => by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [nε]
    exact mul_lt_of_lt_one_right ε0 ((norm_le_pi_norm z 0).trans_lt hz)
  refine ⟨fun z => Φ (L (ε * z 0)), C * ε, ⟨isOpen_ball, fun x => ?_⟩, fun z hz => (a₁ _ (hε (mε z hz)).1).1,
    fun z hz => ?_⟩
  · exact (a₂ x).comp (f := fun z : Fin 1 → ℂ => L (ε * z 0)) (by fun_prop) fun z hz => (hε (mε z hz)).1
  · obtain ⟨h1, h2, h3, h4⟩ := hε (mε z hz.1)
    refine ⟨fun h => h4 (mul_ne_zero εC (hz.2 0 one_pos)) ?_, h2, ?_⟩
    · rw [← ev _ h1, he, map_mul, h, zero_mul]
    · simpa [L0, e₀, ha, abs_of_pos ε0, _root_.mul_assoc] using h3

theorem disc_domain {K A S : Type} [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    [CommRing S] [IsRegularLocalRing S] [Algebra A S] (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime S p]
    (σ : K →+* ℂ) {c a b : A} (hc : c ≠ 0) (ha : a ∈ p) (hb : b ∉ p) :
    ∃ (ψ : (Fin 1 → ℂ) → (A →+* ℂ)) (C : ℝ), IsHolPts (ball 0 1) ψ ∧
      (∀ z ∈ ball (0 : Fin 1 → ℂ) 1, (ψ z).comp (algebraMap K A) = σ) ∧
      ∀ z ∈ punct 1 1 1, ψ z c ≠ 0 ∧ ψ z b ≠ 0 ∧ ‖ψ z a / ψ z b‖ ≤ C * ‖z 0‖ := by
  have : CharZero K := σ.charZero
  have : IsRegularLocalRing (Localization.AtPrime p) :=
    IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl S (Localization.AtPrime p)).toRingEquiv
  have : Algebra.IsSmoothAt K p := GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField K _
  have : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  obtain ⟨g, hg, ⟨_, _, _, _, ⟨P⟩⟩⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K p
  have : Algebra.IsStandardSmoothOfRelativeDimension P.dimension K (Localization.Away g) := ⟨_, _, _, ‹_›, P, rfl⟩
  have g0 : g ≠ 0 := fun h => hg (h ▸ p.zero_mem)
  have hle : Submonoid.powers g ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors g0
  have : IsDomain (Localization.Away g) := IsLocalization.isDomain_localization hle
  obtain ⟨χ, h1, h2, h3⟩ := exists_point σ p (Ideal.IsPrime.mul_notMem ‹_› hb hg)
  rw [map_mul] at h3
  let ψ₀ : Localization.Away g →+* ℂ := IsLocalization.Away.lift g (g := χ) (right_ne_zero_of_mul h3).isUnit
  have hψ : ∀ x, ψ₀ (algebraMap A _ x) = χ x := IsLocalization.Away.lift_eq g _
  obtain ⟨ψ, C, b₁, b₂, b₃⟩ := disc_smooth P.dimension σ ψ₀
    (by rw [← h1]; ext k; simp [IsScalarTower.algebraMap_apply K A (Localization.Away g), hψ])
    (c := algebraMap A _ c) (a := algebraMap A _ a) (b := algebraMap A _ b)
    (fun h => hc (IsLocalization.injective _ hle (h.trans (map_zero _).symm))) (by rw [hψ, h2 a ha])
    (by rw [hψ]; exact left_ne_zero_of_mul h3)
  refine ⟨fun z => (ψ z).comp (algebraMap A _), C, ⟨isOpen_ball, fun x => b₁.2 _⟩, fun z hz => ?_, b₃⟩
  rw [← b₂ z hz, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]

theorem disc_ring {K A S : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    [CommRing S] [IsDomain S] [IsRegularLocalRing S] [Algebra A S] (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime S p]
    (σ : K →+* ℂ) {c a b : A} (hc : algebraMap A S c ≠ 0) (ha : a ∈ p) (hb : b ∉ p) :
    ∃ (ψ : (Fin 1 → ℂ) → (A →+* ℂ)) (C : ℝ), IsHolPts (ball 0 1) ψ ∧
      (∀ z ∈ ball (0 : Fin 1 → ℂ) 1, (ψ z).comp (algebraMap K A) = σ) ∧ (∀ z t, algebraMap A S t = 0 → ψ z t = 0) ∧
      ∀ z ∈ punct 1 1 1, ψ z c ≠ 0 ∧ ψ z b ≠ 0 ∧ ‖ψ z a / ψ z b‖ ≤ C * ‖z 0‖ := by
  let I := RingHom.ker (algebraMap A S)
  have : I.IsPrime := RingHom.ker_isPrime _
  let : Algebra (A ⧸ I) S := (RingHom.kerLift (algebraMap A S)).toAlgebra
  have hm : ∀ x : A, algebraMap (A ⧸ I) S (Ideal.Quotient.mk I x) = algebraMap A S x := fun _ => rfl
  let p' : Ideal (A ⧸ I) := (IsLocalRing.maximalIdeal S).comap (algebraMap (A ⧸ I) S)
  have hp : ∀ x : A, Ideal.Quotient.mk I x ∈ p' ↔ x ∈ p := fun x =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff S p x
  have : IsLocalization.AtPrime S p' := by
    refine (isLocalization_iff _ _).2 ⟨fun y => ?_, fun s => ?_, fun h => ⟨1, ?_⟩⟩
    · exact (IsLocalRing.notMem_maximalIdeal).1 y.2
    · obtain ⟨⟨x, y⟩, h⟩ := IsLocalization.surj p.primeCompl s
      exact ⟨⟨Ideal.Quotient.mk I x, Ideal.Quotient.mk I y, fun h' => y.2 ((hp y).1 h')⟩, h⟩
    · rw [RingHom.kerLift_injective _ h]
  obtain ⟨ψ, C, b₁, b₂, b₃⟩ := disc_domain (S := S) p' σ (c := Ideal.Quotient.mk I c) (a := Ideal.Quotient.mk I a)
    (b := Ideal.Quotient.mk I b) (fun h => hc (by rw [← hm, h, map_zero])) ((hp a).2 ha) (fun h => hb ((hp b).1 h))
  refine ⟨fun z => (ψ z).comp (Ideal.Quotient.mk I), C, ⟨isOpen_ball, fun x => b₁.2 _⟩, fun z hz => b₂ z hz,
    fun z t ht => ?_, b₃⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ht, map_zero]

theorem ft_sec {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) [LocallyOfFiniteType s] {V : X.Opens}
    (hV : IsAffineOpen V) : @Algebra.FiniteType K Γ(X, V) _ _ (Geo.ResK.secAlgebra s V) := by
  have h1 : (s.appLE ⊤ V (fun _ _ => trivial)).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
  exact RingHom.finiteType_respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv h1

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genMap_germ (V : X.Opens) (q : Cpt ξ) (hq : q.1 ∈ V) (h : genPt ξ ∈ V) (v : Γ(X, V)) :
    genMap ξ q (X.presheaf.germ V q.1 hq v) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) h v) := by
  have e := X.presheaf.germ_stalkSpecializes hq q.2
  simp only [genMap]
  rw [← e]
  rfl

theorem val_germ {V : X.Opens} (hV : IsAffineOpen V) (χ : Γ(X, V) →+* ℂ) (v : Γ(X, V)) :
    (Scheme.stalkClosedPointTo (spMap χ ≫ hV.fromSpec)).hom
      (X.presheaf.germ V (centre (spMap χ ≫ hV.fromSpec)) (centre_mem hV χ) v) = χ v := by
  have e₂ := (top_le_iff _ V).2 (centre_mem hV χ)
  have k := SectionNear.germ_closedPoint (R := CommRingCat.of ℂ) (spMap χ ≫ hV.fromSpec) V (centre_mem hV χ) e₂
  exact congrArg (fun φ => φ.hom v) (k.trans (SectionNear.spMap_fromSpec_appLE hV χ e₂))

theorem spec_centre {V : X.Opens} (hV : IsAffineOpen V) (χ : Γ(X, V) →+* ℂ) {q : X}
    (h : ∀ t, χ t ≠ 0 → q ∈ X.basicOpen t) : q ⤳ centre (spMap χ ≫ hV.fromSpec) := by
  rw [specializes_iff_forall_open]
  intro U hU hc
  obtain ⟨t, h1, h2⟩ := hV.exists_basicOpen_le (V := ⟨U, hU⟩) ⟨_, hc⟩ (centre_mem hV χ)
  exact h1 (h t ((centre_mem_basicOpen hV χ t).1 h2))

theorem gen_mem_basicOpen (hξ : IsCptGen ξ) {V : X.Opens} (h : genPt ξ ∈ V) (t : Γ(X, V)) :
    genPt ξ ∈ X.basicOpen t ↔ (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) h t) ≠ 0 := by
  rw [X.mem_basicOpen t _ h]
  exact ⟨fun hu => (hu.map _).ne_zero, fun h0 => (Scheme.isLocalHom_stalkClosedPointTo' ξ).map_nonunit _ h0.isUnit⟩

theorem exists_frac (hξ : IsCptGen ξ) {V : X.Opens} (hV : IsAffineOpen V) (x : Cpt ξ) (hx : x.1 ∈ V)
    [IsDomain (X.presheaf.stalk x.1)] [ValuationRing (X.presheaf.stalk x.1)] {f : Ω} (hf : f ∉ regAt ξ x) :
    ∃ w ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x.1), f * genMap ξ x w = 1 := by
  have hg : genPt ξ ∈ V := x.2.mem_open V.isOpen hx
  obtain ⟨s, rfl⟩ := hξ.bij.2 f
  let := X.presheaf.algebra_section_stalk ⟨genPt ξ, hg⟩
  have := hV.isLocalization_stalk ⟨genPt ξ, hg⟩
  obtain ⟨⟨t, u⟩, h⟩ := IsLocalization.surj (S := X.presheaf.stalk (genPt ξ))
    (hV.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal.primeCompl s
  have hu : genMap ξ x (X.presheaf.germ V x.1 hx u.1) ≠ 0 := by
    rw [genMap_germ V x hx hg]
    exact ((IsLocalization.map_units (X.presheaf.stalk (genPt ξ)) u).map _).ne_zero
  have e : (Scheme.stalkClosedPointTo ξ).hom s * genMap ξ x (X.presheaf.germ V x.1 hx u.1) =
      genMap ξ x (X.presheaf.germ V x.1 hx t) := by
    rw [genMap_germ V x hx hg, genMap_germ V x hx hg]
    let F : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
    exact (map_mul F s _).symm.trans (congrArg F h)
  generalize (Scheme.stalkClosedPointTo ξ).hom s = f at *
  obtain ⟨w, hw | hw⟩ := ValuationRing.cond (X.presheaf.germ V x.1 hx t) (X.presheaf.germ V x.1 hx u.1)
  · have e' : f * genMap ξ x w = 1 := by
      apply mul_right_cancel₀ hu
      rw [mul_right_comm, e, ← map_mul, hw, _root_.one_mul]
    refine ⟨w, fun ⟨w', hw'⟩ => hf ⟨w'.inv, ?_⟩, e'⟩
    rw [← _root_.one_mul (genMap ξ x _), ← e', _root_.mul_assoc, ← map_mul, ← hw', w'.val_inv, map_one, _root_.mul_one]
  · refine (hf ⟨w, ?_⟩).elim
    apply mul_right_cancel₀ hu
    rw [e, ← hw, map_mul, mul_comm]

end PositivityTheory.Xgn.NoPoleDisc

open PositivityTheory.Xgn.HolomorphicChart PositivityTheory.Xgn.NoPoleDisc in
theorem PositivityTheory.Xgn.exists_holomorphic_disc_avoiding_pole : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W : X.Opens) (x : Cpt ξ) (N : X.Opens) (f : Ω), LocallyOfFiniteType s → IsCptGen ξ → genPt ξ ∈ W → x.1 ∉ W → x.1 ∈ N → IsDiscreteValuationRing (regAt ξ x) → f ∉ regAt ξ x → ∃ (V : X.Opens) (hV : IsAffineOpen V) (ψ : (Fin 1 → ℂ) → (Γ(X, V) →+* ℂ)) (r : (Fin 1 → ℂ) → ℂ) (C : ℝ), V ≤ N ∧ IsHolPts (ball 0 1) ψ ∧ (∀ z ∈ ball (0 : Fin 1 → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ genPt ξ ⤳ centre (spMap (ψ z) ≫ hV.fromSpec)) ∧ ∀ z ∈ punct 1 1 1, ⊤ ≤ (spMap (ψ z) ≫ hV.fromSpec) ⁻¹ᵁ W ∧ ValAt ξ (spMap (ψ z) ≫ hV.fromSpec) f (r z) ∧ r z ≠ 0 ∧ ‖(r z)⁻¹‖ ≤ C * ‖z 0‖ := by
  intro K _ σ X s Ω _ ξ W x N f hs hξ hW _ hN hR hf
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, hVN⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hN N.isOpen
  replace hV : IsAffineOpen V := hV
  replace hx : x.1 ∈ V := hx
  have hg : genPt ξ ∈ V := x.2.mem_open V.isOpen hx
  let e : X.presheaf.stalk x.1 ≃+* regAt ξ x := RingEquiv.ofBijective (genMap ξ x).rangeRestrict
    ⟨fun a b h => hξ.inj x (congrArg Subtype.val h), (genMap ξ x).rangeRestrict_surjective⟩
  have : IsDomain (X.presheaf.stalk x.1) := (hξ.inj x).isDomain _
  have : IsDiscreteValuationRing (X.presheaf.stalk x.1) := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm
  obtain ⟨w, hw, hfw⟩ := exists_frac hξ hV x hx hf
  let := X.presheaf.algebra_section_stalk ⟨x.1, hx⟩
  have := hV.isLocalization_stalk ⟨x.1, hx⟩
  let := Geo.ResK.secAlgebra s V
  have := ft_sec s hV
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (S := X.presheaf.stalk x.1)
    (hV.primeIdealOf ⟨x.1, hx⟩).asIdeal.primeCompl w
  obtain ⟨h, h1, h2⟩ := hV.exists_basicOpen_le ⟨genPt ξ, hW⟩ hg
  let φ : Γ(X, V) → Ω := fun t => (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hg t)
  have hφ : ∀ t, genMap ξ x (algebraMap Γ(X, V) (X.presheaf.stalk x.1) t) = φ t := genMap_germ V x hx hg
  have hub := IsLocalization.map_units (X.presheaf.stalk x.1) b
  have fab : f * φ a = φ b := by
    rw [← hφ, ← hφ, ← hab, map_mul, ← _root_.mul_assoc, hfw, _root_.one_mul]
  have a0 : φ a ≠ 0 := fun h0 => (hub.map (genMap ξ x)).ne_zero (by rw [hφ, ← fab, h0, mul_zero])
  have h0 : φ h ≠ 0 := (gen_mem_basicOpen hξ hg h).1 h2
  obtain ⟨ψ, C, b₁, b₂, b₃, b₄⟩ := disc_ring (S := X.presheaf.stalk x.1) (hV.primeIdealOf ⟨x.1, hx⟩).asIdeal σ
    (c := h * a) (a := a) (b := b.1)
    (fun h' => mul_ne_zero h0 a0 (by rw [← hφ, ← hφ, ← map_mul, ← map_mul, h', map_zero]))
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x.1) _ a).1 (hab ▸ Ideal.mul_mem_right _ _ hw)) b.2
  have sp : ∀ z, genPt ξ ⤳ centre (spMap (ψ z) ≫ hV.fromSpec) := fun z => spec_centre hV _ fun t ht =>
    (gen_mem_basicOpen hξ hg t).2 fun h' => ht (b₃ z t (hξ.inj x ((hφ t).trans (h'.trans (map_zero _).symm))))
  refine ⟨V, hV, ψ, fun z => ψ z b / ψ z a, C, hVN, b₁, fun z hz => ⟨(over_iff s hV σ _).2 (b₂ z hz), sp z⟩,
    fun z hz => ?_⟩
  obtain ⟨c₁, c₂, c₃⟩ := b₄ z hz
  rw [map_mul] at c₁
  have c₄ := right_ne_zero_of_mul c₁
  refine ⟨(top_le_iff _ W).2 (h1 ((centre_mem_basicOpen hV _ h).2 (left_ne_zero_of_mul c₁))), ?_,
    div_ne_zero c₂ c₄, by rwa [inv_div]⟩
  obtain ⟨u, hu⟩ := (X.mem_basicOpen a _ (centre_mem hV (ψ z))).1 ((centre_mem_basicOpen hV _ a).2 c₄)
  have k : X.presheaf.germ V _ (centre_mem hV (ψ z)) b.1 * u.inv * X.presheaf.germ V _ (centre_mem hV (ψ z)) a =
      X.presheaf.germ V _ (centre_mem hV (ψ z)) b.1 := by
    rw [_root_.mul_assoc]
    exact (congrArg _ (hu ▸ u.inv_val)).trans (_root_.mul_one _)
  refine ⟨sp z, X.presheaf.germ V _ (centre_mem hV (ψ z)) b.1 * u.inv, mul_right_cancel₀ a0 ?_, eq_div_of_mul_eq c₄ ?_⟩
  · have := congrArg (genMap ξ ⟨_, sp z⟩) k
    rw [map_mul, genMap_germ V ⟨_, sp z⟩ _ hg a, genMap_germ V ⟨_, sp z⟩ _ hg b.1] at this
    rw [fab]
    exact this
  · let F : X.presheaf.stalk (centre (spMap (ψ z) ≫ hV.fromSpec)) →+* ℂ :=
      (Scheme.stalkClosedPointTo (spMap (ψ z) ≫ hV.fromSpec)).hom
    have hF : ∀ v, F (X.presheaf.germ V _ (centre_mem hV (ψ z)) v) = ψ z v := val_germ hV (ψ z)
    have := congrArg F k
    rw [map_mul, hF a, hF b.1] at this
    exact this
