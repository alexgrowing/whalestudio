import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLatticeGeneratorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombTangentIffLinearSumStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF.Loc

theorem exists_basis {V L W : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] [AddCommGroup W] [Module L W] [Module V W] [IsScalarTower V L W] {n : ℕ} (x : Fin n → W)
    (Λ : Submodule V W) {c : V} (hc : c ≠ 0) (h₁ : Λ ≤ Submodule.span V (Set.range x))
    (h₂ : ∀ w ∈ Submodule.span V (Set.range x), c • w ∈ Λ) :
    ∃ P Q : Matrix (Fin n) (Fin n) V, Q * P = c • (1 : Matrix (Fin n) (Fin n) V) ∧
      Submodule.span V (Set.range fun k => ∑ i, P k i • x i) = Λ := by
  classical
  let f : (Fin n → V) →ₗ[V] W := Fintype.linearCombination V x
  have hf : ∀ u, f u = ∑ i, u i • x i := fun u => Fintype.linearCombination_apply V x u
  have hfr : LinearMap.range f = Submodule.span V (Set.range x) := Fintype.range_linearCombination V x
  let N : Submodule V (Fin n → V) := Λ.comap f
  have hcN : ∀ u : Fin n → V, c • u ∈ N := fun u => by
    change f (c • u) ∈ Λ
    rw [map_smul]
    exact h₂ _ (hfr ▸ ⟨u, rfl⟩)
  let g : (Fin n → V) →ₗ[V] N := LinearMap.codRestrict N (c • LinearMap.id) hcN
  have hg : Function.Injective g := fun u u' h => by
    have : c • u = c • u' := congrArg Subtype.val h
    exact smul_right_injective _ hc this
  have hr : Module.finrank V N = n := by
    refine le_antisymm ((Submodule.finrank_le N).trans (by simp)) ?_
    simpa using LinearMap.finrank_le_finrank_of_injective hg
  let b := Module.finBasisOfFinrankEq V N hr
  refine ⟨Matrix.of fun k i => (b k : Fin n → V) i, Matrix.of fun i k => b.repr (g (Pi.single i 1)) k, ?_, ?_⟩
  · ext i i'
    have h := congrArg (fun u : N => (u : Fin n → V) i') (b.sum_repr (g (Pi.single i 1)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [h]
    simp [g, Matrix.one_apply, Pi.single_apply, eq_comm]
  · have e : (fun k => ∑ i, (Matrix.of fun k i => (b k : Fin n → V) i) k i • x i) = fun k => f (b k) :=
      funext fun k => (hf _).symm
    rw [e]
    refine le_antisymm (Submodule.span_le.2 ?_) fun w hw => ?_
    · rintro _ ⟨k, rfl⟩
      exact (b k).2
    · obtain ⟨u, rfl⟩ : w ∈ LinearMap.range f := hfr ▸ h₁ hw
      have hu : u ∈ N := hw
      have h := congrArg (fun t : N => f t) (b.sum_repr ⟨u, hu⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] at h
      rw [← h]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem log_det_bounds {V A : Type} [CommRing V] [NormedField A] (j : V →+* A) (hj : ∀ a, ‖j a‖ ≤ 1) {n : ℕ}
    {P Q : Matrix (Fin n) (Fin n) V} {c : V} (hc : j c ≠ 0) (h : Q * P = c • (1 : Matrix (Fin n) (Fin n) V)) :
    j P.det ≠ 0 ∧ n * Real.log ‖j c‖ ≤ Real.log ‖j P.det‖ ∧ Real.log ‖j P.det‖ ≤ 0 := by
  have e : j Q.det * j P.det = j c ^ n := by
    rw [← map_mul, ← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, map_pow, Fintype.card_fin]
  have h0 : j Q.det * j P.det ≠ 0 := e ▸ pow_ne_zero _ hc
  have hP := right_ne_zero_of_mul h0
  have hQ := left_ne_zero_of_mul h0
  have e2 : Real.log ‖j Q.det‖ + Real.log ‖j P.det‖ = n * Real.log ‖j c‖ := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 hQ) (norm_ne_zero_iff.2 hP), ← norm_mul, e, norm_pow, Real.log_pow]
  have a1 := Real.log_nonpos (norm_nonneg _) (hj Q.det)
  have a2 := Real.log_nonpos (norm_nonneg _) (hj P.det)
  exact ⟨hP, by linarith, a2⟩

section Ev

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]

theorem exists_ev (hξ : IsCptGen ξ) (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) :
    ∃ ev : regAt ξ ⟨centre z, h⟩ →+* R, ∀ a : regAt ξ ⟨centre z, h⟩, ValAt ξ z a (ev a) := by
  let e : X.presheaf.stalk (centre z) ≃+* regAt ξ ⟨centre z, h⟩ :=
    RingEquiv.ofBijective (genMap ξ ⟨centre z, h⟩).rangeRestrict
      ⟨fun a b hab => hξ.inj ⟨centre z, h⟩ (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  refine ⟨(Scheme.stalkClosedPointTo z).hom.comp e.symm.toRingHom, fun a => ⟨h, e.symm a, ?_, rfl⟩⟩
  exact congrArg Subtype.val (e.apply_symm_apply a)

end Ev

theorem norm_p (p : Nat.Primes) : ‖((p : ℕ) : ℂ_[p])‖ = ((p : ℕ) : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast (p := p), PadicComplex.norm_extends (p := p), ← PadicAlgCl.valuation_coe (p := p),
    PadicAlgCl.valuation_p]
  simp

theorem norm_p_lt_one (p : Nat.Primes) : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
  rw [norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)

theorem log_norm_cp {Ω : Type} [Field Ω] (R : Subring Ω) (p : Nat.Primes) (f : R →+* ℂ_[p]) {κ : Ω} (hκ : κ ∈ R)
    (h : HT.IsCp p κ) : f ⟨κ, hκ⟩ ≠ 0 ∧ Real.log ‖f ⟨κ, hκ⟩‖ = -(cP p * Real.log (p : ℕ)) := by
  have hp : (p : ℕ).Prime := p.2
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast hp.one_lt
  have key : ‖f ⟨κ, hκ⟩‖ = ((p : ℕ) : ℝ) ^ (-cP p) := by
    unfold HT.IsCp at h
    unfold cP
    split_ifs at h ⊢ with h2
    · have e : (⟨κ, hκ⟩ : R) = ((p : ℕ) : R) ^ 2 := Subtype.ext (by
        have e0 : κ = (((p : ℕ) : ℕ) : Ω) ^ 2 := by rw [h, h2]; norm_num
        simpa using e0)
      have hn := norm_p p
      rw [e, map_pow, map_natCast, norm_pow, hn, Real.rpow_neg (by positivity), inv_pow]
      norm_num
    · obtain ⟨ζ, hζ, rfl⟩ := h
      have hζR : ζ ∈ R := by simpa using R.add_mem hκ R.one_mem
      have hs : ∑ i ∈ Finset.range p, (⟨ζ, hζR⟩ : R) ^ i = 0 := Subtype.ext (by
        simpa using hζ.geom_sum_eq_zero hp.one_lt)
      have hs' : ∑ i ∈ Finset.range p, f ⟨ζ, hζR⟩ ^ i = 0 := by
        have := congrArg f hs
        rw [map_sum, map_zero] at this
        simp only [map_pow] at this
        exact this
      have h1 : f ⟨ζ, hζR⟩ ≠ 1 := fun h1 => by
        rw [h1] at hs'
        simp at hs'
        exact hp.ne_zero hs'
      have hpow : f ⟨ζ, hζR⟩ ^ (p : ℕ) = 1 := by
        have := mul_geom_sum (f ⟨ζ, hζR⟩) p
        rw [hs', mul_zero] at this
        exact (sub_eq_zero.1 this.symm)
      have hprim : IsPrimitiveRoot (f ⟨ζ, hζR⟩) ((p : ℕ) ^ 1) := by
        rw [pow_one]
        have := IsPrimitiveRoot.orderOf (f ⟨ζ, hζR⟩)
        rwa [orderOf_eq_prime hpow h1] at this
      have e : f ⟨ζ - 1, hκ⟩ = f ⟨ζ, hζR⟩ - 1 := by
        rw [← map_one f, ← map_sub]; rfl
      rw [e, GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex p 1 le_rfl _ hprim]
      congr 1
      simp [neg_div]
  have hpos : 0 < ‖f ⟨κ, hκ⟩‖ := key ▸ Real.rpow_pos_of_pos (by positivity) _
  exact ⟨norm_pos_iff.1 hpos, by rw [key, Real.log_rpow (by positivity)]; ring⟩

section Line

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem wedge_of_span {n : ℕ} (b b₀ : Fin n → E) (h : flagStep Ω b n = flagStep Ω b₀ n) :
    ∃ α : Ω, exteriorPower.ιMulti Ω n b₀ = α • exteriorPower.ιMulti Ω n b := by
  have e : ∀ u : Fin n → E, flagStep Ω u n = Submodule.span Ω (Set.range u) := fun u => by
    unfold flagStep
    congr 1
    ext w
    simp
  have hm : ∀ i, ∃ t : Fin n → Ω, ∑ k, t k • b k = b₀ i := fun i => by
    have : b₀ i ∈ Submodule.span Ω (Set.range b) := by
      rw [← e, h, e]; exact Submodule.subset_span ⟨i, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun _).1 this
  choose t ht using hm
  refine ⟨(Matrix.of t).det, ?_⟩
  rw [← GlobalTheory.alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti Ω n (M := E)) (Matrix.of t) b]
  congr 1
  exact funext fun i => (ht i).symm

theorem coeff_order {A B : Lat ξ E} {p q : ℕ} {a : ⋀[Ω]^p E} {b : ⋀[Ω]^q E} {x : Cpt ξ} {bp : Fin p → E}
    {bq : Fin q → E} (hp : A.IsFrameAt bp x) (hq : B.IsFrameAt bq x) {α β : Ω} (hα : α ≠ 0) (hβ : β ≠ 0)
    (ea : a = α • exteriorPower.ιMulti Ω p bp) (eb : b = β • exteriorPower.ιMulti Ω q bq) {σ ϖ : Ω} {m : ℕ} {k : ℤ}
    (h : OrderAt (lineLat A B p q a b) σ ϖ m k x) : unitAt ξ x ((σ * α / β) ^ m / ϖ ^ k) := by
  obtain ⟨wp, np⟩ := GlobalTheory.T.wedge_lattice_generator X Ω ξ E A p bp x hp
  obtain ⟨wq, nq⟩ := GlobalTheory.T.wedge_lattice_generator X Ω ξ E B q bq x hq
  have hL : lineLat A B p q a b x = Submodule.span (regAt ξ x) {β / α} := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨f, ⟨α', β', hα', hβ', h1, h2, h3⟩, rfl⟩
      have m1 : α' • a ∈ Submodule.span (regAt ξ x) {exteriorPower.ιMulti Ω p bp} := by
        rw [← wp, h1]; exact Submodule.mem_span_singleton_self _
      have m2 : exteriorPower.ιMulti Ω q bq ∈ Submodule.span (regAt ξ x) {β' • b} := by
        rw [← h2, wq]; exact Submodule.mem_span_singleton_self _
      obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 m1
      obtain ⟨u', hu'⟩ := Submodule.mem_span_singleton.1 m2
      have e1 : (u : Ω) = α' * α := smul_left_injective Ω np (by
        change (u : Ω) • _ = (α' * α) • _
        rw [← smul_smul, ← ea]; exact hu)
      have e2 : (u' : Ω) * β' * β = 1 := smul_left_injective Ω nq (by
        change ((u' : Ω) * β' * β) • _ = (1 : Ω) • _
        rw [← smul_smul, ← smul_smul, ← eb, one_smul]; exact hu')
      refine Submodule.mem_span_singleton.2 ⟨u * u', ?_⟩
      change ((u : Ω) * u') * (β / α) = f⁻¹
      have e3 : f = β' / α' := eq_div_of_mul_eq hα' h3
      have e4 : (u' : Ω) = 1 / (β' * β) := eq_div_of_mul_eq (mul_ne_zero hβ' hβ) (by rw [← mul_assoc]; exact e2)
      rw [e1, e3, e4]
      field_simp
    · rintro _ rfl
      refine Submodule.subset_span ⟨α / β, ⟨α⁻¹, β⁻¹, inv_ne_zero hα, inv_ne_zero hβ, ?_, ?_, ?_⟩, (inv_div _ _).symm⟩
      · rw [wp, ea, smul_smul, inv_mul_cancel₀ hα, one_smul]
      · rw [wq, eb, smul_smul, inv_mul_cancel₀ hβ, one_smul]
      · field_simp
  obtain ⟨e, c, he, h1, h2, h3⟩ := h
  have m1 : e ∈ Submodule.span (regAt ξ x) {β / α} := by
    rw [← hL, h1]; exact Submodule.mem_span_singleton_self _
  have m2 : β / α ∈ Submodule.span (regAt ξ x) {e} := by
    rw [← h1, hL]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 m1
  obtain ⟨u', hu'⟩ := Submodule.mem_span_singleton.1 m2
  have hu1 : (u : Ω) * (β / α) = e := hu
  have hu2 : (u' : Ω) * e = β / α := hu'
  have huu : (u : Ω) * u' = 1 := mul_right_cancel₀ he (by rw [mul_assoc, hu2, hu1, one_mul])
  have hunit : unitAt ξ x (u : Ω) :=
    ⟨left_ne_zero_of_mul_eq_one huu, u.2, by rw [← eq_inv_of_mul_eq_one_right huu]; exact u'.2⟩
  have e5 : σ * α / β = c * u := by
    rw [h2, smul_eq_mul, ← hu1]
    field_simp
  rw [e5, mul_pow, mul_div_right_comm]
  exact ZUnit.mul h3 (ZUnit.pow hunit m)

end Line

end RootFieldNumerics.RF.Loc
