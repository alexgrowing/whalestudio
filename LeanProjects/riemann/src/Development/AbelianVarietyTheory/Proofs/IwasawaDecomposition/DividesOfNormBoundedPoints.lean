import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsScfEmbeddingDvdStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointOfIntegralPointStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine.Dvd

attribute [local instance] Over.cartesianMonoidalCategory

section Algebra

variable {R : Type} [CommRing R]

theorem map_ne_zero_of_mem (P : Ideal R) [P.IsPrime] {b : R} (hb : b ∈ nonZeroDivisors R) :
    algebraMap R (Localization.AtPrime P) b ≠ 0 := by
  intro h
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ b).1 h
  have : (c : R) = 0 := (mem_nonZeroDivisors_iff_right.1 hb) _ hc
  exact c.2 (this ▸ P.zero_mem)

theorem dvd_of_height_one [IsNoetherianRing R]
    (hR : ∀ (P : Ideal R) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P))
    {a b : R} (hb : b ∈ nonZeroDivisors R)
    (h : ∀ (P : Ideal R) [P.IsPrime], P.height = 1 → b ∈ P → ∃ s, s ∉ P ∧ b ∣ s * a) : b ∣ a := by
  rw [← Ideal.mem_span_singleton]
  refine Ideal.mem_of_localization_maximal fun m hm => ?_
  obtain ⟨_, _⟩ := hR m
  have : IsNoetherianRing (Localization.AtPrime m) := IsLocalization.isNoetherianRing m.primeCompl _ inferInstance
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  refine GlobalTheory.dvd_of_forall_height_eq_one (map_ne_zero_of_mem m hb) fun Q _ hQ hbQ => ?_
  have hP : (Q.comap (algebraMap R (Localization.AtPrime m))).height = 1 :=
    (IsLocalization.height_comap m.primeCompl Q).trans hQ
  obtain ⟨s, hs, t, ht⟩ := h _ hP hbQ
  exact ⟨algebraMap R _ s, hs, algebraMap R _ t, by rw [← map_mul, ht, map_mul]⟩

theorem isDVR_of_height_one [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (hP : P.height = 1)
    [IsDomain (Localization.AtPrime P)] [IsIntegrallyClosed (Localization.AtPrime P)] :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  have : IsNoetherianRing (Localization.AtPrime P) := IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hd : ringKrullDim (Localization.AtPrime P) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P, hP]
    rfl
  have h1 : Ring.KrullDimLE 1 (Localization.AtPrime P) := by
    rw [Ring.krullDimLE_iff, hd]
    rfl
  have hf : ¬ IsField (Localization.AtPrime P) := fun h => by
    have := ringKrullDim_eq_zero_of_isField h
    rw [hd] at this
    simp at this
  have hm := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf
  have h3 : IsIntegrallyClosed (Localization.AtPrime P) ∧
      ∃! Q : Ideal (Localization.AtPrime P), Q ≠ ⊥ ∧ Q.IsPrime :=
    ⟨inferInstance, _, ⟨hm, inferInstance⟩, fun Q hQ => IsLocalRing.eq_maximalIdeal
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 Q hQ.1 hQ.2)⟩
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hf).out 0 3).mpr h3

theorem exists_of_dvd (P : Ideal R) [P.IsPrime] {a b : R}
    (h : algebraMap R (Localization.AtPrime P) b ∣ algebraMap R (Localization.AtPrime P) a) :
    ∃ s, s ∉ P ∧ b ∣ s * a := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨⟨x, t⟩, he⟩ := IsLocalization.surj P.primeCompl c
  have e : algebraMap R (Localization.AtPrime P) (a * t) = algebraMap R (Localization.AtPrime P) (b * x) := by
    rw [map_mul, map_mul, hc, _root_.mul_assoc]
    exact congrArg _ he
  obtain ⟨u, hu⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) e
  refine ⟨u * t, fun hm => ?_, u * x, ?_⟩
  · rcases Ideal.IsPrime.mem_or_mem inferInstance hm with h | h
    exacts [u.2 h, t.2 h]
  · calc (u : R) * t * a = u * (a * t) := by ring
      _ = u * (b * x) := hu
      _ = b * (u * x) := by ring

theorem mk_localization_le (P : Ideal R) [P.IsPrime] (h : Cardinal.mk R ≤ Cardinal.continuum) :
    Cardinal.mk (Localization.AtPrime P) ≤ Cardinal.continuum := by
  have s : Function.Surjective fun x : R × P.primeCompl => IsLocalization.mk' (Localization.AtPrime P) x.1 x.2 :=
    fun v => by
      obtain ⟨x, e⟩ := IsLocalization.mk'_surjective P.primeCompl v
      exact ⟨x, e⟩
  refine (Cardinal.mk_le_of_surjective s).trans ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc _ ≤ Cardinal.continuum * Cardinal.continuum := mul_le_mul' h ((Cardinal.mk_subtype_le _).trans h)
    _ = _ := Cardinal.continuum_mul_self

theorem mk_le_of_finiteType {D : Type} [CommRing D] (σ : D →+* R) (hσ : σ.FiniteType)
    (h : Cardinal.mk D ≤ Cardinal.continuum) : Cardinal.mk R ≤ Cardinal.continuum := by
  letI := σ.toAlgebra
  have : Algebra.FiniteType D R := hσ
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  refine (Cardinal.mk_le_of_surjective hf).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
  exact max_le (max_le h ((Cardinal.lt_aleph0_of_finite _).le.trans Cardinal.aleph0_le_continuum)) Cardinal.aleph0_le_continuum

theorem ker_le_of_le (P q : Ideal R) [P.IsPrime] [q.IsPrime] (h : q ≤ RingHom.ker (algebraMap R (Localization.AtPrime P))) :
    RingHom.ker (algebraMap R (Localization.AtPrime P)) ≤ q := by
  intro r hr
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ r).1 hr
  refine ((inferInstance : q.IsPrime).mem_or_mem (hc ▸ q.zero_mem)).resolve_left fun hcq => ?_
  have e : algebraMap R (Localization.AtPrime P) c = 0 := h hcq
  have u := IsLocalization.map_units (Localization.AtPrime P) c
  rw [e] at u
  have : Nontrivial (Localization.AtPrime P) := inferInstance
  exact not_isUnit_zero u

theorem natCast_mem {D : Type} [CommRing D] [IsDomain D] [CharZero D] (σ : D →+* R) (hσ : σ.Flat) {n : ℕ} (hn : n ≠ 0) :
    (n : R) ∈ nonZeroDivisors R := by
  letI := σ.toAlgebra
  have : Module.Flat D R := hσ
  have hr : (n : D) ∈ nonZeroDivisors D := mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hn)
  have reg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hr
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => reg ?_
  change (n : D) • x = (n : D) • 0
  rw [Algebra.smul_def, smul_zero]
  have e : algebraMap D R (n : D) = (n : R) := map_natCast _ n
  rw [e, mul_comm, hx]

end Algebra

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem eq_of_specializes {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {F : Type} [Field F] (θ : Γ(X, U) →+* F)
    (P : Ideal Γ(X, U)) [P.IsPrime] (hθ : RingHom.ker θ = RingHom.ker (algebraMap Γ(X, U) (Localization.AtPrime P)))
    (t : Sp F) (x' : X) (h : x' ⤳ (spMap θ ≫ hU.fromSpec) t) : x' = (spMap θ ≫ hU.fromSpec) t := by
  rw [Scheme.Hom.comp_apply] at h ⊢
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum Γ(X, U), q = spMap θ t := ⟨_, rfl⟩
  rw [← hq] at h ⊢
  have hk : q.asIdeal = RingHom.ker θ := by
    have : t.asIdeal.IsPrime := t.2
    have e : t.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [hq]
    change Ideal.comap θ t.asIdeal = _
    rw [e]
    rfl
  have hm : hU.fromSpec q ∈ U := by
    have : hU.fromSpec q ∈ Set.range hU.fromSpec := ⟨q, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hx : x' ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact h.mem_open U.isOpen hm
  obtain ⟨q', rfl⟩ := hx
  have hs : q' ⤳ q := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.1 h
  have hle : q'.asIdeal ≤ q.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 hs
  have := q'.isPrime
  have : q' = q := PrimeSpectrum.ext (le_antisymm hle (by
    rw [hk, hθ]
    exact ker_le_of_le P q'.asIdeal (by rw [← hθ, ← hk]; exact hle)))
  rw [this]

theorem mem_opn (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {x : Z.X} (hx : ∀ x' : Z.X, x' ⤳ x → x' = x) :
    x ∈ Z.opn := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.toPre.s := by
    unfold Pre.s
    infer_instance
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.toPre.s
  have hc := irreducibleComponent_mem_irreducibleComponents x
  have ho := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hc
  have hg := hc.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hc)
  have e := hx _ (hg.specializes mem_irreducibleComponent)
  rw [e] at hg
  obtain ⟨y, hy, hyo⟩ := Z.dense.inter_open_nonempty _ ho ⟨_, mem_irreducibleComponent⟩
  have hopen : IsOpen Z.opn := Z.cover ▸ isOpen_iUnion fun a => (Z.U a).1.isOpen
  exact (hg.specializes hy).mem_open hopen hyo

theorem exists_base (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) :
    ∃ σ : Z.i.c.V W →+* Γ(Z.X, U), σ.Flat ∧ σ.FiniteType := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.toPre.s := by
    unfold Pre.s
    infer_instance
  have := Z.flat
  let σ : Z.i.c.V W →+* Γ(Z.X, U) := (Spec.preimage (hU.fromSpec ≫ Z.toPre.s)).hom
  have e : spMap σ = hU.fromSpec ≫ Z.toPre.s := Spec.map_preimage _
  have h1 : Flat (spMap σ) := by rw [e]; infer_instance
  have h2 : LocallyOfFiniteType (spMap σ) := by rw [e]; infer_instance
  exact ⟨σ, (HasRingHomProperty.Spec_iff (P := @Flat)).1 h1, (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h2⟩

open GlobalTheory.ShFam.Pad.Pull in

theorem exists_local (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U)
    (a b : Γ(Z.X, U)) (h : ∀ y : Z.Pt, ⊤ ≤ y.z ⁻¹ᵁ U → ‖valF y.gen U a‖ ≤ ‖valF y.gen U b‖)
    (P : Ideal Γ(Z.X, U)) [P.IsPrime] (hP : P.height = 1) (hpP : (p : Γ(Z.X, U)) ∈ P)
    (hc : Cardinal.mk Γ(Z.X, U) ≤ Cardinal.continuum) (hnz : ∀ n : ℕ, n ≠ 0 → (n : Γ(Z.X, U)) ∈ nonZeroDivisors Γ(Z.X, U))
    [IsNoetherianRing Γ(Z.X, U)] [IsDomain (Localization.AtPrime P)] [IsIntegrallyClosed (Localization.AtPrime P)] :
    ∃ s, s ∉ P ∧ b ∣ s * a := by
  have := isDVR_of_height_one P hP
  have : CharZero (Localization.AtPrime P) := charZero_of_inj_zero fun n hn => by
    by_contra h0
    exact map_ne_zero_of_mem P (hnz n h0) (by rw [map_natCast]; exact hn)
  have hpV : (p : Localization.AtPrime P) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P (p : Γ(Z.X, U))).2 hpP
    rwa [map_natCast] at this
  obtain ⟨C, φ, φi, hφ⟩ := GlobalTheory.T.exists_spherically_complete_embedding' p (Localization.AtPrime P) hp hpV (mk_localization_le P hc)
  let ψ : Γ(Z.X, U) →+* ↥(intO ↥C.S) := φ.comp (algebraMap _ _)
  let θ : Γ(Z.X, U) →+* ↥C.S := (intO ↥C.S).subtype.comp ψ
  have hθ : RingHom.ker θ = RingHom.ker (algebraMap Γ(Z.X, U) (Localization.AtPrime P)) := by
    ext r
    simp only [RingHom.mem_ker, θ, ψ, RingHom.comp_apply]
    refine ⟨fun e => φi ?_, fun e => by rw [e, map_zero, map_zero]⟩
    rw [map_zero]
    exact (intO ↥C.S).subtype_injective (by rw [e, map_zero])
  have hgen : spMap (intO ↥C.S).subtype ≫ spMap ψ ≫ hU.fromSpec = spMap θ ≫ hU.fromSpec := by
    rw [← Category.assoc, ModelRelProbe.spMap_comp]
  have hr : Set.range (spMap (intO ↥C.S).subtype ≫ spMap ψ ≫ hU.fromSpec) ⊆ Z.opn := by
    rintro _ ⟨t, rfl⟩
    rw [hgen]
    exact mem_opn hp hW Z fun x' hx' => eq_of_specializes hU θ P hθ t x' hx'
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_point_of_integral_point E H Dw Xo p W Y i₀ hp hW Z C (spMap ψ ≫ hU.fromSpec) hr
  let y : Z.Pt := ⟨C, Q, spMap ψ ≫ hU.fromSpec, hQ⟩
  have hy : y.gen = spMap θ ≫ hU.fromSpec := hgen
  have := h y (le_of_fromSpec hU rfl)
  rw [hy, valF_fromSpec, valF_fromSpec] at this
  exact exists_of_dvd P (hφ _ _ this)

theorem dvd_of_forall_pt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (U : Z.X.Opens), IsAffineOpen U → ∀ a b : Γ(Z.X, U), (p : Γ(Z.X, U)) ∈ (Ideal.span {b}).radical → (∀ y : Z.Pt, ⊤ ≤ y.z ⁻¹ᵁ U → ‖valF y.gen U a‖ ≤ ‖valF y.gen U b‖) → b ∣ a := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z U hU a b hrad h
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  obtain ⟨σ, hf, hft⟩ := exists_base hp hW Z hU
  have : CharZero (Z.i.c.V W) := RingHom.charZero (Z.i.c.V W).subtype
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have hR := (GlobalTheory.IsNormalScheme.iff_forall_isAffineOpen Z.X).1 hN U hU
  have hnz : ∀ n : ℕ, n ≠ 0 → (n : Γ(Z.X, U)) ∈ nonZeroDivisors Γ(Z.X, U) := fun n hn => natCast_mem σ hf hn
  have hD : Cardinal.mk (Z.i.c.V W) ≤ Cardinal.continuum :=
    (Cardinal.mk_subtype_le _).trans ((Cardinal.mk_subtype_le _).trans Cardinal.mk_complex.le)
  have hc := mk_le_of_finiteType σ hft hD
  have : IsNoetherianRing Γ(Z.X, U) := by
    letI := σ.toAlgebra
    have : Algebra.FiniteType (Z.i.c.V W) Γ(Z.X, U) := hft
    exact Algebra.FiniteType.isNoetherianRing (Z.i.c.V W) _
  obtain ⟨N, hN'⟩ := hrad
  obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton.1 hN'
  have hb : b ∈ nonZeroDivisors Γ(Z.X, U) :=
    (mul_mem_nonZeroDivisors.1 (hc' ▸ pow_mem (hnz p hp.ne_zero) N)).1
  refine dvd_of_height_one hR hb fun P _ hP hbP => ?_
  obtain ⟨_, _⟩ := hR P
  have hpP : (p : Γ(Z.X, U)) ∈ P := (inferInstance : P.IsPrime).mem_of_pow_mem N (hc' ▸ P.mul_mem_right c hbP)
  exact exists_local hp hW Z hU a b h P hP hpP hc hnz

end Model

end GlobalTheory.HTLine.Dvd
