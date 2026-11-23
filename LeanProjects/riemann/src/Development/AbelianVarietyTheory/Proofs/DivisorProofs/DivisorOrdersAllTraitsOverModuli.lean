import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrWithProportionalValuations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTraitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongStalkPointEqMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomAdicCompletionExtend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqTopOfNotMemSupport
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryLocalPeriodsThetaModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughOpenOfStalkCompleteDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.AllTraits

theorem localPeriods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ x : Y.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : Y.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (p : Λ → R) (c₀ : ℕ), IsNoetherianRing R ∧ CharZero R ∧ GlobalTheory.Poinc.Eq8.IsCpl j ∧ 1 ≤ c₀ ∧ ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → T.y ≫ C.i = jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π → ∃ e : Λ ≃ₗ[𝓞 E] T.P.D.toPre.X, ∀ a, ∃ k : ℕ, (k : ℤ) = c₀ * T.be (e a) (e a) ∧ Associated (ψ (p a)) (T.ϖ ^ k) := GlobalTheory.T.exists_unitary_local_periods_thetaModel

theorem traitThroughOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (x : Y.Z) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A], IsAdicComplete (maximalIdeal A) A → ∀ θ : Y.Z.presheaf.stalk x →+* A, Function.Injective θ → IsLocalHom θ → ∃ (T : UTrait Xo c) (f : A →+* T.V), Function.Injective f ∧ IsLocalHom f ∧ (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) ∧ T.y ≫ C.i = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π := GlobalTheory.T.exists_unitaryTrait_through_open_of_stalk_complete_dvr

theorem pow_exp_eq {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (h : Irreducible ϖ) {a b : ℕ}
    (e : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff h.ne_zero h.not_isUnit).1 e.dvd) ((pow_dvd_pow_iff h.ne_zero h.not_isUnit).1 e.symm.dvd)

theorem form_eq_zero {X I : Type} [AddCommGroup X] (B : LinearMap.BilinForm ℤ X) (hB : ∀ a b, B a b = B b a) (b : I → X)
    (hb : Submodule.span ℤ (Set.range b) = ⊤) (h : ∀ i j, B (b i + b j) (b i + b j) = 0) : B = 0 := by
  have h1 : ∀ i j, B (b i) (b i) + 2 * B (b i) (b j) + B (b j) (b j) = 0 := by
    intro i j
    have := h i j
    simp only [map_add, LinearMap.add_apply] at this
    rw [hB (b j) (b i)] at this
    linarith
  have h2 : ∀ i, B (b i) (b i) = 0 := fun i => by have := h1 i i; linarith
  have h3 : ∀ i j, B (b i) (b j) = 0 := fun i j => by have := h1 i j; have := h2 i; have := h2 j; linarith
  refine LinearMap.ext_on_range hb fun i => LinearMap.ext_on_range hb fun j => ?_
  simpa using h3 i j

theorem idlAlong_ne_bot {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) (h : (jK R ≫ ξ) (closedPoint (FractionRing R)) ∉ J.support) : idlAlong J ξ ≠ ⊥ := by
  intro h0
  have h1 := idlAlong_eq_top_of_notMem_support X J _ _ h
  have h2 := GlobalTheory.TraitOrder.idlAlong_comp J ξ (algebraMap R (FractionRing R))
  rw [h0, Ideal.map_bot] at h2
  exact bot_ne_top (h2.symm.trans h1)

theorem isCpl_props {O R : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] [IsLocalRing R]
    {j : O →+* R} (hj : GlobalTheory.Poinc.Eq8.IsCpl j) : Function.Injective j ∧ IsLocalHom j ∧
      ∀ (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ φ : O →+* V, IsLocalHom φ →
        ∃ ψ : R →+* V, IsLocalHom ψ ∧ ψ.comp j = φ := by
  obtain ⟨e, he⟩ := hj
  have hj : j = e.toRingHom.comp (algebraMap O _) := RingHom.ext fun a => (he a).symm
  have hl : IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O)) := inferInstance
  refine ⟨?_, ?_, fun V _ _ hV φ hφ => ?_⟩
  · rw [hj]
    exact e.injective.comp (AdicCompletion.of_injective (maximalIdeal O) O)
  · refine ⟨fun a ha => ?_⟩
    rw [← he, MulEquiv.isUnit_map] at ha
    exact isUnit_of_map_unit _ _ ha
  · obtain ⟨ψ, h1, h2⟩ := GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend O V hV φ hφ
    refine ⟨ψ.comp e.symm.toRingHom, ⟨fun a ha => ?_⟩, RingHom.ext fun a => ?_⟩
    · have := isUnit_of_map_unit ψ _ ha
      exact (MulEquiv.isUnit_map e.symm).1 this
    · rw [← h2, RingHom.comp_apply, ← he]
      simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem finite_lat (T : UTrait Xo c) : Module.Finite (𝓞 E) T.P.D.toPre.X :=
  Module.Finite.of_restrictScalars_finite ℤ _ _

theorem projective_lat (T : UTrait Xo c) : Module.Projective (𝓞 E) T.P.D.toPre.X := by
  have : Module.Finite (𝓞 E) T.P.D.toPre.X := finite_lat T
  have : Module.Flat (𝓞 E) T.P.D.toPre.X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨a, hx⟩
    by_contra hx0
    obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (a : 𝓞 E)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero (nonZeroDivisors.coe_ne_zero a))
    have h : n • x = 0 := by
      have hx' : (a : 𝓞 E) • x = 0 := hx
      rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul, hx', smul_zero]
    exact hx0 ((smul_eq_zero.1 h).resolve_left hn)
  have : Module.FinitePresentation (𝓞 E) T.P.D.toPre.X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem be_nonneg (T : UTrait Xo c) (x : T.P.D.toPre.X) : 0 ≤ T.be x x := by
  by_cases hx : x = 0
  · subst hx; simp
  · obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
    fin_cases j
    simpa using hj.le

theorem be_bal (T : UTrait Xo c) : T.be ∈ balForms (H.bar : 𝓞 E → 𝓞 E) T.P.D.toPre.X := by
  rw [balForms_eq_levelForms]; exact T.lev

theorem evalZ_prop {φ : InvFun (𝓞 E)} (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) (T T' : UTrait Xo c)
    (e : T.P.D.toPre.X ≃ₗ[𝓞 E] T'.P.D.toPre.X) (m s : ℕ) (he : ∀ a b, (m : ℤ) * T'.be (e a) (e b) = s * T.be a b) :
    (m : ℝ) * φ.evalZ T'.be = s * φ.evalZ T.be := by
  haveI := finite_lat T
  haveI := projective_lat T
  haveI := finite_lat T'
  have hon := hφ T.P.D.toPre.X (GlobalTheory.T.character_group_finrank_le_min_signature_unitary_trait E H Dw l Xo c T)
  have hc := toReal_mem_psdCone_of_nonneg E H _ T.be (be_bal T) (be_nonneg T)
  have hc' := toReal_mem_psdCone_of_nonneg E H _ (pull e.toLinearMap T'.be) (pull_mem _ (be_bal T'))
    (fun x => be_nonneg T' (e x))
  rw [← evalR_toReal φ T.be, ← hon.homog _ hc s s.cast_nonneg,
    ← evalZ_pull φ (r := e.toLinearMap) e.surjective, ← evalR_toReal, ← hon.homog _ hc' m m.cast_nonneg]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h

end GlobalTheory.UPoinc.AllTraits

open GlobalTheory.UPoinc.AllTraits in

theorem GlobalTheory.UPoinc.AllTraits.orders_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (ι : ℕ) (D : GlobalTheory.EffCartierData Y.Z), (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ Y U₀ EE out πY hAdm hEE hHom ι D hD hgen
  intro W _ _ _ hW ϖ hϖ χ y hy _ t tK h1 h2 P be hbe hmono
  let T₀ : UTrait Xo c :=
    { V := W, cdvr := hW, ϖ := ϖ, irr := hϖ, y := y, t := t, gen := ⟨tK, h1, h2⟩, P := P, be := be, lev := hbe, mono := hmono }
  haveI : IsDiscreteValuationRing W := hW.1
  haveI : IsDedekindDomain X₁.o₁ := ArithBase.ded X₁.Ω₁
  haveI := Y.lft
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have hWc : IsAdicComplete (maximalIdeal W) W := hW.2.1
  obtain ⟨R, _, _, _, j, Λ, _, _, p, c₀, hRn, hRc, hj, hc, hper⟩ :=
    localPeriods E H Dw hpq l Xo c C X₁ Y U₀ EE out πY hAdm hEE hHom (χ (closedPoint W))
  obtain ⟨jinj, jloc, jext⟩ := isCpl_props hj
  obtain ⟨ψ, ψloc, hψ⟩ := jext W hWc (Scheme.stalkClosedPointTo χ).hom inferInstance
  have hξ : spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk (χ (closedPoint W)) = χ := by
    rw [hψ]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ
  obtain ⟨d, hd⟩ : ∃ d, FinalTheorems.stalkId D.idealSheaf (χ (closedPoint W)) = Ideal.span {d} := by
    obtain ⟨i, hi⟩ := D.exists_mem (χ (closedPoint W))
    exact ⟨_, D.stalkId_idealSheaf i _ hi⟩
  have hid : idlAlong D.idealSheaf χ = Ideal.span {ψ (j d)} := by
    rw [idlAlong, hd, Ideal.map_span, Set.image_singleton, ← hψ]
    rfl
  have hnot : (jK W ≫ χ) (closedPoint (FractionRing W)) ∉ D.idealSheaf.support := by
    intro hs
    refine hD _ hs ⟨y (closedPoint (FractionRing W)), ?_⟩
    exact congrArg (fun f => f.base (closedPoint (FractionRing W))) hy
  have hne := idlAlong_ne_bot D.idealSheaf χ hnot
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  refine ⟨a, ?_, ha⟩
  have hda : Associated (ψ (j d)) (ϖ ^ a) := Ideal.span_singleton_eq_span_singleton.1 (hid.symm.trans ha)
  obtain ⟨e, he⟩ := hper T₀ ψ ψloc (by rw [hξ]; exact hy)
  choose k hk hk' using he
  haveI := T₀.P.D.toPre.finX
  obtain ⟨N, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := T₀.P.D.toPre.X)
  obtain ⟨A, _, _, _, ϖ', ψ', m, m', k', hA, hϖ', ψ'inj, ψ'loc, hm, hm', hk''⟩ :=
    GlobalTheory.PropDvr.exists_cdvr_proportional R W ϖ hϖ ψ ψloc (Option (Fin N × Fin N))
      (fun i => i.elim (j d) fun ii => p (e.symm (b ii.1 + b ii.2)))
      (fun i => i.elim a fun ii => k (e.symm (b ii.1 + b ii.2)))
      (by rintro (_ | ii); exacts [hda, hk' _])
  haveI : CharZero A := (RingHom.charZero_iff ψ'inj).1 hRc
  haveI := jloc
  haveI := ψ'loc
  obtain ⟨T', f, finj, floc, hthru, hyC⟩ := traitThroughOpen E H Dw hpq l Xo c C X₁ Y U₀ EE out πY hAdm hEE hHom
    (χ (closedPoint W)) A hA (ψ'.comp j) (ψ'inj.comp jinj) inferInstance
  haveI := floc
  haveI : IsDiscreteValuationRing T'.V := T'.cdvr.1
  obtain ⟨e', he'⟩ := hper T' (f.comp ψ') inferInstance (by rw [RingHom.comp_assoc]; exact hyC)
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    ((map_ne_zero_iff f finj).2 hϖ'.ne_zero) T'.irr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hr
    exact hϖ'.not_isUnit ((isUnit_map_iff f ϖ').1 (associated_one_iff_isUnit.1 hr))
  have hpow : ∀ {x : A} {n : ℕ}, Associated x (ϖ' ^ n) → Associated (f x) (T'.ϖ ^ (r * n)) := by
    intro x n h
    have h1 := h.map f
    rw [map_pow] at h1
    rw [pow_mul]
    exact h1.trans hr.pow_pow
  obtain ⟨a', ha', hid'⟩ := hgen T' _ hthru
  rw [GlobalTheory.TraitStalk.idlAlong_spMap_fromSpecStalk _ _ _ _ _ inferInstance, hd, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_eq_span_singleton] at hid'
  have h0 := hk'' none
  have ea : a' = r * k' none := pow_exp_eq T'.irr (hid'.symm.trans (hpow h0.1))
  have h02 : m * k' none = m' * a := h0.2
  let Eq' := e.symm.trans e'
  have hz := form_eq_zero ((m : ℤ) • pull Eq'.toLinearMap T'.be - ((m' * r : ℕ) : ℤ) • T₀.be)
    (fun x z => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, pull_apply]
      rw [T₀.lev.1 x z, T'.lev.1]) b hb (fun i i' => by
      obtain ⟨n, hl, hl'⟩ := he' (e.symm (b i + b i'))
      obtain ⟨h1, h2⟩ := hk'' (some (i, i'))
      have h3 : n = r * k' (some (i, i')) := pow_exp_eq T'.irr (hl'.symm.trans (hpow h1))
      have h4 := hk (e.symm (b i + b i'))
      rw [e.apply_symm_apply] at h4
      have h5 : (m : ℤ) * k' (some (i, i')) = m' * k (e.symm (b i + b i')) := by exact_mod_cast h2
      have hc0 : (c₀ : ℤ) ≠ 0 := by omega
      change (m : ℤ) * T'.be (e' (e.symm (b i + b i'))) (e' (e.symm (b i + b i'))) -
        ((m' * r : ℕ) : ℤ) * T₀.be (b i + b i') (b i + b i') = 0
      refine mul_left_cancel₀ hc0 ?_
      rw [h3] at hl
      push_cast at hl ⊢
      linear_combination (-(m : ℤ)) * hl + r * h5 + m' * r * h4)
  have hev : (m : ℝ) * φ.evalZ T'.be = ((m' * r : ℕ) : ℝ) * φ.evalZ be := evalZ_prop hφ T₀ T' Eq' m (m' * r) fun x z =>
    sub_eq_zero.1 (congrArg (fun B : LinearMap.BilinForm ℤ T₀.P.D.toPre.X => B x z) hz)
  have h02' : (m : ℝ) * k' none = m' * a := by exact_mod_cast h02
  have hmr : ((m' : ℝ) * r) ≠ 0 := by
    have : m' ≠ 0 := by omega
    positivity
  refine mul_left_cancel₀ hmr ?_
  rw [ea] at ha'
  push_cast at ha' hev
  linear_combination (-(r : ℝ)) * h02' + m * ha' + ι * hev
