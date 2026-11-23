import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.RayContainment
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ShortSpanUnitOfExactValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjectiveOfLaws
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverPinCompare

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.RayContainment
open GlobalTheory.ClsVal.Cmp (OverBase overBase_of_ne eq_incl coe_incl spMap_comp')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem nonempty_lift {K L : Type} [Field K] [Field L] [Algebra K L] [Algebra K ℂ] [Module.Finite K L] :
    Nonempty (L →ₐ[K] ℂ) := ⟨IsAlgClosed.lift⟩

theorem exists_algHom_ker {K : Type} [Field K] (σ : K →+* ℂ) (p : TRing K) (m : Ideal p.R) [hm : m.IsMaximal] :
    ∃ ψ : p.R →ₐ[K] CAt σ, ∀ x, ψ x = 0 ↔ x ∈ m := by
  letI : Algebra K ℂ := σ.toAlgebra
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K _
  obtain ⟨j⟩ := nonempty_lift (K := K) (L := p.R ⧸ m)
  refine ⟨(j.comp (Ideal.Quotient.mkₐ K m) : p.R →ₐ[K] ℂ), fun x => ?_⟩
  exact (map_eq_zero_iff j j.toRingHom.injective).trans Ideal.Quotient.eq_zero_iff_mem

theorem ne_zero_of_complex (σ : c.F →+* ℂ) {f : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {w : ℕ} (hf : f ∈ sec Xo c a w)
    (h : ∀ y : FrPt Xo c (CAt σ), evR Xo c f y ≠ 0) (k : Type) [Field k] [Algebra c.F k] (y : FrPt Xo c k) :
    evR Xo c f y ≠ 0 := by
  have hB := GlobalTheory.firstFiveLaws.1.secBaseChange
  obtain ⟨p, φ, y₀, hy⟩ := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c k y
  rw [GlobalTheory.ShortSpanCompare.evR_of_frMap hf φ hy]
  intro h0
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (RingHom.ker φ.toRingHom) (RingHom.ker_ne_top _)
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker σ p m
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ ψ y₀
  exact h z ((GlobalTheory.ShortSpanCompare.evR_of_frMap hf ψ hz).trans ((hψ _).2 (hle h0)))

theorem eq_of_complex (σ : c.F →+* ℂ) {f f' : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {w : ℕ} (hf : f ∈ sec Xo c a w)
    (hf' : f' ∈ sec Xo c a w) (h : ∀ y : FrPt Xo c (CAt σ), evR Xo c f y = evR Xo c f' y) : f = f' := by
  funext p y
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  haveI : IsJacobsonRing p.R := isJacobsonRing_of_finiteType (A := c.F)
  have hj : (⊥ : Ideal p.R).jacobson = ⊥ := IsJacobsonRing.out inferInstance (Ideal.isRadical_bot)
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker σ p m
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c _ _ ψ y
  rw [← hψ, map_sub, ← GlobalTheory.ShortSpanCompare.evR_of_frMap hf ψ hz, ← GlobalTheory.ShortSpanCompare.evR_of_frMap hf' ψ hz, h, sub_self]

def XiValues (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (𝔣 : Ideal (𝓞 E)) (xi : Ideal (𝓞 E) →*₀ c.F) : Prop :=
  (∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H Dw.p Dw.q ty ∧
    Nonempty (FamilyUnif d.Xo₂ ((embCov d σ).comp (IntermediateField.inclusion d.c₂.le).toRingHom) ty)) ∧
  ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H Dw.p Dw.q ty →
    ∀ (U : FamilyUnif d.Xo₂ ((embCov d σ).comp (IntermediateField.inclusion d.c₂.le).toRingHom) ty) (i : Fin U.n),
      (∃ 𝔠, DetIdeal Dw (U.Di i) d.l₂ (U.t i) 𝔣 𝔠) ∧
      ∀ 𝔠, DetIdeal Dw (U.Di i) d.l₂ (U.t i) 𝔣 𝔠 →
        ∀ P, IsPeriod (U.Di i) ty P → ∀ y : FrPt d.Xo₂ d.c₂ (CAt (embCov d σ)), y.x = U.u i P →
          toC (evR d.Xo₂ d.c₂ d.cδ y) = σ (xi 𝔠)

theorem isXiDet_iff (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (𝔣 : Ideal (𝓞 E)) (xi : Ideal (𝓞 E) →*₀ c.F) :
    IsXiDet d σ 𝔣 xi ↔ d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 ∧ XiValues d σ 𝔣 xi := Iff.rfl

theorem twist_ne_zero {Q : Finset (Ideal (𝓞 E))} {K : Type} [Field K] {xi : Ideal (𝓞 E) →*₀ K} (h : IsTwist H Q xi)
    {𝔠 : Ideal (𝓞 E)} (h0 : 𝔠 ≠ ⊥) (h1 : 𝔠 ⊔ modulus H Q = ⊤) : xi 𝔠 ≠ 0 := by
  obtain ⟨a, ha, ha0, ha1⟩ : ∃ a ∈ 𝔠, a ≠ 0 ∧ a - 1 ∈ modulus H Q := by
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h1)
    by_cases ha0 : a = 0
    · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
      rw [ha0, zero_add] at hab
      exact ⟨x, hx, hx0, by rw [← mul_one (x - 1), ← hab]; exact Ideal.mul_mem_left _ _ hb⟩
    · exact ⟨a, ha, ha0, by rw [← hab]; simpa using hb⟩
  obtain ⟨𝔡, h𝔡⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ha)
  intro e
  have := h.2.1 a ha0 ha1
  rw [h𝔡, map_mul, e, zero_mul] at this
  exact zero_ne_one this

theorem exists_value {d : DeltaDat Xo c n} {σ : c.F →+* ℂ} {𝔣 : Ideal (𝓞 E)} {xi : Ideal (𝓞 E) →*₀ c.F}
    (h : XiValues d σ 𝔣 xi) (y : FrPt d.Xo₂ d.c₂ (CAt (embCov d σ))) :
    ∃ 𝔠, 𝔠 ≠ ⊥ ∧ 𝔠 ⊔ 𝔣 = ⊤ ∧ ∀ f : Rul d.Xo₂ d.c₂, XiValues { d with cδ := f } σ 𝔣 xi →
      toC (evR d.Xo₂ d.c₂ f y) = σ (xi 𝔠) := by
  obtain ⟨⟨g, ty, hty, ⟨U⟩⟩, h⟩ := h
  obtain ⟨i, P, hP, hx⟩ := U.onto y.x y.x_over
  obtain ⟨𝔠, h𝔠⟩ := (h g ty hty U i).1
  exact ⟨𝔠, h𝔠.1, h𝔠.2.1, fun f hf => (hf.2 g ty hty U i).2 𝔠 h𝔠 P hP y hx.symm⟩

theorem isXiDet_ne_zero {d : DeltaDat Xo c n} {σ : c.F →+* ℂ} {Q : Finset (Ideal (𝓞 E))}
    {xi : Ideal (𝓞 E) →*₀ c.F} (hxi : IsTwist H Q xi) (h : IsXiDet d σ (modulus H Q) xi)
    (k : Type) [Field k] [Algebra d.c₂.F k] (y : FrPt d.Xo₂ d.c₂ k) : evR d.Xo₂ d.c₂ d.cδ y ≠ 0 := by
  refine ne_zero_of_complex (embCov d σ) h.1 (fun z e => ?_) k y
  obtain ⟨𝔠, h0, h1, hv⟩ := exists_value h.2 z
  have := hv d.cδ h.2
  rw [e] at this
  exact twist_ne_zero hxi h0 h1 ((map_eq_zero σ).1 this.symm)

theorem isXiDet_unique {d : DeltaDat Xo c n} {σ : c.F →+* ℂ} {𝔣 : Ideal (𝓞 E)} {xi : Ideal (𝓞 E) →*₀ c.F}
    (h : IsXiDet d σ 𝔣 xi) (f : Rul d.Xo₂ d.c₂) (hf : IsXiDet { d with cδ := f } σ 𝔣 xi) : f = d.cδ := by
  refine eq_of_complex (embCov d σ) hf.1 h.1 fun z => ?_
  obtain ⟨𝔠, -, -, hv⟩ := exists_value h.2 z
  exact (hv f hf.2).trans (hv d.cδ h.2).symm

theorem nonempty_frPt {d : DeltaDat Xo c n} {σ : c.F →+* ℂ} {𝔣 : Ideal (𝓞 E)} {xi : Ideal (𝓞 E) →*₀ c.F}
    (h : XiValues d σ 𝔣 xi) : letI := (embCov d σ).toAlgebra; Nonempty (FrPt d.Xo₂ d.c₂ ℂ) := by
  letI := (embCov d σ).toAlgebra
  obtain ⟨⟨g, ty, hty, ⟨U⟩⟩, -⟩ := h
  let i : Fin U.n := ⟨0, U.n_pos⟩
  obtain ⟨P, hP⟩ := GlobalTheory.PeriodNonempty.exists_isPeriod E H (U.Di i) g ty (by rw [(U.sig i).1, (U.sig i).2]; exact hty)
  obtain ⟨y, -⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (c := d.c₂) (S := ℂ) (U.u i P) (U.over_σ i P hP)
  exact ⟨y⟩

def Lifts (d : DeltaDat Xo c n) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ y : FrPt Xo c k, ∃ y₂ : FrPt d.Xo₂ d.c₂ k, FrOver d y₂ y

theorem dvd_of_level {d : DeltaDat Xo c n} (hM : d.l₂.M = l.M * d.pd) (hMb : d.l₂.Mb = l.Mb * d.I)
    (hA : d.l₂.A = l.A) : l.Dvd d.l₂ :=
  ⟨hM ▸ dvd_mul_right _ _, hMb ▸ Ideal.mul_le_left, hA ▸ dvd_rfl⟩

theorem half_sup {d : DeltaDat Xo c n} (hMb : d.l₂.Mb = l.Mb * d.I) :
    d.I ⊔ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ := by
  have h : d.l₂.Mb ≤ d.I := hMb ▸ Ideal.mul_le_right
  exact eq_top_iff.2 (d.l₂.coprime.ge.trans (sup_le_sup h (Ideal.map_mono h)))

theorem isCover_iff (hr : 1 ≤ Dw.p + Dw.q) (d : DeltaDat Xo c n) (N : ℕ) (I : Ideal (𝓞 E)) :
    IsCover d N I ↔ d.pd = N ∧ d.I = I ∧ d.l₂.M = l.M * d.pd ∧ d.l₂.Mb = l.Mb * d.I ∧ d.l₂.A = l.A ∧ OverBase d ∧
      d.EtaOK ∧ Lifts d := by
  constructor
  · rintro ⟨rfl, rfl, h1, h2, h3, ⟨j, hj, h4⟩, h5, -, h6⟩
    exact ⟨rfl, rfl, h1, h2, h3, fun h => by rw [h4, eq_incl h j hj], h5, h6⟩
  · rintro ⟨rfl, rfl, h1, h2, h3, h4, h5, h6⟩
    have hle : KA l ≤ KA d.l₂ := by rw [KA, KA, h3]
    have hdiv : d.l₂.M / l.M = d.pd := by
      rw [h1]; exact Nat.mul_div_cancel_left _ (by have := l.three_le; omega)
    have hw : (pullback.fst _ _ ≫ d.r) ≫ Xo.s =
        (pullback.snd d.Xo₂.s (spMap (IntermediateField.inclusion d.c₂.le).toRingHom) ≫
          spMap (IntermediateField.inclusion d.hF.ge).toRingHom) ≫
            spMap (IntermediateField.inclusion c.le).toRingHom := by
      rw [Category.assoc, h4 hle, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, spMap_comp',
        spMap_comp']
      rfl
    refine ⟨rfl, rfl, h1, h2, h3, ⟨_, coe_incl hle, h4 hle⟩, h5,
      ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩, h6⟩
    exact GlobalTheory.LevCover.levelMap_finite_etale_surjective_of_laws GlobalTheory.firstFiveLaws.1 E H Dw l d.l₂ Xo d.Xo₂ hr
      (dvd_of_level h1 h2 h3) d.r _ d.m ⟨coe_incl hle, h4 hle, by rw [hdiv]; exact h5.1, h5.2⟩ c d.c₂ d.hF.symm _
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem guard_of_isLev {d : DeltaDat Xo c n} (h : d.IsLev) (hA : d.l₂.A = l.A) :
    IsHalf H d.pd d.I ∧ Nat.Coprime d.pd l.M ∧ zeta (Nat.lcm (l.M * d.pd) l.A) ∈ c.F := by
  refine ⟨⟨le_antisymm ?_ (Ideal.span_le.2 fun a ha => ha.1), GlobalTheory.LevelCoverDatum.half_mul_conj d h, h.2.2.2.2.1⟩,
    h.2.2.1, ?_⟩
  · have e := GlobalTheory.LevelCoverCompare.half_eq h.2.1 h.2.2.1 h.2.2.2.1
    refine e.ge.trans (sup_le (d.l₂.fromK.le.trans (Ideal.span_mono fun a ha => ⟨e.le (Ideal.mem_sup_left ha.1), ha.2⟩))
      (Ideal.span_mono ?_))
    rintro _ rfl
    exact ⟨e.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)), Subalgebra.natCast_mem _ _⟩
  · have := d.c₂.zeta_mem
    rwa [Level.M', h.2.1, hA, d.hF] at this

theorem isNab_iff_exists [s : StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a) (nab : NabV Xo c) :
    IsNab Xo c nab ↔ ∃ _ : StarRing (𝓞 E), IsNab Xo c nab := by
  refine ⟨fun h => ⟨s, h⟩, fun ⟨s', h⟩ => ?_⟩
  have : s' = s := by
    have h1 : s'.star = s.star := (funext h.1).trans (funext hs).symm
    obtain @⟨@⟨@⟨⟨f⟩, _⟩, _⟩, _⟩ := s
    obtain @⟨@⟨@⟨⟨f'⟩, _⟩, _⟩, _⟩ := s'
    cases h1
    rfl
  exact this ▸ h

section Pins

variable [StarRing (𝓞 E)]

theorem coverPin_iff (hs : ∀ a : 𝓞 E, star a = H.bar a) (hr : 1 ≤ Dw.p + Dw.q) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ)
    {Q : Finset (Ideal (𝓞 E))} {xi : Ideal (𝓞 E) →*₀ c.F} (hxi : IsTwist H Q xi) (I : Ideal (𝓞 E)) :
    (Nat.Coprime (primeUnder Q) l.M ∧ IsPinnedCover₂ d σ Q xi I) ↔
      (d.IsLev ∧ d.l₂.A = l.A ∧ OverBase d ∧ ∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧
        d.pd = primeUnder Q ∧ d.I = I ∧ XiValues d σ (modulus H Q) xi ∧ d.φδ = fun _ => 1 := by
  rw [IsPinnedCover₂, isCover_iff hr, ← isNab_iff_exists hs]
  constructor
  · rintro ⟨h0, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, h9, h10, h11⟩
    exact ⟨⟨⟨dvd_of_level h3 h4 h5, h3, h1 ▸ h0, h4, half_sup h4, h7, h8, h10.1,
      fun k _ _ _ y => isXiDet_ne_zero hxi h10 k y⟩, h5, h6, h9⟩, h1, h2, h10.2, h11⟩
  · rintro ⟨⟨⟨-, h3, h0, h4, -, h7, h8, h10, -⟩, h5, h6, h9⟩, h1, h2, h12, h11⟩
    exact ⟨h1 ▸ h0, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, h9, ⟨h10, h12⟩, h11⟩

omit [StarRing (𝓞 E)] in

theorem level_eq_one {Tup : Type} [Nonempty Tup] {dδ : Tup → DeltaDat Xo c n} (h : CovPin Xo c dδ) : l.A = 1 := by
  obtain ⟨t⟩ := ‹Nonempty Tup›
  exact Nat.dvd_one.1 ((h t).2.1 ▸ (h t).1.1.2.2)

variable {Tup : Type} (σ : c.F →+* ℂ) (Q : Tup → Finset (Ideal (𝓞 E))) (xi : Tup → (Ideal (𝓞 E) →*₀ c.F))
  (I : Tup → Ideal (𝓞 E))

theorem coverPin_iff_covPin (hs : ∀ a : 𝓞 E, star a = H.bar a) (ho : Odd (Dw.p + Dw.q)) (hA : l.A = 1)
    (hg : ∀ t, IsTwist H (Q t) (xi t) ∧ Nat.Coprime (primeUnder (Q t)) l.M) (dδ : Tup → DeltaDat Xo c n) :
    (∀ t, IsPinnedCover₂ (dδ t) σ (Q t) (xi t) (I t)) ↔
      CovPin Xo c dδ ∧ ∀ t, (dδ t).pd = primeUnder (Q t) ∧ (dδ t).I = I t ∧
        XiValues (dδ t) σ (modulus H (Q t)) (xi t) ∧ (dδ t).φδ = fun _ => 1 := by
  have hne : Dw.p ≠ Dw.q := fun e => by obtain ⟨k, hk⟩ := ho; omega
  have key := fun t => coverPin_iff hs ho.pos (dδ t) σ (hg t).1 (I t)
  constructor
  · intro h
    have h' := fun t => (key t).1 ⟨(hg t).2, h t⟩
    exact ⟨fun t => ⟨(h' t).1.1, (h' t).1.2.1.trans hA, (h' t).1.2.2.2⟩, fun t => (h' t).2⟩
  · rintro ⟨h, h'⟩ t
    exact ((key t).2 ⟨⟨(h t).1, (h t).2.1.trans hA.symm, overBase_of_ne hne hA _, (h t).2.2⟩, h' t⟩).2

theorem exists_iff (hs : ∀ a : 𝓞 E, star a = H.bar a) (ho : Odd (Dw.p + Dw.q)) (hA : l.A = 1)
    (hg : ∀ t, IsTwist H (Q t) (xi t) ∧ Nat.Coprime (primeUnder (Q t)) l.M) :
    (∃ dδ : Tup → DeltaDat Xo c n, ∀ t, IsPinnedCover₂ (dδ t) σ (Q t) (xi t) (I t)) ↔
      ∃ dδ : Tup → DeltaDat Xo c n, CovPin Xo c dδ ∧ ∀ t, (dδ t).pd = primeUnder (Q t) ∧ (dδ t).I = I t ∧
        XiValues (dδ t) σ (modulus H (Q t)) (xi t) := by
  constructor
  · rintro ⟨dδ, h⟩
    obtain ⟨h1, h2⟩ := (coverPin_iff_covPin σ Q xi I hs ho hA hg dδ).1 h
    exact ⟨dδ, h1, fun t => ⟨(h2 t).1, (h2 t).2.1, (h2 t).2.2.1⟩⟩
  · rintro ⟨dδ, h1, h2⟩
    exact ⟨fun t => { dδ t with φδ := fun _ => 1 }, (coverPin_iff_covPin σ Q xi I hs ho hA hg _).2
      ⟨h1, fun t => ⟨(h2 t).1, (h2 t).2.1, (h2 t).2.2, rfl⟩⟩⟩

end Pins

set_option synthInstance.maxHeartbeats 200000 in

theorem exists_covPin_not_isXiDet (d : DeltaDat Xo c n) (h : CovPin Xo c fun _ : Unit => d) (σ : c.F →+* ℂ)
    (𝔣 : Ideal (𝓞 E)) (xi : Ideal (𝓞 E) →*₀ c.F) :
    ∃ f : Rul d.Xo₂ d.c₂, CovPin Xo c (fun _ : Unit => { d with cδ := f }) ∧ ¬ XiValues { d with cδ := f } σ 𝔣 xi := by
  by_cases hd : XiValues d σ 𝔣 xi
  · obtain ⟨h1, h2, h3⟩ := h ()
    have h4 := GlobalTheory.LevelCoverDatum.isLev_smul d h1 2 two_ne_zero
    refine ⟨(2 : d.c₂.F) • d.cδ, fun _ => ⟨h4, h2, h3⟩, fun h5 => ?_⟩
    have e := isXiDet_unique ⟨h1.2.2.2.2.2.2.2.1, hd⟩ _ ⟨h4.2.2.2.2.2.2.2.1, h5⟩
    rw [two_smul, add_eq_left] at e
    letI := (embCov d σ).toAlgebra
    obtain ⟨y⟩ := nonempty_frPt hd
    refine h1.2.2.2.2.2.2.2.2 ℂ y ?_
    rw [e]
    exact evalAt_zero _ _ y
  · exact ⟨d.cδ, h, hd⟩

theorem exists_covPin_depth_one (hr : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) :
    ∃ d : DeltaDat Xo c n, CovPin Xo c (fun _ : Unit => d) ∧
      ∀ Q : Finset (Ideal (𝓞 E)), IsPlaceSet H Q → Q.Nonempty → d.pd ≠ primeUnder Q := by
  obtain ⟨d, h1, -, hl, -, -, -, hlev, hs⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev E H Dw l Xo c hr n 1 ⊤ l Xo c rfl
    ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm (top_sup_eq _)
  refine ⟨d, fun _ => ⟨hlev, by rw [hl]; exact hA, hs⟩, fun Q hQ ⟨P, hP⟩ e => ?_⟩
  have : Ideal.absNorm P ∣ primeUnder Q := Finset.dvd_prod_of_mem (fun q => q) (Finset.mem_image_of_mem _ hP)
  rw [← e, h1, Nat.dvd_one] at this
  exact (hQ P hP).2.1.one_lt.ne' this

def CoversExistOverPin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (n : ℕ) (Tup : Type) (Q : Tup → Finset (Ideal (𝓞 E)))
    (xi : Tup → (Ideal (𝓞 E) →*₀ c.F)),
    l.A = 1 → Odd (Dw.p + Dw.q) → GoodEmb c σ → (∀ t, TupleGuard c (Q t) (xi t)) →
      (∀ t, ∃ I, IsHalf H (primeUnder (Q t)) I) ∧
      ∀ I : Tup → Ideal (𝓞 E), (∀ t, IsHalf H (primeUnder (Q t)) (I t)) →
        ∃ dδ : Tup → DeltaDat Xo c n, CovPin Xo c dδ ∧ ∀ t, (dδ t).pd = primeUnder (Q t) ∧ (dδ t).I = I t ∧
          XiValues (dδ t) σ (modulus H (Q t)) (xi t)

theorem exists_star (H : Host E) : ∃ _ : StarRing (𝓞 E), ∀ a : 𝓞 E, star a = H.bar a :=
  ⟨{ star := H.bar
     star_involutive := fun a => Subtype.ext (by
       have := (H.bar_eq (H.bar a)).trans (congrArg _ (H.bar_eq a))
       exact this.trans (IsCMField.complexConj_apply_apply E _))
     star_mul := fun a b => by rw [map_mul, mul_comm]
     star_add := map_add _ }, fun _ => rfl⟩

def CoversExistOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (n : ℕ) (Tup : Type) (Q : Tup → Finset (Ideal (𝓞 E)))
    (xi : Tup → (Ideal (𝓞 E) →*₀ c.F)), l.A = 1 →
    (∀ a : 𝓞 E, star a = H.bar a) → Odd (Dw.p + Dw.q) → GoodEmb c σ → (∀ t, TupleGuard c (Q t) (xi t)) →
      (∀ t, ∃ I, IsHalf H (primeUnder (Q t)) I) ∧
      ∀ I : Tup → Ideal (𝓞 E), (∀ t, IsHalf H (primeUnder (Q t)) (I t)) →
        ∃ dδ : Tup → DeltaDat Xo c n, ∀ t, IsPinnedCover₂ (dδ t) σ (Q t) (xi t) (I t)

theorem coversExistOne_of (h : CoversExist) : CoversExistOne :=
  fun E _ _ _ _ H Dw l Xo c σ n Tup Q xi _ => h E H Dw l Xo c σ n Tup Q xi

theorem coversExistOne_iff : CoversExistOne ↔ CoversExistOverPin := by
  constructor
  · intro h E _ _ _ H Dw l Xo c σ n Tup Q xi hA ho hσ hg
    obtain ⟨s, hs⟩ := exists_star H
    obtain ⟨h1, h2⟩ := h E H Dw l Xo c σ n Tup Q xi hA hs ho hσ hg
    exact ⟨h1, fun I hI => (exists_iff σ Q xi I hs ho hA fun t => ⟨(hg t).2.1, (hg t).2.2.1⟩).1 (h2 I hI)⟩
  · intro h E _ _ _ _ H Dw l Xo c σ n Tup Q xi hA hs ho hσ hg
    obtain ⟨h1, h2⟩ := h E H Dw l Xo c σ n Tup Q xi hA ho hσ hg
    exact ⟨h1, fun I hI => (exists_iff σ Q xi I hs ho hA fun t => ⟨(hg t).2.1, (hg t).2.2.1⟩).2 (h2 I hI)⟩

theorem compare [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ)
    (σ : c.F →+* ℂ) :
    (∀ (Tup : Type) (Q : Tup → Finset (Ideal (𝓞 E))) (xi : Tup → (Ideal (𝓞 E) →*₀ c.F)) (I : Tup → Ideal (𝓞 E)),
      Odd (Dw.p + Dw.q) → l.A = 1 → (∀ t, IsTwist H (Q t) (xi t) ∧ Nat.Coprime (primeUnder (Q t)) l.M) →
      (∀ dδ : Tup → DeltaDat Xo c n, (∀ t, IsPinnedCover₂ (dδ t) σ (Q t) (xi t) (I t)) ↔
        CovPin Xo c dδ ∧ ∀ t, (dδ t).pd = primeUnder (Q t) ∧ (dδ t).I = I t ∧
          XiValues (dδ t) σ (modulus H (Q t)) (xi t) ∧ (dδ t).φδ = fun _ => 1) ∧
      ((∃ dδ : Tup → DeltaDat Xo c n, ∀ t, IsPinnedCover₂ (dδ t) σ (Q t) (xi t) (I t)) ↔
        ∃ dδ : Tup → DeltaDat Xo c n, CovPin Xo c dδ ∧ ∀ t, (dδ t).pd = primeUnder (Q t) ∧ (dδ t).I = I t ∧
          XiValues (dδ t) σ (modulus H (Q t)) (xi t))) ∧
    (∀ (d : DeltaDat Xo c n) (Q : Finset (Ideal (𝓞 E))) (xi : Ideal (𝓞 E) →*₀ c.F) (I : Ideal (𝓞 E)),
      1 ≤ Dw.p + Dw.q → IsTwist H Q xi → ((Nat.Coprime (primeUnder Q) l.M ∧ IsPinnedCover₂ d σ Q xi I) ↔
        (d.IsLev ∧ d.l₂.A = l.A ∧ OverBase d ∧ ∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧
          d.pd = primeUnder Q ∧ d.I = I ∧ XiValues d σ (modulus H Q) xi ∧ d.φδ = fun _ => 1)) ∧
    (∀ d : DeltaDat Xo c n, CovPin Xo c (fun _ : Unit => d) → l.A = 1 ∧
      IsHalf H d.pd d.I ∧ Nat.Coprime d.pd l.M ∧ zeta (Nat.lcm (l.M * d.pd) l.A) ∈ c.F) ∧
    (∀ (d : DeltaDat Xo c n) (𝔣 : Ideal (𝓞 E)) (xi : Ideal (𝓞 E) →*₀ c.F), IsXiDet d σ 𝔣 xi →
      ∀ f : Rul d.Xo₂ d.c₂, IsXiDet { d with cδ := f } σ 𝔣 xi → f = d.cδ) ∧
    (∀ d : DeltaDat Xo c n, CovPin Xo c (fun _ : Unit => d) → ∀ (𝔣 : Ideal (𝓞 E)) (xi : Ideal (𝓞 E) →*₀ c.F),
      ∃ f : Rul d.Xo₂ d.c₂, CovPin Xo c (fun _ : Unit => { d with cδ := f }) ∧
        ¬ XiValues { d with cδ := f } σ 𝔣 xi) ∧
    (1 ≤ Dw.p + Dw.q → l.A = 1 → ∃ d : DeltaDat Xo c n, CovPin Xo c (fun _ : Unit => d) ∧
      ∀ Q : Finset (Ideal (𝓞 E)), IsPlaceSet H Q → Q.Nonempty → d.pd ≠ primeUnder Q) ∧
    (CoversExist → CoversExistOne) ∧ (CoversExistOne ↔ CoversExistOverPin) :=
  ⟨fun _ Q xi I ho hA hg => ⟨coverPin_iff_covPin σ Q xi I hs ho hA hg, exists_iff σ Q xi I hs ho hA hg⟩,
    fun d _ _ I hr hxi => coverPin_iff hs hr d σ hxi I,
    fun _ h => ⟨level_eq_one h, guard_of_isLev (h ()).1 ((h ()).2.1.trans (level_eq_one h).symm)⟩,
    fun _ _ _ h => isXiDet_unique h, fun d h => exists_covPin_not_isXiDet d h σ, exists_covPin_depth_one,
    coversExistOne_of, coversExistOne_iff⟩

end GlobalTheory.CoverPinCompare
