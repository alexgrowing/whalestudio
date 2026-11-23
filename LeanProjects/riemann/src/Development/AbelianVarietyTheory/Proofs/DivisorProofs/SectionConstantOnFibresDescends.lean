import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.EvNatPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricPointOfFaithfullyFlatFiniteTyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescentGeometricPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFiniteEtaleSurjectionTestRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleGoodCoverLevelMapStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverDesc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem exists_lift_pt : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
    Algebra.FiniteType A B → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k),
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := GlobalTheory.T.exists_lift_geometricPoint_of_faithfullyFlat_finiteType

theorem exists_eq_of_geom : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A] [IsJacobsonRing A],
    Module.FaithfullyFlat A B → Algebra.Etale A B → ∀ b : B,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ ψ : B →+* k), φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) →
      φ b = ψ b) → ∃ a : A, algebraMap A B a = b := GlobalTheory.T.etale_faithfullyFlat_descent_geometric_points

theorem exists_etale_lift : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := GlobalTheory.T.exists_lift_finiteEtaleSurjection_testRing

theorem exists_good_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev →
    ∃ (Z : Scheme.{0}) (π : Z ⟶ Xo.XF c) (z₂ : Z ⟶ d.Xo₂.X), IsFinite π ∧ Etale π ∧ Surjective π ∧
      z₂ ≫ d.r = π ≫ pullback.fst _ _ ∧
      z₂ ≫ d.Xo₂.s = π ≫ pullback.snd _ _ ≫
        spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) := GlobalTheory.T.exists_finiteEtale_goodCover_levelMap

end GlobalTheory.CoverDesc

namespace GlobalTheory.CoverDesc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev algAbove (d : DeltaDat Xo c 0) (S : Type) [CommRing S] [Algebra c.F S] : Algebra d.c₂.F S :=
  ((algebraMap c.F S).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra

theorem algAbove_compat (d : DeltaDat Xo c 0) (S : Type) [CommRing S] [Algebra c.F S] :
    letI := algAbove d S
    ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a := by
  intro a
  show algebraMap c.F S (d.eF.symm (d.eF a)) = _
  rw [AlgEquiv.symm_apply_apply]

def Val (d : DeltaDat Xo c 0) (g : Rul d.Xo₂ d.c₂) (p : TRing c.F) (y : FrPt Xo c p.R) (v : p.R) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (φ : p.R →ₐ[c.F] k) (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap φ y z → FrOver d z₂ z →
      φ v = evR d.Xo₂ d.c₂ g z₂

def Lifts (d : DeltaDat Xo c 0) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ y : FrPt Xo c k, ∃ y₂ : FrPt d.Xo₂ d.c₂ k, FrOver d y₂ y

theorem val_unique (d : DeltaDat Xo c 0) (hL : Lifts d) {g : Rul d.Xo₂ d.c₂} {p : TRing c.F} {y : FrPt Xo c p.R}
    {v v' : p.R} (h : Val d g p y v) (h' : Val d g p y v') : v = v' := by
  by_contra hne
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  haveI : IsJacobsonRing p.R := inferInstance
  have hJ : (⊥ : Ideal p.R).jacobson = ⊥ :=
    IsJacobsonRing.out ‹_› (fun x ⟨m, hm⟩ => Ideal.mem_bot.2 (IsNilpotent.eq_zero ⟨m, Ideal.mem_bot.1 hm⟩))
  have hn : v - v' ∉ (⊥ : Ideal p.R).jacobson := by
    rw [hJ]
    exact fun h₀ => hne (sub_eq_zero.1 (Ideal.mem_bot.1 h₀))
  rw [Ideal.jacobson, Ideal.mem_sInf] at hn
  push Not at hn
  obtain ⟨m, ⟨-, hm⟩, ha⟩ := hn
  haveI := hm
  letI := Ideal.Quotient.field m
  let χ : p.R →ₐ[c.F] AlgebraicClosure (p.R ⧸ m) :=
    (IsScalarTower.toAlgHom c.F (p.R ⧸ m) (AlgebraicClosure (p.R ⧸ m))).comp (Ideal.Quotient.mkₐ c.F m)
  letI := algAbove d (AlgebraicClosure (p.R ⧸ m))
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ χ y
  obtain ⟨z₂, hz₂⟩ := hL _ (algAbove_compat d _) z
  have e := (h _ (algAbove_compat d _) χ z z₂ hz hz₂).trans (h' _ (algAbove_compat d _) χ z z₂ hz hz₂).symm
  apply ha
  have e' : algebraMap (p.R ⧸ m) (AlgebraicClosure (p.R ⧸ m)) (Ideal.Quotient.mk m (v - v')) = 0 := by
    have : χ (v - v') = 0 := by rw [map_sub, e, sub_self]
    exact this
  exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (algebraMap _ _).injective).1 e')

end GlobalTheory.CoverDesc

namespace GlobalTheory.CoverDesc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def ptF {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by rw [y.x_over, sOf, ← Spec.map_comp]; rfl)

theorem sOf_cover (d : DeltaDat Xo c 0) (p q : TRing c.F) (ι : p.R →ₐ[c.F] q.R) :
    letI := algAbove d q.R
    spMap ι.toRingHom ≫ spMap (algebraMap c.F p.R) ≫
      spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) = sOf d.c₂ q.R := by
  letI := algAbove d q.R
  simp only [sOf, spMap, ← Spec.map_comp]
  congr 1
  ext t
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  exact ι.commutes _

variable (d : DeltaDat Xo c 0) (hpq : 1 ≤ Dw.p + Dw.q) (hl : d.IsLev)

include hpq hl in
theorem val_exists {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul d.Xo₂ d.c₂} (hg : g ∈ sec d.Xo₂ d.c₂ a n)
    (hF : GlobalTheory.LevPull.FibConst d g) (p : TRing c.F) (y : FrPt Xo c p.R) : ∃ v, Val d g p y v := by
  obtain ⟨Z, π, z₂, hfin, het, hsur, hr, hs⟩ := exists_good_cover E H Dw l Xo c d hpq hl
  obtain ⟨q, ι, ⟨hff, het'⟩, z, hz⟩ := exists_etale_lift _ _ π hfin het hsur c.F p (ptF y)
  letI := algAbove d q.R
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  haveI : IsReduced q.R := (Ideal.isRadical_iff_quotient_reduced q.I).1 q.rad
  have e1 : (z ≫ z₂) ≫ d.r = spMap ι.toRingHom ≫ y.x := by
    rw [Category.assoc, hr, ← Category.assoc, hz, Category.assoc, ptF, pullback.lift_fst]
  have e2 : (z ≫ z₂) ≫ d.Xo₂.s = sOf d.c₂ q.R := by
    rw [Category.assoc, hs, ← Category.assoc, hz, Category.assoc, ptF, pullback.lift_snd_assoc]
    exact sOf_cover d p q ι
  obtain ⟨y', hy'⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ ι y
  obtain ⟨y₂, -, hy₂⟩ := GlobalTheory.FrameLift.exists_frOver d (algAbove_compat d q.R) y' (z ≫ z₂) (e1.trans hy'.1.symm) e2
  have hN₂ := ReciprocityTheory.ChartRestriction.G.PullbackSections.evNat_of d.Xo₂ d.c₂ (GlobalTheory.TransferCompare.evalWD_framed d.Xo₂ d.c₂)
    (GlobalTheory.TransferCompare.allTest_framed d.Xo₂ d.c₂) g hg.1
  letI : Algebra p.R q.R := ι.toRingHom.toAlgebra
  haveI : IsScalarTower c.F p.R q.R := IsScalarTower.of_algebraMap_eq fun t => (ι.commutes t).symm
  obtain ⟨v, hv⟩ := exists_eq_of_geom p.R q.R hff het' (evR d.Xo₂ d.c₂ g y₂) (by
    intro k _ _ φ ψ hφψ
    letI : Algebra c.F k := (φ.comp (algebraMap c.F q.R)).toAlgebra
    letI := algAbove d k
    have hc : ∀ t : c.F, ψ (algebraMap c.F q.R t) = φ (algebraMap c.F q.R t) := fun t => by
      rw [IsScalarTower.algebraMap_apply c.F p.R q.R, ← RingHom.comp_apply, ← hφψ, RingHom.comp_apply]
    let φ' : q.R →ₐ[c.F] k := { φ with commutes' := fun _ => rfl }
    let ψ' : q.R →ₐ[c.F] k := { ψ with commutes' := fun t => hc t }
    let φ₂ : q.R →ₐ[d.c₂.F] k := { φ with commutes' := fun _ => rfl }
    let ψ₂ : q.R →ₐ[d.c₂.F] k := { ψ with commutes' := fun t => hc _ }
    obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ' y'
    obtain ⟨w', hw'⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ ψ' y'
    obtain ⟨w₂, hw₂⟩ := GlobalTheory.TransferCompare.frBC_framed d.Xo₂ d.c₂ _ _ φ₂ y₂
    obtain ⟨w₂', hw₂'⟩ := GlobalTheory.TransferCompare.frBC_framed d.Xo₂ d.c₂ _ _ ψ₂ y₂
    have o₁ : FrOver d w₂ w := GlobalTheory.FrameLift.frOver_map d (ψ := φ') (ψ₂ := φ₂) rfl hy₂ hw hw₂
    have o₂ : FrOver d w₂' w' := GlobalTheory.FrameLift.frOver_map d (ψ := ψ') (ψ₂ := ψ₂) rfl hy₂ hw' hw₂'
    have t₁ := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ι φ' hy' hw
    have t₂ := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ι ψ' hy' hw'
    have ec : ψ'.comp ι = φ'.comp ι := AlgHom.ext fun t => (RingHom.congr_fun hφψ t).symm
    rw [ec] at t₂
    obtain rfl : w = w' := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ (φ'.comp ι) y).1 w w' t₁ t₂
    have k₁ := hN₂ q.R k φ₂ y₂ w₂ hw₂
    have k₂ := hN₂ q.R k ψ₂ y₂ w₂' hw₂'
    have k₃ := hF k (algAbove_compat d k) w₂ w₂' w o₁ o₂
    exact k₁.symm.trans (k₃.trans k₂))
  refine ⟨v, fun k _ _ _ _ hk φ zz zz₂ hzz hzz₂ => ?_⟩
  have hft : Algebra.FiniteType p.R q.R := by haveI := het'; infer_instance
  obtain ⟨φ₁, hφ₁⟩ := exists_lift_pt p.R q.R hff hft k φ.toRingHom
  have hc : ∀ t : c.F, φ₁ (algebraMap c.F q.R t) = algebraMap c.F k t := fun t => by
    rw [IsScalarTower.algebraMap_apply c.F p.R q.R, ← RingHom.comp_apply, hφ₁]
    exact φ.commutes t
  let φ' : q.R →ₐ[c.F] k := { φ₁ with commutes' := hc }
  have hc₂ : ∀ t : d.c₂.F, φ₁ (algebraMap d.c₂.F q.R t) = algebraMap d.c₂.F k t := fun t => by
    show φ₁ (algebraMap c.F q.R (d.eF.symm t)) = _
    rw [hc, ← hk, AlgEquiv.apply_symm_apply]
  let φ₂ : q.R →ₐ[d.c₂.F] k := { φ₁ with commutes' := hc₂ }
  obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ' y'
  obtain ⟨w₂, hw₂⟩ := GlobalTheory.TransferCompare.frBC_framed d.Xo₂ d.c₂ _ _ φ₂ y₂
  have o₁ : FrOver d w₂ w := GlobalTheory.FrameLift.frOver_map d (ψ := φ') (ψ₂ := φ₂) rfl hy₂ hw hw₂
  have t₁ := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ι φ' hy' hw
  have ec : φ'.comp ι = φ := AlgHom.ext fun t => RingHom.congr_fun hφ₁ t
  rw [ec] at t₁
  obtain rfl : w = zz := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ φ y).1 w zz t₁ hzz
  have k₁ := hN₂ q.R k φ₂ y₂ w₂ hw₂
  have k₃ := hF k hk w₂ zz₂ w o₁ hzz₂
  rw [← k₃, k₁, ← hv]
  exact (RingHom.congr_fun hφ₁ v).symm

end GlobalTheory.CoverDesc

namespace GlobalTheory.CoverDesc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem lifts_of_isLev (d : DeltaDat Xo c 0) (hl : d.IsLev) : Lifts d := by
  obtain ⟨-, -, -, -, -, -, hlift, -, -⟩ := hl
  exact hlift

open Classical in

def ruleDown (d : DeltaDat Xo c 0) (g : Rul d.Xo₂ d.c₂) : Rul Xo c := fun p y =>
  if h : ∃ v, Val d g p y v then h.choose else 0

variable (d : DeltaDat Xo c 0) (hpq : 1 ≤ Dw.p + Dw.q) (hl : d.IsLev)

include hpq hl in
theorem val_ruleDown {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul d.Xo₂ d.c₂} (hg : g ∈ sec d.Xo₂ d.c₂ a n)
    (hF : GlobalTheory.LevPull.FibConst d g) (p : TRing c.F) (y : FrPt Xo c p.R) : Val d g p y (ruleDown d g p y) := by
  have h := val_exists d hpq hl hg hF p y
  have e : ruleDown d g p y = h.choose := dif_pos h
  rw [e]
  exact h.choose_spec

include hpq hl in
theorem ruleDown_mem {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul d.Xo₂ d.c₂} (hg : g ∈ sec d.Xo₂ d.c₂ a n)
    (hF : GlobalTheory.LevPull.FibConst d g) : ruleDown d g ∈ sec Xo c a n := by
  have hV := val_ruleDown d hpq hl hg hF
  have hL := lifts_of_isLev d hl
  refine ⟨fun p q φ y z hz => ?_, fun p t y y' hb => ?_⟩
  · refine val_unique d hL (hV q z) fun k _ _ _ _ hk χ w w₂ hw hw₂ => ?_
    have := hV p y k hk (χ.comp φ) w w₂ (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ χ hz hw) hw₂
    rw [← this, AlgHom.comp_apply]
  · refine val_unique d hL (hV p y') fun k _ _ _ _ hk φ z' z₂' hz' hz₂' => ?_
    obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ y
    have hbz := frBorBC (Xo := Xo) (c := c) p.R k φ t y y' z z' hb hz hz'
    obtain ⟨z₂, hz₂⟩ := hL k hk z
    have ex : z₂.x ≫ d.r = z'.x := by rw [hbz.1, ((GlobalTheory.FrameLift.frOver_iff d _ _).1 hz₂).1]
    obtain ⟨z₂'', hx'', hz₂''⟩ := GlobalTheory.FrameLift.exists_frOver d hk z' z₂.x ex z₂.x_over
    have hb₂ := GlobalTheory.FrameLift.frBor_lift d GlobalTheory.abelianSchemeLaws_all.1.globalFns hz₂ hz₂'' hx'' hbz
    have w₁ := GlobalTheory.CoverSec.wtRed d.Xo₂ d.c₂ a n g hg k _ z₂ z₂'' hb₂
    have w₂ := hF k hk z₂' z₂'' z' hz₂' hz₂''
    have w₃ := hV p y k hk φ z z₂ hz hz₂
    rw [w₂, w₁, ← w₃, map_mul]
    congr 1
    simp only [wchar, map_prod, map_pow, Units.coe_map, MonoidHom.coe_coe]

end GlobalTheory.CoverDesc

section Main

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem GlobalTheory.CoverDesc.section_descends :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec d.Xo₂ d.c₂ a n, FibConst d g → ∃ f ∈ sec Xo c a n, Pull d f g := by
  intro E _ _ _ H Dw l Xo c d hpq hl a n g hg hF
  have hm := GlobalTheory.CoverDesc.ruleDown_mem d hpq hl hg hF
  refine ⟨_, hm, fun k _ _ _ _ hk y₂ y ho => ?_⟩
  obtain ⟨p, φ, y₀, hy₀⟩ := GlobalTheory.TransferCompare.allTest_framed Xo c k y
  rw [GlobalTheory.FlatLine.evR_of_frMap_test hm.1 hy₀]
  exact (GlobalTheory.CoverDesc.val_ruleDown d hpq hl hg hF p y₀ k hk φ y y₂ hy₀ ho).symm

end Main
