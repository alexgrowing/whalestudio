import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.StandardFourierShortSpan
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MultAddMultConjugate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPowLeHalfPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricLiftsOfFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmAMemSpanShort
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortSpanCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
open GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism hiding IsShortRule shortGen ShortInCusp
open GlobalTheory.GenusLatCompare GlobalTheory.LevelCoverCompare GlobalTheory.ShortDatumEq GlobalTheory.ShortValueCompare GlobalTheory.TransferCompare

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem liesOver_triv {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [i : Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) :
    @Cover.LiesOver _ _ _ _ _ _ _ _ _ _ (Cover.triv Xo c) S T _ _ _ i φ.toRingHom z y ↔ FrMap φ y z := by
  refine ⟨?_, ?_⟩
  · rintro ⟨-, h1, h2, pm, ⟨h3, h4⟩, h5⟩
    have h6 := (ptOver_iff_charts h3 _ 1 z.s y.s).2 h5
    refine ⟨(Category.comp_id _).symm.trans h1, fun τ i => (Category.comp_id _).symm.trans (h2 τ i), pm,
      h3.trans (Category.comp_id _), h4, fun J e => fn_ext fun x hx => ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, J = fun _ => i := ⟨J 0, fin_one_eq J⟩
    have hi : (snd (Over.mk z.x) Xo.univ.t.G).left x ∈ Xo.univ.t.PP.L.U i := Set.mem_iInter.1 hx 0
    refine (gs_appLE pm _ _ e _ x hx _).trans ((h6 _ (𝟙 _) x i i hi hi).trans ?_)
    have := (GlobalTheory.ObjLower.gw_idIso Xo.univ.t.PP.L (𝟙 _ ≫ (snd (Over.mk z.x) Xo.univ.t.G).left) x i i hi hi).trans
      (gm_self Xo.univ.t.PP.isLB _ x hi)
    refine (congrArg (fun u => (u ^ (1 : ℤ)).val * _) this).trans ?_
    rw [one_zpow, Units.val_one]
    exact _root_.one_mul _
  · rintro ⟨k1, k2, pn, k3, k4, k5⟩
    have h3 : pn ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ≫ 𝟙 _ :=
      k3.trans (Category.comp_id _).symm
    refine ⟨φ.comp_algebraMap, (Category.comp_id _).trans k1, fun τ i => (Category.comp_id _).trans (k2 τ i), pn,
      ⟨h3, k4⟩, (ptOver_iff_charts h3 _ 1 z.s y.s).1 fun Z r x i j hi hj => ?_⟩
    have a : r x ∈ (PPx z.x).U fun _ => i := Set.mem_iInter.2 fun _ => hi
    have a' : r x ∈ (PPx z.x).U fun _ => j := Set.mem_iInter.2 fun _ => hj
    have e := ppx_le_cov pn k3 fun _ => i
    refine (gs_appLE pn _ _ e r x a _).symm.trans ((congrArg (gs r x _) (k5 _ e)).trans
      ((gs_compat z.s r x a a').trans (congrArg (fun u : _ˣ => u.val * _) ?_)))
    refine (gm_linComb Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk z.x) Xo.univ.t.G).left) (fun _ => 1) r x _ _
      a a').trans ?_
    rw [Fin.prod_univ_one]
    exact congrArg (· ^ (1 : ℤ)) (GlobalTheory.ObjLower.gw_idIso _ _ x i j hi hj).symm

section Generators

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)

theorem evR_of_frMap {f : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hf : f ∈ sec Xo c a n) {p : TRing c.F}
    {S : Type} [CommRing S] [Algebra c.F S] (φ : p.R →ₐ[c.F] S) {y : FrPt Xo c p.R} {z : FrPt Xo c S}
    (h : FrMap φ y z) : evR Xo c f z = φ (f p y) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact evalWD_framed Xo c f hf.1 S _ _ _ _ _ _ z hT.choose_spec.choose_spec.choose_spec h

variable {Δ}

end Generators

section Spans

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ)

def RamifiedExcluded (bad : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ ramPart E → p ∣ bad * Δ.a.l₂.M

def genAway (s : ℕ+) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul Xo c) :=
  genOn Δ hK (reps Δ n s) (LevelSpanSeparation.Admissible nV) (harmLat Dw c a) a

variable {Δ}

end Spans

section Claims

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ)
  (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))

def SpanOn (Q : ((E →+* ℂ) × ℕ → ℕ) → Prop) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SpanRange Dw l a n → Q a → cusp a n ≤ shortSpanK Δ hK nV a n

def NeZeroOn (Q : ((E →+* ℂ) × ℕ → ℕ) → Prop) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SpanRange Dw l a n → Q a → cusp a n ≠ ⊥ →
    ∃ f ∈ RamifiedCoverPairIsomorphism.shortGen Δ hK nV a n, f ≠ 0

def SameSpans (bad : ℕ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Even n →
    Submodule.span c.F (shortGen Xo c nab bad nV a n (toDat Δ n)) = shortSpanK Δ hK nV a n

variable {Δ hK nV}

end Claims

section Std

variable (Xo c) (nab : NabV Xo c)

def ValueLaw {n : ℕ} (N : ℕ) (β κ : c.F) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) (w : (Fin n → LevQ Dw l) → S),
    ShortValAt Xo c nab (x0Dat c x0) ⟨stdLat E n⟩ β N P y v →
    (∀ q, ThValAt Xo c nab y (fun b => levRep (q b)) P (w q)) →
    v = algebraMap c.F S κ * algebraMap c.F S ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S (zetaM c ^ pairL (l := l) x0 fun b => levRep (q b)) * w q

def RuleLaw {n : ℕ} (N : ℕ) (β κ : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  (∃ w, IsTranslateFamily Xo c nab P w) ∧
    ∀ w, IsTranslateFamily Xo c nab P w → ∀ f : Rul Xo c,
      RamifiedCoverPairIsomorphism.IsShortRule (DeltaDatum.triv Xo c nab) (Lat.std E n) N β x₀ a P f ↔
        f = fun p y => algebraMap c.F p.R κ * fourierComb Xo c x₀ w p y

def WellDefined (V : ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → S → Prop) : Prop :=
  (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v, V S y v) ∧
    ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S)
      (z : FrPt Xo c T), FrMap φ y z → ∀ v, V S y v → V T z (φ v)

def ValuesWellDefined : Prop :=
  ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ x : Fin n → Dw.La,
    WellDefined Xo c (fun _ _ _ y v => ThValAt Xo c nab y x P v) ∧
    ∀ (N : ℕ) (β : c.F), (Lat.std E n).Admissible l.M N → β ≠ 0 →
      WellDefined Xo c fun _ _ _ y v => ShortValAt Xo c nab (x0Dat c x) ⟨stdLat E n⟩ β N P y v

variable {Xo c nab}

theorem harmLat_std (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) : harmLat Dw c a (Lat.std E n) = harmA c a n :=
  (harmL_eq Dw c _ a).symm.trans (GlobalTheory.StdHarm.harmL_std c n a)

theorem seriesData_std_iff {n N : ℕ} {β : c.F} {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F} :
    IsSeriesData (DeltaDatum.triv Xo c nab) (Lat.std E n) N β a P ↔
      GenLat.LevOK (⟨stdLat E n⟩ : GenLat E n) N l.M ∧ IsBeLat Dw c (Lat.std E n) β ∧ P ∈ harmA c a n := by
  rw [← harmLat_std, ← toGen_std, levOK_iff]
  exact ⟨fun h => h.2, fun h => ⟨std_mem_reps _ n 1, h⟩⟩

theorem translateFamily_iff {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) (w : (Fin n → NamedCl Dw l) → Rul Xo c) :
    IsTranslateFamily Xo c nab P w ↔ ∀ q, IsThRule Xo c nab (fun b => levRep (q b)) P (w q) := by
  refine ⟨fun h q => ?_, fun h x p y => ?_⟩
  · have := h fun b => levRep (q b)
    simpa only [mk_levRep] using this
  · obtain ⟨S', _, _, φ, y', F, h1, h2, h3, h4⟩ := h (fun b => Submodule.Quotient.mk (x b)) p y
    refine ⟨S', _, _, φ, y', F, h1, h2, fun b => ?_, h4⟩
    have := h3 b
    rwa [levPt_levRep, levPtCl_mk] at this

theorem comb_eq {n : ℕ} (κ : c.F) (x0 : Fin n → Dw.La) (W : (Fin n → NamedCl Dw l) → Rul Xo c) (p : TRing c.F)
    (y : FrPt Xo c p.R) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : p.R →ₐ[c.F] T)
    (ψ : S →ₐ[c.F] T) (w : (Fin n → LevQ Dw l) → S) (h : ∀ q, φ (W q p y) = ψ (w q)) :
    φ (algebraMap c.F p.R κ * fourierComb Xo c (-cls l x0) W p y) =
      ψ (algebraMap c.F S κ * algebraMap c.F S ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
        ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S (zetaM c ^ pairL (l := l) x0 fun b => levRep (q b)) * w q) := by
  rw [finsum_eq_sum_of_support_subset (s := levelIndex Dw l n) _ fun q _ => by simp [levelIndex], _root_.mul_assoc,
    Finset.mul_sum, fourierComb]
  simp only [map_mul, map_sum, AlgHom.commutes, h, ← normalized_datum_eq_induced_coeff, x0Dat, _root_.mul_assoc]

theorem rule_triv_iff {n N : ℕ} {β : c.F} {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hN : (Lat.std E n).Admissible l.M N) (hβ : β ≠ 0) (hP : P ∈ harmA c a n) (x0 : Fin n → Dw.La) (f : Rul Xo c) :
    RamifiedCoverPairIsomorphism.IsShortRule (DeltaDatum.triv Xo c nab) (Lat.std E n) N β (-cls l x0) a P f ↔
      ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (S : Type) [CommRing S] [Algebra c.F S] (φ : p.R →ₐ[c.F] S)
        (z : FrPt Xo c S), FrMap φ y z → ShortValAt Xo c nab (x0Dat c x0) ⟨stdLat E n⟩ β N P z (φ (f p y)) := by
  have key : ∀ (S : Type) [CommRing S] [i : Algebra c.F S] (z : FrPt Xo c S) (v : S),
      @CoverVal _ _ _ _ _ _ _ _ _ _ (DeltaDatum.triv Xo c nab) S _ i z n (Lat.std E n) N β (-cls l x0) a P v ↔
        ShortValAt Xo c nab (x0Dat c x0) ⟨stdLat E n⟩ β N P z v := by
    intro S _ _ z v
    have e1 : (DeltaDatum.triv Xo c nab).combinedCoeff (-cls l x0) = normCoef c (x0Dat c x0) := by
      rw [normCoef_x0Dat]
      refine congrArg (fourier c) (funext fun x => ?_)
      refine (congrArg _ (phiDelta_triv _ _ x)).trans ((_root_.mul_one _).trans ?_)
      obtain ⟨x, rfl⟩ := cls_surjective l n x
      rfl
    have e2 : MvPolynomial.map (DeltaDatum.triv Xo c nab).cov.incl P = P := MvPolynomial.map_id P
    unfold CoverVal
    rw [e1, e2]
    refine (thVal_iff Xo c nab z (Lat.std E n) N β (x0Dat c x0) a P v).trans ⟨fun h => h.2.2, fun h => ⟨⟨(std_mem_reps
      (DeltaDatum.triv Xo c nab) n 1).1, (trivAt_iff _ _).2 (std_stdAt _), hβ, ?_⟩, (levOK_iff _ _ _).2 hN, h⟩⟩
    rwa [harmL_eq, harmLat_std]
  refine forall_congr' fun p => forall_congr' fun y => ⟨fun h S _ i φ z hz => ?_, fun h => ⟨?_, ?_⟩⟩
  · obtain ⟨v, hv, e⟩ := @h.2 S _ i φ.toRingHom z ((liesOver_triv φ y z).2 hz)
    have e' : φ (f p y) = v := e.trans ((congrArg (v * ·) (fnAt_one _)).trans (_root_.mul_one v))
    exact e' ▸ (key S z v).1 hv
  · exact ⟨p.R, _, (inferInstance : Algebra c.F p.R), RingHom.id _, y,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id,
      (liesOver_triv (AlgHom.id c.F p.R) y y).2 (GlobalTheory.Frames.frMapUniq_refl y)⟩
  · intro S _ i φ z hz
    letI : Algebra c.F S := i
    let φ' : p.R →ₐ[c.F] S := { φ with commutes' := fun x => RingHom.congr_fun hz.1 x }
    exact ⟨_, (key S z _).2 (h S φ' z ((liesOver_triv φ' y z).1 hz)),
      ((congrArg (_ * ·) (fnAt_one _)).trans (_root_.mul_one _)).symm⟩

theorem valueLaw_iff (h : ValuesWellDefined Xo c nab) {n N : ℕ} {β : c.F} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hN : (Lat.std E n).Admissible l.M N) (hβ : β ≠ 0) (hP : P ∈ harmA c a n)
    (κ : c.F) (x0 : Fin n → Dw.La) :
    ValueLaw Xo c nab N β κ x0 P ↔ RuleLaw Xo c nab N β κ (-cls l x0) a P := by
  have hT := fun x => (h n a P hP x).1
  have hS := (h n a P hP x0).2 N β hN hβ
  constructor
  · intro H
    refine ⟨⟨fun q p y => ((hT fun b => levRep (q b)).1 p.R y).exists.choose, (translateFamily_iff P _).2
      fun q p y => ((hT fun b => levRep (q b)).1 p.R y).exists.choose_spec⟩, fun W hW f => ?_⟩
    rw [translateFamily_iff] at hW
    rw [rule_triv_iff hN hβ hP]
    constructor
    · intro hf
      funext p y
      exact (H p.R y _ _ (hf p y p.R (AlgHom.id _ _) y (GlobalTheory.Frames.frMapUniq_refl y)) fun q => hW q p y).trans
        (comb_eq κ x0 W p y (AlgHom.id _ _) (AlgHom.id _ _) _ fun _ => rfl).symm
    · rintro rfl p y S _ _ φ z hz
      obtain ⟨v, hv, -⟩ := hS.1 S z
      have e := H S z v _ hv fun q => (hT _).2 _ _ φ y z hz _ (hW q p y)
      rwa [e.trans (comb_eq κ x0 W p y φ (AlgHom.id _ _) _ fun _ => rfl).symm] at hv
  · rintro ⟨⟨W, hW⟩, H⟩ S _ _ y v w hv hw
    have hf := (rule_triv_iff hN hβ hP x0 _).1 ((H W hW _).2 rfl)
    rw [translateFamily_iff] at hW
    refine Module.eq_of_localization_maximal (fun m _ => Localization.AtPrime m)
      (fun m _ => Algebra.linearMap S _) _ _ fun m _ => ?_
    obtain ⟨A, u, χ, -, -, -, ⟨z, hz, hu⟩, -⟩ :=
      GlobalTheory.T.chartCoverF_of_sectionBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E _ Dw l Xo c S y y rfl m
    exact ((hS.1 _ z).unique (hS.2 _ _ _ y z hz v hv) (hf A u _ χ z hu)).trans (comb_eq κ x0 W A u χ (locM c.F m) w
      fun q => ((hT _).1 _ z).unique ((hT _).2 _ _ _ u z hu _ (hW q A u)) ((hT _).2 _ _ _ y z hz _ (hw q)))

variable (Xo c nab)

def StdFourierEach : Prop :=
  ∀ (n N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F),
    IsSeriesData (DeltaDatum.triv Xo c nab) (Lat.std E n) N β a P →
    ∃ u : (𝓞 c.F)ˣ, RuleLaw Xo c nab N β ((u : 𝓞 c.F) : c.F) x₀ a P

def StdValuesExact : Prop :=
  ∀ (n N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F),
    GenLat.LevOK (⟨stdLat E n⟩ : GenLat E n) N l.M → P ∈ harmA c a n →
    ValueLaw Xo c nab N (betaH (Dw := Dw) c ⟨stdLat E n⟩) (betaH (Dw := Dw) c ⟨stdLat E n⟩)⁻¹ x0 P

variable {Xo c nab}

theorem isBeLat_std (n : ℕ) : IsBeLat Dw c (Lat.std E n) (betaH (Dw := Dw) c ⟨stdLat E n⟩) :=
  LatticeBetaCompare.isBeLat_betaH Dw c (Lat.std E n) ⟨1, by rw [IsBeLat, latIdeal_std]; exact isBe_top Dw c⟩

theorem exists_unit {n : ℕ} {β : c.F} (h : IsBeLat Dw c (Lat.std E n) β) :
    ∃ u : (𝓞 c.F)ˣ, ((u : 𝓞 c.F) : c.F) = β := by
  obtain ⟨b, hb, hs⟩ := h.1
  have hu : IsUnit b := by
    rw [latIdeal_std] at hs
    rw [← Ideal.span_singleton_eq_top, hs]
    simp only [reflexIdeal, Ideal.map_top]
    simp [← Ideal.one_eq_top]
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u, hb⟩

theorem ValueLaw.scale {n N : ℕ} {β β' κ : c.F} (hβ : β ≠ 0) (hβ' : β' ≠ 0) {x0 : Fin n → Dw.La}
    {P : MvPolynomial (LtN Dw n) c.F} (h : ValueLaw Xo c nab N β κ x0 P) :
    ValueLaw Xo c nab N β' (κ * β * β'⁻¹) x0 P := by
  intro S _ _ y v w ⟨T, _, _, φ, y', z, t, F, h1, h2, h3, h4, h5, h6, h7⟩ hw
  have e := h S y (algebraMap c.F S (β' / β) * v) w ⟨T, _, _, φ, y', z, t, F, h1, h2, h3, h4, h5, h6, by
    rw [map_mul, φ.commutes, h7, ← _root_.mul_assoc, ← map_mul]
    congr 2
    field_simp⟩ hw
  have e1 : v = algebraMap c.F S (β * β'⁻¹) * (algebraMap c.F S (β' / β) * v) := by
    rw [← _root_.mul_assoc, ← map_mul, show β * β'⁻¹ * (β' / β) = 1 by field_simp, map_one, _root_.one_mul]
  rw [e1, e]
  simp only [map_mul]
  ring

theorem exists_neg_cls {n : ℕ} (x₀ : Fin n → ConjCl Dw l) : ∃ x0 : Fin n → Dw.La, x₀ = -cls l x0 := by
  obtain ⟨x, hx⟩ := cls_surjective l n (-x₀)
  exact ⟨x, by rw [hx, neg_neg]⟩

theorem exact_iff (h : ValuesWellDefined Xo c nab) : StdValuesExact Xo c nab ↔ StdFourier Xo c nab := by
  have h0 : ∀ {n : ℕ} {β : c.F}, IsBeLat Dw c (Lat.std E n) β → β ≠ 0 := fun h =>
    LatticeBetaCompare.isBe_ne_zero (latIdeal_ne_bot _) h
  constructor
  · intro H n N β x₀ a P hd
    obtain ⟨x0, rfl⟩ := exists_neg_cls x₀
    obtain ⟨hN, hβ, hP⟩ := seriesData_std_iff.1 hd
    have := (H n N a x0 P hN hP).scale (h0 (isBeLat_std n)) (h0 hβ)
    rw [inv_mul_cancel₀ (h0 (isBeLat_std n)), _root_.one_mul] at this
    exact (valueLaw_iff h hd.2.1 (h0 hβ) hP _ x0).1 this
  · intro H n N a x0 P hN hP
    have hd := (seriesData_std_iff (nab := nab)).2 ⟨hN, isBeLat_std n, hP⟩
    exact (valueLaw_iff h hd.2.1 (h0 hd.2.2.1) hP _ x0).2 (H n N _ (-cls l x0) a P hd)

end Std

end GlobalTheory.ShortSpanCompare
