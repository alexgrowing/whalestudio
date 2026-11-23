import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatticePeriodFormIndependentOfModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMemNonunitsOfInduces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartExtensionHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrier

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.GeoGraft
open Formalism.MainNotions.DIV.Cons (SCF intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PartnerIn

section Lift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_lift (Z : Mdl Y i₀) {C : SCF p} (P : PointsOfFlagModel.PtC (Y Z.i) C) (u : Vecs Dw (Y Z.i).t ↥C.S)
    (hu : IsFrame (c := Z.i.c) (Y Z.i).t P.fK (P.y ≫ (Y Z.i).j) u) :
    ∃ z : Sp ↥(intO ↥C.S) ⟶ Z.X, z ≫ Z.π = P.yt := by
  obtain ⟨w, ⟨hw, -⟩, -⟩ := Z.bij ↥C.S P.fK P.y P.y_over u hu
  have : IsProper Z.s := projProper _ _ Z.s ⟨Z.n, Z.I.subschemeι, inferInstance, rfl⟩
  have hpr : IsProper (Y Z.i).s := projProper _ _ _ (Y Z.i).proj
  have := GlobalTheory.LocM.Cht.isFractionRing_ball ↥C.S
  have hs : w ≫ Z.s = spMap ((intO ↥C.S).subtype.comp P.alg) := by
    rw [← Z.π_s, ← Category.assoc, hw, ← P.ext, Category.assoc, P.yt_over, GlobalTheory.EtaVal.spMap_comp_spMap]
  have hE : ValuativeCriterion.Existence Z.s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Z.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) Z.s).1
  let S : ValuativeCommSq Z.s :=
    { R := ↥(intO ↥C.S)
      K := ↥C.S
      i₁ := w
      i₂ := spMap P.alg
      commSq := ⟨by rw [hs, spMap_comp]; rfl⟩ }
  obtain ⟨⟨l⟩⟩ := hE S
  have hl : spMap (intO ↥C.S).subtype ≫ l.l = w := l.fac_left
  have hr : l.l ≫ Z.s = spMap P.alg := l.fac_right
  refine ⟨l.l, GlobalTheory.EtaVal.point_ext_of_injective (intO ↥C.S).subtype Subtype.val_injective (Y Z.i).s _ _ ?_ ?_⟩
  · rw [← Category.assoc, hl, hw, P.ext]
  · rw [Category.assoc, Z.π_s, hr, P.yt_over]

end Lift

section Frame
open GlobalTheory.Exist.FlagBaseChange MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c₂ : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c₂.F}
  {p : ℕ} {C : SCF p}

end Frame

section Place

variable {K : Type} [Field K] [NumberField K]

theorem exists_overLa (T : CDVR) (s : K →+* T.Fr) {p : ℕ} (hp : p.Prime) (hpm : (p : T.V) ∈ maximalIdeal T.V) :
    ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la T.V s e ∧ ((p : ℕ) : 𝓞 K) ∈ la.asIdeal := by
  have hint : ∀ x : 𝓞 K, ∃ v : T.V, algebraMap T.V T.Fr v = s x := fun x => by
    have h : IsIntegral T.V (s (x : K)) := (RingOfIntegers.isIntegral_coe x).map_of_comp_eq
      (Int.castRingHom T.V) s (RingHom.ext_int _ _)
    exact IsIntegrallyClosed.isIntegral_iff.1 h
  choose f₀ hf₀ using hint
  have hinj := IsFractionRing.injective T.V T.Fr
  let f : 𝓞 K →+* T.V :=
    { toFun := f₀
      map_one' := hinj (by simp [hf₀])
      map_mul' := fun x y => hinj (by simp [hf₀])
      map_zero' := hinj (by simp [hf₀])
      map_add' := fun x y => hinj (by simp [hf₀]) }
  have hf : ∀ x, algebraMap T.V T.Fr (f x) = s x := hf₀
  have hpP : ((p : ℕ) : 𝓞 K) ∈ Ideal.comap f (maximalIdeal T.V) := by
    rw [Ideal.mem_comap, map_natCast]; exact hpm
  have hne : Ideal.comap f (maximalIdeal T.V) ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  let la : HeightOneSpectrum (𝓞 K) := ⟨Ideal.comap f (maximalIdeal T.V), Ideal.comap_isPrime _ _, hne⟩
  obtain ⟨hdvr, -⟩ := isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime K la
    (Ring.HasFiniteQuotients.finiteQuotient la.ne_bot)
  let V₀ := la.valuationSubringAtPrime K
  haveI : IsLocalization la.asIdeal.primeCompl V₀ :=
    Localization.subalgebra.isLocalization_ofField K la.asIdeal.primeCompl la.asIdeal.primeCompl_le_nonZeroDivisors
  have hunit : ∀ y : la.asIdeal.primeCompl, IsUnit (f y) := fun y =>
    IsLocalRing.notMem_maximalIdeal.1 fun h => y.2 h
  let o : V₀ →+* T.V := IsLocalization.lift (M := la.asIdeal.primeCompl) hunit
  have ho : ∀ a : 𝓞 K, o (algebraMap (𝓞 K) V₀ a) = f a := fun a => IsLocalization.lift_eq hunit a
  have e : s.comp V₀.subtype = (algebraMap T.V T.Fr).comp o :=
    IsLocalization.ringHom_ext la.asIdeal.primeCompl (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, ho, hf]
      rfl)
  have hloc : IsLocalHom o := ⟨fun a ha => by
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj la.asIdeal.primeCompl a
    have h1 : o a * f y = f x := by
      have := congrArg o hxy
      simpa [ho] using this
    have h2 : IsUnit (f x) := h1 ▸ ha.mul (hunit y)
    have h3 : x ∉ la.asIdeal := fun h => h (by exact h2)
    have h4 : IsUnit (algebraMap (𝓞 K) V₀ x) :=
      IsLocalization.map_units V₀ (⟨x, h3⟩ : la.asIdeal.primeCompl)
    rw [← hxy] at h4
    exact isUnit_of_mul_isUnit_left h4⟩
  obtain ⟨r, hr, hv⟩ := GlobalTheory.PlaceExtField.exists_index (V := V₀) (K' := K) (V' := T.V) (K'' := T.Fr) o s
    (fun v => RingHom.congr_fun e v)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V₀
  have h1 := GlobalTheory.PlaceCompletion.overLa_one_of_irreducible (la := la) (V := V₀) (K' := K) (RingHom.id K)
    (RingHom.id V₀) (fun x => rfl) hπ hπ
  refine ⟨la, r, ⟨hr, fun a => ?_⟩, hpP⟩
  have h2 := h1.2 a
  simp only [RingHom.id_apply, Nat.cast_one, one_mul] at h2
  rw [hv, h2]

end Place

section Ext
open scoped TensorProduct

end Ext

section Core
open GlobalTheory.Exist.FlagBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c₂ : Coeff l}

end Core

section Core0
open GlobalTheory.Exist.FlagBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c₂ : Coeff l}

end Core0

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Main

section Tr
variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def piPt {ι : Type} (L : ι → ModuliIntegralCharts.Loc D N j p) (v : ι) (y : (L v).Pt (L v).YY) : (Loc.pi L).Pt (Loc.pi L).YY := ⟨v, y⟩

end Tr

end GlobalTheory.PartnerIn
