import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicMemRangeCompleteDvrPadicAlgCl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8
namespace GlobalTheory.LabelTransfer

theorem isAlgebraic_padicAlgCl (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V] (hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V)
    [Algebra (FractionRing V) (PadicAlgCl p)]
    (hV : ∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V))) :
    Algebra.IsAlgebraic (FractionRing V) (PadicAlgCl p) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨P, hP0, hPz⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[p]) z
  set κ := algebraMap (FractionRing V) (PadicAlgCl p)
  have hl : P.map (algebraMap ℚ_[p] (PadicAlgCl p)) ∈ Polynomial.lifts κ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV _
  obtain ⟨P', hP'⟩ := hl
  rw [Polynomial.coe_mapRingHom] at hP'
  refine ⟨P', fun h => hP0 ?_, ?_⟩
  · have : P.map (algebraMap ℚ_[p] (PadicAlgCl p)) = 0 := by rw [← hP', h, Polynomial.map_zero]
    exact (Polynomial.map_eq_zero_iff (algebraMap ℚ_[p] (PadicAlgCl p)).injective).1 this
  · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    change Polynomial.eval z (P'.map κ) = 0
    rw [hP', ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def, hPz]

end GlobalTheory.LabelTransfer

namespace GlobalTheory.LabelTransfer

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (eA : u.A.A ⟶ u.A.A) (s : u.D.toPre.X →+ u.D.toPre.X), (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left = x.left ≫ eA.left → CongMod m pk'.y (s pk.y)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing u.V) F] (k : ℕ), 1 ≤ k → IsUnit (k : u.V) → ∀ (q q' : QkPt u.D.toPre F k) (a a' : TFK (R := u.V) F ⟶ u.A.A), QkToAkU u.U.toUnifPre F k q a → QkToAkU u.U.toUnifPre F k q' a' → a.left = a'.left ≫ eA.left → CongMod k q.y (s q'.y) := by
  intro o Ω _ _ _ S ρ p _ y₀ u eA s H F _ _ _ k hk _ q q' a a' hq hq' haa
  haveI : CharZero (FractionRing u.V) := (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : Algebra.IsAlgebraic (FractionRing u.V) (PadicAlgCl p) :=
    isAlgebraic_padicAlgCl p u.V u.complete u.norm_le
  let emb : PadicAlgCl p →ₐ[FractionRing u.V] F := IsAlgClosed.lift
  letI : Algebra (PadicAlgCl p) F := emb.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing u.V) (PadicAlgCl p) F :=
    IsScalarTower.of_algebraMap_eq fun c => (emb.commutes c).symm
  have hf : (algebraMap (PadicAlgCl p) F).comp (algebraMap (FractionRing u.V) (PadicAlgCl p)) =
      algebraMap (FractionRing u.V) F := (IsScalarTower.algebraMap_eq _ _ _).symm
  have hk0 : ((k : ℕ) : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨q₀, hq₀⟩ := GlobalTheory.QkClosure.exists_qkExt_descent (algebraMap (PadicAlgCl p) F) hf hk0 q
  obtain ⟨q₀', hq₀'⟩ := GlobalTheory.QkClosure.exists_qkExt_descent (algebraMap (PadicAlgCl p) F) hf hk0 q'
  obtain ⟨f₀, hf₀, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) k hk
  obtain ⟨f₁, hf₁, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U F k hk
  have hL := GlobalTheory.firstFiveLaws
  have e₁ : QkToAkU u.U.toUnifPre F k q (GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀) :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow u.U hk hq₀ _).1 ((hf₀ _ _).2 rfl)
  have e₂ : QkToAkU u.U.toUnifPre F k q' (GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀') :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow u.U hk hq₀' _).1 ((hf₀ _ _).2 rfl)
  have ha : a = GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀ :=
    ((hf₁ _ _).1 hq).trans ((hf₁ _ _).1 e₁).symm
  have ha' : a' = GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀' :=
    ((hf₁ _ _).1 hq').trans ((hf₁ _ _).1 e₂).symm
  have hepi : Epi (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left := by
    have : Flat (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left :=
      inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom (algebraMap (PadicAlgCl p) F))))
    have : Surjective (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left :=
      ⟨fun z => ⟨(default : PrimeSpectrum F), Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _⟩⟩
    have : QuasiCompact (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left :=
      inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap (PadicAlgCl p) F))))
    exact Flat.epi_of_flat_of_surjective _
  have hx : (f₀ q₀).left = (f₀ q₀').left ≫ eA.left := by
    rw [ha, ha', Over.comp_left, Over.comp_left, Category.assoc] at haa
    exact (cancel_epi _).1 haa
  have := H k q₀' q₀ (f₀ q₀') (f₀ q₀) hk ((hf₀ _ _).2 rfl) ((hf₀ _ _).2 rfl) hx
  rw [hq₀.1, hq₀'.1]
  exact this

end GlobalTheory.LabelTransfer
