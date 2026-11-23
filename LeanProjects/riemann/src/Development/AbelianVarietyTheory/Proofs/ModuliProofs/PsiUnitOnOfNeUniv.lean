import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.DVRSplitting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback

noncomputable section

namespace GlobalTheory.DvrDataCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke

section Ext

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem isFinUnram_of (W : UnramExt V) : DVRSplitting.IsFinUnram V W.W := ⟨W.inj, W.fin, W.unram⟩

theorem complete_of (hV : IsAdicComplete (maximalIdeal V) V) {W : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Algebra V W] (h : DVRSplitting.IsFinUnram V W) : IsAdicComplete (maximalIdeal W) W := by
  have := h.2.1
  rw [← h.map_maximalIdeal.2]
  exact isAdicComplete_map_of_finite (maximalIdeal V) W

def bundle (hV : IsAdicComplete (maximalIdeal V) V) (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Algebra V W] (h : DVRSplitting.IsFinUnram V W) : UnramExt V :=
  { W := W, fin := h.2.1, inj := h.1, unram := h.2.2, complete := complete_of hV h }

def extEquiv (hV : IsAdicComplete (maximalIdeal V) V) : UnramExt V ≃
    Σ' (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra V W),
      DVRSplitting.IsFinUnram V W where
  toFun W := ⟨W.W, W.ring, W.dom, W.dvr, W.alg, isFinUnram_of W⟩
  invFun x := @bundle V _ _ _ hV x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2
  left_inv _ := rfl
  right_inv _ := rfl

end Ext

section Move

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem psiUnitOn_of_ne_univ (D : DegPre R) (χ : D.X) {U : Set (Sp R)} (hU : U ≠ Set.univ) : PsiUnitOn D χ U := by
  intro j V _ hVU _ h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ (FractionRing R) := by
    refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} e => ⟨1, by rw [IsFractionRing.injective R _ e]⟩⟩
    · rintro ⟨_, n, rfl⟩
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (pow_ne_zero n hϖ.ne_zero))
    · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj (nonZeroDivisors R) z
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hϖ
      refine ⟨⟨a * (u⁻¹ : Rˣ), ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
      have e₁ : ϖ ^ n = (b : R) * (u⁻¹ : Rˣ) := by rw [hu, _root_.mul_right_comm, Units.mul_inv, _root_.one_mul]
      show z * algebraMap R _ (ϖ ^ n) = algebraMap R _ (a * (u⁻¹ : Rˣ))
      rw [e₁, map_mul, map_mul, ← _root_.mul_assoc]
      exact congrArg (· * _) e
  have : IsOpenImmersion (jK R) := IsOpenImmersion.of_isLocalization ϖ
  have hV : V ≤ (jK R).opensRange := by
    intro x hx
    have hx' : x ≠ closedPoint R := fun e => hU (Set.eq_univ_of_univ_subset (by
      have : V = ⊤ := (closedPoint_mem_iff V).1 (e ▸ hx)
      rw [this] at hVU
      exact hVU))
    have hb : x.asIdeal = ⊥ := by
      by_contra hb
      have := x.isPrime
      exact hx' (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal hb)))
    refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
    rw [hb]
    exact Ideal.comap_bot_of_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)
  have := (jK R).isIso_app V hV
  have hb := ConcreteCategory.bijective_of_isIso ((jK R).app V)
  obtain ⟨r, hr⟩ := hb.2 (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val)
  refine ⟨r, ?_, hr⟩
  have hu : IsUnit (((jK R).app V).hom r) := by
    have : ((jK R).app V).hom r = _ := hr
    rw [this]
    exact (Units.isUnit _).map _
  exact (MulEquiv.isUnit_map (RingEquiv.ofBijective ((jK R).app V).hom hb)).1 hu

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem exists_pull (P : ValPt Y) (W : UnramExt P.V) : ∃ t : SAB H (Sp W.W), Nonempty (SABMap t Y.t (P.ξ W)) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull allSixLaws.2.2.1.cubePull (P.ξ W) Y.t
  exact ⟨_, ⟨m⟩⟩

def DataWhereSplit (Y : Model Xo c β) : Prop :=
  ∀ (P : ValPt Y) (W : UnramExt P.V) (t : SAB H (Sp W.W)) (_ : SABMap t Y.t (P.ξ W)), SplitOver W t → DvrDataOver P W t

end GlobalTheory.DvrDataCompare
