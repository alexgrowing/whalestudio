import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntEqFinrankRingOfIntegersMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreeRingOfIntegersOfIsTorsionFreeIntStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LieTens

open GlobalTheory.Serre Matrix

theorem finrank_int_eq (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N]
    [Module (𝓞 E) N] [Module.Free ℤ N] [Module.Finite ℤ N] :
    Module.finrank ℤ N = Module.finrank (𝓞 E) N * Module.finrank ℚ E :=
  GlobalTheory.T.finrank_int_eq_finrank_ringOfIntegers_mul' E N

theorem isTorsionFree_of_int (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N]
    [Module (𝓞 E) N] [Module.IsTorsionFree ℤ N] : Module.IsTorsionFree (𝓞 E) N :=
  GlobalTheory.T.isTorsionFree_ringOfIntegers_of_isTorsionFree_int' E N

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

@[nolint unusedArguments]
def Lat (_ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) : Type := Fin r → 𝓞 ℚ

variable (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)

instance : AddCommGroup (Lat ρ) := inferInstanceAs (AddCommGroup (Fin r → 𝓞 ℚ))
instance : Module (𝓞 ℚ) (Lat ρ) := inferInstanceAs (Module (𝓞 ℚ) (Fin r → 𝓞 ℚ))

def endOf : 𝓞 E →+* Module.End (𝓞 ℚ) (Fin r → 𝓞 ℚ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) (𝓞 ℚ) ≃ₐ[𝓞 ℚ] _).toRingEquiv.toRingHom.comp
    ((Int.castRingHom (𝓞 ℚ)).mapMatrix.comp ρ)

instance : Module (𝓞 E) (Lat ρ) := Module.compHom (Fin r → 𝓞 ℚ) (endOf ρ)

def latEquiv : Lat ρ ≃ₗ[𝓞 ℚ] (Fin r → 𝓞 ℚ) := LinearEquiv.refl _ _

theorem smul_def (c : 𝓞 E) (v : Lat ρ) :
    c • v = ((ρ c).map (Int.cast : ℤ → 𝓞 ℚ)) *ᵥ (show Fin r → 𝓞 ℚ from v) := rfl

instance : IsScalarTower (𝓞 ℚ) (𝓞 E) (Lat ρ) := by
  refine ⟨fun q c v => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, q = n :=
    ⟨Rat.ringOfIntegersEquiv q, Rat.ringOfIntegersEquiv.injective (by rw [map_intCast, Int.cast_id])⟩
  show endOf ρ ((n : 𝓞 ℚ) • c) (show Fin r → 𝓞 ℚ from v) = (n : 𝓞 ℚ) • endOf ρ c (show Fin r → 𝓞 ℚ from v)
  rw [Algebra.smul_def, map_intCast, map_mul, map_intCast, Module.End.mul_apply, Module.End.intCast_apply,
    Int.cast_smul_eq_zsmul]

instance : Module.Finite (𝓞 ℚ) (Lat ρ) := inferInstanceAs (Module.Finite (𝓞 ℚ) (Fin r → 𝓞 ℚ))

instance : Module.Finite (𝓞 E) (Lat ρ) := Module.Finite.of_restrictScalars_finite (𝓞 ℚ) (𝓞 E) (Lat ρ)

def intEquiv : (Fin r → ℤ) ≃ₗ[ℤ] Lat ρ :=
  (LinearEquiv.piCongrRight fun _ => (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ).toAddEquiv.toIntLinearEquiv)

instance : Module.Free ℤ (Lat ρ) := Module.Free.of_equiv (intEquiv ρ)

instance : Module.Finite ℤ (Lat ρ) := Module.Finite.equiv (intEquiv ρ)

theorem finrank_lat_int : Module.finrank ℤ (Lat ρ) = r := by
  rw [← LinearEquiv.finrank_eq (intEquiv ρ), Module.finrank_fin_fun]

instance : Module.Projective (𝓞 E) (Lat ρ) := by
  haveI : Module.IsTorsionFree (𝓞 E) (Lat ρ) := isTorsionFree_of_int E (Lat ρ)
  haveI : Module.FinitePresentation (𝓞 E) (Lat ρ) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

end GlobalTheory.Mum.LieTens

namespace GlobalTheory.Mum.LieTens

open GlobalTheory.Serre

theorem eig_eq_top {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (a : OAct (𝓞 ℚ) G) (τ₀ : 𝓞 ℚ →+* R) : Lie.eig a τ₀ = ⊤ := by
  refine eq_top_iff.mpr fun v _ x => ?_
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = n :=
    ⟨Rat.ringOfIntegersEquiv x, Rat.ringOfIntegersEquiv.injective (by rw [map_intCast, Int.cast_id])⟩
  rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

theorem lieMult_int {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (a : OAct (𝓞 ℚ) G)
    {g : ℕ} (hG : SmoothOfRelativeDimension g G.hom) {F : Type} [Field F] (t : Sp F ⟶ S)
    (τ₀ : 𝓞 ℚ →+* F) : LieMult a t τ₀ g := by
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback a t)]
  have hs : SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis ((Over.pullback t).obj G) hs
  have b := Lie.basis (a.pullback t) hv
  rw [eig_eq_top]
  refine ⟨?_, ?_⟩
  · haveI := Module.Finite.of_basis b
    exact Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl).symm
  · rw [finrank_top, Module.finrank_eq_card_basis b, Fintype.card_fin]

end GlobalTheory.Mum.LieTens

namespace GlobalTheory.Mum.LieTens

open GlobalTheory.Serre

theorem act_eq {S : Scheme.{0}} {O : Type} [CommRing O] {G : Over S} [GrpObj G] (x y : OAct O G)
    (h : ∀ c, x.act c = y.act c) : x = y := by
  obtain ⟨_, _, _, _, _⟩ := x
  obtain ⟨_, _, _, _, _⟩ := y
  simp only [OAct.mk.injEq]
  exact funext h

theorem comapAct_intCast {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (n : ℤ) :
    (comapAct (intAct G) (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)).act (n : 𝓞 ℚ) = (𝟙 G) ^ n := by
  rw [comapAct_act, intAct_act, map_intCast, Int.cast_id]

end GlobalTheory.Mum.LieTens

namespace GlobalTheory.Mum

open GlobalTheory.Serre GlobalTheory.Mum.LieTens

theorem lieMult_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ s : ℕ, r = s * Module.finrank ℚ E → Module.finrank (𝓞 E) D'.toPre.X = s * Module.finrank ℤ D.toPre.X ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (τ : 𝓞 E →+* F), LieMult (letI := H.starRing; ofRingAct o.onB.toRingAct) (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ (s * D.toPre.P.g) := by
  intro R _ _ _ hB E _ _ _ H D D' r W _ _ T ρ _ o hact s hrs
  refine ⟨?_, ?_⟩
  · have h1 := finrank_int_eq E D'.toPre.X
    have h2 : Module.finrank ℤ D'.toPre.X = r * Module.finrank ℤ D.toPre.X := by
      rw [LinearEquiv.finrank_eq T.xe.toIntLinearEquiv, Module.finrank_pi_fintype]
      simp
    rw [h2, hrs] at h1
    have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← h1]
    ring
  · intro F _ _ _ τ
    letI := H.starRing
    haveI : CharZero R := hB.2
    haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
    let p : IsPowGrp D'.toPre.P.A D.toPre.P.A r := ⟨T.pr, T.pr_hom, T.lim⟩
    let a₀ : OAct (𝓞 ℚ) D.toPre.P.A := comapAct (intAct D.toPre.P.A) (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)
    let h₀ := IsTensor.pow p a₀
    let h := h₀.congrLeft (latEquiv ρ)
    have hn := lieMult_int a₀ D.toPre.P.smoothDim
      (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) (τ.comp (algebraMap (𝓞 ℚ) (𝓞 E)))
    have hm := h.lieMult (K := ℚ) _ τ hn
    have key : ∀ c : 𝓞 E, (h.algAct (𝓞 E)).act c = o.onB.act c := by
      intro c
      have e1 : (h.algAct (𝓞 E)).act c = h₀.mapLeft h₀ (Matrix.toLin' ((ρ c).map (Int.cast : ℤ → 𝓞 ℚ))) := by
        haveI := (h.algAct (𝓞 E)).hom c
        refine h.hom_ext fun m => ?_
        rw [IsTensor.tmul_algAct, IsTensor.congrLeft_tmul, IsTensor.congrLeft_tmul, IsTensor.tmul_mapLeft]
        rfl
      refine pow_hom_ext p fun i => ?_
      rw [e1, IsTensor.pow_mapLeft_pr]
      rw [show p.pr i = T.pr i from rfl, hact.2 c i]
      refine Finset.prod_congr rfl fun j _ => ?_
      show T.pr j ≫ a₀.act ((ρ c i j : ℤ) : 𝓞 ℚ) = T.pr j ^ ρ c i j
      rw [comapAct_intCast, GrpObj.comp_zpow, Category.comp_id]
    have hact' : h.algAct (𝓞 E) = (letI := H.starRing; ofRingAct o.onB.toRingAct) := act_eq _ _ key
    have hfr : Module.finrank (𝓞 E) (Lat ρ) = s := by
      have h1 := finrank_int_eq E (Lat ρ)
      rw [finrank_lat_int] at h1
      have h3 : s * Module.finrank ℚ E = Module.finrank (𝓞 E) (Lat ρ) * Module.finrank ℚ E := by
        rw [← hrs]; exact h1
      have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
      exact (Nat.eq_of_mul_eq_mul_right hpos h3).symm
    rwa [hact', hfr, Nat.mul_comm] at hm

end GlobalTheory.Mum
