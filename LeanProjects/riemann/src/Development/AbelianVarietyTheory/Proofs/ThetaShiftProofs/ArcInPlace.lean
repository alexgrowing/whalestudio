import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.ArcPlace

open HostModel ToricData ConjDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

def restrict {D : Datum H} {c : Coeff l} {O k : Type} [CommRing O] [CommRing k] [IsDomain k] (β : O →+* c.F)
    {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF) : ArcIn D l β k (bF.comp β) where
  D₀ := a.D₀
  mod := a.mod
  oa := a.oa
  nontriv := a.nontriv
  even := a.even
  bimult := a.bimult
  gen := a.gen
  w0 := a.w0
  be := a.be
  be_symm := a.be_symm
  be_pos := a.be_pos
  be_adj := a.be_adj
  be_dvd := a.be_dvd
  eta := a.eta
  etaA := a.etaA
  geom F _ _ _ r z := a.geom F (β r) (β z)

variable (c : Coeff l) {F₁ : Type} [Field F₁] (g : c.F →+* F₁)

def root {a : ℕ} (h : a ∣ l.M') : F₁ˣ :=
  Units.map g.toMonoidHom
    (Units.mk0 ⟨zeta a, zeta_mem_coeff_of_dvd c h⟩ fun e => Complex.exp_ne_zero _ (congrArg Subtype.val e))

theorem root_pow {a : ℕ} (h : a ∣ l.M') : root c g h ^ a = 1 := by
  have h1 : IsPrimitiveRoot (⟨zeta a, zeta_mem_coeff_of_dvd c h⟩ : c.F) a :=
    IsPrimitiveRoot.of_map_of_injective (f := c.F.val)
      (isPrimitiveRoot_zeta (Nat.pos_of_dvd_of_pos h (LevelExist.M'_pos l))) Subtype.val_injective
  exact Units.ext (h1.map_of_injective g.injective).pow_eq_one

def arcInFrac {O k : Type} [CommRing O] [CommRing k] [IsDomain k] (β : O →+* c.F) (b : O →+* k)
    (g : c.F →+* FractionRing k) (hg : ∀ x, g (β x) = algebraMap k _ (b x)) : ArcIn (hypDatum H) l β k b where
  D₀ := toricPre k (𝓞 E) fun _ => 1
  oa := arcAct H k
  nontriv := inferInstanceAs (Nontrivial (𝓞 E))
  even := psiEven _ fun _ => rfl
  bimult := tauBimult _ fun _ _ _ => by simp [polar_one]
  gen y := psiUnitOn _ y 1 (by simp)
  w0 := letI := H.starRing; psi_weight_zero_linear_combination _ (𝓞 E) (polar_one_smul k) H.w0 fun _ => polar_one k _ _
  be := arcForm l
  be_symm (y z : 𝓞 E) := congrArg ((2 * l.M' : ℤ) * ·) (trForm_symm H y z)
  be_pos (y : 𝓞 E) hy := mul_pos (mul_pos two_pos (Int.natCast_pos.2 (LevelExist.M'_pos l))) (trForm_pos H hy)
  be_adj a (y z : 𝓞 E) := congrArg ((2 * l.M' : ℤ) * ·) (trForm_adj H a y z)
  be_dvd (y z : 𝓞 E) := ⟨trForm H y z, rfl⟩
  eta := qkPt k (root c g (Nat.dvd_lcm_left l.M l.A)) (root_pow c g _)
  etaA := qkPt k (root c g (Nat.dvd_lcm_right l.M l.A)) (root_pow c g _)
  geom := by
    letI := H.starRing
    intro F _ _ _ r z _ hz f hf
    refine ⟨fun τ => ⟨0, lieMult_zero _ (𝓞 E) (polar_one_smul k) f τ, ?_⟩, ?_⟩
    · rw [hypDatum_p, hypDatum_q, ite_self, zero_add]
      exact Module.finrank_self (𝓞 E)
    haveI := c.fin
    obtain ⟨ζ, hp, hc, hζ⟩ := exists_roots c.F F ((algebraMap (FractionRing k) F).comp g)
    have key : ∀ {n : ℕ} (h : n ∣ l.M') (a : HypLattice H) q,
        QkExt (algebraMap _ F) (qkPt k (root c g h) (root_pow c g h) a) q →
          Out.QkPt.Equiv _ F q ((tateIsoQ H k ζ hp hc).ev n a) := fun {n} h a q hq => by
      rw [qkExt_qkPt k _ (algebraMap (FractionRing k) F) (RingHom.ext fun _ => rfl) (pow_eq_one_of_prim hp n)
        (hζ n (Nat.pos_of_dvd_of_pos h (LevelExist.M'_pos l)) ⟨zeta n, zeta_mem_coeff_of_dvd c h⟩ rfl)] at hq
      subst hq
      exact equiv_refl_split k F _
    refine ⟨tateIsoQ H k ζ hp hc, (hζ l.A l.A_pos (β z) hz).trans ?_, key _, fun a _ => key _ a⟩
    rw [hf, RingHom.comp_apply, hg]
    rfl

end GlobalTheory.ArcPlace
