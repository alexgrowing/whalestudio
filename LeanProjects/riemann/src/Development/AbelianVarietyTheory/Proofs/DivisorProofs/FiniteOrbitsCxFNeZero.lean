import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixLineConjIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicBoundedPolynomials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorIntegralPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderIsHopfOrderNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyPadicBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyBoundedDenominators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitConjOfMinpolyEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugatesAlgebraRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSupportFinitePrimeSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalH1TrivialIffRationalNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryTorusNormClassesAtAllPlaces
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementSeparableMinpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPositivityInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveEigenvectorOfSimilitudeUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SylvesterInertiaInvariance
import GroundTheory.AutomorphicForms.Anisotropic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.T2SpaceAfP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingNormFormSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchMu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorMapEigenvalueNormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetAwayP

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} {β : G.Cˣ} {x : (AfP p ⊗[ℚ] G.C)ˣ}
  {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t} {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)}

theorem posV_val_ne_zero (z : PosV G v β) : z.1 ≠ 0 := by
  intro h
  have hz := z.2
  rw [h] at hz
  simp at hz

theorem fixL_smul_vec_iff (y : grp G β) (z : Fin G.n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    FixL G v β y (c • z) ↔ FixL G v β y z := by
  unfold FixL
  simp only [Matrix.mulVec_smul]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [smul_comm e c z] at he
    exact smul_right_injective _ hc he
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [he, smul_comm]⟩

variable (G v β x t hx Kf K')

def orbOfDat (d : Dat G v β) : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
  Quotient.mk'' (LeftCosets.mk _ _ d.1, (Projectivization.mk ℂ d.2.1 (posV_val_ne_zero d.2) : PLv G v β))

theorem orbOfDat_eq_of_same {a b : Dat G v β} (h : Same G v β x t hx Kf K' a b) :
    orbOfDat G v β x t hx Kf K' a = orbOfDat G v β x t hx Kf K' b := by
  obtain ⟨g, k, c, hk1, hk2, hc, h1, h2⟩ := h
  symm
  apply Quotient.sound
  refine ⟨g, Prod.ext ?_ ?_⟩
  · change g • LeftCosets.mk ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1 = LeftCosets.mk _ _ b.1
    rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk, h1, MonoidHom.prod_apply, inv_mul_cancel_left]
    exact Subgroup.mem_prod.2 ⟨hk1, hk2⟩
  · change Projectivization.map (Matrix.toLin' (toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ))
      (toV_injective G v β g) (Projectivization.mk ℂ a.2.1 (posV_val_ne_zero a.2)) =
      Projectivization.mk ℂ b.2.1 (posV_val_ne_zero b.2)
    rw [Projectivization.map_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨c⁻¹, ?_⟩
    rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul, Matrix.toLin'_apply]

def DatWt (f : G.GAf → ℂ) (f' : Gr G 1 → ℂ) (d : Dat G v β) : Prop :=
  ∃ y : grp G β, FixL G v β y d.2.1 ∧
    f (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * f' (d.1.2⁻¹ * toP1 G β y * d.1.2) ≠ 0

theorem datWt_iff_of_same {f : G.GAf → ℂ} {f' : Gr G 1 → ℂ} (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g)
    (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) {a b : Dat G v β} (h : Same G v β x t hx Kf K' a b) :
    DatWt G v β x t hx f f' a ↔ DatWt G v β x t hx f f' b := by
  obtain ⟨g, k, c, hk1, hk2, hc, h1, h2⟩ := h
  have e1 : ∀ y : grp G β, b.1.1⁻¹ * toAfF G β x t hx (g * y * g⁻¹) * b.1.1 =
      k.1⁻¹ * (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * k.1 := by
    intro y; rw [h1]; simp only [Prod.fst_mul, map_mul, map_inv]; group
  have e2 : ∀ y : grp G β, b.1.2⁻¹ * toP1 G β (g * y * g⁻¹) * b.1.2 =
      k.2⁻¹ * (a.1.2⁻¹ * toP1 G β y * a.1.2) * k.2 := by
    intro y; rw [h1]; simp only [Prod.snd_mul, map_mul, map_inv]; group
  have efix : ∀ y : grp G β, FixL G v β (g * y * g⁻¹) b.2.1 ↔ FixL G v β y a.2.1 := by
    intro y
    rw [h2, fixL_smul_vec_iff _ _ hc]
    exact (fixL_conj_iff p G v β y g a.2.1).symm
  constructor
  · rintro ⟨y, hy, hne⟩
    refine ⟨g * y * g⁻¹, (efix y).2 hy, ?_⟩
    rwa [e1, e2, hf _ hk1, hf' _ hk2]
  · rintro ⟨y', hy', hne⟩
    obtain ⟨y, rfl⟩ : ∃ y, y' = g * y * g⁻¹ := ⟨g⁻¹ * y' * g, by group⟩
    refine ⟨y, (efix y).1 hy', ?_⟩
    rwa [e1, e2, hf _ hk1, hf' _ hk2] at hne

end GlobalTheory.CxUnfold
