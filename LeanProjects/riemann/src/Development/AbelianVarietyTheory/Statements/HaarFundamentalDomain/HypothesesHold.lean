import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.NotLatsOKEven
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSpanningHypotheses
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConstOfNormFactorUnitFr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal

def ValuesSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → ∀ (W : UW U) (k : U.Comp) (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ (Dc : Dic Dw c σ (U.X k) W.g Dw.p n a), Dc.e = W.e → ∀ v : TF n W.g, IsVac (U.X k) Dc.bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v → ∃ C : ℂ, (∀ x ∈ (U.X k).dom, IsUnitFr (U.X k) x → ∀ (θ : (Fin W.g → ℂ) → ℂ) (κ : ℂ), IsTheta1 (U.X k) Dc.bas Dc.idx (H.w0 : E) x (U.X k).Λ θ → MeanOne (U.X k) Dc.bas Dc.idx x (U.X k).Λ θ → (∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA (U.X k) Dc.bas Dc.idx v x z) → ‖κ‖ = ‖C‖) ∧ C ≠ 0 ∧ ∀ (d : DeltaDat Xo c n) [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = σ t) → d.IsLev → d.l₂.A = 1 → (Dw.p = Dw.q → ∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ cv : (Dw.La →ₗ[𝓞 E] (Fin r → E)) → ℂ, (∀ mk, ‖cv mk‖ = 1) → CvIs d (U.X k) Dc.bas Dc.idx W.e (U.X k).Λ cv → ∀ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₂ → MarkOver l d.l₂ (U.X k).Λ (W.mark k) mk₂ → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs), LatsOK d.l₂.M La Nc → (∀ j, io (xs j) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ Y : Cl → (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, (∀ j, IsRoots d.l₂ (U.X k).Λ mk₂ (Nc j) (Y j)) → ∀ f ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f k x = C * cv mk₂ * clsSum σ (U.X k) Dc.hr Dc.bas Dc.idx Dc.eL w La Nc gam vol ep (fun j => io (xs j)) (U.X k).Λ v Y x

end GlobalTheory.ClsVal

namespace GlobalTheory.ClsVal.ValuesTest

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem inclusion_eq {A B : IntermediateField ℚ ℂ} (h : A ≤ B) (j : A →+* B) (hj : ∀ x, ((j x : B) : ℂ) = (x : ℂ)) :
    (IntermediateField.inclusion h).toRingHom = j := RingHom.ext fun x => Subtype.ext (hj x).symm

theorem exists_cover (Xo : Moduli Dw l) (h1 : 1 ≤ Dw.p + Dw.q) :
    ∃ c : Coeff l, ∀ n : ℕ, ∃ d : DeltaDat Xo c n, 3 < d.pd ∧ d.IsLev ∧ d.l₂.A = l.A ∧
      (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) ∧
      (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ d.cδ = 1 := by
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨pd, J, l₂, c, c₂, -, h3, hF, hd, hM, hco, hMb, hJ, hA₂⟩ := GlobalTheory.SpanInhab.exists_split_cover H l
  obtain ⟨Xo₂⟩ : Nonempty (Moduli Dw l₂) := GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level E H Dw l₂ h1
  obtain ⟨r, jK, m, hj, hs, he, heA, -, hrF⟩ := GlobalTheory.levelMaps_closed hL E H Dw h1 l l₂ Xo Xo₂ hd
  obtain ⟨rF, h₁, h₂, hfin, -, hsur, -⟩ := hrF c c₂ hF.symm
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab hL E H Dw l₂ Xo₂ c₂
  refine ⟨c, fun n => ?_⟩
  let d : DeltaDat Xo c n :=
    { pd := pd, I := J, l₂ := l₂, Xo₂ := Xo₂, c₂ := c₂, hF := hF, r := r, m := m, nab₂ := nab, cδ := 1,
      φδ := fun _ => 1 }
  have hdiv : l₂.M / l.M = pd := by
    rw [hM]; exact Nat.mul_div_cancel_left _ (by have := l.three_le; omega)
  refine ⟨d, h3, ⟨hd, hM, hco, hMb, hJ, ⟨?_, heA⟩, ?_, GlobalTheory.LevelCover.one_mem_sec_zero Xo₂ c₂, ?_⟩, hA₂,
    fun h => ?_, ⟨st, hnab⟩, rfl⟩
  · rw [hdiv] at he; exact he
  · intro k _ _ _ i₂ hk y
    obtain ⟨x₂, hx, hs⟩ := @GlobalTheory.LevelCover.exists_point_over E _ _ _ H Dw l l₂ Xo c Xo₂ c₂ hF.symm r rF hfin hsur
      h₁ h₂ k _ _ _ i₂ hk y.x y.x_over
    obtain ⟨y₂, -, hy⟩ := (GlobalTheory.frames_lift_to_cover hL E H Dw l Xo c n d).1 k hk y x₂ hx hs
    exact ⟨y₂, hy⟩
  · intro k _ _ _ y₂
    have h := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l₂ Xo₂ c₂ k y₂
    have e : evR d.Xo₂ d.c₂ d.cδ y₂ = 1 := evalAt_one _ _ y₂ h
    rw [e]; exact one_ne_zero
  · exact hs.trans (congrArg (fun j => Xo₂.s ≫ Geo.Tor.spMap j) (inclusion_eq h jK hj).symm)

theorem vac_ne_zero {r g : ℕ} {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {w : E}
    {A : AddSubgroup (Matrix (Fin 0) (Fin r) E)} {v : TF 0 g} (hv : IsVac X bas w A v) : v 0 ≠ 0 := by
  intro h
  have h0 : v = 0 := funext fun y => by rw [Subsingleton.elim y 0, h]; rfl
  have h1 := hv.2.1
  rw [h0] at h1
  simp [ip, haar, haarAt] at h1

end

theorem exists_moduli (p q : ℕ) (h : 1 ≤ p + q) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (Dw : Datum H)
      (l : Geo.Tor.Level H) (_ : Moduli Dw l), Dw.p = p ∧ Dw.q = q ∧ l.A = 1 := by
  obtain ⟨E, i1, i2, i3, H, -, hD⟩ := exists_datum_sum_and_all_signatures.2
  obtain ⟨D, hp, hq⟩ := hD p q
  obtain ⟨l, hA, -⟩ := exists_level_goodAt_all_primes_and_idx E H 1 one_pos
  obtain ⟨Xo⟩ : Nonempty (Moduli D l) := GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level E H D l (by omega)
  exact ⟨E, i1, i2, i3, H, D, l, Xo, hp, hq, hA⟩

end GlobalTheory.ClsVal.ValuesTest
