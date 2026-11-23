import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralElemOfIsAlgebraicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsHomogeneousOfEquivariant
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcPointTangentPart

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_letters_equivariant (h1 : Out.Laws) (h2 : Out.Laws2) (hev : GlobalTheory.Reg.EvLaws Xo c)
    {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (hY : Mono Y.j)
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] {b₀ : O →+* K₁} {A : ArcIn Dw l β K₁ b₀}
    {χ : Sp (PowerSeries K₁) ⟶ Y.X} (W : Wit Y A χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt A.D₀ (epsR K₁)) (th : A.D₀.P.L.Sec) (hth : ThNZ th)
    (ζ : K₁) (y₀ yF : FrPt Xo c (ArcS Dw K₁)) (hy₀ : IsArcFr W e th (arcι Dw K₁) y₀)
    (hchg : FrChg (letM Dw K₁) (cst Dw ζ) y₀ yF)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c) (hF : F ∈ sec Xo c a n)
    (T : Type) [Field T] (φ ψ : ArcS Dw K₁ →+* T) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T)
    (hφψ : ∀ g : LaurentSeries K₁, φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.C g)) =
      ψ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.C g)))
    (hb : ∀ τ i j, i < j → b τ i j = 0)
    (hX : ∀ τ i k, ψ (arcX Dw K₁ τ i k) = ∑ j, b τ i j * φ (arcX Dw K₁ τ j k)) :
    ψ (evR Xo c F yF) = (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) * φ (evR Xo c F yF) := by
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap c.F K₁).injective
  obtain ⟨hdom, -, -, hconst⟩ := GlobalTheory.ArcConst.algebraic_const E H Dw K₁
  obtain ⟨f₀, hf₀⟩ := hconst c.F (algebraMap c.F (ArcS Dw K₁))
  have hι : φ.comp (arcι Dw K₁) = ψ.comp (arcι Dw K₁) := RingHom.ext fun p => hφψ _
  letI : Algebra c.F T := (φ.comp (algebraMap c.F (ArcS Dw K₁))).toAlgebra
  let φ' : ArcS Dw K₁ →ₐ[c.F] T := { φ with commutes' := fun _ => rfl }
  let ψ' : ArcS Dw K₁ →ₐ[c.F] T :=
    { ψ with
      commutes' := fun r => by
        change ψ (algebraMap c.F (ArcS Dw K₁) r) = φ (algebraMap c.F (ArcS Dw K₁) r)
        rw [hf₀]
        exact (RingHom.congr_fun hι _).symm }
  obtain ⟨y₁, hy₁⟩ := hev.bc _ _ φ' y₀
  obtain ⟨y₂, hy₂⟩ := hev.bc _ _ ψ' y₀
  obtain ⟨z₁, hz₁⟩ := hev.bc _ _ φ' yF
  obtain ⟨z₂, hz₂⟩ := hev.bc _ _ ψ' yF
  have hS := GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c O β Y K₁ b₀ A χ W e th hth _ _ y₀ hy₀
  have a₁ : IsArcFr W e th (φ.comp (arcι Dw K₁)) y₁ := hS.2 hY T φ' y₁ hy₁
  have a₂ : IsArcFr W e th (ψ.comp (arcι Dw K₁)) y₂ := hS.2 hY T ψ' y₂ hy₂
  rw [← hι] at a₂
  obtain rfl : y₂ = y₁ :=
    (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c O β Y K₁ b₀ A χ W e th hth _ _ y₁ a₁).1 hY y₂ a₂
  have cS := GlobalTheory.Frames.frChg_calculus E H Dw l Xo c (ArcS Dw K₁)
  have cT := GlobalTheory.Frames.frChg_calculus E H Dw l Xo c T
  have c₁ := (cS.2.2.1 T φ' _ _ _ _ _ _ hchg hy₁).1 hz₁
  have c₂ := (cS.2.2.1 T ψ' _ _ _ _ _ _ hchg hy₂).1 hz₂
  have hM : ∀ τ, (letM Dw K₁ τ).map ψ' = b τ * (letM Dw K₁ τ).map φ' := fun τ => by
    ext i k
    exact hX τ i k
  have hζ : ψ' (cst Dw ζ) = 1 * φ' (cst Dw ζ) := by
    rw [one_mul]
    exact (RingHom.congr_fun hι _).symm
  rw [funext hM, hζ] at c₂
  have c₃ : FrChg b 1 z₁ z₂ := (cT.1 _ b _ 1 _ _ _ c₁).2 c₂
  have hbu : ∀ τ i, b τ i i ≠ 0 := fun τ i => by
    have hu := ((GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c T b 1 z₁).2.2.1 z₂ c₃).1 τ
    rw [Matrix.det_of_lowerTriangular (b τ) (fun i j hij => hb τ i j hij)] at hu
    exact (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => b τ i i) (Finset.mem_univ i)) hu).ne_zero
  let t : Ix Dw → Tˣ := fun o => match o with
    | none => 1
    | some x => Units.mk0 (b x.1 x.2 x.2) (hbu x.1 x.2)
  have hbor : FrBor t z₁ z₂ := (cT.2.2.2 t z₁ z₂).2 ⟨b, fun _ _ => rfl, hb, c₃⟩
  have eS := (GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a n F hF (ArcS Dw K₁)).1
  have eT := ((GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a n F hF T).2 inferInstance).1 t z₁ z₂ hbor
  rw [eS T φ' yF z₁ hz₁, eS T ψ' yF z₂ hz₂] at eT
  have hw : wchar (ex Dw a n) t = ∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ)) := by
    rw [wchar, Fintype.prod_option, Fintype.prod_sigma]
    simp [t, ex]
  rw [hw] at eT
  exact eT

theorem ArcDatum.exists_normal_tangent (h1 : Out.Laws) (h2 : Out.Laws2)
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) :
    ∃ (ζ : K₁) (e₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt (d.a.restrict (c.V d.Wp).subtype).D₀ (epsR K₁))
      (y₀ : FrPt Xo c (ArcS Dw K₁)), IsArcFr d.W e₀ d.th (arcι Dw K₁) y₀ ∧
        FrChg (letM Dw K₁) (cst Dw ζ) y₀ d.yF := by
  obtain ⟨ζ, -, -, -, -, e₀, y₀, -, hy₀, hc⟩ := GlobalTheory.ArcQ.exists_normalForm h1 h2 E H Dw l Xo c K₁ d
  exact ⟨ζ, e₀, y₀, hy₀, hc⟩

theorem evR_arc_isHomogeneous : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁), algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
  intro h1 h2 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d a n F hF
  obtain ⟨ζ, e₀, y₀, hy₀, hc⟩ := d.exists_normal_tangent h1 h2
  have hth : ThNZ d.th := by
    obtain ⟨_, _, _, _, hne, -⟩ := d.isArc3
    exact (GlobalTheory.ThetaOverField.nonzero_generates h1 h2 K₁ _ d.th).1.1 hne
  exact GlobalTheory.BorelAlg.exists_isHomogeneous_of_equivariant E H Dw K₁ a _ fun T _ φ ψ b hφψ hb hX =>
    evR_letters_equivariant h1 h2 hev (GlobalTheory.ThetaShiftProofs.mono_j d.Y (mono_spMap_subtype _)) d.W e₀ d.th hth ζ y₀ d.yF hy₀ hc
      a n F hF T φ ψ b hφψ hb hX

end GlobalTheory.ArcQ
