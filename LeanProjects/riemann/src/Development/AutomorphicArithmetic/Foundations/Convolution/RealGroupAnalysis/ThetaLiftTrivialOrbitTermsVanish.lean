import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoRealOf
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal

namespace UpperTheory.ConvolutionTheory.R2

section Base

variable (F : Type) [Field F] [NumberField F]

abbrev A : Type := AdeleRing (𝓞 F) F

abbrev G1 : Type := Matrix.SpecialLinearGroup (Fin 2) (A F)
instance : MeasurableSpace (G1 F) := borel _
instance : BorelSpace (G1 F) := ⟨rfl⟩

abbrev V4 : Type := Fin 4 → A F

abbrev S4 : Type := ↥(schwartzBruhatPi F (Fin 4))

variable {F}

def ψ (x : A F) : ℂ := ((adelicChar F x : Circle) : ℂ)

def ab (a : (A F)ˣ) : ℝ := ((IdeleGroup.ideleModule F a : {r : ℝ // 0 < r}) : ℝ)

abbrev rt (c : F) : A F := algebraMap F (A F) c

def nU (b : A F) : G1 F := ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

def mD (a : (A F)ˣ) : G1 F := ⟨!![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)], by simp [Matrix.det_fin_two]⟩
variable (F) in

def wW : G1 F := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

def dM (t : (A F)ˣ) : GL (Fin 2) (A F) :=
  ⟨!![1, 0; 0, (t : A F)], !![1, 0; 0, ((t⁻¹ : (A F)ˣ) : A F)], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

def cD (t : (A F)ˣ) (g : G1 F) : G1 F :=
  ⟨!![g 0 0, g 0 1 * ((t⁻¹ : (A F)ˣ) : A F); (t : A F) * g 1 0, g 1 1], by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    have : g 0 1 * ((t⁻¹ : (A F)ˣ) : A F) * ((t : A F) * g 1 0) = g 0 1 * g 1 0 := by
      rw [mul_assoc, ← mul_assoc ((t⁻¹ : (A F)ˣ) : A F), Units.inv_mul, one_mul]
    rw [this]
    exact h⟩

abbrev gl (g : G1 F) : GL (Fin 2) (A F) := Matrix.SpecialLinearGroup.toGL g
variable (F) in

def ratS : Matrix.SpecialLinearGroup (Fin 2) F →* G1 F := Matrix.SpecialLinearGroup.map (algebraMap F (A F))
variable (F) in

def Gam : Subgroup (G1 F) := (ratS F).range

def InfOne (g : G1 F) : Prop := ∀ i j, (g i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1

def InfOrth (g : G1 F) : Prop := ∀ i j, ((g.1 * g.1ᵀ) i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1

def At (v : HeightOneSpectrum (𝓞 F)) (g : G1 F) : Prop :=
  InfOne g ∧ ∀ v' ≠ v, ∀ i j, (g i j).2 v' = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2 v'

def IntAt (v : HeightOneSpectrum (𝓞 F)) (g : G1 F) : Prop := ∀ i j, (g i j).2 v ∈ v.adicCompletionIntegers F
variable (F) in

def KK : Set (G1 F) := {g | InfOrth g ∧ ∀ v, IntAt v g}

variable (F) in

structure Meas where
  μ : Measure (G1 F)
  κ : Measure (G1 F)
  D : Set (G1 F)
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  prob : IsProbabilityMeasure κ
  supp : κ (KK F)ᶜ = 0
  κ_left : ∀ k ∈ KK F, κ.map (k * ·) = κ
  κ_right : ∀ k ∈ KK F, κ.map (· * k) = κ
  iwasawa : ∀ u : G1 F → ℝ≥0∞, Measurable u → ∫⁻ g, u g ∂μ =
    ∫⁻ k, ∫⁻ a : IdeleGroup F, ∫⁻ b, u (nU b * mD a * k) * ENNReal.ofReal ((ab a)⁻¹ ^ 2) ∂(adeleMeasure F) ∂(ideleMeasure F) ∂κ
  meas : MeasurableSet D
  fund : IsFundamentalDomain (Gam F) D μ

def Meas.ν (M : Meas F) : Measure (IdeleGroup F × G1 F) := (ideleMeasure F).prod M.κ

def iw (u : G1 F → ℂ) (p : IdeleGroup F × G1 F) : ℂ := (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u (mD p.1 * p.2)

def Meas.I0 (M : Meas F) (u : G1 F → ℂ) : ℂ := ∫ p, iw u p ∂M.ν

def Wf (f : GL (Fin 2) (A F) → ℂ) (g : GL (Fin 2) (A F)) : ℂ :=
  ∫ b in fundamentalSet F, f (gl (nU b) * g) * ψ b ∂(adeleMeasure F)

def q4 (δ : F) (v : V4 F) : A F := v 2 ^ 2 - rt δ * v 3 ^ 2 - v 1 * v 0

def B4 (δ : F) (v v' : V4 F) : A F := 2 * (v 2 * v' 2 - rt δ * (v 3 * v' 3)) - v 1 * v' 0 - v 0 * v' 1

def ft4 (δ : F) (φ : V4 F → ℂ) (v : V4 F) : ℂ := ∫ y, φ y * ψ (B4 δ y v) ∂(adeleMeasurePi F)

def hat (φ : V4 F → ℂ) (v : V4 F) : ℂ := ∫ s, φ (Function.update v 1 s) * ψ (-(s * v 1)) ∂(adeleMeasure F)

def Th (φ : V4 F → ℂ) : ℂ := ∑' ξ : Fin 4 → F, φ fun i => rt (ξ i)

def ThRow (r₀ r₁ : A F) (φ : V4 F → ℂ) : ℂ := ∑' ξ : Fin 2 → F, hat φ ![r₀, r₁, rt (ξ 0), rt (ξ 1)]

variable [IsTotallyReal F]

def polyFn : Subalgebra ℂ (V4 F → ℂ) := Algebra.adjoin ℂ {p | ∃ i w, p = fun v => ((TR.pInf F (v i) w : ℝ) : ℂ)}

def gauss (δ : F) (v : V4 F) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * ((∑ w, TR.pInf F (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w : ℝ) : ℂ))

def Fock (δ : F) : Submodule ℂ (S4 F) :=
  (Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F), ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
    φ = fun v => p v * gauss δ v * g (finPartPi v)}).comap (schwartzBruhatPi F (Fin 4)).subtype

end Base

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure Dat where
  δ : F
  θ : E
  σ : E ≃ₐ[F] E
  b : Module.Basis (Fin 2) F E
  b0 : b 0 = 1
  b1 : b 1 = θ
  sq : θ ^ 2 = algebraMap F E δ
  conj : σ θ = -θ
  neg : ∀ φ : F →+* ℝ, φ δ < 0

variable {F E} (D : Dat F E)

def Dat.mkE (u t : A F) : A E := AdeleBaseChange.adeleMap F E u + AdeleBaseChange.adeleMap F E t * rt D.θ

def Dat.co (z : A E) : Fin 2 → A F :=
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  (AdeleBaseChange.adeleBasis D.b).repr z

def Dat.bar : A E →+* A E := MulSemiringAction.toRingHom (E ≃ₐ[F] E) (A E) D.σ

def Dat.herm (v : V4 F) : Matrix (Fin 2) (Fin 2) (A E) :=
  !![D.mkE (v 1) 0, D.mkE (v 2) (v 3); D.mkE (v 2) (-v 3), D.mkE (v 0) 0]

def Dat.unherm (X : Matrix (Fin 2) (Fin 2) (A E)) : V4 F := ![D.co (X 1 1) 0, D.co (X 0 0) 0, D.co (X 0 1) 0, D.co (X 0 1) 1]

def Dat.act (h : GL (Fin 2) (A E)) (v : V4 F) : V4 F := D.unherm (h.val * D.herm v * (h.val.map D.bar)ᵀ)
variable (F) in

def nu (h : GL (Fin 2) (A E)) : (A F)ˣ := ideleNorm F E (Matrix.GeneralLinearGroup.det h)

def aE (a : (A E)ˣ) : GL (Fin 2) (A E) :=
  ⟨!![(a : A E), 0; 0, 1], !![((a⁻¹ : (A E)ˣ) : A E), 0; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

variable [IsTotallyReal F] [IsTotallyComplex E]

structure Weil where
  η : HChar F
  Om : G1 F →* Module.End ℂ (S4 F)
  L : GL (Fin 2) (A E) →* Module.End ℂ (S4 F)
  quad : IsQuadCharOf E η
  η_sq : ∀ a, η.1 a ^ 2 = 1
  η_norm : ∀ z : (A E)ˣ, η.1 (ideleNorm F E z) = 1
  Om_n : ∀ b φ v, (Om (nU b) φ).1 v = ψ (b * q4 D.δ v) * φ.1 v
  Om_m : ∀ (a : (A F)ˣ) φ v, (Om (mD a) φ).1 v = ((η.1 a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 fun i => (a : A F) * v i
  Om_w : ∀ φ v, (Om (wW F) φ).1 v = ft4 D.δ φ.1 v
  L_apply : ∀ h φ v, (L h φ).1 v = (((ab (nu F h))⁻¹ : ℝ) : ℂ) * φ.1 (D.act h⁻¹ v)
  comm : ∀ h g, L h * Om g = Om (cD (nu F h) g) * L h
  th_Om : ∀ γ φ, Th (Om (ratS F γ) φ).1 = Th φ.1
  th_L : ∀ γ φ, Th (L (ratGL E 2 γ) φ).1 = Th φ.1
  level : ∀ φ, ∀ᶠ g in 𝓝 (1 : G1 F), InfOne g → Om g φ = φ
  unr : ∀ φ, ∀ᶠ v in cofinite, ∀ g, At v g → IntAt v g → Om g φ = φ
  cont : ∀ φ, Continuous fun p : G1 F × V4 F => (Om p.1 φ).1 p.2

variable {D} (W : Weil D) (M : Meas F)

def lift (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) : ℂ :=
  ∫ g in M.D, f (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1 ∂M.μ

def T0 (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) : ℂ :=
  ∫ g in M.D, f (gl g * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1 ∂M.μ

def w1 (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) (g : G1 F) : ℂ :=
  Wf f (gl g * dM (nu F h)) * hat (W.Om g (W.L h φ)).1 ![0, 1, 1, 0]

def W1 (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) : ℂ := M.I0 (w1 W f φ h)
variable (D) in

def WE (Φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) : ℂ :=
  ∫ u in Set.univ.pi fun _ : Fin 2 => fundamentalSet F, Φ (gl (nU (D.mkE (u 0) (u 1))) * h) * ψ (2 * u 0) ∂(adeleMeasurePi F)

def span (π : TR.CuspSub F 2) : Submodule ℂ (Sm E 2) :=
  Submodule.span ℂ {Φ | ∃ f ∈ π.V, ∃ φ ∈ Fock D.δ, Φ.1 = lift W M f.1 φ}

def ThetaLiftTrivialOrbitTermsVanish (π : TR.CuspSub F 2) : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h, T0 W M f.1 φ h = 0

end Ext

end UpperTheory.ConvolutionTheory.R2

end
