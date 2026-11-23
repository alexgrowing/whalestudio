import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2.Fo (Ops pl cw)
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section Base

variable {F : Type} [Field F] [NumberField F]

def wt (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : ℝ :=
  if finPartPi v ∈ K then ((1 + ‖infPartPi v‖) ^ N)⁻¹ else 0

def Dom {ι : Type} (s : Set ι) (Φ : ι → V4 F → ℂ) : Prop :=
  ∃ K, IsCompact K ∧ ∀ N, ∃ B : ℝ, ∀ i ∈ s, ∀ v, ‖Φ i v‖ ≤ B * wt K N v

def sc (a : (A F)ˣ) (ξ : Fin 4 → F) : V4 F := fun i => (a : A F) * rt (ξ i)

def LInv {X : Type} (u : G1 F → X) : Prop := ∀ γ g, u (ratS F γ * g) = u g

def LRat (f : GL (Fin 2) (A F) → ℂ) : Prop := ∀ γ g, f (ratGL F 2 γ * g) = f g

def Der (Ψ Ψ' : ℝ → S4 F) : Prop := ∀ t v, HasDerivAt (fun s => (Ψ s).1 v) ((Ψ' t).1 v) t

variable (F)

def WtBound : Prop := ∀ φ : S4 F, Continuous φ.1 ∧ Dom (Set.univ : Set Unit) fun _ => φ.1

def WtInt : Prop := ∃ N, ∀ K, IsCompact K → Integrable (wt (F := F) K N) (adeleMeasurePi F)

def WtSum : Prop := ∃ N, ∀ K, IsCompact K → ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ a : (A F)ˣ, c ≤ ab a →
  Summable (fun ξ => wt K N (sc a ξ)) ∧ ∑' ξ, wt K N (sc a ξ) ≤ C

def WtId : Prop := ∃ N, ∀ K, IsCompact K →
  Integrable (fun a : IdeleGroup F => (ab a)⁻¹ * wt K N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0]) (ideleMeasure F)

def WtLin : Prop := ∀ C : Set (GL (Fin 4) (A F)), IsCompact C → ∀ K, IsCompact K → ∃ K', IsCompact K' ∧ ∀ N, ∃ B : ℝ,
  ∀ x ∈ C, ∀ v, wt K N (x.val *ᵥ v) ≤ B * wt K' N v

def ThDer : Prop := ∀ Ψ Ψ' : ℝ → S4 F, Der Ψ Ψ' → ∀ t, Dom (Metric.ball t 1) (fun s => (Ψ' s).1) →
  HasDerivAt (fun s => Th (Ψ s).1) (Th (Ψ' t).1) t

def ThLin : Prop := (∀ φ φ' : S4 F, Th (φ + φ').1 = Th φ.1 + Th φ'.1) ∧ ∀ (c : ℂ) (φ : S4 F), Th (c • φ).1 = c * Th φ.1

variable [IsTotallyReal F]

def Iwa : Prop := IsCompact (KK F) ∧ ∀ C : Set (G1 F), IsCompact C → ∃ U : Set (A F)ˣ, IsCompact U ∧
  ∀ g ∈ C, ∃ b, ∃ a ∈ U, ∃ k ∈ KK F, g = nU b * mD a * k

def Vol : Prop := ∀ M : Meas F, M.μ M.D < ⊤

def RtInv : Prop := ∀ (M : Meas F) (u : G1 F → ℂ), LInv u → ∀ g₀,
  ∫ g in M.D, u (g * g₀) ∂M.μ = ∫ g in M.D, u g ∂M.μ

variable {F}

def Par (c : ℝ → GL (Fin 2) (TR.Rinf F)) (Y : TR.Lie F 2) : Prop :=
  (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => TR.toL (c t).val) Y 0

variable (F) in

def ParCont : Prop := Continuous (TR.infGL F 2) ∧ ∀ (c : ℝ → GL (Fin 2) (TR.Rinf F)) Y, Par c Y →
  c 0 = 1 ∧ Continuous c ∧ Par (fun t => c (-t)) (-Y)

def SDiff (O : Ops F) : Prop := ∀ (φ : S4 F) (v : V4 F) (x : ℝ → Fin 4 → TR.Rinf F) x', x 0 = 0 → HasDerivAt x x' 0 →
  HasDerivAt (fun t => φ.1 fun i => v i + TR.sInf F (x t i)) (∑ i, ∑ w, ((x' i w : ℝ) : ℂ) * (O.d w i φ).1 v) 0

def Hm (s : ℂ) (w : InfinitePlace F) (v : Fin 4 → TR.Rinf F) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 1 w : ℝ), (v 2 w : ℝ) + s * (v 3 w : ℝ); (v 2 w : ℝ) - s * (v 3 w : ℝ), (v 0 w : ℝ)]

end Base

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

def Ht (y : GL (Fin 2) (Cinf E)) : ℝ := 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖
variable (F) in

def One (y : GL (Fin 2) (Cinf E)) : Prop := nu F (infGL E 2 y) = 1

def ex (X : Lie E 2) (t : ℝ) : GL (Fin 2) (Cinf E) := (Matrix.isUnit_exp (t • Matrix.of X)).unit

def zE (s : Cinf E) : Lie E 2 := toL (Matrix.scalar (Fin 2) s)

def zF (s : TR.Rinf F) : TR.Lie F 2 := TR.toL (Matrix.scalar (Fin 2) s)
variable (F) in

def trI (s : Cinf E) : TR.Rinf F := fun v => ∑ w : InfinitePlace E, if w.comap (algebraMap F E) = v then 2 * (s w).re else 0

variable (E) in

def ExPar : Prop := ∀ X : Lie E 2, (∀ s t, ex X (s + t) = ex X s * ex X t) ∧ Continuous (ex X) ∧
  HasDerivAt (fun t => toL (ex X t).val) X 0 ∧ ((Matrix.of X).trace = 0 → ∀ t, (ex X t).val.det = 1) ∧
  ∀ s t, (ex (X + zE s) t) = ex (zE s) t * ex X t
variable (E) in

def SmFre : Prop := ∀ (Φ : GL (Fin 2) (A E) → ℂ) (T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)),
  (∀ X g, Continuous fun y => T X (g * infGL E 2 y)) →
  (∀ X g, HasDerivAt (fun t => Φ (g * infGL E 2 (ex X t))) (T X g) 0) →
  ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g
variable (E) in

def SmCrit : Prop := ∀ S : Submodule ℂ (GL (Fin 2) (A E) → ℂ), (∀ Φ ∈ S, ∀ g, Continuous fun y => Φ (g * infGL E 2 y)) →
  (∀ Φ ∈ S, ∃ T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ), (∀ X, T X ∈ S) ∧
    ∀ X g, HasDerivAt (fun t => Φ (g * infGL E 2 (ex X t))) (T X g) 0) → S ≤ Sm E 2
variable (F E) in

def NormInf : Prop := ∀ s : (Cinf E)ˣ, ∃ u : (TR.Rinf F)ˣ,
  (∀ v, u.val v = ∏ w : InfinitePlace E, if w.comap (algebraMap F E) = v then ‖s.val w‖ ^ 2 else 1) ∧
    ideleNorm F E (infId E s) = TR.infId F u
variable (E) in

def HtLe : Prop := Continuous (Ht (E := E)) ∧ ∀ y : GL (Fin 2) (Cinf E), 1 ≤ Ht y ∧ Ht y ≤ 3 * GlobalTheory.CuspRep.height y ∧
  ∀ y', Ht (y * y') ≤ 2 * Ht y * Ht y'
variable (F E) in

def Dec : Prop := ∃ (σ : GL (Fin 2) (Cinf E) → (Cinf E)ˣ) (τ : GL (Fin 2) (Cinf E) → GL (Fin 2) (Cinf E)),
  Continuous σ ∧ Continuous τ ∧ ∀ y, infGL E 2 y = Matrix.GeneralLinearGroup.scalar (Fin 2) (infId E (σ y)) * infGL E 2 (τ y) ∧
    One F (τ y) ∧ Ht (τ y) ≤ 4 * Ht y ^ 2 ∧ 1 + ‖(σ y).val‖ + ‖(σ y)⁻¹.val‖ ≤ 2 * Ht y
variable (F E) in

def OneOf : Prop := ∀ y : GL (Fin 2) (Cinf E), (∀ w, ‖y.val.det w‖ = 1) → One F y
variable (F E) in

def OmGrowth : Prop := Continuous (fun s : (Cinf E)ˣ => ideleNorm F E (infId E s)) ∧ ∀ ω : (A F)ˣ →* ℂˣ, Continuous ω →
  ∃ (C : ℝ) (N : ℕ), ∀ s : (Cinf E)ˣ, ‖((ω (ideleNorm F E (infId E s)) : ℂˣ) : ℂ)‖ ≤ C * (1 + ‖s.val‖ + ‖s⁻¹.val‖) ^ N
variable (F E) in

def CenExp : Prop := ∀ s : Cinf E, ∃ (z : ℝ → (A E)ˣ) (c : ℝ → GL (Fin 2) (TR.Rinf F)), Par c (zF (trI F s)) ∧
  ∀ t, infGL E 2 (ex (zE s) t) = Matrix.GeneralLinearGroup.scalar (Fin 2) (z t) ∧
    Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleNorm F E (z t)) = TR.infGL F 2 (c t)
variable (F E) in

def FinTr : Prop := ∃ κ : GL (Fin 2) (Af E) →* GL (Fin 2) (Af F), Continuous κ ∧ ∀ k, dM (nu F (finGL E 2 k)) = finGL F 2 (κ k)

variable (D : Dat F E)

def ActCont : Prop := ∃ ρ : GL (Fin 2) (A E) →* GL (Fin 4) (A F), Continuous ρ ∧ (∀ h v, D.act h v = (ρ h).val *ᵥ v) ∧
  Continuous (nu F : GL (Fin 2) (A E) → (A F)ˣ) ∧ Continuous (infGL E 2) ∧ Continuous (finGL E 2)

def WtAct : Prop := ∃ C : ℝ, ∀ K N y v, wt K N (D.act (infGL E 2 y)⁻¹ v) ≤ (C * Ht y ^ 2) ^ N * wt K N v

def ActInf : Prop := ∀ (y : GL (Fin 2) (Cinf E)) (v : V4 F), finPartPi (D.act (infGL E 2 y) v) = finPartPi v ∧ ∀ τ : E →+* ℂ,
  Hm (τ D.θ) (pl F τ) (fun i => TR.pInf F (D.act (infGL E 2 y) v i)) =
    y.val.map (coord τ) * Hm (τ D.θ) (pl F τ) (fun i => TR.pInf F (v i)) * (y.val.map (coord τ))ᴴ

def VfDer : Prop := ∀ (Y : Lie E 2) v, ∃ (x : ℝ → Fin 4 → TR.Rinf F) (x' : Fin 4 → TR.Rinf F), x 0 = 0 ∧ HasDerivAt x x' 0 ∧
  (∀ t, D.act (infGL E 2 (ex Y t))⁻¹ v = fun i => v i + TR.sInf F (x t i)) ∧ ∀ τ : E →+* ℂ,
    Hm (τ D.θ) (pl F τ) x' = -((Matrix.of Y).map (coord τ) * Hm (τ D.θ) (pl F τ) (fun i => TR.pInf F (v i)) +
      Hm (τ D.θ) (pl F τ) (fun i => TR.pInf F (v i)) * ((Matrix.of Y).map (coord τ))ᴴ)

def VfOps (O : Ops F) : Prop := ∀ Y : Lie E 2, (Matrix.of Y).trace = 0 → ∀ (v : V4 F) (x' : Fin 4 → TR.Rinf F),
  (∀ τ : E →+* ℂ, Hm (τ D.θ) (pl F τ) x' = -((Matrix.of Y).map (coord τ) * Hm (τ D.θ) (pl F τ) (fun i => TR.pInf F (v i)) +
      Hm (τ D.θ) (pl F τ) (fun i => TR.pInf F (v i)) * ((Matrix.of Y).map (coord τ))ᴴ)) →
  ∀ φ : S4 F, ∑ i, ∑ w, ((x' i w : ℝ) : ℂ) * (O.d w i φ).1 v = (O.dL D Y φ).1 v

def DLCen (O : Ops F) : Prop := (∀ s : Cinf E, O.dL D (zE s) = -∑ τ : E →+* ℂ, coord τ s • O.h (pl F τ)) ∧
  (∀ Y Y', O.dL D (Y + Y') = O.dL D Y + O.dL D Y') ∧ (∀ (c : ℝ) Y, O.dL D (c • Y) = (c : ℂ) • O.dL D Y) ∧
  ∀ s : Cinf E, TR.lie F 2 (zF (trI F s)) = ∑ τ : E →+* ℂ, coord τ s • (TR.Eop (pl F τ) 0 0 + TR.Eop (pl F τ) 1 1)

def OpsFock (O : Ops F) : Prop := ∀ w i, ∀ φ ∈ Fock D.δ, O.x w i φ ∈ Fock D.δ ∧ O.d w i φ ∈ Fock D.δ

variable {D} (O : Ops F) (W : Weil D) (M : Meas F)

def DLDer : Prop := ∀ Y : Lie E 2, (Matrix.of Y).trace = 0 → (∀ t, One F (ex Y t)) ∧ ∀ φ : S4 F,
  Der (fun s => W.L (infGL E 2 (ex Y s)) φ) fun s => W.L (infGL E 2 (ex Y s)) (O.dL D Y φ)

def CurveE : Prop := ∀ w : InfinitePlace F, ∃ (G : ℝ → G1 F) (c : ℝ → GL (Fin 2) (TR.Rinf F)),
  Par c (TR.toL (Matrix.single 0 1 (Pi.single w 1))) ∧ (∀ t, gl (G t) = TR.infGL F 2 (c t)) ∧
  ∀ φ, Der (fun s => W.Om (G s) φ) fun s => W.Om (G s) (O.e D.δ w φ)

def CurveH : Prop := ∀ w : InfinitePlace F, ∃ (G : ℝ → G1 F) (c : ℝ → GL (Fin 2) (TR.Rinf F)),
  Par c (TR.toL (Matrix.single 0 0 (Pi.single w 1)) - TR.toL (Matrix.single 1 1 (Pi.single w 1))) ∧
  (∀ t, gl (G t) = TR.infGL F 2 (c t)) ∧ ∀ φ, Der (fun s => W.Om (G s) φ) fun s => W.Om (G s) (O.h w φ)

def LCen : Prop := ∀ z : (A E)ˣ, W.L (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = W.Om (mD (ideleNorm F E z)⁻¹) ∧
  nu F (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = ideleNorm F E z ^ 2

def LLevel : Prop := ∀ φ : S4 F, ∀ᶠ k in 𝓝 (1 : GL (Fin 2) (Af E)), W.L (finGL E 2 k) φ = φ

def ThMeas : Prop := ∀ φ : S4 F, (Measurable fun g => Th (W.Om g φ).1) ∧ LInv (fun g => Th (W.Om g φ).1) ∧
  (∀ r₀ r₁, Measurable fun g => ThRow r₀ r₁ (W.Om g φ).1) ∧ LInv (fun g => ThRow 0 0 (W.Om g φ).1) ∧
  ∀ v, Measurable fun g => hat (W.Om g φ).1 v

def OmFin : Prop := ∀ φ ∈ Fock D.δ, ∃ (n : ℕ) (e : Fin n → S4 F), ∀ k ∈ KK F, ∃ c : Fin n → ℂ, (∀ i, ‖c i‖ ≤ 1) ∧
  W.Om k φ = ∑ i, c i • e i

def OmCpt : Prop := ∀ φ ∈ Fock D.δ, ∀ C : Set (G1 F), IsCompact C → Dom C fun g => (W.Om g φ).1

def LDom : Prop := ∀ (ι : Type) (s : Set ι) (Φ : ι → S4 F), Dom s (fun i => (Φ i).1) → ∀ C : Set (GL (Fin 2) (A E)), IsCompact C →
  Dom (C ×ˢ s) fun p => (W.L p.1 (Φ p.2)).1

def OmDer : Prop := ∀ Ψ Ψ' : ℝ → S4 F, Der Ψ Ψ' → (∀ g t, Dom (Metric.ball t 1) fun s => (W.Om g (Ψ' s)).1) →
  ∀ g, Der (fun s => W.Om g (Ψ s)) fun s => W.Om g (Ψ' s)

def RedH : Prop := ∀ h, ∀ φ ∈ Fock D.δ, ∃ y, One F y ∧ ∃ φ₁ ∈ Fock D.δ, ∃ m : G1 F,
  ∀ g y', W.Om g (W.L (h * infGL E 2 y') φ) = W.Om (g * m) (W.L (infGL E 2 (y * y')) φ₁)

def ThMaj : Prop := ∀ φ ∈ Fock D.δ, ∀ c : ℝ, 0 < c → ∃ (B : ℝ) (N : ℕ), ∀ y, One F y → ∀ b a, ∀ k ∈ KK F, c ≤ ab a →
  ‖Th (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1‖ ≤ B * Ht y ^ N * ab a ^ 2

def HatMaj : Prop := ∀ φ ∈ Fock D.δ, ∀ y, One F y → ∃ K, IsCompact K ∧ ∀ N, ∃ B : ℝ, ∀ b (a : (A F)ˣ), ∀ k ∈ KK F, ∀ x u t,
  ‖hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, x, u, t]‖ ≤
    B * ab a * wt K N ![0, ((a⁻¹ : (A F)ˣ) : A F) * x, a * u, a * t]

def RowMaj : Prop := ∀ φ ∈ Fock D.δ, ∀ y, One F y → ∀ c : ℝ, 0 < c → ∃ B : ℝ, ∀ b a, ∀ k ∈ KK F, c ≤ ab a →
  ‖ThRow 0 0 (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1‖ ≤ B * ab a

def Transl : Prop := ∀ (f : GL (Fin 2) (A F) → ℂ) φ h h₀,
  lift W M f φ (h * h₀) = lift W M (fun x => f (x * dM (nu F h₀))) (W.L h₀ φ) h

def MovG : Prop := ∀ f : GL (Fin 2) (A F) → ℂ, LRat f → ∀ φ g₀ h,
  lift W M f (W.Om g₀ φ) h = lift W M (fun x => f (x * (gl g₀)⁻¹)) φ h

variable (π : TR.CuspSub F 2)

def ThBound : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ C : Set (GL (Fin 2) (A F)), IsCompact C → ∃ (B : ℝ) (N : ℕ),
  ∀ y, One F y → ∀ g, ∀ x ∈ C, ‖f.1 (gl g * x) * Th (W.Om g (W.L (infGL E 2 y) φ)).1‖ ≤ B * Ht y ^ N

def ThBoundH : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h, ∀ C : Set (GL (Fin 2) (A F)), IsCompact C →
  ∀ C' : Set (GL (Fin 2) (Cinf E)), IsCompact C' → (∀ y ∈ C', One F y) → ∃ B : ℝ,
  ∀ g, ∀ x ∈ C, ∀ y ∈ C', ‖f.1 (gl g * x) * Th (W.Om g (W.L (h * infGL E 2 y) φ)).1‖ ≤ B

def RowBoundH : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h x, ∃ B : ℝ,
  ∀ g, ‖f.1 (gl g * x) * ThRow 0 0 (W.Om g (W.L h φ)).1‖ ≤ B

def UnfoldedThetaIntegralConvergesSimilitudeOne : Prop := ∀ f ∈ π.V, ∀ φ : S4 F, ∀ x,
  (Measurable fun g => Wf f.1 (gl g * x) * hat (W.Om g φ).1 ![0, 1, 1, 0]) ∧
  (∀ b g, Wf f.1 (gl (nU b * g) * x) * hat (W.Om (nU b * g) φ).1 ![0, 1, 1, 0] =
    Wf f.1 (gl g * x) * hat (W.Om g φ).1 ![0, 1, 1, 0]) ∧
  (φ ∈ Fock D.δ → ∀ y, One F y →
    Integrable (iw fun g => Wf f.1 (gl g * x) * hat (W.Om g (W.L (infGL E 2 y) φ)).1 ![0, 1, 1, 0]) M.ν)

def Lin : Prop :=
  (∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ φ' ∈ Fock D.δ, lift W M f.1 (φ + φ') = lift W M f.1 φ + lift W M f.1 φ') ∧
  (∀ f (c : ℂ) φ, lift W M f (c • φ) = c • lift W M f φ) ∧
  (∀ f ∈ π.V, ∀ f' ∈ π.V, ∀ φ ∈ Fock D.δ, lift W M (f + f').1 φ = lift W M f.1 φ + lift W M f'.1 φ) ∧
  ∀ f (c : ℂ) φ, lift W M (c • f) φ = c • lift W M f φ

def FinLift : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ k, ∃ f' ∈ π.V, ∃ φ' ∈ Fock D.δ,
  ∀ h, lift W M f.1 φ (h * finGL E 2 k) = lift W M f'.1 φ' h

def ContOne : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ContinuousOn (fun y => lift W M f.1 φ (infGL E 2 y)) {y | One F y}

def LiftCont : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h, Continuous fun y => lift W M f.1 φ (h * infGL E 2 y)

def Growth : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h, ∃ (C : ℝ) (N : ℕ), ∀ y,
  ‖lift W M f.1 φ (h * infGL E 2 y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N

def RedLift : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h, ∃ f' ∈ π.V, ∃ φ' ∈ Fock D.δ, ∃ y₀ k, h = infGL E 2 y₀ * finGL E 2 k ∧
  φ' = W.L (finGL E 2 k) φ ∧ (∀ x, f'.1 x = f.1 (x * dM (nu F (finGL E 2 k)))) ∧
  ∀ φ₁ y, lift W M f.1 φ₁ (h * infGL E 2 y) = lift W M f'.1 (W.L (finGL E 2 k) φ₁) (infGL E 2 (y₀ * y))

def DerL : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ Y : Lie E 2, (Matrix.of Y).trace = 0 →
  ∀ h, HasDerivAt (fun t => lift W M f.1 φ (h * infGL E 2 (ex Y t))) (lift W M f.1 (O.dL D Y φ) h) 0

def ThDerL : Prop := ∀ φ : S4 F, ∀ Y : Lie E 2, (Matrix.of Y).trace = 0 → ∀ g h t,
  HasDerivAt (fun s => Th (W.Om g (W.L (h * infGL E 2 (ex Y s)) φ)).1) (Th (W.Om g (W.L (h * infGL E 2 (ex Y t)) (O.dL D Y φ))).1) t

def ThDerOm : Prop := ∀ φ : S4 F, ∀ φ' ∈ Fock D.δ, ∀ G : ℝ → G1 F, Continuous G →
  Der (fun s => W.Om (G s) φ) (fun s => W.Om (G s) φ') → ∀ g h t,
  HasDerivAt (fun s => Th (W.Om g (W.L h (W.Om (G s) φ))).1) (Th (W.Om g (W.L h (W.Om (G t) φ'))).1) t

def DerX : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ (Y : Lie E 2) (s : Cinf E), (Matrix.of Y).trace = 0 →
  ∀ h, HasDerivAt (fun t => lift W M f.1 φ (h * infGL E 2 (ex (Y + zE s) t)))
    (lift W M f.1 (O.dL D Y φ) h + lift W M (TR.lie F 2 (zF (trI F s)) f).1 φ h) 0

def LieL : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ Y : Lie E 2, (Matrix.of Y).trace = 0 →
  ∀ Φ : Sm E 2, Φ.1 = lift W M f.1 φ → (lie E 2 Y Φ).1 = lift W M f.1 (O.dL D Y φ)

def MoveH : Prop :=
  ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ w h, lift W M f.1 (O.h w φ) h = -lift W M (TR.Eop w 0 0 f - TR.Eop w 1 1 f : TR.Sm F 2).1 φ h

def DerF : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ c Y, Par c Y → ∀ h,
  HasDerivAt (fun t => lift W M (fun x => f.1 (x * TR.infGL F 2 (c t))) φ h) (lift W M (TR.lie F 2 Y f).1 φ h) 0

def DerOm : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ φ' ∈ Fock D.δ, ∀ G : ℝ → G1 F, Continuous G → G 0 = 1 →
  Der (fun s => W.Om (G s) φ) (fun s => W.Om (G s) φ') → ∀ h,
  HasDerivAt (fun t => lift W M f.1 (W.Om (G t) φ) h) (lift W M f.1 φ' h) 0

def LieZ : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ s : Cinf E,
  ∀ Φ : Sm E 2, Φ.1 = lift W M f.1 φ → (lie E 2 (zE s) Φ).1 = lift W M (TR.lie F 2 (zF (trI F s)) f).1 φ

def Mov : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ φ' ∈ Fock D.δ, ∀ (G : ℝ → G1 F) c Y, Par c Y → (∀ t, gl (G t) = TR.infGL F 2 (c t)) →
  Der (fun s => W.Om (G s) φ) (fun s => W.Om (G s) φ') → lift W M f.1 φ' = -lift W M (TR.lie F 2 Y f).1 φ

def Level : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ Φ : Sm E 2, Φ.1 = lift W M f.1 φ → IsOpen {k | GlobalTheory.CuspRep.finRep E 2 k Φ = Φ}

def KFin : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ Φ : Sm E 2, Φ.1 = lift W M f.1 φ →
  (∀ k, cptRep E 2 k Φ ∈ span W M π) ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E 2 k Φ))

def ZFin : Prop := π.IsRegAlg → ∀ Φ ∈ span W M π,
  FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E 2) => z Φ) '' Zalg E 2))

end Ext

end UpperTheory.ConvolutionTheory.R2.Ff

end
