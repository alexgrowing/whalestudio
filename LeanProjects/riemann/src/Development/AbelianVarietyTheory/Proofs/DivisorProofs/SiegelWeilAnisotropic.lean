import Mathlib
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FlatZetaIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsNormInvSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

def LaurentConst (h : ℂ → ℂ) (s₀ c : ℂ) : Prop :=
  ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧ Tendsto (fun s => h s - p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 c)

open Classical in

def withReal {F : Type} [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Finset (Pl F) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Sf.map ⟨Sum.inr, Sum.inr_injective⟩

section Interface

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B)

def zGlob {π : O.Pi} (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch) (s : ℂ) : ℂ :=
  ∫ g : O.GQ × O.GQ, O.Eis (O.tensor φ₁ φ₂) s (O.io g.1 g.2) * star (O.form π f₁ g.1) * O.form π f₂ g.2 *
    O.muInv g.2 ∂(O.muG.prod O.muG)

def HalfPlaneCont (π : O.Pi) (S : Finset (Pl F)) (t : ℕ) (g : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ g {s | (t : ℝ) / 2 ≤ s.re} ∧
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → HasProd (fun v : {v : Pl F // v ∉ S} => O.Lv π v (s + 1 / 2)) (g s)

def TripleIntegrable {π : O.Pi} (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch) : Prop :=
  Integrable (fun p : (O.GQ × O.GQ) × O.HQ => O.thetaK φ₁ p.1.1 p.2 * star (O.thetaK φ₂ p.1.2 p.2) *
    star (O.form π f₁ p.1.1) * O.form π f₂ p.1.2) ((O.muG.prod O.muG).prod O.muH)

variable (F E) in

def DInvAnalytic : Prop :=
  ∀ (n M : ℕ) (P : HeightOneSpectrum (𝓞 F) → Prop), ∃ e : ℂ → ℂ, AnalyticOnNhd ℂ e {s | 1 / 2 < s.re} ∧
    ∀ s : ℂ, 1 / 2 < s.re → e s ≠ 0 ∧ (∀ w : HeightOneSpectrum (𝓞 F), dvLoc (E := E) n M w s ≠ 0) ∧
      HasProd (fun w : {w // P w} => (dvLoc (E := E) n M w.1 s)⁻¹) (e s)

def Measurability : Prop :=
  SFinite O.muG ∧ (∀ φ, O.good φ → Measurable fun p : O.GQ × O.HQ => O.thetaK φ p.1 p.2) ∧
    (∀ π f, Measurable (O.form π f)) ∧ Measurable O.muInv ∧ ∀ g, ‖O.muInv g‖ = 1

def FlatLocal : Prop :=
  ∀ (π : O.Pi) (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch), O.good φ₁ → O.good φ₂ → ∀ v : Pl F,
    ∃ (Y : Type) (_ : MeasurableSpace Y) (ν : Measure Y) (f : Y → ℂ) (a : Y → ℝ),
      Measurable a ∧ (∀ y, 0 < a y) ∧ (∀ y, a y ≤ 1) ∧ ∀ s : ℂ,
        (O.zconv π f₁ f₂ φ₁ φ₂ v s ↔
          Integrable (GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand f a (((B.rank : ℂ) - A.rank) / 2) s) ν) ∧
        (O.zconv π f₁ f₂ φ₁ φ₂ v s →
          O.Zv π f₁ f₂ φ₁ φ₂ v s = GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatZeta ν f a (((B.rank : ℂ) - A.rank) / 2) s)

def CuspDecay : Prop :=
  ∀ (π : O.Pi) (f₁ f₂ : O.Vec π) (N : ℝ),
    Integrable (fun g : O.GQ × O.GQ => (max 1 (O.ht (O.io g.1 g.2))) ^ N * ‖O.form π f₁ g.1‖ * ‖O.form π f₂ g.2‖)
      (O.muG.prod O.muG)

def SiegelWeilAnisotropic : Prop :=
  ∀ t : ℕ, B.rank = A.rank + t → 1 ≤ t → wittIdx B = 0 → ∀ φ₁ φ₂, O.good φ₁ → O.good φ₂ → ∀ g,
    AnalyticAt ℂ (fun s => O.Eis (O.tensor φ₁ φ₂) s g) ((t : ℂ) / 2) ∧
      O.Eis (O.tensor φ₁ φ₂) ((t : ℂ) / 2) g = Ith O (O.tensor φ₁ φ₂) g

def SiegelWeilConvergent : Prop :=
  ∀ t : ℕ, B.rank = A.rank + t → A.rank < t → ∀ φ₁ φ₂, O.good φ₁ → O.good φ₂ → ∀ g,
    O.Eis (O.tensor φ₁ φ₂) ((t : ℂ) / 2) g = Ith O (O.tensor φ₁ φ₂) g

def EisensteinRegular : Prop :=
  ∀ φ₁ φ₂, O.good φ₁ → O.good φ₂ →
    (∀ s₀ : ℂ, (A.rank : ℝ) / 2 < s₀.re → ∀ g, AnalyticAt ℂ (fun s => O.Eis (O.tensor φ₁ φ₂) s g) s₀) ∧
    ∀ s₀ : ℂ, (∀ g, AnalyticAt ℂ (fun s => O.Eis (O.tensor φ₁ φ₂) s g) s₀) →
      ∃ C N : ℝ, ∀ᶠ s in 𝓝 s₀, Measurable (fun g : O.GQ × O.GQ => O.Eis (O.tensor φ₁ φ₂) s (O.io g.1 g.2)) ∧
        ∀ g, ‖O.Eis (O.tensor φ₁ φ₂) s g‖ ≤ C * (max 1 (O.ht g)) ^ N

def DoublingMeromorphic : Prop :=
  ∀ (π : O.Pi) (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch), O.good φ₁ → O.good φ₂ → Meromorphic (zGlob O f₁ f₂ φ₁ φ₂)

def PairInputs : Prop :=
  Measurability O ∧ FlatLocal O ∧ CuspDecay O ∧ admW O ∧ DoublingBasicIdentity O ∧ SiegelWeilAnisotropic O ∧ SiegelWeilConvergent O ∧
    EisensteinRegular O ∧ DoublingMeromorphic O

variable {O}

def IsTensorModel {π : O.Pi} {n : ℕ} {I Xf : Type} (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (vec : EuclideanSpace ℂ (Fin n) → I → Xf → O.Vec π) (loc : Xf → Xf → HeightOneSpectrum (𝓞 F) → ℂ) : Prop :=
  (∀ ι ι' i a, O.form π (vec (ι + ι') i a) = O.form π (vec ι i a) + O.form π (vec ι' i a)) ∧
  (∀ (c : ℂ) ι i a, O.form π (vec (c • ι) i a) = c • O.form π (vec ι i a)) ∧
  (∀ ι ι' i i' a b, O.be π (vec ι i a) (vec ι' i' b) = ⟪ι, ι'⟫_ℂ) ∧
  (∀ a, ∀ w ∈ Sf, loc a a w = 1) ∧
  ∀ ι ι' i a b, ∫ g, star (O.form π (vec ι i a) g) * O.form π (vec ι' i b) g ∂O.muG = ⟪ι, ι'⟫_ℂ * ∏ w ∈ Sf, loc a b w

def IsLocalValues {π : O.Pi} {n : ℕ} {I K Xf : Type} (t : ℕ) (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (vec : EuclideanSpace ℂ (Fin n) → I → Xf → O.Vec π) (φ : I → K → O.Sch)
    (zf : Xf → Xf → HeightOneSpectrum (𝓞 F) → ℂ) (zr : I → I → K → InfinitePlace F → ℂ) : Prop :=
  ∀ ι ι' i i' k a b,
    (∀ w ∈ Sf, O.Zv π (vec ι i a) (vec ι' i' b) (φ i k) (φ i' k) (Sum.inr w) ((t : ℂ) / 2) = zf a b w) ∧
    ∀ ρ, O.Zv π (vec ι i a) (vec ι' i' b) (φ i k) (φ i' k) (Sum.inl ρ) ((t : ℂ) / 2) = zr i i' k ρ

def IsAdmissible {π : O.Pi} {n : ℕ} {I K Xf : Type} (t : ℕ) (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (vec : EuclideanSpace ℂ (Fin n) → I → Xf → O.Vec π) (φ : I → K → O.Sch) : Prop :=
  ∀ ι ι' i i' k a b, RFData O π (vec ι i a) (vec ι' i' b) (φ i k) (φ i' k) (withReal Sf) ((t : ℂ) / 2)

end Interface

def LocalScalar {P Xf : Type} (Sf : Finset P) (loc zf : Xf → Xf → P → ℂ) : Prop :=
  ∀ w ∈ Sf, ∃ z : ℂ, ∀ a b, zf a b w = z * loc a b w

def IsUnitValue {P Xf : Type} (zf : Xf → Xf → P → ℂ) (w : P) (c : ℂ) : Prop :=
  Nonempty Xf → ∃ a, zf a a w = c

def IsLValue {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B) (π : O.Pi) (S : Finset (Pl F)) (t : ℕ) (c : ℂ) : Prop :=
  ∀ g, HalfPlaneCont O π S t g → c = g ((t : ℂ) / 2)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev ChainObj (D : D7) : Type 1 :=
  ∀ (_μ : D.what₂.Tup) (i : ℕ), RFObj D.host.F D.host.E (D.sp.Y i) (D.sp.Y (i + 1))

abbrev BlockObj (D : D7) : Type 1 :=
  ∀ (_μ : D.what₂.Tup) (j : ℕ), RFObj D.host.F D.host.E (D.sp.W j) (D.sp.V j)

section Towers

variable (T : ThetaX D)

def IsPetClosed (V : HSp D) (ϖ : Submodule ℂ (T.cusp V)) : Prop :=
  ∀ G : T.cusp V, (∀ ε : ℝ, 0 < ε → ∃ G' ∈ ϖ, (T.pet V ((G - G' : T.cusp V) : T.AF V) (G - G')).re < ε) → G ∈ ϖ

def IsIrredCusp (V : HSp D) (ϖ : Submodule ℂ (T.cusp V)) : Prop :=
  ϖ ≠ ⊥ ∧ T.IsStable V (ϖ.map (T.cusp V).subtype) ∧ IsPetClosed T V ϖ ∧
    ∀ ϖ' ≤ ϖ, T.IsStable V (ϖ'.map (T.cusp V).subtype) → IsPetClosed T V ϖ' → ϖ' = ⊥ ∨ ϖ' = ϖ

def InnerProductLowRange (μ : D.what₂.Tup) (i : ℕ) (O : RFObj D.host.F D.host.E (D.sp.Y i) (D.sp.Y (i + 1)))
    (ev : T.AF (D.sp.Y i) →ₗ[ℂ] (O.GQ → ℂ)) : Prop :=
  (D.sp.Y (i + 1)).rank = (D.sp.Y i).rank + D.R.t → D.R.t ≤ (D.sp.Y i).rank →
  (wittIdx (D.sp.Y (i + 1)) = 0 ∨ wittIdx (D.sp.Y (i + 1)) < D.R.t) →
  ∀ ϖ : Submodule ℂ (T.cusp (D.sp.Y i)), IsIrredCusp T _ ϖ →
    (∀ l, 1 ≤ l → l ≤ wittIdx (D.sp.Y (i + 1)) → ∀ (Φ : T.Sch (D.sp.Y i) (T.YsLow D.R.t (i + 1) l)), ∀ G ∈ ϖ,
      Formalism.MainNotions.InnerProductFormulaField.thS T μ i _ Φ G = 0) →
    ∀ (π : O.Pi) (f₁ f₂ : O.Vec π), (∃ G ∈ ϖ, ev (G : T.AF _) = O.form π f₁) → (∃ G ∈ ϖ, ev (G : T.AF _) = O.form π f₂) →
    ∀ φ₁ φ₂, O.good φ₁ → O.good φ₂ → LaurentConst (zGlob O f₁ f₂ φ₁ φ₂) ((D.R.t : ℂ) / 2) (thetaIP O f₁ f₂ φ₁ φ₂)

def LowerLiftsVanish : Prop :=
  ∀ (μ : D.what₂.Tup) (i l : ℕ), i < D.R.m → 1 ≤ l → l ≤ (sigYD D.R (i + 1)).2 →
    ∀ (Φ : T.Sch (D.sp.Y i) (T.YsLow D.R.t (i + 1) l)) (G : T.cusp (D.sp.Y i)), Formalism.MainNotions.InnerProductFormulaField.IsTypeD T i G →
      Formalism.MainNotions.InnerProductFormulaField.thS T μ i _ Φ G = 0

end Towers

variable (Z : DivX D) (T : ThetaX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)

open Classical in

def finPl (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) (μ : D.what₂.Tup) : Finset (Formalism.MainNotions.InnerProductFormulaField.Pl D) :=
  X.Sg ∪ Finset.univ.map (e μ)

def PlacesTie (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) : Prop :=
  ∀ μ, (∀ v, Z.qv μ v = Ideal.absNorm (e μ v).asIdeal) ∧ (∀ v, e μ v ∉ X.Sg) ∧
    ∀ w ∈ finPl Z X e μ, IsSplit (E := D.host.E) w

def DTie : Prop :=
  ∀ a, X.dFin a = ∏' w : Formalism.MainNotions.InnerProductFormulaField.Pl D, dvLoc (E := D.host.E) a (a + D.R.t) w ((D.R.t : ℂ) / 2)

def ConstTie (κC κB : ℕ → ℂ) (rC rB : ℕ → ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → (κC j ≠ 0 ∧ 0 < rC j ∧ X.cCh j = ‖κC j‖ ^ 2 * rC j) ∧
    (κB j ≠ 0 ∧ 0 < rB j ∧ X.cSb j = ‖κB j‖ ^ 2 * rB j)

def ChainTowerTie (μ : D.what₂.Tup) (i : ℕ) (O : RFObj D.host.F D.host.E (D.sp.Y i) (D.sp.Y (i + 1)))
    (evG : T.AF (D.sp.Y i) →ₗ[ℂ] (O.GQ → ℂ)) (evH : T.AF (D.sp.Y (i + 1)) →ₗ[ℂ] (O.HQ → ℂ)) (κ : ℂ) (φ : O.Sch) : Prop :=
  (∀ G, evG (T.conjAF _ G) = star (evG G)) ∧ (∀ G, evH (T.conjAF _ G) = star (evH G)) ∧
  (∀ G G' : T.cusp (D.sp.Y i), T.petY μ i (G : T.AF _) G' = ∫ g, star (evG G g) * evG G' g ∂O.muG) ∧
  (∀ G G' : T.cusp (D.sp.Y (i + 1)),
    T.petY μ (i + 1) (G : T.AF _) G' = (X.volCh Z μ (i + 1) : ℂ) * ∫ h, star (evH G h) * evH G' h ∂O.muH) ∧
  ∀ (G : T.cusp (D.sp.Y i)) (h : O.HQ),
    (T.mY μ i : ℂ) * evH (T.th _ _ (T.carY μ (i + 1) i) (T.carY μ (i + 1) (i + 1)) (T.PhiYup μ i) G) h =
      κ * ∫ g, O.thetaK φ g h * evG G g ∂O.muG

def OneFinitePart (μ : D.what₂.Tup) (i : ℕ) (πf : D.what₂.FT) {O : RFObj D.host.F D.host.E (D.sp.Y i) (D.sp.Y (i + 1))}
    (evG : T.AF (D.sp.Y i) →ₗ[ℂ] (O.GQ → ℂ)) {π : O.Pi} {n : ℕ} {Xf : Type}
    (vec : EuclideanSpace ℂ (Fin n) → Unit → Xf → O.Vec π) : Prop :=
  (∀ x ∈ D.what₂.EEpart πf, Formalism.MainNotions.InnerProductFormulaField.upChain D μ i x ∈ Submodule.span ℂ
    {u : D.what₂.Mult μ i | ∃ ι a, evG ((T.rowAF μ i u : T.cusp _) : T.AF _) = O.form π (vec ι () a)}) ∧
  ∀ ι, ι ≠ 0 → ∃ ϖ : Submodule ℂ (T.cusp (D.sp.Y i)), IsIrredCusp T _ ϖ ∧ (∀ G ∈ ϖ, Formalism.MainNotions.InnerProductFormulaField.IsTypeD T i G) ∧
    ∀ a, ∃ G ∈ ϖ, evG (G : T.AF _) = O.form π (vec ι () a)

def ChainNumbersTie (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) (μ : D.what₂.Tup) (i : ℕ) (πf : D.what₂.FT)
    {O : RFObj D.host.F D.host.E (D.sp.Y i) (D.sp.Y (i + 1))} (π : O.Pi) {Xf : Type}
    (zf : Xf → Xf → Formalism.MainNotions.InnerProductFormulaField.Pl D → ℂ) (zr : Unit → Unit → Unit → InfinitePlace D.host.F → ℂ) (r : ℝ) : Prop :=
  IsLValue O π (withReal (finPl Z X e μ)) D.R.t (X.LChS μ (i + 1) πf) ∧
  (∀ w ∈ X.Sg, IsUnitValue zf w (X.ZgCh μ (i + 1) πf w)) ∧ (∀ v, IsUnitValue zf (e μ v) (Z.ZQ μ v (i + 1))) ∧
  ∏ ρ, zr () () () ρ = (r : ℂ) * X.ZChR (i + 1)

def ChainInputs (O : ChainObj D) (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) (κ : ℕ → ℂ) (r : ℕ → ℝ) : Prop :=
  ∀ μ i, i < D.R.m → ∃ (evG : T.AF (D.sp.Y i) →ₗ[ℂ] ((O μ i).GQ → ℂ)) (evH : T.AF (D.sp.Y (i + 1)) →ₗ[ℂ] ((O μ i).HQ → ℂ))
    (φ : (O μ i).Sch), ChainTowerTie Z T X μ i (O μ i) evG evH (κ (i + 1)) φ ∧ InnerProductLowRange T μ i (O μ i) evG ∧
    ∀ πf, ∃ (π : (O μ i).Pi) (n : ℕ) (Xf : Type) (vec : EuclideanSpace ℂ (Fin n) → Unit → Xf → (O μ i).Vec π)
      (loc zf : Xf → Xf → Formalism.MainNotions.InnerProductFormulaField.Pl D → ℂ) (zr : Unit → Unit → Unit → InfinitePlace D.host.F → ℂ),
      IsTensorModel (finPl Z X e μ) vec loc ∧ IsLocalValues D.R.t (finPl Z X e μ) vec (fun _ (_ : Unit) => φ) zf zr ∧
      OneFinitePart T μ i πf evG vec ∧ IsAdmissible D.R.t (finPl Z X e μ) vec (fun _ (_ : Unit) => φ) ∧
      LocalScalar (finPl Z X e μ) loc zf ∧ (∃ g, HalfPlaneCont (O μ i) π (withReal (finPl Z X e μ)) D.R.t g) ∧
      ChainNumbersTie Z X e μ i πf π zf zr (r (i + 1))

def BlockMapTie (μ : D.what₂.Tup) (j : ℕ) (O : RFObj D.host.F D.host.E (D.sp.W j) (D.sp.V j)) {I K : Type} [Fintype I] [Fintype K]
    (evW : D.what₂.Mj j →ₗ[ℂ] (I → O.GQ → ℂ)) (evV : D.what₂.Mt μ j →ₗ[ℂ] (K → O.HQ → ℂ)) (κ : ℂ) (φ : I → K → O.Sch) : Prop :=
  (∀ x y, ⟪x, y⟫_ℂ = ∑ i, ∫ g, star (evW x i g) * evW y i g ∂O.muG) ∧
  (∀ y k, MemLp (evV y k) 2 O.muH) ∧
  (∀ y y', ⟪y, y'⟫_ℂ = (X.volSb Z μ j : ℂ) * ∑ k, ∫ h, star (evV y k h) * evV y' k h ∂O.muH) ∧
  ∀ y x, ⟪D.what₂.thetaP μ j y, x⟫_ℂ = ∑ i, ∫ g,
    star (κ * (X.volSb Z μ j : ℂ) * ∑ k, ∫ h, O.thetaK (φ i k) g h * evV y k h ∂O.muH) * evW x i g ∂O.muG

def BlockPart (j : ℕ) (πf : D.what₂.FT) {O : RFObj D.host.F D.host.E (D.sp.W j) (D.sp.V j)} {I : Type}
    (evW : D.what₂.Mj j →ₗ[ℂ] (I → O.GQ → ℂ)) {π : O.Pi} {n : ℕ} {Xf : Type}
    (vec : EuclideanSpace ℂ (Fin n) → I → Xf → O.Vec π) : Prop :=
  D.what₂.isot j πf ≤ Submodule.span ℂ {x : D.what₂.Mj j | ∃ ι a, ∀ i, evW x i = O.form π (vec ι i a)}

def LiftHasType (μ : D.what₂.Tup) (j : ℕ) {O : RFObj D.host.F D.host.E (D.sp.W j) (D.sp.V j)} {I K : Type} [Fintype I]
    (evV : D.what₂.Mt μ j →ₗ[ℂ] (K → O.HQ → ℂ)) (φ : I → K → O.Sch) {π : O.Pi} {n : ℕ} {Xf : Type}
    (vec : EuclideanSpace ℂ (Fin n) → I → Xf → O.Vec π) : Prop :=
  ∀ ι a, ∃ y : D.what₂.Mt μ j, ∀ k h, evV y k h = ∑ i, star (thetaLift O (vec ι i a) (φ i k) h)

def BlockNumbersTie (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) (μ : D.what₂.Tup) (j : ℕ) (πf : D.what₂.FT)
    {O : RFObj D.host.F D.host.E (D.sp.W j) (D.sp.V j)} (π : O.Pi) {I K Xf : Type} [Fintype I] [Fintype K]
    (zf : Xf → Xf → Formalism.MainNotions.InnerProductFormulaField.Pl D → ℂ) (zr : I → I → K → InfinitePlace D.host.F → ℂ) (r : ℝ) : Prop :=
  IsLValue O π (withReal (finPl Z X e μ)) D.R.t (X.LsS μ j πf) ∧
  (∀ w ∈ X.Sg, IsUnitValue zf w (X.ZgSb μ j πf w)) ∧ (∀ v, IsUnitValue zf (e μ v) (Z.quotientLocalValueFirst μ v)) ∧
  ∑ k, ∑ i, ∑ i', ∏ ρ, zr i i' k ρ = (r : ℂ) * X.ZSbR j * Fintype.card I

def BlockInputs (O : BlockObj D) (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) (κ : ℕ → ℂ) (r : ℕ → ℝ) : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∃ (I K : Type) (_ : Fintype I) (_ : Fintype K)
    (evW : D.what₂.Mj j →ₗ[ℂ] (I → (O μ j).GQ → ℂ)) (evV : D.what₂.Mt μ j →ₗ[ℂ] (K → (O μ j).HQ → ℂ))
    (φ : I → K → (O μ j).Sch), BlockMapTie Z X μ j (O μ j) evW evV (κ j) φ ∧
    ∀ πf, ∃ (π : (O μ j).Pi) (n : ℕ) (Xf : Type) (vec : EuclideanSpace ℂ (Fin n) → I → Xf → (O μ j).Vec π)
      (loc zf : Xf → Xf → Formalism.MainNotions.InnerProductFormulaField.Pl D → ℂ) (zr : I → I → K → InfinitePlace D.host.F → ℂ),
      IsTensorModel (finPl Z X e μ) vec loc ∧ IsLocalValues D.R.t (finPl Z X e μ) vec φ zf zr ∧
      BlockPart j πf evW vec ∧ LiftHasType μ j evV φ vec ∧ IsAdmissible D.R.t (finPl Z X e μ) vec φ ∧
      LocalScalar (finPl Z X e μ) loc zf ∧ (∃ g, HalfPlaneCont (O μ j) π (withReal (finPl Z X e μ)) D.R.t g) ∧
      BlockNumbersTie Z X e μ j πf π zf zr (r j)

end GlobalTheory.ThetaInner

end
