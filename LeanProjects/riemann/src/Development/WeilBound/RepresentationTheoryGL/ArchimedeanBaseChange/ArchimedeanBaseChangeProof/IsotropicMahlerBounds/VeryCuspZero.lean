import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB

def thetaR {A : Type} [CommRing A] (σ : A →+* A) (n : ℕ) : Monoid.End (GL (Fin n) A) where
  toFun g := ⟨(((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).map σ)ᵀ, ((g : Matrix (Fin n) (Fin n) A).map σ)ᵀ,
    by rw [← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp [Matrix.map_one _ (map_zero σ) (map_one σ)])
  map_mul' := fun a b => Units.ext (by
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul])

theorem thetaR_val {A : Type} [CommRing A] (σ : A →+* A) (n : ℕ) (g : GL (Fin n) A) :
    (thetaR σ n g).val = (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).map σ)ᵀ := rfl

def perp {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (W : Submodule K (Fin n → K)) : Submodule K (Fin n → K) where
  carrier := {y | ∀ x ∈ W, ∑ i, σ (x i) * y i = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun ha hb x hx => by simp [mul_add, Finset.sum_add_distrib, ha x hx, hb x hx]
  smul_mem' := fun c y hy x hx => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum, hy x hx, mul_zero]

theorem perp_bot {K : Type} [Field K] (σ : K →+* K) {n : ℕ} : perp σ (⊥ : Submodule K (Fin n → K)) = ⊤ :=
  eq_top_iff.2 fun _ _ x hx => by simp [(Submodule.mem_bot K).1 hx]

def img {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) : Submodule K (Fin n → K) :=
  W.map (Matrix.toLin' g.val)

def perpD {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (d : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    Submodule K (Fin n → K) := img d (perp σ W)

def nilrad {K : Type} [Field K] {n : ℕ} (W₁ W₂ : Submodule K (Fin n → K)) : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {X | (∀ y, X *ᵥ y ∈ W₂) ∧ (∀ y ∈ W₂, X *ᵥ y ∈ W₁) ∧ ∀ y ∈ W₁, X *ᵥ y = 0}
  zero_mem' := by simp
  add_mem' := fun ha hb => ⟨fun y => by rw [Matrix.add_mulVec]; exact W₂.add_mem (ha.1 y) (hb.1 y),
    fun y hy => by rw [Matrix.add_mulVec]; exact W₁.add_mem (ha.2.1 y hy) (hb.2.1 y hy),
    fun y hy => by rw [Matrix.add_mulVec, ha.2.2 y hy, hb.2.2 y hy, add_zero]⟩
  smul_mem' := fun c X h => ⟨fun y => by rw [Matrix.smul_mulVec]; exact W₂.smul_mem c (h.1 y),
    fun y hy => by rw [Matrix.smul_mulVec]; exact W₁.smul_mem c (h.2.1 y hy),
    fun y hy => by rw [Matrix.smul_mulVec, h.2.2 y hy, smul_zero]⟩

section Degree

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n k : ℕ}

def cV (v : InfinitePlace E) : Ad E →+* ℂ := (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).comp (pInf E)

def cW (w : HeightOneSpectrum (𝓞 E)) : Ad E →+* w.adicCompletion E := (pLoc E w).comp (pFin E)

def embInf (n : ℕ) (v : InfinitePlace E) : GL (Fin n) ℂ →* GA E n := by
  classical
  exact (infGL E n).comp <|
    (Units.map (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom).comp <|
      (MulEquiv.piUnits (M := fun _ : InfinitePlace E => Matrix (Fin n) (Fin n) ℂ)).symm.toMonoidHom.comp
        (MonoidHom.mulSingle (fun _ : InfinitePlace E => GL (Fin n) ℂ) v)

def lognInf (v : InfinitePlace E) (A : Matrix (Fin n) (Fin k) (Ad E)) : ℝ :=
  Real.log (((A.map (cV v))ᴴ * A.map (cV v)).det).re

def lognFin (w : HeightOneSpectrum (𝓞 E)) (A : Matrix (Fin n) (Fin k) (Ad E)) : ℝ :=
  Real.log (⨆ s : Fin k → Fin n, ‖((A.map (cW w)).submatrix s id).det‖)

def frame (x : GA E n) (M : Matrix (Fin n) (Fin k) E) : Matrix (Fin n) (Fin k) (Ad E) :=
  (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))

def degM (x : GA E n) (M : Matrix (Fin n) (Fin k) E) : ℝ :=
  -(∑ v, lognInf v (frame x M) + ∑ᶠ w, lognFin w (frame x M))

def basisMat (W : Submodule E (Fin n → E)) : Matrix (Fin n) (Fin (Module.finrank E W)) E :=
  Matrix.of fun i j => (Module.finBasis E W j : Fin n → E) i

def deg (x : GA E n) (W : Submodule E (Fin n → E)) : ℝ := degM x (basisMat W)

theorem degM_zero (x : GA E n) (M : Matrix (Fin n) (Fin 0) E) : degM x M = 0 := by
  simp [degM, lognInf, lognFin]

def prof (n : ℕ) (τ : ℝ) (k : ℕ) : ℝ := τ * k * (2 * n + 1 - k)

def cutSet (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (τ : ℝ) : Set (GA E n) :=
  {x | (∀ W : Submodule E (Fin n → E), deg x W ≤ prof n τ (Module.finrank E W)) ∧ -τ ≤ deg x ⊤}

def chiT (τ : ℝ) (x : GA E n) : ℂ := (cutSet E n τ).indicator 1 x

def logSizeM (A : Matrix (Fin n) (Fin n) (Ad E)) : ℝ :=
  ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2) +
    ∑ᶠ w, Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖)

def logSize (g : GA E n) : ℝ := logSizeM g.val + logSizeM (g⁻¹ : GA E n).val

def SizeLE (φ : GA E n → ℂ) (r : ℝ) : Prop := ∀ g, φ g ≠ 0 → logSize g ≤ r

structure IsTest (φ : GA E n → ℂ) : Prop where
  cont : Continuous φ
  supp : HasCompactSupport φ
  level : ∃ U : Subgroup (GL (Fin n) (Af E)), IsOpen (U : Set (GL (Fin n) (Af E))) ∧
    ∀ u ∈ U, ∀ g, φ (finGL E n u * g) = φ g ∧ φ (g * finGL E n u) = φ g

theorem isTest_zero : IsTest (0 : GA E n → ℂ) :=
  ⟨continuous_const, HasCompactSupport.zero, ⊤, isOpen_univ, fun _ _ _ => ⟨rfl, rfl⟩⟩

end Degree

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def conjE (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom

abbrev thetaA (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Monoid.End (GA E n) := thetaR (conjAd E) n

abbrev thetaE (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Monoid.End (GL (Fin n) E) := thetaR (conjE E) n

def nrm (d : GL (Fin n) E) : GL (Fin n) E := d * thetaE E n d

def IsRegD (d : GL (Fin n) E) : Prop := (nrm d).val.charpoly.Separable

def IsRegEll (d : GL (Fin n) E) : Prop :=
  IsRegD d ∧ ∀ (τ : E →+* ℂ) (z : ℂ), ((nrm d).val.charpoly.map τ).IsRoot z → ‖z‖ = 1

def RegSupp (φ : GA E n → ℂ) : Prop :=
  ∀ (d : GL (Fin n) E) (x : GA E n), φ (twConj (thetaA E n) x (ratGL E n d)) ≠ 0 → IsRegD d

def kerTw (φ : GA E n → ℂ) (x y : GA E n) : ℂ := ∑ᶠ d : GL (Fin n) E, φ (x⁻¹ * ratGL E n d * thetaA E n y)

def kerTw2 (φ : GA E a × GA E b → ℂ) (x y : GA E a × GA E b) : ℂ :=
  ∑ᶠ d : GL (Fin a) E × GL (Fin b) E,
    φ (x.1⁻¹ * ratGL E a d.1 * thetaA E a y.1, x.2⁻¹ * ratGL E b d.2 * thetaA E b y.2)

def cutTr [MeasurableSpace (GA E n)] (μ : Measure (GA E n)) (F : Set (GA E n)) (τ : ℝ) (φ : GA E n → ℂ) : ℂ :=
  ∫ x in F, chiT τ x * kerTw φ x x ∂μ

def cutTr2 [MeasurableSpace (GA E a)] [MeasurableSpace (GA E b)] (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b))
    (F₁ : Set (GA E a)) (F₂ : Set (GA E b)) (τ : ℝ) (φ : GA E a × GA E b → ℂ) : ℂ :=
  ∫ x in F₁ ×ˢ F₂, chiT τ x.1 * chiT τ x.2 * kerTw2 φ x x ∂(μ₁.prod μ₂)

def ratCent (d : GL (Fin n) E) : Subgroup (GA E n) := (twCent (thetaE E n) d).map (ratGL E n)

def orbTerm [MeasurableSpace (GA E n)] (μ : Measure (GA E n)) (φ : GA E n → ℂ) (d : GL (Fin n) E) : ℂ :=
  quotIntegral μ (ratCent d) Measure.count fun x => φ (twConj (thetaA E n) x (ratGL E n d))

def TwClass (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Type := Quot (TwConjugate (thetaE E n))

def ellSum [MeasurableSpace (GA E n)] (μ : Measure (GA E n)) (φ : GA E n → ℂ) : ℂ :=
  ∑ᶠ (c : TwClass E n) (_ : IsRegEll (Quot.out c)), orbTerm μ φ (Quot.out c)

def toInf [MeasurableSpace (GL (Fin n) ℂ)] (μ : Measure (GL (Fin n) ℂ)) (d : GL (Fin n) ℂ)
    (μd : Measure (twCent (thetaR (starRingEnd ℂ) n) d)) (f : GL (Fin n) ℂ → ℂ) : ℂ :=
  twOrbIntegralC (thetaR (starRingEnd ℂ) n) μ d μd f

def VeryCusp (f : GL (Fin n) ℂ → ℂ) : Prop :=
  (∀ k d, thetaR (starRingEnd ℂ) n k = k → f (twConj (thetaR (starRingEnd ℂ) n) k d) = f d) ∧
    ∀ (d : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≠ ⊥ → W₁ ≤ W₂ →
      perpD (starRingEnd ℂ) d W₁ = W₂ → perpD (starRingEnd ℂ) d W₂ = W₁ →
      ∀ u : nilrad W₁ W₂ → GL (Fin n) ℂ, (∀ X, (u X).val = 1 + X.1) →
      ∀ [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure],
        ∫ X, f (u X * d) ∂ν = 0

def VCAt (v : InfinitePlace E) (φ : GA E n → ℂ) : Prop :=
  ∀ g : GA E n, GeneralLinearGroup.map (cV v) g = 1 → VeryCusp fun d => φ (embInf n v d * g)

theorem veryCusp_zero : VeryCusp (0 : GL (Fin n) ℂ → ℂ) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp⟩

theorem regSupp_zero : RegSupp (0 : GA E n → ℂ) := fun _ _ h => absurd rfl h

end CM

end PositivityTheory.Rg.BcB

end
