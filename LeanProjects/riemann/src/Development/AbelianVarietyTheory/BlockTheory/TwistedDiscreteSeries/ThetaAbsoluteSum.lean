import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.MixModel GlobalTheory.Grow
open scoped TensorProduct NNReal ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.WordMatrixSeminorms

variable {D : D7}

abbrev Letter (D : D7) (m n : ℕ) : Type := D.what₂.Tau × Fin m × Fin n × Bool

def Letter.mat {m n : ℕ} (a : Letter D m n) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)

section Semi

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))

def wordOp (w : List (Letter D T.rank S.rank)) (f : WO S T → ℂ) : WO S T → ℂ :=
  w.foldr (fun a φ => dRho (heisO ψ S T) θ a.1 a.mat φ) f

open Classical in

def semiOn (P : D.what₂.Tau → Prop) (d : ℕ) (f : WO S T → ℂ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (d + 1), ∑ w : Fin k → Letter D T.rank S.rank,
    if ∀ i, P (w i).1 then eLpNorm (wordOp ψ θ S T (List.ofFn w) f) 2 (μ.restrict 𝓕) else 0

def semi (d : ℕ) (f : WO S T → ℂ) : ℝ≥0∞ := semiOn ψ θ S T μ 𝓕 (fun _ => True) d f

def HasLevel (U : AddSubgroup (WO S T)) (f : WO S T → ℂ) : Prop :=
  ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f

def coef (f : WO S T → ℂ) (a : WO S T) : ℂ := ∫ w in 𝓕, heisO ψ S T a f w * starRingEnd ℂ (f w) ∂μ

def IsPureAt (τ : D.what₂.Tau) (f : WO S T → ℂ) : Prop :=
  ∀ a b : WO S T, a.map (finPart D) = 0 → (∀ τ', τ' ≠ τ → compAt θ τ' a = 0) → compAt θ τ b = 0 →
    coef ψ S T μ 𝓕 f (a + b) * coef ψ S T μ 𝓕 f 0 = coef ψ S T μ 𝓕 f a * coef ψ S T μ 𝓕 f b

end Semi

section Sums

variable {S S₀ T T₀ : HSp D} {ρ ρ' : ℕ} (ψ : AddChar (AF D.host.F) ℂ)

def absSum (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) : ℝ≥0∞ :=
  ∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ μ 𝓕 f x 0‖ₑ

def absSum₂ (d : HypDec S S₀ ρ) (d' : HypDec T T₀ ρ') (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ))
    (μ' : Measure (Mx D ρ' S₀.rank)) (𝓕' : Set (Mx D ρ' S₀.rank)) (f : WO S T → ℂ) : ℝ≥0∞ :=
  ∑' x : ratMx D T.rank ρ, ∑' y : ratMx D S₀.rank ρ', ‖d'.mixT S₀ ψ μ' 𝓕' (d.mixS T ψ μ 𝓕 f x) y 0‖ₑ

def comb {n : ℕ} (u : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E) (l : Fin n → AF D.host.F) : WO S T :=
  ∑ i, algebraMap (AF D.host.F) (AE D) (l i) • (rat (u i) : Mx D T.rank S.rank)

variable (S T) in

def IsLagPair (u u' : Fin (S.rank * T.rank) → Matrix (Fin T.rank) (Fin S.rank) D.host.E) : Prop :=
  ∀ i j, symplO S T (rat (u i)) (rat (u j)) = 0 ∧ symplO S T (rat (u' i)) (rat (u' j)) = 0 ∧
    symplO S T (rat (u i)) (rat (u' j)) = if i = j then 1 else 0

def ratVec (D : D7) (n : ℕ) : AddSubgroup (Fin n → AF D.host.F) :=
  ((algebraMap D.host.F (AF D.host.F)).toAddMonoidHom.compLeft (Fin n)).range

def lagVal {n : ℕ} (u u' : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E) (μ : Measure (Fin n → AF D.host.F))
    (𝓕 : Set (Fin n → AF D.host.F)) (f : WO S T → ℂ) (l : Fin n → AF D.host.F) : ℂ :=
  ∫ a in 𝓕, heisO ψ S T (comb u' a) (heisO ψ S T (comb u l) f) 0 ∂μ

def lagSum {n : ℕ} (u u' : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E) (μ : Measure (Fin n → AF D.host.F))
    (𝓕 : Set (Fin n → AF D.host.F)) (f : WO S T → ℂ) : ℝ≥0∞ :=
  ∑' l : ratVec D n, ‖lagVal ψ u u' μ 𝓕 f l‖ₑ

end Sums

section Lift

variable {S T : HSp D}

variable (T) in

def RapidMeas (G : GA D T → ℂ) : Prop :=
  (∀ γ ∈ GQ T, ∀ h, G (γ * h) = G h) ∧ Measurable G ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖G h‖ * quotHeight T h ^ N ≤ C

theorem rapidMeas_of_rapidDec {G : GA D T → ℂ} (h : RapidDec T G) : RapidMeas T G :=
  ⟨h.1, h.2.1.measurable, h.2.2⟩

def weightInt (A : ℕ) (ν : Measure (GA D T)) (𝓖 : Set (GA D T)) (G : GA D T → ℂ) : ℝ≥0∞ :=
  ∫⁻ h in 𝓖, ENNReal.ofReal (quotHeight T h ^ A) * ‖G h‖ₑ ∂ν

def lift (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D T)) (𝓖 : Set (GA D T))
    (f : WO S T → ℂ) (G : GA D T → ℂ) : GA D S → ℂ :=
  Formalism.IndefR.Lift.liftInt ν 𝓖 (thetaKO om) f G

def dOm (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (θ : InfFam D) (τ : D.what₂.Tau)
    (X : Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  fun w => deriv (fun t : ℝ => om (oneP θ S τ X t, 1) f w) 0

end Lift

section Statements

variable (A d : ℕ) {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
  (θ : InfFam D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))

structure PairBounds : Prop where

  semi_ne_top : ∀ k f, IsThetaFunO ψ S T f → semi ψ θ S T μ 𝓕 k f ≠ ∞

  mix : ∀ (S₀ : HSp D) (ρ : ℕ) (e : HypDec S S₀ ρ) (μ₁ : Measure (Mx D T.rank ρ)) (𝓕₁ : Set (Mx D T.rank ρ)),
    IsCovolOne (ratMx D T.rank ρ) μ₁ 𝓕₁ → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
    ∃ C : ℝ≥0, ∀ f, IsThetaFunO ψ S T f → HasLevel ψ S T U f →
      (∀ g h, absSum ψ e μ₁ 𝓕₁ (om (g, h) f) ≤
        C * semi ψ θ S T μ 𝓕 d f * ENNReal.ofReal ((height S g * height T h) ^ A)) ∧
      ∀ (ν : Measure (GA D T)) (𝓖 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓖 ν →
        ∀ G, RapidMeas T G → ∀ g, ∫⁻ h in 𝓖, absSum ψ e μ₁ 𝓕₁ (om (g, h) f) * ‖G h‖ₑ ∂ν ≤
          C * semi ψ θ S T μ 𝓕 d f * ENNReal.ofReal (height S g ^ A) * weightInt A ν 𝓖 G

  mix₂ : ∀ (S₀ T₀ : HSp D) (ρ ρ' : ℕ) (e : HypDec S S₀ ρ) (e' : HypDec T T₀ ρ')
    (μ₁ : Measure (Mx D T.rank ρ)) (𝓕₁ : Set (Mx D T.rank ρ))
    (μ₂ : Measure (Mx D ρ' S₀.rank)) (𝓕₂ : Set (Mx D ρ' S₀.rank)),
    IsCovolOne (ratMx D T.rank ρ) μ₁ 𝓕₁ → IsCovolOne (ratMx D ρ' S₀.rank) μ₂ 𝓕₂ →
    ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
    ∃ C : ℝ≥0, ∀ f, IsThetaFunO ψ S T f → HasLevel ψ S T U f → ∀ g h,
      absSum₂ ψ e e' μ₁ 𝓕₁ μ₂ 𝓕₂ (om (g, h) f) ≤
        C * semi ψ θ S T μ 𝓕 d f * ENNReal.ofReal ((height S g * height T h) ^ A)

  weight_ne_top : ∀ (ν : Measure (GA D T)) (𝓖 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓖 ν →
    ∀ G, RapidMeas T G → weightInt A ν 𝓖 G ≠ ∞

  lift_le : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
    ∃ C : ℝ≥0, ∀ f, IsThetaFunO ψ S T f → HasLevel ψ S T U f →
      ∀ (ν : Measure (GA D T)) (𝓖 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓖 ν →
        ∀ G, RapidMeas T G → ∀ g, IntegrableOn (fun h => thetaKO om g h f * G h) 𝓖 ν ∧
          ‖lift om ν 𝓖 f G g‖ₑ ≤ C * semi ψ θ S T μ 𝓕 d f * ENNReal.ofReal (height S g ^ A) * weightInt A ν 𝓖 G

  dOm_theta : ∀ τ, ∀ X ∈ lieAt S τ, ∀ f, IsThetaFunO ψ S T f →
    (∀ w, HasDerivAt (fun t : ℝ => om (oneP θ S τ X t, 1) f w) (dOm om θ τ X f w) 0) ∧
      IsThetaFunO ψ S T (dOm om θ τ X f) ∧ ∀ U, HasLevel ψ S T U f → HasLevel ψ S T U (dOm om θ τ X f)

  dOm_cont : ∀ τ, ∀ X ∈ lieAt S τ, ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ k : ℕ,
    ∃ (k' : ℕ) (C : ℝ≥0), ∀ f, IsThetaFunO ψ S T f → HasLevel ψ S T U f →
      semi ψ θ S T μ 𝓕 k (dOm om θ τ X f) ≤ C * semi ψ θ S T μ 𝓕 k' f

  lift_deriv : ∀ τ, ∀ X ∈ lieAt S τ, ∀ f, IsThetaFunO ψ S T f →
    ∀ (ν : Measure (GA D T)) (𝓖 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓖 ν →
      ∀ G, RapidMeas T G → ∀ g,
        HasDerivAt (fun t : ℝ => lift om ν 𝓖 f G (g * oneP θ S τ X t)) (lift om ν 𝓖 (dOm om θ τ X f) G g) 0

def LagBound : Prop :=
  ∀ u u' : Fin (S.rank * T.rank) → Matrix (Fin T.rank) (Fin S.rank) D.host.E, IsLagPair S T u u' →
    ∀ (μ₁ : Measure (Fin (S.rank * T.rank) → AF D.host.F)) (𝓕₁ : Set (Fin (S.rank * T.rank) → AF D.host.F)),
      μ₁.IsAddHaarMeasure → IsAddFundamentalDomain (ratVec D (S.rank * T.rank)) 𝓕₁ μ₁ → μ₁ 𝓕₁ = 1 →
      ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
      ∃ C : ℝ≥0, ∀ f, IsThetaFunO ψ S T f → HasLevel ψ S T U f → ∀ g h,
        lagSum ψ u u' μ₁ 𝓕₁ (om (g, h) f) ≤ C * semi ψ θ S T μ 𝓕 d f * ENNReal.ofReal ((height S g * height T h) ^ A)

def TensorBound : Prop :=
  ∀ τ f, IsThetaFunO ψ S T f → IsPureAt ψ θ S T μ 𝓕 τ f →
    semi ψ θ S T μ 𝓕 d f * eLpNorm f 2 (μ.restrict 𝓕) ≤
      2 ^ d * semiOn ψ θ S T μ 𝓕 (fun τ' => τ' = τ) d f * semiOn ψ θ S T μ 𝓕 (fun τ' => τ' ≠ τ) d f

end Statements

def ForPairs (D : D7) (n : ℕ)
    (P : ∀ {S T : HSp D}, AddChar (AF D.host.F) ℂ → (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) → InfFam D →
      Measure (WO S T) → Set (WO S T) → Prop) : Prop :=
  ∀ S T : HSp D, S.rank * T.rank = n → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
      IsCovolOne (ratMx D T.rank S.rank) μ 𝓕 → P ψ om θ μ 𝓕

def ThetaGrowth : Prop :=
  ∀ deg n : ℕ, ∃ A d : ℕ, ∀ D : D7, Module.finrank ℚ D.host.F = deg →
    ForPairs D n fun ψ om θ μ 𝓕 => PairBounds A d ψ om θ μ 𝓕

def ThetaGrowthAt (D : D7) : Prop :=
  ∀ n : ℕ, ∃ A d : ℕ, ForPairs D n fun ψ om θ μ 𝓕 => PairBounds A d ψ om θ μ 𝓕

def ThetaGrowthFull : Prop :=
  ∀ deg n : ℕ, ∃ A d : ℕ, ∀ D : D7, Module.finrank ℚ D.host.F = deg →
    ForPairs D n fun ψ om θ μ 𝓕 =>
      PairBounds A d ψ om θ μ 𝓕 ∧ LagBound A d ψ om θ μ 𝓕 ∧ TensorBound d ψ θ μ 𝓕

theorem ThetaGrowth.at (h : ThetaGrowth) (D : D7) : ThetaGrowthAt D := fun n =>
  let ⟨A, d, H⟩ := h _ n
  ⟨A, d, H D rfl⟩

theorem ThetaGrowthFull.thetaGrowth (h : ThetaGrowthFull) : ThetaGrowth := fun deg n =>
  let ⟨A, d, H⟩ := h deg n
  ⟨A, d, fun D hD S T hn ψ χS χT om ho θ hθ μ 𝓕 hμ => (H D hD S T hn ψ χS χT om ho θ hθ μ 𝓕 hμ).1⟩

section Basic₂

variable {A d : ℕ} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {θ : InfFam D} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

example (f : WO S T → ℂ) : semi ψ θ S T μ 𝓕 0 f = eLpNorm f 2 (μ.restrict 𝓕) := by
  simp [semi, semiOn, wordOp]

theorem PairBounds.rder_lift (H : PairBounds A d ψ om θ μ 𝓕) {τ : D.what₂.Tau} {X : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hX : X ∈ lieAt S τ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {ν : Measure (GA D T)} {𝓖 : Set (GA D T)}
    (hν : ν.IsHaarMeasure) (h𝓖 : IsFundamentalDomain (GQ T) 𝓖 ν) {G : GA D T → ℂ} (hG : RapidMeas T G) :
    Rder θ S τ X (lift om ν 𝓖 f G) = lift om ν 𝓖 (dOm om θ τ X f) G :=
  funext fun g => (H.lift_deriv τ X hX f hf ν 𝓖 hν h𝓖 G hG g).deriv

theorem PairBounds.modGrowthExp_lift (H : PairBounds A d ψ om θ μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {ν : Measure (GA D T)} {𝓖 : Set (GA D T)} (hν : ν.IsHaarMeasure) (h𝓖 : IsFundamentalDomain (GQ T) 𝓖 ν)
    {G : GA D T → ℂ} (hG : RapidMeas T G) : ModGrowthExp S A (lift om ν 𝓖 f G) := by
  obtain ⟨U, hU, hfU⟩ := hf.level
  obtain ⟨C, hC⟩ := H.lift_le U hU
  have h1 := H.semi_ne_top d f hf
  have h2 := H.weight_ne_top ν 𝓖 hν h𝓖 G hG
  refine ⟨(C * semi ψ θ S T μ 𝓕 d f * weightInt A ν 𝓖 G).toReal, fun g => ?_⟩
  have h3 := (hC f hf hfU ν 𝓖 hν h𝓖 G hG g).2
  rw [mul_right_comm] at h3
  have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h1) h2) ENNReal.ofReal_ne_top) h3
  rwa [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos (height_pos S g) A).le] at h4

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.WordMatrixSeminorms

end
