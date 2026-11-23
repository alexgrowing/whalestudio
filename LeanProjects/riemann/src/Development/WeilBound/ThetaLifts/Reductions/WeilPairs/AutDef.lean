import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.GoodLat
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.EtaDef
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsBis
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsMore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev tauB (B : Base F E) : InfinitePlace F → (E →+* ℂ) := fun w => (B.emb w).1

structure Ctx (σ : E →ₐ[F] E) (B : Base F E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E) : Prop where
  good : B.IsGood σ
  hS : IsHermND σ JS
  hT : IsHermND σ JT
  h0 : ξ₀ ≠ 0
  hξ : σ ξ₀ = -ξ₀
  inf : IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ
  chart : IsChartF θ ι

variable (F E) in

def finIdem : AEF F E := algebraMap (AF F) (AEF F E) (pairA F 0 1)

theorem infPartF_finIdem : infPartF F E (finIdem F E) = 0 := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 0 1 ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 0 1) = 0 from rfl, TensorProduct.zero_tmul]

theorem finIdem_smul_fin {nS nT : ℕ} (x : WOF F E nS nT) : (finIdem F E • x).map (infPartF F E) = 0 := by
  funext i j
  show infPartF F E (finIdem F E * x i j) = 0
  rw [map_mul, infPartF_finIdem, zero_mul]

variable (F) in

def finRatF {nS nT : ℕ} : Matrix (Fin nT) (Fin nS) E →ₗ[𝓞 E] XFF F E nS nT where
  toFun y := XFF.mk (finIdem F E • ratWF (F := F) y) (finIdem_smul_fin _)
  map_add' x y := XFF.ext (by
    show finIdem F E • ratWF (F := F) (x + y) = finIdem F E • ratWF (F := F) x + finIdem F E • ratWF (F := F) y
    rw [← smul_add]
    congr 1
    funext i j
    exact (incAF F E).map_add (x i j) (y i j))
  map_smul' r x := XFF.ext (by
    show finIdem F E • ratWF (F := F) (r • x) = intAF F r • finIdem F E • ratWF (F := F) x
    rw [smul_comm]
    congr 1
    funext i j
    exact (incAF F E).map_mul (r : E) (x i j))

def infRatF {nS nT : ℕ} (τ : InfinitePlace F → (E →+* ℂ)) : Matrix (Fin nT) (Fin nS) E →+ (IxF F nS nT → ℂ) where
  toFun y := fun p => τ p.2 (y p.1.1 p.1.2)
  map_zero' := funext fun p => (τ p.2).map_zero
  map_add' x y := funext fun p => (τ p.2).map_add _ _

def piWA {nS nT : ℕ} (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) : WOF F E nS nT →+ (IxF F nS nT → ℂ) where
  toFun := piWF θ
  map_zero' := funext fun p => by simp [piWF]
  map_add' x y := funext fun p => by simp [piWF]

def iotaA {nS nT : ℕ} (ι : (InfinitePlace F → ℂ) →+ AEF F E) : (IxF F nS nT → ℂ) →+ WOF F E nS nT where
  toFun := iotaVF ι
  map_zero' := iotaVF_zero ι
  map_add' := iotaVF_add ι

section Lin

variable {κ : Type} [Fintype κ]

def omV (H : Matrix κ κ ℂ) : (κ → ℂ) →ₗ[ℝ] (κ → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => -(star y ⬝ᵥ H *ᵥ x).im)
    (fun x x' y => by rw [mulVec_add, dotProduct_add, Complex.add_im]; ring)
    (fun c x y => by rw [mulVec_smul, dotProduct_smul, Complex.smul_im, smul_eq_mul, smul_eq_mul]; ring)
    (fun x y y' => by rw [star_add, add_dotProduct, Complex.add_im]; ring)
    (fun c x y => by rw [star_smul, star_trivial, smul_dotProduct, Complex.smul_im, smul_eq_mul, smul_eq_mul]; ring)

theorem omV_apply (H : Matrix κ κ ℂ) (x y : κ → ℂ) : omV H x y = -(star y ⬝ᵥ H *ᵥ x).im := rfl

def jV (s : Matrix κ κ ℂ) : (κ → ℂ) →ₗ[ℝ] (κ → ℂ) where
  toFun v := Complex.I • s *ᵥ v
  map_add' x y := by rw [mulVec_add, smul_add]
  map_smul' c x := by rw [mulVec_smul, smul_comm]; rfl

theorem jV_apply (s : Matrix κ κ ℂ) (v : κ → ℂ) : jV s v = Complex.I • s *ᵥ v := rfl

def gaussV (H s g : Matrix κ κ ℂ) (v : κ → ℂ) : ℂ :=
  Complex.exp (-(Real.pi * Complex.I) * (omV H (g *ᵥ v) v : ℝ)) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (omV H (g *ᵥ v - v) (jV s (g *ᵥ v - v)) : ℝ))

end Lin

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)

def IsRatF {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) (a : Matrix (Fin n) (Fin n) E) : Prop :=
  mtF σ J g = a.map (incAF F E)

def gamQF (ψ : AddChar (AF F) ℂ) (x y : Matrix (Fin nT) (Fin nS) E) : ℂ :=
  gamFF σ JS JT ξ₀ ψ (finRatF F x) (finRatF F y)

structure CartF (B : Base F E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ))
    (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ) : Prop where
  sq : s * s = 1
  pos : (HMF JS JT ξ₀ (tauB B) * s).PosDef
  cen : ∀ (k : GAF σ JT) (t : E), IsRatF σ JT k (t • 1) → s * mMF σ JS JT θ (1, k) = mMF σ JS JT θ (1, k) * s

def IsVacF (ψ : AddChar (AF F) ℂ) (ι : (InfinitePlace F → ℂ) →+ AEF F E) (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ)
    (f : WOF F E nS nT → ℂ) : Prop :=
  ∀ x z, deriv (fun t : ℝ => heisOF σ JS JT ξ₀ ψ (iotaVF ι (t • z)) f x) 0 +
    Complex.I * deriv (fun t : ℝ => heisOF σ JS JT ξ₀ ψ (iotaVF ι (t • jV s z)) f x) 0 = 0

def chiLatF (ψ : AddChar (AF F) ℂ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E) (x : WOF F E nS nT) : ℂ :=
  if finIdem F E • x ∈ latOF F E nS nT Λ then
    ψ (symplOHF σ JS JT ξ₀ (intAF F w • finIdem F E • x) (finIdem F E • x)) else 0

def serF (B : Base F E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E)
    (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
    (a : IxF F nS nT → ℂ) : WOF F E nS nT → ℂ :=
  GlobalTheory.HeisenbergGaussianSeries.series (G := WOF F E nS nT) (piWA θ) (iotaA ι) (fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y))
    (omV (HMF JS JT ξ₀ (tauB B))) (jV s) (ratLF F E nS nT) (chiLatF σ JS JT ξ₀ B.ψ Λ w) a

def zF (η : (AEF F E)ˣ →* Circle) (ε : AEF F E) (h : ε * ε = ε) (p : GAF σ JS × GAF σ JT) : Circle :=
  ((η ^ nT) (GlobalTheory.SplitDetCharF.cutDet σ JS ε h p.1))⁻¹ * (η ^ nS) (GlobalTheory.SplitDetCharF.cutDet σ JT ε h p.2)

structure IsHalfF (ε : AEF F E) : Prop where
  idem : ε * ε = ε
  orth : ε * cAF σ ε = 0
  fin : infPartF F E ε = 0
  split : ∀ e, IsSplitIdemF σ e → (ε * e = e ∧ ε * cAF σ e = 0) ∨ (ε * e = 0 ∧ ε * cAF σ e = cAF σ e)

end PositivityTheory.ThKW

end
