import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder

namespace Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Mx (D : D7) (m n : ℕ) : Type := Matrix (Fin m) (Fin n) (AE D)

scoped instance measMx (m n : ℕ) : MeasurableSpace (Mx D m n) := borel _

abbrev InfFam (D : D7) : Type := D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

section Orient

abbrev WO (S T : HSp D) : Type := Mx D T.rank S.rank

def hO (S T : HSp D) (x y : WO S T) : AE D :=
  ∑ a, ∑ b, ∑ c, ∑ d, incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a

def symplO (S T : HSp D) (x y : WO S T) : AF D.host.F :=
  Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * hO S T x y)

def symplOH (S T : HSp D) (x y : WO S T) : AF D.host.F :=
  algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x y

def heisO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (f : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ψ (symplOH S T w w₀) * f (w + w₀)

def actO (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) : WO S T :=
  HMul.hMul (HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)

structure IsThetaFunO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : Prop where

  quasi : ∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w

  level : ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f
  cont : Continuous f

  smooth : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) →
    ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)

def splitFacO (χS χT : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) : Circle := (χT x)⁻¹ * χS y

structure IsWeilDatumO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where
  std : IsStdChar D ψ (-1)

  hecS : IsHeckeChar D χS

  hecT : IsHeckeChar D χT

  resS : ResEta D χS S.rank

  resT : ResEta D χT T.rank
  om_pres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)
  om_heis : ∀ g h w₀ f, IsThetaFunO ψ S T f →
    om (g, h) (heisO ψ S T w₀ f) = heisO ψ S T (actO S T g h w₀) (om (g, h) f)
  om_aut : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → om (γ, γ') f 0 = f 0
  om_cont : ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun p : GA D S × GA D T => om p f w
  om_unit : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ p f, IsThetaFunO ψ S T f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ
  om_split : ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ∀ f, IsThetaFunO ψ S T f → ℓ (om (g, h) f) = (r : ℂ) * (splitFacO χS χT x y : ℂ) * ℓ f

def thetaKO {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    (f : WO S T → ℂ) : ℂ :=
  om (g, h) f 0

def toTWsmall (S T : HSp D) (x : WO S T) : WA S T :=
  (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) ((S.gram⁻¹).map (incA D))).transpose

def toTWlarge (S T : HSp D) (x : WO S T) : WA T S :=
  (HMul.hMul ((S.gram⁻¹).map (incA D)) ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose).transpose

end Orient

section Real

variable {m n : ℕ}

def compAt (θ : InfFam D) (τ : D.what₂.Tau) (w : Mx D m n) : Matrix (Fin m) (Fin n) ℂ :=
  w.map fun a => θ τ (infPart D a)

open Classical in

def IsLineAt (θ : InfFam D) (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (L : ℝ →+ Mx D m n) : Prop :=
  Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧
    ∀ t τ', compAt θ τ' (L t) = if τ' = τ then (t : ℂ) • z else 0

def lineAt (θ : InfFam D) (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) : ℝ →+ Mx D m n :=
  Classical.epsilon (IsLineAt θ τ z)

def dRho (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (θ : InfFam D) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (f : Mx D m n → ℂ) : Mx D m n → ℂ :=
  fun x => deriv (fun t : ℝ => hs (lineAt θ τ z t) f x) 0

def IsCartanInv {k : ℕ} (G s : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  s * s = 1 ∧ sᴴ * G * s = G ∧ (G * s).PosDef

def cplxO (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin m) (Fin n) ℂ :=
  Complex.I • (sT * z * sS)

def actC (V W : HSp D) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ) (b : Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (z : Matrix (Fin V.rank) (Fin W.rank) ℂ) : Matrix (Fin V.rank) (Fin W.rank) ℂ :=
  if V.rank ≤ W.rank then a.map (starRingEnd ℂ) * z * b.transpose
  else a * z * (b.map (starRingEnd ℂ)).transpose

def cplxT (V W : HSp D) (sV : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW : Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (z : Matrix (Fin V.rank) (Fin W.rank) ℂ) : Matrix (Fin V.rank) (Fin W.rank) ℂ :=
  Complex.I • actC V W sV sW z

def annih (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (θ : InfFam D) (τ : D.what₂.Tau)
    (J : Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ) (z : Matrix (Fin m) (Fin n) ℂ)
    (f : Mx D m n → ℂ) : Mx D m n → ℂ :=
  dRho hs θ τ z f + Complex.I • dRho hs θ τ (J z) f

def crea (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (θ : InfFam D) (τ : D.what₂.Tau)
    (J : Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ) (z : Matrix (Fin m) (Fin n) ℂ)
    (f : Mx D m n → ℂ) : Mx D m n → ℂ :=
  dRho hs θ τ z f - Complex.I • dRho hs θ τ (J z) f

def fockScale (D : D7) (τ : D.what₂.Tau) : ℝ :=
  2 * Real.sqrt (2 * Real.pi * ‖tauE D τ D.host.xi0‖)

def aPlus (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (θ : InfFam D) (τ : D.what₂.Tau)
    (J : Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ) (u : Matrix (Fin m) (Fin n) ℂ)
    (f : Mx D m n → ℂ) : Mx D m n → ℂ :=
  ((fockScale D τ : ℂ)⁻¹) • crea hs θ τ J u f

def IsFockVacAt (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (θ : InfFam D) (τ : D.what₂.Tau)
    (J : Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ) (f : Mx D m n → ℂ) : Prop :=
  ∀ z, annih hs θ τ J z f = 0

def unitMap (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (j : Fin n) :
    Matrix (Fin m) (Fin n) ℂ :=
  B' * Matrix.single i j (1 : ℂ) * B⁻¹

def IsONBasis {k : ℕ} (G s B : Matrix (Fin k) (Fin k) ℂ) (p : ℕ) : Prop :=
  ∃ ε : Fin k → ℝ, (∀ a, (ε a = 1 ∧ a.val < p) ∨ (ε a = -1 ∧ p ≤ a.val)) ∧
    Bᴴ * G * B = Matrix.diagonal (fun a => (ε a : ℂ)) ∧ s * B = B * Matrix.diagonal (fun a => (ε a : ℂ))

def opPow {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (k : ι →₀ ℕ) (f : X → ℂ) : X → ℂ :=
  (Multiset.toList (Finsupp.toMultiset k)).foldr (fun i g => A i g) f

def polyAct {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (P : MvPolynomial ι ℂ) (f : X → ℂ) : X → ℂ :=
  ∑ k ∈ P.support, P.coeff k • opPow A k f

def pureTensorL {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) : MvPolynomial ι ℂ →ₗ[ℂ] (X → ℂ) :=
  (MvPolynomial.basisMonomials ι ℂ).constr ℂ (fun k : ι →₀ ℕ => opPow A k f)

abbrev FVar (D : D7) (m n : ℕ) : Type := D.what₂.Tau × Fin m × Fin n

def aPlusAll (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (θ : InfFam D)
    (J : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ)
    (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) :
    FVar D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ) :=
  fun k => aPlus hs θ k.1 (J k.1) (unitMap (B k.1) (B' k.1) k.2.1 k.2.2)

def fockVec (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (θ : InfFam D)
    (J : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ)
    (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (P : MvPolynomial (FVar D m n) ℂ) (f : Mx D m n → ℂ) : Mx D m n → ℂ :=
  pureTensorL (aPlusAll hs θ J B B') f P

end Real

section Fin

variable {m n : ℕ}

def latO (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : AddSubgroup (WO S T) :=
  AddSubgroup.closure {w | ∃ α ∈ intAf D.host.F, (∀ v, ¬ P v → evalV D.host.F v α = 0) ∧
    ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ s ∈ LS, ∃ t ∈ LT,
      w = Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)}

def latT (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : AddSubgroup (WA V W) :=
  AddSubgroup.closure {w | ∃ α ∈ intAf D.host.F, (∀ v, ¬ P v → evalV D.host.F v α = 0) ∧
    ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ LV, ∃ y ∈ LW,
      w = Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (if V.rank ≤ W.rank then a * star (x i) * y j else a * x i * star (y j))}

def IsHalf (e : AE D) (u : Mx D m n) : Prop := ∀ i j, e * u i j = u i j

def IsLatVac (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (Λ : AddSubgroup (Mx D m n))
    (f : Mx D m n → ℂ) : Prop :=
  (∀ u ∈ Λ, hs (2 • u) f = f) ∧ ∀ e, IsSplitIdem D e → ∀ u ∈ Λ, IsHalf e u → hs u f = f

end Fin

section Vac

variable {m n : ℕ}

def IsCovolOne (Γ : AddSubgroup (Mx D m n)) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) : Prop :=
  μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1

def nrm2 (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f : Mx D m n → ℂ) : ℝ := ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ

structure IsVacuum (thf : (Mx D m n → ℂ) → Prop) (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (Γ : AddSubgroup (Mx D m n)) (θ : InfFam D) (J : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ)
    (Λ : AddSubgroup (Mx D m n)) (f : Mx D m n → ℂ) : Prop where
  inf : IsInfFam θ
  theta : thf f
  lat : IsLatVac hs Λ f
  fock : ∀ τ, IsFockVacAt hs θ τ (J τ) f
  norm : AllSome (fun p : Measure (Mx D m n) × Set (Mx D m n) => IsCovolOne Γ p.1 p.2) fun p => nrm2 p.1 p.2 f = 1

def IsVacO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO S T → ℂ) : Prop :=
  IsStdChar D ψ (-1) ∧ IsVacuum (IsThetaFunO ψ S T) (heisO ψ S T) (ratL T S) θ (fun τ => cplxO (sS τ) (sT τ))
    (latO S T LS LT fun _ => True) f

def IsVacT (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D)
    (sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E)) (f : WA V W → ℂ) : Prop :=
  IsStdChar D ψ (-1) ∧ IsVacuum (IsThetaFun ψ V W) (Heisenberg₂ ψ V W) (ratL V W) θ (fun τ => cplxT V W (sV τ) (sW τ))
    (latT V W LV LW fun _ => True) f

end Vac

section Split

variable {m n : ℕ}

def IsSBHalf (e : AE D) (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ) : Prop :=
  (∀ t, Φ t ≠ 0 → IsHalf e t) ∧ ∃ k : ℕ, 0 < k ∧
    (∀ u ∈ Λ, IsHalf e u → ∀ t, Φ (t + k • u) = Φ t) ∧ ∀ t, Φ t ≠ 0 → k • t ∈ Λ

open Classical in

def halfInd (e : AE D) (Λ : AddSubgroup (Mx D m n)) (t : Mx D m n) : ℂ :=
  if t ∈ Λ ∧ IsHalf e t then 1 else 0

structure IsPlaceModel (ψ : AddChar (AF D.host.F) ℂ) (B : Mx D m n → Mx D m n → AF D.host.F)
    (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (e : AE D) (Λ : AddSubgroup (Mx D m n)) (c : ℂ)
    (f₀ : Mx D m n → ℂ) (T : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) : Prop where
  trans : ∀ Φ, IsSBHalf e Λ Φ → ∀ x, IsHalf e x → T (fun t => Φ (t + x)) = hs x (T Φ)
  modul : ∀ Φ, IsSBHalf e Λ Φ → ∀ y, IsHalf (cA D e) y → T (fun t => ψ (B t y) * Φ t) = hs y (T Φ)
  vac : T (c • halfInd e Λ) = f₀

def IsThetaAt (ψ : AddChar (AF D.host.F) ℂ) (B : Mx D m n → Mx D m n → AF D.host.F)
    (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (e : AE D) (Λ : AddSubgroup (Mx D m n)) (c : ℂ)
    (f₀ Φ f : Mx D m n → ℂ) : Prop :=
  AllSome (IsPlaceModel ψ B hs e Λ c f₀) fun T => f = T Φ

def volRel {X : Type} [AddCommGroup X] (A B : AddSubgroup X) : ℝ :=
  (Nat.card (A ⧸ (A ⊓ B).addSubgroupOf A) : ℝ) / (Nat.card (B ⧸ (A ⊓ B).addSubgroupOf B) : ℝ)

end Split

section Local

open Classical in

def localNewformFunction (v : HeightOneSpectrum (𝓞 D.host.F)) {r t : ℕ}
    (P : Subgroup (GL (Fin r) (v.adicCompletionIntegers D.host.F))) (lam : P →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ)
    (x : Matrix (Fin r ⊕ Fin t) (Fin r) (Fv D.host.F v)) : ℂ :=
  if h : (∃ k : P, ((k : GL (Fin r) (v.adicCompletionIntegers D.host.F)) : Matrix (Fin r) (Fin r) _).map
        (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)) = x.submatrix Sum.inl id) ∧
      ∀ i j, x (Sum.inr i) j ∈ v.adicCompletionIntegers D.host.F ∧ Valued.v (x (Sum.inr i) j) < 1 then
    (lam h.1.choose : ℂ) *
      ((mu (Units.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)).toMonoidHom
        (Matrix.GeneralLinearGroup.det (h.1.choose : GL (Fin r) (v.adicCompletionIntegers D.host.F)))) : ℂˣ) : ℂ)⁻¹
  else 0

variable {m n : ℕ}

end Local

section Ext

variable {m n : ℕ}

def varF (τ : D.what₂.Tau) (i c : ℕ) : MvPolynomial (FVar D m n) ℂ :=
  if h : i < m ∧ c < n then MvPolynomial.X (τ, ⟨i, h.1⟩, ⟨c, h.2⟩) else 0

def minorPlus (τ : D.what₂.Tau) (k : ℕ) : MvPolynomial (FVar D m n) ℂ :=
  (Matrix.of fun α β : Fin k => (varF τ β α : MvPolynomial (FVar D m n) ℂ)).det

def minorMinus (τ : D.what₂.Tau) (p k : ℕ) : MvPolynomial (FVar D m n) ℂ :=
  (Matrix.of fun α β : Fin k => (varF τ (p + β) (n - k + α) : MvPolynomial (FVar D m n) ℂ)).det

def deltaAt (τ : D.what₂.Tau) (p : ℕ) (ap : ℕ → ℕ) (q : ℕ) (am : ℕ → ℕ) : MvPolynomial (FVar D m n) ℂ :=
  (∏ i ∈ Finset.range p, minorPlus τ (i + 1) ^ (ap i - if i + 1 < p then ap (i + 1) else 0)) *
    ∏ i ∈ Finset.range q, minorMinus τ p (i + 1) ^ (am i - if i + 1 < q then am (i + 1) else 0)

def delta (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) : MvPolynomial (FVar D m n) ℂ :=
  ∏ τ, deltaAt τ (p τ) (ap τ) (q τ) (am τ)

structure IsIoFock {GK GU TK Tau : Type} [NormedAddCommGroup TK] [InnerProductSpace ℂ TK] [NormedAddCommGroup Tau]
    [InnerProductSpace ℂ Tau] (πK : GK → TK →ₗ[ℂ] TK) (πT : GU → Tau →ₗ[ℂ] Tau)
    (πP : GK × GU → MvPolynomial (FVar D m n) ℂ →ₗ[ℂ] MvPolynomial (FVar D m n) ℂ)
    (hK : TK) (hT : Tau) (Δ : MvPolynomial (FVar D m n) ℂ)
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] MvPolynomial (FVar D m n) ℂ) : Prop where
  unitK : ∀ k x y, inner ℂ (πK k x) (πK k y) = inner ℂ x y
  unitT : ∀ u x y, inner ℂ (πT u x) (πT u y) = inner ℂ x y
  irrK : ∀ U : Submodule ℂ TK, (∀ k, ∀ x ∈ U, πK k x ∈ U) → U = ⊥ ∨ U = ⊤
  irrT : ∀ U : Submodule ℂ Tau, (∀ u, ∀ x ∈ U, πT u x ∈ U) → U = ⊥ ∨ U = ⊤
  normK : ‖hK‖ = 1
  normT : ‖hT‖ = 1
  delta_ne : Δ ≠ 0
  equiv : ∀ k u x y, io (πK k x) (πT u y) = πP (k, u) (io x y)
  extremal : io hK hT = Δ

structure IsIt {Pol Dj Djm : Type} [AddCommGroup Pol] [Module ℂ Pol] [AddCommGroup Dj] [Module ℂ Dj]
    [AddCommGroup Djm] [Module ℂ Djm] {KA gA KB gB : Type}
    (ωKa : KA → Pol →ₗ[ℂ] Pol) (πKa : KA → Djm →ₗ[ℂ] Djm) (ωga : gA → Pol →ₗ[ℂ] Pol) (πga : gA → Djm →ₗ[ℂ] Djm)
    (ωKb : KB → Pol →ₗ[ℂ] Pol) (πKb : KB → Dj →ₗ[ℂ] Dj) (ωgb : gB → Pol →ₗ[ℂ] Pol) (πgb : gB → Dj →ₗ[ℂ] Dj)
    (It : Pol →ₗ[ℂ] Dj →ₗ[ℂ] Djm) : Prop where
  ne : It ≠ 0

  nonemptyA : Nonempty gA
  nonemptyB : Nonempty gB
  eqK : ∀ k x y, It (ωKa k x) y = πKa k (It x y)
  eqg : ∀ X x y, It (ωga X x) y = πga X (It x y)
  invK : ∀ k x y, It (ωKb k x) (πKb k y) = It x y
  invg : ∀ X x y, It (ωgb X x) y + It x (πgb X y) = 0

end Ext

def IsSelfDualC (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) : Prop :=
  Submodule.IsLattice D.host.E Λ ∧ ∀ y : Fin S.rank → D.host.E, y ∈ Λ ↔
    ∀ x ∈ Λ, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * S.gram i j * y j

section Props

def LineAtExists (D : D7) : Prop :=
  ∀ θ : InfFam D, IsInfFam θ → ∀ (m n : ℕ) (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ),
    ∃ L : ℝ →+ Mx D m n, IsLineAt θ τ z L

def LineAtUnique (D : D7) : Prop :=
  ∀ θ : InfFam D, IsInfFam θ → ∀ (m n : ℕ) (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (L L' : ℝ →+ Mx D m n),
    IsLineAt θ τ z L → IsLineAt θ τ z L' → L = L'

def VacExistsO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), S.SigOK → T.SigOK →
      (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
      ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
        IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∃ f, IsVacO ψ θ S T sS sT ΛS ΛT f

def VacUniqueO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), S.SigOK → T.SigOK →
      (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
      ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
        IsSelfDualC S ΛS → IsSelfDualC T ΛT →
        ∀ f f', IsVacO ψ θ S T sS sT ΛS ΛT f → IsVacO ψ θ S T sS sT ΛS ΛT f' → ∃ c : ℂ, ‖c‖ = 1 ∧ f' = c • f

def PlaceModelExistsO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (ε : AF D.host.F), IsSplitIdem D e → IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (AE D) ε →
    ∀ (c : ℂ) (f₀ : WO S T → ℂ), c ≠ 0 → IsThetaFunO ψ S T f₀ →
      IsLatVac (heisO ψ S T) (latO S T (L0c D S) (L0c D T) fun w => w = v) f₀ →
      ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (L0c D S) (L0c D T) fun w => w = v) c f₀ Tm

def BridgeSmall (D : D7) : Prop :=
  ∀ S T : HSp D, S.rank ≤ T.rank →
    (∀ x y : WO S T, symplO S T x y = sympl S T (toTWsmall S T x) (toTWsmall S T y)) ∧
    ∀ g h (x : WO S T), toTWsmall S T (actO S T g h x) = actHom S T g h (toTWsmall S T x)

def BridgeLarge (D : D7) : Prop :=
  ∀ S T : HSp D, T.rank < S.rank →
    (∀ x y : WO S T, symplO S T x y = -sympl T S (toTWlarge S T x) (toTWlarge S T y)) ∧
    ∀ g h (x : WO S T), toTWlarge S T (actO S T g h x) = actHom T S h g (toTWlarge S T x)

end Props

end Formalism.IndefR.Datum

end
