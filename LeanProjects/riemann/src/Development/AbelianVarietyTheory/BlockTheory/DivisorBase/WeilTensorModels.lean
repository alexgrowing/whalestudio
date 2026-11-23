import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

abbrev AE : Type := AF F ⊗[F] E

variable (F) in

abbrev Pl : Type := HeightOneSpectrum (𝓞 F)

scoped instance lcAdele : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F

scoped instance invTwo : Invertible (2 : AF F) :=
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  (Invertible.map (algebraMap F (AF F)) (2 : F)).copy 2 (map_ofNat _ 2).symm

scoped instance modTop : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locField (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

local instance measFv (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFv (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

def cA (σ : E →ₐ[F] E) : AE F E →ₐ[AF F] AE F E := Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ

variable (F) in

def incM {m n : Type} (J : Matrix m n E) : Matrix m n (AE F E) := J.map (inclR (F := F) (AF F))

abbrev UA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Type := UG (cA σ) (incM F J)

scoped instance measUA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : MeasurableSpace (UA σ J) := borel _

def mat {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : Matrix (Fin n) (Fin n) (AE F E) := g.1.1

def ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (UA σ J) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf _

def ht {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : ℝ≥0 := heightGL F g.1

def qht {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : ℝ≥0 := ⨅ γ : ratU σ J, ht (γ.1 * g)

variable (F) in

def evI (a : AF F) : mixedEmbedding.mixedSpace F := InfiniteAdeleRing.ringEquiv_mixedSpace F a.1

variable (F) in

def realAd (t : ℝ) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t))

def At {R M : Type} [Zero R] [Zero M] [SMul (AF F) M] (ev : AF F → R) (z : M) : Prop := ∀ u, ev u = 0 → u • z = 0

def tens {R κ : Type} (ev : AF F → R) (φ : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  fun x => φ (fun i => ev (x i)) * r x

def Rest {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R) (φ : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) : Prop :=
  (∀ x z, At ev z → r (x + z) = r x) ∧ tens ev φ r ∈ schA F κ

def Acts {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (φ φ₁ : (κ → R) → ℂ) : Prop := ∀ r, Rest ev φ r → T (tens ev φ r) = tens ev φ₁ r

def ActsD {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R) (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (φ φ₁ : (κ → R) → ℂ) : Prop :=
  ∀ r, Rest ev φ r → ∀ x, HasDerivAt (fun t => T t (tens ev φ r) x) (tens ev φ₁ r x) 0

open scoped Classical in
variable (F) in

abbrev SInf (κ : Type) [Fintype κ] : Type := SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ

def pure {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : (κ → AF F) → ℂ :=
  fun x => f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)

def piW {v : Pl F} (τ : E →ₐ[F] Fv F v) : AE F E →+* Fv F v :=
  (splitProj τ : Fv F v ⊗[F] E →+* Fv F v).comp (compFin F E v)

def piInf {w : InfinitePlace F} (τ : EmbOver E w) : AE F E →+* ℂ := (infEmb τ).comp (compInf F E w)

def IsStd (ψ : AddChar (AF F) ℂ) : Prop :=
  Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : AF F, At (evI F) a →
    ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) : ℝ))

def psiLoc (ψ : AddChar (AF F) ℂ) (v : Pl F) (x : Fv F v) : ℂ := ψ (LinearMap.inr F (Ainf F) (Af F) (singleFin v x))

def PsiUnr (ψ : AddChar (AF F) ℂ) (v : Pl F) : Prop :=
  ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F

variable (F E) in

abbrev Chr : Type := (AE F E)ˣ →* Circle

def chrW (χ : Chr F E) {v : Pl F} (τ : E →ₐ[F] Fv F v) : (Fv F v)ˣ →* ℂˣ :=
  (locChar χ (splitPrime τ)).comp (Units.map (complMap (splitPrime_under τ)).toMonoidHom)

def HasExp (τ : ∀ w : InfinitePlace F, EmbOver E w) (χ : Chr F E) (m : InfinitePlace F → ℤ) : Prop :=
  ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → (χ z : ℂ) = ∏ w, (piInf (τ w) z / ‖piInf (τ w) z‖) ^ m w

def idealVal (χ : Chr F E) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) : ℂˣ := ∏ᶠ w, val χ w ^ FractionalIdeal.count E w 𝔞

def unifAt (v : Pl F) : (Fv F v)ˣ := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose

def condExp {v : Pl F} (ν : (Fv F v)ˣ →* ℂˣ) : ℕ := sInf {c | GlobalTheory.SplitFlip.CondLE (unifAt v) c ν}

open Classical in

def gauss (ψ : AddChar (AF F) ℂ) {v : Pl F} (ν : (Fv F v)ˣ →* ℂˣ) : ℂ :=
  ∑ y : (GlobalTheory.SplitFlip.Res (Fv F v) (condExp ν))ˣ,
    if h : ((Quotient.out y.1 : (ValuativeRel.valuation (Fv F v)).integer) : Fv F v) = 0 then 0 else
      (((ν (Units.mk0 _ h))⁻¹ : ℂˣ) : ℂ) *
        psiLoc ψ v (((Quotient.out y.1 : (ValuativeRel.valuation (Fv F v)).integer) : Fv F v) / unifAt v ^ condExp ν)

def eps (ψ : AddChar (AF F) ℂ) {v : Pl F} (ν : (Fv F v)ˣ →* ℂˣ) (s : ℤ) : ℂ :=
  (Ideal.absNorm v.asIdeal : ℂ) ^ (-(condExp ν : ℤ) * s) * gauss ψ ν * (ν (unifAt v) : ℂ) ^ condExp ν

variable (E) in

def SplitsFully (v : Pl F) : Prop := ((v.asIdeal.under ℤ).primesOver (𝓞 E)).ncard = Module.finrank ℚ E

variable (F E) in

structure Base where

  ψ : AddChar (AF F) ℂ

  emb : ∀ w : InfinitePlace F, EmbOver E w

  mα : InfinitePlace F → ℤ

  mβ : InfinitePlace F → ℤ

  P : Finset (Pl F)

  τ : ∀ v : P, E →ₐ[F] Fv F v

  v₁ : Pl F

  τ₁ : E →ₐ[F] Fv F v₁

variable (F E) in

structure Spc (n : ℕ) where

  J : Matrix (Fin n) (Fin n) E

  L : Submodule (𝓞 E) (Fin n → E)

  θ : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ

  bas : ∀ v : Pl F, GL (Fin n) (Fv F v)

def form (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E := x ⬝ᵥ J *ᵥ fun i => σ (y i)

def HasSig {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ) : Prop :=
  r + s = n ∧ ∃ A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ, Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)

def IsCartan {n : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  θ * θ = 1 ∧ θᵀ * M * θ.map star = M ∧ ∀ x : Fin n → ℂ, x ≠ 0 → 0 < ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x).re

variable {σ : E →ₐ[F] E}

variable (σ) in

structure Spc.IsHerm (B : Base F E) {n : ℕ} (X : Spc F E n) (r s : ℕ) : Prop where
  herm : ∀ i j, σ (X.J j i) = X.J i j
  sig : ∀ w, HasSig (X.J.map (B.emb w).1) r s
  lat : X.L.IsLattice E
  dual : ∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, IsIntegral ℤ (form σ X.J y x)
  cartan : ∀ w, IsCartan (X.J.map (B.emb w).1) (X.θ w)
  bas : ∀ v : B.P, IsSplitBasis (B.τ v) X.L (X.bas v)

variable (σ) in

structure Spc.IsSkew (B : Base F E) {n : ℕ} (X : Spc F E n) (r s : ℕ) : Prop where
  skew : ∀ i j, σ (X.J j i) = -X.J i j
  sig : ∀ w, HasSig (Complex.I • X.J.map (B.emb w).1) r s
  lat : X.L.IsLattice E
  dual : ∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ X.J y x))
  cartan : ∀ w, IsCartan (Complex.I • X.J.map (B.emb w).1) (X.θ w)
  bas : ∀ v : B.P, IsSplitBasis (B.τ v) X.L (X.bas v)

variable (σ) in

structure Model {n d : ℕ} (X : Spc F E n) (W : Spc F E d) where

  co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)

  vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ

  μ : Measure (UA σ X.J)

  dom : Set (UA σ X.J)

variable (σ) in

abbrev Rep {n d : ℕ} (X : Spc F E n) (W : Spc F E d) : Type :=
  UA σ X.J × UA σ W.J →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)

section Pair

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

variable (X W) in

def latAtV (v : Pl F) : AddSubgroup (Matrix (Fin n) (Fin d) (AE F E)) :=
  AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
    ∃ x ∈ X.L, ∃ y ∈ W.L, z = a • incM F (Matrix.vecMulVec x y)}

namespace Model

variable (M : Model σ X W) (ψ : AddChar (AF F) ℂ)

def IsVac (v : Pl F) (φ : (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  φ ∈ SB _ ∧ φ ≠ 0 ∧ ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 ∧ ∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho ψ γ) φ
    (ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • φ)

structure IsGood : Prop where
  rat : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
    M.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))
  vac : ∀ v, M.IsVac ψ v (M.vac v)
  std : ∀ᶠ v in cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  haar : M.μ.IsHaarMeasure
  dom : IsFundamentalDomain (ratU σ X.J) M.dom M.μ

def heisLine (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ) := M.co.rho ψ (realAd F t • u)

variable (τ : ∀ w : InfinitePlace F, EmbOver E w)

def IsGauss (f₀ : SInf F (Fin n × Fin d)) : Prop :=
  ∃ ε : InfinitePlace F → ℤˣ, ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
    (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
    ∀ f f' : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f₀ f → ActsD (evI F) (M.heisLine ψ u') f₀ f' →
      f' = Complex.I • f

def Pol : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  sInf {N | (∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ N) ∧ ∀ u, At (evI F) u → ∀ f ∈ N, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ N}

structure IsLin {v : Pl F} (π₁ π₀ : AE F E →+* Fv F v)
    (co : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (Fv F v))
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) : Prop where
  bij : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _)
  trans : ∀ u, At (evFin F v) u → u.map π₀ = 0 → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ →
    ∀ Y, ι φ₁ Y = ι φ (Y + co u)
  mult : ∀ u, At (evFin F v) u → u.map π₁ = 0 → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ →
    ∀ x, At (evFin F v) x → x.map π₀ = 0 →
      ι φ₁ (co x) = ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) * ι φ (co x)

def IsLinW {v : Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) : Prop :=
  M.IsLin ψ (piW t) (piW (t.comp σ)) (fun u => (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ) ι

def IsLinBar {v : Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) : Prop :=
  M.IsLin ψ (piW (t.comp σ)) (piW t) (fun u => -(b.1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ * c.1)) ι

def SoLoc {v : Pl F} (t : E →ₐ[F] Fv F v) : Set ((Fin n × Fin d → Fv F v) → ℂ) :=
  {φ | φ ∈ SB _ ∧ ∃ ι, M.IsLinBar ψ t 1 1 ι ∧ ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), Y.rank ≠ n → ι φ Y = 0}

def So {v₁ : Pl F} (t : E →ₐ[F] Fv F v₁) : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f φ, (∀ v, φ v ∈ SB _) ∧ (∀ᶠ v in cofinite, φ v = M.vac v) ∧ φ v₁ ∈ M.SoLoc ψ t ∧ Φ = pure f φ}

def IsWeil (χX χW : Chr F E) (om : Rep σ X W) : Prop :=
  IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om

end Model

def theta (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ) (g : UA σ X.J) (h : UA σ W.J) : ℂ := thetaSum F (om (g, h) Φ)

def Model.I (M : Model σ X W) (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ) (h : UA σ W.J) : ℂ :=
  ∫ g in M.dom, theta om Φ g h ∂M.μ

def Model.Conv (M : Model σ X W) (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ) : Prop :=
  ∀ h, IntegrableOn (fun g => theta om Φ g h) M.dom M.μ

variable (σ X) in

def UAt {R : Type} [Zero R] (ev : AF F → R) : Set (UA σ X.J) := {g | At ev (mat g - 1)}

variable (σ X) in

def KInf (τ : ∀ w : InfinitePlace F, EmbOver E w) : Set (UA σ X.J) :=
  {k | k ∈ UAt σ X (evI F) ∧ ∀ w, Commute ((mat k).map (piInf (τ w))) (X.θ w)}

variable (σ X) in

def Lines : Set (Multiplicative ℝ →* UA σ X.J) := {γ | Continuous γ ∧ ∀ t, γ t ∈ UAt σ X (evI F)}

def augAt (om : Rep σ X W) (v : Pl F) : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ) :=
  Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), ∃ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (g, 1)) φ φ₁ ∧ z = φ₁ - φ}

end Pair

variable (σ) in

structure Geo (a a' : ℕ) where

  p : ℕ

  q : ℕ

  V : Spc F E a

  V' : Spc F E a'

  W : Spc F E (a + a')

  M : Model σ V W

  M' : Model σ V' W

variable (F E) in

structure Chars where

  α : Chr F E

  β : Chr F E

  S₀ : Finset (Pl F)

  Q : Finset (Pl F)

def Chars.ν (X : Chars F E) : Chr F E := X.α / X.β

open Classical in

def Chars.T (X : Chars F E) : Finset (Pl F) := X.S₀ ∪ X.Q

variable (σ) in

structure Base.IsGood (B : Base F E) : Prop where
  cm : IsCMExt F E σ
  galois : IsGalois ℚ E
  unram : Algebra.Unramified (𝓞 F) (𝓞 E)
  std : IsStd B.ψ
  inert : ∀ v w, Formalism.UG.IsInertAt F E v w → (2 : 𝓞 F) ∉ v.asIdeal ∧ 3 < Ideal.absNorm v.asIdeal ∧ PsiUnr B.ψ v
  psiP : ∀ v ∈ B.P, PsiUnr B.ψ v

variable {a a' : ℕ}

structure Geo.IsGood (B : Base F E) (G : Geo σ a a') : Prop where
  lt : a' < a
  even : Even (a + a')
  kappa : ∀ w, ((a + a' : ℕ) : ℤ) < B.mα w - B.mβ w
  eBig : 2 * (G.p + G.q) + 1 < (a - a') / 2
  aBig : 2 * (G.p + G.q) + 1 < a'
  hV : G.V.IsHerm σ B (a - G.p) G.p
  hV' : G.V'.IsHerm σ B G.q (a' - G.q)
  hW : G.W.IsSkew σ B (a + a' - (G.p + G.q)) (G.p + G.q)
  hM : G.M.IsGood B.ψ
  hM' : G.M'.IsGood B.ψ

def Chars.Good (X : Chars F E) (v : Pl F) : Prop := v ∉ X.T ∧ SplitsFully E v

structure Chars.IsGood (B : Base F E) (X : Chars F E) (a a' : ℕ) : Prop where
  heckeα : IsHecke F E X.α
  heckeβ : IsHecke F E X.β
  resα : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.α a'
  resβ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β a
  expα : HasExp B.emb X.α B.mα
  expβ : HasExp B.emb X.β B.mβ
  disj : Disjoint X.S₀ X.Q
  sub : X.T ⊆ B.P
  ram : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ X.T → ¬ UnrAt X.ν w
  unrα : UnrOff X.α (X.T : Set (Pl F))
  unrβ : UnrOff X.β (X.T : Set (Pl F))
  good : X.Good B.v₁

structure IsTriple (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) : Prop where
  base : B.IsGood σ
  geo : G.IsGood B
  chars : X.IsGood B a a'
  weil : G.M.IsWeil B.ψ X.β (X.β / X.α) om
  weil' : G.M'.IsWeil B.ψ X.α (X.α / X.β) om'

variable (F) in

structure RealMaps (a a' : ℕ) : Type 1 where

  Pi : Type
  [grp : AddCommGroup Pi]
  [mod : Module ℂ Pi]

  p : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] Pi

  p' : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] Pi

variable (F) in

structure FinMaps (a a' : ℕ) : Type 1 where

  Pi : Pl F → Type
  [grp : ∀ v, AddCommGroup (Pi v)]
  [mod : ∀ v, Module ℂ (Pi v)]

  p : ∀ v, ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] Pi v

  p' : ∀ v, ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] Pi v

attribute [instance] RealMaps.grp RealMaps.mod FinMaps.grp FinMaps.mod

section Maps

variable (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)

structure RealQuot {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P]
    [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Prop where
  onto : (M.Pol B.ψ B.emb).map p = ⊤
  lie : ∀ γ ∈ Lines σ Y, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → p f₁ = 0
  cpt : ∀ k ∈ KInf σ Y B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    Acts (evI F) (om (k, 1)) f f₁ → p f₁ = p f

structure IsRealMaps (R : RealMaps F a a') : Prop where
  quot : RealQuot B G.M om R.p
  quot' : RealQuot B G.M' om' R.p'
  lie : ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f' ∈ G.M'.Pol B.ψ B.emb, ∀ (f₁ : SInf F _) (f₁' : SInf F _),
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f' f₁' → R.p f = R.p' f' → R.p f₁ = R.p' f₁'
  cpt : ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f' ∈ G.M'.Pol B.ψ B.emb, ∀ (f₁ : SInf F _) (f₁' : SInf F _),
    Acts (evI F) (om (1, k)) f f₁ → Acts (evI F) (om' (1, k)) f' f₁' → R.p f = R.p' f' → R.p f₁ = R.p' f₁'
  nontriv : Nontrivial R.Pi
  irred : ∀ N : Submodule ℂ R.Pi,
    (∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F _,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → R.p f ∈ N → R.p f₁ ∈ N) →
    (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F _,
      Acts (evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N) → N = ⊥ ∨ N = ⊤

def IsZetaAt (R : FinMaps F a a') (v : B.P) : Prop :=
  ∃ ι ι', G.M.IsLinW B.ψ (B.τ v) (G.V.bas v) (G.W.bas v) ι ∧ G.M'.IsLinBar B.ψ (B.τ v) (G.V'.bas v) (G.W.bas v) ι' ∧
    ι (G.M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.1.adicCompletionIntegers F} 1 ∧
    ι' (G.M'.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.1.adicCompletionIntegers F} 1 ∧
    ∀ φ ∈ SB _, ∀ φ' ∈ SB _, R.p v φ = R.p' v φ' ↔
      GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO _ (Fin a))) (unifAt v.1) finSumFinEquiv
                   (chrW X.ν (B.τ v)) (chrW X.β (B.τ v)) (ι φ) =
        GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO _ (Fin a'))) finSumFinEquiv
          (chrW X.ν (B.τ v)) (chrW X.α (B.τ v)) (ι' φ')

structure IsFinMaps (R : FinMaps F a a') : Prop where
  onto : ∀ v, (SB _).map (R.p v) = ⊤
  onto' : ∀ v, (SB _).map (R.p' v) = ⊤
  inv : ∀ v, augAt om v ≤ LinearMap.ker (R.p v)
  inv' : ∀ v, augAt om' v ≤ LinearMap.ker (R.p' v)
  equiv : ∀ v, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
    Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
    R.p v φ = R.p' v φ' → R.p v φ₁ = R.p' v φ₁'
  nontriv : ∀ v, Nontrivial (R.Pi v)
  irred : ∀ v, ∀ N : Submodule ℂ (R.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
    Acts (evFin F v) (om (1, h)) φ φ₁ → R.p v φ ∈ N → R.p v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤
  sph : ∀ v ∉ X.T, R.p v (G.M.vac v) = R.p' v (G.M'.vac v) ∧ R.p v (G.M.vac v) ≠ 0
  zeta : ∀ v : B.P, v.1 ∈ X.T → IsZetaAt B G X R v

variable (R : RealMaps F a a') (Rf : FinMaps F a a')

def PolMatch (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) : Prop :=
  ∃ T : Finset (Pl F), X.T ⊆ T ∧ ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

def Match (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) : Prop :=
  Φ' ∈ G.M'.So B.ψ B.τ₁ ∧ ∃ (m m' : ℕ) (g : Fin m → (_ → Af F) → ℂ) (f : Fin m → SInf F _) (s : ℕ → Fin m → SInf F _)
    (g' : Fin m' → (_ → Af F) → ℂ) (f' : Fin m' → SInf F _) (s' : ℕ → Fin m' → SInf F _),
    (∀ i, g i ∈ SB _ ∧ Tendsto (s · i) atTop (𝓝 (f i))) ∧ (∀ j, g' j ∈ SB _ ∧ Tendsto (s' · j) atTop (𝓝 (f' j))) ∧
    Φ = ∑ i, pureA F (f i) (g i) ∧ Φ' = ∑ j, pureA F (f' j) (g' j) ∧
    ∀ k, ∑ j, pureA F (s' k j) (g' j) ∈ G.M'.So B.ψ B.τ₁ ∧
      PolMatch B G X R Rf (∑ i, pureA F (s k i) (g i)) (∑ j, pureA F (s' k j) (g' j))

def IsConst (c : ℂ) : Prop := ∀ Φ Φ', Match B G X R Rf Φ Φ' → ∀ h, G.M.I om Φ h = c * G.M'.I om' Φ' h

structure IsMatched : Prop where
  triple : IsTriple B G X om om'
  real : IsRealMaps B G om om' R
  fin : IsFinMaps B G X om om' Rf

def Decay : Prop :=
  (∀ Φ ∈ schA F _, G.M.Conv om Φ) ∧ ∀ Φ' ∈ G.M'.So B.ψ B.τ₁,
    (∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om' Φ' g h‖ * (qht g : ℝ) ^ N ≤ C * (ht h : ℝ) ^ k) ∧
    G.M'.Conv om' Φ' ∧ IsModerate ht (G.M'.I om' Φ')

def OneConst : Prop :=
  (∃ Φ' ∈ G.M'.So B.ψ B.τ₁, G.M'.I om' Φ' ≠ 0) ∧ (∃! c, IsConst B G X om om' R Rf c) ∧
    ∀ c, IsConst B G X om om' R Rf c → c ≠ 0

def Coinv : Prop :=
  (∀ v, X.Good v → (∀ φ ∈ SB _, Rf.p v φ = 0 ↔ φ ∈ augAt om v) ∧ (∀ φ ∈ SB _, Rf.p' v φ = 0 ↔ φ ∈ augAt om' v) ∧
    (∀ t : E →ₐ[F] Fv F v, ∀ ξ, ∃ φ ∈ G.M'.SoLoc B.ψ t, Rf.p' v φ = ξ) ∧
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, augAt om' v ≤ LinearMap.ker l →
      ∃ l₀ : Rf.Pi v →ₗ[ℂ] ℂ, ∀ φ ∈ SB _, l φ = l₀ (Rf.p' v φ)) ∧
  ∀ γ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, om' γ Φ' ∈ G.M'.So B.ψ B.τ₁

end Maps

variable (E) in

structure Plane (n n₁ : ℕ) where

  x : Fin n → E

  y : Fin n → E

  ι : Matrix (Fin n) (Fin n₁) E

  𝔟 : FractionalIdeal (𝓞 E)⁰ E

def skip (i₀ i₁ j : ℕ) : ℕ := if j < i₀ then j else if j + 1 < i₁ then j + 1 else j + 2

variable (σ) in

structure Plane.IsAdapted (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ : ℕ) :
    Prop where
  rank : n = n₁ + 2
  xx : form σ Y.J H.x H.x = 0
  yy : form σ Y.J H.y H.y = 0
  xy : form σ Y.J H.x H.y = 1
  orth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0
  gram : H.ιᵀ * Y.J * H.ι.map σ = Y₁.J
  low : ∀ u, u ∈ Y₁.L ↔ H.ι *ᵥ u ∈ Y.L
  split : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • H.x ∈ Y.L ∧ t • H.y ∈ Y.L ∧ u ∈ Y₁.L ∧
    z = s • H.x + H.ι *ᵥ u + t • H.y
  ideal : ∀ s : E, s ∈ H.𝔟 ↔ s • H.x ∈ Y.L
  cartan : ∀ w, Y.θ w * H.ι.map (B.emb w).1 = H.ι.map (B.emb w).1 * Y₁.θ w ∧
    ∃ c : ℂ, c ≠ 0 ∧ (fun i => (B.emb w).1 (H.y i)) = c • Y.θ w *ᵥ fun i => (B.emb w).1 (H.x i)
  bas : ∀ (v : B.P) (i : Fin n), (i.1 = i₀ → ∀ r, (Y.bas v).1 r i = B.τ v (H.x r)) ∧
    (i.1 = i₁ → ∀ r, (Y.bas v).1 r i = B.τ v (H.y r)) ∧
    ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, (Y.bas v).1 r i = (H.ι.map (B.τ v) * (Y₁.bas v).1) r j

open Classical in

def stepFac (B : Base F E) (X : Chars F E) (e₁ e₂ s : ℤˣ) (𝔟 𝔠 : FractionalIdeal (𝓞 E)⁰ E) (z : ℤ) : ℂ :=
  ((idealVal X.ν 𝔟 ^ (e₁ : ℤ) * idealVal X.ν 𝔠 ^ (e₂ : ℤ) : ℂˣ) : ℂ) *
    ∏ v : B.P with v.1 ∈ X.T, (chrW X.ν (B.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) *
      eps B.ψ (chrW X.ν (B.τ v)) z

variable (σ) in

def StepBeta (e₁ e₂ s : ℤˣ) : Prop :=
  ∀ (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)) (R : RealMaps F a (b + 2)) (R₁ : RealMaps F a b),
    G₁.V = G.V → G₁.p = G.p → G₁.q + 1 = G.q → H.IsAdapted σ B G.V' G₁.V' 0 (b + 1) →
    H'.IsAdapted σ B G.W G₁.W a (a + b + 1) →
    ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ c c₁, IsConst B G X om om' R Rf c → IsConst B G₁ X om₁ om₁' R₁ Rf₁ c₁ →
        ∃ u : ℂ, u * (C * stepFac B X e₁ e₂ s H.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ))) = 1 ∧
          c * charL X.ν (X.S₀ : Set (Pl F)) ((((a - (b + 2)) / 2 : ℕ) : ℂ) + 1) = u * c₁

variable (σ) in

def StepAlpha (e₁ e₂ s : ℤˣ) : Prop :=
  ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')) (R : RealMaps F (b + 2) a') (R₁ : RealMaps F b a'),
    G₁.V' = G.V' → G.q = 0 → G₁.q = 0 → G₁.p + 1 = G.p → H.IsAdapted σ B G.V G₁.V 0 (b + 1) →
    H'.IsAdapted σ B G.W G₁.W 0 (b + 1) →
    ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ c c₁, IsConst B G X om om' R Rf c → IsConst B G₁ X om₁ om₁' R₁ Rf₁ c₁ →
        c = C * stepFac B X e₁ e₂ s H.𝔟 H'.𝔟 (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) *
          charL X.ν (X.S₀ : Set (Pl F)) (((b + 2 - a') / 2 : ℕ) : ℂ) * c₁

def LocalMatching : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∃ R Rf, IsMatched B G X om om' R Rf

def ThetaIntegralsAgree : Prop :=
  (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → Decay B G om om' ∧
      ∀ R Rf, IsMatched B G X om om' R Rf → OneConst B G X om om' R Rf ∧ Coinv B G X om om' Rf) ∧
  (∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    StepBeta σ e₁ e₂ s) ∧
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    StepAlpha σ e₁ e₂ s

example : (List.range 4).map (skip 1 4) = [0, 2, 3, 5] := by decide

example : HasSig (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 0 ∧ IsCartan (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 := by
  refine ⟨⟨rfl, Matrix.of fun _ _ => 1, ?_⟩, by simp, by simp, fun x hx => ?_⟩
  · ext (i | i) (j | j)
    · simp [Matrix.mul_apply, Subsingleton.elim i j]
    all_goals first | exact i.elim0 | exact j.elim0
  · have : x 0 ≠ 0 := fun h => hx (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
    simpa [dotProduct, Complex.mul_conj, ← Complex.normSq_apply] using Complex.normSq_pos.2 this

end GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

end
