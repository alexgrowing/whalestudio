import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain
  NumberField Matrix
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev FinPl (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.F)

abbrev Place (D : D7) : Type := FinPl D ⊕ D.what₂.Tau

def plTau (D : D7) (τ : D.what₂.Tau) : InfinitePlace D.host.F :=
  InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))

def idem (D : D7) : Place D → AE D
  | .inl v => algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1))
  | .inr τ => algebraMap (AF D.host.F) (AE D) (pairA D.host.F (GlobalTheory.AutFunCompare.sgW (plTau D τ) 1) 0)

def wAt {m n : ℕ} (p : Place D) (w : Mx D m n) : Mx D m n := fun i j => idem D p * w i j

def gAt (V : HSp D) : Place D → GA D V → GA D V
  | .inl v => fun g => GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)
  | .inr τ => fun g =>
      GlobalTheory.AdelicU.embArch D.sp.cm.sig V.gram (plTau D τ) (GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram (plTau D τ) g)

def ipO {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f₁ f₂ : Mx D m n → ℂ) : ℂ :=
  ∫ w in 𝓕, f₁ w * (starRingEnd ℂ) (f₂ w) ∂μ

section Tensor

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
  (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
  (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))

def IsBase (f₀ : WO S T → ℂ) : Prop :=
  (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) ∧ (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) ∧
    IsSelfDualC S ΛS ∧ IsSelfDualC T ΛT ∧ IsVacO ψ θ S T sS sT ΛS ΛT f₀

def IsLocal (p : Place D) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => Sum.inl u ≠ p) f ∧
    ∀ τ, Sum.inr τ ≠ p → IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f

def IsRestricted (f₀ : WO S T → ℂ) (x : Place D → WO S T → ℂ) : Prop :=
  (∀ p, IsLocal ψ θ S T sS sT ΛS ΛT p (x p)) ∧ {p | x p ≠ f₀}.Finite

def IsPure (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f₀ : WO S T → ℂ) (x : Place D → WO S T → ℂ) (f : WO S T → ℂ) : Prop :=
  IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x ∧ IsThetaFunO ψ S T f ∧ ∀ w : WO S T,
    (Function.mulSupport fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)).Finite ∧
    ipO μ 𝓕 f (heisO ψ S T w f₀) = ∏ᶠ p, ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)

end Tensor

section Split

abbrev SplitProj (D : D7) (v : FinPl D) : Type :=
  (Fv D.host.F v ⊗[D.host.F] D.host.E) →ₐ[Fv D.host.F v] Fv D.host.F v

variable {v : FinPl D} (φ : SplitProj D v)

def rdA : AE D →+* Fv D.host.F v := φ.toRingHom.comp (GlobalTheory.AdelicU.compFin D.host.F D.host.E v)

def rdE : EAf D →+* Fv D.host.F v :=
  φ.toRingHom.comp
    (((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom).comp
      (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)).toAlgHom.toRingHom)

def rdQ (x : D.host.E) : Fv D.host.F v := φ ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x)

def IsIdemOf (e : AE D) : Prop :=
  IsSplitIdem D e ∧ e + cA D e = idem D (.inl v) ∧ rdA φ e = 1

def IsProjAt (PP : Formalism.L2.DIV.Pl D.host.E) : Prop :=
  ∀ x : 𝓞 D.host.E, x ∈ PP.asIdeal ↔ Valued.v (rdQ φ (x : D.host.E)) < 1

def RedRel (PP : Formalism.L2.DIV.Pl D.host.E) (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP) : Prop :=
  ∃ x : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal x = b ∧ Valued.v (a - rdQ φ (x : D.host.E)) < 1

def LiftsChar (PP : Formalism.L2.DIV.Pl D.host.E) (mu : (Fv D.host.F v)ˣ →* ℂˣ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ (u : (Fv D.host.F v)ˣ) (k : (Formalism.L2.DIV.kP PP)ˣ), RedRel φ PP (u : Fv D.host.F v) (k : Formalism.L2.DIV.kP PP) → mu u = ξ k

def grpCo (V : HSp D) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) : GL (Fin V.rank) (Fv D.host.F v) :=
  B⁻¹ * Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom V g) * B

def frCo {n : ℕ} (β : GL (Fin n) (EAf D)) : GL (Fin n) (Fv D.host.F v) := Matrix.GeneralLinearGroup.map (rdE φ) β

variable (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v))

def mapCo (x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) :=
  HMul.hMul (HMul.hMul (BT⁻¹).val ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (rdA φ))) BS.val

def adjCo (x : WO S T) : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) :=
  HMul.hMul (HMul.hMul (BS⁻¹).val
    ((HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose)
      (T.gram.map (incA D))).map (rdA φ))) BT.val

open Classical in

def onHalf (e : AE D) (Φ : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) → ℂ) : WO S T → ℂ :=
  fun t => if IsHalf e t then Φ (mapCo φ S T BS BT t) else 0

open Classical in

def onHalfAdj (e : AE D) (Φ : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ) : WO S T → ℂ :=
  fun t => if IsHalf (cA D e) t then Φ (adjCo φ S T BS BT t) else 0

end Split

def linOm (v : FinPl D) {a b : ℕ} (g : GL (Fin a) (Fv D.host.F v)) (h : GL (Fin b) (Fv D.host.F v))
    (Φ : Matrix (Fin b) (Fin a) (Fv D.host.F v) → ℂ) : Matrix (Fin b) (Fin a) (Fv D.host.F v) → ℂ :=
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  GlobalTheory.SplitWeil.om (k := Fv D.host.F v) 1 g h Φ

open Classical in

def phiQ (v : FinPl D) {a b : ℕ} (r : ℕ) (de : (Fv D.host.F v)ˣ →* ℂˣ) (x : Matrix (Fin b) (Fin a) (Fv D.host.F v)) : ℂ :=
  if h : IsUnit (topL r x).det ∧ Valued.v (topL r x).det = 1 ∧ (∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F) ∧
      ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1 then
    ((de h.1.unit : ℂˣ) : ℂ)⁻¹
  else 0

def rowsTB {κ : Type} {n r t : ℕ} (h : r + t = n) (x : Matrix (Fin n) (Fin r) κ) : Matrix (Fin r ⊕ Fin t) (Fin r) κ :=
  x.submatrix (fun i => Fin.cast h (finSumFinEquiv i)) id

def princ (v : FinPl D) (r : ℕ) : Subgroup (GL (Fin r) (v.adicCompletionIntegers D.host.F)) :=
  (Matrix.GeneralLinearGroup.map (IsLocalRing.residue (v.adicCompletionIntegers D.host.F))).ker

def IsLocLevel {v : FinPl D} (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E) {a : ℕ}
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ)
    (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ) : Prop :=
  ∀ (k : GL (Fin a) (v.adicCompletionIntegers D.host.F)) (kb : GL (Fin a) (Formalism.L2.DIV.kP PP)),
    (∀ i j, RedRel φ PP ((k.val i j : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) (kb.val i j)) →
      (k ∈ J ↔ kb ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr kb ∈ H) ∧
      ∀ hk : k ∈ J, lam ⟨k, hk⟩ = Formalism.L2.DIV.ext1 H c (Formalism.L2.DIV.upperLeftBlock L.hr kb) *
        ∏ i ∈ Finset.range L.s, L.cg (i + 1) PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf L.r L.t) (i + 1) kb)

def UnramAt (χ : (AE D)ˣ →* Circle) (v : FinPl D) : Prop :=
  ∀ x : (AE D)ˣ, idem D (.inl v) * ((x : AE D) - 1) = (x : AE D) - 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def IsSplitPlace (D : D7) (v : FinPl D) : Prop := ∃ e, IsSplitIdem D e ∧ e + cA D e = idem D (.inl v)

section Fock

variable {m n : ℕ}

def IsKMat {k : ℕ} (p : ℕ) (κ : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  κ ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ ∀ i j, ¬ (i.val < p ↔ j.val < p) → κ i j = 0

def IsPMat {k : ℕ} (p : ℕ) (Y : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  Yᴴ = Y ∧ ∀ i j, (i.val < p ↔ j.val < p) → Y i j = 0

def detPos {k : ℕ} (p : ℕ) (κ : Matrix (Fin k) (Fin k) ℂ) : ℂ := (κ.toSquareBlockProp fun i => i.val < p).det

def detNeg {k : ℕ} (p : ℕ) (κ : Matrix (Fin k) (Fin k) ℂ) : ℂ := (κ.toSquareBlockProp fun i => ¬ i.val < p).det

open Classical in

def fockSub (τ : D.what₂.Tau) (pS pT : ℕ) (κS : Matrix (Fin n) (Fin n) ℂ) (κT : Matrix (Fin m) (Fin m) ℂ) :
    MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.aeval fun y : FVar D m n =>
    if y.1 = τ then
      ∑ i, ∑ j, MvPolynomial.C (if (y.2.1.val < pT ↔ y.2.2.val < pS) then κT i y.2.1 * κS⁻¹ y.2.2 j
        else (starRingEnd ℂ) (κT i y.2.1 * κS⁻¹ y.2.2 j)) * MvPolynomial.X (τ, i, j)
    else MvPolynomial.X y

def quadOp {ι : Type} (c : ℂ) (z z' : ι) (P : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  c • (MvPolynomial.X z * MvPolynomial.X z' * P) -
    (starRingEnd ℂ) c • MvPolynomial.pderiv z (MvPolynomial.pderiv z' P)

open Classical in

def fockP (τ : D.what₂.Tau) (pS pT : ℕ) (YS : Matrix (Fin n) (Fin n) ℂ) (YT : Matrix (Fin m) (Fin m) ℂ)
    (P : MvPolynomial (FVar D m n) ℂ) : MvPolynomial (FVar D m n) ℂ :=
  (∑ c : Fin n, ∑ i : Fin m, ∑ i' : Fin m,
    if (i.val < pT ↔ c.val < pS) ∧ ¬ (i'.val < pT ↔ c.val < pS) then quadOp (YT i i') (τ, i, c) (τ, i', c) P else 0) +
  ∑ i : Fin m, ∑ d : Fin n, ∑ c : Fin n,
    if (i.val < pT ↔ d.val < pS) ∧ ¬ (i.val < pT ↔ c.val < pS) then quadOp (-(YS c d)) (τ, i, d) (τ, i, c) P else 0

def fockIp {ι : Type} (P Q : MvPolynomial ι ℂ) : ℂ :=
  ∑ k ∈ P.support, P.coeff k * (starRingEnd ℂ) (Q.coeff k) * ((k.prod fun _ e => e.factorial : ℕ) : ℂ)

end Fock

abbrev OmT (S T : HSp D) : Type := GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)

def Unitary (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T),
    IsWeilDatumO ψ S T χS χT om →
    AllSome (fun q : Measure (WO S T) × Set (WO S T) => IsCovolOne (ratL T S) q.1 q.2) fun q =>
      ∀ f₁ f₂, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ →
        (∀ c : ℂ, IsThetaFunO ψ S T (c • f₁ + f₂)) ∧
        IntegrableOn (fun w => f₁ w * (starRingEnd ℂ) (f₂ w)) q.2 q.1 ∧
        (nrm2 q.1 q.2 f₁ = 0 → f₁ = 0) ∧
        (∀ μ' 𝓕', IsCovolOne (ratL T S) μ' 𝓕' → ipO μ' 𝓕' f₁ f₂ = ipO q.1 q.2 f₁ f₂) ∧
        (∀ w, IsThetaFunO ψ S T (heisO ψ S T w f₁) ∧
          ipO q.1 q.2 (heisO ψ S T w f₁) (heisO ψ S T w f₂) = ipO q.1 q.2 f₁ f₂) ∧
        (∀ p, IsThetaFunO ψ S T (om p f₁) ∧ ipO q.1 q.2 (om p f₁) (om p f₂) = ipO q.1 q.2 f₁ f₂) ∧
        Continuous fun p => nrm2 q.1 q.2 (om p f₁ - f₂)

def RestrictedTensor (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T)
    sS sT ΛS ΛT (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 →
    (∀ p f, IsLocal ψ θ S T sS sT ΛS ΛT p f →
      (∀ w, IsLocal ψ θ S T sS sT ΛS ΛT p (heisO ψ S T (wAt p w) f)) ∧
      ∀ g h, IsLocal ψ θ S T sS sT ΛS ΛT p (om (gAt S p g, gAt T p h) f)) ∧
    (∀ x, IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x → ∃! f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f) ∧
    (∀ f, IsThetaFunO ψ S T f → ∀ ε : ℝ, 0 < ε →
      ∃ f' ∈ Submodule.span ℂ {u | ∃ x, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x u}, nrm2 μ 𝓕 (f - f') < ε) ∧
    ∀ x f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f →
      (∀ w, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => heisO ψ S T (wAt p w) (x p)) (heisO ψ S T w f)) ∧
      ∀ g h, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f)

def CoeffProduct (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T)
    sS sT ΛS ΛT (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 →
    ∀ x₁ f₁ x₂ f₂, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ → ∀ g h,
      (Function.mulSupport fun p => ipO μ 𝓕 (om (gAt S p g, gAt T p h) (x₁ p)) (x₂ p)).Finite ∧
      ipO μ 𝓕 (om (g, h) f₁) f₂ = ∏ᶠ p, ipO μ 𝓕 (om (gAt S p g, gAt T p h) (x₁ p)) (x₂ p)

def SplitModel (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T)
    sS sT ΛS ΛT (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 →
    ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e →
    ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)),
    AllSome (IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀) fun Tm =>
      Set.BijOn (fun Φ => Tm (onHalf φ S T BS BT e Φ)) (GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)))
        {f | IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f} ∧
      (∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure →
        let vol := GlobalTheory.SplitWeil.volM ν (Fin T.rank) (Fin S.rank)
          (mapCo φ S T BS BT '' {t | t ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e t})
        vol ≠ 0 ∧ vol ≠ ⊤ ∧ ∀ Φ₁ ∈ GlobalTheory.SplitWeil.SB _, ∀ Φ₂ ∈ GlobalTheory.SplitWeil.SB _,
          (vol.toReal : ℂ) * ipO μ 𝓕 (Tm (onHalf φ S T BS BT e Φ₁)) (Tm (onHalf φ S T BS BT e Φ₂)) =
            GlobalTheory.SplitWeil.ip ν Φ₁ Φ₂) ∧
      ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ Φ ∈ GlobalTheory.SplitWeil.SB _,
        om (g, h) (Tm (onHalf φ S T BS BT e Φ)) = ((splitFacO χS χT x y : Circle) : ℂ) •
          Tm (onHalf φ S T BS BT e (linOm v (grpCo φ S BS g) (grpCo φ T BT h) Φ))

def SplitModelAdj (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T)
    sS sT ΛS ΛT (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 →
    ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e →
    ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)),
    AllSome (IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀) fun Tm =>
      Set.BijOn (fun Φ => Tm (onHalfAdj φ S T BS BT e Φ))
        (GlobalTheory.SplitWeil.SB (Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)))
        {f | IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f} ∧
      (∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure →
        let vol := GlobalTheory.SplitWeil.volM ν (Fin S.rank) (Fin T.rank)
          (adjCo φ S T BS BT '' {t | t ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf (cA D e) t})
        vol ≠ 0 ∧ vol ≠ ⊤ ∧ ∀ Φ₁ ∈ GlobalTheory.SplitWeil.SB _, ∀ Φ₂ ∈ GlobalTheory.SplitWeil.SB _,
          (vol.toReal : ℂ) * ipO μ 𝓕 (Tm (onHalfAdj φ S T BS BT e Φ₁)) (Tm (onHalfAdj φ S T BS BT e Φ₂)) =
            GlobalTheory.SplitWeil.ip ν Φ₁ Φ₂) ∧
      ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ Φ ∈ GlobalTheory.SplitWeil.SB _,
        om (g, h) (Tm (onHalfAdj φ S T BS BT e Φ)) = ((splitFacO χS χT x y : Circle) : ℂ) •
          Tm (onHalfAdj φ S T BS BT e (linOm v (grpCo φ T BT h) (grpCo φ S BS g) Φ))

def SplitLattice (D : D7) : Prop :=
  ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e →
      (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ (∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ a') ≤ Valued.v (rdQ φ a)) ∧
        mapCo φ S T (frCo φ βS) (frCo φ βT) '' {t | t ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e t} =
          {y | ∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ a)}) ∧
      ∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧
        (∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ (star a')) ≤ Valued.v (rdQ φ (star a))) ∧
        adjCo φ S T (frCo φ βS) (frCo φ βT) '' {t | t ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf (cA D e) t} =
          {y | ∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ (star a))}

def VacuumFixedOn (D : D7) (C : FinPl D → Prop) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ v, C v → UnramAt χS v → UnramAt χT v →
    ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f →
    ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig S.gram ΛS v, ∀ k' ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig T.gram ΛT v,
      om (GlobalTheory.AdelicU.emb D.sp.cm.sig S.gram v k, GlobalTheory.AdelicU.emb D.sp.cm.sig T.gram v k') f = f

def InertVacuumFixed (D : D7) : Prop := VacuumFixedOn D fun v => ¬ IsSplitPlace D v

def SplitVacuumFixed (D : D7) : Prop := VacuumFixedOn D fun v => IsSplitPlace D v

def FockModel (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T),
    IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ τ : D.what₂.Tau, ∃ mS mT : ℤ,
    ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
      (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) →
      (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) →
      (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) →
      ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∀ P,
        IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) ∧
        (∀ μ 𝓕, IsCovolOne (ratL T S) μ 𝓕 → ∀ Q,
          ipO μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f P) (pureTensorO ψ θ S T sS sT BS BT f Q) =
            fockIp P Q * (nrm2 μ 𝓕 f : ℂ)) ∧
        (∀ κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT →
          ∀ g h, IsAtTau θ S τ (BS τ * κS * (BS τ)⁻¹) g → IsAtTau θ T τ (BT τ * κT * (BT τ)⁻¹) h →
            om (g, h) (pureTensorO ψ θ S T sS sT BS BT f P) =
              (detPos (pS τ) κS ^ (mS + (T.rank - pT τ : ℕ)) * detNeg (pS τ) κS ^ (mS + pT τ) *
                (detPos (pT τ) κT ^ (mT + pS τ) * detNeg (pT τ) κT ^ (mT + (S.rank - pS τ : ℕ)))) •
              pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P)) ∧
        ∀ YS YT, IsPMat (pS τ) YS → IsPMat (pT τ) YT → ∀ w,
          HasDerivAt (fun t : ℝ => om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t)
              (pureTensorO ψ θ S T sS sT BS BT f P) w)
            (pureTensorO ψ θ S T sS sT BS BT f (fockP τ (pS τ) (pT τ) YS YT P) w) 0

def FockPure (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT ΛS ΛT (f₀ : WO S T → ℂ) (μ : Measure (WO S T))
    (𝓕 : Set (WO S T)) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ),
    IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 →
    (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) →
    ∀ x f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → (∀ τ, x (.inr τ) = f₀) →
    ∀ P : D.what₂.Tau → MvPolynomial (FVar D T.rank S.rank) ℂ,
      (∀ τ, P τ ∈ MvPolynomial.supported ℂ {y : FVar D T.rank S.rank | y.1 = τ}) →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
        (Sum.elim (fun v => x (.inl v)) fun τ => pureTensorO ψ θ S T sS sT BS BT f₀ (P τ))
        (pureTensorO ψ θ S T sS sT BS BT f (∏ τ, P τ))

def IsBaseOff {S T : HSp D} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (f₀ : WO S T → ℂ) (x : Place D → WO S T → ℂ) : Prop :=
  (∀ τ, x (.inr τ) = f₀) ∧ ∀ v : FinPl D, (∀ PP ∈ P, PP.asIdeal.under (𝓞 D.host.F) ≠ v.asIdeal) → x (.inl v) = f₀

def ThetaVecLocal (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ)
    (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (t : ℕ) (ht : T.rank + t = S.rank),
    IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 →
    Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint Pg Q →
    IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f →
    AllSome (fun x : Place D → WO S T → ℂ =>
      (open Classical in IsBaseOff (Pg ∪ Q) f₀ x) ∧
      ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ mu : (Fv D.host.F v)ˣ →* ℂˣ,
        (∀ PP ∈ Pg, IsProjAt φ PP → (∀ u : (Fv D.host.F v)ˣ, Valued.v ((u : Fv D.host.F v) - 1) < 1 → mu u = 1) →
          IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀
            (onHalfAdj φ S T (frCo φ βS) (frCo φ βT) e fun u => localNewformFunction v (princ v T.rank) 1 mu (rowsTB ht u)) (x (.inl v))) ∧
        ∀ PP ∈ Q, IsProjAt φ PP → LiftsChar φ PP mu (ξ PP) →
          IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀
            (onHalfAdj φ S T (frCo φ βS) (frCo φ βT) e fun u => localNewformFunction v ⊤ 1 mu (rowsTB ht u)) (x (.inl v)))
      fun x => IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f

def StepVecLocal (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (χ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ)
    (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (t : ℕ) (ht : S.rank + t = T.rank)
    (Hl : ∀ PP : ↥LS.Pg, Subgroup (GL (Fin LS.r) (Formalism.L2.DIV.kP PP.1))) (cl : ∀ PP : ↥LS.Pg, Hl PP →* ℂˣ),
    LS.P = Formalism.L2.DIV.LevelP.ofLocal Hl cl →
    IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 →
    Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint LS.Pg Q →
    IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χ Q ξ f₀ f →
    AllSome (fun x : Place D → WO S T → ℂ =>
      (open Classical in IsBaseOff (LS.Pg ∪ Q) f₀ x) ∧
      ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ mu : (Fv D.host.F v)ˣ →* ℂˣ,
        (∀ PP : ↥LS.Pg, IsProjAt φ PP.1 → LiftsChar φ PP.1 mu (χ PP.1) →
          ∀ (J : Subgroup (GL (Fin S.rank) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ),
            IsLocLevel φ PP.1 LS (Hl PP) (cl PP) J lam →
            IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀
              (onHalf φ S T (frCo φ βS) (frCo φ βT) e fun y => localNewformFunction v J lam mu (rowsTB ht y)) (x (.inl v))) ∧
        ∀ PP ∈ Q, IsProjAt φ PP → LiftsChar φ PP mu (ξ PP)⁻¹ →
          IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀
            (onHalf φ S T (frCo φ βS) (frCo φ βT) e (phiQ v LS.r mu)) (x (.inl v)))
      fun x => IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f

def PlaceModels (D : D7) : Prop :=
  Unitary D ∧ RestrictedTensor D ∧ CoeffProduct D ∧ SplitModel D ∧ SplitModelAdj D ∧ SplitLattice D ∧
    InertVacuumFixed D ∧ SplitVacuumFixed D ∧ FockModel D ∧ FockPure D ∧ ThetaVecLocal D ∧ StepVecLocal D

example (V : HSp D) (v : FinPl D) (g : GA D V) : gAt V (.inl v) (gAt V (.inl v) g) = gAt V (.inl v) g := by
  simp [gAt]

example : fockIp (MvPolynomial.monomial (Finsupp.single () 2) (1 : ℂ)) (MvPolynomial.monomial (Finsupp.single () 2) 1) = 2 := by
  classical
  simp [fockIp, MvPolynomial.support_monomial, Finsupp.prod_single_index]

end GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

end
