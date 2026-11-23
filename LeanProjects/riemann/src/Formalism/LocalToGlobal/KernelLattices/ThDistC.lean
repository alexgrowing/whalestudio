import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

section Jet

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

abbrev DVar (ι : Type) (a b : ℕ) : Type := ι × Fin b × Fin a

def frDet (K : Type) [Field K] {ι : Type} (a : ℕ) (τ : ι) : Pol K ι a :=
  (Matrix.of fun α s : Fin a => (X (τ, α, s) : Pol K ι a)).det

def subD (K : Type) [Field K] (ι : Type) (a b : ℕ) : Pol K ι a →ₐ[K] MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K :=
  aeval fun v => if h : v.2.2.1 < b then
    ∑ β : Fin b, X (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b))) * X (Sum.inr (v.1, β, v.2.1)) else 0

def jetLin (J : (DVar ι a b →₀ ℕ) → K) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K →ₗ[K] Pol K ι b :=
  (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).constr K fun m =>
    monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn))

def jetMap (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) : Pol K ι a →ₗ[K] Pol K ι b :=
  jetLin J ∘ₗ (subD K ι a b).toLinearMap ∘ₗ LinearMap.mulRight K (∏ τ, frDet K a τ ^ n τ)

def retrVV (K : Type) [Field K] {ι : Type} [Fintype ι] {b : ℕ} (lam' : ι → DomWeight b) : Pol K ι b →ₗ[K] DIV.VV K lam' :=
  Submodule.projectionOnto (DIV.VV K lam') _ (Classical.choose_spec (Submodule.exists_isCompl (DIV.VV K lam')))

def jetOp (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) :
    DIV.VV K lam →ₗ[K] DIV.VV K lam' :=
  retrVV K lam' ∘ₗ jetMap J n ∘ₗ (DIV.VV K lam).subtype

def JetInVV (K : Type) [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) : Prop :=
  ∀ (J : (DVar ι a b →₀ ℕ) → K), ∀ P ∈ DIV.VV K lam, jetMap J n P ∈ DIV.VV K lam'

end Jet

section Table

variable {ι : Type} [Fintype ι] {a b : ℕ}

abbrev VCx (ι : Type) (a b : ℕ) : Type := ι → Fin b → Fin a → ℂ

open Classical in

def coordX (k : DVar ι a b) : VCx ι a b := fun τ i j => if τ = k.1 ∧ i = k.2.1 ∧ j = k.2.2 then 1 else 0

def derivAt0 (G : VCx ι a b → ℂ) (m : DVar ι a b →₀ ℕ) : ℂ :=
  iteratedFDeriv ℂ (Multiset.card m.toMultiset) G 0
    (fun i => coordX (m.toMultiset.toList.get ⟨i, by simpa using i.2⟩))

def jetC (cD : ι → ℂ) (G : VCx ι a b → ℂ) (m : DVar ι a b →₀ ℕ) : ℂ :=
  (m.prod fun k n => cD k.1 ^ n) * derivAt0 G m

open Classical in

def desc {K : Type} [Field K] (σ : K →+* ℂ) (z : ℂ) : K := if h : ∃ k : K, σ k = z then h.choose else 0

end Table

structure Amb (X : Fields) where
  σ₀ : X.K →+* ℂ
  δ : ℂ
  d : ℕ
  sc : ℝ
  AA : Submodule (𝓞 X.E) X.E
  cD : X.Tau → ℂ
  e : ∀ a b : ℕ, Submodule (𝓞 X.E) (Sp X.E a) → Submodule (𝓞 X.E) (Sp X.E b) → VCx X.Tau a b → ℂ
  chiF : ∀ a b : ℕ, Submodule (𝓞 X.E) (Sp X.E a) → Submodule (𝓞 X.E) (Sp X.E b) → ℂ

section Ind

variable {X : Fields} (A : Amb X) {a b : ℕ}

variable (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

def Amb.IsLift (c : ℕ) (x s : HomE X.E a b) : Prop :=
  (∃ c' : ℕ, 0 < c' ∧ s ∈ halfAO S (perO A.AA N N') c') ∧ s - x ∈ mulLat c (homAt S N N')

def Amb.liftW (c : ℕ) (x : HomE X.E a b) : HomE X.E a b := Classical.epsilon (A.IsLift S N N' c x)

def Amb.thInd (c : ℕ) (x : HomE X.E a b) : VCx X.Tau a b → ℂ := fun z =>
  ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ)⁻¹ *
    xiInd (HV A.sc) (alV A.d A.sc) (volC A.AA S N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c)
      (repsOf (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c))
      (repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c))
      (A.e a b N N') (embH (X.embC A.σ₀) A.δ (A.liftW S N N' c x)) z

def Amb.IndTie (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), IsSdLat N → IsSdLat N' → 0 < c →
    x ∈ divLat c (homAt S N N') → ∀ z, A.thInd S N N' c x z =
      ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ)⁻¹ *
        xiIndC (X.embC A.σ₀) A.δ A.d A.sc A.AA S N N' c (A.e a b N N') x z

def Amb.jetK (c : ℕ) (x : HomE X.E a b) (m : DVar X.Tau a b →₀ ℕ) : X.K :=
  desc A.σ₀ ((A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) m)

end Ind

section Scal

variable {X : Fields} {n : ℕ}

def ordE {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (x : E) : ℤ := -WithZero.log (P.valuation E x)

def frameAt {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) : Sp E n ≃ₗ[E] Sp E n :=
  Classical.epsilon fun f : Sp E n ≃ₗ[E] Sp E n => ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P

def ordDet {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) : ℤ :=
  ordE P ((LinearEquiv.det (frameAt P N) : Eˣ) : E)

open Classical in

def muOff (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (N : Submodule (𝓞 X.E) (Sp X.E n)) : X.K :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 X.F),
    if ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal then 1 else ((mU (sel v) ^ ordDet (sel v) N : X.Kˣ) : X.K)

def muInvDet (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n SB) : X.K :=
  muOff sel SB mU N * ∏ P : SB, mI P ((LinearEquiv.det (fr P) : X.Eˣ) : X.E)

end Scal

section Dist

variable {X : Fields} (A : Amb X) {a b : ℕ}

def thDistC (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ) :
    ThDist X.E X.K a b SB (DIV.VV X.K lam) (DIV.VV X.K lam') :=
  fun N fr N' fr' c x =>
    open Classical in
    if c ∣ D ∧ x ∈ divLat D (homAt Sall N N') then
      (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹) • jetOp lam lam' (A.jetK Sall N N' c x) n
    else 0

end Dist

section XiVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

def IsUnifVal (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (k : Lˣ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), P.asIdeal.under (𝓞 F) = v.asIdeal →
  ∀ (y : (AfE F E)ˣ) (y₀ : RInt F E) (b : 𝓞 E), (y₀ : AfE F E) = (y : AfE F E) → b ∈ P.asIdeal → b ∉ P.asIdeal ^ 2 → y ∈ suppAt E v →
    y₀ - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E) →
    (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E)) → ξ y = k

open Classical in

def unifVal (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) : Lˣ := if h : ∃ k, IsUnifVal ξ P k then h.choose else 1

def IsQVal (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (k : Lˣ) : Prop := IsQValC ξ P k

def qVal (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) : Lˣ := qValC ξ P

def QValExists : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L] (ξ : Chr F E L)
    (P : HeightOneSpectrum (𝓞 E)), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) →
    ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∃ k, IsQVal ξ P k

def QValUnique : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L] (ξ : Chr F E L)
    (P : HeightOneSpectrum (𝓞 E)) (k k' : Lˣ), IsQVal ξ P k → IsQVal ξ P k' → k = k'

end XiVal

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def nuLast (u : Pr.Word) (i : ℕ) (τ : X.Tau) : ℕ := (W.nuW u (i + 1) τ).detShift.toNat

open Classical in

def mUof (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : X.Kˣ :=
  (if h : i < R.m then Ch.muVal ⟨i, h⟩ P else 1)⁻¹ * (unifVal (mu : Chr X.F X.E X.K) P)⁻¹

open Classical in

def muqT (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : X.Kˣ :=
  (if h : i < R.m then Ch.muVal ⟨i, h⟩ P else 1)⁻¹ * (qVal (mu : Chr X.F X.E X.K) P)⁻¹

def MuqTie : Prop :=
  ∀ i, i < R.m → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → cst.muq (i + 1) P = ((muqT Ch mu i P.1 : X.Kˣ) : X.K)

def MuqTieG (σ₀ : X.K →+* ℂ) (m0 : Fin R.m → Formalism.L2.Host.HChar X.E) : Prop :=
  ∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ qu : X.Eˣ, (qu : X.E) = ((Col.qOf P.1 : ℕ) : X.E) →
    σ₀ (cst.muq (i + 1) P) =
      ((((m0 ⟨i, h⟩).locK P.1 qu : ℂˣ) : ℂ))⁻¹ * σ₀ (((qVal (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K)

open Classical in

def muAtT (i : ℕ) (P : rowSG Pr sel mu) : X.E → X.K :=
  LocE.locChar (Col.qOf P.1) (if P.1 ∈ Pr.vGs then cst.muq (i + 1) P else ((muqT Ch mu i P.1 : X.Kˣ) : X.K))
    (if P.1 ∈ Pr.vGs then chiP Ch P.1 i else (resChar (mu : Chr X.F X.E X.K) P.1)⁻¹)

def stepC (A : Amb X) (u : Pr.Word) (i : ℕ) {b : ℕ} (lam' : X.Tau → DomWeight b) :
    ThDist X.E X.K (R.N i) b (rowSG Pr sel mu) (DIV.VV X.K (W.lamTrue u i)) (DIV.VV X.K lam') :=
  thDistC A (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst * cBof sel mu cst u) sel (mUof Ch mu i) (muAt Ch sel mu cst i) (W.lamTrue u i) lam' (nuLast W u i)

def chTh (A : Amb X) (u : Pr.Word) (m2 : ℕ) : ChTh W sel mu u m2 where
  th i := stepC W Ch sel mu cst A u i (W.lamTrue u (i + 1))
  top := stepC W Ch sel mu cst A u (m2 + 1) (W.lamTrue u R.m)

def stepT (A : Amb X) (u : Pr.Word) (i : ℕ) {b : ℕ} (lam' : X.Tau → DomWeight b) :
    ThDist X.E X.K (R.N i) b (rowSG Pr sel mu) (DIV.VV X.K (W.lamTrue u i)) (DIV.VV X.K lam') :=
  thDistC A (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst * cBof sel mu cst u) sel (mUof Ch mu i) (muAtT Ch sel mu cst i) (W.lamTrue u i) lam' (nuLast W u i)

def chThT (A : Amb X) (u : Pr.Word) (m2 : ℕ) : ChTh W sel mu u m2 where
  th i := stepT W Ch sel mu cst A u i (W.lamTrue u (i + 1))
  top := stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u R.m)

end Chain

section Stmts

def InRange {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} (Sall : Finset (HeightOneSpectrum (𝓞 E))) (D c : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) : Prop :=
  IsSdLat N ∧ IsSdLat N' ∧ 0 < c ∧ c ∣ D ∧ x ∈ divLat D (homAt Sall N N')

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)

def LatFin : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c c' : ℕ), IsSdLat N → IsSdLat N' → 0 < c → 0 < c' →
    Finite (↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)

def Amb.JetsRat : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange Sall D c N N' x →
    ∀ m : DVar X.Tau a b →₀ ℕ, ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m

def Amb.IndAdd : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c c' : ℕ) (x : HomE X.E a b), 0 < c → 0 < c' →
    InRange Sall D (c * c') N N' x → ∀ z, A.thInd Sall N N' c x z =
      latSum (mulLat c (homAt Sall N N')) (mulLat (c * c') (homAt Sall N N')) fun y => A.thInd Sall N N' (c * c') (x + y) z

def Amb.ESmooth : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' → ∀ k : ℕ, ContDiff ℂ k (A.e a b N N')

def Amb.IndSmooth : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange Sall D c N N' x →
    ∀ k : ℕ, ContDiff ℂ k (A.thInd Sall N N' c x)

def Amb.JetAdd : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c c' : ℕ) (x : HomE X.E a b), 0 < c → 0 < c' →
    InRange Sall D (c * c') N N' x → ∀ m, A.jetK Sall N N' c x m =
      latSum (mulLat c (homAt Sall N N')) (mulLat (c * c') (homAt Sall N N')) fun y => A.jetK Sall N N' (c * c') (x + y) m

def Amb.StepHyp : Prop :=
  LatFin (X := X) a b Sall ∧ A.IndAdd a b Sall D ∧ A.ESmooth a b ∧ A.JetsRat a b Sall D

open Classical in

def cosInd {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ) (x t : HomE E a b) : ℂ :=
  if t - x ∈ mulLat c (homAt S N N') then 1 else 0

def Amb.AAUnit : Prop := ∀ P ∈ Sall, localization₂ P.asIdeal A.AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E)

def Amb.HeisHyp : Prop :=
  A.δ ≠ 0 ∧ Nonempty X.Tau ∧ (∀ P ∈ Sall, conjPrime₂ P ∉ Sall) ∧ A.AAUnit Sall ∧
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    A.e a b N N' ∈ fixedBy (HV A.sc) (alV A.d A.sc) (LamC (X.embC A.σ₀) A.δ A.AA N N') ∧
    ∀ c : ℕ, 0 < c →
      SplitHyp (HV A.sc) (alV A.d A.sc) (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c) (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c)
        (LamC (X.embC A.σ₀) A.δ A.AA N N') ∧
      relIdx (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA Sall N N' c) ≠ 0 ∧
      relIdx (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) ≠ 0 ∧
      relIdx (LamC (X.embC A.σ₀) A.δ A.AA N N') (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c) ≠ 0

def Amb.LaHyp : Prop :=
  A.δ ≠ 0 ∧ Nonempty X.Tau ∧ (∀ P ∈ Sall, conjPrime₂ P ∉ Sall) ∧ A.AAUnit Sall ∧ A.AA.FG ∧
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    A.e a b N N' ∈ fixedBy (HV A.sc) (alV A.d A.sc) (LamC (X.embC A.σ₀) A.δ A.AA N N') ∧
    LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N'

def Amb.LiftIndep : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x s : HomE X.E a b), IsSdLat N → IsSdLat N' → 0 < c →
    A.IsLift Sall N N' c x s → ∀ z, A.thInd Sall N N' c x z =
      ((Real.sqrt (volC A.AA Sall N N') : ℝ) : ℂ)⁻¹ *
        xiInd (HV A.sc) (alV A.d A.sc) (volC A.AA Sall N N') (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c)
          (repsOf (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA Sall N N' c))
          (repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c))
          (A.e a b N N') (embH (X.embC A.σ₀) A.δ s) z

def Amb.Refine : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (s : HomE X.E a b), IsSdLat N → IsSdLat N' → 0 < c → c ∣ D →
    0 < D → s ∈ halfAO Sall (perO A.AA N N') D →
    ∀ T : Finset (VCx X.Tau a b), IsReps (BC (X.embC A.σ₀) A.δ A.AA Sall N N' D) (AC (X.embC A.σ₀) A.δ A.AA Sall N N' D) T → ∀ z,
      xiInd (HV A.sc) (alV A.d A.sc) (volC A.AA Sall N N') (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c)
          (repsOf (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA Sall N N' c))
          (repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c))
          (A.e a b N N') (embH (X.embC A.σ₀) A.δ s) z =
        ∑ t ∈ T, indL (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) (t - embH (X.embC A.σ₀) A.δ s) *
          xiInd (HV A.sc) (alV A.d A.sc) (volC A.AA Sall N N') (BC (X.embC A.σ₀) A.δ A.AA Sall N N' D)
            (repsOf (BC (X.embC A.σ₀) A.δ A.AA Sall N N' D) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA Sall N N' D))
            (repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA Sall N N' D))
            (A.e a b N N') t z

def Amb.IndTieD : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange Sall D c N N' x →
    0 < D → ∀ z, A.thInd Sall N N' c x z =
      ((Real.sqrt (volC A.AA Sall N N') : ℝ) : ℂ)⁻¹ *
        xiC (X.embC A.σ₀) A.δ A.d A.sc A.AA Sall N N' D (cosInd Sall N N' c x) (A.e a b N N') z

def MuDetLaw {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (n : ℕ) (mI sS : SB → X.E → X.K) : Prop :=
  ∀ (P : SB) (f : Sp X.E n ≃ₗ[X.E] Sp X.E n) (κ : ↥(GLint X.E n P.1)),
    mI P ((LinearEquiv.det (f * κ.1) : X.Eˣ) : X.E) = mI P ((LinearEquiv.det f : X.Eˣ) : X.E) * sS P ((LinearEquiv.det κ.1 : X.Eˣ) : X.E)

def UnitInv {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (sS sT : SB → X.E → X.K) : Prop :=
  ∀ (P : SB) (x : X.E), sT P x = (sS P x)⁻¹

def Amb.pullV (γ : Sp X.E a ≃ₗ[X.E] Sp X.E a) (γ' : Sp X.E b ≃ₗ[X.E] Sp X.E b) (z : VCx X.Tau a b) : VCx X.Tau a b :=
  fun τ i j => ∑ k : Fin b, ∑ l : Fin a,
    X.embC A.σ₀ τ (γ'.symm (Pi.single k 1) i) * z τ k l * X.embC A.σ₀ τ (γ (Pi.single j 1) l)

def Amb.ThIndEq : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b),
    InRange Sall D c N N' x → ∀ z, A.thInd Sall (gmap γ.1 N) (gmap γ'.1 N') c (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) z =
      A.thInd Sall N N' c x (A.pullV a b γ.1 γ'.1 z)

def MuProdLaw {X : Fields} (n : ℕ) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K) (e : X.Tau → ℤ) : Prop :=
  ∀ (γ : UF X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n SB), IsSdLat N →
    muInvDet sel SB mU mI (gmap γ.1 N) (fun P => γ.1 * fr P) =
      (∏ τ, X.emb τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ^ (-(e τ))) * muInvDet sel SB mU mI N fr

def Amb.ChiLaw : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    A.chiF a b (gmap γ.1 N) (gmap γ'.1 N') =
      (∏ τ, X.embC A.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) ^ (-((b / 2 : ℕ) : ℤ)) *
        (∏ τ, X.embC A.σ₀ τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E)) ^ (((a / 2 : ℕ) : ℤ)) * A.chiF a b N N'

def ThEquivP {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
    {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] (th : ThDist E K a b SB V V')
    (Sall : Finset (HeightOneSpectrum (𝓞 E))) (D : ℕ) (rho : UF E a →* Module.End K V) (rho' : UF E b →* Module.End K V') : Prop :=
  ∀ (γ : UF E a) (γ' : UF E b) N fr N' fr' c x, InRange Sall D c N N' x →
    th (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P) c
        (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = (rho' γ') ∘ₗ (th N fr N' fr' c x) ∘ₗ (rho γ⁻¹)

end Stmts

section Kernels

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {u : Pr.Word} {m2 : ℕ} (T : ChTh W sel mu u m2)

def matK (i : ℕ) (al : L.β i) (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) :
    (colValF W sel mu u i).V →ₗ[X.K] (colValF W sel mu u (i + 1)).V :=
  kerOf (T.th i) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p)
    p'.deco.1.N (frsF sel mu p') (XiEntry Ch sel mu cst L i al be p p')

open Classical in

def cp1K (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) :
    (colValF W sel mu u m2).V →ₗ[X.K] (colValF W sel mu u (m2 + 1)).V :=
  if Y ∈ ybSet sel mu cst p.deco.1.N then
    kerOf (T.th m2) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p₀.deco.1.N (frsF sel mu p₀)
      p.deco.1.N (frsF sel mu p) (XiCpl1 Ch sel mu cst L m2 al p₀ p Y)
  else 0

open Classical in

def cp2K (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu) :
    (colValF W sel mu u (m2 + 1)).V →ₗ[X.K] (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).V :=
  if Y ∈ ybSet sel mu cst p.deco.1.N then
    kerOf T.top (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p)
      (tilQ sel mu u d).1.N (frsT sel mu u d) (XiCpl2 Ch sel mu cst m2 p Y d)
  else 0

def ClsEq {K : Type} [Field K] [NumberField K] [StarRing K] {S S' : GSD K} (k : S.D → S'.D → (S.V →ₗ[K] S'.V)) : Prop :=
  ∀ (g : S.G) (g' : S'.G) (d : S.D) (d' : S'.D), k (g • d) (g' • d') = (S'.ρ g') ∘ₗ (k d d') ∘ₗ (S.ρ g⁻¹)

def CplEq1 {K : Type} [Field K] [NumberField K] [StarRing K] {S₀ S : GSD K} (Y : Cpl S) (k1 : S₀.D → S.D → Y.Yb → (S₀.V →ₗ[K] S.V)) : Prop :=
  ∀ (g₀ : S₀.G) (g : S.G) (d₀ : S₀.D) (d : S.D) (y : Y.Yb), k1 (g₀ • d₀) (g • d) (g • y) = (S.ρ g) ∘ₗ (k1 d₀ d y) ∘ₗ (S₀.ρ g₀⁻¹)

def CplEq2 {K : Type} [Field K] [NumberField K] [StarRing K] {S S₁ : GSD K} (Y : Cpl S) (k2 : S.D → Y.Yb → S₁.D → (S.V →ₗ[K] S₁.V)) : Prop :=
  ∀ (g : S.G) (g₁ : S₁.G) (d : S.D) (y : Y.Yb) (d₁ : S₁.D), k2 (g • d) (g • y) (g₁ • d₁) = (S₁.ρ g₁) ∘ₗ (k2 d y d₁) ∘ₗ (S.ρ g⁻¹)

def CplEq1On {K : Type} [Field K] [NumberField K] [StarRing K] {S₀ S : GSD K} (Y : Cpl S) (k1 : S₀.D → S.D → Y.Yb → (S₀.V →ₗ[K] S.V)) : Prop :=
  ∀ (g₀ : S₀.G) (g : S.G) (d₀ : S₀.D) (d : S.D) (y : Y.Yb), y ∈ Y.ys d →
    k1 (g₀ • d₀) (g • d) (g • y) = (S.ρ g) ∘ₗ (k1 d₀ d y) ∘ₗ (S₀.ρ g₀⁻¹)

def CplEq2On {K : Type} [Field K] [NumberField K] [StarRing K] {S S₁ : GSD K} (Y : Cpl S) (k2 : S.D → Y.Yb → S₁.D → (S.V →ₗ[K] S₁.V)) : Prop :=
  ∀ (g : S.G) (g₁ : S₁.G) (d : S.D) (y : Y.Yb) (d₁ : S₁.D), y ∈ Y.ys d →
    k2 (g • d) (g • y) (g₁ • d₁) = (S₁.ρ g₁) ∘ₗ (k2 d y d₁) ∘ₗ (S.ρ g⁻¹)

def MatEquiv : Prop :=
  ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)),
    ClsEq (S := (chF W sel mu L u i).mem al) (S' := (chF W sel mu L u (i + 1)).mem be) (matK W Ch sel mu cst L T i al be)

variable (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)

def Cp1Equiv : Prop :=
  ∀ al : L.β m2, CplEq1 (S₀ := (chF W sel mu L u m2).mem al) (S := midGSD W sel mu L u m2 b) (ybCpl W sel mu cst L u m2 b hY)
    (cp1K W Ch sel mu cst L T al)

def Cp2Equiv (P : LevFam X.E X.K R.r Pr.vGs) : Prop :=
  CplEq2 (S := midGSD W sel mu L u m2 b) (S₁ := evGSD W Ch sel mu P u) (ybCpl W sel mu cst L u m2 b hY) (cp2K W Ch sel mu cst T)

def Cp1EquivOn : Prop :=
  ∀ al : L.β m2, CplEq1On (S₀ := (chF W sel mu L u m2).mem al) (S := midGSD W sel mu L u m2 b) (ybCpl W sel mu cst L u m2 b hY)
    (cp1K W Ch sel mu cst L T al)

def Cp2EquivOn (P : LevFam X.E X.K R.r Pr.vGs) : Prop :=
  CplEq2On (S := midGSD W sel mu L u m2 b) (S₁ := evGSD W Ch sel mu P u) (ybCpl W sel mu cst L u m2 b hY) (cp2K W Ch sel mu cst T)

def zeroKer {K : Type} [Field K] [NumberField K] [StarRing K] (S S' : GSD K) : ClsKer S S' :=
  ⟨fun _ _ => 0, fun _ _ _ _ => by rw [LinearMap.zero_comp, LinearMap.comp_zero]⟩

open Classical in

def chKer (P : LevFam X.E X.K R.r Pr.vGs) (hM : MatEquiv W Ch sel mu cst L T) (h1 : Cp1Equiv W Ch sel mu cst L T b hY)
    (h2 : Cp2Equiv W Ch sel mu cst L T b hY P) : ChKer W Ch sel mu cst L P u m2 b hY where
  kk i al be := if h : i < m2 then ClsKer.mk (matK W Ch sel mu cst L T i al be) (hM i h al be) else zeroKer _ _
  cp al := CplKer.mk (cp1K W Ch sel mu cst L T al) (cp2K W Ch sel mu cst T) (h1 al) h2

end Kernels

section Const

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)

def JetInVVStep (i : ℕ) {b' : ℕ} (lam' : X.Tau → DomWeight b') : Prop := JetInVV X.K (W.lamTrue u i) lam' (nuLast W u i)

def KerEquivC : Prop :=
  MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) ∧ Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY ∧
    Cp2Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY P

def chKerC (h : KerEquivC W Ch sel mu cst L A u m2 b hY P) : ChKer W Ch sel mu cst L P u m2 b hY :=
  chKer W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY P h.1 h.2.1 h.2.2

def colMu (h : KerEquivC W Ch sel mu cst L A u m2 b hY P) (hF : ∀ j, (chF W sel mu L u j).Ok) {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2) :
    MfV W Ch u →ₗ[X.K] (evGSD W Ch sel mu P u).EqFun :=
  colC (chKerC W Ch sel mu cst L A u m2 b hY P h) hF hL

end Const

section Seam

open Formalism.MainNotions

structure Seam (D : D7) (X : Fields) where
  iE : X.E ≃+* D.host.E
  iT : X.Tau ≃ D.what₂.Tau
  σ₀ : X.K →+* ℂ

variable {D : D7} {X : Fields} (s : Seam D X)

def Seam.Ok : Prop :=
  (∀ τ x, s.σ₀ (X.emb τ x) = TaylorLogMetric.embT D (s.iT τ) (s.iE x)) ∧ ∀ x, s.iE (star x) = D.host.conj (s.iE x)

def Seam.lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.span (𝓞 D.host.E) ((fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) '' (N : Set (Sp X.E n)))

def IsDgen (D : D7) (cD : D.what₂.Tau → ℂ) : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), (∀ τ x, TaylorLogMetric.embT D τ x ∈ M) ∧ ∀ τ, ∃ s : M, (s : ℂ) = cD τ ∧
    TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {s}

def ambOf {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Amb X where
  σ₀ := s.σ₀
  δ := δ
  d := D.host.d
  sc := (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹
  AA := Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}
  cD τ := cD (s.iT τ)
  e a b N N' z := B.eNat χ a b (s.lat N) (s.lat N') fun τ => z (s.iT.symm τ)
  chiF a b N N' := Base.chiFac χ a b (s.lat N) (s.lat N')

end Seam

end Formalism.L2.Ker
