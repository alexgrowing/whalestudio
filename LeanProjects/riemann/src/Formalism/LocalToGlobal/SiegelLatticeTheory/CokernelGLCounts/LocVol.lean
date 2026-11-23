import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

noncomputable section

namespace Formalism.L2.SG.LocVol

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

abbrev TupV (n a : ℕ) : Type := Fin a → Fin n → Fv F v ⊗[F] E

def dX (a : ℕ) : Measure (TupV (E := E) v n a) :=
  if h : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ then h.choose else 0

def dT (a : ℕ) : Measure (HermR (Fv F v) σ a) :=
  if h : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν then h.choose else 0

def IndepV (a : ℕ) : Set (TupV (E := E) v n a) := {X | LinearIndependent (Fv F v ⊗[F] E) X}

def IsOm (a : ℕ) (fib : HermR (Fv F v) σ a → Measure (TupV (E := E) v n a)) : Prop :=
  IsFibreFamily (dX σ J ψ v a) (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a)
    (dT σ ψ v a) Set.univ fib

def omFam (a : ℕ) : HermR (Fv F v) σ a → Measure (TupV (E := E) v n a) :=
  if h : ∃ fib, IsOm σ J ψ v a fib then h.choose else fun _ => 0

def omAt {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) : Measure (TupV (E := E) v n a) :=
  if h : T ∈ HermR (Fv F v) σ a then omFam σ J ψ v a ⟨T, h⟩ else 0

def sdE (ι : Type) [Fintype ι] : Measure (ι → Fv F v ⊗[F] E) :=
  if h : ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ
      (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)))
  then h.choose else 0

def IsStdChar (ψ : AddChar (AF F) ℂ) : Prop :=
  ∀ x : Ainf F, psiInf F ψ x =
    Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : NumberField.InfinitePlace F, (NumberField.InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

def StdHyp : Prop := IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧ IsStdChar ψ

def SdExists (a : ℕ) (ι : Type) [Fintype ι] : Prop :=
  StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) ∧
  ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ
      (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)))

def OmUnique (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ fib, IsOm σ J ψ v a fib) ∧ ∀ fib fib', IsOm σ J ψ v a fib → IsOm σ J ψ v a fib' → fib = fib'

end Meas

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def OEv : Set (Fv F v ⊗[F] E) :=
  SetLike.coe (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ))

def sc (x : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ[F] (1 : E)

variable {n : ℕ} (Λ : Set (Fin n → E))

def IsPrim {a : ℕ} (X : TupV (E := E) v n a) : Prop :=
  (∀ i, X i ∈ latLoc (E := E) v Λ) ∧
  ∀ c : Fin a → Fv F v ⊗[F] E, (∑ i, c i • X i) ∈ latLoc (E := E) v Λ → ∀ i, c i ∈ OEv (E := E) v

def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d

def dV : Fv F v := if h : ∃ d, IsDiffVal v d then h.choose else 1

def DiffExists : Prop := ∃ d, IsDiffVal v d

def alp (r : ℕ) (a : Fin (r + 1)) : Fv F v := if (a : ℕ) < r then (dV v)⁻¹ ^ (r - (a : ℕ)) else 1

def locF {r : ℕ} (X : TupV (E := E) v n (r + 1)) : TupV (E := E) v n (r + 1) :=
  fun a => sc (E := E) v (alp v r a) • X a

def locZ {r : ℕ} (z : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) (i j : Fin (r + 1)) : Fv F v ⊗[F] E :=
  sc (E := E) v (alp v r i * alp v r j) * z (i, j)

end Frames

section Sets

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def OmOrd (r : ℕ) : Set (TupV (E := E) v n (r + 1) × TupV (E := E) v n (r + 1)) :=
  {p | IsPrim v Λ (locF v p.1) ∧ IsPrim v Λ (locF v p.2)}

def OmTyp (g r : ℕ) : Set (TupV (E := E) v n (r + 1) × TupV (E := E) v n (r + 1)) :=
  {p | IsPrim v Λ (locF v p.1) ∧ IsPrim v Λ (locF v p.2) ∧
    ∀ a, ∃ y ∈ latLoc (E := E) v Λ, locF v p.2 a - locF v p.1 a = sc (E := E) v (g : Fv F v) • y}

def Mv {r : ℕ} (TF TF' : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E))
    (Om : Set (TupV (E := E) v n (r + 1) × TupV (E := E) v n (r + 1))) : ℝ :=
  (((omAt σ J ψ v TF).prod (omAt σ J ψ v TF')) Om).toReal

def ZZOrd (r : ℕ) : Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {z | ∀ i j, locZ v z i j ∈ OEv (E := E) v}

def ZZTyp (g r : ℕ) (TF TF' : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :
    Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {z | ∀ i j, (locZ v z i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v ∧
    ((locZ v z i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ +
        sigR (Fv F v) σ ((locZ v z j i - TF j i) * sc (E := E) v (g : Fv F v)⁻¹) -
        (TF' i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}

def PPOrd (r : ℕ) (l : Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  {c | sc (E := E) v (alp v r l ^ 2) * c ∈ OEv (E := E) v}

def PPTyp (g r T T' : ℕ) (l : Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  if (l : ℕ) < r then
    {c | sc (E := E) v (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈ OEv (E := E) v ∧
      sc (E := E) v (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) * (c + sigR (Fv F v) σ c) ∈ OEv (E := E) v}
  else
    {c | sc (E := E) v (g : Fv F v)⁻¹ * (c + (T : Fv F v ⊗[F] E)) ∈ OEv (E := E) v ∧
      sc (E := E) v (((g : Fv F v)⁻¹) ^ 2) * (c + sigR (Fv F v) σ c + (T : Fv F v ⊗[F] E) + (T' : Fv F v ⊗[F] E))
        ∈ OEv (E := E) v}

abbrev UIdx (r : ℕ) : Type := {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}

def UO (r : ℕ) : Set (UIdx r → Fv F v ⊗[F] E) :=
  {x | ∀ p, sc (E := E) v ((alp v r p.1.1)⁻¹ * alp v r p.1.2) * x p ∈ OEv (E := E) v}

def localVolumeOrdinary (r : ℕ) : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E)) :=
  UO v r ×ˢ UO v r

def deepCongruenceVolume (g r : ℕ) : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E)) :=
  {p | p.1 ∈ UO v r ∧ p.2 ∈ UO v r ∧ ∀ q,
    sc (E := E) v ((alp v r q.1.1)⁻¹ * alp v r q.1.2 * (g : Fv F v)⁻¹) * (p.1 q - p.2 q) ∈ OEv (E := E) v}

def volS {r : ℕ} (S : Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E)) : ℝ :=
  (sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) S).toReal

def volC (S : Set (Fv F v ⊗[F] E)) : ℝ :=
  (sdE (E := E) ψ v Unit ((fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' S)).toReal

def volU {r : ℕ} (S : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E))) : ℝ :=
  (((sdE (E := E) ψ v (UIdx r)).prod (sdE (E := E) ψ v (UIdx r))) S).toReal

def absV (x : Fv F v) : ℝ :=
  if h : Valued.v x = 0 then 0
  else ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (Multiplicative.toAdd (WithZero.unzero h))

def jacS (typed : Prop) (g r : ℕ) : ℝ :=
  ∏ l : Fin r, ((absV v ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), alp v r i ^ 2) *
    (if typed then ((g : Fv F v)⁻¹) ^ ((l : ℕ) + 1) else 1))) ^ 2) ^ 2

def etaV : ℤ := if ∃ x : Fv F v ⊗[F] E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1 then 1 else -1

def aP (k N T : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc (if ((T : 𝓞 F) ∈ v.asIdeal) then k else k + 1) N,
    (1 - ((etaV (E := E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i)

end Sets

section OfSetting

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

abbrev PlX : Type := HeightOneSpectrum (𝓞 X.B.I.F)

def TypAt (v : PlX X) : Prop := v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)

abbrev OrdX : Type := {v : PlX X // ¬ TypAt X v}

def gAt (v : PlX X) : ℕ := if ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal then D.host.g 0 else D.host.g 1

def Tw (w : D.what₂.Word) : ℕ := ((D.mem w).A.T : ℕ)

def TFv (w : D.what₂.Word) (v : PlX X) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) :=
  (gramE X.B.I.cm.sig X.B.I.J (F0 (frameOf X w))).map (inclR (Fv X.B.I.F v))

def OmX (v : PlX X) :
    Set (TupV (E := X.B.I.E) v X.B.I.n (D.R.rS + 1) × TupV (E := X.B.I.E) v X.B.I.n (D.R.rS + 1)) :=
  if TypAt X v then OmTyp v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (gAt X v) D.R.rS
  else OmOrd v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) D.R.rS

def MX (v : PlX X) : ℝ := Mv X.B.I.cm.sig X.B.I.J ψ v (TFv X u v) (TFv X u' v) (OmX X v)

def ZZX (v : PlX X) : ℝ :=
  volS (E := X.B.I.E) ψ v (if TypAt X v then ZZTyp X.B.I.cm.sig v (gAt X v) D.R.rS (TFv X u v) (TFv X u' v)
    else ZZOrd v D.R.rS)

def PPX (l : Fin (D.R.rS + 1)) (v : PlX X) : ℝ :=
  volC (E := X.B.I.E) ψ v (if TypAt X v then PPTyp X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u') l
    else PPOrd v D.R.rS l)

def localVolumeUnit (v : PlX X) : ℝ :=
  volU (E := X.B.I.E) ψ v (if TypAt X v then deepCongruenceVolume v (gAt X v) D.R.rS else localVolumeOrdinary v D.R.rS)

def alX (v : PlX X) : ℝ :=
  if TypAt X v then aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u)
  else aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u) * aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u')

def jacX (v : PlX X) : ℝ := jacS v (TypAt X v) (gAt X v) D.R.rS

def locOf : LocIn (TypX X) where
  Mp p := MX X u u' ψ p.1
  localVolumeAtPlace p := localVolumeUnit X ψ p.1
  Mo := ∏' v : OrdX X, MX X u u' ψ v.1
  localVolumeArchimedean := ∏' v : OrdX X, localVolumeUnit X ψ v.1
  volZZ := ∏' v : PlX X, ZZX X u u' ψ v
  volPP := ∏ l : Fin (D.R.rS + 1), ∏' v : PlX X, PPX X u u' ψ l v
  al := (∏ p : TypX X, alX X u u' p.1) * ∏' v : OrdX X, alX X u u' v.1

def ProdConv : Prop :=
  (∀ v, (TypAt X v → 0 < MX X u u' ψ v) ∧ 0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧
    0 < alX X u u' v) ∧
  True ∧ True ∧
  Multipliable (fun v : OrdX X => localVolumeUnit X ψ v.1) ∧ 0 < ∏' v : OrdX X, localVolumeUnit X ψ v.1 ∧
  Multipliable (ZZX X u u' ψ) ∧ 0 < ∏' v : PlX X, ZZX X u u' ψ v ∧
  (∀ l, Multipliable (PPX X u u' ψ l) ∧ 0 < ∏' v : PlX X, PPX X u u' ψ l v) ∧
  Multipliable (fun v : OrdX X => alX X u u' v.1) ∧ 0 < ∏' v : OrdX X, alX X u u' v.1 ∧
  Multipliable (jacX X) ∧ 0 < ∏' v : PlX X, jacX X v

def ProdConvOK : Prop := IsCharAF X.B.I.F ψ → IsStdChar ψ → ProdConv X u u' ψ

def JacLocAt (v : PlX X) : Prop :=
  (TypAt X v → (gAt X v : ℤ) ∣ ((Tw u : ℤ) - Tw u')) →
    ZZX X u u' ψ v * jacX X v = localVolumeUnit X ψ v * ∏ l : Fin (D.R.rS + 1), PPX X u u' ψ l v

def FinJac : Prop :=
  ProdConv X u u' ψ → (∀ p : TypX X, (gAt X p.1 : ℤ) ∣ ((Tw u : ℤ) - Tw u')) →
    (locOf X u u' ψ).volZZ * ∏' v : PlX X, jacX X v =
      ((locOf X u u' ψ).localVolumeArchimedean * ∏ p : TypX X, (locOf X u u' ψ).localVolumeAtPlace p) * (locOf X u u' ψ).volPP

end OfSetting

section Ties

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def IsCompatLoc {a : ℕ} (X0 : Fin a → Fin n → E) (μ : Measure (HA (Fv F v) σ J))
    (μ' : Measure (stabT (Fv F v) σ J X0)) (ν : Measure (TupV (E := E) v n a)) : Prop :=
  ν {y | ¬ ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) X0 = y} = 0 ∧
  ∀ f : HA (Fv F v) σ J → ENNReal, Measurable f →
    ∀ s : TupV (E := E) v n a → HA (Fv F v) σ J,
      (∀ y, (∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) X0 = y) → s y • ratTup (Fv F v) X0 = y) →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Fv F v) σ J)) ∂μ' ∂ν

def uMat {r : ℕ} (x : UIdx r → Fv F v ⊗[F] E) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E) :=
  fun a b => if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0

def IsProdU {r : ℕ} (P : Frame E n r) (μS : Measure (Ssub (Fv F v) σ J P)) (μS0 : Measure (S0 (Fv F v) σ J P))
    (μU : Measure (UIdx r → Fv F v ⊗[F] E)) : Prop :=
  ∀ h : HA (Fv F v) σ J → ENNReal, Measurable h →
    ∀ t : (UIdx r → Fv F v ⊗[F] E) → HA (Fv F v) σ J,
      (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) =
        ∑ a, uMat v x a b • ratV (F := F) (Fv F v) (F0 P a)) →
      ∫⁻ s, h s ∂(amb μS) = ∫⁻ x, ∫⁻ s0, h ((s0 : HA (Fv F v) σ J) * t x) ∂μS0 ∂μU

def TFl {r : ℕ} (P : Frame E n r) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E) :=
  (gramE σ J (F0 P)).map (inclR (Fv F v))

def LocTieW {r : ℕ} (P : Frame E n r) (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P)) :
    Prop :=
  ∃ μS0 : Measure (S0 (Fv F v) σ J P), μS0.IsHaarMeasure ∧
    IsCompatLoc σ J v (F0 P) μG μS0 (omAt σ J ψ v (TFl σ J v P)) ∧
    IsProdU σ J v P μS μS0 (sdE (E := E) ψ v (UIdx r))

def KSv {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E)) : Set (Ssub (Fv F v) σ J P) :=
  Subtype.val ⁻¹' Formalism.L2.SG.TypedSets.Kv σ J Λ v

def KSvT {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E)) (y : HA (Fv F v) σ J) : Set (Ssub (Fv F v) σ J P) :=
  {s | y * (s : HA (Fv F v) σ J) * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v}

def IsSDLoc (Λ : Set (Fin n → E)) : Prop :=
  ∀ y, y ∈ latLoc (E := E) v Λ ↔ ∀ x ∈ latLoc (E := E) v Λ, hR (Fv F v) σ J x y ∈ OEv (E := E) v

def UnramAt : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal →
    Ideal.ramificationIdx P (𝓞 F) = 1

def OrdLocAt {r : ℕ} (P P' : Frame E n r) (Λ : Set (Fin n → E)) : Prop :=
  StdHyp σ J ψ → ∀ T T' : F, P.IsStd σ J T → P'.IsStd σ J T' → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure →
  ∀ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure → LocTieW σ J ψ v P μG μS →
  ∀ μS' : Measure (Ssub (Fv F v) σ J P'), μS'.IsHaarMeasure → LocTieW σ J ψ v P' μG μS' →
  ∀ y y' : HA (Fv F v) σ J,
  IsPrim v Λ (locF v (y • ratTup (Fv F v) (F0 P))) → IsPrim v Λ (locF v (y' • ratTup (Fv F v) (F0 P'))) →
    Mv σ J ψ v (TFl σ J v P) (TFl σ J v P') (OmOrd v Λ r) / volU (E := E) ψ v (localVolumeOrdinary v r) =
      (μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v)).toReal ^ 2 /
        ((μS (KSvT σ J v P Λ y)).toReal * (μS' (KSvT σ J v P' Λ y')).toReal)

def TypLocAt {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E)) : Prop :=
  StdHyp σ J ψ → ∀ T T' : F, P.IsStd σ J T → P'.IsStd σ J T' → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) → g.Prime → (g : 𝓞 F) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g → etaV (E := E) v = 1 →
  (∃ κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, ∀ a, ∃ y ∈ latLoc (E := E) v Λ,
    locF v (κ • ratTup (Fv F v) (F0 P')) a - locF v (ratTup (Fv F v) (F0 P)) a = sc (E := E) v (g : Fv F v) • y) →
  ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure →
  ∀ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure → LocTieW σ J ψ v P μG μS →
  ∀ μS' : Measure (Ssub (Fv F v) σ J P'), μS'.IsHaarMeasure → LocTieW σ J ψ v P' μG μS' →
  IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P))) → IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P'))) →
    Mv σ J ψ v (TFl σ J v P) (TFl σ J v P') (OmTyp v Λ g r) / volU (E := E) ψ v (deepCongruenceVolume v g r) =
      (μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v)).toReal * (μG (Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v)).toReal /
        ((μS (KSv σ J v P Λ)).toReal * (μS' (KSv σ J v P' Λ)).toReal)

end Ties

section MassDataConditions

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.AdBridge

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (A : AnIn) (ψ : AddChar (AF X.B.I.F) ℂ)

abbrev LamX : Set (Fin X.B.I.n → X.B.I.E) := (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def ProdTie (w : D.what₂.Word) : Prop :=
  Multipliable (fun v : PlX X => (X.measG.μGv v (Kv X.B.I.cm.sig X.B.I.J (LamX X) v)).toReal) ∧
  (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (LamX X))).toReal =
    ∏' v : PlX X, (X.measG.μGv v (Kv X.B.I.cm.sig X.B.I.J (LamX X) v)).toReal ∧
  Multipliable (fun v : PlX X =>
    ((X.measW w).μSv v (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (LamX X) v)).toReal) ∧
  ((X.measW w).μSf (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (LamX X) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal =
    ∏' v : PlX X, ((X.measW w).μSv v (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (LamX X) v)).toReal

def LocTieX (w : D.what₂.Word) : Prop :=
  ∀ v : PlX X, (X.measG.μGv v).IsHaarMeasure ∧ ((X.measW w).μSv v).IsHaarMeasure ∧
    LocTieW X.B.I.cm.sig X.B.I.J ψ v (frameOf X w) (X.measG.μGv v) ((X.measW w).μSv v) ∧
    IsPrim v (LamX X) (locF v (ratTup (Fv X.B.I.F v) (F0 (frameOf X w))))

def TypFacts : Prop :=
  ∀ p : TypX X, (gAt X p.1).Prime ∧ Ideal.absNorm p.1.asIdeal = gAt X p.1 ∧ etaV (E := X.B.I.E) p.1 = 1 ∧
    (gAt X p.1 : ℤ) ∣ ((Tw u : ℤ) - Tw u') ∧
    ∃ κ ∈ Kv X.B.I.cm.sig X.B.I.J (LamX X) p.1, ∀ a, ∃ y ∈ latLoc (E := X.B.I.E) p.1 (LamX X),
      locF p.1 (κ • ratTup (Fv X.B.I.F p.1) (F0 (frameOf X u'))) a -
        locF p.1 (ratTup (Fv X.B.I.F p.1) (F0 (frameOf X u))) a = sc (E := X.B.I.E) p.1 (gAt X p.1 : Fv X.B.I.F p.1) • y

def InOrdinaryAt : Prop :=
  ProdConv X u u' ψ → ProdTie X u → ProdTie X u' → LocTieX X ψ u → LocTieX X ψ u' →
    (bOf X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) A).InOrdinary

def InTypedAt : Prop :=
  HypX X hb FdN FdN' u u' → ProdConv X u u' ψ → LocTieX X ψ u → LocTieX X ψ u' → TypFacts X u u' →
    (bOf X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) A).InTyped

def OrdLocX : Prop :=
  ∀ v : OrdX X, OrdLocAt X.B.I.cm.sig X.B.I.J ψ v.1 (frameOf X u) (frameOf X u') (LamX X)

def TypLocX : Prop :=
  ∀ p : TypX X, TypLocAt X.B.I.cm.sig X.B.I.J ψ p.1 (gAt X p.1) (frameOf X u) (frameOf X u') (LamX X)

end MassDataConditions

section Parts

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem gAt_prime (v : PlX X) : (gAt X v).Prime := by
  unfold gAt
  split_ifs
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1

def GSplitX : Prop :=
  ∀ p : TypX X, Ideal.absNorm p.1.asIdeal = gAt X p.1 ∧ etaV (E := X.B.I.E) p.1 = 1

def TCongX : Prop := ∀ p : TypX X, (gAt X p.1 : ℤ) ∣ ((Tw u : ℤ) - Tw u')

def KapX : Prop :=
  ∀ p : TypX X, ∃ κ ∈ Kv X.B.I.cm.sig X.B.I.J (LamX X) p.1, ∀ a, ∃ y ∈ latLoc (E := X.B.I.E) p.1 (LamX X),
    locF p.1 (κ • ratTup (Fv X.B.I.F p.1) (F0 (frameOf X u'))) a -
      locF p.1 (ratTup (Fv X.B.I.F p.1) (F0 (frameOf X u))) a = sc (E := X.B.I.E) p.1 (gAt X p.1 : Fv X.B.I.F p.1) • y

theorem T_sub_one_dvd (D : D7) (u : D.what₂.Word) :
    ((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : ℤ) ∣ (((D.mem u).A.T : ℕ) : ℤ) - 1 := by
  obtain ⟨π, -, hT, hm⟩ := D.T_norm u
  set m : ℕ := D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 with hmdef
  rw [Ideal.mem_span_singleton] at hm
  obtain ⟨c, hc⟩ := hm

  have hπ : (π : D.host.E) = 1 + (m : D.host.E) * (c : D.host.E) := by
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hc
    simp only [map_sub, map_one, map_mul, map_natCast] at this
    linear_combination this
  set y : D.host.E := (c : D.host.E) + D.host.conj (c : D.host.E) + (m : D.host.E) * (c : D.host.E) * D.host.conj (c : D.host.E)
    with hy
  have hTy : (((D.mem u).A.T : ℕ) : D.host.E) - 1 = (m : D.host.E) * y := by
    rw [← hT, hπ, map_add, map_one, map_mul, map_natCast]
    ring
  have hint : IsIntegral ℤ y := by
    have h1 : IsIntegral ℤ (c : D.host.E) := c.2
    have h2 : IsIntegral ℤ (D.host.conj (c : D.host.E)) :=
      h1.map (D.host.conj.toAlgHom.restrictScalars ℤ)
    have h3 : IsIntegral ℤ (m : D.host.E) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ D.host.E (m : ℤ)))
    exact (h1.add h2).add ((h3.mul h1).mul h2)
  by_cases hm0 : m = 0
  · simp [hm0] at hTy ⊢
    have : (((D.mem u).A.T : ℕ) : D.host.E) = 1 := sub_eq_zero.mp hTy
    have h' : (((D.mem u).A.T : ℕ) : ℤ) = 1 := by exact_mod_cast this
    omega
  · set q : ℚ := ((((D.mem u).A.T : ℕ) : ℤ) - 1 : ℤ) / (m : ℚ) with hq
    have hyq : y = algebraMap ℚ D.host.E q := by
      have hmE : (m : D.host.E) ≠ 0 := by exact_mod_cast hm0
      rw [hq, map_div₀]
      push_cast
      field_simp
      rw [mul_comm]; exact hTy.symm
    rw [hyq] at hint
    have hqint : IsIntegral ℤ q := (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ D.host.E)
      (algebraMap ℚ D.host.E).injective).mp hint
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqint
    refine ⟨z, ?_⟩
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
    have hz' : (z : ℚ) = q := by simpa using hz
    have : ((((D.mem u).A.T : ℕ) : ℤ) - 1 : ℚ) = (m : ℚ) * (z : ℚ) := by
      rw [hz', hq]; push_cast; field_simp
    exact_mod_cast this

theorem tCongX : TCongX X u u' := by
  intro p
  have hg : (gAt X p.1 : ℤ) ∣ ((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : ℤ) := by
    apply Int.natCast_dvd_natCast.mpr
    apply Dvd.dvd.mul_left
    unfold gAt
    split_ifs
    · exact dvd_pow (dvd_mul_right _ _) two_ne_zero
    · exact dvd_pow (dvd_mul_left _ _) two_ne_zero
  have h := dvd_sub (hg.trans (T_sub_one_dvd D u)) (hg.trans (T_sub_one_dvd D u'))
  have e : (((D.mem u).A.T : ℕ) : ℤ) - 1 - ((((D.mem u').A.T : ℕ) : ℤ) - 1) = (Tw u : ℤ) - Tw u' := by
    unfold Tw; ring
  rwa [e] at h

theorem typFacts_of (h1 : GSplitX X) (h2 : TCongX X u u') (h3 : KapX X u u') : TypFacts X u u' :=
  fun p => ⟨gAt_prime X p.1, (h1 p).1, (h1 p).2, h2 p, h3 p⟩

def LocCompatX (w : D.what₂.Word) : Prop :=
  ∀ v : PlX X, LocTieW X.B.I.cm.sig X.B.I.J ψ v (frameOf X w) (X.measG.μGv v) ((X.measW w).μSv v)

def PrimX (w : D.what₂.Word) : Prop :=
  ∀ v : PlX X, IsPrim v (LamX X) (locF v (ratTup (Fv X.B.I.F v) (F0 (frameOf X w))))

theorem locTieX_of (w : D.what₂.Word) (h1 : LocCompatX X ψ w) (h2 : PrimX X w) : LocTieX X ψ w := by
  intro v
  refine ⟨X.measG_norm.2.2.2.1 v, (X.measW_norm w).2.2.2.2.2.2.2.1 v, h1 v, h2 v⟩

end Parts

end Formalism.L2.SG.LocVol
