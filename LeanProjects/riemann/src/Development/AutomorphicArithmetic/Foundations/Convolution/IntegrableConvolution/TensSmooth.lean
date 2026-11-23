import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev InfD (σ : E ≃ₐ[F] E) (m : ℕ) : Type :=
  Split (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (galInf σ) m

variable {σ : E ≃ₐ[F] E} {m : ℕ}

def compA (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : archGroup E n →* archGroup F n :=
  (archEquiv F n).toMonoidHom.comp ((D.comp n i).comp (archEquiv E n).symm.toMonoidHom)

def glueA (D : InfD σ m) (n : ℕ) (g : Fin (m + 1) → archGroup F n) : archGroup E n :=
  archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i))

def IsTens (D : InfD σ m) {n : ℕ} (φ : Fin (m + 1) → TI F n) (β : TI E n) : Prop := ∀ g, β g = ∏ i, φ i (compA D n i g)

def IsBlockElement (D : InfD σ m) (n : ℕ) (s : Fin (m + 1) → archGroup F n →* archGroup E n) : Prop :=
  ∀ i g, s i g = glueA D n (Pi.mulSingle i g)

def InSlot (D : InfD σ m) (τ : E →+* ℂ) (k : Fin (m + 1)) : Prop :=
  ∀ z : ℂ, (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (along τ z) =
    D.e.symm (Pi.single k ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (along (τ.comp (algebraMap F E)) z)))

structure ArchSlot (D : InfD σ m) {n : ℕ} (νE : Measure (archGroup E n)) (νF : Measure (archGroup F n)) (b a : TI F n)
    (aE : TI E n) (aF : TI F n) : Prop where
  meas : νE = Measure.map (glueA D n) (Measure.pi fun _ => νF)
  smooth : SmoothT b
  fin : LeftFin b
  norm : ∫ g, ‖b g‖ ∂νF ≤ 1
  sq : ∀ g, a g = cv νF b (fun x => conj (b x⁻¹)) g
  tens : IsTens D (fun _ => a) aE
  pow : ∀ g, aF g = cvPow νF a m g

end

def ArchBasic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ),
    (∀ g i, compA D n i (glueA D n g) = g i) ∧ (∀ x, glueA D n (fun i => compA D n i x) = x) ∧
    (∀ g h, glueA D n (g * h) = glueA D n g * glueA D n h) ∧ Continuous (glueA D n) ∧ (∀ i, Continuous (compA D n i)) ∧
    (∃ s, IsBlockElement D n s ∧ ∀ i, Continuous (s i)) ∧
    (∀ (νF : Measure (archGroup F n)) [νF.IsHaarMeasure], (Measure.map (glueA D n) (Measure.pi fun _ => νF)).IsHaarMeasure) ∧
    ∀ φ : Fin (m + 1) → TI F n, ∃ β, IsTens D φ β

def PositionOf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : InfD σ m), (∀ τ, ∃ k, InSlot D τ k) ∧
      ∀ (n : ℕ) (g : archGroup E n), g ∈ archCompact E n ↔ ∀ i, compA D n i g ∈ archCompact F n

def TensSmooth : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : InfD σ m) (n : ℕ) (φ : Fin (m + 1) → TI F n) (β : TI E n), IsTens D φ β →
    ((∀ i, SmoothT (φ i)) → SmoothT β) ∧ ((∀ i, LeftFin (φ i)) → LeftFin β)

def JUnique : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (τ : K →+* ℂ),
    (∃! j, IsJ (n := n) τ j) ∧ ∀ i : Fin n, zc τ i ∈ Subalgebra.center ℂ (UC K n)

def LactLaws : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (β : TI K n), SmoothT β →
    (∀ u, SmoothT (lact u β)) ∧ lact 1 β = β ∧ (∀ u v, lact (u * v) β = lact u (lact v β)) ∧
      (∀ u v, lact (u + v) β = lact u β + lact v β) ∧ ∀ (c : ℂ) u, lact (c • u) β = c • lact u β

def LactGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : InfD σ m) (n : ℕ) (τ : E →+* ℂ) (k : Fin (m + 1)), InSlot D τ k → ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n),
    (∀ i, SmoothT (φ i)) → IsTens D φ β → ∀ (p q : Fin n) (z : ℂ),
      IsTens D (Function.update φ k (lact ((1 : ℂ) ⊗ₜ elem (τ.comp (algebraMap F E)) p q z) (φ k))) (lact ((1 : ℂ) ⊗ₜ elem τ p q z) β)

def LactTens : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E]
    (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ) (τ : E →+* ℂ) (k : Fin (m + 1)), InSlot D τ k →
    ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β → ∀ i : Fin n,
      IsTens D (Function.update φ k (lact (zc (τ.comp (algebraMap F E)) i) (φ k))) (lact (zc τ i) β)

def LactCv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
    (α β γ : TI K n), SmoothT α → (∀ g, γ g = cv ν α β g) → SmoothT γ ∧ (LeftFin α → LeftFin γ) ∧
      (∀ u g, lact u γ g = cv ν (lact u α) β g) ∧
      (SmoothT β → ∀ z ∈ Subalgebra.center ℂ (UC K n), ∀ g, lact z γ g = cv ν α (lact z β) g)

def TensOp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ)
    (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure],
    νE = Measure.map (glueA D n) (Measure.pi fun _ => νF) →
    ∀ (s : Fin (m + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup E n) H)
      (φ : Fin (m + 1) → TI F n) (β : TI E n), IsTens D φ β →
      π.integrated νE (UnitaryRep.ccToL1 νE β) =
        (List.ofFn fun i => (π.compHom (s i) (hs i)).integrated νF (UnitaryRep.ccToL1 νF (φ i))).prod

def SqOp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (b a aF : TI K n) (m : ℕ),
    (∀ g, a g = cv ν b (fun x => conj (b x⁻¹)) g) → (∀ g, aF g = cvPow ν a m g) → ∫ g, ‖b g‖ ∂ν ≤ 1 →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup K n) H),
      π.integrated ν (UnitaryRep.ccToL1 ν a) =
          π.integrated ν (UnitaryRep.ccToL1 ν b) * star (π.integrated ν (UnitaryRep.ccToL1 ν b)) ∧
        0 ≤ π.integrated ν (UnitaryRep.ccToL1 ν a) ∧ ‖π.integrated ν (UnitaryRep.ccToL1 ν a)‖ ≤ 1 ∧
        π.integrated ν (UnitaryRep.ccToL1 ν aF) = π.integrated ν (UnitaryRep.ccToL1 ν a) ^ (m + 1)

def ArchSlotEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ)
    (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b : TI F n), SmoothT b → LeftFin b → ∫ g, ‖b g‖ ∂νF ≤ 1 →
    ∃ (νE : Measure (archGroup E n)) (_ : νE.IsHaarMeasure) (a : TI F n) (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF

def BumpEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup K n) H) (v : H), v ≠ 0 →
    ∃ b : TI K n, SmoothT b ∧ LeftFin b ∧ ∫ g, ‖b g‖ ∂ν ≤ 1 ∧ star (π.integrated ν (UnitaryRep.ccToL1 ν b)) v ≠ 0

end UpperTheory.ConvolutionTheory.L1
