import Mathlib
import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Formalism.LocalRingCardinality.DataKap
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds

noncomputable section

namespace Formalism.MainNotions.PrimeDegreeVariant

open Formalism.BasicNotions MvPolynomial

def blkHom (R : Type) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by simp [Matrix.fromBlocks_multiply]

def embGL (R : Type) [CommRing R] (n N : ℕ) (h : n + 1 = N) : GL (Fin n) R →* GL (Fin N) R :=
  Units.map (((Matrix.reindexAlgEquiv R R (finSumFinEquiv.trans (finCongr h))).toAlgHom.toRingHom.toMonoidHom).comp
    (blkHom R n))

def lastGL (R : Type) [CommRing R] (N : ℕ) (a : Rˣ) : GL (Fin N) R :=
  diagGL R N (fun i => if i.1 + 1 = N then a else 1)

def wsum {k : ℕ} (l : DomWeight k) : ℤ := ∑ i, l.w i

def Interlace {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, sg.w i ≤ lam.w ⟨i.1, by omega⟩ ∧ lam.w ⟨i.1 + 1, by omega⟩ ≤ sg.w i

def aa {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : ℤ :=
  sg.w i - lam.w ⟨i.1 + 1, by omega⟩

def bb {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : ℤ :=
  lam.w ⟨i.1, by omega⟩ - sg.w i

def D0 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, (sg.w i - lam.w ⟨i.1 + 1, by omega⟩)

def D1 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, min (lam.w ⟨i.1, by omega⟩ - lam.w ⟨i.1 + 1, by omega⟩) (D0 h lam sg)

def degZ {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n) : ℤ := wsum lam - wsum sg

def Rset {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam.w ⟨i.1 + 1, by omega⟩) (min (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg))

def cBr {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (Rset h lam sg i).erase (sg.w i), ∏ j : Fin n, ((v - (i.1 : ℤ)) - sg.w j + (j.1 : ℤ))

def rowsZ {n N : ℕ} (h : n + 1 = N) (i : Fin n) : Fin (i.1 + 1) → Fin N :=
  fun p => if p.1 = i.1 then ⟨N - 1, by omega⟩ else ⟨p.1, by omega⟩

def xi (R : Type) [CommRing R] {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) R :=
  ∏ i : Fin n, (Formalism.GradedWeylDivisibility.lpMinor R (i.1 + 1) (by omega) (by omega)) ^ (aa h lam sg i).toNat *
    (Formalism.GradedWeylDivisibility.initMinor R (rowsZ h i) (by omega)) ^ (bb h lam sg i).toNat

def cBd {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  (((2 * lam.spread : ℤ) : ℝ)) ^ ((((N : ℤ) * D1 h lam sg : ℤ) : ℝ))

def brBd {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  cBd h lam sg * Real.sqrt (Module.finrank ℂ (delSq ℂ N lam))

def IsIota {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  (∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
    io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f) ∧
  (∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
    io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s)) ∧
  io (extremal ℂ n sg) = ((cBr h lam sg : ℤ) : ℂ) • xi ℂ h lam sg ∧
  (∀ (a : ℂˣ), ∀ s ∈ nablaSq ℂ n sg,
    sqAct ℂ N lam (lastGL ℂ N a) (io s) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • io s) ∧
  (∀ s ∈ nablaSq ℂ n sg,
    (normFock lam (io s) (io s)).re ≤ brBd h lam sg ^ 2 * (normFock sg s s).re)

def IsBr {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  (∀ f ∈ delSq ℤ N lam, ∃ g ∈ delSq ℤ n sg,
    br (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g) ∧
  (∀ f ∈ delSq ℂ N lam, br f ∈ delSq ℂ n sg) ∧
  (∃ f ∈ delSq ℂ N lam, br f ≠ 0) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (embGL ℂ n N h g) f) = sqAct ℂ n sg g (br f)) ∧
  (∀ (a : ℂˣ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (lastGL ℂ N a) f) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • br f) ∧
  (∀ f ∈ delSq ℂ N lam,
    (normFock sg (br f) (br f)).re ≤ brBd h lam sg ^ 2 * (normFock lam f f).re)

def IsTranspose {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  ∀ s ∈ nablaSq ℂ n sg, ∀ f ∈ delSq ℂ N lam, normFock lam (io s) f = normFock sg s (br f)

def Branch {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Prop :=
  cBr h lam sg ≠ 0 ∧ |((cBr h lam sg : ℤ) : ℝ)| ≤ cBd h lam sg ∧ xi ℂ h lam sg ≠ 0 ∧
  degZ lam sg = lam.w ⟨0, by omega⟩ - D0 h lam sg ∧
  ∃ (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ),
    IsIota h lam sg io ∧ IsBr h lam sg br ∧ IsTranspose lam sg io br

def Conclusion6 : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg → Branch h lam sg

def BranchingTransposeMap : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∃ br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ, IsBr h lam sg br

theorem branchingTranspose_of_branching (H : Conclusion6) : BranchingTransposeMap := by
  intro n N h lam sg hI
  obtain ⟨-, -, -, -, io, br, -, hbr, -⟩ := H n N h lam sg hI
  exact ⟨br, hbr⟩

def StandardMonomialSpanAlt : Prop := Formalism.GradedWeylDivisibility.StandardMonomialSpan

def WeylDualLattice : Prop := Formalism.BasicNotions.FactDelDualNabla

def WeylModuleIrreducible : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), nablaSq ℂ N lam = delSq ℂ N lam ∧
    (∀ U : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ), U ≤ nablaSq ℂ N lam →
      (∀ (g : GL (Fin N) ℂ), ∀ f ∈ U, sqAct ℂ N lam g f ∈ U) → U = ⊥ ∨ U = nablaSq ℂ N lam) ∧
    ∀ f ∈ nablaSq ℂ N lam,
      (∀ g : GL (Fin N) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) → sqAct ℂ N lam g f = f) →
      ∃ c : ℂ, f = c • extremal ℂ N lam

def BranchingLawGL : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N),
    (∀ (mu : DomWeight n) (φ φ' : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
      (∀ ψ ∈ ({φ, φ'} : Set _), (∀ s ∈ nablaSq ℂ n mu, ψ s ∈ nablaSq ℂ N lam) ∧
        ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
          ψ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (ψ s)) →
      (∃ s ∈ nablaSq ℂ n mu, φ' s ≠ 0) →
      Interlace h lam mu ∧ ∃ c : ℂ, ∀ s ∈ nablaSq ℂ n mu, φ s = c • φ' s) ∧
    nablaSq ℂ N lam = ⨆ (mu : DomWeight n) (_ : Interlace h lam mu)
      (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
      (_ : (∀ s ∈ nablaSq ℂ n mu, φ s ∈ nablaSq ℂ N lam) ∧
        ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
          φ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (φ s)), (nablaSq ℂ n mu).map φ

def SchurOrthogonalityUnitary : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), ∀ s ∈ nablaSq ℂ N lam,
    (∀ x ∈ Matrix.unitaryGroup (Fin N) ℂ, ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) s‖ ≤ 1) →
    (normFock lam s s).re ≤ (Module.finrank ℂ (delSq ℂ N lam) : ℝ)

def Adm6 : Prop := StandardMonomialSpanAlt ∧ WeylDualLattice ∧ WeylModuleIrreducible ∧ BranchingLawGL ∧ SchurOrthogonalityUnitary

def ShareFromInputs : Prop := Adm6 → Conclusion6

def BranchingScaling : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ),
    IsIota h lam sg io → IsBr h lam sg br → ∀ a : ℂˣ,
    (∀ s ∈ nablaSq ℂ n sg,
      (normFock lam (sqAct ℂ N lam (lastGL ℂ N a⁻¹) (io s)) (sqAct ℂ N lam (lastGL ℂ N a⁻¹) (io s))).re ≤
        ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) * brBd h lam sg ^ 2 * (normFock sg s s).re) ∧
    (∀ f ∈ delSq ℂ N lam,
      (normFock sg (br f) (br f)).re ≤ ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) * brBd h lam sg ^ 2 *
        (normFock lam (sqAct ℂ N lam (lastGL ℂ N a) f) (sqAct ℂ N lam (lastGL ℂ N a) f)).re)

def PairwiseIndependentOrbitPoints : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (hn : 0 < n) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    lam.w ⟨1, by omega⟩ + D0 h lam sg ≤ lam.w ⟨0, by omega⟩ →
    |((cBr h lam sg : ℤ) : ℝ)| ≤
      (((2 * (sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩) + (N : ℤ) : ℤ) : ℝ)) ^ ((((n : ℤ) * D1 h lam sg : ℤ) : ℝ)) ∧
    ∀ lam' : DomWeight N, (∀ i : Fin N, i.1 ≠ 0 → lam'.w i = lam.w i) →
      lam'.w ⟨1, by omega⟩ + D0 h lam' sg ≤ lam'.w ⟨0, by omega⟩ →
      cBr h lam' sg = cBr h lam sg ∧ D1 h lam' sg = D1 h lam sg

section Abstract

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

def laG (G : Type) [Fintype G] : ℝ := Real.log (Fintype.card G : ℝ)

def IsGLat (A : HLat K) (ρ : Representation K G A.V) : Prop :=
  A.Good ∧ (∀ g, ∀ x ∈ A.L, ρ g x ∈ A.L) ∧
  ∀ g v x, Formalism.HermitianLatticesTheory.normAt A.b A.X v (ρ g x) = Formalism.HermitianLatticesTheory.normAt A.b A.X v x

structure GoodSet (K : Type) [Field K] (G : Type) [Group G] where
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  W : S → Type
  [acgW : ∀ s, AddCommGroup (W s)]
  [modW : ∀ s, Module K (W s)]
  [fdW : ∀ s, FiniteDimensional K (W s)]
  [ntW : ∀ s, Nontrivial (W s)]
  tau : ∀ s, Representation K G (W s)

  irr : ∀ s, Function.Surjective (tau s).asAlgebraHom

  inj : Function.Injective fun s g => LinearMap.trace K (W s) (tau s g)

attribute [instance] GoodSet.finS GoodSet.decS GoodSet.acgW GoodSet.modW GoodSet.fdW GoodSet.ntW

structure Pair (K : Type) [Field K] (G : Type) [Group G] where
  H : Subgroup G
  chi : H →* Kˣ

def eS (T : GoodSet K G) (s : T.S) : MonoidAlgebra K G :=
  ∑ x : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s x⁻¹)) • MonoidAlgebra.of K G x

def eG (T : GoodSet K G) : MonoidAlgebra K G := ∑ s, eS T s

open Classical in

def eps (P : Pair K G) : MonoidAlgebra K G :=
  ((Nat.card P.H : ℕ) : K)⁻¹ • ∑ x : G, if h : x ∈ P.H then
    (((P.chi ⟨x, h⟩)⁻¹ : Kˣ) : K) • MonoidAlgebra.of K G x else 0

def nS (T : GoodSet K G) (P : Pair K G) (s : T.S) : ℕ :=
  Module.finrank K (LinearMap.range ((T.tau s).asAlgebraHom (eps P)))

def M1 (T : GoodSet K G) (P0 : Pair K G) : Prop := ∀ s, nS T P0 s = 1

variable (A : HLat K) (ρ : Representation K G A.V)

def cutE (e : Module.End K A.V) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  M ⊓ (LinearMap.range e).restrictScalars (𝓞 K)

def imgE (e : Module.End K A.V) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  M.map (LinearMap.restrictScalars (𝓞 K) e)

def dimE (e : Module.End K A.V) : ℕ := Module.finrank K (LinearMap.range e)

def cut (a : MonoidAlgebra K G) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  cutE A (ρ.asAlgebraHom a) M

def img (a : MonoidAlgebra K G) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  imgE A (ρ.asAlgebraHom a) M

def dimOf (a : MonoidAlgebra K G) : ℕ := dimE A (ρ.asAlgebraHom a)

def rkL (M : Submodule (𝓞 K) A.V) : ℕ := Formalism.HN.rkK M

def degL (M : Submodule (𝓞 K) A.V) : ℝ := (Formalism.HN.rkK M : ℝ) * Formalism.HN.muDef A.b A.X M

def muMaxL (M : Submodule (𝓞 K) A.V) : ℝ := Formalism.HN.muMaxDef A.b A.X M

def lenAt {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    (M N : Submodule (𝓞 K) V) : ℕ∞ :=
  letI : w.asIdeal.IsPrime := w.isPrime
  Module.length (Localization.AtPrime w.asIdeal)
    (LocalizedModule w.asIdeal.primeCompl (↥M ⧸ N.comap M.subtype))

def idxAt {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    (M N : Submodule (𝓞 K) V) : ℤ :=
  ((lenAt w M N).toNat : ℤ) - ((lenAt w N M).toNat : ℤ)

def LocLe {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K)) (F : ℕ)
    (M N : Submodule (𝓞 K) V) : Prop :=
  ∀ x ∈ M, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ (w.asIdeal ^ F) • N

def vCard (G : Type) [Fintype G] (w : HeightOneSpectrum (𝓞 K)) : ℤ := vAdd w ((Fintype.card G : ℕ) : K)

def IsFull (M : Submodule (𝓞 K) A.V) : Prop := M.FG ∧ Submodule.span K (M : Set A.V) = ⊤

def IsProj (e : Module.End K A.V) (n : ℕ) : Prop :=
  A.Good ∧ 0 < n ∧ e * e = e ∧ (∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • e x ∈ A.L) ∧
  ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) y = Formalism.HermitianLatticesTheory.majAt A.b A.X v x (e y)

end Abstract

section Lemma2

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def ProjectionSandwichLength (A : HLat K) (e : Module.End K A.V) (n : ℕ) : Prop :=
  (∀ x ∈ imgE A e A.L, ((n : ℕ) : 𝓞 K) • x ∈ cutE A e A.L) ∧
  cutE A e A.L ≤ imgE A e A.L ∧
  Nonempty ((↥(imgE A e A.L) ⧸ (cutE A e A.L).comap (imgE A e A.L).subtype) ≃ₗ[𝓞 K]
    (↥(imgE A (1 - e) A.L) ⧸ (cutE A (1 - e) A.L).comap (imgE A (1 - e) A.L).subtype)) ∧
  (∀ w : HeightOneSpectrum (𝓞 K),
    idxAt w (imgE A e A.L) (cutE A e A.L) = idxAt w (imgE A (1 - e) A.L) (cutE A (1 - e) A.L) ∧
    0 ≤ idxAt w (imgE A e A.L) (cutE A e A.L) ∧
    idxAt w (imgE A e A.L) (cutE A e A.L) ≤
      (min (dimE A e) (dimE A (1 - e)) : ℕ) * vAdd w ((n : ℕ) : K)) ∧
  (∀ ψ : Module.Dual K A.V, ψ ∘ₗ e = ψ →
    (ψ ∈ Formalism.HN.dualLat (cutE A e A.L) ↔ ∃ φ ∈ A.dualL, ψ = φ ∘ₗ e))

def DegreeKernelLowerBound (A : HLat K) (e : Module.End K A.V) (n : ℕ) : Prop :=
  degL A A.L - (dimE A (1 - e) : ℝ) * (muMaxL A A.L + 2 * Real.log (n : ℝ)) ≤ degL A (cutE A e A.L)

def KernelIndexFullLattice (A : HLat K) (e : Module.End K A.V) : Prop :=
  ∀ Th : Submodule (𝓞 K) A.V, IsFull A Th →
    (∀ (w : HeightOneSpectrum (𝓞 K)) (F : ℕ), LocLe w F Th A.L →
      idxAt w (cutE A e A.L) (cutE A e Th) ≤ idxAt w A.L Th - (F : ℤ) * (dimE A (1 - e) : ℤ)) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (F : ℕ), LocLe w 0 ((w.asIdeal ^ F) • Th) A.L →
      idxAt w (cutE A e A.L) (cutE A e Th) ≤ idxAt w A.L Th + (F : ℤ) * (dimE A (1 - e) : ℤ)) ∧
    cutE A e Th ≤ imgE A e Th

def projection_sandwich_lattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V),
    IsGLat A ρ → ProjectionSandwichLength A (ρ.asAlgebraHom (eG T)) (Fintype.card G)

def MassRatio₂ : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V),
    IsGLat A ρ → DegreeKernelLowerBound A (ρ.asAlgebraHom (eG T)) (Fintype.card G)

def kernel_index_full_lattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V),
    IsGLat A ρ → KernelIndexFullLattice A (ρ.asAlgebraHom (eG T))

def projection_lemma_base_level : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ), IsProj A e n → ProjectionSandwichLength A e n ∧ DegreeKernelLowerBound A e n ∧ KernelIndexFullLattice A e

end Lemma2

section Lemma4

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

def rS (T : GoodSet K G) (P0 : Pair K G) (A : HLat K) (ρ : Representation K G A.V) (s : T.S) : ℕ :=
  rkL A (cut A ρ (eps P0 * eS T s) A.L)

def rkT (T : GoodSet K G) (P0 P : Pair K G) (A : HLat K) (ρ : Representation K G A.V) : ℕ :=
  ∑ s, nS T P s * rS T P0 A ρ s

def delRk (T : GoodSet K G) (P0 P : Pair K G) (A : HLat K) (ρ : Representation K G A.V)
    (Gam : ∀ s : T.S, Matrix (Fin (nS T P s)) (Fin (nS T P s)) (𝓞 K)) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ s, ((nS T P s * rS T P0 A ρ s : ℕ) : ℝ) *
    ((vAdd w (algebraMap (𝓞 K) K (Gam s).det) : ℝ) / (nS T P s : ℝ) + (vCard (K := K) G w : ℝ))

def Conclusion4a : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      rkL A (cut A ρ (eps P * eG T) A.L) = rkT T P0 P A ρ ∧
      |degL A (cut A ρ (eps P * eG T) A.L) -
          ∑ s, (nS T P s : ℝ) * degL A (cut A ρ (eps P0 * eS T s) A.L)| ≤
        10 * laG G * (rkT T P0 P A ρ : ℝ) ∧
      (0 < rkT T P0 P A ρ →
        muMaxL A (cut A ρ (eps P * eG T) A.L) ≤ muMaxL A (cut A ρ (eps P0 * eG T) A.L) + 10 * laG G)

def Conclusion4b (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∃ Gam : ∀ s : T.S, Matrix (Fin (nS T P s)) (Fin (nS T P s)) (𝓞 K), (∀ s, (Gam s).det ≠ 0) ∧
      ∀ (A : HLat K) (ρ : Representation K G A.V) (B : Submodule (𝓞 K) A.V),
        IsGLat A ρ → IsGLat (K := K) (G := G) { A with L := B } ρ →
        (∀ w, 0 ≤ delRk T P0 P A ρ Gam w ∧
          |(idxAt w (cut A ρ (eps P * eG T) A.L) (cut A ρ (eps P * eG T) B) : ℝ) -
            ∑ s, (nS T P s : ℝ) *
              (idxAt w (cut A ρ (eps P0 * eS T s) A.L) (cut A ρ (eps P0 * eS T s) B) : ℝ)| ≤
            C * delRk T P0 P A ρ Gam w) ∧
        ∑ᶠ w, lw K w * delRk T P0 P A ρ Gam w ≤ 8 * laG G * (rkT T P0 P A ρ : ℝ)

def Conclusion4 (C : ℝ) : Prop := Conclusion4a ∧ Conclusion4b C

end Lemma4

section Lemma8

def eigP {K : Type} [Field K] (σ : K →+* ℂ) {G : Type} [Group G] (P : Pair K G)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : Submodule ℂ V :=
  ⨅ h : P.H, LinearMap.ker (ρ (h : G) - (σ ((P.chi h : Kˣ) : K)) • LinearMap.id)

structure GMap (K : Type) [Field K] (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (T : GoodSet K G)
    (EE : Type) [AddCommGroup EE] [Module ℂ EE] (ρE : Representation ℂ G EE) where
  VK : Type
  [acgK : AddCommGroup VK]
  [modK : Module K VK]
  [fdK : FiniteDimensional K VK]
  rhoK : Representation K G VK
  V : Type
  [acgV : AddCommGroup V]
  [modV : Module ℂ V]
  rho : Representation ℂ G V

  j : VK →ₛₗ[σ] V
  j_indep : ∀ (n : ℕ) (b : Fin n → VK), LinearIndependent K b → LinearIndependent ℂ (fun i => j (b i))
  j_span : Submodule.span ℂ (Set.range j) = ⊤
  j_eq : ∀ g x, j (rhoK g x) = rho g (j x)

  good : rhoK.asAlgebraHom (eG T) = 1
  io : V →ₗ[ℂ] EE
  io_eq : ∀ g x, io (rho g x) = ρE g (io x)

attribute [instance] GMap.acgK GMap.modK GMap.fdK GMap.acgV GMap.modV

namespace GMap

variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE} (M : GMap K σ G T EE ρE)

def IsRat (U : Submodule ℂ M.V) : Prop := Submodule.span ℂ (M.j '' {x | M.j x ∈ U}) = U

def form (a : MonoidAlgebra K G) : Set EE := Set.range fun x : M.VK => M.io (M.j (M.rhoK.asAlgebraHom a x))

end GMap

def Conclusion8 : Prop :=
  ∀ (K : Type) [Field K] (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 : Pair K G),
    M1 T P0 → ∀ (EE : Type) [AddCommGroup EE] [Module ℂ EE] (ρE : Representation ℂ G EE)
      (M : GMap K σ G T EE ρE),
      M.IsRat (LinearMap.ker M.io ⊓ eigP σ P0 M.rho) →
      M.IsRat (LinearMap.ker M.io) ∧
      M.form 1 = (AddSubgroup.closure {z | ∃ g, ∃ y ∈ M.form (eps P0), z = ρE g y} : Set EE)

def SameFormAllLevels : Prop :=
  ∀ (K : Type) [Field K] (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 : Pair K G),
    M1 T P0 → ∀ (EE : Type) [AddCommGroup EE] [Module ℂ EE] (ρE : Representation ℂ G EE)
      (M M' : GMap K σ G T EE ρE), M.form (eps P0) = M'.form (eps P0) →
      M.form 1 = M'.form 1 ∧ ∀ P : Pair K G, M.form (eps P) = M'.form (eps P)

end Lemma8

namespace Ten

section Tensor

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

def tens (a : ∀ i, MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => ∏ i, (a i).coeff (g i))

theorem tens_coeff (a : ∀ i, MonoidAlgebra ℂ (G i)) (g : ∀ i, G i) :
    (tens a).coeff g = ∏ i, (a i).coeff (g i) := rfl

theorem conv_coeff {H : Type} [Group H] [Fintype H] (x y : MonoidAlgebra ℂ H) (g : H) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro i; simp

theorem tens_mul (a b : ∀ i, MonoidAlgebra ℂ (G i)) :
    tens a * tens b = tens (fun i => a i * b i) := by
  classical
  have : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
  ext g
  rw [conv_coeff, tens_coeff]
  simp only [tens_coeff, conv_coeff]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem tens_one : tens (fun i => (1 : MonoidAlgebra ℂ (G i))) = 1 := by
  classical
  ext g
  rw [tens_coeff]
  simp only [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.prod_boole]
  simp [funext_iff, eq_comm]

theorem sum_tens {P : ι → Type} [∀ i, Fintype (P i)] [DecidableEq ι]
    (E : ∀ i, P i → MonoidAlgebra ℂ (G i)) :
    ∑ p : ∀ i, P i, tens (fun i => E i (p i)) = tens (fun i => ∑ q, E i q) := by
  ext g
  rw [tens_coeff, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [tens_coeff, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

variable [DecidableEq ι]

def plc (i : ι) (a : MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  tens (Function.update (fun _ => 1) i a)

theorem tens_mul_plc (a : ∀ i, MonoidAlgebra ℂ (G i)) (i : ι) (b : MonoidAlgebra ℂ (G i)) :
    tens a * plc i b = tens (Function.update a i (a i * b)) := by
  rw [plc, tens_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem mapDomain_mulSingle (i : ι) (a : MonoidAlgebra ℂ (G i)) :
    MonoidAlgebra.ofCoeff (Finsupp.mapDomain (fun h => Pi.mulSingle (M := G) i h) a.coeff) = plc i a := by
  classical
  ext g
  rw [MonoidAlgebra.coeff_ofCoeff, plc, tens_coeff, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hinj : Function.Injective (fun h : G i => Pi.mulSingle (M := G) i h) := Pi.mulSingle_injective i
  have hrest : ∏ j ∈ Finset.univ.erase i,
      (Function.update (fun j => (1 : MonoidAlgebra ℂ (G j))) i a j).coeff (g j) =
      if ∀ j ∈ Finset.univ.erase i, g j = 1 then 1 else 0 := by
    trans ∏ j ∈ Finset.univ.erase i, (if g j = 1 then (1 : ℂ) else 0)
    · refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), MonoidAlgebra.one_def,
        MonoidAlgebra.coeff_single, Finsupp.single_apply]
      simp [eq_comm]
    · rw [Finset.prod_boole]; congr
  rw [hrest, Function.update_self]
  by_cases hg : ∀ j ∈ Finset.univ.erase i, g j = 1
  · have : g = Pi.mulSingle i (g i) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Pi.mulSingle_eq_of_ne hj]; exact hg j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)
    rw [if_pos hg, mul_one]
    conv_lhs => rw [this]
    exact Finsupp.mapDomain_apply hinj _ _
  · rw [if_neg hg, mul_zero]
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨h, rfl⟩
    exact hg fun j hj => Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hj) _

variable {P : ι → Type} [∀ i, Fintype (P i)]

open Classical in

def eGood (E : ∀ i, P i → MonoidAlgebra ℂ (G i)) (good : (∀ i, P i) → Prop) :
    MonoidAlgebra ℂ (∀ i, G i) :=
  ∑ p : ∀ i, P i, if good p then tens (fun i => E i (p i)) else 0

theorem alg_eGood {W : Type} [AddCommGroup W] [Module ℂ W] (E : ∀ i, P i → MonoidAlgebra ℂ (G i))
    (good : (∀ i, P i) → Prop) (hid : ∀ i p, E i p * E i p = E i p) (hsum : ∀ i, ∑ p, E i p = 1)
    (Φ : MonoidAlgebra ℂ (∀ i, G i) →ₐ[ℂ] Module.End ℂ W) (F : W) (lab : ∀ i, P i)
    (h : ∀ i p, p ≠ lab i → Φ (plc i (E i p)) F = 0) (hg : good lab) : Φ (eGood E good) F = F := by
  classical
  have hne : ∀ p : ∀ i, P i, p ≠ lab → Φ (tens (fun i => E i (p i))) F = 0 := by
    intro p hp
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hp
    have hmul : tens (fun i => E i (p i)) = tens (fun i => E i (p i)) * plc i (E i (p i)) := by
      rw [tens_mul_plc, hid, Function.update_eq_self]
    rw [hmul, map_mul, Module.End.mul_apply, h i (p i) hi, map_zero]
  have hone : ∑ p : ∀ i, P i, tens (fun i => E i (p i)) = 1 := by
    rw [sum_tens]
    simp only [hsum]
    exact tens_one
  have hlab : Φ (tens (fun i => E i (lab i))) F = F := by
    have h1 : Φ (∑ p : ∀ i, P i, tens (fun i => E i (p i))) F = F := by rw [hone, map_one]; rfl
    rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single lab (fun p _ hp => hne p hp)
      (fun hh => absurd (Finset.mem_univ _) hh)] at h1
    exact h1
  rw [eGood, map_sum, LinearMap.sum_apply, Finset.sum_eq_single lab]
  · rw [if_pos hg]; exact hlab
  · intro p _ hp
    split_ifs
    · exact hne p hp
    · simp
  · intro hh; exact absurd (Finset.mem_univ _) hh

end Tensor

end Ten

section Record

open NumberField IsDedekindDomain

@[instance_reducible] def finiteLevelGroupFintype (D : D7) : Fintype (G0g D.nd) := by
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Finite (G0g D.nd) := inferInstance
  exact Fintype.ofFinite _

attribute [local instance] finiteLevelGroupFintype

structure GSp (D : D7) where
  V : Type
  [nacg : NormedAddCommGroup V]
  [ips : InnerProductSpace ℂ V]
  [fd : FiniteDimensional ℂ V]
  lat : Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) V
  act : Representation ℂ (G0g D.nd) V

attribute [instance] GSp.nacg GSp.ips GSp.fd

def GSp.IsGMod {D : D7} (S : GSp D) : Prop :=
  (∀ g x, ‖S.act g x‖ = ‖x‖) ∧ ∀ g, ∀ x ∈ S.lat.carrier, S.act g x ∈ S.lat.carrier

structure Prov (D : D7) (X : BaseLevelRowSide D) where

  T : GoodSet D.what₂.LL (G0g D.nd)

  T_e : ∀ g, (eG T).coeff g = ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL)

  psi0 : D.nexp.U →* (D.what₂.LL)ˣ

  Ps : Pair D.what₂.LL (G0g D.nd)

  EEK : Type
  [nacgEE : NormedAddCommGroup EEK]
  [ipsEE : InnerProductSpace ℂ EEK]
  [fdEE : FiniteDimensional ℂ EEK]

  sK : RowSide D EEK

  actEE : Representation ℂ (G0g D.nd) EEK

  actAmb : ∀ μ, Representation ℂ (G0g D.nd) (sK.Amb μ)

  cen_tie : ∀ μ z, sK.cen μ z = (actAmb μ).asAlgebraHom (z : MonoidAlgebra ℂ (G0g D.nd))

  MtK : D.what₂.Tup → ℕ → GSp D

  MjK : ℕ → GSp D

  thK : ∀ μ j, (MtK μ j).V →ₗ[ℂ] (MjK j).V

  rho : Representation D.what₂.LL (G0g D.nd) sK.RR.V

  j0 : X.principalHermitianLattice.V →ₗ[D.what₂.LL] sK.RR.V

  js : D.div.RR.V →ₗ[D.what₂.LL] sK.RR.V

attribute [instance] Prov.nacgEE Prov.ipsEE Prov.fdEE

variable {D : D7} {X : BaseLevelRowSide D}

def Prov.RK (Y : Prov D X) : HLat D.what₂.LL := Y.sK.RR

def Prov.P0 (Y : Prov D X) : Pair D.what₂.LL (G0g D.nd) := ⟨D.nexp.U, Y.psi0⟩

theorem card_tie (D : D7) : D.what₂.restRowsFiniteGroupCard = Fintype.card (G0g D.nd) := by
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  rw [D.nd.restN_card_levelGroup_eq, ← Nat.card_eq_fintype_card, Nat.card_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  change _ = ∏ _y : D.nd.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
  rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG k]

def Conclusion0 (D : D7) : Prop :=
  ∀ Y : ℝ, (∀ i, (D.host.g i : ℝ) ≤ 2 * Y) → lam0 D ≤ 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log (2 * Y)

def Conclusion1 (Y : Prov D X) : Prop :=
  (∀ g x, ‖Y.actEE g x‖ = ‖x‖) ∧
  (∀ μ, (∀ g x, ‖Y.actAmb μ g x‖ = ‖x‖) ∧
    ∀ g, ∀ x ∈ (Y.sK.Mtilde μ).carrier, Y.actAmb μ g x ∈ (Y.sK.Mtilde μ).carrier) ∧
  (∀ μ, ∀ j ∈ Finset.Icc 1 D.R.m, (Y.MtK μ j).IsGMod) ∧
  (∀ j ∈ Finset.Icc 1 D.R.m, (Y.MjK j).IsGMod) ∧
  (∀ μ g x, Y.sK.iota μ (Y.actAmb μ g x) = Y.actEE g (Y.sK.iota μ x)) ∧
  (∀ μ g x, Y.sK.thetaUp μ (Y.actEE g x) = Y.actAmb μ g (Y.sK.thetaUp μ x)) ∧
  (∀ μ, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ g x,
    Y.thK μ j ((Y.MtK μ j).act g x) = (Y.MjK j).act g (Y.thK μ j x)) ∧
  (∀ μ, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ g x,
    LinearMap.adjoint (Y.thK μ j) ((Y.MjK j).act g x) = (Y.MtK μ j).act g (LinearMap.adjoint (Y.thK μ j) x))

def ExponentBlockSplitting (Y : Prov D X) : Prop := Y.actEE.asAlgebraHom D.ntypes.e0 = 1

def ErrorFirstTermSize (D : D7) : Prop :=
  (∀ μ j, 1 ≤ j → j ≤ D.R.m →
    ∀ (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k) (f : Polynomial (ZMod (D.host.g k))),
    ∀ F ∈ D.ntypes.MtPar μ j σ',
      D.ntypes.onMt μ j (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F ≠ 0 → f = D.ntypes.labPar k σ' v) ∧
  (∀ μ (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k) (f : Polynomial (ZMod (D.host.g k))),
    ∀ F ∈ D.ntypes.AmbPar μ σ',
      D.ntypes.onAmb μ (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F ≠ 0 →
        f = Formalism.MainNotions.ArithmeticCylinders.dualLab D k (D.ntypes.labPar k σ' v))

theorem secondSentence_iff (D : D7) : Formalism.MainNotions.ArithmeticCylinders.adm3 D ↔
    (∀ (τ : ℂ ≃+* ℂ) (k : Fin 2) (f : Polynomial (ZMod (D.host.g k))), Formalism.MainNotions.ArithmeticCylinders.IsLabel D k f →
      (D.ntypes.eSer k f).coeff.mapRange τ (map_zero τ) =
        (D.ntypes.eSer k (Formalism.MainNotions.ArithmeticCylinders.labAct D τ k f)).coeff) ∧ ErrorFirstTermSize D := by
  exact Iff.rfl

def SerSupp (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V]
    (on : MonoidAlgebra ℂ (G0g D.nd) → Module.End ℂ V) (par : D.ntypes.Par → Submodule ℂ V)
    (lab : D.ntypes.Par → ∀ k : Fin 2, D.nd.PlG k → Polynomial (ZMod (D.host.g k))) (d : ℕ) : Prop :=
  ∃ (Pi : Type) (sp : Pi → Submodule ℂ V)
    (sup : Pi → ∀ k : Fin 2, D.nd.PlG k → Polynomial (ZMod (D.host.g k)))
    (blk : ∀ k : Fin 2, D.nd.PlG k → Polynomial (ZMod (D.host.g k))),
    (∀ k v, (blk k v).Monic ∧ (blk k v).natDegree = d) ∧
    (∀ σ', par σ' ≤ ⨆ P ∈ {P | ∀ k v, sup P k v = lab σ' k v * blk k v}, sp P) ∧
    ∀ P k v (f : Polynomial (ZMod (D.host.g k))),
      (∃ F ∈ sp P, on (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F ≠ 0) → sup P k v = f * blk k v

def SecondSentenceInputs (D : D7) : Prop :=
  (∀ μ j, 1 ≤ j → j ≤ D.R.m →
    SerSupp D (D.ntypes.onMt μ j) (D.ntypes.MtPar μ j) (fun σ' k v => D.ntypes.labPar k σ' v) D.R.t) ∧
  ∀ μ, SerSupp D (D.ntypes.onAmb μ) (D.ntypes.AmbPar μ)
    (fun σ' k v => Formalism.MainNotions.ArithmeticCylinders.dualLab D k (D.ntypes.labPar k σ' v)) (D.R.m * D.R.t)

theorem serSupp_cancel (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V]
    (on : MonoidAlgebra ℂ (G0g D.nd) → Module.End ℂ V) (par : D.ntypes.Par → Submodule ℂ V)
    (lab : D.ntypes.Par → ∀ k : Fin 2, D.nd.PlG k → Polynomial (ZMod (D.host.g k))) (d : ℕ)
    (h : SerSupp D on par lab d) (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k)
    (f : Polynomial (ZMod (D.host.g k))) (F : V) (hF : F ∈ par σ')
    (hne : on (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F ≠ 0) : f = lab σ' k v := by
  obtain ⟨Pi, sp, sup, blk, hblk, hpar, hsup⟩ := h
  have key : ∃ P, (∀ k v, sup P k v = lab σ' k v * blk k v) ∧
      ∃ F' ∈ sp P, on (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F' ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    have hle : (⨆ P ∈ {P | ∀ k v, sup P k v = lab σ' k v * blk k v}, sp P) ≤
        LinearMap.ker (on (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f))) := by
      refine iSup₂_le fun P hP => ?_
      intro y hy
      exact LinearMap.mem_ker.mpr (hcon P hP y hy)
    exact LinearMap.mem_ker.mp (hle (hpar σ' hF))
  obtain ⟨P, hP, hex⟩ := key
  have h1 := hsup P k v f hex
  rw [hP k v] at h1
  have h2 : blk k v * (f - lab σ' k v) = 0 := by
    rw [mul_sub, mul_comm (blk k v) f, mul_comm (blk k v) (lab σ' k v), h1, sub_self]
  exact sub_eq_zero.mp ((hblk k v).1.mul_right_eq_zero_iff.mp h2)

theorem secondSentenceLemmaOne_of (D : D7) (h : SecondSentenceInputs D) : ErrorFirstTermSize D := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun μ j hj1 hj2 σ' k v f F hF hne => serSupp_cancel D _ _ _ _ (h1 μ j hj1 hj2) σ' k v f F hF hne,
    fun μ σ' k v f F hF hne => serSupp_cancel D _ _ _ _ (h2 μ) σ' k v f F hF hne⟩

def ThetaUpInV0Side {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) : Prop := ∀ μ, LinearMap.range (S.thetaUp μ) ≤ S.V0 μ

def ThetaUpInV0 (D : D7) : Prop := ∀ μ, LinearMap.range (D.what₂.thetaUp μ) ≤ D.what₂.V0 μ

def ThetaUpInV0Small (X : BaseLevelRowSide D) : Prop := ThetaUpInV0Side X.s

theorem thetaUpInV0_level_of (Y : Prov D X) (hc : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))
    (h1 : Conclusion1 Y) (he : ExponentBlockSplitting Y) : ThetaUpInV0Side Y.sK := by
  intro μ y hy
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
  obtain ⟨-, -, -, -, -, hth, -⟩ := h1
  have he' : Y.actEE.asAlgebraHom D.ntypes.e0 = 1 := he
  have hcomm : ∀ (a : MonoidAlgebra ℂ (G0g D.nd)) (v : Y.EEK),
      Y.sK.thetaUp μ (Y.actEE.asAlgebraHom a v) = (Y.actAmb μ).asAlgebraHom a (Y.sK.thetaUp μ v) := by
    intro a
    refine MonoidAlgebra.induction_on (motive := fun a => ∀ v : Y.EEK,
      Y.sK.thetaUp μ (Y.actEE.asAlgebraHom a v) = (Y.actAmb μ).asAlgebraHom a (Y.sK.thetaUp μ v)) a ?_ ?_ ?_
    · intro m v
      rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of]
      exact hth μ m v
    · intro a b ha hb v
      have ha' := ha v
      have hb' := hb v
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha', hb']
    · intro r a ha v
      have ha' := ha v
      rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.map_smul, ha']
  have hx := hcomm D.ntypes.e0 x
  rw [he', Module.End.one_apply] at hx
  show Y.sK.thetaUp μ x ∈ LinearMap.range (Y.sK.eOp μ)
  refine LinearMap.mem_range.mpr ⟨Y.sK.thetaUp μ x, ?_⟩
  rw [Y.sK.eOp_tie μ, dif_pos hc, Y.cen_tie μ]
  exact hx.symm

def IdempotentCentral (D : D7) : Prop := D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))

theorem coeff_conj {G : Type} [Group G] (x : MonoidAlgebra ℂ G)
    (hx : ∀ a, x * a = a * x) (h g : G) : x.coeff (h * g * h⁻¹) = x.coeff g := by
  have h1 : (x * MonoidAlgebra.single h 1).coeff (h * g) = (MonoidAlgebra.single h 1 * x).coeff (h * g) := by
    rw [hx]
  rw [MonoidAlgebra.coeff_mul_single_eq_coeff_mul (m₂ := h * g * h⁻¹) (by intro m' _; constructor <;> intro e <;> [rw [← e]; rw [e]] <;> group),
    MonoidAlgebra.coeff_single_mul_eq_mul_coeff (m₂ := g) (by intro m' _; constructor <;> intro e <;> [exact mul_left_cancel e; rw [e]])] at h1
  simpa using h1

theorem central_of_class {G : Type} [Group G] (x : MonoidAlgebra ℂ G)
    (hc : ∀ h g : G, x.coeff (h * g * h⁻¹) = x.coeff g) : ∀ b, b * x = x * b := by
  have hs : ∀ h : G, MonoidAlgebra.single h (1 : ℂ) * x = x * MonoidAlgebra.single h 1 := by
    intro h
    ext m
    rw [MonoidAlgebra.coeff_mul_single_eq_coeff_mul (m₂ := m * h⁻¹) (by intro m' _; constructor <;> intro e <;> [rw [← e]; rw [e]] <;> group),
      MonoidAlgebra.coeff_single_mul_eq_mul_coeff (m₂ := h⁻¹ * m) (by intro m' _; constructor <;> intro e <;> [rw [← e]; rw [e]] <;> group)]
    have := hc h (h⁻¹ * m)
    simp only [one_mul, mul_one]
    rw [← this]; congr 1; group
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of g => simpa [MonoidAlgebra.of_apply] using hs g
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]
  | smul c a ha => rw [smul_mul_assoc, mul_smul_comm, ha]

theorem idempotentCentral_holds (D : D7) : IdempotentCentral D := by
  unfold IdempotentCentral
  rw [Subalgebra.mem_center_iff]
  refine central_of_class _ fun h g => ?_
  simp only [NTypes.e0, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
  refine finsum_congr fun a => ?_
  split_ifs
  · refine Finset.prod_congr rfl fun kv _ => ?_
    exact coeff_conj _ (fun c => D.ntypes.eSer_central _ _ c) (h kv) (g kv)
  · rfl

def IsometricActionCond (Y : Prov D X) : Prop :=
  (∀ g x, ‖Y.actEE g x‖ = ‖x‖) ∧
  (∀ μ, (∀ g x, ‖Y.actAmb μ g x‖ = ‖x‖) ∧
    ∀ g, ∀ x ∈ (Y.sK.Mtilde μ).carrier, Y.actAmb μ g x ∈ (Y.sK.Mtilde μ).carrier) ∧
  (∀ μ, ∀ j ∈ Finset.Icc 1 D.R.m, (Y.MtK μ j).IsGMod) ∧
  (∀ j ∈ Finset.Icc 1 D.R.m, (Y.MjK j).IsGMod)

def MultiplicityEquivariance (Y : Prov D X) : Prop :=
  ∃ act : ∀ μ j, Representation ℂ (G0g D.nd) (Y.sK.Mult μ j),
    (∀ μ j, j < D.R.m → ∀ g x, Y.sK.io μ j (act μ (j + 1) g x) = act μ j g (Y.sK.io μ j x)) ∧
    (∀ μ g x, Y.sK.multZero μ (act μ 0 g x) = Y.actEE g (Y.sK.multZero μ x)) ∧
    (∀ μ g x, Y.sK.multTop μ (act μ D.R.m g x) = Y.actAmb μ g (Y.sK.multTop μ x))

def ThetaEquivarianceCond (Y : Prov D X) : Prop :=
  ∀ μ, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ g x, Y.thK μ j ((Y.MtK μ j).act g x) = (Y.MjK j).act g (Y.thK μ j x)

def IdempotentGoodTypeCond (Y : Prov D X) : Prop :=
  ∃ (Pi : Type) (sp : Pi → Submodule ℂ Y.EEK)
    (sup : Pi → ∀ k : Fin 2, D.nd.PlG k → Polynomial (ZMod (D.host.g k))),
    (⨆ P ∈ {P | D.ntypes.goodTuple (sup P)}, sp P) = ⊤ ∧
    ∀ P k v (f : Polynomial (ZMod (D.host.g k))),
      (∃ F ∈ sp P, Y.actEE.asAlgebraHom (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F ≠ 0) → sup P k v = f

theorem comm_alg {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (G0g D.nd) V) (σ : Representation ℂ (G0g D.nd) W) (T : V →ₗ[ℂ] W)
    (h : ∀ g x, T (ρ g x) = σ g (T x)) (a : MonoidAlgebra ℂ (G0g D.nd)) :
    ∀ x, T (ρ.asAlgebraHom a x) = σ.asAlgebraHom a (T x) := by
  refine MonoidAlgebra.induction_on
    (motive := fun a => ∀ x, T (ρ.asAlgebraHom a x) = σ.asAlgebraHom a (T x)) a ?_ ?_ ?_
  · intro m x
    rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of]
    exact h m x
  · intro a b ha hb x
    have ha' := ha x
    have hb' := hb x
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha', hb']
  · intro r a ha x
    have ha' := ha x
    rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.map_smul, ha']

theorem adj_equiv {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (G0g D.nd) V) (σ : Representation ℂ (G0g D.nd) W)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖) (T : V →ₗ[ℂ] W)
    (h : ∀ g x, T (ρ g x) = σ g (T x)) (g : G0g D.nd) (y : W) :
    LinearMap.adjoint T (σ g y) = ρ g (LinearMap.adjoint T y) := by
  have hρi := (LinearMap.norm_map_iff_inner_map_map (ρ g)).1 (hρ g)
  have hσi := (LinearMap.norm_map_iff_inner_map_map (σ g)).1 (hσ g)
  apply ext_inner_left ℂ
  intro x
  have hρinv : ρ g (ρ g⁻¹ x) = x := by
    show (ρ g * ρ g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hσinv : σ g (σ g⁻¹ (T x)) = T x := by
    show (σ g * σ g⁻¹) (T x) = T x
    rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [LinearMap.adjoint_inner_right]
  conv_lhs => rw [← hσinv]
  conv_rhs => rw [← hρinv]
  rw [hσi, hρi, LinearMap.adjoint_inner_right, h]

theorem iota_equiv (Y : Prov D X) (hB : MultiplicityEquivariance Y) (μ : D.what₂.Tup) (g : G0g D.nd) (x : Y.sK.Amb μ) :
    Y.sK.iota μ (Y.actAmb μ g x) = Y.actEE g (Y.sK.iota μ x) := by
  obtain ⟨act, hio, h0, hm⟩ := hB
  have hd : ∀ j, j ≤ D.R.m → ∀ (g : G0g D.nd) (y : Y.sK.Mult μ j),
      Y.sK.downTo μ j (act μ j g y) = act μ 0 g (Y.sK.downTo μ j y) := by
    intro j
    induction j with
    | zero =>
      intro _ g y
      rfl
    | succ j ih =>
      intro hj g y
      show Y.sK.downTo μ j (Y.sK.io μ j (act μ (j + 1) g y)) =
        act μ 0 g (Y.sK.downTo μ j (Y.sK.io μ j y))
      rw [hio μ j (by omega) g y, ih (by omega) g]
  have ht : (Y.sK.multTop μ).symm (Y.actAmb μ g x) = act μ D.R.m g ((Y.sK.multTop μ).symm x) := by
    apply (Y.sK.multTop μ).injective
    rw [LinearIsometryEquiv.apply_symm_apply, hm μ g, LinearIsometryEquiv.apply_symm_apply]
  show Y.sK.multZero μ (Y.sK.downTo μ D.R.m ((Y.sK.multTop μ).symm (Y.actAmb μ g x))) =
    Y.actEE g (Y.sK.multZero μ (Y.sK.downTo μ D.R.m ((Y.sK.multTop μ).symm x)))
  rw [ht, hd D.R.m le_rfl g, h0 μ g]

theorem baseChange_preserves_unitary_of (Y : Prov D X) (hA : IsometricActionCond Y) (hB : MultiplicityEquivariance Y) (hth : ThetaEquivarianceCond Y) : Conclusion1 Y := by
  obtain ⟨hE, hAmb, hMt, hMj⟩ := hA
  refine ⟨hE, hAmb, hMt, hMj, fun μ g x => iota_equiv Y hB μ g x, fun μ g x => ?_, hth, fun μ j hj g x => ?_⟩
  · exact adj_equiv (Y.actAmb μ) Y.actEE (hAmb μ).1 hE (Y.sK.iota μ) (iota_equiv Y hB μ) g x
  · exact adj_equiv (Y.MtK μ j).act (Y.MjK j).act (hMt μ j hj).1 (hMj j hj).1 (Y.thK μ j) (hth μ j hj) g x

section GoodType

local instance factG (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

namespace Ten

def ESer (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k) (p : Fin D.R.r → ZMod (D.host.g kv.1)) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :=
  D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf p)

def goodVec (D : D7) (p : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) : Prop :=
  D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (p ⟨k, v⟩))

theorem monicOf_inj {K : Type} [Field K] {N : ℕ} (a b : Fin N → K)
    (h : Formalism.CyclotomicNorms.monicOf a = Formalism.CyclotomicNorms.monicOf b) : a = b := by
  funext i
  have hc := congrArg (fun p => Polynomial.coeff p (i : ℕ)) h
  simp only [Formalism.CyclotomicNorms.monicOf, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul_X_pow, Fin.val_inj] at hc
  simpa [i.isLt.ne, Finset.sum_ite_eq, Finset.sum_ite_eq'] using hc

theorem ESer_sum (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k) : ∑ p, ESer D kv p = 1 := by
  classical
  obtain ⟨S, hS, hsum⟩ := D.ntypes.eSer_sum kv.1
  rw [← hsum]
  have himg : ∑ p, ESer D kv p =
      ∑ f ∈ Finset.univ.image (fun p : Fin D.R.r → ZMod (D.host.g kv.1) => Formalism.CyclotomicNorms.monicOf p),
        D.ntypes.eSer kv.1 f := by
    rw [Finset.sum_image fun a _ b _ h => monicOf_inj a b h]
    rfl
  rw [himg]
  symm
  refine Finset.sum_subset (fun f hf => ?_) fun f _ hf => ?_
  · obtain ⟨hm, hd, -⟩ := (hS f).1 hf
    exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f hm hd⟩
  · exact D.ntypes.eSer_zero _ _ fun hh => hf ((hS f).2 hh)

theorem e0_eq (D : D7) [DecidableEq (Σ k : Fin 2, D.nd.PlG k)] : D.ntypes.e0 = eGood (ESer D) (goodVec D) := by
  classical
  ext g
  rw [eGood, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  show (∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))), _) = _
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : goodVec D p
  · rw [if_pos hp]; exact (if_pos hp).trans rfl
  · rw [if_neg hp]; exact (if_neg hp).trans rfl

theorem atPlace_eq (D : D7) [DecidableEq (Σ k : Fin 2, D.nd.PlG k)] (k : Fin 2) (v : D.nd.PlG k)
    (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a =
      plc (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ a := by
  unfold Formalism.MainNotions.ArithmeticCylinders.atPlace
  convert mapDomain_mulSingle (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k) a
  all_goals rfl

end Ten

open Ten in

theorem idempotent_acts_trivially_of (Y : Prov D X) (hE : IdempotentGoodTypeCond Y) : ExponentBlockSplitting Y := by
  classical
  obtain ⟨Pi, sp, sup, htop, hT⟩ := hE
  have hfix : ∀ P, D.ntypes.goodTuple (sup P) → ∀ F ∈ sp P, Y.actEE.asAlgebraHom D.ntypes.e0 F = F := by
    intro P hP F hF
    let lab : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1) :=
      fun kv i => (sup P kv.1 kv.2).coeff i
    have hlab : ∀ kv, Formalism.CyclotomicNorms.monicOf (lab kv) = sup P kv.1 kv.2 := fun kv =>
      Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ ((hP kv.1).1.1 kv.2).1 ((hP kv.1).1.1 kv.2).2.1
    rw [e0_eq]
    refine alg_eGood (ESer D) (goodVec D) (fun _ _ => D.ntypes.eSer_idem _ _) (ESer_sum D)
      Y.actEE.asAlgebraHom F lab ?_ ?_
    · rintro ⟨k, v⟩ p hp
      by_contra hne
      have h1 := hT P k v (Formalism.CyclotomicNorms.monicOf p) ⟨F, hF, by rw [atPlace_eq]; exact hne⟩
      exact hp (monicOf_inj _ _ ((hlab ⟨k, v⟩).trans h1).symm)
    · have h2 : (fun k v => Formalism.CyclotomicNorms.monicOf (lab ⟨k, v⟩)) = sup P := by
        funext k v
        exact hlab ⟨k, v⟩
      show D.ntypes.goodTuple _
      rw [h2]
      exact hP
  have hle : (⨆ P ∈ {P | D.ntypes.goodTuple (sup P)}, sp P) ≤
      LinearMap.ker (Y.actEE.asAlgebraHom D.ntypes.e0 - 1) :=
    iSup₂_le fun P hP F hF => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hfix P hP F hF]
      simp
  refine LinearMap.ext fun y => ?_
  have hy : y ∈ LinearMap.ker (Y.actEE.asAlgebraHom D.ntypes.e0 - 1) := hle (by rw [htop]; exact Submodule.mem_top)
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hy
  exact hy

end GoodType

def IsLevelIn (Y : Prov D X) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (P : Pair D.what₂.LL (G0g D.nd)) (j : S.RR.V →ₗ[D.what₂.LL] Y.sK.RR.V)
    (aE : EE →ₗ[ℂ] Y.EEK) (aA : ∀ μ, S.Amb μ →ₗ[ℂ] Y.sK.Amb μ) : Prop :=
  (∀ x, ‖aE x‖ ^ 2 = (Nat.card P.H : ℝ) * ‖x‖ ^ 2) ∧
  (∀ μ y, ‖aA μ y‖ ^ 2 = (Nat.card P.H : ℝ) * ‖y‖ ^ 2) ∧
  (∀ μ y, aE (S.iota μ y) = Y.sK.iota μ (aA μ y)) ∧
  (∀ μ x, aA μ (S.thetaUp μ x) = Y.sK.thetaUp μ (aE x)) ∧
  (∀ μ z y, aA μ (S.cen μ z y) = Y.sK.cen μ z (aA μ y)) ∧
  ∀ x, aE (S.jEE x) = Y.sK.jEE (j x)

def LevelIn (Y : Prov D X) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (P : Pair D.what₂.LL (G0g D.nd)) (j : S.RR.V →ₗ[D.what₂.LL] Y.sK.RR.V) : Prop :=
  ∃ (aE : EE →ₗ[ℂ] Y.EEK) (aA : ∀ μ, S.Amb μ →ₗ[ℂ] Y.sK.Amb μ), IsLevelIn Y S P j aE aA

def adm1_alt (Y : Prov D X) : Prop :=
  ∃ (aE0 : D.what₂.EE0 →ₗ[ℂ] Y.EEK) (aA0 : ∀ μ, X.s.Amb μ →ₗ[ℂ] Y.sK.Amb μ)
    (aEs : D.what₂.EE →ₗ[ℂ] Y.EEK) (aAs : ∀ μ, (RowSide.sharp D).Amb μ →ₗ[ℂ] Y.sK.Amb μ),
    IsLevelIn Y X.s Y.P0 Y.j0 aE0 aA0 ∧ IsLevelIn Y (RowSide.sharp D) Y.Ps Y.js aEs aAs ∧
    ∀ σ, aEs (D.what₂.onb σ) ∈ Submodule.span ℂ
      {z | ∃ (g : G0g D.nd) (σ0 : Fin D.what₂.D0), D.what₂.ft0 σ0 = D.what₂.ft σ ∧
        z = Y.actEE g (aE0 (D.what₂.onb0 σ0))}

theorem adm1_alt.level0 {Y : Prov D X} (h : adm1_alt Y) : LevelIn Y X.s Y.P0 Y.j0 := by
  obtain ⟨aE0, aA0, -, -, h0, -, -⟩ := h
  exact ⟨aE0, aA0, h0⟩

theorem adm1_alt.levelS {Y : Prov D X} (h : adm1_alt Y) : LevelIn Y (RowSide.sharp D) Y.Ps Y.js := by
  obtain ⟨-, -, aEs, aAs, -, hs, -⟩ := h
  exact ⟨aEs, aAs, hs⟩

theorem inj_of_normSq {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (H : Subgroup (G0g D.nd)) (a : V →ₗ[ℂ] W) (h : ∀ x, ‖a x‖ ^ 2 = (Nat.card H : ℝ) * ‖x‖ ^ 2) :
    Function.Injective a := by
  refine (injective_iff_map_eq_zero a).mpr fun x hx => ?_
  have hc : (0 : ℝ) < (Nat.card H : ℝ) := Nat.cast_pos.mpr Nat.card_pos
  have h1 := h x
  rw [hx, norm_zero] at h1
  have h2 : (Nat.card H : ℝ) * ‖x‖ ^ 2 = 0 := by rw [← h1]; norm_num
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hc.ne'
  · exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)

theorem thetaUpInV0_of (Y : Prov D X) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (S : RowSide D EE) (P : Pair D.what₂.LL (G0g D.nd))
    (j : S.RR.V →ₗ[D.what₂.LL] Y.sK.RR.V) (hc : IdempotentCentral D) (h1 : Conclusion1 Y) (he : ExponentBlockSplitting Y)
    (hT : LevelIn Y S P j) : ThetaUpInV0Side S := by
  obtain ⟨aE, aA, hE, hA, hio, hth, hcen, -⟩ := hT
  have hc' : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := hc
  have hK := thetaUpInV0_level_of Y hc' h1 he
  intro μ y hy
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
  show S.thetaUp μ x ∈ LinearMap.range (S.eOp μ)
  refine LinearMap.mem_range.mpr ⟨S.thetaUp μ x, ?_⟩
  apply inj_of_normSq P.H (aA μ) (hA μ)
  have hKx : Y.sK.thetaUp μ (aE x) ∈ LinearMap.range (Y.sK.eOp μ) :=
    hK μ (LinearMap.mem_range_self _ _)
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hKx
  have hidem : Y.sK.eOp μ (Y.sK.thetaUp μ (aE x)) = Y.sK.thetaUp μ (aE x) := by
    rw [← hz, ← LinearMap.comp_apply, Y.sK.eOp_idem μ]
  rw [Y.sK.eOp_tie μ, dif_pos hc'] at hidem
  rw [S.eOp_tie μ, dif_pos hc', hcen μ, hth μ x]
  exact hidem

theorem sharp_downTo (D : D7) (μ : D.what₂.Tup) (j : ℕ) :
    (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show ((RowSide.sharp D).downTo μ j).comp ((RowSide.sharp D).io μ j) =
      (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [ih]
    all_goals rfl

theorem sharp_thetaUp (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).thetaUp μ = D.what₂.thetaUp μ := by
  have hi : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
    show (D.what₂.multZero μ).toLinearEquiv.toLinearMap ∘ₗ (RowSide.sharp D).downTo μ D.R.m ∘ₗ
        (D.what₂.multTop μ).symm.toLinearEquiv.toLinearMap =
      (D.what₂.multZero μ).toLinearEquiv.toLinearMap ∘ₗ D.what₂.downTo μ D.R.m ∘ₗ
        (D.what₂.multTop μ).symm.toLinearEquiv.toLinearMap
    rw [sharp_downTo]
    all_goals rfl
  show LinearMap.adjoint ((RowSide.sharp D).iota μ) = LinearMap.adjoint (D.what₂.iota μ)
  rw [hi]
  all_goals rfl

theorem thetaUpInV0_iff_sharp (D : D7) : ThetaUpInV0 D ↔ ThetaUpInV0Side (RowSide.sharp D) := by
  unfold ThetaUpInV0 ThetaUpInV0Side
  refine forall_congr' fun μ => ?_
  rw [sharp_thetaUp]
  all_goals rfl

def frg (D : D7) : ℝ := (D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ)

def nbar (D : D7) : ℝ := ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ^ (D.R.f * D.R.k)

def LabTie (Y : Prov D X) (lab : Y.T.S → ∀ k : Fin 2, D.nd.PlG k → Polynomial (ZMod (D.host.g k))) : Prop :=
  ∀ s (g : G0g D.nd), D.what₂.embLL ((eS Y.T s).coeff g) =
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (lab s kv.1 kv.2)).coeff (g kv)

def adm3_alt (Y : Prov D X) : Prop :=
  ∃ lab, LabTie Y lab ∧ ∀ s, D.ntypes.goodTuple (lab s)

def LocalMultiplicityFactor (Y : Prov D X) : Prop :=
  ∀ lab, LabTie Y lab → ∃ n0 nSh : Y.T.S → (Σ k : Fin 2, D.nd.PlG k) → ℕ,
    (∀ s, nS Y.T Y.P0 s = ∏ kv, n0 s kv) ∧ (∀ s, nS Y.T Y.Ps s = ∏ kv, nSh s kv) ∧
    ∀ s, D.ntypes.goodTuple (lab s) → ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      n0 s kv = 1 ∧ (D.R.r ≤ D.host.g kv.1 →
        (D.host.g kv.1 : ℝ) ^ D.R.k * (1 - 1 / (D.host.g kv.1 : ℝ)) ≤ (nSh s kv : ℝ) ∧
        (nSh s kv : ℝ) ≤ (D.host.g kv.1 : ℝ) ^ D.R.k * (1 + (2 * (D.R.r : ℝ) - 1) / (D.host.g kv.1 : ℝ)))

def LevelRatioBound (D : D7) : Prop := 4 * D.R.f * D.R.r ≤ min (D.host.g 0) (D.host.g 1)

def PointsLemma (Y : Prov D X) (C : ℝ) : Prop :=
  ∀ lab, LabTie Y lab → ∀ s, D.ntypes.goodTuple (lab s) →
    nS Y.T Y.P0 s = 1 ∧ |(nS Y.T Y.Ps s : ℝ) - nbar D| ≤ C * frg D * nbar D

def RowMultiplicityBound (D : D7) (C : ℝ) : Prop := Formalism.BasicNotions.Lemma3 D C

def LatticeChainWithoutLast (Y : Prov D X) : Prop :=
  ∀ lab, LabTie Y lab → ∀ s, D.ntypes.goodTuple (lab s) → nS Y.T Y.P0 s = 1

def ExactRowOccurrence (D : D7) : Prop := ∀ π, 0 < D.what₂.nRows0 π

def RowTensorMultiplicity (Y : Prov D X) : Prop :=
  ∃ (lab : D.what₂.FT → Y.T.S) (mult : D.what₂.FT → ℕ), (∀ π, 0 < mult π) ∧
    (∀ π, D.what₂.nRows π = nS Y.T Y.Ps (lab π) * mult π) ∧
    (∀ π, D.what₂.nRows0 π = nS Y.T Y.P0 (lab π) * mult π) ∧
    ∀ π π', (∀ k, D.nd.lab k π = D.nd.lab k π') → lab π = lab π'

theorem nbar_pos (D : D7) : 0 < nbar D := by
  unfold nbar
  exact pow_pos (Nat.cast_pos.mpr (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)) _

theorem card_sigmaPl (D : D7) : Fintype.card (Σ k : Fin 2, D.nd.PlG k) = 2 * D.R.f := by
  rw [Fintype.card_sigma, Fin.sum_univ_two, D.nd.card_PlG, D.nd.card_PlG]
  ring

theorem nbar_eq (D : D7) : (∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.host.g kv.1 : ℝ) ^ D.R.k) = nbar D := by
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, D.nd.card_PlG, Fin.prod_univ_two]
  unfold nbar
  push_cast
  ring

theorem prod_near_one {ι : Type} (s : Finset ι) (a : ι → ℝ) (x : ℝ) (hx0 : 0 ≤ x) (hx : (s.card : ℝ) * x ≤ 1)
    (ha : ∀ i ∈ s, 1 - x ≤ a i ∧ a i ≤ 1 + x) : |∏ i ∈ s, a i - 1| ≤ 2 * s.card * x := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs
    simp
  have hn1 : (1 : ℝ) ≤ s.card := Nat.one_le_cast.mpr hs.card_pos
  have hx1 : x ≤ 1 := by nlinarith
  have hpos : ∀ i ∈ s, 0 ≤ a i := fun i hi => by linarith [(ha i hi).1]
  have hup : ∏ i ∈ s, a i ≤ (1 + x) ^ s.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod hpos fun i hi => (ha i hi).2
  have hlo : (1 - x) ^ s.card ≤ ∏ i ∈ s, a i := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by linarith) fun i hi => (ha i hi).1
  have hbern : 1 + (s.card : ℝ) * (-x) ≤ (1 + -x) ^ s.card := one_add_mul_le_pow (by linarith) _
  have hneg : (1 + -x) = 1 - x := by ring
  rw [hneg] at hbern
  have key : ∀ j : ℕ, (j : ℝ) * x ≤ 1 → (1 + x) ^ j ≤ 1 + j * x + (j * x) ^ 2 := by
    intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hj
      push_cast at hj ⊢
      have hjx : (j : ℝ) * x ≤ 1 := by nlinarith
      have h1 := mul_le_mul_of_nonneg_right (ih hjx) (by linarith : (0 : ℝ) ≤ 1 + x)
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have h2 : 0 ≤ x ^ 2 * ((j : ℝ) + 1 - (j : ℝ) ^ 2 * x) :=
        mul_nonneg (sq_nonneg x) (by nlinarith [mul_le_mul_of_nonneg_left hjx hj0])
      rw [pow_succ]
      nlinarith [h1, h2]
  have hk := key s.card hx
  have hnx0 : 0 ≤ (s.card : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx0
  rw [abs_sub_le_iff]
  constructor
  · nlinarith [hup, hk, mul_nonneg hnx0 (by linarith : (0 : ℝ) ≤ 1 - s.card * x)]
  · nlinarith [hlo, hbern]

theorem exactMultiplicityOne_of (Y : Prov D X) (hL : LocalMultiplicityFactor Y) : LatticeChainWithoutLast Y := by
  intro lab hl s hs
  obtain ⟨n0, nSh, h0, -, hloc⟩ := hL lab hl
  rw [h0 s]
  exact Finset.prod_eq_one fun kv _ => (hloc s hs kv).1

theorem latticeChain_succ_of_partial (Y : Prov D X) (C : ℝ) (hC : 8 ≤ C) (hL : LocalMultiplicityFactor Y) (hg : LevelRatioBound D) : PointsLemma Y C := by
  intro lab hl s hs
  obtain ⟨n0, nSh, h0, hSh, hloc⟩ := hL lab hl
  refine ⟨by rw [h0 s]; exact Finset.prod_eq_one fun kv _ => (hloc s hs kv).1, ?_⟩
  have hnb : 0 < nbar D := nbar_pos D
  have hmpos : (0 : ℝ) < ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (lt_min (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
  have hr1 : 1 ≤ D.R.r := by
    unfold Ranks.r
    have := D.R.two_le_m
    omega
  have hg' : 4 * D.R.f * D.R.r ≤ min (D.host.g 0) (D.host.g 1) := hg
  rw [hSh s]
  rcases Nat.eq_zero_or_pos D.R.f with hf | hf
  · have hcard : Fintype.card (Σ k : Fin 2, D.nd.PlG k) = 0 := by rw [card_sigmaPl, hf]
    haveI : IsEmpty (Σ k : Fin 2, D.nd.PlG k) := Fintype.card_eq_zero_iff.mp hcard
    have hnb1 : nbar D = 1 := by
      rw [← nbar_eq]
      simp
    have hfrg : frg D = 0 := by
      unfold frg
      rw [hf]
      simp
    simp [hnb1, hfrg]
  · have hmin : ∀ k : Fin 2, min (D.host.g 0) (D.host.g 1) ≤ D.host.g k := by
      intro k
      fin_cases k
      · exact min_le_left _ _
      · exact min_le_right _ _
    have hrg : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), D.R.r ≤ D.host.g kv.1 := by
      intro kv
      have h4 : D.R.r ≤ 4 * D.R.f * D.R.r := by nlinarith
      exact le_trans h4 (le_trans hg' (hmin kv.1))
    have hmR : ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
        ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) ≤ (D.host.g kv.1 : ℝ) :=
      fun kv => Nat.cast_le.mpr (hmin kv.1)
    have hr1R : (1 : ℝ) ≤ (D.R.r : ℝ) := Nat.one_le_cast.mpr hr1
    have hqpos : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (0 : ℝ) < (D.host.g kv.1 : ℝ) :=
      fun kv => Nat.cast_pos.mpr (D.host.g_prime kv.1).pos
    have hg'R : ((4 * D.R.f * D.R.r : ℕ) : ℝ) ≤ ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hg'
    have e4 : ((4 * D.R.f * D.R.r : ℕ) : ℝ) = 4 * (D.R.f : ℝ) * D.R.r := by push_cast; ring
    rw [e4] at hg'R
    set m : ℝ := ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) with hmdef
    set x : ℝ := (2 * (D.R.r : ℝ) - 1) / m with hxdef
    have hx0 : 0 ≤ x := div_nonneg (by linarith) hmpos.le
    have ha : ∀ kv ∈ (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)),
        1 - x ≤ (nSh s kv : ℝ) / (D.host.g kv.1 : ℝ) ^ D.R.k ∧
          (nSh s kv : ℝ) / (D.host.g kv.1 : ℝ) ^ D.R.k ≤ 1 + x := by
      intro kv _
      obtain ⟨hlo, hhi⟩ := (hloc s hs kv).2 (hrg kv)
      have hqk : (0 : ℝ) < (D.host.g kv.1 : ℝ) ^ D.R.k := pow_pos (hqpos kv) _
      have hinv1 : 1 / (D.host.g kv.1 : ℝ) ≤ x := by
        rw [hxdef, div_le_div_iff₀ (hqpos kv) hmpos]
        nlinarith [hmR kv, hqpos kv,
          mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * D.R.r - 1 by linarith) (hqpos kv).le]
      have hinv2 : (2 * (D.R.r : ℝ) - 1) / (D.host.g kv.1 : ℝ) ≤ x := by
        rw [hxdef]
        exact div_le_div_of_nonneg_left (by linarith) hmpos (hmR kv)
      constructor
      · rw [le_div_iff₀ hqk]
        nlinarith [mul_le_mul_of_nonneg_right hinv1 hqk.le]
      · rw [div_le_iff₀ hqk]
        nlinarith [mul_le_mul_of_nonneg_right hinv2 hqk.le]
    have hcardR : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).card : ℝ) = 2 * (D.R.f : ℝ) := by
      rw [Finset.card_univ, card_sigmaPl]
      push_cast
      ring
    have hnx : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).card : ℝ) * x ≤ 1 := by
      rw [hcardR, hxdef, mul_div_assoc', div_le_one hmpos]
      nlinarith [Nat.cast_nonneg (α := ℝ) D.R.f]
    have hprod := prod_near_one Finset.univ (fun kv => (nSh s kv : ℝ) / (D.host.g kv.1 : ℝ) ^ D.R.k) x hx0 hnx ha
    rw [hcardR] at hprod
    have hsplit : ((∏ kv, nSh s kv : ℕ) : ℝ) =
        (∏ kv, (nSh s kv : ℝ) / (D.host.g kv.1 : ℝ) ^ D.R.k) * nbar D := by
      rw [← nbar_eq, ← Finset.prod_mul_distrib, Nat.cast_prod]
      refine Finset.prod_congr rfl fun kv _ => ?_
      rw [div_mul_cancel₀]
      exact (pow_pos (hqpos kv) _).ne'
    have hfrgE : frg D = (D.R.f : ℝ) * D.R.r / m := rfl
    have hfrg : 2 * (2 * (D.R.f : ℝ)) * x ≤ C * frg D := by
      rw [hfrgE, hxdef]
      rw [show 2 * (2 * (D.R.f : ℝ)) * ((2 * D.R.r - 1) / m) = (4 * D.R.f * (2 * D.R.r - 1)) / m by ring,
        show C * ((D.R.f : ℝ) * D.R.r / m) = (C * D.R.f * D.R.r) / m by ring]
      refine div_le_div_of_nonneg_right ?_ hmpos.le
      have hfr : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hC hfr, Nat.cast_nonneg (α := ℝ) D.R.f]
    rw [hsplit, ← sub_one_mul, abs_mul, abs_of_pos hnb]
    calc |(∏ kv, (nSh s kv : ℝ) / (D.host.g kv.1 : ℝ) ^ D.R.k) - 1| * nbar D
        ≤ (2 * (2 * (D.R.f : ℝ)) * x) * nbar D := mul_le_mul_of_nonneg_right hprod hnb.le
      _ ≤ (C * frg D) * nbar D := mul_le_mul_of_nonneg_right hfrg hnb.le

theorem exactRowOccurrence_of (Y : Prov D X) (hTt : adm3_alt Y) (hT : RowTensorMultiplicity Y) (h : LatticeChainWithoutLast Y) : ExactRowOccurrence D := by
  intro π
  obtain ⟨lab', hl, hg⟩ := hTt
  obtain ⟨lab, mult, hpos, -, h0, -⟩ := hT
  rw [h0 π, h lab' hl (lab π) (hg (lab π)), one_mul]
  exact hpos π

theorem rowMultiplicity_of (Y : Prov D X) (C : ℝ) (hTt : adm3_alt Y) (hT : RowTensorMultiplicity Y) (h : PointsLemma Y C) : RowMultiplicityBound D C := by
  obtain ⟨lab', hl, hg⟩ := hTt
  obtain ⟨lab, mult, hpos, hN, h0, hlab⟩ := hT
  have hone : ∀ π, nS Y.T Y.P0 (lab π) = 1 := fun π => (h lab' hl (lab π) (hg (lab π))).1
  refine ⟨fun π => nS Y.T Y.Ps (lab π), fun π => ?_, fun π => ?_, fun π π' hπ => ?_, fun π => ?_⟩
  · rw [hN π, h0 π, hone π, one_mul]
  · rw [h0 π, hone π, one_mul]
    exact hpos π
  · dsimp only
    rw [hlab π π' hπ]
  · exact (h lab' hl (lab π) (hg (lab π))).2

theorem exactRowOccurrence_of_multiplicity (D : D7) (C : ℝ) (h : RowMultiplicityBound D C) : ExactRowOccurrence D := by
  obtain ⟨n, -, h0, -⟩ := h
  exact h0

def LevelTie (Y : Prov D X) (RP : HLat D.what₂.LL) (j : RP.V →ₗ[D.what₂.LL] Y.RK.V)
    (P : Pair D.what₂.LL (G0g D.nd)) : Prop :=
  Function.Injective j ∧ LinearMap.range j = LinearMap.range (Y.rho.asAlgebraHom (eps P)) ∧
  (∀ x ∈ RP.L, j x ∈ Y.RK.L) ∧
  (∃ n : ℕ, n ∣ Fintype.card (G0g D.nd) ∧
    ∀ y ∈ cut Y.RK Y.rho (eps P) Y.RK.L, ∃ x ∈ RP.L, j x = ((n : ℕ) : D.what₂.LL) • y) ∧
  ∃ c : ℝ, 1 ≤ c ∧ c ≤ (Fintype.card (G0g D.nd) : ℝ) ∧ ∀ v x,
    Formalism.HermitianLatticesTheory.normAt Y.RK.b Y.RK.X v (j x) ^ 2 = c * Formalism.HermitianLatticesTheory.normAt RP.b RP.X v x ^ 2

def RowsExistSmall (X : BaseLevelRowSide D) : Prop := 0 < X.principalHermitianLattice.rank

def GoodTypeGLattice (Y : Prov D X) : Prop :=
  IsGLat Y.RK Y.rho ∧ (∀ g x, Y.sK.jEE (Y.rho g x) = Y.actEE g (Y.sK.jEE x)) ∧
  Y.rho.asAlgebraHom (eG Y.T) = 1 ∧
  LevelTie Y X.principalHermitianLattice Y.j0 Y.P0 ∧ LevelTie Y D.div.RR Y.js Y.Ps

def RowsExistSharp (D : D7) : Prop := 0 < D.what₂.Drows

def ChainConstantSmallLevelCond (X : BaseLevelRowSide D) : Prop := X.BaseLevelSideLevelOneCondition

def Conclusion5 (D : D7) (X : BaseLevelRowSide D) (C : ℝ) : Prop := Formalism.BasicNotions.LemmaT D X C

def GGFromIrreducibility (Y : Prov D X) (C : ℝ) : Prop :=
  RowsExistSmall X → GoodTypeGLattice Y → adm3_alt Y → PointsLemma Y C → Conclusion4a → Conclusion5 D X C

def ChainConstantPassage (D : D7) (X : BaseLevelRowSide D) (C : ℝ) : Prop :=
  |Real.log (kapSharp D) - Real.log X.kap0| ≤ C * (D.R.m : ℝ) * lam0 D

theorem iotaQ_adj {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (hV : ThetaUpInV0Side S) (μ : D.what₂.Tup) (x : EE) :
    S.iotaQ μ (LinearMap.adjoint (S.iotaQ μ) x) = S.iota μ (S.thetaUp μ x) := by
  have hyV : S.thetaUp μ x ∈ S.V0 μ := hV μ (LinearMap.mem_range_self _ _)
  set q := LinearMap.adjoint (S.iotaQ μ) x with hq
  have hqQ : (q : S.Amb μ) ∈ S.V0 μ ⊓ (S.Usp μ)ᗮ := q.2
  obtain ⟨hqV, -⟩ := Submodule.mem_inf.mp hqQ
  have hperp : ∀ w (hw : w ∈ S.Qsp μ), @inner ℂ _ _ w (S.thetaUp μ x - (q : S.Amb μ)) = 0 := by
    intro w hw
    have h1 : @inner ℂ _ _ w (S.thetaUp μ x) = @inner ℂ _ _ (S.iota μ w) x :=
      LinearMap.adjoint_inner_right (S.iota μ) w x
    have h2 : @inner ℂ _ _ w (q : S.Amb μ) = @inner ℂ _ _ (S.iota μ w) x := by
      have := LinearMap.adjoint_inner_right (S.iotaQ μ) ⟨w, hw⟩ x
      exact this
    rw [inner_sub_right, h1, h2, sub_self]
  have hz : S.thetaUp μ x - (q : S.Amb μ) ∈ S.V0 μ := Submodule.sub_mem _ hyV hqV
  obtain ⟨u, hu, w', hw', hdec⟩ :=
    Submodule.exists_add_mem_mem_orthogonal (K := S.Usp μ) (S.thetaUp μ x - (q : S.Amb μ))
  have huV : u ∈ S.V0 μ := (Submodule.mem_inf.mp hu).1
  have hw'Q : w' ∈ S.Qsp μ := by
    show w' ∈ S.V0 μ ⊓ (S.Usp μ)ᗮ
    refine Submodule.mem_inf.mpr ⟨?_, hw'⟩
    have hw'eq : w' = (S.thetaUp μ x - (q : S.Amb μ)) - u := by
      rw [hdec]
      abel
    rw [hw'eq]
    exact Submodule.sub_mem _ hz huV
  have hw0 : w' = 0 := by
    have e1 := hperp w' hw'Q
    have e2 : @inner ℂ _ _ w' u = 0 := Submodule.inner_left_of_mem_orthogonal hu hw'
    rw [hdec, inner_add_right, e2, zero_add] at e1
    exact inner_self_eq_zero.mp e1
  rw [hw0, add_zero] at hdec
  have hker : S.iota μ (S.thetaUp μ x - (q : S.Amb μ)) = 0 := by
    rw [hdec]
    exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hu).2
  rw [map_sub, sub_eq_zero] at hker
  exact hker.symm

theorem iotaQ_inj {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (μ : D.what₂.Tup) : Function.Injective (S.iotaQ μ) := by
  refine (injective_iff_map_eq_zero (S.iotaQ μ)).mpr fun q hq => ?_
  have hq' : S.iota μ (q : S.Amb μ) = 0 := hq
  have hmem : (q : S.Amb μ) ∈ S.V0 μ ⊓ (S.Usp μ)ᗮ := q.2
  obtain ⟨hV, hperp⟩ := Submodule.mem_inf.mp hmem
  have hU : (q : S.Amb μ) ∈ S.Usp μ := Submodule.mem_inf.mpr ⟨hV, LinearMap.mem_ker.mpr hq'⟩
  have h0 := Submodule.inner_right_of_mem_orthogonal hU hperp
  rw [inner_self_eq_zero] at h0
  exact Submodule.coe_eq_zero.mp h0

theorem eig_ne_zero {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (μ : D.what₂.Tup) (hs : Function.Surjective (S.iotaQ μ)) (x : EE) (hx : x ≠ 0) (c : ℂ)
    (h : S.iota μ (S.thetaUp μ x) = c • x) : c ≠ 0 := by
  rintro rfl
  rw [zero_smul] at h
  have ht : LinearMap.adjoint (S.iota μ) = S.thetaUp μ := rfl
  have h1 : S.thetaUp μ x = 0 := by
    have h0 := LinearMap.adjoint_inner_left (S.iota μ) (S.thetaUp μ x) x
    rw [ht, h, inner_zero_right, inner_self_eq_zero] at h0
    exact h0
  obtain ⟨q, hq⟩ := hs x
  have hq' : S.iota μ (q : S.Amb μ) = x := hq
  have h2 := LinearMap.adjoint_inner_left (S.iota μ) (q : S.Amb μ) x
  rw [ht, h1, inner_zero_left, hq'] at h2
  exact hx (inner_self_eq_zero.mp h2.symm)

theorem l1cSharp_of (Y : Prov D X) (hc : IdempotentCentral D) (h1 : Conclusion1 Y) (he : ExponentBlockSplitting Y) (hT : adm1_alt Y) (kap : ℝ)
    (hL : X.L1c0 kap) : SharpLatticeBound D kap := by
  have hV0 : ThetaUpInV0Side X.s := thetaUpInV0_of Y _ _ _ hc h1 he hT.level0
  have hVs : ThetaUpInV0Side (RowSide.sharp D) := thetaUpInV0_of Y _ _ _ hc h1 he hT.levelS
  obtain ⟨aE0, aA0, aEs, aAs, ⟨hn0, -, hi0, ht0, -, -⟩, ⟨hns, -, his, hts, -, -⟩, hty⟩ := hT
  obtain ⟨hbij, hk, ρ, hρ0, hρ, hρu, h0⟩ := hL
  have hgi := h1.2.2.2.2.1
  have hgt := h1.2.2.2.2.2.1
  have hinjs := inj_of_normSq Y.Ps.H aEs hns
  set c : D.what₂.Tup → D.what₂.FT → ℂ :=
    fun μ π => ((kap * ρ μ * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP μ j π : ℝ) : ℂ) with hcdef
  have e0 : ∀ μ σ0, X.s.iota μ (X.s.thetaUp μ (D.what₂.onb0 σ0)) = c μ (D.what₂.ft0 σ0) • D.what₂.onb0 σ0 := by
    intro μ σ0
    rw [← iotaQ_adj X.s hV0]
    exact h0 μ σ0
  have eK : ∀ μ g σ0, Y.sK.iota μ (Y.sK.thetaUp μ (Y.actEE g (aE0 (D.what₂.onb0 σ0)))) =
      c μ (D.what₂.ft0 σ0) • Y.actEE g (aE0 (D.what₂.onb0 σ0)) := by
    intro μ g σ0
    rw [hgt, hgi, ← ht0, ← hi0, e0, map_smul, map_smul]
  have eS : ∀ μ σ, Y.sK.iota μ (Y.sK.thetaUp μ (aEs (D.what₂.onb σ))) =
      c μ (D.what₂.ft σ) • aEs (D.what₂.onb σ) := by
    intro μ σ
    refine Submodule.span_induction
      (p := fun z _ => Y.sK.iota μ (Y.sK.thetaUp μ z) = c μ (D.what₂.ft σ) • z) ?_ ?_ ?_ ?_ (hty σ)
    · rintro z ⟨g, σ0, hσ, rfl⟩
      rw [← hσ]
      exact eK μ g σ0
    · simp
    · intro a b _ _ ha hb
      rw [map_add, map_add, ha, hb, smul_add]
    · intro t a _ ha
      rw [map_smul, map_smul, ha, smul_comm]
  have es : ∀ μ σ, (RowSide.sharp D).iota μ ((RowSide.sharp D).thetaUp μ (D.what₂.onb σ)) =
      c μ (D.what₂.ft σ) • D.what₂.onb σ := by
    intro μ σ
    apply hinjs
    rw [his, hts, eS, map_smul]
  have hne : ∀ μ σ, c μ (D.what₂.ft σ) ≠ 0 := by
    intro μ σ
    have hex : ∃ σ0, D.what₂.ft0 σ0 = D.what₂.ft σ := by
      by_contra hno
      have hempty : {z | ∃ (g : G0g D.nd) (σ0 : Fin D.what₂.D0), D.what₂.ft0 σ0 = D.what₂.ft σ ∧
          z = Y.actEE g (aE0 (D.what₂.onb0 σ0))} = ∅ := by
        ext z
        refine ⟨?_, fun h => h.elim⟩
        rintro ⟨g, σ0, hσ, -⟩
        exact hno ⟨σ0, hσ⟩
      have hz := hty σ
      rw [hempty, Submodule.span_empty, Submodule.mem_bot] at hz
      have h2 : D.what₂.onb σ = 0 := hinjs (by rw [hz, map_zero])
      exact (D.what₂.onb.orthonormal.ne_zero σ) h2
    obtain ⟨σ0, hσ⟩ := hex
    rw [← hσ]
    exact eig_ne_zero X.s μ (hbij μ).2 _ (D.what₂.onb0.orthonormal.ne_zero σ0) _ (e0 μ σ0)
  refine ⟨fun μ => ⟨iotaQ_inj _ μ, ?_⟩, hk, ρ, hρ0, hρ, hρu, fun μ σ => ?_⟩
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← D.what₂.onb.toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    refine ⟨(c μ (D.what₂.ft σ))⁻¹ • LinearMap.adjoint ((RowSide.sharp D).iotaQ μ) (D.what₂.onb σ), ?_⟩
    rw [map_smul, iotaQ_adj _ hVs, es, smul_smul, inv_mul_cancel₀ (hne μ σ), one_smul,
      OrthonormalBasis.coe_toBasis]
  · show (RowSide.sharp D).iotaQ μ (LinearMap.adjoint ((RowSide.sharp D).iotaQ μ) (D.what₂.onb σ)) = _
    rw [iotaQ_adj _ hVs]
    exact es μ σ

theorem kap_eq (Y : Prov D X) (hc : IdempotentCentral D) (h1 : Conclusion1 Y) (he : ExponentBlockSplitting Y) (hT : adm1_alt Y) (hL : ChainConstantSmallLevelCond X)
    (hn : RowsExistSharp D) : kapSharp D = X.kap0 := by
  have h : (RowSide.sharp D).RowLatticeBoundForBasis D.what₂.onb D.what₂.ft X.kap0 := l1cSharp_of Y hc h1 he hT _ hL
  exact (RowSide.RowLatticeBoundForBasis.kap_eq h hn).symm

theorem chainConstantPassage_of (Y : Prov D X) (C : ℝ) (hc : IdempotentCentral D) (h1 : Conclusion1 Y) (he : ExponentBlockSplitting Y) (hT : adm1_alt Y)
    (hL : ChainConstantSmallLevelCond X) (hn : RowsExistSharp D) (hC : 0 ≤ C) : ChainConstantPassage D X C := by
  unfold ChainConstantPassage
  rw [kap_eq Y hc h1 he hT hL hn, sub_self, abs_zero]
  have hl : 0 ≤ lam0 D := by
    unfold lam0
    rcases Nat.eq_zero_or_pos D.what₂.restRowsFiniteGroupCard with h0 | h0
    · rw [h0]
      simp
    · exact Real.log_nonneg (Nat.one_le_cast.mpr h0)
  exact mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) hl

theorem normSq_det_first_block_pos (h0 : RowsExistSmall X) : 0 < D.what₂.D0 := by
  by_contra hD
  have hD0 : D.what₂.D0 = 0 := by omega
  haveI : IsEmpty (Fin D.what₂.D0) := by
    rw [hD0]
    infer_instance
  haveI hsub : Subsingleton D.what₂.EE0 := D.what₂.onb0.toBasis.repr.toEquiv.subsingleton
  haveI hempty : IsEmpty X.s.RR.ι := by
    constructor
    intro i
    exact X.s.jEE_basis.1.ne_zero i (Subsingleton.elim _ _)
  haveI hV : Subsingleton X.s.RR.V := X.s.RR.b.repr.toEquiv.subsingleton
  have hr : X.principalHermitianLattice.rank = 0 := by
    unfold HLat.rank Formalism.HN.rkK BaseLevelRowSide.principalHermitianLattice
    exact Module.finrank_zero_of_subsingleton
  unfold RowsExistSmall at h0
  omega

theorem Drows_pos (Y : Prov D X) (C : ℝ) (hTt : adm3_alt Y) (hR : RowTensorMultiplicity Y) (h3 : PointsLemma Y C)
    (hδ : C * frg D ≤ 1 / 3) (h0 : RowsExistSmall X) : RowsExistSharp D := by
  obtain ⟨labT, hl, hg⟩ := hTt
  obtain ⟨lab, mult, hm, hs, -, -⟩ := hR
  have hD0 := normSq_det_first_block_pos h0
  have hnb := nbar_pos D
  have hn : 0 < nS Y.T Y.Ps (lab (D.what₂.ft0 ⟨0, hD0⟩)) := by
    by_contra hz
    have hz' : nS Y.T Y.Ps (lab (D.what₂.ft0 ⟨0, hD0⟩)) = 0 := by omega
    have h := (h3 labT hl (lab (D.what₂.ft0 ⟨0, hD0⟩)) (hg _)).2
    rw [hz', Nat.cast_zero, zero_sub, abs_neg, abs_of_pos hnb] at h
    have : C * frg D * nbar D ≤ 1 / 3 * nbar D := mul_le_mul_of_nonneg_right hδ hnb.le
    linarith
  have hr : 0 < D.what₂.nRows (D.what₂.ft0 ⟨0, hD0⟩) := by
    rw [hs]
    exact Nat.mul_pos hn (hm _)
  unfold Rows.Data.nRows at hr
  obtain ⟨⟨σ, -⟩⟩ := Fintype.card_pos_iff.1 hr
  exact lt_of_le_of_lt (Nat.zero_le _) σ.2

theorem nonemptyS (Y : Prov D X) (h0 : RowsExistSmall X) (h51 : GoodTypeGLattice Y) : Nonempty Y.T.S := by
  by_contra hS
  rw [not_nonempty_iff] at hS
  haveI := hS
  obtain ⟨-, -, he, ⟨hj, -⟩, -⟩ := h51
  have h0e : eG Y.T = 0 := by
    unfold eG
    simp
  rw [h0e, map_zero] at he
  haveI hsub : Subsingleton Y.sK.RR.V := ⟨fun a b => by
    have ha : (1 : Module.End D.what₂.LL Y.sK.RR.V) a = (0 : Module.End D.what₂.LL Y.sK.RR.V) a := by
      rw [he]
    have hb : (1 : Module.End D.what₂.LL Y.sK.RR.V) b = (0 : Module.End D.what₂.LL Y.sK.RR.V) b := by
      rw [he]
    simp only [Module.End.one_apply, LinearMap.zero_apply] at ha hb
    rw [ha, hb]⟩
  haveI hsub' : Subsingleton Y.RK.V := hsub
  haveI hV : Subsingleton X.principalHermitianLattice.V := ⟨fun a b => hj (Subsingleton.elim _ _)⟩
  have hr : X.principalHermitianLattice.rank = 0 := by
    unfold HLat.rank Formalism.HN.rkK
    exact Module.finrank_zero_of_subsingleton
  unfold RowsExistSmall at h0
  omega

theorem C_nonneg (Y : Prov D X) (C : ℝ) (h0 : RowsExistSmall X) (h51 : GoodTypeGLattice Y) (hTt : adm3_alt Y) (h3 : PointsLemma Y C) :
    0 ≤ C := by
  obtain ⟨lab, hl, hgd⟩ := hTt
  obtain ⟨s⟩ := nonemptyS Y h0 h51
  have h := (h3 lab hl s (hgd s)).2
  have hr : 0 < D.R.r := by
    unfold Ranks.r
    have := D.R.two_le_m
    omega
  have hf : 0 < D.R.f := by
    unfold Ranks.f Ranks.n
    have := D.R.m_le_f
    have := D.R.two_le_m
    omega
  have hm : (0 : ℝ) < ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (lt_min (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
  have hpos : 0 < frg D * nbar D := by
    refine mul_pos ?_ (nbar_pos D)
    unfold frg
    exact div_pos (mul_pos (Nat.cast_pos.mpr hf) (Nat.cast_pos.mpr hr)) hm
  have habs := abs_nonneg ((nS Y.T Y.Ps s : ℝ) - nbar D)
  by_contra hneg
  push_neg at hneg
  nlinarith [mul_neg_of_neg_of_pos hneg hpos]

end Record

section Herm

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

def StarIsConj (K : Type) [Field K] [StarRing K] : Prop :=
  ∃ σ0 : K →+* ℂ, ∀ x, σ0 (star x) = star (σ0 x)

def IsCM (z : K) : Prop := ∀ σ : K →+* ℂ, σ (star z) = star (σ z)

def IsConjPlK (w w' : HeightOneSpectrum (𝓞 K)) : Prop := ∀ x : K, vAdd w' x = vAdd w (star x)

def IsHermE (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  (∀ x y, h y x = star (h x y)) ∧ (∀ x, (∀ y, h x y = 0) → x = 0) ∧ ∀ x y, h (e x) y = h x (e y)

def IsGHerm (A : HLat K) (ρ : Representation K G A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  (∀ x y, h y x = star (h x y)) ∧ (∀ x, (∀ y, h x y = 0) → x = 0) ∧ ∀ g x y, h (ρ g x) (ρ g y) = h x y

def DualInAt (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (M : Submodule (𝓞 K) A.V)
    (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ v : A.V, (∀ a ∈ M, h v a ∈ Set.range (algebraMap (𝓞 K) K)) → ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • v ∈ M

def IsBasisAt (A : HLat K) {d : ℕ} (a : Fin d → A.V) (M : Submodule (𝓞 K) A.V)
    (w w' : HeightOneSpectrum (𝓞 K)) : Prop :=
  LinearIndependent K a ∧ ∀ u ∈ ({w, w'} : Set (HeightOneSpectrum (𝓞 K))),
    LocLe u 0 (Submodule.span (𝓞 K) (Set.range a)) M ∧ LocLe u 0 M (Submodule.span (𝓞 K) (Set.range a))

def GramDetKernelValuation (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  ∀ w w' : HeightOneSpectrum (𝓞 K), IsConjPlK w w' → DualInAt A h A.L w → DualInAt A h A.L w' →
    ∀ (d : ℕ) (a : Fin d → A.V), IsBasisAt A a (cutE A e A.L) w w' →
      vAdd w (Matrix.of fun i j => h (a i) (a j)).det ≤ 2 * (dimE A (1 - e) : ℤ) * vAdd w ((n : ℕ) : K)

def gram_det_kernel_dual_lattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), StarIsConj K → IsGLat A ρ → IsGHerm A ρ h →
    GramDetKernelValuation A (ρ.asAlgebraHom (eG T)) (Fintype.card G) h

def gram_det_kernel_base_level : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → GramDetKernelValuation A e n h

def IsCMFormE (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  (∀ i j, IsCM (h (A.b i) (A.b j))) ∧ (∀ i j, IsCM (A.b.repr (e (A.b j)) i)) ∧
  ∀ (v : InfinitePlace K) i j, Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b i) (A.b j) = v.embedding (h (A.b i) (A.b j))

def IsCMForm (A : HLat K) (ρ : Representation K G A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  (∀ i j, IsCM (h (A.b i) (A.b j))) ∧ (∀ g i j, IsCM (A.b.repr (ρ g (A.b j)) i)) ∧
  ∀ (v : InfinitePlace K) i j, Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b i) (A.b j) = v.embedding (h (A.b i) (A.b j))

def LamStar (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (U : Submodule K A.V) (y : A.V) : Prop :=
  y ∈ LinearMap.range e ∧ (∀ u ∈ U, h y u = 0) ∧
  ∀ m ∈ cutE A e A.L, h y m ∈ Set.range (algebraMap (𝓞 K) K)

def IsValG (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (U : Submodule K A.V) (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) : Prop :=
  ∃ w', IsConjPlK w w' ∧ ∃ (d : ℕ) (y : Fin d → A.V), LinearIndependent K y ∧
    (∀ u ∈ ({w, w'} : Set (HeightOneSpectrum (𝓞 K))),
      (∀ i, ∃ s : 𝓞 K, s ∉ u.asIdeal ∧ LamStar A e h U (s • y i)) ∧
      ∀ z, LamStar A e h U z → ∃ s : 𝓞 K, s ∉ u.asIdeal ∧
        s • z ∈ Submodule.span (𝓞 K) (Set.range y)) ∧
    n = - vAdd w (Matrix.of fun i j => h (y i) (y j)).det

def L7 (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    (∀ w k, IsValG A e h U w k →
      k ≤ ((dimE A e : ℤ) - (Module.finrank K U : ℤ)) * vAdd w ((n : ℕ) : K)) ∧
    (∀ γ : HeightOneSpectrum (𝓞 K) → ℤ, (∀ w, IsValG A e h U w (γ w)) →
      degL A (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)) - degL A (cutE A e A.L) ≤
        ∑ᶠ w, lw K w * (γ w : ℝ)) ∧
    (∀ φ ∈ A.dualL, (∀ u ∈ U, φ u = 0) →
      ∀ m ∈ cutE A e A.L, φ m ∈ Set.range (algebraMap (𝓞 K) K))

def division_rows_rational_lattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), StarIsConj K → IsGLat A ρ → IsGHerm A ρ h → IsCMForm A ρ h →
    (∀ w, DualInAt A h A.L w) → L7 A (ρ.asAlgebraHom (eG T)) (Fintype.card G) h

def division_rows_base_level : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → IsCMFormE A e h →
    (∀ w, DualInAt A h A.L w) → L7 A e n h

end Herm

section Whole

variable {D : D7} {X : BaseLevelRowSide D}

def ConclusionC : Prop :=
  projection_sandwich_lattice ∧ MassRatio₂ ∧ kernel_index_full_lattice ∧ gram_det_kernel_dual_lattice ∧ projection_lemma_base_level ∧ gram_det_kernel_base_level ∧ (∃ C4 : ℝ, Conclusion4 C4) ∧ Conclusion6 ∧ BranchingScaling ∧ PairwiseIndependentOrbitPoints ∧ division_rows_rational_lattice ∧ division_rows_base_level ∧
  Conclusion8 ∧ SameFormAllLevels

def PropositionCStatement : Prop := Adm6 → ConclusionC

def AdmA (Y : Prov D X) (C : ℝ) : Prop :=
  IsometricActionCond Y ∧ MultiplicityEquivariance Y ∧ ThetaEquivarianceCond Y ∧ IdempotentGoodTypeCond Y ∧ adm1_alt Y ∧ adm3_alt Y ∧ RowTensorMultiplicity Y ∧ LocalMultiplicityFactor Y ∧ LevelRatioBound D ∧ 8 ≤ C

def AtEveryPlace (Y : Prov D X) (C : ℝ) : Prop :=
  Conclusion1 Y ∧ ExponentBlockSplitting Y ∧ PointsLemma Y C ∧ ThetaUpInV0 D ∧ ThetaUpInV0Small X ∧ ExactRowOccurrence D ∧ RowMultiplicityBound D C

def IntegralityGoodReduction (Y : Prov D X) (C : ℝ) : Prop := AdmA Y C → AtEveryPlace Y C

theorem stmtA (Y : Prov D X) (C : ℝ) : IntegralityGoodReduction Y C := by
  intro h
  obtain ⟨hA, hB, hth, hE, hT, hTt, hR, hL, hg, hC⟩ := h
  have h1 : Conclusion1 Y := baseChange_preserves_unitary_of Y hA hB hth
  have he : ExponentBlockSplitting Y := idempotent_acts_trivially_of Y hE
  have hc : IdempotentCentral D := idempotentCentral_holds D
  have h3 : PointsLemma Y C := latticeChain_succ_of_partial Y C hC hL hg
  refine ⟨h1, he, h3, ?_, ?_, exactRowOccurrence_of Y hTt hR (exactMultiplicityOne_of Y hL), rowMultiplicity_of Y C hTt hR h3⟩
  · exact (thetaUpInV0_iff_sharp D).2 (thetaUpInV0_of Y _ _ _ hc h1 he hT.levelS)
  · exact thetaUpInV0_of Y _ _ _ hc h1 he hT.level0

def KappaDegreeStatement (D : D7) : Prop := SecondSentenceInputs D → ErrorFirstTermSize D

theorem stmtD (D : D7) : KappaDegreeStatement D := by
  intro h
  exact secondSentenceLemmaOne_of D h

def AdmB (Y : Prov D X) (C : ℝ) : Prop := Adm6 ∧ AdmA Y C ∧ RowsExistSmall X ∧ GoodTypeGLattice Y

def ConclusionB (X : BaseLevelRowSide D) (C : ℝ) : Prop := ConclusionC ∧ Conclusion0 D ∧ Conclusion5 D X C

def SecondFromFirstStatement (Y : Prov D X) (C : ℝ) : Prop := AdmB Y C → ConclusionB X C

def AdmK (Y : Prov D X) (C : ℝ) : Prop := AdmA Y C ∧ RowsExistSharp D ∧ ChainConstantSmallLevelCond X

def KernelFormRational (Y : Prov D X) (C : ℝ) : Prop := AdmK Y C → ChainConstantPassage D X C

theorem stmtK (Y : Prov D X) (C : ℝ) : KernelFormRational Y C := by
  intro h
  obtain ⟨⟨hA, hB, hth, hE, hT, -, -, -, -, hC⟩, hn, hL⟩ := h
  exact chainConstantPassage_of Y C (idempotentCentral_holds D) (baseChange_preserves_unitary_of Y hA hB hth) (idempotent_acts_trivially_of Y hE) hT hL hn (by linarith)

def LemmasOneThreeInputs (Y : Prov D X) (C : ℝ) : Prop := SecondSentenceInputs D ∧ AdmA Y C

def admitted (Y : Prov D X) (C : ℝ) : Prop :=
  Adm6 ∧ LemmasOneThreeInputs Y C ∧ RowsExistSmall X ∧ RowsExistSharp D ∧ GoodTypeGLattice Y ∧ ChainConstantSmallLevelCond X

def Conclusion₂ (Y : Prov D X) (C : ℝ) : Prop :=
  ConclusionC ∧ Conclusion0 D ∧ ErrorFirstTermSize D ∧ ThetaUpInV0 D ∧ ThetaUpInV0Small X ∧ ExactRowOccurrence D ∧ RowMultiplicityBound D C ∧ Conclusion5 D X C ∧ ChainConstantPassage D X C ∧
    Conclusion1 Y ∧ ExponentBlockSplitting Y ∧ PointsLemma Y C

def Stmt (Y : Prov D X) (C : ℝ) : Prop := admitted Y C → Conclusion₂ Y C

theorem stmt_of (Y : Prov D X) (C : ℝ) (sB : SecondFromFirstStatement Y C) : Stmt Y C := by
  intro h
  obtain ⟨h6, ⟨hD, hA⟩, h0, h0s, h51, hL⟩ := h
  obtain ⟨hC, hp0, hp5⟩ := sB ⟨h6, hA, h0, h51⟩
  obtain ⟨h1, he, h3, hV, hV0, hR0, hR⟩ := stmtA Y C hA
  exact ⟨hC, hp0, stmtD D hD, hV, hV0, hR0, hR, hp5, stmtK Y C ⟨hA, h0s, hL⟩, h1, he, h3⟩

theorem stmt_rows (Y : Prov D X) (C : ℝ) (h : LemmasOneThreeInputs Y C) :
    Conclusion1 Y ∧ ExponentBlockSplitting Y ∧ ErrorFirstTermSize D ∧ PointsLemma Y C ∧ ThetaUpInV0 D ∧ ThetaUpInV0Small X ∧ ExactRowOccurrence D ∧ RowMultiplicityBound D C := by
  obtain ⟨hD, hA⟩ := h
  obtain ⟨h1, he, h3, hV, hV0, hR0, hR⟩ := stmtA Y C hA
  exact ⟨h1, he, stmtD D hD, h3, hV, hV0, hR0, hR⟩

theorem stmt_sk (Y : Prov D X) (C : ℝ) (h : admitted Y C) : ChainConstantPassage D X C := by
  obtain ⟨-, ⟨-, hA⟩, -, h0s, -, hL⟩ := h
  exact stmtK Y C ⟨hA, h0s, hL⟩

end Whole

section Family

open Formalism.MainNotions

variable {ε : ℝ}

abbrev ProvF (Fm : FamP ε) : Type 1 :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Prov (Fm.D x i) (Fm.ex x hx i).p0

def familyMultiplicityBoundConst (Fm : FamP ε) (YF : ProvF Fm) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), PointsLemma (YF x hx i) C

def Conclusion3Family (Fm : FamP ε) (YF : ProvF Fm) : Prop := ∃ C : ℝ, familyMultiplicityBoundConst Fm YF C

def familyRowMultiplicity (Fm : FamP ε) : Prop :=
  ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, RowMultiplicityBound (Fm.D x i) C

def familyExactRowOccurrence (Fm : FamP ε) : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ExactRowOccurrence (Fm.D x i)

def FamilyRatioTendsZero (Fm : FamP ε) : Prop :=
  ∀ C : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, C * frg (Fm.D x i) ≤ 1 / 3

def familyLemmaFiveWith (Fm : FamP ε) (C : ℝ) : Prop :=
  0 < C ∧ ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    C * frg (Fm.D x i) ≤ 1 / 3 ∧ Conclusion5 (Fm.D x i) (Fm.ex x hx i).p0 C

def SlopeLossFamily (Fm : FamP ε) : Prop := ∃ C : ℝ, familyLemmaFiveWith Fm C

def Adm5F (Fm : FamP ε) (YF : ProvF Fm) : Prop :=
  (∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    RowsExistSmall (Fm.ex x hx i).p0 ∧ GoodTypeGLattice (YF x hx i)) ∧ FamilyRatioTendsZero Fm

def FamilyProportionality (Fm : FamP ε) (YF : ProvF Fm) : Prop :=
  Adm5F Fm YF → (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), adm3_alt (YF x hx i)) → Conclusion3Family Fm YF → Conclusion4a → SlopeLossFamily Fm

private theorem pointsLemma_mono {D : D7} {X : BaseLevelRowSide D} (Y : Prov D X) {C C' : ℝ} (h : PointsLemma Y C)
    (hC : C ≤ C') : PointsLemma Y C' := by
  intro lab hl s hs
  obtain ⟨h0, h1⟩ := h lab hl s hs
  refine ⟨h0, le_trans h1 ?_⟩
  have hnn : 0 ≤ frg D * nbar D := by
    unfold frg nbar
    positivity
  calc C * frg D * nbar D = C * (frg D * nbar D) := by ring
    _ ≤ C' * (frg D * nbar D) := mul_le_mul_of_nonneg_right hC hnn
    _ = C' * frg D * nbar D := by ring

theorem familyLemmaFive_of_pointwise (Fm : FamP ε) (YF : ProvF Fm)
    (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (C : ℝ), GGFromIrreducibility (YF x hx i) C) : FamilyProportionality Fm YF := by
  intro hA hT h3 h4
  obtain ⟨⟨x0, hx0⟩, h2⟩ := hA
  obtain ⟨C3, x3, hx3⟩ := h3
  refine ⟨max C3 1, lt_of_lt_of_le one_pos (le_max_right C3 1), ?_⟩
  obtain ⟨x2, hx2⟩ := h2 (max C3 1)
  refine ⟨max x0 (max x3 x2), fun x hx hx1 i => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨ha, hb, hc⟩ := hx
  obtain ⟨a0, a1⟩ := hx0 x ha hx1 i
  exact ⟨hx2 x hc hx1 i, H x hx1 i (max C3 1) a0 a1 (hT x hx1 i)
    (pointsLemma_mono _ (hx3 x hb hx1 i) (le_max_left C3 1)) h4⟩

def LemmaFiveLargeConstants (Fm : FamP ε) : Prop := ∃ C0 : ℝ, ∀ C, C0 ≤ C → familyLemmaFiveWith Fm C

theorem familyLemmaFive_of_large (Fm : FamP ε) (h : LemmaFiveLargeConstants Fm) : SlopeLossFamily Fm := by
  obtain ⟨C0, hC0⟩ := h
  exact ⟨max C0 0, hC0 _ (le_max_left _ _)⟩

theorem stmt5Thr_of (Fm : FamP ε) (YF : ProvF Fm)
    (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (C : ℝ), GGFromIrreducibility (YF x hx i) C) :
    Adm5F Fm YF → (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), adm3_alt (YF x hx i)) → Conclusion3Family Fm YF → Conclusion4a → LemmaFiveLargeConstants Fm := by
  intro hA hT h3 h4
  obtain ⟨⟨x0, hx0⟩, h2⟩ := hA
  obtain ⟨C3, x3, hx3⟩ := h3
  refine ⟨max C3 1, fun C hC => ⟨lt_of_lt_of_le one_pos (le_trans (le_max_right C3 1) hC), ?_⟩⟩
  obtain ⟨x2, hx2⟩ := h2 C
  refine ⟨max x0 (max x3 x2), fun x hx hx1 i => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨ha, hb, hc⟩ := hx
  obtain ⟨a0, a1⟩ := hx0 x ha hx1 i
  exact ⟨hx2 x hc hx1 i, H x hx1 i C a0 a1 (hT x hx1 i)
    (pointsLemma_mono _ (hx3 x hb hx1 i) (le_trans (le_max_left C3 1) hC)) h4⟩

def familyChainConstantWith (Fm : FamP ε) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), ChainConstantPassage (Fm.D x i) (Fm.ex x hx i).p0 C

def familyChainConstantPassage (Fm : FamP ε) : Prop := ∃ C : ℝ, familyChainConstantWith Fm C

theorem chainConstantPassage_mono (Fm : FamP ε) {C C' : ℝ} (h : familyChainConstantWith Fm C) (hC : C ≤ C') : familyChainConstantWith Fm C' := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  have h1 := hx0 x hx hx1 i
  unfold ChainConstantPassage at h1 ⊢
  have hl : 0 ≤ lam0 (Fm.D x i) := by
    unfold lam0
    rcases Nat.eq_zero_or_pos (Fm.D x i).what₂.restRowsFiniteGroupCard with h0 | h0
    · rw [h0]
      simp
    · exact Real.log_nonneg (Nat.one_le_cast.mpr h0)
  have hml : 0 ≤ ((Fm.D x i).R.m : ℝ) * lam0 (Fm.D x i) := mul_nonneg (Nat.cast_nonneg _) hl
  nlinarith [mul_le_mul_of_nonneg_right hC hml]

def FamilyLemmaFiveUniform (Fm : FamP ε) : Prop := ∃ C : ℝ, familyLemmaFiveWith Fm C ∧ familyChainConstantWith Fm C

theorem lemmaFiveUniform_of (Fm : FamP ε) (h : LemmaFiveLargeConstants Fm) (hk : familyChainConstantPassage Fm) : FamilyLemmaFiveUniform Fm := by
  obtain ⟨C0, hC0⟩ := h
  obtain ⟨Ck, hCk⟩ := hk
  exact ⟨max C0 Ck, hC0 _ (le_max_left _ _), chainConstantPassage_mono Fm hCk (le_max_right _ _)⟩

def familyThetaUpInV0 (Fm : FamP ε) : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ThetaUpInV0 (Fm.D x i)

def familyThetaUpInV0Small (Fm : FamP ε) : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaUpInV0Small (Fm.ex x hx i).p0

def Conclusion1Family (Fm : FamP ε) (YF : ProvF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion1 (YF x hx i) ∧ ExponentBlockSplitting (YF x hx i)

def familySecondSentenceLemmaOne (Fm : FamP ε) : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ErrorFirstTermSize (Fm.D x i)

def Adm1aF (Fm : FamP ε) (YF : ProvF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), IsometricActionCond (YF x hx i) ∧
    MultiplicityEquivariance (YF x hx i) ∧ ThetaEquivarianceCond (YF x hx i) ∧ IdempotentGoodTypeCond (YF x hx i) ∧ adm1_alt (YF x hx i) ∧
    adm3_alt (YF x hx i) ∧ RowTensorMultiplicity (YF x hx i) ∧ LocalMultiplicityFactor (YF x hx i)

def familySecondSentenceInputs (Fm : FamP ε) : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, SecondSentenceInputs (Fm.D x i)

def Adm1F (Fm : FamP ε) (YF : ProvF Fm) : Prop := familySecondSentenceInputs Fm ∧ Adm1aF Fm YF

def familySmallScalarCond (Fm : FamP ε) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), ChainConstantSmallLevelCond (Fm.ex x hx i).p0

theorem levelBound_of_ratio (D : D7) (h : 12 * frg D ≤ 1 / 3) : LevelRatioBound D := by
  unfold LevelRatioBound
  unfold frg at h
  set m : ℕ := min (D.host.g 0) (D.host.g 1) with hmdef
  have hm : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (lt_min (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
  have hfr : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by positivity
  have e : (D.R.f : ℝ) * D.R.r = (D.R.f : ℝ) * D.R.r / m * m := (div_mul_cancel₀ _ hm.ne').symm
  have h3 : 36 * ((D.R.f : ℝ) * D.R.r / m) ≤ 1 := by linarith
  have h2 : ((4 * D.R.f * D.R.r : ℕ) : ℝ) ≤ (m : ℝ) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right h3 hm.le]
  exact Nat.cast_le.mp h2

theorem familyMultiplicityBound_of (Fm : FamP ε) (YF : ProvF Fm) (h1 : Adm1aF Fm YF) (h2 : FamilyRatioTendsZero Fm) : familyMultiplicityBoundConst Fm YF 8 := by
  obtain ⟨x0, hx0⟩ := h2 12
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, hL⟩ := h1 x hx1 i
  exact latticeChain_succ_of_partial _ 8 le_rfl hL (levelBound_of_ratio _ (hx0 x hx hx1 i))

def AdmFA (Fm : FamP ε) (YF : ProvF Fm) : Prop := Adm1aF Fm YF ∧ FamilyRatioTendsZero Fm

def ThetaOccurrenceOnFamily (Fm : FamP ε) (YF : ProvF Fm) : Prop :=
  Conclusion1Family Fm YF ∧ familyThetaUpInV0 Fm ∧ familyThetaUpInV0Small Fm ∧ familyExactRowOccurrence Fm ∧ familyRowMultiplicity Fm ∧ Conclusion3Family Fm YF

def FamilyPartAImplication (Fm : FamP ε) (YF : ProvF Fm) : Prop := AdmFA Fm YF → ThetaOccurrenceOnFamily Fm YF

def FamilyPartA (Fm : FamP ε) (_CH : ℝ) : Prop := ∀ YF : ProvF Fm, FamilyPartAImplication Fm YF

theorem stmtFA_exact (Fm : FamP ε) (YF : ProvF Fm) (h1 : Adm1aF Fm YF) :
    Conclusion1Family Fm YF ∧ familyThetaUpInV0 Fm ∧ familyThetaUpInV0Small Fm ∧ familyExactRowOccurrence Fm := by
  refine ⟨fun x hx i => ?_, fun x hx i => ?_, fun x hx i => ?_, fun x hx i => ?_⟩
  · obtain ⟨hA, hB, hth, hE, -⟩ := h1 x hx i
    exact ⟨baseChange_preserves_unitary_of _ hA hB hth, idempotent_acts_trivially_of _ hE⟩
  · obtain ⟨hA, hB, hth, hE, hT, -⟩ := h1 x hx i
    exact (thetaUpInV0_iff_sharp _).2 (thetaUpInV0_of _ _ _ _ (idempotentCentral_holds _) (baseChange_preserves_unitary_of _ hA hB hth) (idempotent_acts_trivially_of _ hE) hT.levelS)
  · obtain ⟨hA, hB, hth, hE, hT, -⟩ := h1 x hx i
    exact thetaUpInV0_of _ _ _ _ (idempotentCentral_holds _) (baseChange_preserves_unitary_of _ hA hB hth) (idempotent_acts_trivially_of _ hE) hT.level0
  · obtain ⟨-, -, -, -, -, hTt, hR, hL⟩ := h1 x hx i
    exact exactRowOccurrence_of _ hTt hR (exactMultiplicityOne_of _ hL)

theorem stmtAtA (Fm : FamP ε) (YF : ProvF Fm) : FamilyPartAImplication Fm YF := by
  rintro ⟨h1, h2⟩
  obtain ⟨e1, e2, e3, e4⟩ := stmtFA_exact Fm YF h1
  obtain ⟨x0, hx0⟩ := familyMultiplicityBound_of Fm YF h1 h2
  refine ⟨e1, e2, e3, e4, ⟨8, x0, fun x hx hx1 i => ?_⟩, ⟨8, familyMultiplicityBound_of Fm YF h1 h2⟩⟩
  obtain ⟨-, -, -, -, -, hTt, hR, -⟩ := h1 x hx1 i
  exact rowMultiplicity_of _ 8 hTt hR (hx0 x hx hx1 i)

theorem stmtFA (Fm : FamP ε) (CH : ℝ) : FamilyPartA Fm CH := by
  intro YF
  exact stmtAtA Fm YF

def FamilyPartDImplication (Fm : FamP ε) (_CH : ℝ) : Prop := familySecondSentenceInputs Fm → familySecondSentenceLemmaOne Fm

theorem stmtFD (Fm : FamP ε) (CH : ℝ) : FamilyPartDImplication Fm CH := by
  intro h x hx i
  exact secondSentenceLemmaOne_of _ (h x hx i)

def AdmFB (Fm : FamP ε) (YF : ProvF Fm) : Prop := Adm6 ∧ Adm1aF Fm YF ∧ Adm5F Fm YF

def FamilyConclusionB (Fm : FamP ε) : Prop := ConclusionC ∧ (∀ x (i : Fm.Ix x), Conclusion0 (Fm.D x i)) ∧ LemmaFiveLargeConstants Fm

def FamilyPartBImplication (Fm : FamP ε) (YF : ProvF Fm) : Prop := AdmFB Fm YF → FamilyConclusionB Fm

def FamilyPartB (Fm : FamP ε) (_CH : ℝ) : Prop := ∀ YF : ProvF Fm, FamilyPartBImplication Fm YF

theorem stmtAtB_of (Fm : FamP ε) (YF : ProvF Fm) (pC : ConclusionC) (p0 : ∀ x (i : Fm.Ix x), Conclusion0 (Fm.D x i))
    (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (C : ℝ), GGFromIrreducibility (YF x hx i) C) : FamilyPartBImplication Fm YF := by
  rintro ⟨-, h1, ⟨h50, h52⟩⟩
  have h4 : Conclusion4a := by
    obtain ⟨-, -, -, -, -, -, ⟨C4, h4, -⟩, -⟩ := pC
    exact h4
  exact ⟨pC, p0, stmt5Thr_of Fm YF H ⟨h50, h52⟩ (fun x hx i => (h1 x hx i).2.2.2.2.2.1)
    ⟨8, familyMultiplicityBound_of Fm YF h1 h52⟩ h4⟩

theorem stmtAtB_ofC (Fm : FamP ε) (YF : ProvF Fm) (sC : PropositionCStatement) (p0 : ∀ x (i : Fm.Ix x), Conclusion0 (Fm.D x i))
    (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (C : ℝ), GGFromIrreducibility (YF x hx i) C) : FamilyPartBImplication Fm YF := by
  rintro ⟨h6, h1, h5⟩
  exact stmtAtB_of Fm YF (sC h6) p0 H ⟨h6, h1, h5⟩

def AdmFK (Fm : FamP ε) (YF : ProvF Fm) : Prop := Adm1aF Fm YF ∧ Adm5F Fm YF ∧ familySmallScalarCond Fm

def FamilyPartKImplication (Fm : FamP ε) (YF : ProvF Fm) : Prop := AdmFK Fm YF → familyChainConstantPassage Fm

def PacketAlongFamilyInClass (Fm : FamP ε) (_CH : ℝ) : Prop := ∀ YF : ProvF Fm, FamilyPartKImplication Fm YF

theorem stmtAtK (Fm : FamP ε) (YF : ProvF Fm) : FamilyPartKImplication Fm YF := by
  rintro ⟨h1, ⟨⟨x0, hx0⟩, h2⟩, ⟨xL, hxL⟩⟩
  obtain ⟨x2, hx2⟩ := h2 12
  obtain ⟨x3, hx3⟩ := familyMultiplicityBound_of Fm YF h1 h2
  refine ⟨8, max x0 (max x2 (max x3 xL)), fun x hx hx1 i => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨ha, hb, hc, hd⟩ := hx
  obtain ⟨hA, hB, hth, hE, hT, hTt, hR, -⟩ := h1 x hx1 i
  have hδ := hx2 x hb hx1 i
  have hf : 0 ≤ frg (Fm.D x i) := by
    unfold frg
    positivity
  exact chainConstantPassage_of _ 8 (idempotentCentral_holds _) (baseChange_preserves_unitary_of _ hA hB hth) (idempotent_acts_trivially_of _ hE) hT (hxL x hd hx1 i)
    (Drows_pos _ 8 hTt hR (hx3 x hc hx1 i) (by linarith) (hx0 x ha hx1 i).1) (by norm_num)

theorem stmtFK (Fm : FamP ε) (CH : ℝ) : PacketAlongFamilyInClass Fm CH := by
  intro YF
  exact stmtAtK Fm YF

def FamilyFreeObjectInputs (Fm : FamP ε) (YF : ProvF Fm) : Prop := Adm6 ∧ Adm1F Fm YF ∧ Adm5F Fm YF

def AdmF (Fm : FamP ε) (YF : ProvF Fm) : Prop :=
  Adm6 ∧ Adm1F Fm YF ∧ Adm5F Fm YF ∧ familySmallScalarCond Fm

theorem family_admitted_of_parts (Fm : FamP ε) (YF : ProvF Fm) (h : FamilyFreeObjectInputs Fm YF) (hL : familySmallScalarCond Fm) : AdmF Fm YF := by
  obtain ⟨a, b, c⟩ := h
  exact ⟨a, b, c, hL⟩

theorem FamilyFreeObjectInputs.toA {Fm : FamP ε} {YF : ProvF Fm} (h : FamilyFreeObjectInputs Fm YF) : AdmFA Fm YF := by
  obtain ⟨-, ⟨-, h1⟩, -, h52⟩ := h
  exact ⟨h1, h52⟩

theorem FamilyFreeObjectInputs.toB {Fm : FamP ε} {YF : ProvF Fm} (h : FamilyFreeObjectInputs Fm YF) : AdmFB Fm YF := by
  obtain ⟨h6, ⟨-, h1⟩, h5⟩ := h
  exact ⟨h6, h1, h5⟩

theorem FamilyFreeObjectInputs.toD {Fm : FamP ε} {YF : ProvF Fm} (h : FamilyFreeObjectInputs Fm YF) : familySecondSentenceInputs Fm := by
  obtain ⟨-, ⟨hD, -⟩, -⟩ := h
  exact hD

theorem FamilyFreeObjectInputs.toK {Fm : FamP ε} {YF : ProvF Fm} (h : FamilyFreeObjectInputs Fm YF) (hL : familySmallScalarCond Fm) : AdmFK Fm YF := by
  obtain ⟨-, ⟨-, h1⟩, h5⟩ := h
  exact ⟨h1, h5, hL⟩

def ConclusionOnFamily (Fm : FamP ε) (YF : ProvF Fm) : Prop :=
  ConclusionC ∧ (∀ x (i : Fm.Ix x), Conclusion0 (Fm.D x i)) ∧ familySecondSentenceLemmaOne Fm ∧ familyThetaUpInV0 Fm ∧ familyThetaUpInV0Small Fm ∧ familyExactRowOccurrence Fm ∧ familyRowMultiplicity Fm ∧
  LemmaFiveLargeConstants Fm ∧ familyChainConstantPassage Fm ∧ Conclusion1Family Fm YF ∧ Conclusion3Family Fm YF

def ErrorExponentStatement (Fm : FamP ε) (YF : ProvF Fm) : Prop := AdmF Fm YF → ConclusionOnFamily Fm YF

def KudlaFamilyStatement (Fm : FamP ε) (_CH : ℝ) : Prop := ∀ YF : ProvF Fm, ErrorExponentStatement Fm YF

theorem stmtAt_of (Fm : FamP ε) (YF : ProvF Fm) (sB : FamilyPartBImplication Fm YF) : ErrorExponentStatement Fm YF := by
  rintro ⟨h6, ⟨hD, h1⟩, ⟨h50, h52⟩, hL⟩
  obtain ⟨pC, p0, pT⟩ := sB ⟨h6, h1, ⟨h50, h52⟩⟩
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := stmtAtA Fm YF ⟨h1, h52⟩
  exact ⟨pC, p0, stmtFD Fm 0 hD, e2, e3, e4, e5, pT, stmtAtK Fm YF ⟨h1, ⟨h50, h52⟩, hL⟩, e1, e6⟩

theorem stmtF_of (Fm : FamP ε) (CH : ℝ) (s : FamilyPartB Fm CH) : KudlaFamilyStatement Fm CH := by
  intro YF
  exact stmtAt_of Fm YF (s YF)

theorem stmtF_rows (Fm : FamP ε) (YF : ProvF Fm) (h : FamilyFreeObjectInputs Fm YF) :
    familySecondSentenceLemmaOne Fm ∧ familyThetaUpInV0 Fm ∧ familyThetaUpInV0Small Fm ∧ familyExactRowOccurrence Fm ∧ familyRowMultiplicity Fm ∧ Conclusion1Family Fm YF ∧ Conclusion3Family Fm YF := by
  obtain ⟨-, ⟨hD, h1⟩, -, h52⟩ := h
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := stmtAtA Fm YF ⟨h1, h52⟩
  exact ⟨stmtFD Fm 0 hD, e2, e3, e4, e5, e1, e6⟩

theorem stmtF_sk (Fm : FamP ε) (YF : ProvF Fm) (h : AdmF Fm YF) : familySecondSentenceLemmaOne Fm ∧ familyChainConstantPassage Fm := by
  obtain ⟨-, ⟨hD, h1⟩, h5, hL⟩ := h
  exact ⟨stmtFD Fm 0 hD, stmtAtK Fm YF ⟨h1, h5, hL⟩⟩

end Family

end Formalism.MainNotions.PrimeDegreeVariant
