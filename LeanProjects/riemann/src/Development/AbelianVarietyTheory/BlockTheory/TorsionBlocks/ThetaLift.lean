import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalRingCardinality.DataForms
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions
open scoped Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

section Theta
variable {P : Type} [Fintype P]

def piH (z w : P → ℂ) : ℂ := ∑ p, z p * (starRingEnd ℂ) (w p)

def IsTheta (Λ : AddSubgroup (P → ℂ)) (α : (P → ℂ) → ℂ) (Th : (P → ℂ) → ℂ) : Prop :=
  Differentiable ℂ Th ∧ ∀ l ∈ Λ, ‖α l‖ = 1 ∧
    ∀ z, Th (z + l) = α l * Complex.exp (piH z l + piH l l / 2) * Th z

def nTh (Th : (P → ℂ) → ℂ) (z : P → ℂ) : ℝ := ‖Th z‖ ^ 2 * Real.exp (-(piH z z).re)

def HasNormSq (Λ : AddSubgroup (P → ℂ)) (Th : (P → ℂ) → ℂ) (r : ℝ) : Prop :=
  ∃ F : Set (P → ℂ), IsAddFundamentalDomain Λ F volume ∧ IntegrableOn (nTh Th) F volume ∧
    (∫ z in F, nTh Th z) / Real.pi ^ Fintype.card P = r

def transl (t : P → ℂ) (Th : (P → ℂ) → ℂ) (z : P → ℂ) : ℂ :=
  Complex.exp (-piH z t - piH t t / 2) * Th (z + t)

def IsTranslSum (Λ : AddSubgroup (P → ℂ)) (Th0 Th : (P → ℂ) → ℂ) (S : ℝ) : Prop :=
  ∃ (κ : ℂ) (R : Finset (P → ℂ)) (c : (P → ℂ) → ℂ),
    (∀ t ∈ R, ∃ n : ℕ, 0 < n ∧ n • t ∈ Λ) ∧
    ‖κ‖ * ∑ t ∈ R, ‖c t‖ ≤ Real.exp S ∧
    ∀ z, Th z = κ * ∑ t ∈ R, c t * transl t Th0 z

end Theta

section Schur
variable {T : Type} [Fintype T] {n₀ : ℕ}

abbrev Cell (ν : T → Fin n₀ → ℕ) : Type := Σ τ : T, Σ r : Fin n₀, Fin (ν τ r)

abbrev Tens (ν : T → Fin n₀ → ℕ) (n : ℕ) : Type := (Cell ν → Fin n) → ℂ

def tensSq {ν : T → Fin n₀ → ℕ} {n : ℕ} (w : Tens ν n) : ℝ := ∑ a, ‖w a‖ ^ 2

def tpow (ν : T → Fin n₀ → ℕ) {n n' : ℕ} (g : T → Fin n' → Fin n → ℂ) (w : Tens ν n) : Tens ν n' :=
  fun a => ∑ b, (∏ c : Cell ν, g c.1 (a c) (b c)) * w b

def extVec (ν : T → Fin n₀ → ℕ) {n : ℕ} (h : n₀ ≤ n) : Tens ν n :=
  fun a => ∑ σ : Equiv.Perm (Cell ν),
    if (∀ c, (σ c).1 = c.1 ∧ ((σ c).2.2 : ℕ) = (c.2.2 : ℕ)) ∧ (∀ c, a c = Fin.castLE h (σ c).2.1)
    then ((Equiv.Perm.sign σ : ℤ) : ℂ) else 0

def schurSpace (ν : T → Fin n₀ → ℕ) {n : ℕ} (h : n₀ ≤ n) : Submodule ℂ (Tens ν n) :=
  Submodule.span ℂ (Set.range fun g : T → Fin n → Fin n → ℂ => tpow ν g (extVec ν h))

def jetOp (ν : T → Fin n₀ → ℕ) {n₁ : ℕ} (c : T → ℂ) (Th : (T × Fin n₁ × Fin n₀ → ℂ) → ℂ)
    (w : Tens ν n₀) : Tens ν n₁ :=
  fun a => ∑ b, iteratedFDeriv ℂ (Fintype.card (Cell ν)) Th 0
    (fun k => Pi.single (((Fintype.equivFin (Cell ν)).symm k).1, a ((Fintype.equivFin (Cell ν)).symm k),
      b ((Fintype.equivFin (Cell ν)).symm k)) (c ((Fintype.equivFin (Cell ν)).symm k).1)) * w b

end Schur

def hookProd (n : ℕ) (ν : ℕ → ℕ) : ℕ :=
  ∏ r ∈ Finset.range n, ∏ c ∈ Finset.range (ν r),
    ((ν r - c - 1) + ((Finset.Ioo r n).filter (fun r' => c < ν r')).card + 1)

example : hookProd 2 (fun r => if r = 0 then 3 else 1) = 8 := by decide

def IsOrthoFrame {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (τ : E →+* ℂ) {n : ℕ}
    (fr : S.V →ₛₗ[τ] (Fin n → ℂ)) : Prop :=
  ∀ x y, ∑ a, (starRingEnd ℂ) (fr x a) * fr y a = τ (S.hT x y)

def pairLattice {E : Type} [Field E] [NumberField E] [StarRing E] {T : Type} (S S' : HSpace E)
    (pl : T → (E →+* ℂ)) {n₀ n₁ : ℕ} (fr : ∀ τ, S.V →ₛₗ[pl τ] (Fin n₀ → ℂ))
    (fr' : ∀ τ, S'.V →ₛₗ[pl τ] (Fin n₁ → ℂ)) (𝔞 : Submodule (𝓞 E) E) (ξ : E)
    (L : Submodule (𝓞 E) S.V) (L' : Submodule (𝓞 E) S'.V) : AddSubgroup (T × Fin n₁ × Fin n₀ → ℂ) :=
  AddSubgroup.closure {u | ∃ φ : S.V →ₗ[E] S'.V, (∀ x ∈ L, φ x ∈ Formalism.HermitianLatticesTheory.idealSmul 𝔞 L') ∧
    ∀ τ x a, ∑ b, u (τ, a, b) * fr τ x b =
      ((Real.sqrt (2 * Real.pi * ‖pl τ ξ‖) : ℝ) : ℂ) * fr' τ (φ x) a}

variable (D : D7)

theorem N_le_succ (i : ℕ) : D.R.N i ≤ D.R.N (i + 1) := by
  unfold Ranks.N; nlinarith

def nuNat (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (r : ℕ) : ℕ := ⌊DV.nuRow D u j τ r⌋₊

def nuFin (u : D.what₂.Word) (i : ℕ) : D.what₂.Tau → Fin (D.R.N i) → ℕ := fun τ r => nuNat D u (i + 1) τ r

def nuSize (u : D.what₂.Word) (i : ℕ) (τ : D.what₂.Tau) : ℝ :=
  ∑ r ∈ Finset.range (D.R.N i), DV.nuRow D u (i + 1) τ r

def liftNormSq (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ) : ℝ :=
  Formalism.HN.opNormAt ((D.fm u).lat i).b ((D.fm u).lat i).X ((D.fm u).lat (i + 1)).b ((D.fm u).lat (i + 1)).X
    (InfinitePlace.mk s) ((D.fm u).KL i hK) ^ 2

def conjPlace (s : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  s.comp (D.embE.comp
    (D.host.sigmaOf ((D.eTau τ : D.R.Psi) : D.R.GG) : D.host.E →+* D.host.E))

def datumIdeal (cc : Ideal (𝓞 D.host.K)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0

def datumXi (cc : Ideal (𝓞 D.host.K)) : D.host.E :=
  -1 / ((Ideal.absNorm cc : D.host.E) * D.host.sqrtMinusD)

def classSq (u : D.what₂.Word) (i' : ℕ) {n₀ n : ℕ} {ν : D.what₂.Tau → Fin n₀ → ℕ}
    (φ : (D.mem u).C.cls i' → Tens ν n) : ℝ :=
  ∑ c, ((Nat.card ((D.mem u).C.stab i' c) : ℕ) : ℝ)⁻¹ * tensSq (φ c)

def IsThetaLift (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ) (S r : ℝ) : Prop :=
  letI := D.host.cmStar
  ∃ (s' : D.what₂.LL →+* ℂ) (cc : Ideal (𝓞 D.host.K))
    (fr : ∀ τ, (D.sp.X i).V →ₛₗ[conjPlace D s' τ] (Fin (D.R.N i) → ℂ))
    (fr' : ∀ τ, (D.sp.X (i + 1)).V →ₛₗ[conjPlace D s' τ] (Fin (D.R.N (i + 1)) → ℂ))
    (ζ : D.what₂.Tau → ℂ)
    (e₀ : ((D.fm u).lat i).V →ₛₗ[s'] ((D.mem u).C.cls i → Tens (nuFin D u i) (D.R.N i)))
    (e₁ : ((D.fm u).lat (i + 1)).V →ₛₗ[s'] ((D.mem u).C.cls (i + 1) → Tens (nuFin D u i) (D.R.N (i + 1))))
    (ε : (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → ℂ)
    (Th : (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) →
      (D.what₂.Tau × Fin (D.R.N (i + 1)) × Fin (D.R.N i) → ℂ) → ℂ),
    InfinitePlace.mk s' = InfinitePlace.mk s ∧
    s' (D.embE D.host.sqrtMinusD) = D.what₂.embLL (D.embE D.host.sqrtMinusD) ∧
    cc ≠ ⊥ ∧
    (∀ τ, IsOrthoFrame (D.sp.X i) (conjPlace D s' τ) (fr τ)) ∧
    (∀ τ, IsOrthoFrame (D.sp.X (i + 1)) (conjPlace D s' τ) (fr' τ)) ∧
    (∀ τ, ‖ζ τ‖ = 1) ∧
    (∀ x c, e₀ x c ∈ schurSpace (nuFin D u i) le_rfl) ∧
    (∀ x c, e₁ x c ∈ schurSpace (nuFin D u i) (N_le_succ D i)) ∧
    (∀ x, Formalism.HermitianLatticesTheory.normAt ((D.fm u).lat i).b ((D.fm u).lat i).X (InfinitePlace.mk s) x ^ 2 =
      classSq D u i (e₀ x)) ∧
    (∀ x, Formalism.HermitianLatticesTheory.normAt ((D.fm u).lat (i + 1)).b ((D.fm u).lat (i + 1)).X (InfinitePlace.mk s) x ^ 2 =
      classSq D u (i + 1) (e₁ x)) ∧
    (∀ c c', ‖ε c c'‖ = 1) ∧
    (∀ x c', e₁ ((D.fm u).KL i hK x) c' = ∑ c, ((D.mem u).C.wt i c * ε c c') •
      jetOp (nuFin D u i) (fun τ => (((Real.sqrt (D.gx.Om τ s))⁻¹ : ℝ) : ℂ) * ζ τ) (Th c c') (e₀ x c)) ∧
    ∀ c c', ∃ (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) (M' : Submodule (𝓞 D.host.E) (D.sp.X (i + 1)).V)
      (α Th0 : (D.what₂.Tau × Fin (D.R.N (i + 1)) × Fin (D.R.N i) → ℂ) → ℂ),
      Submodule.IsLattice D.host.E M ∧ Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X i).hT M ∧
      Submodule.IsLattice D.host.E M' ∧ Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X (i + 1)).hT M' ∧
      IsTheta (pairLattice (D.sp.X i) (D.sp.X (i + 1)) (conjPlace D s') fr fr'
        (datumIdeal D cc : Submodule (𝓞 D.host.E) D.host.E) (datumXi D cc) M M') α Th0 ∧
      HasNormSq (pairLattice (D.sp.X i) (D.sp.X (i + 1)) (conjPlace D s') fr fr'
        (datumIdeal D cc : Submodule (𝓞 D.host.E) D.host.E) (datumXi D cc) M M') Th0 r ∧
      IsTranslSum (pairLattice (D.sp.X i) (D.sp.X (i + 1)) (conjPlace D s') fr fr'
        (datumIdeal D cc : Submodule (𝓞 D.host.E) D.host.E) (datumXi D cc) M M') Th0 (Th c c') S

def mainPh (u : D.what₂.Word) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  ∑ τ, ((∑ r ∈ Finset.range (D.R.N i), phF (DV.nuRow D u (i + 1) τ r)) -
    nuSize D u i τ * Real.log (D.gx.Om τ s))

def mainHook (u : D.what₂.Word) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  ∑ τ, (Real.log (hookProd (D.R.N i) (nuNat D u (i + 1) τ) : ℝ) - nuSize D u i τ * Real.log (D.gx.Om τ s))

def ExactBound : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ) (S r : ℝ),
    IsThetaLift D u i hK s S r →
    liftNormSq D u i hK s ≤ Real.exp (mainPh D u i s) * r *
      Real.exp ((D.R.f : ℝ) * (D.R.N i * D.R.N (i + 1)) *
          Real.log (8 + 32 * ((D.R.f : ℝ) * (D.R.N i * D.R.N (i + 1))) * D.host.v) + 2 * S +
        ∑ τ, (1 + 2 * ((D.R.N i : ℝ) * D.R.N (i + 1)) * Real.log (2 * nuSize D u i τ + 2))) *
      ((Fintype.card ((D.mem u).C.cls i) : ℝ) * Fintype.card ((D.mem u).C.cls (i + 1)))

def logLev (u : D.what₂.Word) : ℝ := Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * (D.mem u).A.T)

def restTerm (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  (D.R.f : ℝ) * D.R.N i * D.R.N (i + 1) * Real.log (D.gx.thOne s ^ 2) +
    C * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) ^ 2 * (L.sc.L + logLev D u)

def BoundPh (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i)
    (s : D.what₂.LL →+* ℂ) : Prop :=
  liftNormSq D u i hK s ≤ Real.exp (mainPh D u i s + restTerm D L C u i s)

def BoundHook (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i)
    (s : D.what₂.LL →+* ℂ) : Prop :=
  liftNormSq D u i hK s ≤ Real.exp (mainHook D u i s + restTerm D L C u i s)

def Inputs (L : SizeData₂ D) (C' : ℝ) (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i)
    (s : D.what₂.LL →+* ℂ) : Prop :=
  IsThetaLift D u i hK s (C' * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) ^ 2 * logLev D u)
      ((D.gx.thOne s ^ (D.R.f * D.R.N i * D.R.N (i + 1))) ^ 2) ∧
    (Fintype.card ((D.mem u).C.cls i) : ℝ) ≤
      Real.exp (C' * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * (L.sc.L + logLev D u)) ∧
    (Fintype.card ((D.mem u).C.cls (i + 1)) : ℝ) ≤
      Real.exp (C' * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * (L.sc.L + logLev D u))

def SizeAt (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ),
    BoundPh D L C u i hK s ∧ BoundHook D L C u i hK s

def ParametersSizeBoundAt (L : SizeData₂ D) (C' C : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ),
    Inputs D L C' u i hK s → BoundPh D L C u i hK s ∧ BoundHook D L C u i hK s

def SizeFam {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ p : Fm.Ix x, SizeAt (Fm.D x p) (Fm.L x p) C

def InputsFam {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C' x0 : ℝ, ∀ x ≥ x0, ∀ (p : Fm.Ix x) (u : (Fm.D x p).what₂.Word) (i : ℕ), i < (Fm.D x p).R.m →
    ∀ (hK : ((Fm.D x p).fm u).KRat i) (s : (Fm.D x p).what₂.LL →+* ℂ), Inputs (Fm.D x p) (Fm.L x p) C' u i hK s

def LiftSize {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ C' : ℝ, ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ p : Fm.Ix x, ParametersSizeBoundAt (Fm.D x p) (Fm.L x p) C' C

end GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

end
