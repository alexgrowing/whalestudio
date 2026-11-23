import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker

open Formalism.L2.Th1.H (Sesq matH stdH stdLat alphaQ kernel4 tens4 StdData pow4 imgLat inter opU)
open Formalism.MainNotions

section Gen

variable (L : PeriodPair) (ω₀ : ℂ) (c : ℝ) {n : Type} [Fintype n] [DecidableEq n]

def hOne (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] : Matrix n n ℂ :=
  ((Formalism.L2.Th1.F.area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ)

def IsThM (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (κ : ℂ)
    (θ : (n → ℂ) → ℂ) : Prop :=
  θ ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM ∧
    tens4 θ = κ • kernel4 L ω₀ ΛM (alphaQ c (stdH L (Fin 4 × n))) g

def thM (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (κ : ℂ) : (n → ℂ) → ℂ :=
  Classical.epsilon (IsThM L ω₀ c ΛM g κ)

def StdOK (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : Prop :=
  StdData L ω₀ (hOne L n) ΛM (alphaQ c (matH (hOne L n))) (alphaQ c (stdH L (Fin 4 × n))) g

def tensPow (θ : (n → ℂ) → ℂ) (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) : ℂ :=
  ∏ i : Fin N', ∏ j : Fin N, θ fun τ => z τ i j

def powLat (ΛM : AddSubgroup (n → ℂ)) (N N' : ℕ) : AddSubgroup (n → Fin N' → Fin N → ℂ) where
  carrier := {z | ∀ i j, (fun τ => z τ i j) ∈ ΛM}
  zero_mem' := fun _ _ => ΛM.zero_mem
  add_mem' := fun hx hy i j => ΛM.add_mem (hx i j) (hy i j)
  neg_mem' := fun hx i j => ΛM.neg_mem (hx i j)

def formV (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : Sesq (n → Fin N' → Fin N → ℂ) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun z w => (∑ τ, ∑ i, ∑ j, z τ i j * conj (w τ i j)) / (A : ℂ))
    (by intro a b c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)
    (by intro a b c; simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)

def twoMoves {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₀ Λ₁ Λ₂ : AddSubgroup V)
    (θ : V → ℂ) : V → ℂ :=
  inter H α Λ₁ Λ₂ (inter H α Λ₀ Λ₁ θ)

end Gen

section Arith

variable (D : D7)

def SplitK (p : ℕ) : Prop := p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1

structure IsoKG (K E : Type) [Field K] [Field E] [Algebra K E] (cj : E → E) (n : Type) [Fintype n] where
  g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)
  isom : ∀ x y, ∑ w, algebraMap K E (g x w) * cj (algebraMap K E (g y w))
      = algebraMap K E (∑ a, Algebra.trace K E (x a * cj (y a)))

abbrev IsoK : Type := IsoKG D.host.K D.host.E D.host.conj D.what₂.Tau

variable {D}

def IsoK.AtP (γ : IsoK D) (p : ℕ) : Prop :=
  (∀ x : Fin 4 → D.host.E, (∀ a, x a ∈ D.host.AA0) → ∃ s : ℕ, Nat.Coprime s p ∧
    ∀ w, (s : D.host.K) * γ.g x w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) ∧
  ∀ v : Fin 4 × D.what₂.Tau → D.host.K, (∀ w, v w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) →
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : D.host.E) * γ.g.symm v a ∈ D.host.AA0

def IsoK.detRel (γ γ₀ : IsoK D) : D.host.K :=
  LinearMap.det ((γ₀.g.symm.trans γ.g : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] _) :
    (Fin 4 × D.what₂.Tau → D.host.K) →ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K))

def ordK (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)) (x : D.host.K) : ℤ :=
  -WithZero.log (𝔭.valuation D.host.K x)

structure KapChoice (γ₀ : IsoK D) where
  pp : ℕ → IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)
  pp_over : ∀ p, p.Prime → SplitK D p → ((p : ℕ) : 𝓞 D.host.K) ∈ (pp p).asIdeal
  pi : ℕ → 𝓞 D.host.K
  pi_gen : ∀ p, p.Prime → SplitK D p → (pp p).asIdeal ^ classNumber D.host.K = Ideal.span {pi p}
  gaP : ℕ → IsoK D
  gaP_at : ∀ p, p.Prime → SplitK D p → (gaP p).AtP p
  rt : ℕ → ℂ
  rt_pow : ∀ p, p.Prime → SplitK D p → rt p ^ (2 * classNumber D.host.K)
    = D.host.φ₀ (((pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)
      / D.host.φ₀ (D.host.conj (((pi p : 𝓞 D.host.K) : D.host.K) : D.host.E))

def KapChoice.yP {γ₀ : IsoK D} (k : KapChoice γ₀) (p : ℕ) : ℤ := ordK (k.pp p) ((k.gaP p).detRel γ₀)

def KapChoice.kappa {γ₀ : IsoK D} (k : KapChoice γ₀) : ℂ :=
  ∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK D p}, k.rt p ^ (-(k.yP p))

def KapChoice.YFinite {γ₀ : IsoK D} (k : KapChoice γ₀) : Prop :=
  {p : ℕ | p.Prime ∧ SplitK D p ∧ k.yP p ≠ 0}.Finite

def YIndep (γ₀ : IsoK D) : Prop :=
  ∀ (p : ℕ) (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)) (γ γ' : IsoK D), p.Prime → SplitK D p →
    ((p : ℕ) : 𝓞 D.host.K) ∈ 𝔭.asIdeal → γ.AtP p → γ'.AtP p → ordK 𝔭 (γ.detRel γ₀) = ordK 𝔭 (γ'.detRel γ₀)

def lamMM (D : D7) (Λ : AddSubgroup ℂ) : AddSubgroup (D.what₂.Tau → ℂ) :=
  AddSubgroup.closure {z | ∃ w ∈ Λ, ∃ a ∈ D.host.AA0, z = fun τ => w * TaylorLogMetric.embT D τ a}

end Arith

section Fam

variable {D : D7}

structure Base (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) where
  L : PeriodPair
  lat : L.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ
  ω₀ : ℂ
  t0 : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (ω₀ / 2)
  γ₀ : IsoK D
  gC : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)
  gC_spec : ∀ x : Fin 4 → D.host.E, gC (fun w => TaylorLogMetric.embT D w.2 (x w.1))
    = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E)
  kc : KapChoice γ₀

namespace Base

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

def cq (_B : Base D cc δ) : ℝ := Real.sqrt D.host.d / 2

def lamM (_B : Base D cc δ) : AddSubgroup (D.what₂.Tau → ℂ) := lamMM D (TaylorLogMetric.lamOf D cc δ)

def th0 : ℂ → ℂ := Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2)

def kappa : ℂ := B.kc.kappa

def StdOK : Prop := Ker.StdOK B.L B.ω₀ B.cq B.lamM B.gC

def IsThMM (θ : (D.what₂.Tau → ℂ) → ℂ) : Prop := IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa θ

def thMM : (D.what₂.Tau → ℂ) → ℂ := thM B.L B.ω₀ B.cq B.lamM B.gC B.kappa

def thZero (N N' : ℕ) : TaylorLogMetric.VC D N N' → ℂ := tensPow B.thMM N N'

abbrev tor (_B : Base D cc δ) : TaylorLogMetric.Tor D := TaylorLogMetric.tor0 D cc δ

def eY (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : TaylorLogMetric.VC D N N' → ℂ :=
  TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L L') (B.thZero N N')

def thHalf (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : TaylorLogMetric.VC D N N' → ℂ :=
  TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N'))
    (B.thZero N N')

def thMoved (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : TaylorLogMetric.VC D N N' → ℂ :=
  TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L L') (B.thHalf N N' L)

def chiFac (χ : TaylorLogMetric.IdE D → ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : ℂ :=
  χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ^ (((N' / 2 : ℕ) : ℤ)) * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N') L') ^ (-((N / 2 : ℕ) : ℤ))

def eNat (χ : TaylorLogMetric.IdE D → ℂ) : TaylorLogMetric.FamE D :=
  fun N N' L L' z => chiFac χ N N' L L' * B.thMoved N N' L L' z

def AreaOK : Prop := TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L

def Lat0OK (N N' : ℕ) : Prop :=
  TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N'

def LatOK (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Prop :=
  Formalism.L2.Th1.H.IsSelfDual (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D B.tor L L') ∧
  Formalism.L2.Th1.H.IsSemiChar (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D B.tor L L')
    (TaylorLogMetric.al D B.tor)

def ThZeroMem (N N' : ℕ) : Prop :=
  B.thZero N N' ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
    (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))

def QInt0 (N N' : ℕ) : Prop :=
  ∀ x ∈ TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'), ∃ m : ℤ,
    Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D B.tor x x).re = (m : ℝ)

def QIntAll : Prop :=
  ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → ∀ x ∈ TaylorLogMetric.La D B.tor L L', ∃ m : ℤ,
    Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D B.tor x x).re = (m : ℝ)

def ThZeroSpans (N N' : ℕ) : Prop :=
  ∀ F ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
    (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')), ∃ a : ℂ, F = a • B.thZero N N'

def Comm {V : Type*} [AddCommGroup V] (Λ₁ Λ₂ : AddSubgroup V) : Prop :=
  Formalism.L2.Th1.H.relIdx Λ₁ Λ₂ ≠ 0 ∧ Formalism.L2.Th1.H.relIdx Λ₂ Λ₁ ≠ 0

def LatAll : Prop :=
  (∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → B.LatOK N N' L L') ∧
  ∀ N N' L₁ L₁' L₂ L₂', TaylorLogMetric.admitted D N N' L₁ L₁' → TaylorLogMetric.admitted D N N' L₂ L₂' →
    Comm (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂')

def VecP (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.vec22 D B.tor (B.eNat χ)

def ThP (C : ℝ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.th22 D B.tor C (B.eNat χ)

def EqP (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.eq22 D B.tor χ (B.eNat χ)

def IntP (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.int22 D B.tor (B.eNat χ)

def MomP (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.mom22 D cc δ (B.eNat χ) ∧ TaylorLogMetric.LargerSupportMomentCondition D cc δ (B.eNat χ)

def StrP (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.str22 D B.tor (B.eNat χ)

def LateralTheory (C : ℝ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  B.VecP χ ∧ B.ThP C χ ∧ B.EqP χ ∧ B.IntP χ ∧ B.MomP χ ∧ B.StrP χ

def SignP : Prop :=
  ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → B.thMoved N N' L L' = B.eY N N' L L' ∨ B.thMoved N N' L L' = -B.eY N N' L L'

def OrderP : Prop :=
  ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → B.thMoved N N' L L' =
    TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D B.tor L L')
      (TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L')
        (B.thZero N N'))

end Base

def BaseExists (D : D7) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), TaylorLogMetric.IsCurveIdeal D cc → ∀ δ : ℂ, δ ≠ 0 → Nonempty (Base D cc δ)

def GCUnique (D : D7) : Prop :=
  ∀ (γ₀ : IsoK D) (g g' : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)),
    (∀ x : Fin 4 → D.host.E, g (fun w => TaylorLogMetric.embT D w.2 (x w.1)) = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E)) →
    (∀ x : Fin 4 → D.host.E, g' (fun w => TaylorLogMetric.embT D w.2 (x w.1)) = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E)) →
    g = g'

end Fam

end Formalism.L2.Ker
