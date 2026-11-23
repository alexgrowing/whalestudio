import Mathlib
import Formalism.LocalToGlobal.Columns.CoefModB

open MvPolynomial NumberField
open Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators

section Numbers

variable {n : ℕ}

def Interlace (lam : DomWeight (n + 1)) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, lam.w i.succ ≤ sg.w i ∧ sg.w i ≤ lam.w i.castSucc

def EqualLast (lam : DomWeight (n + 1)) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, i.val + 1 = n → sg.w i = lam.w (Fin.last n)

def aNum (lam : DomWeight (n + 1)) (sg : DomWeight n) (i : Fin n) : ℕ := (sg.w i - lam.w i.succ).toNat

def bNum (lam : DomWeight (n + 1)) (sg : DomWeight n) (i : Fin n) : ℕ := (lam.w i.castSucc - sg.w i).toNat

def dZero (lam : DomWeight (n + 1)) (sg : DomWeight n) : ℤ := ∑ i : Fin n, (sg.w i - lam.w i.succ)

def rangeSet (lam : DomWeight (n + 1)) (sg : DomWeight n) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam.w i.succ) (min (lam.w i.castSucc) (lam.w i.succ + dZero lam sg))

def degDiff (lam : DomWeight (n + 1)) (sg : DomWeight n) : ℤ := ∑ i, lam.w i - ∑ i, sg.w i

end Numbers

section Capelli

variable (K : Type) [Field K] (n : ℕ)

def eOp (i j : Fin (n + 1)) : Module.End K (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :=
  ∑ s : Fin (n + 1), (LinearMap.mulLeft K (X (i, s) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) K)) ∘ₗ
    (pderiv (j, s) : Derivation K (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) _).toLinearMap

def fOp (u : ℤ) (i j : Fin n) : Module.End K (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :=
  (if i = j then (u + ((j.val : ℤ) + 1)) • (1 : Module.End K (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K)) else 0) -
    eOp K n i.castSucc j.castSucc

def capelli (u : ℤ) : Module.End K (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :=
  ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) • (List.ofFn fun j : Fin n => fOp K n u (p j) j).prod

variable {n}

def zOp (lam : DomWeight (n + 1)) (sg : DomWeight n) : Module.End K (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :=
  (List.ofFn fun i : Fin n =>
    ((((rangeSet lam sg i).erase (sg.w i)).toList).map fun v =>
      capelli K n (v - lam.w (Fin.last n) - ((i.val : ℤ) + 1))).prod).prod

end Capelli

section Tensors

variable (K : Type) [Field K] {n : ℕ}

abbrev Gen (lam : DomWeight (n + 1)) (sg : DomWeight n) : Type :=
  (∀ i : Fin n, Fin (aNum lam sg i) → Fin (i.val + 1) → Fin n) ×
    (∀ i : Fin n, Fin (bNum lam sg i) → Fin i.val → Fin n)

def piGen (lam : DomWeight (n + 1)) (sg : DomWeight n) (t : Gen lam sg) : MvPolynomial (Fin n × Fin n) K :=
  (∏ i : Fin n, ∏ k : Fin (aNum lam sg i), Formalism.GradedWeylDivisibility.initMinor K (t.1 i k) (Nat.succ_le_of_lt i.isLt)) *
    ∏ i : Fin n, ∏ k : Fin (bNum lam sg i), Formalism.GradedWeylDivisibility.initMinor K (t.2 i k) i.isLt.le

def phiGen (lam : DomWeight (n + 1)) (sg : DomWeight n) (t : Gen lam sg) :
    MvPolynomial (Fin (n + 1) × Fin (n + 1)) K :=
  (∏ i : Fin n, ∏ k : Fin (aNum lam sg i),
      Formalism.GradedWeylDivisibility.initMinor K (fun r => (t.1 i k r).castSucc) (Nat.succ_le_succ i.isLt.le)) *
    ∏ i : Fin n, ∏ k : Fin (bNum lam sg i),
      Formalism.GradedWeylDivisibility.initMinor K (s := i.val + 1)
        (Fin.snoc (α := fun _ => Fin (n + 1)) (fun r : Fin i.val => (t.2 i k r).castSucc) (Fin.last n))
        (Nat.succ_le_succ i.isLt.le)

variable {ι : Type} [Fintype ι]

def piAll (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n) :
    ((∀ τ, Gen (lam τ) (sg τ)) →₀ K) →ₗ[K] Pol K ι n :=
  Finsupp.linearCombination K fun t => ten fun τ => piGen K (lam τ) (sg τ) (t τ)

def zPhiAll (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n) :
    ((∀ τ, Gen (lam τ) (sg τ)) →₀ K) →ₗ[K] Pol K ι (n + 1) :=
  Finsupp.linearCombination K fun t => ten fun τ => zOp K (lam τ) (sg τ) (phiGen K (lam τ) (sg τ) (t τ))

end Tensors

section Maps

theorem exists_section {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) : ∃ g : W →ₗ[K] V, ∀ v, f (g (f v)) = f v := by
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g, hg⟩ := s.exists_extend
  refine ⟨g, fun v => ?_⟩
  have h1 : g (f v) = s (f.rangeRestrict v) := LinearMap.congr_fun hg (f.rangeRestrict v)
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict v))
  rw [h1]
  simpa using h2

variable (K : Type) [Field K] {n : ℕ} {ι : Type} [Fintype ι]

def branch (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n) : VV K sg →ₗ[K] Pol K ι (n + 1) :=
  zPhiAll K lam sg ∘ₗ (exists_section (piAll K lam sg)).choose ∘ₗ (VV K sg).subtype

instance finiteVV (lam : ι → DomWeight n) : Module.Finite K (VV K lam) := Module.Finite.of_basis (bVV K lam)

variable [CharZero K]

def branchT (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n) : VV K lam →ₗ[K] VV K sg :=
  (LinearMap.BilinForm.toDual (pairBK (K := K) sg) (pairingBNondegenerate_holds K ι n sg)).symm.toLinearMap ∘ₗ
    (branch K lam sg).dualMap ∘ₗ pairB lam ∘ₗ (VV K lam).subtype

theorem pair_branchT (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n) (x : VV K lam) (y : VV K sg) :
    pairBK sg (branchT K lam sg x) y = pairB lam x.1 (branch K lam sg y) := by
  simp [branchT, LinearMap.BilinForm.apply_toDual_symm_apply]

variable {K}

def pTilde (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n) (t : ι → K) : VV K lam →ₗ[K] VV K sg :=
  (∏ τ, t τ ^ (-degDiff (lam τ) (sg τ))) • branchT K lam sg

end Maps

section Statement

def extLat {K : Type} [Field K] [NumberField K] {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) (t : K) :
    Submodule (𝓞 K) (Fin (n + 1) → K) :=
  M.comap (LinearMap.funLeft (𝓞 K) K Fin.castSucc) ⊓
    (Submodule.span (𝓞 K) {t}).comap (LinearMap.proj (Fin.last n))

theorem mem_extLat {K : Type} [Field K] [NumberField K] {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) (t : K)
    (x : Fin (n + 1) → K) :
    x ∈ extLat M t ↔ (fun a : Fin n => x a.castSucc) ∈ M ∧ ∃ c : 𝓞 K, c • t = x (Fin.last n) := by
  simp only [extLat, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_span_singleton, LinearMap.proj_apply]
  rfl

def PTildeIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n),
    (∀ τ, Interlace (lam τ) (sg τ)) → (∀ τ, EqualLast (lam τ) (sg τ)) →
    ∀ (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
    ∀ (t : ι → K), (∀ τ, t τ ≠ 0) →
    ∀ x : VV K lam, x ∈ delK lam (fun τ => extLat (M τ) (t τ)) → pTilde lam sg t x ∈ delK sg M

end Statement

example (K : Type) [Field K] (lam : DomWeight 1) (sg : DomWeight 0) (t : Gen lam sg) :
    zOp K lam sg = 1 ∧ piGen K lam sg t = 1 ∧ phiGen K lam sg t = 1 ∧ degDiff lam sg = lam.w 0 := by
  simp [zOp, piGen, phiGen, degDiff]

example (K : Type) [Field K] (ι : Type) [Fintype ι] (lam : ι → DomWeight 1) (sg : ι → DomWeight 0) :
    LinearMap.ker (piAll K lam sg) ≤ LinearMap.ker (zPhiAll K lam sg) := by
  have h1 : ∀ t, piAll K lam sg t = C (t.sum fun _ c => c) := by
    intro t
    simp [piAll, piGen, ten, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_C_mul]
  have h2 : ∀ t, zPhiAll K lam sg t = C (t.sum fun _ c => c) := by
    intro t
    simp [zPhiAll, zOp, phiGen, ten, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_C_mul]
  intro t ht
  rw [LinearMap.mem_ker, h1, C_eq_zero] at ht
  rw [LinearMap.mem_ker, h2, ht, C_0]

example (K : Type) [Field K] (u : ℤ) :
    capelli K 1 u (X (0, 0)) = u • (X (0, 0) : MvPolynomial (Fin 2 × Fin 2) K) := by
  simp [capelli, fOp, eOp, Fin.sum_univ_two, pderiv_X, Pi.single_apply, add_mul]

end GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators
