import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudADef
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def midI (r : ℕ) (j : Fin r) : Fin (r + 1 + 1) := j.castSucc.succ

def midOf {r : ℕ} (t : Fin (r + 1 + 1)) : Option (Fin r) :=
  if h : 0 < t.val ∧ t.val < r + 1 then some ⟨t.val - 1, by omega⟩ else none

def subY (A : Type) [CommRing A] (r : ℕ) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) :=
  aeval fun v => match midOf v.2 with
    | some j => ∑ i : Fin r, C (X (i, j)) * X (v.1, midI r i)
    | none => X v

def sub2 (K : Type) [Field K] (r : ℕ) :
    MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
  aeval fun w => map (blockEmb K (k := r) (n := r) w.1).toRingHom (subY K r (X w.2))

theorem coeff_sum_monomial_linear {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (L : B →ₗ[K] K) (f : MvPolynomial σ B)
    (u : σ →₀ ℕ) : coeff u (∑ u' ∈ f.support, monomial u' (L (coeff u' f))) = L (coeff u f) := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hu
  · rfl
  · have h0 : coeff u f = 0 := by simpa [mem_support_iff] using hu
    rw [h0, map_zero]

def lcoef {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (L : B →ₗ[K] K) :
    MvPolynomial σ B →ₗ[K] MvPolynomial σ K where
  toFun f := ∑ u ∈ f.support, monomial u (L (coeff u f))
  map_add' f g := by
    ext u
    rw [coeff_add, coeff_sum_monomial_linear, coeff_sum_monomial_linear, coeff_sum_monomial_linear, coeff_add, map_add]
  map_smul' c f := by
    ext u
    rw [RingHom.id_apply, coeff_smul, coeff_sum_monomial_linear, coeff_sum_monomial_linear, coeff_smul, map_smul]

theorem coeff_lcoef {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (L : B →ₗ[K] K) (f : MvPolynomial σ B)
    (u : σ →₀ ℕ) : coeff u (lcoef L f) = L (coeff u f) :=
  coeff_sum_monomial_linear L f u

def lamOf (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) :
    MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K →ₗ[K] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K :=
  lcoef L ∘ₗ (sub2 K r).toLinearMap

def detY (A : Type) [CommRing A] (r : ℕ) : MvPolynomial (Fin r × Fin r) A :=
  Matrix.det (fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))

def resY (A : Type) [CommRing A] (r : ℕ) (s : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) :
    MvPolynomial (Fin r × Fin r) A :=
  eval (idPoint (MvPolynomial (Fin r × Fin r) A) (r + 1 + 1) (r + 1 + 1)) (subY A r s)

def RowA {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (f : MvPolynomial (Fin k × Fin n) K) (d : ℕ) : Prop :=
  ∀ u, coeff u f ≠ 0 → rowDeg u a = d

def shapeC {r : ℕ} (c : ℕ) (β : Fin r → ℕ) : Fin (r + 1 + 1) → ℕ :=
  fun t => if t = 0 then c else match midOf t with
    | some j => β j
    | none => 0

def PhInv (K : Type) [Field K] (r N : ℕ) (α α' : Fin r → ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) : Prop :=
  ∀ l : Matrix (Fin r) (Fin r) K, IsUnit l.det → ∀ f ∈ dualWeyl K r r α, ∀ f' ∈ dualWeyl K r r α',
    L (blockEmb K true (rowAct K l f) * blockEmb K false (rowAct K l f')) =
      l.det ^ N * L (blockEmb K true f * blockEmb K false f')

def QPh : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (r : ℕ), 1 ≤ r → ∀ (a c N : ℕ) (α : Fin r → ℕ), Antitone α → (∀ i, α i ≤ N) →
    (∀ i j, α i ≤ α j + c) → c ≤ 8 * a →
    ∃ L : MvPolynomial (Bool × (Fin r × Fin r)) R.Kf →ₗ[R.Kf] R.Kf,
      PhInv R.Kf r N α (fun i => N - α i.rev) L ∧
      (∀ f ∈ intO R.O r α, ∀ f' ∈ intO R.O r (fun i => N - α i.rev),
        L (blockEmb R.Kf true f * blockEmb R.Kf false f') ∈ Set.range (algebraMap R.O R.Kf)) ∧
      ∃ (nb : ℕ) (u u' : Fin nb → MvPolynomial (Fin r × Fin r) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim r (fun j => (α j : ℤ)) ∧ (∀ b, ka b ≤ ⌈kappaOneExponent p a (r + 1)⌉₊) ∧
        (∀ b, u b ∈ intO R.O r α) ∧ (∀ a', u' a' ∈ intO R.O r (fun i => N - α i.rev)) ∧
        ∀ a' b, L (blockEmb R.Kf true (u b) * blockEmb R.Kf false (u' a')) = if a' = b then (p : R.Kf) ^ ka b else 0

def SubCoeffP : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (ν : Fin (r + 1 + 1) → ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
    v ∈ dualWeyl A (r + 1 + 1) (r + 1 + 1) ν → ∀ u, coeff u (subY A r v) ∈ dualWeyl A r r (fun j => ν (midI r j))

def SubMapP : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
    subY B r (map φ v) = map (map φ) (subY A r v)

def SubRowP : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (d : ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
    RowA a v d → RowA a (subY A r v) d

def LamCoeffP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ),
    coeff u (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal u,
        L (blockEmb K true (coeff x.1 (subY K r v)) * blockEmb K false (coeff x.2 (subY K r t)))

def LamEquivP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (g : Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) K) (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K),
    lamOf K r L (blockEmb K true (rowAct K g v) * blockEmb K false (rowAct K g t)) =
      rowAct K g (lamOf K r L (blockEmb K true v * blockEmb K false t))

def LamMulP : Prop :=
  ∀ (K : Type) [Field K] (r Q : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (F s t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K), subY K r F = C (detY K r ^ Q) * map C F →
    lamOf K r L (blockEmb K true (F * s) * blockEmb K false t) =
      F * lcoef L (C (blockEmb K true (detY K r ^ Q)) * map (blockEmb K (k := r) (n := r) true).toRingHom (subY K r s) *
        map (blockEmb K (k := r) (n := r) false).toRingHom (subY K r t))

def LamEvalP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K),
    eval (idPoint K (r + 1 + 1) (r + 1 + 1)) (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      L (blockEmb K true (resY K r v) * blockEmb K false (resY K r t))

def LamMemP : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (r N : ℕ) (ν ν' νp : Fin (r + 1 + 1) → ℕ)
    (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K),
    ν (Fin.last (r + 1)) = 0 → ν' (Fin.last (r + 1)) = 0 → νp (Fin.last (r + 1)) = 0 → νp 0 = ν 0 + ν' 0 →
    (∀ j, νp (midI r j) = N) → PhInv K r N (fun j => ν (midI r j)) (fun j => ν' (midI r j)) L →
    ∀ v ∈ dualWeyl K (r + 1 + 1) (r + 1 + 1) ν, ∀ t ∈ dualWeyl K (r + 1 + 1) (r + 1 + 1) ν',
      lamOf K r L (blockEmb K true v * blockEmb K false t) ∈ dualWeyl K (r + 1 + 1) (r + 1 + 1) νp

def SubMuP : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (r : ℕ), 1 ≤ r → ∀ (P Q : ℕ),
    ∀ F ∈ dualWeyl R.Kf (r + 1 + 1) (r + 1 + 1) (nuOf (wtPQ (r + 1) P Q)), subY R.Kf r F = C (detY R.Kf r ^ Q) * map C F

def TopLineP : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (r : ℕ), 1 ≤ r → ∀ (a b : ℕ),
    ∀ Ψ ∈ dualWeyl R.Kf (r + 1 + 1) (r + 1 + 1) (nuOf (wtPQ (r + 1) a b)), RowA 0 Ψ (a + b) → RowA (Fin.last (r + 1)) Ψ 0 →
      Ψ = C (eval (idPoint R.Kf (r + 1 + 1) (r + 1 + 1)) Ψ) * hw R.Kf (le_refl (r + 1 + 1)) (nuOf (wtPQ (r + 1) a b))

def LiftP : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (r c : ℕ) (β : Fin r → ℕ), Antitone β → (∀ j, β j ≤ c) →
    ∀ u ∈ dualWeyl A r r β, ∃ s ∈ dualWeyl A (r + 1 + 1) (r + 1 + 1) (shapeC c β),
      RowA 0 s c ∧ RowA (Fin.last (r + 1)) s 0 ∧ resY A r s = u

def DetDivP : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (r Q : ℕ) (β : Fin r → ℕ), 1 ≤ r → Antitone β →
    ∀ u ∈ dualWeyl A r r (fun j => β j + Q), ∃ u₀ ∈ dualWeyl A r r β, u = detY A r ^ Q * u₀

def IntCapP : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K], Function.Injective (algebraMap O K) →
    ∀ (k : ℕ) (ν : Fin k → ℕ) (F : MvPolynomial (Fin k × Fin k) K), F ∈ dualWeyl K k k ν →
      (∀ u, coeff u F ∈ Set.range (algebraMap O K)) → F ∈ intO O k ν

def HwMulP : Prop :=
  ∀ (A : Type) [CommRing A] (k : ℕ) (ν ν' : Fin k → ℕ), Antitone ν → Antitone ν' →
    hw A (le_refl k) (ν + ν') = hw A (le_refl k) ν * hw A (le_refl k) ν' ∧
    eval (idPoint A k k) (hw A (le_refl k) ν) = 1

end Formalism.MainNotions.flipOneThree.Pf

end
