import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes

set_option autoImplicit false

noncomputable section

namespace CrystallineSemistableComparison.Onto

structure ChartRings (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A] (n d : ℕ) where
  x : Fin n → A
  t : Fin d → A
  etale : (MvPolynomial.aeval (R := K) (Sum.elim x t) : MvPolynomial (Fin n ⊕ Fin d) K →ₐ[K] A).toRingHom.Etale
  R : Finset (Fin d) → Type
  [cr : ∀ S, CommRing (R S)]
  [alg : ∀ S, Algebra K (R S)]
  res : ∀ {S T : Finset (Fin d)}, S ⊆ T → (R S →ₐ[K] R T)
  res_id : ∀ (S : Finset (Fin d)) (h : S ⊆ S) y, res h y = y
  res_comp : ∀ {S T U : Finset (Fin d)} (h : S ⊆ T) (h' : T ⊆ U) y, res h' (res h y) = res (h.trans h') y
  base : R ∅ ≃ₐ[K] A

  u : ∀ (S : Finset (Fin d)) (k : Fin d), k ∈ S → Fin d → R S
  t_eq : ∀ (S : Finset (Fin d)) (k : Fin d) (hk : k ∈ S) (j : Fin d),
    res (Finset.empty_subset S) (base.symm (t j)) = res (Finset.empty_subset S) (base.symm (t k)) * u S k hk j
  u_res : ∀ {S T : Finset (Fin d)} (h : S ⊆ T) (k : Fin d) (hk : k ∈ S) (j : Fin d), res h (u S k hk j) = u T k (h hk) j

  chart_surj : ∀ k : Fin d,
    letI : Algebra A (R {k}) := ((res (Finset.empty_subset {k})).toRingHom.comp base.symm.toRingHom).toAlgebra
    Function.Surjective (MvPolynomial.aeval (R := A) (S₁ := R {k}) (u {k} k (Finset.mem_singleton_self k)))
  chart_ker : ∀ k : Fin d,
    letI : Algebra A (R {k}) := ((res (Finset.empty_subset {k})).toRingHom.comp base.symm.toRingHom).toAlgebra
    RingHom.ker (MvPolynomial.aeval (R := A) (S₁ := R {k}) (u {k} k (Finset.mem_singleton_self k))).toRingHom =
      Ideal.span (insert (MvPolynomial.X k - 1) (Set.range fun j => MvPolynomial.C (t j) - MvPolynomial.C (t k) * MvPolynomial.X j))

  loc : ∀ (S : Finset (Fin d)) (k : Fin d) (hk : k ∈ S),
    letI : Algebra (R {k}) (R S) := (res (Finset.singleton_subset_iff.2 hk)).toRingHom.toAlgebra
    IsLocalization.Away (∏ j ∈ S, u {k} k (Finset.mem_singleton_self k) j) (R S)

attribute [instance] ChartRings.cr ChartRings.alg

variable {K : Type} [Field K] {A : Type} [CommRing A] [Algebra K A] {n d : ℕ}

def ChartRings.I (C : ChartRings K A n d) (S : Finset (Fin d)) : Ideal (C.R S) :=
  Ideal.span {y | ∃ k, (S = ∅ ∨ k ∈ S) ∧ y = C.res (Finset.empty_subset S) (C.base.symm (C.t k))}

def ChartFormsCechExact : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : Type) [CommRing A] [Algebra K A] (n d : ℕ), 0 < d → ∀ (C : ChartRings K A n d)
    (a : ℕ) (P : PM.{0} K (Fin d)) (e : ∀ S, P.M S ≃ₗ[K] relOm K (C.I S) a),
    (∀ {S T : Finset (Fin d)} (h : S ⊆ T) (y : P.M S),
      ((e T (P.res h y) : relOm K (C.I T) a) : Om K (C.R T) a) = omMap (C.res h) a ((e S y : relOm K (C.I S) a) : Om K (C.R S) a)) →
    P.Ex

end CrystallineSemistableComparison.Onto
