import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq

noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W
open scoped TensorProduct

namespace UpperTheory.V.Pa

variable {l : ℕ} [Fact l.Prime]

structure SinfRel (l : ℕ) {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {D q n : ℕ}
    (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D) (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) :
    Prop where
  X : ∀ p, τS (Til.ι O O' _ (MvPowerSeries.X p)) = MvPowerSeries.X p
  C : ∀ a : abelian₂ O Empty D, τS (Til.ι O O' _ (MvPowerSeries.C a)) = MvPowerSeries.C (lamEmb O O' D a)
  cc : ∀ c : Sinf O Empty D q n →ₐ[O] abelian₂ O Empty D, (∀ z, c z = MvPowerSeries.constantCoeff z) →
    ∀ z, MvPowerSeries.constantCoeff (τS z) = τ (Til.map O' c z)
  del : ∀ a : Fin q → ℕ, delIdeal l (abelian₂ O' Unit D) n a =
    (delIdeal l (abelian₂ O Empty D) n a).map ((τS.toRingEquiv : _ →+* Sinf O' Unit D q n).comp (Til.ι O O' _))

structure RingRel {L : Loc} {G0 G : Glob l L} {O O' : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CommRing O']
    [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] {n : ℕ} {r : Resid G0.frame O n} {r' : Resid G0.frame O' n}
    {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {B' : Type} [CommRing B'] [Algebra O' B'] [IsCO O' B']
    {u : Pair r B} {u' : Pair r' B'} {J : Ideal B} {J' : Ideal B'} {D : ℕ} {b : TWBase u J Empty D}
    {b' : TWBase u' J' Unit D} {h : G.Hom G0} {q : ℕ} {ut : Fin q → Fin n → O} {ut' : Fin q → Fin n → O'} {N : ℕ}
    (A : TWRing b h ut N) (A' : TWRing b' h ut' N)
    (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) where
  ρ : Til O O' A.R ≃ₐ[O'] A'.R
  maps : A.p.Maps ((ρ.toRingEquiv : _ →+* A'.R).comp (Til.ι O O' A.R)) A'.p.D A'.p.ψ
  s : ∀ z, A'.s (τS z) = ρ (Til.map O' A.s z)
  U : ∀ j i, A'.U j i = ρ (Til.ι O O' A.R (A.U j i))
  ν : Til O O' A.R ⊗[A.R] A.M ≃+ A'.M
  ν_smul : ∀ t m, ν (t • m) = ρ t • ν m

end UpperTheory.V.Pa
