import Formalism.WachLatticeTwists.HodgeTateChains.XiAdicFiltrationData

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

def AdicPerturbationFixedFreeAndCoboundary : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Type) [CommRing R] [Algebra ℤ_[ℓ] R] (Xm : Type) [AddCommGroup Xm]
    [Module R Xm] [Module ℤ_[ℓ] Xm] [IsScalarTower ℤ_[ℓ] R Xm] (ϖ z z' : R),
    z * z' = algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ]) →
    IsAdicComplete (Ideal.span {ϖ}) Xm → (∀ x : Xm, z • x = 0 → x = 0) →
    ∀ g B : Xm →ₗ[R] Xm, (∀ x, g x = x → x = 0) → (∀ x, ∃ y, z • x = g y - y) →
    (∀ x, g x + (z * ϖ) • B (g x) = x → x = 0) ∧
    ∀ x, ∃ y, (ℓ : ℤ_[ℓ]) • x = (g y + (z * ϖ) • B (g y)) - y

def StatBKb : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O], ¬ IsField O →
    ∀ (HT HD' HV HV' : Type) [AddCommGroup HT] [Module O HT] [AddCommGroup HD'] [Module O HD']
      [AddCommGroup HV] [Module (FractionRing O) HV] [Module O HV]
      [IsScalarTower O (FractionRing O) HV]
      [AddCommGroup HV'] [Module (FractionRing O) HV'] [Module O HV']
      [IsScalarTower O (FractionRing O) HV']
      (jT : HT →ₗ[O] HV) (pr : HV' →ₗ[O] HD')
      (pair : HV →ₗ[FractionRing O] HV' →ₗ[FractionRing O] FractionRing O)
      (pT : HT →ₗ[O] HD' →ₗ[O] Formalism.NG.KO O)
      (Hf : Submodule (FractionRing O) HV) (Hf' : Submodule (FractionRing O) HV'),
    (∀ a, a ∈ Hf ↔ ∀ b ∈ Hf', pair a b = 0) →
    (∀ a b, pT a (pr b) = Submodule.Quotient.mk (pair (jT a) b)) →
    ∀ a : HT, (∀ b ∈ Hf', pT a (pr b) = 0) ↔ jT a ∈ Hf

def InvariantsLengthBound : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ), 0 ∉ U → U.Nonempty → ∀ D : InvariantsCohomologyData ℓ,
    D.piece.Inputs w U 0 → D.Union → D.Flat → D.LES → D.Inv →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (d : Type) [Fintype d]
      (N : Submodule O (d → Formalism.NG.KO O)) (_ : D.M ≃+ N),
      Module.length O N ≤
        (Fintype.card d : ℕ∞) * ((c0 ℓ m U : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}))

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
