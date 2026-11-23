import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.IdealNormClassCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CokerDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LayerUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LayerGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycMemPrincIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ShaDGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.GenGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.GenIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.RankBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.RankXRk
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv
import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

noncomputable section

namespace UpperTheory.V.Tower

section Step0

variable {l : ℕ} [Fact l.Prime] {L₀ : Type} [Field L₀] [NumberField L₀] {Ω : Type} [Field Ω] [Algebra L₀ Ω] [IsAlgClosure L₀ Ω]

theorem step0 (hμ : HasMuQ l L₀) {γ : G L₀ Ω} (hγ : IsGen l ⊤ γ) {e : ℤ} (he : e ≠ 0) (m : ℕ) (L₁ : Type) [Field L₁]
    [NumberField L₁] [Algebra L₀ L₁] (hL : IsLayer l m L₀ L₁) :
    shaInv L₁ l e = cokerLen (xTw l l (⊤ : Subgroup (G L₀ Ω)) e γ ^ l ^ m - 1) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L₀
  haveI : FiniteDimensional L₀ L₁ := Module.Finite.of_restrictScalars_finite ℚ L₀ L₁
  let j : L₁ →ₐ[L₀] Ω := IsAlgClosed.lift
  letI : Algebra L₁ Ω := j.toRingHom.toAlgebra
  haveI : IsScalarTower L₀ L₁ Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Algebra.IsAlgebraic L₀ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure L₁ Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := L₀) L₁⟩
  obtain ⟨D⟩ := Formalism.GaloisCohomology.ldataExists L₁ Ω l
  have hμ₁ : HasMuQ l L₁ := by
    obtain ⟨ζ, hζ⟩ := hμ
    exact ⟨_, hζ.map_of_injective (algebraMap L₀ L₁).injective⟩
  have hU := (layerUniq L₀ Ω l hμ).2.1 m L₁ hL
  obtain ⟨Φ, -⟩ := desc L₀ L₁ Ω l D e ⊤ he ((muQ L₁ Ω l).2.2.2.1 hμ₁).2 (by rw [hU, cycU_levU])
  have hg := ((layerGen L₀ Ω l hμ).2 γ hγ).2.2 m
  rw [← hU] at hg
  rw [← shaLen_eq_shaInv D, shaLen, Φ.length_eq, (shaDGen L₀ Ω l l ⊤ _ e _ isClosed_univ le_top hg).2, ← map_pow]
  exact (cokerDual l _ _ _ fun x φ => by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.sub_apply, map_sub, xTw_apply_apply]; rfl).symm

variable (l L₀ Ω) in

theorem exists_descends (hμ : HasMuQ l L₀) : ∃ γ : G L₀ Ω, IsGen l ⊤ γ ∧
    PropA.IsLevel l (cycZ L₀ Ω l γ : ℤ_[l]ˣ) (cZero l L₀) ∧ (∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ cZero l L₀)) ∧
    ∀ e : ℕ, 1 ≤ e → ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
      shaInv L₁ l e = cokerLen (xTw l l (⊤ : Subgroup (G L₀ Ω)) e γ ^ l ^ m - 1) := by
  obtain ⟨γ, hγ⟩ := (genGal L₀ L₀ Ω l).2.2 ((muQ L₀ Ω l).2.2.2.1 hμ).2
  rw [galOf_self] at hγ
  exact ⟨γ, hγ, ((layerGen L₀ Ω l hμ).2 γ hγ).1, ((muQ L₀ Ω l).1 _).2 le_rfl, fun e he m L₁ _ _ _ hL =>
    step0 hμ hγ (by omega) m L₁ hL⟩

variable (l L₀) in
theorem isTower_iff (R : ℕ) : IsTower l L₀ R ↔ HasMuQ l L₀ ∧ 1 ≤ R ∧ rankN l L₀ l ≤ R :=
  ⟨fun h => ⟨h.mu, h.pos, (genIff L₀ _ l l ⊤ R isClosed_univ).1 h.gen⟩, fun h =>
    ⟨((muQ L₀ (AlgebraicClosure L₀) l).2.2.2.1 h.1).1, h.1, h.2.1, (genIff L₀ _ l l ⊤ R isClosed_univ).2 h.2.2⟩⟩

theorem isTower_of_xRk (k : Type) [Field k] [NumberField k] [Algebra k L₀] [Algebra k Ω] [IsScalarTower k L₀ Ω]
    [IsAlgClosure k Ω] (hμ : HasMuQ l L₀) {R : ℕ} (hR : 1 ≤ R) {U : Subgroup (G k Ω)}
    (hU : cycU l U = cycU l (galOf k L₀ Ω)) (h : Two.XRk l 1 (cycU l U) R) : IsTower l L₀ R :=
  (isTower_iff l L₀ R).2 ⟨hμ, hR, by
    rw [← rankBase.1 k L₀ Ω l l U hU]
    exact (rankXRk k Ω l l U R).2 (h.of_one l)⟩

end Step0

end UpperTheory.V.Tower

end
