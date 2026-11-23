import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompletionEquivUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSphericalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BiInvScalar

open GlobalTheory.SphLabelOps GlobalTheory.HeckeScalarSph

theorem biInv_scalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (Ds : Set (GAf L n)), (∀ x ∈ Ds, TrivOutside {s.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → ∀ R : Finset (GAf L n), (∀ γ ∈ R, γ ∈ Ds) → (∀ x ∈ Ds, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  intro L _ _ _ n W _ _ ρ S hS s Ds hDt hDs R hRD hRu
  classical
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose Rb hRb using exists_repsU (L := L) (n := n) s.v
  let K := locK (L := L) n s.v
  let dc : GAf L n → Set (GAf L n) := fun a => {x | ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂}

  have hdcD : ∀ a ∈ Ds, ∀ x ∈ dc a, x ∈ Ds := by
    rintro a ha _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    exact (hDs _ (hDs a ha k₁ h₁.1 h₁.2).2 k₂ h₂.1 h₂.2).1
  have hdc_eq : ∀ a b, b ∈ dc a → dc b = dc a := by
    rintro a _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    ext x
    constructor
    · rintro ⟨l₁, i₁, l₂, i₂, rfl⟩
      exact ⟨l₁ * k₁, K.mul_mem i₁ h₁, k₂ * l₂, K.mul_mem h₂ i₂, by group⟩
    · rintro ⟨l₁, i₁, l₂, i₂, rfl⟩
      exact ⟨l₁ * k₁⁻¹, K.mul_mem i₁ (K.inv_mem h₁), k₂⁻¹ * l₂, K.mul_mem (K.inv_mem h₂) i₂, by group⟩
  have hself : ∀ a, a ∈ dc a := fun a => ⟨1, K.one_mem, 1, K.one_mem, by group⟩

  let fib : GAf L n → Finset (GAf L n) := fun a => R.filter (fun γ => dc γ = dc a)
  have hfib : ∀ α ∈ R, (∀ γ ∈ fib α, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂) ∧
      ∀ x, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ fib α ∧ γ⁻¹ * x ∈ Umax L n := by
    intro α hα
    refine ⟨fun γ hγ => ?_, fun x hx => ?_⟩
    · have e := (Finset.mem_filter.1 hγ).2
      have : γ ∈ dc α := e ▸ hself γ
      exact this
    · have hxD : x ∈ Ds := hdcD α (hRD α hα) x hx
      obtain ⟨γ, ⟨hγ, hu⟩, huniq⟩ := hRu x hxD
      have ht : TrivOutside {s.v} (γ⁻¹ * x) := triv_mul (triv_inv (hDt γ (hRD γ hγ))) (hDt x hxD)
      have hγdc : γ ∈ dc x := ⟨1, K.one_mem, (γ⁻¹ * x)⁻¹, K.inv_mem ⟨hu, ht⟩, by group⟩
      have e : dc γ = dc α := (hdc_eq x γ hγdc).trans (hdc_eq α x hx)
      exact ⟨γ, ⟨Finset.mem_filter.2 ⟨hγ, e⟩, hu⟩, fun δ hδ => huniq δ ⟨(Finset.mem_filter.1 hδ.1).1, hδ.2⟩⟩
  have hfibTriv : ∀ α ∈ R, TrivOutside {s.v} α := fun α hα => hDt α (hRD α hα)
  have conv : ∀ {b x : GAf L n}, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * b * k₂) ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * b * k₂ :=
    ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
      fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩

  have hsplit : ∀ (F : GAf L n → (GAf L n → W)), ∑ γ ∈ R, F γ = ∑ D ∈ R.image dc, ∑ γ ∈ R.filter (fun γ => dc γ = D), F γ :=
    fun F => (Finset.sum_fiberwise_of_maps_to (fun γ hγ => Finset.mem_image_of_mem dc hγ) F).symm
  have hD : ∀ D ∈ R.image dc, ∃ α ∈ R, R.filter (fun γ => dc γ = D) = fib α := by
    intro D hD
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hD
    exact ⟨α, hα, rfl⟩
  let T : (GAf L n → W) →ₗ[ℂ] (GAf L n → W) := ∑ γ ∈ R, rtHom L n W γ
  have hT : ∀ x, T x = ∑ γ ∈ R, rtHom L n W γ x := fun x => LinearMap.sum_apply _ _ _
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ GlobalTheory.SphScalar.fixS (rtHom L n W) S (locK n s.v), T x = c • x := by
    refine GlobalTheory.SphScalar.abs_scalar (rtHom L n W) S hS.1.stable
      (fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, hst⟩ hle) (rank_le hS) (locK n s.v)
      {x | TrivOutside {s.v} x} {y | TrivOutside {s.v}ᶜ y}
      (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩)
      (fun κ hκ b hb => (hcomm κ b hκ.2 hb).eq) Rb (fun b hb => reps_of_repsU hb (hRb b)) T ?_ ?_ ?_
    · intro x hx
      rw [hT]
      refine ⟨S.sum_mem fun γ _ => hS.1.stable γ x hx.1, fun κ hκ => ?_⟩
      rw [hsplit, map_sum]
      refine Finset.sum_congr rfl fun D hDm => ?_
      obtain ⟨α, hα, e⟩ := hD D hDm
      rw [e]
      have hRα := reps_of_repsU (hfibTriv α hα) (hfib α hα)
      rw [map_sum]
      have := hRα.sum_eq hRα hκ (fun g => rtHom L n W g x)
        (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
      simpa only [map_mul, Module.End.mul_apply] using this
    · intro b hb x _
      rw [hT, hT, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, (hcomm γ b (hfibTriv γ hγ) hb).eq]
    · intro b hb x hx
      rw [hT, hT]
      rw [hsplit (fun γ => rtHom L n W γ (∑ δ ∈ Rb b, rtHom L n W δ x)), hsplit (fun γ => rtHom L n W γ x)]
      refine Eq.trans ?_ ((Finset.sum_congr rfl fun δ _ => map_sum (rtHom L n W δ) _ _).trans Finset.sum_comm).symm
      refine Finset.sum_congr rfl fun D hDm => ?_
      obtain ⟨α, hα, e⟩ := hD D hDm
      rw [e]
      exact GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical L n W s α b (fib α) (Rb b) (hfibTriv α hα) hb (fun y hy => (hfib α hα).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hfib α hα).1 γ hγ)) (fun y hy => (hRb b).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hRb b).1 γ hγ)) x (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
  refine ⟨c, fun f hf hfix => ?_⟩
  have e := hc f ⟨hf, fun κ hκ => hfix κ hκ⟩
  rw [hT] at e
  exact e

end GlobalTheory.BiInvScalar

end
