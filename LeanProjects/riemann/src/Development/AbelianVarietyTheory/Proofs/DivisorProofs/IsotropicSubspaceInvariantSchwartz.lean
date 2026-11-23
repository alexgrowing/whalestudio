import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangiaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterConductorExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianCombinedIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSupportVanishingIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSubmoduleSupportClosedStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

open ValuativeRel

noncomputable section
namespace GlobalTheory.CoinvIrr

theorem std {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (ψ0 : AddChar k ℂ) (hc : Continuous ψ0)
    (hn : ∀ x : k, ‖ψ0 x‖ = 1) (h1 : ψ0 ≠ 1) (I : Set (Y × Y')) (S : Submodule ℂ (Matrix Y Y' k → ℂ))
    (hS : S ≤ GlobalTheory.WeilM.SB (Matrix Y Y' k))
    (hN : ∀ z : Matrix Y Y' k, (∀ r q, (r, q) ∉ I → z r q = 0) → ∀ φ ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k),
      (fun t => ψ0 (∑ r, ∑ q, t r q * z r q) * φ t) - φ ∈ S)
    (hT : ∀ x : Matrix Y Y' k, (∀ r q, (r, q) ∈ I → x r q = 0) → ∀ φ ∈ S, (fun t => φ (t + x)) ∈ S)
    (hM : ∀ z : Matrix Y Y' k, ∀ φ ∈ S, (fun t => ψ0 (∑ r, ∑ q, t r q * z r q) * φ t) ∈ S)
    (φ₀ : Matrix Y Y' k → ℂ) (h0 : φ₀ ∈ S)
    (hne : φ₀ ∉ Submodule.span ℂ {f | ∃ z : Matrix Y Y' k, (∀ r q, (r, q) ∉ I → z r q = 0) ∧
      ∃ φ' ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k), f = (fun t => ψ0 (∑ r, ∑ q, t r q * z r q) * φ' t) - φ'}) :
    S = GlobalTheory.WeilM.SB (Matrix Y Y' k) := by
  have hspan : Submodule.span ℂ {f | ∃ z : Matrix Y Y' k, (∀ r q, (r, q) ∉ I → z r q = 0) ∧
      ∃ φ' ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k), f = (fun t => ψ0 (∑ r, ∑ q, t r q * z r q) * φ' t) - φ'} ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro f ⟨z, hz, φ', hφ', rfl⟩
    exact hN z hz φ' hφ'
  obtain ⟨t₀, ht₀, hne'⟩ : ∃ t₀ : Matrix Y Y' k, (∀ r q, (r, q) ∈ I → t₀ r q = 0) ∧ φ₀ t₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (GlobalTheory.T.schwartz_support_vanishing_ideal ψ0 hc hn h1 I φ₀ (hS h0) hcon)
  exact GlobalTheory.T.schwartz_submodule_support_closed ψ0 hc hn h1 I S hS (fun φ hφ hv => hspan (GlobalTheory.T.schwartz_support_vanishing_ideal ψ0 hc hn h1 I φ hφ hv)) hT hM φ₀ h0 t₀ ht₀ hne'

theorem coinvariants_irreducible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ U : Submodule k ((κ → k) × (κ → k)), (∀ u ∈ U, ∀ u' ∈ U, u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 = 0) →
    ∀ S : Submodule ℂ ((κ → k) → ℂ), S ≤ GlobalTheory.WeilM.SB (κ → k) →
    (∀ u ∈ U, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 u φ - φ ∈ S) →
    (∀ w : (κ → k) × (κ → k), (∀ u ∈ U, u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2 = 0) → ∀ φ ∈ S, GlobalTheory.WeilM.schr ψ0 w φ ∈ S) →
    ∀ φ₀ ∈ S, φ₀ ∉ Submodule.span ℂ {f | ∃ u ∈ U, ∃ φ ∈ GlobalTheory.WeilM.SB (κ → k), f = GlobalTheory.WeilM.schr ψ0 u φ - φ} →
    S = GlobalTheory.WeilM.SB (κ → k) := by
  intro k _ _ _ _ _ _ κ _ ψ0 hψc hψ1 U hU S hS hN hstab φ₀ h0 hne
  obtain ⟨c, hc0, hcond⟩ := GlobalTheory.T.local_character_conductor_exists ψ0 hψc hψ1
  have hnorm := GlobalTheory.T.local_character_unitary ψ0 hψc
  let ψc : AddChar k ℂ := ψ0.compAddMonoidHom (AddMonoidHom.mulLeft c)
  have hψcapp : ∀ t, ψc t = ψ0 (c * t) := fun t => rfl
  let σl : ((κ → k) × (κ → k)) →ₗ[k] ((κ → k) × (κ → k)) :=
    LinearMap.prodMap LinearMap.id (c⁻¹ • LinearMap.id)
  let τl : ((κ → k) × (κ → k)) →ₗ[k] ((κ → k) × (κ → k)) :=
    LinearMap.prodMap LinearMap.id (c • LinearMap.id)
  have hσ : ∀ w, σl w = (w.1, c⁻¹ • w.2) := fun w => rfl
  have hτ : ∀ w, τl w = (w.1, c • w.2) := fun w => rfl
  have hτσ : ∀ w, τl (σl w) = w := fun w => by
    rw [hσ, hτ]; ext <;> simp [mul_inv_cancel_left₀ hc0]
  have hkey : ∀ v φ, GlobalTheory.WeilM.schr ψ0 (τl v) φ = GlobalTheory.WeilM.schr ψc v φ := by
    intro v φ
    funext x
    simp only [GlobalTheory.WeilM.schr, hτ, hψcapp, dotProduct_smul, smul_eq_mul]
    congr 2
    ring
  have hBτ : ∀ u v : (κ → k) × (κ → k), u.1 ⬝ᵥ (τl v).2 - (τl v).1 ⬝ᵥ u.2 =
      c * ((σl u).1 ⬝ᵥ v.2 - v.1 ⬝ᵥ (σl u).2) := by
    intro u v
    simp only [hσ, hτ, dotProduct_smul, smul_eq_mul]
    first | (field_simp; done) | (field_simp; ring)
  let U' : Submodule k ((κ → k) × (κ → k)) := U.map σl
  have hU' : ∀ u ∈ U', ∀ u' ∈ U', u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 = 0 := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hU a ha b hb
    simp only [hσ, dotProduct_smul, smul_eq_mul]
    linear_combination c⁻¹ * this
  obtain ⟨n, wT, wM, I, hTT, hMM, hTM, hspan, hUiff⟩ := GlobalTheory.T.lagrangian_combined_isotropic U' hU'
  let e : Matrix (Fin n) (Fin 1) k →+ (Fin n → k) :=
    { toFun := fun Y i => Y i 0, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have he : ∀ Y : Matrix (Fin n) (Fin 1) k, ∀ i, e Y i = Y i 0 := fun _ _ => rfl
  let wT' : Matrix (Fin n) (Fin 1) k →+ (κ → k) × (κ → k) := wT.toAddMonoidHom.comp e
  let wM' : Matrix (Fin n) (Fin 1) k →+ (κ → k) × (κ → k) := wM.toAddMonoidHom.comp e
  have hwT : ∀ Y, wT' Y = wT (e Y) := fun _ => rfl
  have hwM : ∀ Y, wM' Y = wM (e Y) := fun _ => rfl
  have hsum : ∀ Y z : Matrix (Fin n) (Fin 1) k, ∑ i, ∑ j, Y i j * z i j = e Y ⬝ᵥ e z := by
    intro Y z
    simp [dotProduct, Fin.sum_univ_one, he]
  have hψcc : Continuous ψc := hψc.comp (continuous_const.mul continuous_id)
  have hcond' : ∀ x : k, (∀ y ∈ 𝒪[k], ψc (x * y) = 1) ↔ x ∈ 𝒪[k] := fun x => by
    simp only [hψcapp]; exact hcond x
  obtain ⟨ι, hbij, hιT, hιM⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians (n := n) (d := 1) ψc hψcc hcond' wT' wM'
    (fun Y Y' => by rw [hwT, hwT]; exact hTT _ _) (fun z z' => by rw [hwM, hwM]; exact hMM _ _)
    (fun Y z => by rw [hwT, hwM, hsum]; exact hTM _ _)
    (fun w => by
      obtain ⟨Y, z, h⟩ := hspan w
      exact ⟨Matrix.of fun i _ => Y i, Matrix.of fun i _ => z i, h⟩)

  have hτU : ∀ z : Fin n → k, (∀ i ∉ I, z i = 0) → τl (wM z) ∈ U := by
    intro z hz
    obtain ⟨u, hu, hσu⟩ := (Submodule.mem_map).1 ((hUiff _).2 ⟨z, hz, rfl⟩)
    rw [← hσu, hτσ]
    exact hu
  have hσU : ∀ u ∈ U, ∃ z : Fin n → k, (∀ i ∉ I, z i = 0) ∧ wM z = σl u := fun u hu =>
    (hUiff _).1 (Submodule.mem_map_of_mem hu)
  let I' : Set (Fin n × Fin 1) := {p | p.1 ∈ I}
  have hperpM : ∀ z, ∀ u ∈ U, u.1 ⬝ᵥ (τl (wM' z)).2 - (τl (wM' z)).1 ⬝ᵥ u.2 = 0 := by
    intro z u hu
    obtain ⟨z0, -, hz0⟩ := hσU u hu
    rw [hBτ, ← hz0, hwM, hMM, mul_zero]
  have hperpT : ∀ x : Matrix (Fin n) (Fin 1) k, (∀ r q, (r, q) ∈ I' → x r q = 0) →
      ∀ u ∈ U, u.1 ⬝ᵥ (τl (wT' x)).2 - (τl (wT' x)).1 ⬝ᵥ u.2 = 0 := by
    intro x hx u hu
    obtain ⟨z0, hz0I, hz0⟩ := hσU u hu
    rw [hBτ, ← hz0, hwT]
    have h2 := hTM (e x) z0
    have h3 : e x ⬝ᵥ z0 = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : i ∈ I
      · rw [he, hx i 0 hi, zero_mul]
      · rw [hz0I i hi, mul_zero]
    rw [h3] at h2
    linear_combination (-c) * h2
  have hgen : ∀ z : Matrix (Fin n) (Fin 1) k, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k),
      ι (GlobalTheory.WeilM.schr ψ0 (τl (wM' z)) φ - φ) =
        (fun t => ψc (∑ r, ∑ q, t r q * z r q) * ι φ t) - ι φ := by
    intro z φ hφ
    rw [map_sub, hkey, hιM z φ hφ]
  have hNU : Submodule.span ℂ {f | ∃ u ∈ U, ∃ φ ∈ GlobalTheory.WeilM.SB (κ → k), f = GlobalTheory.WeilM.schr ψ0 u φ - φ} ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro f ⟨u, hu, φ, hφ, rfl⟩
    exact hN u hu φ hφ
  have hT_eq : Submodule.map ι S = GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin 1) k) := by
    refine std ψc hψcc (fun x => by rw [hψcapp]; exact hnorm _) ?_ I' (Submodule.map ι S) ?_ ?_ ?_ ?_ (ι φ₀)
      (Submodule.mem_map_of_mem h0) ?_
    · intro h
      apply hψ1
      ext t
      have := DFunLike.congr_fun h (c⁻¹ * t)
      rw [hψcapp, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at this
      simpa using this
    · rintro _ ⟨φ, hφ, rfl⟩
      exact hbij.mapsTo (hS hφ)
    · intro z hz φ' hφ'
      obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hφ'
      refine ⟨_, hN _ (hτU (e z) fun i hi => hz i 0 hi) φ hφ, ?_⟩
      exact hgen z φ hφ
    · rintro x hx _ ⟨φ, hφ, rfl⟩
      refine ⟨_, hstab _ (hperpT x hx) φ hφ, ?_⟩
      show ι (GlobalTheory.WeilM.schr ψ0 (τl (wT' x)) φ) = _
      rw [hkey, hιT x φ (hS hφ)]
    · rintro z _ ⟨φ, hφ, rfl⟩
      refine ⟨_, hstab _ (hperpM z) φ hφ, ?_⟩
      show ι (GlobalTheory.WeilM.schr ψ0 (τl (wM' z)) φ) = _
      rw [hkey, hιM z φ (hS hφ)]
    · intro hmem
      have hle : Submodule.span ℂ {f | ∃ z : Matrix (Fin n) (Fin 1) k, (∀ r q, (r, q) ∉ I' → z r q = 0) ∧
          ∃ φ' ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin 1) k),
            f = (fun t => ψc (∑ r, ∑ q, t r q * z r q) * φ' t) - φ'} ≤
          Submodule.map ι (Submodule.span ℂ {f | ∃ u ∈ U, ∃ φ ∈ GlobalTheory.WeilM.SB (κ → k),
            f = GlobalTheory.WeilM.schr ψ0 u φ - φ}) := by
        refine Submodule.span_le.mpr ?_
        rintro f ⟨z, hz, φ', hφ', rfl⟩
        obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hφ'
        exact ⟨_, Submodule.subset_span ⟨_, hτU (e z) (fun i hi => hz i 0 hi), φ, hφ, rfl⟩, hgen z φ hφ⟩
      obtain ⟨m, hm, hιm⟩ := hle hmem
      have := hbij.injOn (hS (hNU hm)) (hS h0) hιm
      exact hne (this ▸ hm)
  refine le_antisymm hS fun φ hφ => ?_
  have hmem : ι φ ∈ Submodule.map ι S := hT_eq ▸ hbij.mapsTo hφ
  obtain ⟨s, hs, hιs⟩ := hmem
  have := hbij.injOn (hS hs) hφ hιs
  exact this ▸ hs

end GlobalTheory.CoinvIrr
