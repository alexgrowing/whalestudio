import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.TransExists

open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.FoldDCUnfold.W

universe u

theorem translation_exists : TransExists.{u} := by
  intro G _ K H hHK
  classical
  obtain ⟨rep, hrepdef⟩ : ∃ rep : G → G,
      ∀ γ, rep γ = (Quotient.mk (QuotientGroup.rightRel H) γ).out := ⟨_, fun _ => rfl⟩
  have hrep : ∀ γ, γ * (rep γ)⁻¹ ∈ H := fun γ => by
    rw [hrepdef]
    exact QuotientGroup.rightRel_apply.mp
      (Quotient.exact (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel H) γ)))
  have hrep_eq : ∀ γ γ', γ * γ'⁻¹ ∈ H → rep γ = rep γ' := fun γ γ' h => by
    rw [hrepdef, hrepdef]
    congr 1
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simpa using H.inv_mem h))
  have hrepK : ∀ γ ∈ K, rep γ ∈ K := fun γ hγ => by
    have h1 : rep γ = (γ * (rep γ)⁻¹)⁻¹ * γ := by group
    rw [h1]
    exact K.mul_mem (K.inv_mem (hHK (hrep γ))) hγ
  refine ⟨rep '' (K : Set G), ?_, ?_⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    exact hrepK γ hγ
  · intro γ hγ
    refine ⟨(⟨γ * (rep γ)⁻¹, hrep γ⟩, ⟨rep γ, γ, hγ, rfl⟩), by simp, ?_⟩
    rintro ⟨⟨s, hs⟩, ⟨e, ⟨γ', hγ', rfl⟩⟩⟩ he
    have he' : s * rep γ' = γ := he
    have h1 : rep γ' = rep γ := by
      have h2 : rep (rep γ') = rep γ' :=
        hrep_eq _ _ (by simpa using H.inv_mem (hrep γ'))
      rw [← h2]
      apply hrep_eq
      rw [← he']
      simpa using H.inv_mem hs
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show s = γ * (rep γ)⁻¹
      calc s = s * rep γ' * (rep γ')⁻¹ := by group
        _ = γ * (rep γ)⁻¹ := by rw [he', h1]
    · exact h1

theorem translation_independent : TransIndep.{u} := by
  intro G _ Γ H T T' hT hT' c hc f hf
  classical
  have hmem : ∀ η : T, (η : G) * c ∈ Γ := fun η => Γ.mul_mem (hT.1 η.2) hc
  choose φ hφ using fun η : T => (hT'.2 _ (hmem η)).exists
  have hfeq : ∀ η : T, f ((η : G) * c) = f ((φ η).2 : G) := fun η => by
    rw [← hφ η, hf _ (φ η).1.2]
  have hinj : Function.Injective (fun η => (φ η).2) := by
    intro η₁ η₂ h12
    have h12' : (φ η₁).2 = (φ η₂).2 := h12
    have e1 : ((φ η₁).1 : G) * ((φ η₂).2 : G) = η₁ * c := by rw [← h12']; exact hφ η₁
    have e2 : ((φ η₂).1 : G) * ((φ η₂).2 : G) = η₂ * c := hφ η₂
    have hk : (((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹) * η₁ = η₂ := by
      calc (((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹) * η₁
          = ((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹ * (η₁ * c) * c⁻¹ := by group
        _ = ((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹ * (((φ η₁).1 : G) * ((φ η₂).2 : G)) * c⁻¹ := by
          rw [e1]
        _ = (((φ η₂).1 : G) * ((φ η₂).2 : G)) * c⁻¹ := by group
        _ = η₂ * c * c⁻¹ := by rw [e2]
        _ = η₂ := by group
    have hu := (hT.2 (η₂ : G) (hT.1 η₂.2)).unique
      (y₁ := ((1 : H), η₂)) (y₂ := (⟨((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹,
        H.mul_mem (φ η₂).1.2 (H.inv_mem (φ η₁).1.2)⟩, η₁)) (by simp) hk
    exact (congrArg Prod.snd hu).symm
  have hsurj : Function.Surjective (fun η => (φ η).2) := by
    intro η'
    have hm : (η' : G) * c⁻¹ ∈ Γ := Γ.mul_mem (hT'.1 η'.2) (Γ.inv_mem hc)
    obtain ⟨⟨s, η⟩, hsη, -⟩ := hT.2 _ hm
    have hsη' : (s : G) * η = η' * c⁻¹ := hsη
    refine ⟨η, ?_⟩
    have hy : ((s : G))⁻¹ * η' = η * c := by
      have : (η : G) = (s : G)⁻¹ * (η' * c⁻¹) := by rw [← hsη']; group
      rw [this]
      group
    have hu := (hT'.2 _ (hmem η)).unique (hφ η)
      (y₂ := (⟨(s : G)⁻¹, H.inv_mem s.2⟩, η')) hy
    exact congrArg Prod.snd hu
  calc ∑' η : T, f ((η : G) * c) = ∑' η : T, f ((φ η).2 : G) := tsum_congr hfeq
    _ = ∑' η' : T', f η' :=
      Equiv.tsum_eq (Equiv.ofBijective (fun η => (φ η).2) ⟨hinj, hsurj⟩) (fun η' : T' => f η')

theorem translation_product : TransProd.{u} := by
  intro G _ Γ S H E D hHS hSΓ hE hD
  have key : ∀ (e₁ e₂ : E) (d₁ d₂ : D), (e₁ : G) * d₁ = e₂ * d₂ → e₁ = e₂ ∧ d₁ = d₂ := by
    intro e₁ e₂ d₁ d₂ h
    have hγ : (e₁ : G) * d₁ ∈ Γ := Γ.mul_mem (hSΓ (hE.1 e₁.2)) (hD.1 d₁.2)
    have u := (hD.2 _ hγ).unique (y₁ := (⟨e₁, hE.1 e₁.2⟩, d₁)) (y₂ := (⟨e₂, hE.1 e₂.2⟩, d₂))
      rfl h.symm
    have hd : d₁ = d₂ := congrArg Prod.snd u
    have he : (e₁ : G) = e₂ := congrArg (fun p : S × D => ((p.1 : S) : G)) u
    exact ⟨Subtype.ext he, hd⟩
  refine ⟨fun p q h => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := key p.1 q.1 p.2 q.2 h
    exact Prod.ext h1 h2
  · rintro _ ⟨p, rfl⟩
    exact Γ.mul_mem (hSΓ (hE.1 p.1.2)) (hD.1 p.2.2)
  · intro γ hγ
    obtain ⟨⟨s, d⟩, hsd, hsd_u⟩ := hD.2 γ hγ
    obtain ⟨⟨h, e⟩, hhe, hhe_u⟩ := hE.2 s s.2
    have hsd' : (s : G) * d = γ := hsd
    have hhe' : (h : G) * e = s := hhe
    refine ⟨(h, ⟨(e : G) * d, ⟨(e, d), rfl⟩⟩), ?_, ?_⟩
    · show (h : G) * ((e : G) * d) = γ
      rw [← mul_assoc, hhe']
      exact hsd'
    · rintro ⟨h', ⟨x, ⟨⟨e', d'⟩, rfl⟩⟩⟩ hx
      have hx' : (h' : G) * ((e' : G) * d') = γ := hx
      have hs' : (h' : G) * e' ∈ S := S.mul_mem (hHS h'.2) (hE.1 e'.2)
      have u1 := hsd_u (⟨(h' : G) * e', hs'⟩, d')
        (by show (h' : G) * e' * d' = γ; rw [mul_assoc]; exact hx')
      have hd' : d' = d := congrArg Prod.snd u1
      have hs1 : (h' : G) * e' = s := congrArg (fun p : S × D => ((p.1 : S) : G)) u1
      have u2 := hhe_u (h', e') hs1
      have hh : h' = h := congrArg Prod.fst u2
      have he : e' = e := congrArg Prod.snd u2
      subst hd' hh he
      rfl

end PI.FoldDCUnfold.W
