import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsNoetherianModelOfSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreGoingDownTensorStatement
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NzdDescent

open TensorProduct GlobalTheory.SmoothDescent

theorem model_data (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B] (b g : B) :
    ∃ (S B₁ : Type) (_ : CommRing S) (_ : IsNoetherianRing S) (_ : Algebra S A) (_ : CommRing B₁)
      (_ : Algebra S B₁) (_ : Algebra.Smooth S B₁) (e : A ⊗[S] B₁ ≃ₐ[A] B) (b₁ g₁ : B₁),
      Function.Injective (fun x : B₁ => e (1 ⊗ₜ x)) ∧ e (1 ⊗ₜ b₁) = b ∧ e (1 ⊗ₜ g₁) = g := by
  classical
  obtain ⟨A₀, B₀, _, _, h₀, hB, ⟨β⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A B
  haveI : IsNoetherianRing A₀ := isNoetherianRing_of_fg h₀
  obtain ⟨S, hS, hsub⟩ := exists_fg_subset_range_incl (C₁ := B₀) ({β b, β g} : Finset _)
  obtain ⟨b₁, hb₁⟩ := hsub (by simp : β b ∈ _)
  obtain ⟨g₁, hg₁⟩ := hsub (by simp : β g ∈ _)
  refine ⟨S, S ⊗[A₀] B₀, inferInstance, isNoetherianRing_of_fg hS, inferInstance, inferInstance,
    inferInstance, inferInstance,
    (Algebra.TensorProduct.cancelBaseChange A₀ S A A B₀).trans β.symm, b₁, g₁, ?_, ?_, ?_⟩
  · intro x y h
    simp only [AlgEquiv.trans_apply, cancel_one_tmul] at h
    exact incl_injective S (β.symm.injective h)
  · simp only [AlgEquiv.trans_apply, cancel_one_tmul]
    exact (congrArg β.symm hb₁).trans (β.symm_apply_apply b)
  · simp only [AlgEquiv.trans_apply, cancel_one_tmul]
    exact (congrArg β.symm hg₁).trans (β.symm_apply_apply g)

theorem of_model (hN : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0)) (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    (S B₁ : Type) (b g : B) [CommRing S] [IsNoetherianRing S] [Algebra S A] [CommRing B₁] [Algebra S B₁]
    [Algebra.Smooth S B₁] (e : A ⊗[S] B₁ ≃ₐ[A] B) (b₁ g₁ : B₁)
    (hinj : Function.Injective (fun x : B₁ => e (1 ⊗ₜ x))) (hb : e (1 ⊗ₜ b₁) = b) (hg : e (1 ⊗ₜ g₁) = g)
    (u : PrimeSpectrum B) (hgb : g * b = 0)
    (hmin : ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q) :
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  let ι : B₁ →+* B := e.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight : B₁ →ₐ[S] A ⊗[S] B₁).toRingHom
  have hι : ∀ x, ι x = e (1 ⊗ₜ x) := fun x => rfl
  have hιS : ∀ s : S, ι (algebraMap S B₁ s) = algebraMap A B (algebraMap S A s) := by
    intro s
    rw [hι, ← Algebra.TensorProduct.tmul_one_eq_one_tmul, ← Algebra.TensorProduct.algebraMap_apply,
      IsScalarTower.algebraMap_apply S A (A ⊗[S] B₁), AlgEquiv.commutes]
  have hgb₁ : g₁ * b₁ = 0 := by
    apply hinj
    show ι (g₁ * b₁) = ι 0
    rw [map_mul, hι, hι, hg, hb, hgb, map_zero]
  let u₁ : PrimeSpectrum B₁ := ⟨u.asIdeal.comap ι, Ideal.comap_isPrime _ _⟩
  have key := hN S B₁ b₁ g₁ u₁ hgb₁ ?_
  · obtain ⟨⟨t, ht⟩, htb⟩ := (IsLocalization.map_eq_zero_iff u₁.asIdeal.primeCompl _ b₁).mp key
    refine (IsLocalization.map_eq_zero_iff u.asIdeal.primeCompl _ b).mpr ⟨⟨ι t, ht⟩, ?_⟩
    show ι t * b = 0
    rw [← hb, ← hι, ← map_mul]
    simp only at htb
    rw [htb, map_zero]
  intro Q₁ hQ₁ hQ₁u hgQ₁
  haveI : Q₁.IsPrime := hQ₁.1.1
  let uT : Ideal (A ⊗[S] B₁) := u.asIdeal.comap e.toAlgHom.toRingHom
  haveI : uT.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨QT, hQTp, hQTu, hQT1, hQTA⟩ := GlobalTheory.T.exists_prime_le_comap_of_goingDown_tensor S A B₁ uT Q₁ (fun x hx => hQ₁u hx) (by
    apply le_antisymm
    · intro s hs
      have : algebraMap S B₁ s ∈ u₁.asIdeal := hQ₁u hs
      show e (algebraMap S (A ⊗[S] B₁) s) ∈ u.asIdeal
      rw [← (Algebra.TensorProduct.includeRight : B₁ →ₐ[S] A ⊗[S] B₁).commutes]
      exact this
    · intro s hs
      apply hQ₁.1.2
      apply Ideal.mem_map_of_mem
      show ι (algebraMap S B₁ s) ∈ u.asIdeal
      have : e (algebraMap S (A ⊗[S] B₁) s) ∈ u.asIdeal := hs
      rwa [← (Algebra.TensorProduct.includeRight : B₁ →ₐ[S] A ⊗[S] B₁).commutes] at this)
  let Q' : Ideal B := QT.comap e.symm.toAlgHom.toRingHom
  haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hQ'u : Q' ≤ u.asIdeal := by
    intro x hx
    have := hQTu hx
    simpa [uT] using this
  have hmap : (u.asIdeal.comap (algebraMap A B)).map (algebraMap A B) ≤ Q' := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have h1 : a ∈ uT.comap (algebraMap A (A ⊗[S] B₁)) := by
      show e (algebraMap A _ a) ∈ u.asIdeal
      rw [AlgEquiv.commutes]; exact ha
    rw [← hQTA] at h1
    show e.symm (algebraMap A B a) ∈ QT
    rw [AlgEquiv.commutes]; exact h1
  obtain ⟨Q, hQmin, hQQ'⟩ := Ideal.exists_minimalPrimes_le hmap
  apply hmin Q hQmin (hQQ'.trans hQ'u)
  haveI : Q.IsPrime := hQmin.1.1
  have hJ : Q₁ ≤ Q.comap ι := by
    refine hQ₁.2 ⟨Ideal.comap_isPrime _ _, ?_⟩ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro s hs
      show ι (algebraMap S B₁ s) ∈ Q
      rw [hιS]
      apply hQmin.1.2
      apply Ideal.mem_map_of_mem
      show algebraMap A B (algebraMap S A s) ∈ u.asIdeal
      rw [← hιS]; exact hs
    · intro x hx
      rw [← hQT1]
      have := hQQ' hx
      have h2 : e.symm (e (1 ⊗ₜ x)) ∈ QT := this
      rw [AlgEquiv.symm_apply_apply] at h2
      exact h2
  have := hJ hgQ₁
  rw [← hg]; exact this

theorem of_noetherian : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0) →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  intro hN A B _ _ _ _ b g u hgb hmin
  obtain ⟨S, B₁, _, _, _, _, _, _, e, b₁, g₁, hinj, hb, hg⟩ := model_data A B b g
  exact of_model hN A B S B₁ b g e b₁ g₁ hinj hb hg u hgb hmin

end GlobalTheory.NzdDescent
