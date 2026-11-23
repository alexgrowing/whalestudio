import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.TameInertiaTowers.TowerFieldFoundations

open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Frob

theorem frob_mul_inertia {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]
    [SMulCommClass G ℤ S] (Q : Ideal S) (ρ τ : G) (hρ : ρ ∈ Q.inertia G)
    (hτ : IsArithFrobAt ℤ τ Q) : IsArithFrobAt ℤ (ρ * τ) Q := by
  intro x
  have h1 : ρ • (τ • x) - τ • x ∈ Q := hρ (τ • x)
  have h2 := hτ x
  try simp only [MulSemiringAction.toAlgHom_apply] at h2 ⊢
  rw [mul_smul]
  have h3 := Q.add_mem h1 h2
  rwa [sub_add_sub_cancel] at h3

end Frob

theorem hostFrob_of (hGal : HostGalois) (hSpec : HostGalSpec) : HostFrob := by
  intro e q d hqd L _ _ ζ a b h p _ hp2 hpq hpd P _ _
  obtain ⟨hEgal, -, hmulE, hbijE⟩ := hGal e q d hqd L ζ a b h
  obtain ⟨hLgal, -, hmulL, hbijL⟩ := layerGalois (e + 2) q d (by omega) hqd L ζ a b h
  have := hEgal
  have := hLgal
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
  have : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P (span {(p : ℤ)})
  have hFr := layerFrob (e + 2) q d (by omega) hqd L ζ a b h p hp2 hpq hpd Q
  obtain ⟨⟨τ, hτ⟩, hτspec⟩ := hFr
  obtain ⟨hτ1, hτ2, hτ3⟩ := (hτspec τ).mp hτ

  have hgm1 : galMap h.1 a b (1 : Gal(L/ℚ)) = 1 := by
    have := hmulL 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)

  have hIQ : ∀ ρ ∈ Q.inertia Gal(L/ℚ), ρ = 1 := by
    intro ρ hρ
    have hF := Frob.frob_mul_inertia Q ρ τ hρ hτ
    obtain ⟨h1, h2, h3⟩ := (hτspec (ρ * τ)).mp hF
    have heq : galMap h.1 a b (ρ * τ) = galMap h.1 a b τ := by
      refine Prod.ext (Units.ext (h1.trans hτ1.symm)) (Prod.ext ?_ ?_)
      · exact Units.ext (h2.trans hτ2.symm)
      · exact Units.ext (h3.trans hτ3.symm)
    rw [hmulL, mul_eq_right] at heq
    exact hbijL.1 (heq.trans hgm1.symm)
  have heQ : Q.ramificationIdx ℤ = 1 := by
    rw [← odd_card L p Q]
    have : Q.inertia Gal(L/ℚ) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hIQ
    rw [this]
    simp
  have heP : P.ramificationIdx ℤ = 1 := by
    have hte := Ideal.ramificationIdx_tower (R := ℤ) P Q
    rw [heQ] at hte
    exact Nat.eq_one_of_mul_eq_one_right hte.symm
  have hIP : ∀ σ ∈ P.inertia Gal(hostE ζ a b/ℚ), σ = 1 := by
    have hc := odd_card (hostE ζ a b) p P
    rw [heP, Nat.card_eq_one_iff_unique] at hc
    intro σ hσ
    have : (⟨σ, hσ⟩ : P.inertia Gal(hostE ζ a b/ℚ)) = ⟨1, one_mem _⟩ := hc.1.elim _ _
    exact congrArg Subtype.val this

  let σ₀ : Gal(hostE ζ a b/ℚ) := τ.restrictNormal (hostE ζ a b)
  have hσ₀ : ∀ x : hostE ζ a b, ((σ₀ x : hostE ζ a b) : L) = τ x :=
    fun x => AlgEquiv.restrictNormal_commutes τ (hostE ζ a b) x
  have hσ₀F : IsArithFrobAt ℤ σ₀ P := by
    intro x
    have hx := hτ (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x)
    rw [odd_card_under p Q] at hx
    rw [odd_card_under p P]
    rw [Ideal.over_def Q P, Ideal.under_def, Ideal.mem_comap]
    convert hx using 1
    apply RingOfIntegers.coe_injective
    simp only [map_sub, map_pow, MulSemiringAction.toAlgHom_apply]
    congr 1
    show (((σ₀ • x : 𝓞 (hostE ζ a b)) : hostE ζ a b) : L) =
      τ (((x : 𝓞 (hostE ζ a b)) : hostE ζ a b) : L)
    exact hσ₀ x
  have hval := (hSpec e q d hqd L ζ a b h σ₀).2.2.2 τ hσ₀
  have hgalE1 : galE e ζ a b (1 : Gal(hostE ζ a b/ℚ)) = 1 := by
    have := hmulE 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have huniq : ∀ σ : Gal(hostE ζ a b/ℚ), IsArithFrobAt ℤ σ P → σ = σ₀ := by
    intro σ hσ
    have := hIP _ (hσ.mul_inv_mem_inertia hσ₀F)
    exact mul_inv_eq_one.mp this
  refine ⟨⟨σ₀, hσ₀F⟩, fun σ => ⟨fun hσ => ?_, fun hs => ?_⟩, fun σ => ⟨fun hσ => ?_, fun hσ => ?_⟩⟩
  · rw [huniq σ hσ, hval]
    exact ⟨hτ2, hτ3, (galMap h.1 a b τ).1, hτ1, rfl⟩
  · obtain ⟨s1, s2, u, hu, hu2⟩ := hs
    have : σ = σ₀ := by
      apply hbijE.1
      rw [hval]
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · exact Units.ext (s1.trans hτ2.symm)
      · exact Units.ext (s2.trans hτ3.symm)
      · rw [hu2]
        exact congrArg (hcl e) (Units.ext (hu.trans hτ1.symm))
    rw [this]
    exact hσ₀F
  · exact hIP σ (AddSubgroup.mem_inertia.mpr hσ)
  · subst hσ
    intro x
    simp

end Formalism.FrobeniusOrbits
