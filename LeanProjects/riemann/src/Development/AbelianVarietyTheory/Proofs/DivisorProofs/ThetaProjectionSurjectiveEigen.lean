import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionEigenImageStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem projEigenspaceEquiv (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type)
    [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (σ : Λ →+* O) (f : RL p O Λ →+* O)
    (ρ : Λ → Matrix (Fin h) (Fin h) (Ainf p O))
    (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O))
    (π : (Fin h → C) →ₗ[C] (Fin N → C)) :
    Function.Injective (algebraMap O C) → Function.Surjective (WittVector.fontaineTheta O p) →
    Function.Surjective f → IsTheta σ f → IsFrame ρ e → IsProj C e f π →
    (⨆ s : Λ →+* O, eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s) = ⊤ →
    Module.finrank C (eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ) = N →
    ∃ q : eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ ≃ₗ[C] (Fin N → C),
      (∀ x, q x = π x) ∧ ∀ x, x ∈ quotLattice C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ ↔
        ∀ i, q x i ∈ (algebraMap O C).range := by
  intro hinj hθ hf hth hfr hpr hsup hrank
  have hkill : ∀ z ∈ ⨆ s : {s : Λ →+* O // s ≠ σ},
      eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1, π z = 0 :=
    GlobalTheory.T.theta_projection_eigen_image p O C Λ N h σ f ρ e π hinj hth hfr hpr
  have hdec : ∀ z : Fin h → C, ∃ x ∈ eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ,
      ∃ z' ∈ ⨆ s : {s : Λ →+* O // s ≠ σ},
        eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1, x + z' = z := by
    intro z
    have hsplit : (⨆ s : Λ →+* O, eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s) =
        eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ ⊔
          ⨆ s : {s : Λ →+* O // s ≠ σ},
            eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1 := by
      rw [iSup_split_single _ σ, iSup_subtype']
    have hz : z ∈ eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ ⊔
          ⨆ s : {s : Λ →+* O // s ≠ σ},
            eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1 := by
      rw [← hsplit, hsup]; trivial
    exact Submodule.mem_sup.mp hz
  have hπsurj : Function.Surjective π := by
    obtain ⟨r, hr⟩ := hf 1
    have hs : ∀ i : Fin N, Pi.single i (1 : C) ∈ LinearMap.range π := by
      intro i
      refine ⟨fun j => algebraMap O C (WittVector.fontaineTheta O p (e (Pi.single i r) j)), ?_⟩
      rw [hpr]
      ext k
      by_cases hk : k = i
      · subst hk; simp [hr]
      · simp [Pi.single_apply, hk]
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun C (Fin N)).span_eq,
      Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simpa using hs i
  let π₀ : eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ →ₗ[C] (Fin N → C) :=
    π ∘ₗ (eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ).subtype
  have hsurj : Function.Surjective π₀ := by
    intro v
    obtain ⟨z, rfl⟩ := hπsurj v
    obtain ⟨x, hx, z', hz', rfl⟩ := hdec z
    exact ⟨⟨x, hx⟩, by simp [π₀, map_add, hkill z' hz']⟩
  have hinj0 : Function.Injective π₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hrank, Module.finrank_fin_fun])).mpr hsurj
  let q := LinearEquiv.ofBijective π₀ ⟨hinj0, hsurj⟩
  have hq : ∀ x, q x = π x := fun x => rfl
  refine ⟨q, hq, fun x => ?_⟩
  simp only [quotLattice, Set.mem_setOf_eq, RingHom.mem_range, hq]
  constructor
  · rintro ⟨t, ht⟩
    have hlift : ∀ j, ∃ a : Ainf p O, WittVector.fontaineTheta O p a = t j := fun j => hθ (t j)
    choose a ha using hlift
    have h1 : π (fun j => algebraMap O C (t j)) = fun i => algebraMap O C (f (e.symm a i)) := by
      have := hpr (e.symm a)
      simpa [ha] using this
    have h2 := hkill _ ht
    rw [map_sub, sub_eq_zero, h1] at h2
    intro i
    exact ⟨f (e.symm a i), by rw [← h2]⟩
  · intro hx
    choose c hc using hx
    have hlift : ∀ i, ∃ r, f r = c i := fun i => hf (c i)
    choose w hw using hlift
    refine ⟨fun j => WittVector.fontaineTheta O p (e w j), ?_⟩
    obtain ⟨x', hx', z', hz', hsum⟩ :=
      hdec (fun j => algebraMap O C (WittVector.fontaineTheta O p (e w j)))
    have h1 := hpr w
    have hqq : q ⟨x', hx'⟩ = q x := by
      rw [hq, hq]
      have : π (x' + z') = π x' := by rw [map_add, hkill z' hz', add_zero]
      rw [← this, hsum, h1]
      funext i
      simp [hw, ← hc i]
    have hxx : (⟨x', hx'⟩ : eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ) = x :=
      q.injective hqq
    have hz : (fun j => algebraMap O C (WittVector.fontaineTheta O p (e w j))) -
        (x : Fin h → C) = z' := by
      rw [← hsum, ← hxx]; simp
    rw [hz]; exact hz'

end GlobalTheory.DetInv
