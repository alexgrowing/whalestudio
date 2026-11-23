import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipModHalf

theorem zpow_sub_one_eq_mul {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (ℓ : A ≃ₗ[R] A) (n : ℤ) :
    ∃ X : Module.End R A, Commute ((ℓ : Module.End R A) - 1) X ∧
      ((ℓ ^ n : A ≃ₗ[R] A) : Module.End R A) - 1 = ((ℓ : Module.End R A) - 1) * X := by
  have h1 : (ℓ.symm : Module.End R A) * (ℓ : Module.End R A) = 1 := by
    ext y; simp
  have h2 : (ℓ : Module.End R A) * (ℓ.symm : Module.End R A) = 1 := by
    ext y; simp
  have hDℓ : Commute ((ℓ : Module.End R A) - 1) (ℓ : Module.End R A) :=
    (Commute.refl _).sub_left (Commute.one_left _)
  have hDs : Commute ((ℓ : Module.End R A) - 1) (ℓ.symm : Module.End R A) := by
    show _ = _
    rw [sub_mul, mul_sub, h2, h1, one_mul, mul_one]
  induction n using Int.induction_on with
  | zero => exact ⟨0, Commute.zero_right _, by ext y; simp⟩
  | succ k ih =>
    obtain ⟨X, hc, hX⟩ := ih
    refine ⟨(ℓ : Module.End R A) * X + 1, (hDℓ.mul_right hc).add_right (Commute.one_right _), ?_⟩
    have e : ((ℓ ^ ((k : ℤ) + 1) : A ≃ₗ[R] A) : Module.End R A)
        = (ℓ : Module.End R A) * ((ℓ ^ (k : ℤ) : A ≃ₗ[R] A) : Module.End R A) := by
      ext y; rw [add_comm, zpow_add, zpow_one]; rfl
    rw [e, eq_add_of_sub_eq hX]
    noncomm_ring
  | pred k ih =>
    obtain ⟨X, hc, hX⟩ := ih
    refine ⟨(ℓ.symm : Module.End R A) * X - (ℓ.symm : Module.End R A),
      (hDs.mul_right hc).sub_right hDs, ?_⟩
    have e : ((ℓ ^ (-(k : ℤ) - 1) : A ≃ₗ[R] A) : Module.End R A)
        = (ℓ.symm : Module.End R A) * ((ℓ ^ (-(k : ℤ)) : A ≃ₗ[R] A) : Module.End R A) := by
      ext y; rw [sub_eq_neg_add, zpow_add, zpow_neg_one]; rfl
    rw [e, eq_add_of_sub_eq hX]
    set s : Module.End R A := (ℓ.symm : Module.End R A)
    set l : Module.End R A := (ℓ : Module.End R A)
    have : s * ((l - 1) * X + 1) - 1 = (l - 1) * (s * X - s) + (s * l - 1) * X
        - (l * s - 1) * X + (l * s - 1) := by noncomm_ring
    rw [this, h1, h2]; simp

end GlobalTheory.UnipModHalf

namespace GlobalTheory.UnipModHalf

open Matrix

theorem unip_mod_half : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (L' : Submodule (𝓞 E) (Fin r → E)) (Mb P : Ideal (𝓞 E)), Mb ≤ P →
    ∀ {A : Type} [AddCommGroup A] [Module (𝓞 E) A] (φ : A ≃ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))
      (ℓ : A ≃ₗ[𝓞 E] A) (n : ℤ),
    (∀ x : A, ((ℓ.toLinearMap - LinearMap.id : Module.End (𝓞 E) A) ^ r) x ∈ P • (⊤ : Submodule (𝓞 E) A)) →
    ∀ γ t : Matrix (Fin r) (Fin r) E, (∀ w ∈ L', Matrix.mulVec γ w ∈ L') → (∀ w ∈ L', Matrix.mulVec γ w - w ∈ Mb • L') →
    (∀ w : L', ∃ hw : Matrix.mulVec t w ∈ L',
      Submodule.Quotient.mk (p := Mb • (⊤ : Submodule (𝓞 E) L')) ⟨_, hw⟩ = φ ((ℓ ^ n) (φ.symm (Submodule.Quotient.mk w)))) →
    ∀ w ∈ L', Matrix.mulVec ((γ * t - 1) ^ r) w ∈ P • L' := by
  intro E _ _ r L' Mb P hMP A _ _ φ ℓ n hℓ γ t hγ hγ1 ht w hw

  let tL : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (Matrix.mulVecLin t).restrictScalars (𝓞 E)
  let gL : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (Matrix.mulVecLin γ).restrictScalars (𝓞 E)
  let T : Module.End (𝓞 E) L' := tL.restrict (fun x hx => (ht ⟨x, hx⟩).1)
  let G : Module.End (𝓞 E) L' := gL.restrict (fun x hx => hγ x hx)
  let U : Module.End (𝓞 E) L' := G * T - 1
  have hU : ∀ x : L', ((U x : L') : Fin r → E) = γ *ᵥ (t *ᵥ (x : Fin r → E)) - x := by
    intro x; rfl
  have hpow : ∀ k : ℕ, ∀ x : L', ((γ * t - 1) ^ k) *ᵥ (x : Fin r → E) = (((U ^ k) x : L') : Fin r → E) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, pow_succ', Module.End.mul_apply, hU,
        Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]

  have hsub : ∀ (I : Ideal (𝓞 E)) (z : L'), (z : Fin r → E) ∈ I • L' → z ∈ I • (⊤ : Submodule (𝓞 E) L') := by
    intro I z hz
    have e : I • L' = (I • (⊤ : Submodule (𝓞 E) L')).map L'.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
    rw [e] at hz
    obtain ⟨u, hu, huz⟩ := hz
    have : u = z := Subtype.ext huz
    exact this ▸ hu
  set ℓn : Module.End (𝓞 E) A := ((ℓ ^ n : A ≃ₗ[𝓞 E] A) : Module.End (𝓞 E) A)
  have hπU : ∀ x : L', (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (U x) = φ ((ℓn - 1) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := by
    intro x
    have hG : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (G (T x)) = (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (T x) := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact hsub Mb _ (hγ1 _ (T x).2)
    have hT : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (T x) = φ ((ℓ ^ n) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := (ht x).2
    simp only [U, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, map_sub, hG, hT]
    simp [ℓn]
  have hπUk : ∀ k : ℕ, ∀ x : L', (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ ((U ^ k) x) = φ (((ℓn - 1) ^ k) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, hπU, ih, LinearEquiv.symm_apply_apply, pow_succ',
        Module.End.mul_apply]

  obtain ⟨X, hc, hX⟩ := zpow_sub_one_eq_mul ℓ n
  have hℓ' : ∀ y : A, ((ℓn - 1) ^ r) y ∈ P • (⊤ : Submodule (𝓞 E) A) := by
    intro y
    rw [show ℓn - 1 = ((ℓ : Module.End (𝓞 E) A) - 1) * X from hX, hc.mul_pow, Module.End.mul_apply]
    have := hℓ ((X ^ r) y)
    rwa [← Module.End.one_eq_id] at this

  have hQ : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ ((U ^ r) ⟨w, hw⟩) ∈ P • (⊤ : Submodule (𝓞 E) (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L')))) := by
    rw [hπUk]
    have hm : ((P • (⊤ : Submodule (𝓞 E) A)).map (φ : A →ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))) ≤ P • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact hm (Submodule.mem_map_of_mem (hℓ' _))
  have hL : (U ^ r) ⟨w, hw⟩ ∈ P • (⊤ : Submodule (𝓞 E) L') := by
    have e : P • (⊤ : Submodule (𝓞 E) (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L')))) = (P • (⊤ : Submodule (𝓞 E) L')).map (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [e] at hQ
    have hQ' := Submodule.mem_comap.mpr hQ
    rw [Submodule.comap_map_mkQ] at hQ'
    have hle : Mb • (⊤ : Submodule (𝓞 E) L') ≤ P • (⊤ : Submodule (𝓞 E) L') := Submodule.smul_mono_left hMP
    exact (sup_le hle le_rfl) hQ'
  have key := hpow r ⟨w, hw⟩
  simp only at key
  rw [key]
  have e : P • L' = (P • (⊤ : Submodule (𝓞 E) L')).map L'.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [e]
  exact Submodule.mem_map_of_mem hL

end GlobalTheory.UnipModHalf
