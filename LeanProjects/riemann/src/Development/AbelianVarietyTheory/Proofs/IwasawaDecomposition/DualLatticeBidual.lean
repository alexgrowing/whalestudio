import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGlob

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelHecke.DualConj

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_dualL (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ dualL σ J L ↔ ∀ x ∈ L, hform σ J x y ∈ (algebraMap (𝓞 E) E).range := by
  have := bwG_span_dualSet σ J L
  change y ∈ ((Submodule.span (𝓞 E) (dualSet σ J L) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ↔ _
  rw [this]; rfl

omit [NumberField E] in
theorem hform_eq (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

omit [NumberField E] in
theorem hform_unitary (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) E)
    (hg : cT σ g * J * g = J) (x y : Fin n → E) : hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have e : (fun i => σ ((g *ᵥ x) i)) = (fun i => σ (x i)) ᵥ* cT σ g := by
    funext i
    simp [cT, mulVec, vecMul, dotProduct, mul_comm]
  rw [hform_eq, hform_eq, e, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg]

omit [NumberField E] in
theorem hform_smul_left (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hform σ J (a • x) y = σ a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

omit [NumberField E] in
theorem hform_smul_right (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

@[reducible] def starOf (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) : StarRing E where
  star := σ
  star_involutive := hσ
  star_mul a b := by rw [map_mul, mul_comm]
  star_add := map_add σ

theorem dual_lattice_bidual (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit J.det) (hH : cT σ J = J) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice E (dualL σ J L) ∧ dualL σ J (dualL σ J L) = L := by
  letI : StarRing E := starOf σ hσ
  let h : (Fin n → E) →ₗ⋆[E] (Fin n → E) →ₗ[E] E :=
    LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (hform σ J)
      (fun x x' y => by simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
      (fun a x y => hform_smul_left σ J a x y)
      (fun x y y' => by simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib])
      (fun a x y => hform_smul_right σ J a x y)
  have hh : ∀ x y, h x y = hform σ J x y := fun _ _ => rfl
  have hsym' : ∀ x y, σ (hform σ J x y) = hform σ J y x := by
    intro x y
    have e : ∀ i j, σ (J i j) = J j i := fun i j => congrFun (congrFun hH j) i
    simp only [hform, map_sum, map_mul, hσ, e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsym : h.IsSymm := ⟨fun x y => hsym' x y⟩
  have hr : ∀ y, (∀ x, hform σ J x y = 0) → y = 0 := by
    intro y hy
    have h1 : J *ᵥ y = 0 := by
      funext i
      have := hy (Pi.single i 1)
      rw [hform_eq, dotProduct, Finset.sum_eq_single i] at this
      · simpa using this
      · intro b _ hb
        simp [hb]
      · simp
    have ey : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    rw [ey, h1, mulVec_zero]
  have hnd : h.Nondegenerate := by
    refine ⟨fun x hx => hr x fun y => ?_, fun y hy => hr y hy⟩
    rw [← hsym', ← hh, hx y, map_zero]
  have hd : ∀ M : Submodule (𝓞 E) (Fin n → E), Formalism.HermitianLatticesTheory.dual h M = dualL σ J M := by
    intro M
    ext y
    rw [mem_dualL]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one]
    rfl
  have := Formalism.HermitianLatticesTheory.dualLattice (𝓞 E) E (Fin n → E) h hsym hnd (fun r => LocB.sig_int σ r) L hL
  rw [hd, hd] at this
  exact ⟨this.1, this.2.1⟩

theorem localization_dualL_le (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime]
    (hPQ : ∀ a b : 𝓞 E, (a : E) = σ (b : E) → a ∈ Q → b ∈ P) (M N : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG)
    (h : Formalism.HermitianLatticesTheory.localization₂ P M ≤ Formalism.HermitianLatticesTheory.localization₂ P N) :
    Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J N) ≤ Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J M) := by
  have h1P : (1 : 𝓞 E) ∉ P := P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)
  have key : ∃ s : 𝓞 E, s ∉ P ∧ ∀ x ∈ M, s • x ∈ N := by
    have h0 : M ≤ Formalism.HermitianLatticesTheory.localization₂ P N := fun x hx =>
      h ((rlv_mem_locP P M x).2 ⟨1, h1P, by rwa [one_smul]⟩)
    clear h
    induction M, hM using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨s, hs, hx⟩ := (rlv_mem_locP P N x).1 (h0 (Submodule.mem_span_singleton_self x))
      refine ⟨s, hs, fun y hy => ?_⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [smul_comm]; exact N.smul_mem a hx
    | sup A B _ _ hA hB =>
      obtain ⟨s, hs, h1⟩ := hA (le_sup_left.trans h0)
      obtain ⟨t, ht, h2⟩ := hB (le_sup_right.trans h0)
      refine ⟨s * t, fun hst => (Ideal.IsPrime.mem_or_mem inferInstance hst).elim hs ht, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [smul_add]
      refine N.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact N.smul_mem _ (h1 a ha)
      · rw [mul_smul]; exact N.smul_mem _ (h2 b hb)
  obtain ⟨s, hs, hsM⟩ := key
  obtain ⟨s', hs'⟩ := LocB.sig_int σ s
  have hs'Q : s' ∉ Q := fun hq => hs (hPQ s' s hs' hq)
  intro y hy
  obtain ⟨t, ht, hty⟩ := (rlv_mem_locP Q _ y).1 hy
  refine (rlv_mem_locP Q _ y).2 ⟨s' * t, fun hst => (Ideal.IsPrime.mem_or_mem inferInstance hst).elim hs'Q ht, ?_⟩
  rw [mem_dualL] at hty ⊢
  intro x hx
  have := hty _ (hsM x hx)
  rw [← algebraMap_smul E s x, hform_smul_left] at this
  rw [mul_smul, ← algebraMap_smul E s' (t • y), hform_smul_right, hs']
  exact this

theorem mem_mulLat (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ mulLat γ.1 L ↔ (γ⁻¹).1 *ᵥ y ∈ L := by
  rw [← map_glE, Submodule.mem_map_equiv, glE_symm_apply]

theorem mulLat_lattice (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice E (mulLat γ.1 L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have e : (mulLat γ.1 L : Set (Fin n → E)) = (Matrix.mulVecLin γ.1) '' (L : Set (Fin n → E)) := rfl
  rw [e, ← Submodule.map_span, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact (glE γ).surjective

theorem dualL_mulLat (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E) (hγ : γ ∈ UJ σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) : dualL σ J (mulLat γ.1 L) = mulLat γ.1 (dualL σ J L) := by
  ext y
  have ey : γ.1 *ᵥ ((γ⁻¹).1 *ᵥ y) = y := (glE γ).apply_symm_apply y
  rw [mem_mulLat, mem_dualL, mem_dualL]
  constructor
  · intro h x hx
    rw [← hform_unitary σ J γ.1 hγ, ey]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    have := h x hx
    rw [← hform_unitary σ J γ.1 hγ, ey] at this
    exact this

theorem dual_conj_primes : ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime], (∀ x, σ (σ x) = x) → IsUnit J.det → cT σ J = J → (∀ a b : 𝓞 E, (b : E) = σ (a : E) → (a ∈ Q ↔ b ∈ P)) → ∀ M N : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E M → Submodule.IsLattice E N → (Formalism.HermitianLatticesTheory.localization₂ P M = Formalism.HermitianLatticesTheory.localization₂ P N → Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J M) = Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J N)) ∧ (Formalism.HermitianLatticesTheory.localization₂ P (dualL σ J M) = Formalism.HermitianLatticesTheory.localization₂ P (dualL σ J N) → Formalism.HermitianLatticesTheory.localization₂ Q M = Formalism.HermitianLatticesTheory.localization₂ Q N) ∧ ∀ γ : GL (Fin n) E, γ ∈ UJ σ J → Submodule.IsLattice E (mulLat γ.1 M) ∧ dualL σ J (mulLat γ.1 M) = mulLat γ.1 (dualL σ J M) := by
  intro E _ _ σ n J P Q _ _ hσ hJ hH hPQ M N hM hN
  have hPQ' : ∀ a b : 𝓞 E, (a : E) = σ (b : E) → a ∈ Q → b ∈ P := fun a b hab =>
    (hPQ a b (by rw [hab, hσ])).1
  have one : ∀ A B : Submodule (𝓞 E) (Fin n → E), A.FG → B.FG → Formalism.HermitianLatticesTheory.localization₂ P A = Formalism.HermitianLatticesTheory.localization₂ P B →
      Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J A) = Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J B) := fun A B hA hB h =>
    le_antisymm (localization_dualL_le σ J P Q hPQ' B A hB h.ge) (localization_dualL_le σ J P Q hPQ' A B hA h.le)
  obtain ⟨hM1, hM2⟩ := dual_lattice_bidual σ hσ J hJ hH M hM
  obtain ⟨hN1, hN2⟩ := dual_lattice_bidual σ hσ J hJ hH N hN
  refine ⟨one M N hM.fg hN.fg, fun h => ?_, fun γ hγ => ⟨mulLat_lattice γ M hM, dualL_mulLat σ J γ hγ M⟩⟩
  have := one _ _ hM1.fg hN1.fg h
  rwa [hM2, hN2] at this

end GlobalTheory.LevelHecke.DualConj

end
