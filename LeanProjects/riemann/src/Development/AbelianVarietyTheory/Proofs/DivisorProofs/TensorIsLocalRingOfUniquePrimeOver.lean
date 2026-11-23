import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_isLocalRing_of_unique_prime_over : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [IsLocalRing L] [Algebra.IsIntegral P T] (𝔐 : Ideal T) [𝔐.IsPrime],
    𝔐.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) →
    (∀ 𝔔 : Ideal T, 𝔔.IsPrime → 𝔔.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) → 𝔔 = 𝔐) →
    (∀ y : L, ∃ a : P, y - algebraMap P L a ∈ maximalIdeal L) →
    IsLocalRing (TensorProduct P T L) := by
  intro P T L _ _ _ _ _ _ _ 𝔐 _ hM huniq hres

  let fκ : P →ₐ[P] L ⧸ maximalIdeal L := Algebra.ofId P _
  have hfκ : ∀ a, fκ a = Ideal.Quotient.mk (maximalIdeal L) (algebraMap P L a) := fun a => rfl
  have hsurj : Function.Surjective fκ := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hres y
    exact ⟨a, by rw [hfκ]; exact (Ideal.Quotient.eq.mpr ha).symm⟩
  have hker : RingHom.ker fκ = (maximalIdeal L).comap (algebraMap P L) := by
    ext a
    rw [RingHom.mem_ker, hfκ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
  let e : (P ⧸ RingHom.ker fκ) ≃ₐ[P] L ⧸ maximalIdeal L := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let q : (P ⧸ RingHom.ker fκ) →ₐ[P] T ⧸ 𝔐 :=
    Ideal.quotientMapₐ 𝔐 (Algebra.ofId P T) (le_of_eq (by rw [hker, ← hM]; rfl))
  let g : L →ₐ[P] T ⧸ 𝔐 := (q.comp e.symm.toAlgHom).comp (Ideal.Quotient.mkₐ P (maximalIdeal L))
  have hg : ∀ a : P, ∀ y : L, y - algebraMap P L a ∈ maximalIdeal L →
      g y = Ideal.Quotient.mk 𝔐 (algebraMap P T a) := by
    intro a y hy
    have h1 : Ideal.Quotient.mkₐ P (maximalIdeal L) y = Ideal.Quotient.mkₐ P (maximalIdeal L) (algebraMap P L a) := by
      rw [Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq.mpr hy
    have h2 : g y = g (algebraMap P L a) := by
      simp only [g, AlgHom.comp_apply]; rw [h1]
    rw [h2, AlgHom.commutes]; rfl
  let ψ : TensorProduct P T L →ₐ[P] T ⧸ 𝔐 :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ P 𝔐) g (fun _ _ => Commute.all _ _)
  have hψ : ∀ t y, ψ (t ⊗ₜ[P] y) = Ideal.Quotient.mk 𝔐 t * g y := by
    intro t y; simp [ψ, Algebra.TensorProduct.lift_tmul]
  haveI : Nontrivial (T ⧸ 𝔐) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨t ⊗ₜ[P] 1, by rw [hψ, map_one, mul_one]⟩
  haveI : Nontrivial (TensorProduct P T L) := hψs.nontrivial

  letI : Algebra L (TensorProduct P T L) := Algebra.TensorProduct.rightAlgebra
  have hmap : ∀ x, algebraMap L (TensorProduct P T L) x = (1 : T) ⊗ₜ[P] x := fun _ => rfl
  have hint : Algebra.IsIntegral L (TensorProduct P T L) := by
    constructor
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | add a b ha hb => exact ha.add hb
    | tmul a b =>
      have h1 : a ⊗ₜ[P] b = (a ⊗ₜ[P] (1 : L)) * algebraMap L (TensorProduct P T L) b := by
        rw [hmap]; simp
      rw [h1]
      refine IsIntegral.mul ?_ isIntegral_algebraMap
      have ha : IsIntegral P a := Algebra.IsIntegral.isIntegral a
      have h2 : IsIntegral P (a ⊗ₜ[P] (1 : L)) :=
        ha.map (Algebra.TensorProduct.includeLeft : T →ₐ[P] TensorProduct P T L)
      obtain ⟨p, hp, hp0⟩ := h2
      refine ⟨p.map (algebraMap P L), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap L (TensorProduct P T L)).comp (algebraMap P L) = algebraMap P _ := by
        ext x
        exact (Algebra.TensorProduct.includeRight : L →ₐ[P] TensorProduct P T L).commutes x
      rw [this]; exact hp0
  have hPB : ∀ a : P, (algebraMap P T a) ⊗ₜ[P] (1 : L) = (1 : T) ⊗ₜ[P] (algebraMap P L a) := by
    intro a
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have key : ∀ 𝔫 : Ideal (TensorProduct P T L), 𝔫.IsMaximal → 𝔫 = RingHom.ker ψ := by
    intro 𝔫 h𝔫
    have hLmax : (𝔫.comap (algebraMap L (TensorProduct P T L))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := L) 𝔫
    have hL : 𝔫.comap (algebraMap L (TensorProduct P T L)) = maximalIdeal L :=
      IsLocalRing.eq_maximalIdeal hLmax
    let iT : T →+* TensorProduct P T L := Algebra.TensorProduct.includeLeftRingHom
    have hiT : ∀ t, iT t = t ⊗ₜ[P] (1 : L) := fun _ => rfl
    have hcomp : iT.comp (algebraMap P T) = (algebraMap L (TensorProduct P T L)).comp (algebraMap P L) := by
      ext a; simp only [RingHom.comp_apply, hiT, hmap]; exact hPB a
    have hT : 𝔫.comap iT = 𝔐 := by
      apply huniq
      · exact Ideal.comap_isPrime iT 𝔫
      · rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hL]
    let j : T ⧸ 𝔐 →+* TensorProduct P T L ⧸ 𝔫 := Ideal.quotientMap 𝔫 iT hT.ge
    have hj : Function.Injective j := Ideal.quotientMap_injective' hT.le
    have hφ : ∀ b, Ideal.Quotient.mk 𝔫 b = j (ψ b) := by
      intro b
      induction b using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
      | tmul t y =>
        obtain ⟨a, ha⟩ := hres y
        have hy1 : (1 : T) ⊗ₜ[P] (y - algebraMap P L a) ∈ 𝔫 := by
          rw [← hmap, ← Ideal.mem_comap, hL]; exact ha
        have hsplit : t ⊗ₜ[P] y - (t * algebraMap P T a) ⊗ₜ[P] (1 : L) = (t ⊗ₜ[P] (1 : L)) * ((1 : T) ⊗ₜ[P] (y - algebraMap P L a)) := by
          rw [TensorProduct.tmul_sub, mul_sub, ← hPB]
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [hψ, hg a y ha, ← map_mul]
        show _ = Ideal.quotientMap 𝔫 iT hT.ge (Ideal.Quotient.mk 𝔐 (t * algebraMap P T a))
        rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, hiT, hsplit]
        exact 𝔫.mul_mem_left _ hy1
    ext b
    rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, RingHom.mem_ker, map_eq_zero_iff j hj]
  obtain ⟨𝔫₀, h0⟩ := Ideal.exists_maximal (TensorProduct P T L)
  exact IsLocalRing.of_unique_max_ideal ⟨𝔫₀, h0, fun 𝔫 h => (key 𝔫 h).trans (key 𝔫₀ h0).symm⟩

end GlobalTheory
