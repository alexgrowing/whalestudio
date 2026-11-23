import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom.LatChar

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_psi_ne_one {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) :
    ∃ w : F, w ≠ 0 ∧ -1 ≤ ord w ∧ ψ w ≠ 1 := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have h := not_isTrivialOn_addCharConductor_sub_one hc h1
  rw [h0] at h
  simp only [IsTrivialOn, not_forall] at h
  obtain ⟨y, hy, hne⟩ := h
  have y0 : y ≠ 0 := by
    rintro rfl
    simp at hne
  exact ⟨y, y0, by simpa using (mem_valBall_iff_le_ord y0).1 hy, hne⟩

theorem mem_integers_iff {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← mem_valBall_iff_le_ord hx, mem_valBall_zero_iff]

theorem exists_lattice_witness {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (A : GL (Fin 2) F)
    (hA : ¬ ∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) :
    ∃ y : Fin 2 → F, (∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ y) i ∈ 𝒪[F]) ∧ ψ (-y 1) ≠ 1 := by
  obtain ⟨w, w0, hw, hne⟩ := exists_psi_ne_one hψ
  simp only [not_forall] at hA
  obtain ⟨b, hb⟩ := hA
  set e := ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b with he
  have e0 : e ≠ 0 := fun h => hb (h ▸ zero_mem _)
  have hord : ord e < 0 := by
    by_contra hc
    exact hb ((mem_integers_iff e0).2 (not_lt.1 hc))
  have ei : e⁻¹ ≠ 0 := inv_ne_zero e0
  have ht : -w * e⁻¹ ∈ 𝒪[F] := by
    have nw : -w ≠ 0 := neg_ne_zero.2 w0
    have hnw : ord (-w) = ord w := by simp [ord, Valuation.map_neg]
    refine (mem_integers_iff (mul_ne_zero nw ei)).2 ?_
    rw [ord_mul nw ei, ord_inv e0, hnw]
    omega
  refine ⟨((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single b (-w * e⁻¹), ?_, ?_⟩
  · intro i
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hi : i = b
    · subst hi; simpa using ht
    · simp [Pi.single_eq_of_ne hi, zero_mem]
  · have : (((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single b (-w * e⁻¹)) 1 = -w := by
      have hg : ∀ (M : Matrix (Fin 2) (Fin 2) F) (t : F), (M *ᵥ Pi.single b t) 1 = M 1 b * t := by
        intro M t
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hg, ← he]
      field_simp
    rw [this, neg_neg]
    exact hne

end GlobalTheory.CompanionTheory.LFUDom.LatChar

open GlobalTheory.CompanionTheory.LFUDom.LatChar in

theorem GlobalTheory.CompanionTheory.LFUDom.integral_lattice_char_eq_zero
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (hψ : Ad3.IsStd ψ) (A : GL (Fin 2) F)
    (hA : ¬ ∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) :
    ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}
      (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ = 0 := by
  obtain ⟨y, hy, hne⟩ := exists_lattice_witness hψ A hA
  have hv : (Ad3.LFS.vol2 ψ).IsAddHaarMeasure := by unfold Ad3.LFS.vol2; infer_instance
  set S := {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} with hS
  set g : (Fin 2 → F) → ℂ := S.indicator (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) with hg
  have hmem : ∀ x, x + y ∈ S ↔ x ∈ S := by
    intro x
    simp only [hS, Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply]
    refine forall_congr' fun i => ?_
    constructor
    · intro h
      simpa using sub_mem h (hy i)
    · intro h
      exact add_mem h (hy i)
  have hshift : ∀ x, g (x + y) = ((ψ (-y 1) : Circle) : ℂ) * g x := by
    intro x
    by_cases hx : x ∈ S
    · rw [hg, Set.indicator_of_mem ((hmem x).2 hx), Set.indicator_of_mem hx, Pi.add_apply,
        neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, mul_comm]
    · rw [hg, Set.indicator_of_notMem (fun h => hx ((hmem x).1 h)), Set.indicator_of_notMem hx,
        mul_zero]
  have h := integral_add_right_eq_self (μ := Ad3.LFS.vol2 ψ) g y
  simp only [hshift, integral_const_mul] at h
  have hc : ((ψ (-y 1) : Circle) : ℂ) ≠ 1 := fun h1 => hne (Circle.ext (by simpa using h1))
  have : (((ψ (-y 1) : Circle) : ℂ) - 1) * ∫ x, g x ∂Ad3.LFS.vol2 ψ = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)
