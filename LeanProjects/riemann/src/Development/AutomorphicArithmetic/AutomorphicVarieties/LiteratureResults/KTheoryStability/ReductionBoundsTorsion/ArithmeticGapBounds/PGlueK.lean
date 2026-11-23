import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.Arith

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SpectralGap.GlueK

variable (L : Type) [Field L] [NumberField L] (N : ℕ)

abbrev Hq (π : 𝓞 L) (hπ : π ≠ 0) : Subgroup (Gm L N) :=
  ((toK L N).range.map (MulAut.conj (qel L N π hπ)⁻¹).toMonoidHom).comap (toK L N)

abbrev iO : Matrix.SpecialLinearGroup (Fin N) (𝓞 L) →* Matrix.SpecialLinearGroup (Fin N) L :=
  Matrix.SpecialLinearGroup.map (algebraMap (𝓞 L) L)

theorem dg_zero' (π : 𝓞 L) : dg L N π 0 = 1 := by
  unfold dg
  simp

theorem coe_qel (π : 𝓞 L) (hπ : π ≠ 0) :
    ((qel L N π hπ : GK L N) : Matrix (Fin N) (Fin N) L) = dg L N π 1 := by
  show (diagonal fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1) = dg L N π 1
  unfold dg
  congr 1
  funext i
  simp

theorem coe_toK_toGL (a : Matrix.SpecialLinearGroup (Fin N) (𝓞 L)) :
    ((toK L N (Matrix.SpecialLinearGroup.toGL a) : GK L N) : Matrix (Fin N) (Fin N) L) =
      ((iO L N a : Matrix.SpecialLinearGroup (Fin N) L) : Matrix (Fin N) (Fin N) L) := rfl

theorem mem_Hq_iff (π : 𝓞 L) (hπ : π ≠ 0) (h : Gm L N) :
    h ∈ Hq L N π hπ ↔ ∃ δ : Gm L N, qel L N π hπ * toK L N h = toK L N δ * qel L N π hπ := by
  constructor
  · intro hh
    obtain ⟨x, ⟨δ, rfl⟩, hx⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hh)
    refine ⟨δ, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hx
    rw [← hx]
    group
  · rintro ⟨δ, hδ⟩
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨toK L N δ, ⟨δ, rfl⟩, ?_⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mul_assoc, ← hδ, inv_mul_cancel_left]

theorem mem_Kg_zero (π : 𝓞 L) (g : Matrix.SpecialLinearGroup (Fin N) L) :
    g ∈ Kg L N π 0 ↔ ∃ a, iO L N a = g := by
  show (∃ γ, dg L N π 0 * mt L N g = mo L N γ * dg L N π 0) ↔ _
  rw [dg_zero']
  constructor
  · rintro ⟨γ, h⟩
    refine ⟨γ, Subtype.ext ?_⟩
    rw [one_mul, mul_one] at h
    exact h.symm
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [one_mul, mul_one]; rfl⟩

theorem mem_Hq (π : 𝓞 L) (hπ : π ≠ 0) (a : Matrix.SpecialLinearGroup (Fin N) (𝓞 L)) :
    Matrix.SpecialLinearGroup.toGL a ∈ Hq L N π hπ ↔ iO L N a ∈ Kg L N π 1 := by
  rw [mem_Hq_iff]
  show _ ↔ ∃ γ, dg L N π 1 * mt L N (iO L N a) = mo L N γ * dg L N π 1
  constructor
  · rintro ⟨δ, hδ⟩
    have hm := congrArg (fun x : GK L N => (x : Matrix (Fin N) (Fin N) L)) hδ
    simp only [GeneralLinearGroup.coe_mul, coe_qel, coe_toK_toGL] at hm
    have hdet : (δ : Matrix (Fin N) (Fin N) (𝓞 L)).det = 1 := by
      have h1 := congrArg Matrix.det hm
      rw [det_mul, det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one] at h1
      have hd : (dg L N π 1).det ≠ 0 := by
        rw [← coe_qel L N π hπ]
        exact (qel L N π hπ).isUnit.map (detMonoidHom) |>.ne_zero
      have h2 : ((toK L N δ : GK L N) : Matrix (Fin N) (Fin N) L).det = 1 :=
        mul_right_cancel₀ hd (h1.symm.trans (one_mul _).symm)
      have h3 : ((toK L N δ : GK L N) : Matrix (Fin N) (Fin N) L).det =
          algebraMap (𝓞 L) L (δ : Matrix (Fin N) (Fin N) (𝓞 L)).det := by
        rw [RingHom.map_det]
        rfl
      rw [h3] at h2
      exact (FaithfulSMul.algebraMap_injective (𝓞 L) L) (by rw [h2, map_one])
    refine ⟨⟨δ, hdet⟩, ?_⟩
    exact hm
  · rintro ⟨γ, hγ⟩
    refine ⟨Matrix.SpecialLinearGroup.toGL γ, Units.ext ?_⟩
    simp only [GeneralLinearGroup.coe_mul, coe_qel, coe_toK_toGL]
    exact hγ

theorem Hq_surj (π : 𝓞 L) (hπ : π ≠ 0) (hN : 0 < N) (γ : Gm L N) :
    ∃ a, γ * (Matrix.SpecialLinearGroup.toGL a)⁻¹ ∈ Hq L N π hπ := by
  let i0 : Fin N := ⟨0, hN⟩
  let u : (𝓞 L)ˣ := GeneralLinearGroup.det γ
  let du : Fin N → 𝓞 L := Function.update 1 i0 (u : 𝓞 L)
  let dv : Fin N → 𝓞 L := Function.update 1 i0 ((u⁻¹ : (𝓞 L)ˣ) : 𝓞 L)
  have h1 : ∀ i, du i * dv i = 1 := by
    intro i
    by_cases hi : i = i0
    · subst hi; simp [du, dv]
    · simp [du, dv, hi]
  have h2 : ∀ i, dv i * du i = 1 := fun i => by rw [mul_comm]; exact h1 i
  let h : Gm L N := ⟨diagonal du, diagonal dv,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact h1 i,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact h2 i⟩
  have hdeth : (h : Matrix (Fin N) (Fin N) (𝓞 L)).det = u := by
    show (diagonal du).det = u
    rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have hdet : ((h⁻¹ * γ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).det = 1 := by
    have := congrArg (fun x : (𝓞 L)ˣ => (x : 𝓞 L)) (map_mul (GeneralLinearGroup.det) h⁻¹ γ)
    simp only [map_inv, Units.val_mul] at this
    rw [← GeneralLinearGroup.val_det_apply, this]
    have e1 : ((GeneralLinearGroup.det h : (𝓞 L)ˣ) : 𝓞 L) = u := by
      rw [GeneralLinearGroup.val_det_apply, hdeth]
    have e2 : GeneralLinearGroup.det h = u := Units.ext e1
    rw [e2]
    exact Units.inv_mul u
  refine ⟨⟨_, hdet⟩, ?_⟩
  have hg : Matrix.SpecialLinearGroup.toGL ⟨_, hdet⟩ = h⁻¹ * γ := Units.ext rfl
  rw [hg, _root_.mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [mem_Hq_iff]
  refine ⟨h, Units.ext ?_⟩
  simp only [GeneralLinearGroup.coe_mul, coe_qel]
  have hK : ((toK L N h : GK L N) : Matrix (Fin N) (Fin N) L) = diagonal fun i => algebraMap (𝓞 L) L (du i) := by
    show (diagonal du).map (algebraMap (𝓞 L) L) = _
    rw [diagonal_map (map_zero _)]
  rw [hK]
  unfold dg
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mul_comm]

theorem toP_toGL (a : Matrix.SpecialLinearGroup (Fin N) (𝓞 L)) :
    toP L N (toK L N (Matrix.SpecialLinearGroup.toGL a)) = ofS L N (jS L N (iO L N a)) := by
  funext w
  ext i j
  rfl

end PositivityTheory.KB.SpectralGap.GlueK

end
