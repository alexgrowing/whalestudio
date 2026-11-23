import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

omit [NumberField E] [IsTotallyComplex E] in

theorem blkMat_one_mem (hr : r ≤ a) (k : Kinf E (a - r)) :
    blkMat (Cinf E) hr (1, k.1) ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := by
  have hs : star (blkMat (Cinf E) hr (1, k.1)) = blkMat (Cinf E) hr (1, star k.1) := by
    change Matrix.conjTranspose (Matrix.reindex (blkEquiv hr) (blkEquiv hr) (Matrix.fromBlocks 1 0 0 k.1)) =
      Matrix.reindex (blkEquiv hr) (blkEquiv hr) (Matrix.fromBlocks 1 0 0 (Matrix.conjTranspose k.1))
    rw [Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]
    simp
  rw [Matrix.mem_unitaryGroup_iff', hs, ← map_mul]
  have : ((1 : Matrix (Fin r) (Fin r) (Cinf E)), star k.1) * (1, k.1) = 1 :=
    Prod.ext (mul_one _) (Matrix.mem_unitaryGroup_iff'.1 k.2)
  rw [this, map_one]

def blkK (hr : r ≤ a) (k : Kinf E (a - r)) : Kinf E a := ⟨blkMat (Cinf E) hr (1, k.1), blkMat_one_mem hr k⟩

omit [NumberField E] [IsTotallyComplex E] in
theorem toUnits_blkK (hr : r ≤ a) (k : Kinf E (a - r)) :
    Unitary.toUnits (blkK hr k) = blkGL hr (1, Unitary.toUnits k) := Units.ext rfl

variable (E) in

def slice [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E))
    (hr : r ≤ a) (φ : GA E a → ℂ) (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) : GA E (a - r) → ℂ :=
  fun m₂ => ∫ x in 𝓕, φ (unip x * (blkGL hr (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ

def levelSub (hr : r ≤ a) (t : GL (Fin a) (Af E)) (L : Subgroup (GL (Fin a) (Af E))) :
    Subgroup (GL (Fin (a - r)) (Af E)) :=
  (L.map (MulAut.conj t).toMonoidHom).comap ((blkGL hr).comp (MonoidHom.inr _ _))

theorem mem_levelSub (hr : r ≤ a) (t : GL (Fin a) (Af E)) (L : Subgroup (GL (Fin a) (Af E)))
    (l : GL (Fin (a - r)) (Af E)) : l ∈ levelSub hr t L ↔ t⁻¹ * blkGL hr (1, l) * t ∈ L := by
  simp only [levelSub, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, hk, e⟩
    rw [← e]; simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by group⟩

def ktypeSub (hr : r ≤ a) (κ : Kinf E a) (W : Submodule ℂ (Kinf E a → ℂ)) : Submodule ℂ (Kinf E (a - r) → ℂ) :=
  W.map (LinearMap.funLeft ℂ ℂ fun k => κ⁻¹ * blkK hr k * κ)

instance (hr : r ≤ a) (κ : Kinf E a) (W : Submodule ℂ (Kinf E a → ℂ)) [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (ktypeSub hr κ W) := by
  unfold ktypeSub; infer_instance

theorem blkGL_one_corner {R S : Type} [CommRing R] [CommRing S] (hr : r ≤ a) (s : R →ₙ+* S)
    (l : GL (Fin (a - r)) R) : blkGL hr (1, cornerGL (a - r) s l) = cornerGL a s (blkGL hr (1, l)) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
  rw [blkGL_apply]
  change _ = (1 : Matrix (Fin a) (Fin a) S) _ _ - s ((1 : Matrix (Fin a) (Fin a) R) _ _) + s ((blkGL hr (1, l) : Matrix (Fin a) (Fin a) R) _ _)
  rw [blkGL_apply]
  have e1 : ∀ {T : Type} [CommRing T] (i j : Fin r ⊕ Fin (a - r)),
      (1 : Matrix (Fin a) (Fin a) T) (blkEquiv hr i) (blkEquiv hr j) = (1 : Matrix (Fin r ⊕ Fin (a - r)) _ T) i j := by
    intro T _ i j
    simp [Matrix.one_apply, (blkEquiv hr).injective.eq_iff]
  rw [e1, e1]
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.one_apply]
  · simp
  · simp
  · change (1 : Matrix _ _ S) i j - s ((1 : Matrix _ _ R) i j) + s (l i j) = _
    simp [Matrix.one_apply]

theorem blkGL_mul_finGL (hr : r ≤ a) (m₁ : GA E r) (m₂ : GA E (a - r)) (l : GL (Fin (a - r)) (Af E)) :
    blkGL hr (m₁, m₂ * finGL E (a - r) l) = blkGL hr (m₁, m₂) * finGL E a (blkGL hr (1, l)) := by
  rw [show (m₁, m₂ * finGL E (a - r) l) = (m₁, m₂) * (1, finGL E (a - r) l) by simp, map_mul]
  exact congrArg _ (blkGL_one_corner hr _ l)

theorem blkGL_mul_infGL (hr : r ≤ a) (m₁ : GA E r) (m₂ : GA E (a - r)) (y : GL (Fin (a - r)) (Cinf E)) :
    blkGL hr (m₁, m₂ * infGL E (a - r) y) = blkGL hr (m₁, m₂) * infGL E a (blkGL hr (1, y)) := by
  rw [show (m₁, m₂ * infGL E (a - r) y) = (m₁, m₂) * (1, infGL E (a - r) y) by simp, map_mul]
  exact congrArg _ (blkGL_one_corner hr _ y)

theorem slice_mul_finGL [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)) (hr : r ≤ a) (φ : GA E a → ℂ) (L : Subgroup (GL (Fin a) (Af E)))
    (hφ : ∀ k ∈ L, ∀ g, φ (g * finGL E a k) = φ g) (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a)
    (l : GL (Fin (a - r)) (Af E)) (hl : l ∈ levelSub hr t L) (g : GA E (a - r)) :
    slice E μ 𝓕 hr φ m₁ t κ (g * finGL E (a - r) l) = slice E μ 𝓕 hr φ m₁ t κ g := by
  unfold slice
  congr 1
  funext x
  have hk := hφ _ ((mem_levelSub hr t L l).1 hl)
    (unip x * (blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)))
  rw [← hk, blkGL_mul_finGL]
  congr 1
  have e : finGL E a t * finGL E a (t⁻¹ * blkGL hr (1, l) * t) = finGL E a (blkGL hr (1, l)) * finGL E a t := by
    rw [← map_mul, ← map_mul]; congr 1; group
  calc unip x * (blkGL hr (m₁, g) * finGL E a (blkGL hr (1, l)) * finGL E a t * infGL E a (Unitary.toUnits κ))
      = unip x * (blkGL hr (m₁, g) * (finGL E a t * finGL E a (t⁻¹ * blkGL hr (1, l) * t)) *
          infGL E a (Unitary.toUnits κ)) := by rw [e]; simp only [mul_assoc]
    _ = unip x * (blkGL hr (m₁, g) * finGL E a t * (infGL E a (Unitary.toUnits κ) *
          finGL E a (t⁻¹ * blkGL hr (1, l) * t))) := by rw [infGL_comm]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem slice_mul_cpt [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)) (hr : r ≤ a) (φ : GA E a → ℂ) (m₁ : GA E r) (t : GL (Fin a) (Af E))
    (κ : Kinf E a) (g : GA E (a - r)) (k : Kinf E (a - r)) :
    slice E μ 𝓕 hr φ m₁ t κ (g * infGL E (a - r) (Unitary.toUnits k)) =
      ∫ x in 𝓕, φ (unip x * ((blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)) *
        infGL E a (Unitary.toUnits (κ⁻¹ * blkK hr k * κ)))) ∂μ := by
  unfold slice
  congr 1
  funext x
  congr 2
  rw [blkGL_mul_infGL]
  simp only [map_mul, map_inv, toUnits_blkK]
  simp only [mul_assoc, mul_inv_cancel_left]
  rw [← mul_assoc (infGL E a (blkGL hr (1, Unitary.toUnits k))) (finGL E a t),
    infGL_comm (blkGL hr (1, Unitary.toUnits k)) t]
  simp only [mul_assoc]

end GlobalTheory.SliceTwo

end
