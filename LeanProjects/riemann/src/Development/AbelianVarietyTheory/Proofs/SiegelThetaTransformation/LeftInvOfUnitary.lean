import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant

noncomputable section

open MeasureTheory Topology Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory.VolPairExists

theorem exists_haar_image {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsOpen (H : Set G))
    {R : Type} [Group R] [TopologicalSpace R] [IsTopologicalGroup R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (ν : Measure R) [ν.IsHaarMeasure] (ψ : G →* R) (hψ : Continuous ψ)
    (hs : ∀ t, ∃ h ∈ H, ψ h = t)
    (hf : ∀ t, ∃ W ∈ 𝓝 t, ∃ K : Set G, IsCompact K ∧ (H : Set G) ∩ ψ ⁻¹' W ⊆ K) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ s, MeasurableSet s → μ (ψ ⁻¹' s ∩ H) = ν s := by
  classical
  have hψm : Measurable ψ := hψ.measurable
  set μ₀ : Measure G := Measure.haar
  set ρ : Measure R := (μ₀.restrict (H : Set G)).map ψ with hρdef
  have hρ : ∀ s, MeasurableSet s → ρ s = μ₀ (ψ ⁻¹' s ∩ H) := by
    intro s hsm
    rw [hρdef, Measure.map_apply hψm hsm, Measure.restrict_apply (hψm hsm)]
  have : ρ.IsMulLeftInvariant := by
    refine ⟨fun r => ?_⟩
    obtain ⟨h, hh, rfl⟩ := hs r
    refine Measure.ext fun s hsm => ?_
    have hpre : ψ ⁻¹' ((fun x => ψ h * x) ⁻¹' s) ∩ H = (fun x => h * x) ⁻¹' (ψ ⁻¹' s ∩ H) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, SetLike.mem_coe]
      rw [Subgroup.mul_mem_cancel_left H hh]
    rw [Measure.map_apply (measurable_const_mul _) hsm, hρ _ ((measurable_const_mul _) hsm), hρ _ hsm,
      hpre, measure_preimage_mul]
  have : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun C hC => ?_⟩
    choose W hW K hK hWK using hf
    obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun x => interior (W x))
      (fun x _ => interior_mem_nhds.2 (hW x))
    have hUo : IsOpen (⋃ x ∈ t, interior (W x)) := isOpen_biUnion fun x _ => isOpen_interior
    calc ρ C ≤ ρ (⋃ x ∈ t, interior (W x)) := measure_mono ht
      _ = μ₀ (ψ ⁻¹' (⋃ x ∈ t, interior (W x)) ∩ H) := hρ _ hUo.measurableSet
      _ ≤ μ₀ (⋃ x ∈ t, K x) := by
          apply measure_mono
          rintro y ⟨hy1, hy2⟩
          simp only [Set.mem_preimage, Set.mem_iUnion] at hy1 ⊢
          obtain ⟨x, hx, hyx⟩ := hy1
          exact ⟨x, hx, hWK x ⟨hy2, show ψ y ∈ W x from interior_subset hyx⟩⟩
      _ ≤ ∑ x ∈ t, μ₀ (K x) := measure_biUnion_finset_le t K
      _ < ⊤ := ENNReal.sum_lt_top.2 fun x _ => (hK x).measure_lt_top
  have hρ0 : ρ ≠ 0 := by
    intro h0
    have h1 := hρ Set.univ MeasurableSet.univ
    rw [h0] at h1
    simp only [Measure.coe_zero, Pi.zero_apply, Set.preimage_univ, Set.univ_inter] at h1
    exact (hH.measure_pos μ₀ ⟨1, H.one_mem⟩).ne' h1.symm
  have hc := Measure.isMulLeftInvariant_eq_smul ρ ν
  set c := Measure.haarScalarFactor ρ ν
  have hc0 : c ≠ 0 := by
    intro h0
    apply hρ0
    rw [hc, h0, zero_smul]
  have : (c⁻¹ • μ₀).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ (inv_ne_zero hc0)
  refine ⟨c⁻¹ • μ₀, inferInstance, fun s hsm => ?_⟩
  have h1 := hρ s hsm
  rw [hc] at h1
  rw [Measure.smul_apply, ← h1, Measure.smul_apply, smul_smul, inv_mul_cancel₀ hc0, one_smul]

variable {P Q : ℕ}

theorem jpq_mul_self : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  unfold Formalism.UG.Jpq
  simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem left_inv_of_unitary {u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ}
    (h : uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q) : Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q * u = 1 := by
  calc Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q * (uᴴ * Formalism.UG.Jpq P Q * u) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, jpq_mul_self]

def mkU (u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (h : uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q) :
    UpqT P Q :=
  (⟨⟨u, Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q, mul_eq_one_comm.1 (left_inv_of_unitary h),
    left_inv_of_unitary h⟩, h⟩ : Formalism.UG.Upq P Q)

theorem mat_mkU (u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (h) : UpqT.mat (mkU u h) = u := rfl

theorem mat_injective : Function.Injective (UpqT.mat (P := P) (Q := Q)) := by
  intro a b h
  let a' : Formalism.UG.Upq P Q := a
  let b' : Formalism.UG.Upq P Q := b
  have h' : a'.1 = b'.1 := Units.ext h
  exact (Subtype.ext h' : a' = b')

theorem mat_mul (b c : UpqT P Q) : UpqT.mat (b * c) = UpqT.mat b * UpqT.mat c := rfl

theorem mat_one : UpqT.mat (1 : UpqT P Q) = 1 := rfl

theorem mat_unitary (b : UpqT P Q) : (UpqT.mat b)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat b = Formalism.UG.Jpq P Q := by
  have hb := (b : Formalism.UG.Upq P Q).2
  exact hb

theorem continuous_mat : Continuous (UpqT.mat (P := P) (Q := Q)) := by
  exact Units.continuous_val.comp continuous_subtype_val

theorem continuous_mkU {X : Type} [TopologicalSpace X] (f : X → Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)
    (hf : Continuous f) (h : ∀ x, (f x)ᴴ * Formalism.UG.Jpq P Q * f x = Formalism.UG.Jpq P Q) :
    Continuous fun x => mkU (f x) (h x) := by
  have hinv : Continuous fun x => Formalism.UG.Jpq P Q * (f x)ᴴ * Formalism.UG.Jpq P Q :=
    (continuous_const.matrix_mul hf.matrix_conjTranspose).matrix_mul continuous_const
  unfold mkU
  refine (Units.continuous_iff.2 ⟨?_, ?_⟩).subtype_mk _
  · exact hf
  · exact hinv

variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}

theorem exists_frame (h : Formalism.UG.HasSignature G P Q) :
    ∃ (A : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ) (L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ),
      Aᴴ * Formalism.UG.Jpq P Q * A = G ∧ L * A = 1 ∧ A * L = 1 := by
  unfold Formalism.UG.HasSignature at h
  obtain ⟨e, g, hg⟩ := h
  have hg' : (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Matrix.reindex e e G * g = Formalism.UG.Jpq P Q := hg
  have key : Matrix.reindex e e G =
      ((g⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Formalism.UG.Jpq P Q *
        ((g⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
    set u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := g.val
    set v : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := (g⁻¹).val
    have huv : u * v = 1 := Units.mul_inv g
    calc Matrix.reindex e e G = (u * v)ᴴ * Matrix.reindex e e G * (u * v) := by
          rw [huv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = vᴴ * (uᴴ * Matrix.reindex e e G * u) * v := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = vᴴ * Formalism.UG.Jpq P Q * v := by rw [hg']
  refine ⟨((g⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix id e,
    (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix e id, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_id_id (Formalism.UG.Jpq P Q),
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← key]
    ext i j
    simp [Matrix.reindex_apply]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Units.mul_inv, Matrix.submatrix_one_equiv]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ e.bijective, Units.inv_mul, Matrix.submatrix_id_id]

variable {A A' : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ} {L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ}

theorem conj_frame (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) : Lᴴ * G * L = Formalism.UG.Jpq P Q := by
  rw [← hA]
  have h1 : Lᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) * L = (A * L)ᴴ * Formalism.UG.Jpq P Q * (A * L) := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [h1, hr, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem change_unitary (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) (hA' : A'ᴴ * Formalism.UG.Jpq P Q * A' = G) :
    (A' * L)ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Formalism.UG.Jpq P Q := by
  rw [Matrix.conjTranspose_mul]
  have h1 : Lᴴ * A'ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Lᴴ * (A'ᴴ * Formalism.UG.Jpq P Q * A') * L := by
    simp only [Matrix.mul_assoc]
  rw [h1, hA', conj_frame hA hr]

theorem conj_unitary (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᴴ * G * g = G) : (A * g * L)ᴴ * Formalism.UG.Jpq P Q * (A * g * L) = Formalism.UG.Jpq P Q := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have h1 : Lᴴ * (gᴴ * Aᴴ) * Formalism.UG.Jpq P Q * (A * g * L) =
      Lᴴ * (gᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) * g) * L := by
    simp only [Matrix.mul_assoc]
  rw [h1, hA, hg, conj_frame hA hr]

theorem conj_unitary_back (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) (b : UpqT P Q) :
    (L * UpqT.mat b * A)ᴴ * G * (L * UpqT.mat b * A) = G := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have h1 : Aᴴ * ((UpqT.mat b)ᴴ * Lᴴ) * G * (L * UpqT.mat b * A) =
      Aᴴ * ((UpqT.mat b)ᴴ * (Lᴴ * G * L) * UpqT.mat b) * A := by
    simp only [Matrix.mul_assoc]
  rw [h1, conj_frame hA hr, mat_unitary, hA]

theorem exists_hom {Γ : Type} [Group Γ] [TopologicalSpace Γ] (m : Γ → Matrix (Fin n) (Fin n) ℂ)
    (hm : Continuous m) (hmul : ∀ g h, m (g * h) = m g * m h) (hu : ∀ h, (m h)ᴴ * G * m h = G)
    (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hl : L * A = 1) (hr : A * L = 1) :
    ∃ ψ : Γ →* UpqT P Q, Continuous ψ ∧ ∀ h, UpqT.mat (ψ h) = A * m h * L := by
  let f : Γ → UpqT P Q := fun x => mkU (A * m x * L) (conj_unitary hA hr (hu x))
  have hf : ∀ x, UpqT.mat (f x) = A * m x * L := fun x => mat_mkU _ _
  refine ⟨MonoidHom.mk' f fun x y => mat_injective ?_, ?_, fun x => hf x⟩
  · rw [mat_mul, hf, hf, hf, hmul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc L, hl, Matrix.one_mul]
  · show Continuous f
    exact continuous_mkU (fun x => A * m x * L) ((continuous_const.matrix_mul hm).matrix_mul continuous_const)
      (fun x => conj_unitary hA hr (hu x))

theorem read_iff (hl : L * A = 1) (hr : A * L = 1) (u : UpqT P Q) (hu : UpqT.mat u = A' * L)
    {g : Matrix (Fin n) (Fin n) ℂ} (t : UpqT P Q) (ht : UpqT.mat t = A * g * L) (B : Set (UpqT P Q)) :
    (∃ b ∈ B, UpqT.mat b * A' = A' * g) ↔ t ∈ (fun b => b * u⁻¹) ⁻¹' ((fun b => u * b) ⁻¹' B) := by
  have hA' : A' = UpqT.mat u * A := by rw [hu, Matrix.mul_assoc, hl, Matrix.mul_one]
  have hinv : UpqT.mat u⁻¹ * UpqT.mat u = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  have key : ∀ b : UpqT P Q, UpqT.mat b * A' = A' * g ↔ b = u * (t * u⁻¹) := by
    intro b
    constructor
    · intro h
      have h2 : UpqT.mat (b * u) = UpqT.mat (u * t) := by
        rw [mat_mul, mat_mul, ht]
        calc UpqT.mat b * UpqT.mat u = UpqT.mat b * A' * L := by rw [hu, Matrix.mul_assoc]
          _ = A' * g * L := by rw [h]
          _ = UpqT.mat u * (A * g * L) := by rw [hA']; simp only [Matrix.mul_assoc]
      have h3 := mat_injective h2
      rw [← mul_assoc, ← h3, mul_inv_cancel_right]
    · rintro rfl
      rw [mat_mul, mat_mul, ht, hA']
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (UpqT.mat u⁻¹), hinv, Matrix.one_mul, hl, Matrix.mul_one]
  simp only [Set.mem_preimage]
  constructor
  · rintro ⟨b, hb, h⟩
    rwa [(key b).1 h] at hb
  · intro h
    exact ⟨_, h, (key _).2 rfl⟩

end GlobalTheory.VolPairExists
