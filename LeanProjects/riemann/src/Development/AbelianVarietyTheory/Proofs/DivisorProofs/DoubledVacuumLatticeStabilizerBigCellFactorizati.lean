import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFactorisationDoubledUnitaryGroup
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacFactor

open Matrix GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

@[reducible] def invTwoE : Invertible (2 : AE F E) :=
  (Invertible.map (algebraMap (AF F) (AE F E)) (2 : AF F)).copy 2 (map_ofNat _ 2).symm

theorem invOf_two_eq [Invertible (2 : AE F E)] :
    (⅟(2 : AE F E)) = algebraMap (AF F) (AE F E) (⅟(2 : AF F)) :=
  invOf_eq_right_inv (by rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, mul_invOf_self, map_one])

theorem valued_two {v : Pl F} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : Valued.v (2 : Fv F v) = 1 := by
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (2 : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h2] at this
  convert this using 2
  exact (map_ofNat _ 2).symm

theorem evFin_half_mem {v : Pl F} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have e : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h := congrArg Valued.v e
  rw [map_mul, valued_two h2, mul_one, map_one] at h
  rw [h]

theorem half_smul_mem {d : ℕ} {W : Spc F E d} {v : Pl F} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : (⅟(2 : AF F)) • y ∈ GlobalTheory.InertSph.latAt W v := by
  have hle : GlobalTheory.InertSph.latAt W v ≤ (GlobalTheory.InertSph.latAt W v).comap
      (DistribMulAction.toAddMonoidHom (Fin d → AE F E) (⅟(2 : AF F))) := by
    show AddSubgroup.closure _ ≤ _
    rw [AddSubgroup.closure_le]
    rintro z ⟨a, ha, hint, y, hy, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply, smul_smul]
    refine AddSubgroup.subset_closure ⟨⅟(2 : AF F) * a, fun u hu => ?_, ?_, y, hy, rfl⟩
    · rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]; exact mul_mem (evFin_half_mem h2) hint
  exact hle hy

section Lat

variable {d : ℕ} {W : Spc F E d} {v : Pl F}

theorem latD_add {z w : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) (hw : w ∈ latD W v) : z + w ∈ latD W v :=
  ⟨add_mem hz.1 hw.1, add_mem hz.2 hw.2⟩

theorem latD_sub {z w : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) (hw : w ∈ latD W v) : z - w ∈ latD W v :=
  ⟨sub_mem hz.1 hw.1, sub_mem hz.2 hw.2⟩

theorem latD_half [Invertible (2 : AE F E)] (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {z : Fin d ⊕ Fin d → AE F E}
    (hz : z ∈ latD W v) : (⅟(2 : AE F E)) • z ∈ latD W v := by
  rw [invOf_two_eq, algebraMap_smul]
  exact ⟨half_smul_mem h2 hz.1, half_smul_mem h2 hz.2⟩

theorem latD_diag {y : Fin d → AE F E} (hy : y ∈ GlobalTheory.InertSph.latAt W v) :
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1) *ᵥ y ∈ latD W v := by
  rw [fromRows_mulVec, one_mulVec]
  exact ⟨hy, hy⟩

theorem latD_anti {y : Fin d → AE F E} (hy : y ∈ GlobalTheory.InertSph.latAt W v) :
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1)) *ᵥ y ∈ latD W v := by
  rw [fromRows_mulVec, one_mulVec, neg_mulVec, one_mulVec]
  exact ⟨hy, neg_mem hy⟩

theorem lat_diagT {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) :
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  rw [fromCols_mulVec, one_mulVec, one_mulVec]
  exact add_mem hz.1 hz.2

theorem lat_antiT {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) :
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  rw [fromCols_mulVec, one_mulVec, neg_mulVec, one_mulVec]
  exact add_mem hz.1 (neg_mem hz.2)

end Lat

section Group

variable {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F}

theorem KD_mul {a b : UD σ W} (ha : a ∈ KD σ W v) (hb : b ∈ KD σ W v) : a * b ∈ KD σ W v := by
  have hm : matD (a * b) = matD a * matD b := rfl
  have hi : matD (a * b)⁻¹ = matD b⁻¹ * matD a⁻¹ := by rw [_root_.mul_inv_rev]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · rw [hm, show matD a * matD b - 1 = (matD a - 1) * matD b + (matD b - 1) by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel, smul_add, ← Matrix.smul_mul, ha.1 u hu, hb.1 u hu,
      Matrix.zero_mul, add_zero]
  · rw [hm, hi, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(ha.2 _ (hb.2 z hz).1).1, (hb.2 _ (ha.2 z hz).2).2⟩

theorem KD_inv {a : UD σ W} (ha : a ∈ KD σ W v) : a⁻¹ ∈ KD σ W v := by
  have h1 : matD a⁻¹ * matD a = 1 := by
    rw [show matD a⁻¹ * matD a = matD (a⁻¹ * a) from rfl, inv_mul_cancel]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · rw [show matD a⁻¹ - 1 = -(matD a⁻¹ * (matD a - 1)) by rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel,
      smul_neg, ← Matrix.mul_smul, ha.1 u hu, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(ha.2 z hz).2, (ha.2 z hz).1⟩

end Group

end GlobalTheory.DblVacFactor

namespace GlobalTheory.DblVacFactor

open Matrix GlobalTheory.DblVac GlobalTheory.BigCell

theorem factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
    IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d).det →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v,
      ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d)⁻¹ *ᵥ z ∈
        GlobalTheory.InertSph.latAt W v) →
    ∃ p q : GlobalTheory.DblVac.UD σ W, p ∈ GlobalTheory.DblVac.KD σ W v ∧ p ∈ GlobalTheory.DblVac.PDiag σ W ∧
      q ∈ GlobalTheory.DblVac.KD σ W v ∧ q ∈ GlobalTheory.DblVac.PAnti σ W ∧ g = p * q := by
  intro F E _ _ _ _ _ σ d W v h2 g hg hdet hC
  letI : Invertible (2 : AE F E) := invTwoE
  have hNt : (antiCols (F := F) (E := E) d)ᵀ = fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) := by
    rw [antiCols, transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  rw [hNt] at hdet hC
  unfold antiCols at hdet hC
  set G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := matD g with hGdef
  set f : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hf
  set J : Matrix (Fin d) (Fin d) (AE F E) := incM F W.J with hJ
  have hG : Gᵀ * dbl J * G.map f = dbl J := g.2
  have h1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map f = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hm1 : (-1 : Matrix (Fin d) (Fin d) (AE F E)).map f = -1 := by rw [Matrix.map_neg _ (map_neg f), h1]
  have hΔT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 1 := by
    rw [transpose_fromRows, transpose_one]
  have hNT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 (-1) := by
    rw [transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  have hΔf : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)).map f =
      fromRows 1 1 := by rw [fromRows_map, h1]
  have hNf : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)).map f =
      fromRows 1 (-1) := by rw [fromRows_map, h1, hm1]
  have hΔtf : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)).map f =
      fromCols 1 1 := by rw [fromCols_map, h1]
  have hNtf : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)).map f =
      fromCols 1 (-1) := by rw [fromCols_map, h1, hm1]
  set D : Matrix (Fin d) (Fin d) (AE F E) := (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) :
    Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) with hDdef
  have hD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hD' : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ hdet
  set M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
    ((fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * D⁻¹) *
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) with hMdef
  have hinv := mul_inv_eq (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) e1
    ((fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * D⁻¹)
  have hmem := mem_unitary f J (dbl J) G _ _ _ _ D⁻¹ hG hΔT hNT hΔf hΔtf hNf hNtf (e3 J) (e4 J) (e5 J) (e6 J) (e7 J) hD
  let P : GL (Fin d ⊕ Fin d) (AE F E) := ⟨1 + ⅟(2 : AE F E) • M, 1 - ⅟(2 : AE F E) • M, hinv.1, hinv.2⟩
  let p : UD σ W := ⟨P, hmem⟩
  have hdetS : IsUnit (⅟(2 : AE F E) • D).det := by
    rw [det_smul]
    exact ((isUnit_of_invertible (⅟(2 : AE F E))).pow _).mul hdet
  let s : GL (Fin d) (AE F E) := ((Matrix.isUnit_iff_isUnit_det _).mpr hdetS).unit

  have hΔtN : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) *
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = 0 := by
    simp [fromCols_mul_fromRows]
  have hMu : ∀ u : AF F, evFin F v u = 0 → u • M = 0 := by
    intro u hu
    have hE : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * (G - 1) *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hΔtN, sub_zero]
    have hu' : u • (G - 1) = 0 := hg.1 u hu
    calc u • M = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * (u • (G - 1)) * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * D⁻¹) * (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
          rw [hMdef, hE]; simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = 0 := by rw [hu']; simp
  have hpK : p ∈ KD σ W v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
    · show u • ((1 + ⅟(2 : AE F E) • M) - 1) = 0
      rw [add_sub_cancel_left, smul_comm, hMu u hu, smul_zero]
    · show (1 + ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_add hz (latD_half h2 (latD_diag (lat_diagT (hg.2 _ (latD_anti (hC _ (lat_antiT hz)))).1)))
    · show (1 - ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_sub hz (latD_half h2 (latD_diag (lat_diagT (hg.2 _ (latD_anti (hC _ (lat_antiT hz)))).1)))
  refine ⟨p, p⁻¹ * g, hpK, ⟨1, ?_⟩, KD_mul (KD_inv hpK) hg, ⟨s, ?_⟩, (mul_inv_cancel_left p g).symm⟩
  · have key : ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hMdef, Matrix.mul_assoc _ _ (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)), e1, Matrix.mul_zero,
        smul_zero, add_zero]
    show ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))
    rw [Units.val_one, Matrix.mul_one]
    exact key
  · show (1 - ⅟(2 : AE F E) • M) * G * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * (s : Matrix (Fin d) (Fin d) (AE F E))
    rw [IsUnit.unit_spec]
    exact q_col G _ _ _ _ D⁻¹ e2 hD'

end GlobalTheory.DblVacFactor
