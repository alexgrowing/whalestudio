import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbitProper

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

theorem companionMatrixOfCoeffs_pow_mulVec_first_basis (p : Fin r → k) (n : ℕ) (hn : n < r) :
    (companion p ^ n) *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) = Pi.single (⟨n, hn⟩ : Fin r) 1 := by
  induction n with
  | zero =>
    rw [pow_zero, one_mulVec]
    funext i
    simp [Pi.single_apply, Fin.ext_iff]
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ih (by omega), mulVec_single_one]
    funext i
    simp only [companion, transpose_apply, of_apply, Pi.single_apply, Fin.ext_iff]
    have : ¬ (n + 1 = r) := by omega
    simp [this]

theorem conj_pow_GL (g : GL (Fin r) k) (A : Matrix (Fin r) (Fin r) k) (j : ℕ) :
    ((g : Matrix (Fin r) (Fin r) k) * A * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)) ^ j =
      (g : Matrix (Fin r) (Fin r) k) * A ^ j * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  exact Units.conj_pow g A j

theorem Bm_sec (a : Inv r k) : Bm (sec a) = 1 := by
  ext i j
  simp only [Bm, sec, of_apply]
  rw [companionMatrixOfCoeffs_pow_mulVec_first_basis a.1 j j.2, one_apply, Pi.single_apply]

theorem Bm_act (g : GL (Fin r) k) (Y : Gl r k) :
    Bm (act g Y) = (g : Matrix (Fin r) (Fin r) k) * Bm Y := by
  ext i j
  simp only [Bm, act, of_apply]
  rw [conj_pow_GL, mulVec_mulVec, mul_assoc _ _ (g : Matrix (Fin r) (Fin r) k), Units.inv_mul, mul_one,
    ← mulVec_mulVec]
  simp [mul_apply, mulVec, dotProduct]

theorem Cm_act (g : GL (Fin r) k) (Y : Gl r k) :
    Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  ext i j
  simp only [Cm, act, of_apply]
  rw [conj_pow_GL, vecMul_vecMul, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, ← vecMul_vecMul]
  simp [mul_apply, vecMul, dotProduct]

theorem Cm_sec (a : Inv r k) : Cm (sec a) = hankel a := by
  ext i j
  simp only [Cm, hankel, mom, sec, of_apply]
  rw [pow_add, ← mulVec_mulVec, companionMatrixOfCoeffs_pow_mulVec_first_basis a.1 j j.2, mulVec_single_one, dotProduct_comm]
  simp [vecMul, dotProduct, transpose_apply, mul_comm]

end Alg

section Top
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem cont_companion : Continuous (fun p : Fin r → F => companion p) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [companion, of_apply]
  split_ifs
  · exact ((continuous_apply i)).neg
  all_goals exact continuous_const

theorem cont_sec : Continuous (fun a : Inv r F => sec a) := by
  unfold sec
  exact (cont_companion.comp continuous_fst).prodMk
    (continuous_const.prodMk ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))

theorem cont_act : Continuous (fun p : GL (Fin r) F × Gl r F => act p.1 p.2) := by
  have h1 : Continuous (fun p : GL (Fin r) F × Gl r F => ((p.1 : Matrix (Fin r) (Fin r) F))) :=
    Units.continuous_val.comp continuous_fst
  have h2 : Continuous (fun p : GL (Fin r) F × Gl r F => (((p.1)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
    Units.continuous_coe_inv.comp continuous_fst
  unfold act
  exact ((h1.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul h2).prodMk
    ((h1.matrix_mulVec (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
      (((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).matrix_vecMul h2).prodMk
        (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))))

theorem cont_charpoly_coeff (i : ℕ) :
    Continuous (fun A : Matrix (Fin r) (Fin r) F => A.charpoly.coeff i) := by
  have h : ∀ A : Matrix (Fin r) (Fin r) F, A.charpoly.coeff i =
      MvPolynomial.eval (fun ij : Fin r × Fin r => A ij.1 ij.2)
        (MvPolynomial.map (Int.castRingHom F) ((Matrix.charpoly.univ ℤ (Fin r)).coeff i)) := by
    intro A
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, Matrix.charpoly.univ_coeff_eval₂Hom]
    rfl
  simp_rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem cont_mom (n : ℕ) : Continuous (fun Y : Gl r F => mom Y n) := by
  unfold mom
  exact (continuous_fst.comp (continuous_snd.comp continuous_snd)).dotProduct
    (((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow n).matrix_mulVec (continuous_fst.comp continuous_snd))

theorem cont_inv : Continuous (fun Y : Gl r F => inv Y) := by
  unfold inv
  exact (continuous_pi fun i : Fin r => (cont_charpoly_coeff (r := r) (F := F) (i : ℕ)).comp continuous_fst).prodMk
    ((continuous_pi fun i : Fin r => cont_mom (r := r) (F := F) (i : ℕ)).prodMk
      (show Continuous fun Y : Gl r F => Y.2.2.2 from continuous_snd.comp (continuous_snd.comp continuous_snd)))

theorem cont_hankel : Continuous (fun a : Inv r F => hankel a) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun a : Inv r F => mom (sec a) ((i : ℕ) + (j : ℕ))
    exact (cont_mom _).comp cont_sec

theorem cont_Delta : Continuous (fun a : Inv r F => Delta a) := cont_hankel.matrix_det

end Top

section Cpt
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem cont_Bm : Continuous (fun Y : Gl r F => Bm Y) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun Y : Gl r F => ((Y.1 ^ (j : ℕ)) *ᵥ Y.2.1) i
    exact (continuous_apply i).comp
      (((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow _).matrix_mulVec
        (continuous_fst.comp continuous_snd))

theorem cont_Cm : Continuous (fun Y : Gl r F => Cm Y) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun Y : Gl r F => (Y.2.2.1 ᵥ* (Y.1 ^ (i : ℕ))) j
    exact (continuous_apply j).comp
      ((continuous_fst.comp (continuous_snd.comp continuous_snd)).matrix_vecMul
        ((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow _))

theorem contAt_hankel_inv (a : Inv r F) (ha : Delta a ≠ 0) :
    ContinuousAt (fun b : Inv r F => (hankel b)⁻¹) a := by
  refine (continuousAt_matrix_inv _ ?_).comp cont_hankel.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ ha

theorem coe_eq (g : GL (Fin r) F) (a : Inv r F) :
    (g : Matrix (Fin r) (Fin r) F) = Bm (act g (sec a)) := by
  rw [Bm_act, Bm_sec, mul_one]

theorem coe_inv_eq (g : GL (Fin r) F) (a : Inv r F) (ha : Delta a ≠ 0) :
    ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = (hankel a)⁻¹ * Cm (act g (sec a)) := by
  have h : IsUnit (hankel a).det := isUnit_iff_ne_zero.mpr ha
  rw [Cm_act, Cm_sec, ← mul_assoc, nonsing_inv_mul _ h, one_mul]

theorem isCompact_set (C : Set (Gl r F)) (Ω : Set (Inv r F)) (hC : IsCompact C) (hΩ : IsCompact Ω)
    (hD : ∀ a ∈ Ω, Delta a ≠ 0) :
    IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
  set Φ : Gl r F × Inv r F → (Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ) × Inv r F :=
    fun q => ((Bm q.1, MulOpposite.op ((hankel q.2)⁻¹ * Cm q.1)), q.2) with hΦdef
  have hΦ : ContinuousOn Φ (C ×ˢ Ω) := by
    intro q hq
    apply ContinuousAt.continuousWithinAt
    have h3 : ContinuousAt (fun q : Gl r F × Inv r F => (hankel q.2)⁻¹) q :=
      (contAt_hankel_inv q.2 (hD q.2 hq.2)).comp continuous_snd.continuousAt
    exact (((cont_Bm.comp continuous_fst).continuousAt).prodMk
      (MulOpposite.continuous_op.continuousAt.comp (h3.mul (cont_Cm.comp continuous_fst).continuousAt))).prodMk
      continuous_snd.continuousAt
  set e : GL (Fin r) F × Inv r F → (Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ) × Inv r F :=
    Prod.map (Units.embedProduct (Matrix (Fin r) (Fin r) F)) id with hedef
  have he : Topology.IsClosedEmbedding e :=
    Units.isClosedEmbedding_embedProduct.prodMap Topology.IsClosedEmbedding.id
  have hK : IsCompact (e ⁻¹' (Φ '' (C ×ˢ Ω))) :=
    he.isCompact_preimage ((hC.prod hΩ).image_of_continuousOn hΦ)
  have hS : IsClosed {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
    have hc : Continuous (fun p : GL (Fin r) F × Inv r F => act p.1 (sec p.2)) :=
      cont_act.comp (continuous_fst.prodMk (cont_sec.comp continuous_snd))
    exact (hΩ.isClosed.preimage continuous_snd).inter (hC.isClosed.preimage hc)
  refine hK.of_isClosed_subset hS ?_
  rintro ⟨g, a⟩ ⟨ha, hY⟩
  refine ⟨(act g (sec a), a), ⟨hY, ha⟩, ?_⟩
  simp only [hΦdef, hedef, Prod.map, id, Units.embedProduct_apply]
  rw [← coe_eq g a, ← coe_inv_eq g a (hD a ha)]

end Cpt

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), Continuous (fun p : GL (Fin r) F × Inv r F => act p.1 (sec p.2)) ∧ Continuous (fun Y : Gl r F => inv Y) ∧ Continuous (fun a : Inv r F => Delta a) ∧ ∀ (C : Set (Gl r F)) (Ω : Set (Inv r F)), IsCompact C → IsCompact Ω → (∀ a ∈ Ω, Delta a ≠ 0) → IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
  intro F E _ _ _ _ _ r
  exact ⟨cont_act.comp (continuous_fst.prodMk (cont_sec.comp continuous_snd)), cont_inv, cont_Delta,
    fun C Ω hC hΩ hD => isCompact_set C Ω hC hΩ hD⟩

end GlobalTheory.JR.OrbitProper
