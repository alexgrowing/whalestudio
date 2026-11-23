import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceSplitsCompletelyNotMemEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNormOneIdeles
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst

noncomputable section

namespace GlobalTheory.NormOneIdele.QuasiRefl

open Matrix

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

private def qr (P : Matrix (Fin n) (Fin n) R) (z : R) : Matrix (Fin n) (Fin n) R := 1 + (z - 1) • P

private theorem qr_one (P : Matrix (Fin n) (Fin n) R) : qr P 1 = 1 := by simp [qr]

private theorem qr_mul {P : Matrix (Fin n) (Fin n) R} (hP : P * P = P) (z w : R) : qr P z * qr P w = qr P (z * w) := by
  simp only [qr, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP]
  module

private theorem qr_map {S : Type} [CommRing S] (f : R →+* S) (P : Matrix (Fin n) (Fin n) R) (z : R) :
    (qr P z).map f = qr (P.map f) (f z) := by
  ext i j
  simp only [qr, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> simp

private theorem qr_unitary (f : R →+* R) {P J : Matrix (Fin n) (Fin n) R} (hP : P * P = P) (hPJ : Pᵀ * J = J * P.map f)
    {z : R} (hz : z * f z = 1) : (qr P z)ᵀ * J * (qr P z).map f = J := by
  rw [qr_map]
  have hP' : P.map f * P.map f = P.map f := by rw [← Matrix.map_mul, hP]
  have h1 : (qr P z)ᵀ = 1 + (z - 1) • Pᵀ := by simp [qr, Matrix.transpose_add, Matrix.transpose_smul]
  rw [h1]
  simp only [qr, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hPJ, Matrix.mul_assoc, hP']
  linear_combination (norm := module) hz • (J * P.map f)

private theorem det_qr_vecMulVec (a b : Fin n → R) (z : R) : (qr (vecMulVec a b) z).det = 1 + (z - 1) * (b ⬝ᵥ a) := by
  have : qr (vecMulVec a b) z = 1 + replicateCol Unit ((z - 1) • a) * replicateRow Unit b := by
    ext i j
    simp [qr, vecMulVec_apply, replicateCol, replicateRow, Matrix.mul_apply, mul_assoc]
  rw [this, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul]

private def qrU {P : Matrix (Fin n) (Fin n) R} (hP : P * P = P) (x : Rˣ) : GL (Fin n) R :=
  ⟨qr P x, qr P ↑x⁻¹, by rw [qr_mul hP, x.mul_inv, qr_one], by rw [qr_mul hP, x.inv_mul, qr_one]⟩

private theorem map_vecMulVec {S : Type} [CommRing S] (f : R →+* S) (a b : Fin n → R) :
    (vecMulVec a b).map f = vecMulVec (fun i => f (a i)) (fun i => f (b i)) := by
  ext i j
  simp [vecMulVec_apply]

end Alg

section Herm

variable {E : Type} [Field E] {n : ℕ} (σ : E →+* E)

private def sv (e : Fin n → E) : Fin n → E := fun i => σ (e i)

private theorem single_dot_mulVec_single (J : Matrix (Fin n) (Fin n) E) (a b : Fin n) (x y : E) :
    Pi.single a x ⬝ᵥ J *ᵥ Pi.single b y = x * J a b * y := by
  simp [dotProduct, mulVec, Pi.single_apply, mul_assoc]

private theorem exists_aniso [CharZero E] (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E)
    (herm : ∀ i j, σ (J j i) = J i j) (hJ : J ≠ 0) : ∃ e : Fin n → E, e ⬝ᵥ J *ᵥ sv σ e ≠ 0 := by
  by_cases hd : ∃ i, J i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    refine ⟨Pi.single i 1, ?_⟩
    have h1 : sv σ (Pi.single i (1 : E)) = Pi.single i 1 := by
      funext k
      by_cases h : k = i
      · subst h; simp [sv]
      · simp [sv, Pi.single_apply, h]
    rw [h1, single_dot_mulVec_single]
    simpa using hi
  · push_neg at hd
    obtain ⟨i, j, hij⟩ : ∃ i j, J i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hJ (Matrix.ext fun i j => h i j)
    have hne : i ≠ j := by
      rintro rfl
      exact hij (hd i)
    have hσij : σ (J i j) ≠ 0 := (map_ne_zero σ).2 hij
    refine ⟨Pi.single i 1 + Pi.single j (σ (J i j))⁻¹, ?_⟩
    have h1 : sv σ (Pi.single i 1 + Pi.single j (σ (J i j))⁻¹) = Pi.single i 1 + Pi.single j (J i j)⁻¹ := by
      funext k
      by_cases hk : k = i
      · subst hk; simp [sv, hne]
      · by_cases hk' : k = j
        · subst hk'; simp [sv, hk, map_inv₀, hσ]
        · simp [sv, hk, hk']
    rw [h1]
    simp only [add_dotProduct, mulVec_add, dotProduct_add, single_dot_mulVec_single, hd, herm j i]
    have h2 : J i j * (J i j)⁻¹ = 1 := mul_inv_cancel₀ hij
    have h3 : (σ (J i j))⁻¹ * σ (J i j) = 1 := inv_mul_cancel₀ hσij
    rw [← herm j i]
    simp only [mul_one, one_mul, mul_zero, zero_mul, zero_add, add_zero, h2, h3]
    norm_num

variable {σ}

private theorem sigma_form (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} (herm : ∀ i j, σ (J j i) = J i j)
    (e : Fin n → E) : σ (e ⬝ᵥ J *ᵥ sv σ e) = e ⬝ᵥ J *ᵥ sv σ e := by
  simp only [dotProduct, mulVec, sv, map_sum, map_mul, hσ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [herm]
  ring

private theorem sigma_mulVec (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} (herm : ∀ i j, σ (J j i) = J i j)
    (e : Fin n → E) (k : Fin n) : σ ((J *ᵥ sv σ e) k) = (e ᵥ* J) k := by
  simp only [mulVec, vecMul, dotProduct, sv, map_sum, map_mul, hσ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [herm]
  ring

variable (σ) in

private def proj (J : Matrix (Fin n) (Fin n) E) (e : Fin n → E) : Matrix (Fin n) (Fin n) E :=
  vecMulVec e ((e ⬝ᵥ J *ᵥ sv σ e)⁻¹ • (J *ᵥ sv σ e))

private theorem proj_dot {J : Matrix (Fin n) (Fin n) E} {e : Fin n → E} (hc : e ⬝ᵥ J *ᵥ sv σ e ≠ 0) :
    ((e ⬝ᵥ J *ᵥ sv σ e)⁻¹ • (J *ᵥ sv σ e)) ⬝ᵥ e = 1 := by
  rw [smul_dotProduct, dotProduct_comm (J *ᵥ sv σ e) e, smul_eq_mul, inv_mul_cancel₀ hc]

private theorem proj_mul {J : Matrix (Fin n) (Fin n) E} {e : Fin n → E} (hc : e ⬝ᵥ J *ᵥ sv σ e ≠ 0) :
    proj σ J e * proj σ J e = proj σ J e := by
  rw [proj, vecMulVec_mul_vecMulVec, proj_dot hc, one_smul]

private theorem proj_adj (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} (herm : ∀ i j, σ (J j i) = J i j)
    (e : Fin n → E) : (proj σ J e)ᵀ * J = J * (proj σ J e).map σ := by
  rw [proj, transpose_vecMulVec, vecMulVec_mul, map_vecMulVec, mul_vecMulVec]
  ext i k
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, sigma_form hσ herm,
    sigma_mulVec hσ herm]
  change _ = (J *ᵥ sv σ e) i * _
  ring

end Herm

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem cA_inclR (σ : E →ₐ[F] E) (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR]

end Adelic

end GlobalTheory.NormOneIdele.QuasiRefl

open GlobalTheory.NormOneIdele.QuasiRefl Matrix in

theorem _root_.GlobalTheory.T.norm_one_idele_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (V : Spc F E n) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s → 0 < n →
    ∃ sec : GlobalTheory.NormOneIdele.N1 F E σ →* UA σ V.J, Continuous sec ∧
      (∀ z, (mat (sec z)).det = ((z : (AE F E)ˣ) : AE F E)) ∧
      (∀ z : GlobalTheory.NormOneIdele.N1 F E σ, (∃ e : E, ((z : (AE F E)ˣ) : AE F E) = inclR (F := F) (AF F) e) → sec z ∈ ratU σ V.J) ∧
      (∀ (v : Pl F) (z : GlobalTheory.NormOneIdele.N1 F E σ), At (evFin F v) (((z : (AE F E)ˣ) : AE F E) - 1) → sec z ∈ UAt σ V (evFin F v)) := by
  intro F E _ _ _ _ _ σ B n V r s hB hV hn
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
  set τ : E →+* ℂ := (B.emb w).1
  have hσ : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star])
  have hJ : V.J ≠ 0 := by
    intro h0
    obtain ⟨hrs, A, hA⟩ := hV.sig w
    rw [h0] at hA
    simp only [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul] at hA
    rcases Nat.eq_zero_or_pos r with hr | hr
    · have hs : 0 < s := by omega
      have := congrFun (congrFun hA (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)
      simp at this
    · have := congrFun (congrFun hA (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
      simp at this
  let σ' : E →+* E := σ
  have hσ' : ∀ x, σ' (σ' x) = x := hσ
  have herm : ∀ i j, σ' (V.J j i) = V.J i j := hV.herm
  obtain ⟨e, hc⟩ := exists_aniso σ' hσ' V.J herm hJ
  let f : E →+* AE F E := inclR (F := F) (AF F)
  have hPP := proj_mul (σ := σ') hc
  have hPJ := proj_adj hσ' herm e
  set P := proj σ' V.J e with hPdef
  let Q : Matrix (Fin n) (Fin n) (AE F E) := P.map f
  have hQQ : Q * Q = Q := by rw [← Matrix.map_mul, hPP]
  have hQσ : Q.map (cA σ : AE F E →+* AE F E) = (P.map σ').map f := by
    ext i j
    exact cA_inclR σ (P i j)
  have hQJ : Qᵀ * incM F V.J = incM F V.J * Q.map (cA σ : AE F E →+* AE F E) := by
    rw [hQσ]
    simp only [incM, Q, f, ← Matrix.transpose_map, ← Matrix.map_mul, hPJ]
  let sec : GlobalTheory.NormOneIdele.N1 F E σ →* UA σ V.J :=
    { toFun := fun z => ⟨qrU hQQ (z : (AE F E)ˣ),
        qr_unitary (cA σ : AE F E →+* AE F E) hQQ hQJ (GlobalTheory.NormOneIdele.mem_normOneIdeles.1 z.2)⟩
      map_one' := Subtype.ext (Units.ext (by simp [qrU, qr_one]))
      map_mul' := fun a b => Subtype.ext (Units.ext (by simp [qrU, qr_mul hQQ])) }
  have hmat : ∀ z, mat (sec z) = qr Q ((z : (AE F E)ˣ) : AE F E) := fun z => rfl
  refine ⟨sec, ?_, ?_, ?_, ?_⟩
  · refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun z : GlobalTheory.NormOneIdele.N1 F E σ => qr Q (((z : (AE F E)ˣ)) : AE F E)
      unfold qr
      exact continuous_const.add (((Units.continuous_val.comp continuous_subtype_val).sub continuous_const).smul
        continuous_const)
    · show Continuous fun z : GlobalTheory.NormOneIdele.N1 F E σ => qr Q ((((z : (AE F E)ˣ))⁻¹ : (AE F E)ˣ) : AE F E)
      unfold qr
      exact continuous_const.add (((Units.continuous_coe_inv.comp continuous_subtype_val).sub continuous_const).smul
        continuous_const)
  · intro z
    rw [hmat]
    have hQv : Q = vecMulVec (fun i => f (e i)) (fun i => f (((e ⬝ᵥ V.J *ᵥ sv σ' e)⁻¹ • (V.J *ᵥ sv σ' e)) i)) :=
      map_vecMulVec f _ _
    rw [hQv, det_qr_vecMulVec]
    have h1 : (fun i => f (((e ⬝ᵥ V.J *ᵥ sv σ' e)⁻¹ • (V.J *ᵥ sv σ' e)) i)) ⬝ᵥ (fun i => f (e i)) = 1 := by
      have h2 := congrArg f (proj_dot (σ := σ') hc)
      rw [RingHom.map_dotProduct, map_one] at h2
      exact h2
    rw [h1]
    ring
  · rintro z ⟨e', he'⟩
    rw [ratU, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    by_cases h0 : e' = 0
    · have h01 := (z : (AE F E)ˣ).mul_inv
      rw [he', h0, map_zero, zero_mul] at h01
      haveI : Subsingleton (AE F E) := subsingleton_of_zero_eq_one h01
      exact ⟨1, Units.ext (Matrix.ext fun i j => Subsingleton.elim _ _)⟩
    · refine ⟨qrU hPP (Units.mk0 e' h0), Units.ext ?_⟩
      ext i j
      rw [Matrix.GeneralLinearGroup.map_apply]
      change f (qr P e' i j) = qr Q ((z : (AE F E)ˣ) : AE F E) i j
      rw [he']
      change f (qr P e' i j) = qr (P.map f) (f e') i j
      rw [← qr_map]
      rfl
  · intro v z hz u hu
    change u • (qr Q ((z : (AE F E)ˣ) : AE F E) - 1) = 0
    unfold qr
    rw [add_sub_cancel_left, ← smul_assoc, hz u hu, zero_smul]
