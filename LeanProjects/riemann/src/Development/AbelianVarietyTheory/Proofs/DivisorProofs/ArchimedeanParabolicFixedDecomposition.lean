import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviLiftOfAdaptedPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSmallUnitary
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.StabDec

open Matrix

section Alg

variable {R : Type} [CommRing R] (c : R →+* R) {d d₁ : ℕ} (Jd : Matrix (Fin d) (Fin d) R)
  (J₁ : Matrix (Fin d₁) (Fin d₁) R) (I : Matrix (Fin d) (Fin d₁) R) (P : Matrix (Fin d₁) (Fin d) R) (x y : Fin d → R)

theorem map_mulVec_fun {k l : ℕ} (M : Matrix (Fin k) (Fin l) R) (v : Fin l → R) :
    (fun i => c ((M *ᵥ v) i)) = M.map c *ᵥ fun i => c (v i) := by
  funext i; exact RingHom.map_mulVec c M v i

theorem transpose_mulVec_fix (q : Matrix (Fin d) (Fin d) R) (hq : qᵀ * Jd * q.map c = Jd) (hqx : q *ᵥ x = x) :
    qᵀ *ᵥ (Jd *ᵥ fun i => c (x i)) = Jd *ᵥ fun i => c (x i) := by
  have hcx : (fun i => c (x i)) = q.map c *ᵥ fun i => c (x i) := by
    conv_lhs => rw [← hqx]
    exact map_mulVec_fun c q x
  conv_lhs => rw [hcx]
  rw [mulVec_mulVec, mulVec_mulVec, hq]

theorem orth_of (hc : Iᵀ * Jd = J₁ * P.map c) (hPx : P *ᵥ x = 0) :
    Iᵀ *ᵥ (Jd *ᵥ fun i => c (x i)) = 0 := by
  rw [mulVec_mulVec, hc, ← mulVec_mulVec, ← map_mulVec_fun c P x, hPx]
  simp only [Pi.zero_apply, map_zero]
  exact mulVec_zero J₁

theorem orth_mul (hc : Iᵀ * Jd = J₁ * P.map c) (hPx : P *ᵥ x = 0) (q : Matrix (Fin d) (Fin d) R)
    (hq : qᵀ * Jd * q.map c = Jd) (hqx : q *ᵥ x = x) : (q * I)ᵀ *ᵥ (Jd *ᵥ fun i => c (x i)) = 0 := by
  rw [transpose_mul, ← mulVec_mulVec, transpose_mulVec_fix c Jd x q hq hqx, orth_of c Jd J₁ I P x hc hPx]

theorem decomp_mul
    (hD : vecMulVec x (Jd *ᵥ fun i => c (y i)) + I * P + vecMulVec y (Jd *ᵥ fun i => c (x i)) = 1)
    (M : Matrix (Fin d) (Fin d₁) R) (hM : Mᵀ *ᵥ (Jd *ᵥ fun i => c (x i)) = 0) :
    I * (P * M) = M - vecMulVec x ((Jd *ᵥ fun i => c (y i)) ᵥ* M) := by
  have hM' : (Jd *ᵥ fun i => c (x i)) ᵥ* M = 0 := by rw [← mulVec_transpose]; exact hM
  have h := congrArg (· * M) hD
  have hz : vecMulVec y (0 : Fin d₁ → R) = 0 := by ext; simp [vecMulVec]
  simp only [Matrix.add_mul, Matrix.one_mul, vecMulVec_mul, hM', hz, add_zero] at h
  rw [← Matrix.mul_assoc]
  exact eq_sub_of_add_eq' h

theorem restr_mul (hc : Iᵀ * Jd = J₁ * P.map c) (hPx : P *ᵥ x = 0)
    (hD : vecMulVec x (Jd *ᵥ fun i => c (y i)) + I * P + vecMulVec y (Jd *ᵥ fun i => c (x i)) = 1)
    (q q' : Matrix (Fin d) (Fin d) R) (hqx : q *ᵥ x = x) (hq' : q'ᵀ * Jd * q'.map c = Jd) (hqx' : q' *ᵥ x = x) :
    P * (q * I) * (P * (q' * I)) = P * (q * q' * I) := by
  have h := decomp_mul c Jd I P x y hD (q' * I) (orth_mul c Jd J₁ I P x hc hPx q' hq' hqx')
  calc P * (q * I) * (P * (q' * I)) = P * (q * (I * (P * (q' * I)))) := by simp only [Matrix.mul_assoc]
    _ = P * (q * q' * I) := by
      rw [h, Matrix.mul_sub, Matrix.mul_vecMulVec, hqx, Matrix.mul_sub, Matrix.mul_vecMulVec, hPx]
      simp [Matrix.mul_assoc]

theorem restr_unitary (hPI : P * I = 1) (hc : Iᵀ * Jd = J₁ * P.map c) (hd : Jd * I.map c = Pᵀ * J₁)
    (hPx : P *ᵥ x = 0)
    (hD : vecMulVec x (Jd *ᵥ fun i => c (y i)) + I * P + vecMulVec y (Jd *ᵥ fun i => c (x i)) = 1)
    (q : Matrix (Fin d) (Fin d) R) (hq : qᵀ * Jd * q.map c = Jd) (hqx : q *ᵥ x = x) :
    (P * (q * I))ᵀ * J₁ * (P * (q * I)).map c = J₁ := by
  set M := q * I with hMdef
  have hM := orth_mul c Jd J₁ I P x hc hPx q hq hqx
  rw [← hMdef] at hM
  have h := decomp_mul c Jd I P x y hD M hM
  set a := (Jd *ᵥ fun i => c (y i)) ᵥ* M
  have hvm : (vecMulVec x a).map c = vecMulVec (fun i => c (x i)) (fun j => c (a j)) := by
    ext i j; simp [vecMulVec]
  have hsub : (M - vecMulVec x a).map c = M.map c - (vecMulVec x a).map c := Matrix.map_sub _ (map_sub c) _ _
  have hgram : Iᵀ * Jd * I.map c = J₁ := by
    rw [hc, Matrix.mul_assoc, ← Matrix.map_mul, hPI, Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_one]
  have hMM : Mᵀ * Jd * M.map c = J₁ := by
    rw [hMdef, transpose_mul, Matrix.map_mul]
    have e : Iᵀ * qᵀ * Jd * (q.map c * I.map c) = Iᵀ * (qᵀ * Jd * q.map c) * I.map c := by
      simp only [Matrix.mul_assoc]
    rw [e, hq, hgram]
  clear_value M
  have hzero : Mᵀ * Jd * vecMulVec (fun i => c (x i)) (fun j => c (a j)) = 0 := by
    rw [Matrix.mul_vecMulVec, ← mulVec_mulVec, hM]; simp
  calc (P * M)ᵀ * J₁ * (P * M).map c = Mᵀ * (Jd * I.map c) * (P.map c * M.map c) := by
        rw [hd, transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
    _ = Mᵀ * Jd * (I * (P * M)).map c := by
        rw [Matrix.map_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
    _ = J₁ := by
        rw [h, hsub, hvm, Matrix.mul_sub, hMM, hzero, sub_zero]

theorem vecMulVec_mulVec_comm (w : Fin d → R) (v z : Fin d₁ → R) : vecMulVec w v *ᵥ z = (v ⬝ᵥ z) • w := by
  ext i
  simp only [mulVec, vecMulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end Alg

end GlobalTheory.ThK.StabDec

namespace GlobalTheory.ThK.LemF

open Matrix GlobalTheory.ThK.StabDec

theorem stab_eq_unip_mul_levi_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∀ p ∈ UAt σ X (evI F), mat p *ᵥ incV F H.x = incV F H.x →
    ∃ n ∈ unip σ X H, n ∈ UAt σ X (evI F) ∧ ∃ g₀ : UA σ X₁.J, g₀ ∈ UAt σ X₁ (evI F) ∧
      ∃ g' : UA σ X.J, IsLevi H 1 g₀ g' ∧ g' ∈ UAt σ X (evI F) ∧ p = n * g' := by
  intro F E _ _ _ _ _ σ B n₁ X X₁ H i₀ i₁ r s r₁ s₁ hB hX _ hA p hp hpx
  obtain ⟨π, hπι, hπx, hπy, hc, hd⟩ := GlobalTheory.LeviFrameH.frame_facts σ B X X₁ H hB.cm hX hA
  obtain ⟨π', -, hD'⟩ := GlobalTheory.LeviFrameH.frame_dual σ B X X₁ H hB.cm hX hA

  have hππ : π' = π := by
    have h := congrArg (π * ·) hD'
    simp only [Matrix.mul_add, Matrix.mul_vecMulVec, hπx, hπy, ← Matrix.mul_assoc, hπι, Matrix.one_mul,
      Matrix.mul_one] at h
    have hz : ∀ w : Fin (n₁ + 2) → E, vecMulVec (0 : Fin n₁ → E) w = 0 := fun w => by ext; simp [vecMulVec]
    rw [hz, hz, zero_add, add_zero] at h
    exact h
  rw [hππ] at hD'
  let c : AE F E →+* AE F E := (cA σ).toRingHom
  have hPI : incM F π * incM F H.ι = 1 := by
    simp only [incM]; rw [← Matrix.map_mul, hπι, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcM : (incM F H.ι)ᵀ * incM F X.J = incM F X₁.J * (incM F π).map c := by
    rw [show (incM F π).map c = (incM F π).map (cA σ) from rfl, GlobalTheory.LeviFrame.incM_map_cA]
    simp only [incM]; rw [← Matrix.transpose_map, ← Matrix.map_mul, hc, Matrix.map_mul]
  have hdM : incM F X.J * (incM F H.ι).map c = (incM F π)ᵀ * incM F X₁.J := by
    rw [show (incM F H.ι).map c = (incM F H.ι).map (cA σ) from rfl, GlobalTheory.LeviFrame.incM_map_cA]
    simp only [incM]; rw [← Matrix.transpose_map, ← Matrix.map_mul, hd, Matrix.map_mul]
  have h0 : incV F (0 : Fin n₁ → E) = 0 := funext fun _ => map_zero _
  have hPx : incM F π *ᵥ incV F H.x = 0 := by rw [GlobalTheory.LeviFrame.incM_mulVec_incV, hπx, h0]
  have hPy : incM F π *ᵥ incV F H.y = 0 := by rw [GlobalTheory.LeviFrame.incM_mulVec_incV, hπy, h0]
  have hDA : vecMulVec (incV F H.x) (incM F X.J *ᵥ fun i => c (incV F H.y i)) + incM F H.ι * incM F π +
      vecMulVec (incV F H.y) (incM F X.J *ᵥ fun i => c (incV F H.x i)) = 1 := by
    rw [← Matrix.map_one (inclR (F := F) (AF F)) (map_zero _) (map_one _), ← hD']
    ext i j
    simp [Matrix.vecMulVec, Matrix.mulVec, dotProduct, incM, incV, map_sum, map_mul, Matrix.add_apply,
      Matrix.mul_apply, c, GlobalTheory.LeviTorusH.cA_incl]

  have hpU : (mat p)ᵀ * incM F X.J * (mat p).map c = incM F X.J := p.2
  have hpiU : (mat p⁻¹)ᵀ * incM F X.J * (mat p⁻¹).map c = incM F X.J := (p⁻¹).2
  have hpinv : mat p⁻¹ * mat p = 1 := by
    have h := GlobalTheory.StabHaar.mat_mul_inv p⁻¹
    rwa [inv_inv] at h
  have hpix : mat p⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hpx]
    rw [mulVec_mulVec, hpinv, one_mulVec]

  obtain ⟨G, hG⟩ : ∃ G, G = incM F π * (mat p * incM F H.ι) := ⟨_, rfl⟩
  obtain ⟨Gi, hGi⟩ : ∃ G, G = incM F π * (mat p⁻¹ * incM F H.ι) := ⟨_, rfl⟩
  have hGGi : G * Gi = 1 := by
    rw [hG, hGi, restr_mul c (incM F X.J) (incM F X₁.J) (incM F H.ι) (incM F π) (incV F H.x) (incV F H.y) hcM hPx
      hDA (mat p) (mat p⁻¹) hpx hpiU hpix, GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mul, hPI]
  have hGiG : Gi * G = 1 := by
    rw [hG, hGi, restr_mul c (incM F X.J) (incM F X₁.J) (incM F H.ι) (incM F π) (incV F H.x) (incV F H.y) hcM hPx
      hDA (mat p⁻¹) (mat p) hpix hpU hpx, hpinv, Matrix.one_mul, hPI]
  have hGU : Gᵀ * incM F X₁.J * G.map c = incM F X₁.J := by
    rw [hG]
    exact restr_unitary c (incM F X.J) (incM F X₁.J) (incM F H.ι) (incM F π) (incV F H.x) (incV F H.y) hPI hcM hdM
      hPx hDA (mat p) hpU hpx
  let g₀ : UA σ X₁.J := ⟨⟨G, Gi, hGGi, hGiG⟩, hGU⟩
  have hg₀ : g₀ ∈ UAt σ X₁ (evI F) := by
    intro u hu
    show u • (G - 1) = 0
    have e : G - 1 = incM F π * ((mat p - 1) * incM F H.ι) := by
      rw [hG, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hPI]
    rw [e, ← Matrix.mul_smul, ← Matrix.smul_mul, hp u hu, Matrix.zero_mul, Matrix.mul_zero]

  let g' : UA σ X.J :=
    ⟨⟨1 + incM F H.ι * ((G - 1) * incM F π), 1 + incM F H.ι * ((Gi - 1) * incM F π),
      GlobalTheory.LeviFrame.levi_inv_alg _ _ _ _ hPI hGGi, GlobalTheory.LeviFrame.levi_inv_alg _ _ _ _ hPI hGiG⟩,
      GlobalTheory.LeviFrame.levi_unit_alg c (incM F X.J) (incM F X₁.J) (incM F H.ι) (incM F π) G hPI hcM hdM hGU⟩
  have hLevi : IsLevi H 1 g₀ g' := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 + incM F H.ι * ((G - 1) * incM F π)) *ᵥ incV F H.x = ((1 : (AE F E)ˣ) : AE F E) • incV F H.x
      rw [Units.val_one, one_smul, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hPx, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
    · show (1 + incM F H.ι * ((G - 1) * incM F π)) *ᵥ incV F H.y =
        cA σ (((1 : (AE F E)ˣ)⁻¹ : (AE F E)ˣ) : AE F E) • incV F H.y
      rw [inv_one, Units.val_one, map_one, one_smul, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hPy, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
    · show (1 + incM F H.ι * ((G - 1) * incM F π)) * incM F H.ι = incM F H.ι * G
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hPI, Matrix.mul_one, Matrix.mul_sub,
        Matrix.mul_one, add_sub_cancel]
  have hg' : g' ∈ UAt σ X (evI F) := by
    intro u hu
    show u • (1 + incM F H.ι * ((G - 1) * incM F π) - 1) = 0
    have h1 : u • (G - 1) = 0 := hg₀ u hu
    rw [add_sub_cancel_left, ← Matrix.mul_smul, ← Matrix.smul_mul, h1, Matrix.zero_mul, Matrix.mul_zero]

  have hgi : mat g'⁻¹ = 1 + incM F H.ι * ((Gi - 1) * incM F π) := rfl
  obtain ⟨a, ha⟩ : ∃ a : Fin n₁ → AE F E,
      a = (incM F X.J *ᵥ fun i => c (incV F H.y i)) ᵥ* (mat p * incM F H.ι) := ⟨_, rfl⟩
  have hpI : mat p * incM F H.ι = incM F H.ι * G + vecMulVec (incV F H.x) a := by
    have h := decomp_mul c (incM F X.J) (incM F H.ι) (incM F π) (incV F H.x) (incV F H.y) hDA (mat p * incM F H.ι)
      (orth_mul c (incM F X.J) (incM F X₁.J) (incM F H.ι) (incM F π) (incV F H.x) hcM hPx (mat p) hpU hpx)
    rw [hG, ha]
    exact sub_eq_iff_eq_add.mp h.symm
  have hnI : mat (p * g'⁻¹) * incM F H.ι = incM F H.ι + vecMulVec (incV F H.x) (a ᵥ* Gi) := by
    calc mat (p * g'⁻¹) * incM F H.ι = mat p * incM F H.ι * Gi := by
          rw [GlobalTheory.StabHaar.mat_mul, hgi, Matrix.mul_assoc, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
            Matrix.mul_assoc, hPI, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel, Matrix.mul_assoc]
      _ = _ := by
          rw [hpI, Matrix.add_mul, Matrix.mul_assoc, hGGi, Matrix.mul_one, vecMulVec_mul]
  have hn : p * g'⁻¹ ∈ unip σ X H := by
    refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
    · rw [GlobalTheory.StabHaar.mat_mul, hgi, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPx, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero, hpx]
    · refine ⟨(a ᵥ* Gi) ⬝ᵥ z, ?_⟩
      rw [Matrix.mulVec_mulVec, hnI, Matrix.add_mulVec, vecMulVec_mulVec_comm]
  have hnA : p * g'⁻¹ ∈ UAt σ X (evI F) :=
    (UAtSub σ X (evI F)).mul_mem hp ((UAtSub σ X (evI F)).inv_mem hg')
  exact ⟨p * g'⁻¹, hn, hnA, g₀, hg₀, g', hLevi, hg', (inv_mul_cancel_right p g').symm⟩

end GlobalTheory.ThK.LemF

end
