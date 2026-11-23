import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinatesInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedBis
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IwUnitaryPart

open GlobalTheory.ThK.UnipDom GlobalTheory.ThK.UnipDom.Inverse

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem fA_sub_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → AE F E) :
    fA σ J v (w - w') = fA σ J v w - fA σ J v w' := by
  have h : (fun i => cA σ ((w - w') i)) = (fun i => cA σ (w i)) - (fun i => cA σ (w' i)) := by
    funext i; simp
  simp only [fA, h, Matrix.mulVec_sub, dotProduct_sub]

theorem fA_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (v w : Fin n → AE F E) :
    fA σ J v (a • w) = cA σ a * fA σ J v w := by
  have h : (fun i => cA σ ((a • w) i)) = cA σ a • (fun i => cA σ (w i)) := by
    funext i; simp
  simp only [fA, h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem entry_eq_fA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin n) (Fin n) (AE F E))
    (i j : Fin n) :
    (Mᵀ * incM F J * M.map (cA σ)) i j = fA σ J (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) := by
  have h : (fun k => cA σ ((M *ᵥ Pi.single j 1) k)) = M.map (cA σ) *ᵥ Pi.single j 1 := by
    funext k; simp [Matrix.mulVec_single_one]
  rw [fA, h, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, single_one_dotProduct, Matrix.mulVec_single_one]
  rfl

theorem fA_iota (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (hg : ιᵀ * J * ι.map σ = J₁) (v w : Fin n₁ → AE F E) :
    fA σ J₁ v w = fA σ J (incM F ι *ᵥ v) (incM F ι *ᵥ w) := by
  have hm : (incM F ι).map (cA σ) = incM F (ι.map σ) := by
    ext k l; simp [incM, cA_inclR]
  have hc : (fun i => cA σ ((incM F ι *ᵥ w) i)) = incM F (ι.map σ) *ᵥ (fun i => cA σ (w i)) := by
    funext i; rw [← hm]; exact RingHom.map_mulVec (cA σ).toRingHom (incM F ι) w i
  have hJ : (incM F ι)ᵀ * (incM F J * incM F (ι.map σ)) = incM F J₁ := by
    rw [← hg, ← Matrix.mul_assoc]; simp [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [fA, fA, hc, ← hJ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose]

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin n → E) : form σ J a b = σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem incM_mulVec_single {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) (i : Fin n₁) :
    incM F ι *ᵥ Pi.single i 1 = incV F (ι *ᵥ Pi.single i 1) := by
  funext k; simp [incM, incV, Matrix.mulVec_single_one]

end GlobalTheory.IwUnitaryPart

namespace GlobalTheory.IwUnitaryPart

open GlobalTheory.ThK.UnipDom GlobalTheory.ThK.UnipDom.Inverse

theorem unitary_part : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ p ∈ GlobalTheory.IwLine.lineStab σ X.J H.x, ∀ G G' : Matrix (Fin n₁) (Fin n₁) (AE F E), (∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat p *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (G *ᵥ z) + a • incV F H.x) → (∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat p⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (G' *ᵥ z) + a • incV F H.x) → ∃ g₀ : UA σ X₁.J, mat g₀ = G := by
  intro F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hH p hp G G' hG hG'
  obtain rfl := hH.rank
  have hs : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])

  have hL : Submodule.span E ((reS X Y).L : Set (Fin (n₁ + 2) → E)) = ⊤ := hX.lat.span_eq_top
  choose a b c hdec using fun j : Fin (n₁ + 2) =>
    GlobalTheory.IterBochner.exists_decomp B H (reS X Y) X₁ hH hL (Pi.single j 1)
  set P : Matrix (Fin (n₁ + 2)) (Fin n₁ ⊕ Fin 2) E := GlobalTheory.IwEmb.frame H.x H.y H.ι with hP
  set R : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) E :=
    Matrix.of fun k i => Sum.elim (fun t => c i t) (fun t => ![a i, b i] t) k with hR
  have hPR : P * R = 1 := by
    ext i i'
    have e := congrFun (hdec i') i
    rw [Matrix.one_apply]
    rw [Pi.single_apply] at e
    rw [e]
    simp only [hP, hR, GlobalTheory.IwEmb.frame, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, GlobalTheory.LeviElem.cols2, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    ring
  have hRP : R * P = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv.symm).1 hPR
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hPf : P.map f = GlobalTheory.IwEmb.frame (incV F H.x) (incV F H.y) (incM F H.ι) := by
    ext i (k | k)
    · rfl
    · fin_cases k <;> rfl
  have hQP' : R.map f * GlobalTheory.IwEmb.frame (incV F H.x) (incV F H.y) (incM F H.ι) = 1 := by
    rw [← hPf, ← Matrix.map_mul, hRP, Matrix.map_one _ (map_zero f) (map_one f)]
  obtain ⟨α, hα⟩ := hp
  have hpp : ∀ v, mat p *ᵥ (mat p⁻¹ *ᵥ v) = v := fun v => by
    have h := mat_inv_mulVec p⁻¹ v
    rwa [inv_inv] at h

  have hz : ∀ z, (G * G') *ᵥ z = z := by
    intro z
    obtain ⟨a', ha'⟩ := hG' z
    obtain ⟨a₁, ha₁⟩ := hG (G' *ᵥ z)
    have e : incM F H.ι *ᵥ z = incM F H.ι *ᵥ ((G * G') *ᵥ z) + (a₁ + a' * α.1) • incV F H.x := by
      calc incM F H.ι *ᵥ z = mat p *ᵥ (mat p⁻¹ *ᵥ (incM F H.ι *ᵥ z)) := (hpp _).symm
        _ = _ := by
          rw [ha', Matrix.mulVec_add, ha₁, Matrix.mulVec_smul, hα, ← Matrix.mulVec_mulVec, smul_smul, add_smul,
            add_assoc]
    have e2 := congrArg (fun v => R.map f *ᵥ v) e
    simp only [GlobalTheory.IwEmb.Q_line hQP', GlobalTheory.IwEmb.Q_ι hQP'] at e2
    funext i
    have h := congrFun e2 (Sum.inl i)
    simpa using h.symm
  have hGG : G * G' = 1 := by
    ext i j
    have h := congrFun (hz (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at h
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h

  have hgram : H.ιᵀ * X.J * H.ι.map σ = X₁.J := hH.gram
  have horth : ∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 := fun u => (hH.orth u).1
  have hxx0 : form σ X.J H.x H.x = 0 := hH.xx
  have hvx : ∀ i, fA σ X.J (incM F H.ι *ᵥ Pi.single i 1) (incV F H.x) = 0 := fun i => by
    rw [incM_mulVec_single, fA_incV, horth, map_zero]
  have hxv : ∀ i, fA σ X.J (incV F H.x) (incM F H.ι *ᵥ Pi.single i 1) = 0 := fun i => by
    rw [incM_mulVec_single, fA_incV, form_swap σ hs X.J hX.herm, horth, map_zero, map_zero]
  have hxx : fA σ X.J (incV F H.x) (incV F H.x) = 0 := by rw [fA_incV, hxx0, map_zero]
  have hx' : incV F H.x = ((α⁻¹ : (AE F E)ˣ) : AE F E) • (mat p *ᵥ incV F H.x) := by
    rw [hα, smul_smul, Units.inv_mul, one_smul]
  have hPx : ∀ i, fA σ X.J (mat p *ᵥ (incM F H.ι *ᵥ Pi.single i 1)) (incV F H.x) = 0 := fun i => by
    rw [hx', fA_smul_right, fA_mulVec, hvx, mul_zero]
  have hxP : ∀ i, fA σ X.J (incV F H.x) (mat p *ᵥ (incM F H.ι *ᵥ Pi.single i 1)) = 0 := fun i => by
    rw [hx', fA_smul_left, fA_mulVec, hxv, mul_zero]
  have hU : Gᵀ * incM F X₁.J * G.map (cA σ) = incM F X₁.J := by
    ext i j
    have e0 := entry_eq_fA σ X₁.J 1 i j
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.one_mulVec, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.mul_one] at e0
    rw [entry_eq_fA, e0, fA_iota σ X.J X₁.J H.ι hgram, fA_iota σ X.J X₁.J H.ι hgram]
    obtain ⟨ai, hai⟩ := hG (Pi.single i 1)
    obtain ⟨aj, haj⟩ := hG (Pi.single j 1)
    rw [eq_sub_of_add_eq hai.symm, eq_sub_of_add_eq haj.symm]
    simp only [fA_sub_left, fA_sub_right, fA_smul_left, fA_smul_right, fA_mulVec, hPx, hxP, hxx]
    ring
  exact ⟨⟨⟨G, G', hGG, (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hGG⟩, hU⟩, rfl⟩

end GlobalTheory.IwUnitaryPart
