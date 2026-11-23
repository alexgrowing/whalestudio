import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicOrbitOrthogonalAtPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.IsoOrthLocB
open GlobalTheory.IsoOrthLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_herm {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x w : Fin n → E) : form σ J x w = σ (form σ J w x) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hJ, hσ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hTens_transpose (σ : E →ₐ[F] E) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) (AE F E))
    (JW : Matrix (Fin d) (Fin d) (AE F E)) (x y : Matrix (Fin n) (Fin d) (AE F E)) :
    hTens (cA σ) JX JW x y = hTens (cA σ) JW JX xᵀ yᵀ := by
  simp only [hTens, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem at_transpose {n d : ℕ} {v : Pl F} {m : Matrix (Fin n) (Fin d) (AE F E)} (hm : At (evFin F v) m) :
    At (evFin F v) mᵀ := by
  intro u hu
  rw [← Matrix.transpose_smul, hm u hu, Matrix.transpose_zero]

theorem at_mul_left {n d k : ℕ} {v : Pl F} {m : Matrix (Fin d) (Fin k) (AE F E)} (hm : At (evFin F v) m)
    (N : Matrix (Fin n) (Fin d) (AE F E)) : At (evFin F v) (N * m) := by
  intro u hu
  rw [← Matrix.mul_smul, hm u hu, Matrix.mul_zero]

theorem at_vecMulVec_right {n d : ℕ} {v : Pl F} {z : Fin d → AE F E} (hz : At (evFin F v) z) (x : Fin n → AE F E) :
    At (evFin F v) (Matrix.vecMulVec x z) := by
  rw [← Matrix.transpose_vecMulVec]
  exact at_transpose (at_vecMulVec hz x)

theorem at_mulVec_right {n d : ℕ} {v : Pl F} {y : Fin d → AE F E} (hy : At (evFin F v) y)
    (A : Matrix (Fin n) (Fin d) (AE F E)) : At (evFin F v) (A *ᵥ y) := by
  intro u hu
  rw [← Matrix.mulVec_smul, hy u hu, Matrix.mulVec_zero]

theorem at_cA {k : ℕ} {v : Pl F} (σ : E →ₐ[F] E) {β : Fin k → AE F E} (hβ : At (evFin F v) β) :
    At (evFin F v) (fun i => cA σ (β i)) := by
  intro u hu
  funext i
  have := congrFun (hβ u hu) i
  simp only [Pi.smul_apply, Pi.zero_apply] at this ⊢
  rw [← map_smul, this, map_zero]

theorem vanish_lin (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {k : ℕ} (v : Pl F) (β : Fin k → AE F E)
    (hβ : At (evFin F v) β)
    (h : ∀ yv : Fin k → AE F E, At (evFin F v) yv →
      evFin F v (Algebra.trace (AF F) (AE F E) (-1 * (yv ⬝ᵥ β))) = 0) : β = 0 := by
  have h1 : incM F (1 : Matrix (Fin k) (Fin k) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 := vanish_of_orth σ hσ (1 : Matrix (Fin k) (Fin k) E) (by simp) v (fun i => cA σ (β i)) (at_cA σ hβ)
    (fun yv hyv => by
      rw [← h yv hyv, h1]
      congr 3
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, cA_cA hσ, dotProduct])
  funext i
  rw [Pi.zero_apply, ← cA_cA hσ (β i)]
  have := congrFun h0 i
  simp only [Pi.zero_apply] at this
  rw [this, map_zero]

theorem eq_zero_of_plane {n n₁ : ℕ} (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E) (s t : Fin n → E)
    (U : Matrix (Fin n₁) (Fin n) E)
    (hE : ∀ j l, s j * x l + ∑ q, ι l q * U q j + t j * y l = if l = j then 1 else 0)
    (δ : Fin n → AE F E) (hx : incV F x ⬝ᵥ δ = 0) (hy : incV F y ⬝ᵥ δ = 0) (hι : (incM F ι)ᵀ *ᵥ δ = 0) :
    δ = 0 := by
  funext j
  have h1 : δ j = ∑ l, inclR (F := F) (AF F) (s j * x l + ∑ q, ι l q * U q j + t j * y l) * δ l := by
    simp only [hE, apply_ite (inclR (F := F) (AF F)), map_one, map_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 : ∑ l, inclR (F := F) (AF F) (s j * x l + ∑ q, ι l q * U q j + t j * y l) * δ l =
      inclR (F := F) (AF F) (s j) * (incV F x ⬝ᵥ δ) +
        ∑ q, inclR (F := F) (AF F) (U q j) * ((incM F ι)ᵀ *ᵥ δ) q +
        inclR (F := F) (AF F) (t j) * (incV F y ⬝ᵥ δ) := by
    simp only [map_add, map_mul, map_sum, add_mul, Finset.sum_add_distrib, dotProduct, Matrix.mulVec,
      Finset.mul_sum, Finset.sum_mul, incV, incM, Matrix.transpose_apply, Matrix.map_apply]
    congr 1
    · congr 1
      · exact Finset.sum_congr rfl fun l _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun l _ => by ring
    · exact Finset.sum_congr rfl fun l _ => by ring
  rw [h1, h2, hx, hy, hι]
  simp

theorem orth_col {σ : E →ₐ[F] E} {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (x : Fin n → E) (h : ∀ u, form σ J (ι *ᵥ u) x = 0) : ιᵀ *ᵥ (J *ᵥ fun k => σ (x k)) = 0 := by
  funext p
  have := h (Pi.single p 1)
  rw [Matrix.mulVec_single_one] at this
  simp only [form, dotProduct, Matrix.col_apply] at this
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply]
  exact this

theorem orth_row {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (ι : Matrix (Fin n) (Fin n₁) E)
    (x : Fin n → E) (h : ∀ u, form σ J (ι *ᵥ u) x = 0) : x ᵥ* (J * ι.map σ) = 0 := by
  funext q
  have h2 : form σ J x (ι *ᵥ Pi.single q 1) = 0 := by rw [form_herm hσ hJ, h, map_zero]
  rw [Matrix.mulVec_single_one] at h2
  simp only [form, dotProduct, Matrix.mulVec, Matrix.col_apply] at h2
  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.map_apply, Pi.zero_apply]
  rw [← h2]

theorem incM_mulVec_incV {n k : ℕ} (A : Matrix (Fin n) (Fin k) E) (u : Fin k → E) :
    incM F A *ᵥ incV F u = incV F (A *ᵥ u) := by
  funext i
  simp [incM, incV, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem incV_vecMul_incM {n k : ℕ} (A : Matrix (Fin n) (Fin k) E) (u : Fin n → E) :
    incV F u ᵥ* incM F A = incV F (u ᵥ* A) := by
  funext i
  simp [incM, incV, Matrix.vecMul, dotProduct, map_sum, map_mul]

theorem incV_zero {n : ℕ} : incV F (0 : Fin n → E) = 0 := by
  funext i
  simp [incV]

theorem cA_mulVec (σ : E →ₐ[F] E) {n k : ℕ} (A : Matrix (Fin n) (Fin k) E) (w : Fin k → AE F E) :
    (fun i => cA σ ((incM F A *ᵥ w) i)) = incM F (A.map σ) *ᵥ fun i => cA σ (w i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, incM, Matrix.map_apply]
  rfl

theorem sum_dot (σ : E →ₐ[F] E) {n : ℕ} (a : Fin n → AE F E) (A : Matrix (Fin n) (Fin n) (AE F E))
    (c : Fin n → AE F E) :
    ∑ i, ∑ k, a i * A i k * cA σ (c k) = a ⬝ᵥ (A *ᵥ fun k => cA σ (c k)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem dot_transpose {n k : ℕ} (A : Matrix (Fin n) (Fin k) (AE F E)) (y : Fin k → AE F E) (w : Fin n → AE F E) :
    (A *ᵥ y) ⬝ᵥ w = y ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem eq_zero_of_det (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : J.det ≠ 0) (b : Fin n → AE F E) (h : incM F J *ᵥ (fun k => cA σ (b k)) = 0) : b = 0 := by
  have hdet : IsUnit (incM F J).det := by
    rw [show incM F J = (inclR (F := F) (AF F)).mapMatrix J from rfl, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 hJ).map _
  have hcb0 : (fun k => cA σ (b k)) = 0 := by
    rw [← Matrix.one_mulVec (fun k => cA σ (b k)), ← Matrix.nonsing_inv_mul _ hdet, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_zero]
  funext k
  have := congrFun hcb0 k
  simp only [Pi.zero_apply] at this
  rw [Pi.zero_apply, ← cA_cA hσ (b k), this, map_zero]

theorem iota_vanish {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (s t : Fin n → E) (U : Matrix (Fin n₁) (Fin n) E)
    (hE : ∀ j l, s j * x l + ∑ q, ι l q * U q j + t j * y l = if l = j then 1 else 0)
    (hx : ∀ u, form σ J (ι *ᵥ u) x = 0) (hy : ∀ u, form σ J (ι *ᵥ u) y = 0)
    (a : AE F E) (β : Fin n₁ → AE F E) (c : Fin n → AE F E) (hc : c = a • incV F x + incM F ι *ᵥ β)
    (h : (incM F ι)ᵀ *ᵥ (incM F J *ᵥ fun k => cA σ (c k)) = 0) : incM F ι *ᵥ β = 0 := by
  have e1 : (fun k => cA σ (c k)) = cA σ a • incV F (fun k => σ (x k)) + fun k => cA σ ((incM F ι *ᵥ β) k) := by
    funext k
    rw [hc]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    rfl
  have eT : (incM F ι)ᵀ = incM F ιᵀ := rfl
  have e2 : (incM F ι)ᵀ *ᵥ (incM F J *ᵥ incV F (fun k => σ (x k))) = 0 := by
    rw [eT, incM_mulVec_incV, incM_mulVec_incV, orth_col J ι x hx, incV_zero]
  rw [e1, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, e2, smul_zero,
    zero_add] at h
  have e3 : ∀ z : Fin n → E, (∀ u, form σ J (ι *ᵥ u) z = 0) →
      incV F z ⬝ᵥ (incM F J *ᵥ fun k => cA σ ((incM F ι *ᵥ β) k)) = 0 := by
    intro z hz
    rw [cA_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, incV_vecMul_incM, incV_vecMul_incM,
      Matrix.vecMul_vecMul, orth_row hσ hJ ι z hz, incV_zero, zero_dotProduct]
  exact eq_zero_of_det σ hσ J hdet _ (eq_zero_of_plane x y ι s t U hE _ (e3 x hx) (e3 y hy) h)

theorem isoB_orth_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ d d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (W : Spc F E d) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (M : Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (v : Pl F) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)),
      (∀ u ∈ isoB (F := F) H H', At (evFin F v) u →
        (GlobalTheory.LatVac.locCo M.co v u).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u).2 = 0) →
      ∃ z₀ : Fin d → AE F E, At (evFin F v) (Matrix.vecMulVec (incV F H.x) z₀) ∧
      ∃ y₀ : Fin n₁ → AE F E, At (evFin F v) (Matrix.vecMulVec (incM F H.ι *ᵥ y₀) (incV F H'.x)) ∧
      ∃ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evFin F v) z ∧
        w = GlobalTheory.LatVac.locCo M.co v (Matrix.vecMulVec (incV F H.x) z₀) +
          GlobalTheory.LatVac.locCo M.co v (Matrix.vecMulVec (incM F H.ι *ᵥ y₀) (incV F H'.x)) +
          GlobalTheory.LatVac.locCo M.co v (incM F H.ι * z * (incM F H'.ι)ᵀ) := by
  intro F E _ _ _ _ _ σ B n n₁ d d₁ r s r' s' i₀ i₁ j₀ j₁ X X₁ W W₁ H H' M hB hX hW hH hH' v w hw
  have hσ := sigma_sigma hB.cm
  obtain ⟨m, hm, rfl⟩ := locCo_surj M.co v w
  have hspX := span_decomp H X.L hX.lat (fun z hz => by
    obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
    exact ⟨s, t, u, h⟩)
  choose sX tX uX hstuX using fun j : Fin n => hspX (Pi.single j 1)
  let UX : Matrix (Fin n₁) (Fin n) E := fun q j => uX j q
  have hEX : ∀ j l, sX j * H.x l + ∑ q, H.ι l q * UX q j + tX j * H.y l = if l = j then 1 else 0 := by
    intro j l
    have h := congrFun (hstuX j) l
    simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at h
    rw [h]
  have hxX : ∀ l, ∑ j, H.x j * X.J j l = σ (tX l) := by
    intro l
    rw [← form_single σ X.J H.x l, hstuX l, form_add_right, form_add_right, form_smul_right, form_smul_right, hH.xx,
      hH.xy, form_herm hσ hX.herm H.x (H.ι *ᵥ uX l), (hH.orth (uX l)).1]
    simp
  have hspW := span_decomp H' W.L hW.lat (fun z hz => by
    obtain ⟨s, t, u, -, -, -, h⟩ := hH'.split z hz
    exact ⟨s, t, u, h⟩)
  choose sW tW uW hstuW using fun j : Fin d => hspW (Pi.single j 1)
  let UW : Matrix (Fin d₁) (Fin d) E := fun q j => uW j q
  have hEW : ∀ j l, sW j * H'.x l + ∑ q, H'.ι l q * UW q j + tW j * H'.y l = if l = j then 1 else 0 := by
    intro j l
    have h := congrFun (hstuW j) l
    simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at h
    rw [h]
  have hxW : ∀ l, ∑ j, H'.x j * W.J j l = σ (tW l) := by
    intro l
    rw [← form_single σ W.J H'.x l, hstuW l, form_add_right, form_add_right, form_smul_right, form_smul_right, hH'.xx,
      hH'.xy, form_skew hσ hW.skew H'.x (H'.ι *ᵥ uW l), (hH'.orth (uW l)).1]
    simp
  have hJX : X.J.det ≠ 0 := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.IwLine.det_ne_zero_of_sig (hX.sig (InfinitePlace.mk φ))
    intro e
    apply h0
    rw [show X.J.map (B.emb (InfinitePlace.mk φ)).1 = RingHom.mapMatrix (B.emb (InfinitePlace.mk φ)).1 X.J from rfl,
      ← RingHom.map_det, e, map_zero]
  have hJW : W.J.det ≠ 0 := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.IwLine.det_ne_zero_of_sig (hW.sig (InfinitePlace.mk φ))
    intro e
    apply h0
    rw [Matrix.det_smul,
      show W.J.map (B.emb (InfinitePlace.mk φ)).1 = RingHom.mapMatrix (B.emb (InfinitePlace.mk φ)).1 W.J from rfl,
      ← RingHom.map_det, e, map_zero, mul_zero]

  have hb0 : mᵀ *ᵥ incV F tX = 0 := by
    refine vanish_of_orth σ hσ W.J hJW v _ (at_mulVec (at_transpose hm) _) fun yv hyv => ?_
    have h := hw (Matrix.vecMulVec (incV F H.x) yv) (Or.inl ⟨yv, rfl⟩) (at_vecMulVec_right hyv _)
    rw [locCo_form M.co v] at h
    rw [← h, symp, hTens_transpose, Matrix.transpose_vecMulVec, hTens_left σ W.J X.J H.x tX hxX yv mᵀ]
  have hmL : m = Matrix.vecMulVec (incV F H.x) (mᵀ *ᵥ incV F sX) + incM F H.ι * (incM F UX * m) := by
    have hdec := decomp (n := d) H.x H.y H.ι sX tX UX hEX mᵀ
    rw [hb0, Matrix.zero_vecMulVec, add_zero] at hdec
    conv_lhs => rw [← Matrix.transpose_transpose m, hdec]
    rw [Matrix.transpose_add, Matrix.transpose_vecMulVec, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.transpose_transpose]
  have hN : At (evFin F v) (incM F UX * m) := at_mul_left hm _
  have hcm : m *ᵥ incV F tW = ((mᵀ *ᵥ incV F sX) ⬝ᵥ incV F tW) • incV F H.x +
      incM F H.ι *ᵥ ((incM F UX * m) *ᵥ incV F tW) := by
    conv_lhs => rw [hmL]
    rw [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.mulVec_mulVec, op_smul_eq_smul]

  have hγ : (incM F H.ι)ᵀ *ᵥ (incM F X.J *ᵥ fun k => cA σ ((m *ᵥ incV F tW) k)) = 0 := by
    refine vanish_lin σ hσ v _ (at_mulVec_right (at_mulVec_right (at_cA σ (at_mulVec hm _)) _) _) fun y' hy' => ?_
    have h := hw (Matrix.vecMulVec (incM F H.ι *ᵥ y') (incV F H'.x)) (Or.inr ⟨y', rfl⟩)
      (at_vecMulVec (at_mulVec_right hy' _) _)
    rw [locCo_form M.co v] at h
    rw [← h, symp, hTens_left σ X.J W.J H'.x tW hxW _ m, sum_dot, dot_transpose]
  have hβ := iota_vanish hσ hX.herm hJX H.x H.y H.ι sX tX UX hEX (fun u => (hH.orth u).1) (fun u => (hH.orth u).2)
    _ _ _ hcm hγ
  have hdec := decomp (n := n) H'.x H'.y H'.ι sW tW UW hEW (incM F H.ι * (incM F UX * m))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec (incV F tW), hβ, Matrix.zero_vecMulVec, add_zero,
    Matrix.mul_assoc (incM F H.ι) (incM F UX * m)] at hdec
  refine ⟨mᵀ *ᵥ incV F sX, at_vecMulVec_right (at_mulVec (at_transpose hm) _) _,
    (incM F UX * m) *ᵥ incV F sW, at_vecMulVec (at_mulVec_right (at_mulVec hN _) _) _,
    incM F UX * m * (incM F UW)ᵀ, at_mul hN _, ?_⟩
  rw [← map_add, ← map_add, add_assoc, ← hdec, ← hmL]

end GlobalTheory.IsoOrthLocB
