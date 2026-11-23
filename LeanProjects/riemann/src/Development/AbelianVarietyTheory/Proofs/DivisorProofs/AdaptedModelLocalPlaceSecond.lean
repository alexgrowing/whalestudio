import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelG
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

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.IsoAOrthLoc
open GlobalTheory.IsoOrthLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem form_herm {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x w : Fin d → E) : form σ J x w = σ (form σ J w x) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hJ, hσ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private def fA (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (a b : Fin d → AE F E) : AE F E :=
  ∑ i, ∑ k, a i * incM F J i k * cA σ (b k)

private theorem fA_add_left (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (a a' b : Fin d → AE F E) :
    fA σ J (a + a') b = fA σ J a b + fA σ J a' b := by
  simp only [fA, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem fA_add_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (a b b' : Fin d → AE F E) :
    fA σ J a (b + b') = fA σ J a b + fA σ J a b' := by
  simp only [fA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private theorem fA_smul_left (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (c : AE F E)
    (a b : Fin d → AE F E) : fA σ J (c • a) b = c * fA σ J a b := by
  simp only [fA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem fA_smul_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (c : AE F E)
    (a b : Fin d → AE F E) : fA σ J a (c • b) = cA σ c * fA σ J a b := by
  simp only [fA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem fA_inc (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (a b : Fin d → E) :
    fA σ J (incV F a) (incV F b) = inclR (F := F) (AF F) (form σ J a b) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  simp only [fA, form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul,
    mul_assoc]

private theorem incM_mulVec {d d₁ : ℕ} (ι : Matrix (Fin d) (Fin d₁) E) (e : Fin d₁ → AE F E) :
    incM F ι *ᵥ e = ∑ p, e p • incV F (ι *ᵥ Pi.single p 1) := by
  funext i
  simp only [Matrix.mulVec_single_one, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, incV, incM, Matrix.mulVec,
    dotProduct, Matrix.map_apply, Matrix.col, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

private theorem fA_left_zero (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (ι : Matrix (Fin d) (Fin d₁) E)
    (x : Fin d → E) (h : ∀ u, form σ J (ι *ᵥ u) x = 0) (e : Fin d₁ → AE F E) :
    fA σ J (incM F ι *ᵥ e) (incV F x) = 0 := by
  rw [incM_mulVec]
  refine Finset.sum_induction _ (fun a => fA σ J a (incV F x) = 0) (fun a b ha hb => ?_) ?_ (fun p _ => ?_)
  · rw [fA_add_left, ha, hb, add_zero]
  · simp [fA]
  · rw [fA_smul_left, fA_inc, h, map_zero, mul_zero]

private theorem fA_right_zero (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (ι : Matrix (Fin d) (Fin d₁) E)
    (x : Fin d → E) (h : ∀ u, form σ J x (ι *ᵥ u) = 0) (e : Fin d₁ → AE F E) :
    fA σ J (incV F x) (incM F ι *ᵥ e) = 0 := by
  rw [incM_mulVec]
  refine Finset.sum_induction _ (fun a => fA σ J (incV F x) a = 0) (fun a b ha hb => ?_) ?_ (fun p _ => ?_)
  · rw [fA_add_right, ha, hb, add_zero]
  · simp [fA]
  · rw [fA_smul_right, fA_inc, h, map_zero, mul_zero]

private theorem hTens_swap {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (m m' : Matrix α β A) :
    hTens c JA JB m m' = hTens c JB JA mᵀ m'ᵀ := by
  simp only [hTens, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem decompV {d d₁ : ℕ} (x y : Fin d → E) (ι : Matrix (Fin d) (Fin d₁) E) (s t : Fin d → E)
    (U : Matrix (Fin d₁) (Fin d) E)
    (hE : ∀ j l, s j * x l + ∑ q, ι l q * U q j + t j * y l = if l = j then 1 else 0) (a : Fin d → AE F E) :
    a = (a ⬝ᵥ incV F s) • incV F x + incM F ι *ᵥ (incM F U *ᵥ a) + (a ⬝ᵥ incV F t) • incV F y := by
  have h := decomp (F := F) (n := 1) x y ι s t U hE (Matrix.of fun _ j => a j)
  funext l
  have h1 := congrFun (congrFun h 0) l
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply] at h1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  refine h1.trans ?_
  congr 2
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

private theorem decompL {n n₁ k : ℕ} (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E) (s t : Fin n → E)
    (U : Matrix (Fin n₁) (Fin n) E)
    (hE : ∀ j l, s j * x l + ∑ q, ι l q * U q j + t j * y l = if l = j then 1 else 0)
    (z : Matrix (Fin n) (Fin k) (AE F E)) :
    z = Matrix.vecMulVec (incV F x) (zᵀ *ᵥ incV F s) + incM F ι * (incM F U * z) +
      Matrix.vecMulVec (incV F y) (zᵀ *ᵥ incV F t) := by
  have h := congrArg Matrix.transpose (decomp (F := F) x y ι s t U hE zᵀ)
  rw [Matrix.transpose_transpose, Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_vecMulVec,
    Matrix.transpose_vecMulVec, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.transpose_transpose] at h
  exact h

private theorem at_transpose {n d : ℕ} {v : Pl F} {m : Matrix (Fin n) (Fin d) (AE F E)} (hm : At (evFin F v) m) :
    At (evFin F v) mᵀ := by
  intro u hu
  rw [← Matrix.transpose_smul, hm u hu, Matrix.transpose_zero]

private theorem at_mul_left {n d k : ℕ} {v : Pl F} {m : Matrix (Fin n) (Fin d) (AE F E)} (hm : At (evFin F v) m)
    (N : Matrix (Fin k) (Fin n) (AE F E)) : At (evFin F v) (N * m) := by
  intro u hu
  rw [← Matrix.mul_smul, hm u hu, Matrix.mul_zero]

private theorem at_mulVec_right {n d : ℕ} {v : Pl F} (m : Matrix (Fin n) (Fin d) (AE F E)) {e : Fin d → AE F E}
    (he : At (evFin F v) e) : At (evFin F v) (m *ᵥ e) := by
  intro u hu
  rw [← Matrix.mulVec_smul, he u hu, Matrix.mulVec_zero]

private theorem at_vecMulVec_right {n d : ℕ} {v : Pl F} (x : Fin n → AE F E) {e : Fin d → AE F E}
    (he : At (evFin F v) e) : At (evFin F v) (Matrix.vecMulVec x e) := by
  rw [← Matrix.transpose_vecMulVec]
  exact at_transpose (at_vecMulVec he x)

private theorem coords {σ : E →ₐ[F] E} {B : Base F E} {n n₁ i₀ i₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n}
    {Y₁ : Spc F E n₁} (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hL : Y.L.IsLattice E)
    (ho : ∀ u, form σ Y.J H.x (H.ι *ᵥ u) = 0) :
    ∃ (s t : Fin n → E) (U : Matrix (Fin n₁) (Fin n) E),
      (∀ j l, s j * H.x l + ∑ q, H.ι l q * U q j + t j * H.y l = if l = j then 1 else 0) ∧
      ∀ l, ∑ j, H.x j * Y.J j l = σ (t l) := by
  have hsp := span_decomp H Y.L hL (fun z hz => by
    obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
    exact ⟨s, t, u, h⟩)
  choose s t u hstu using fun j : Fin n => hsp (Pi.single j 1)
  refine ⟨s, t, fun q j => u j q, fun j l => ?_, fun l => ?_⟩
  · have h := congrFun (hstu j) l
    simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at h
    rw [h]
  · rw [← form_single σ Y.J H.x l, hstu l, form_add_right, form_add_right, form_smul_right, form_smul_right, hH.xx,
      hH.xy, ho]
    simp

private theorem det_skew_ne {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s) :
    W.J.det ≠ 0 := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have h0 := GlobalTheory.IwLine.det_ne_zero_of_sig (hW.sig (InfinitePlace.mk φ))
  intro e
  apply h0
  rw [Matrix.det_smul,
    show W.J.map (B.emb (InfinitePlace.mk φ)).1 = RingHom.mapMatrix (B.emb (InfinitePlace.mk φ)).1 W.J from rfl,
    ← RingHom.map_det, e, map_zero, mul_zero]

end GlobalTheory.IsoAOrthLoc
end

open GlobalTheory.IsoOrthLoc GlobalTheory.IsoAOrthLoc in
theorem _root_.GlobalTheory.T.adapted_model_local_place_second : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F,
    ∀ w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
      (∀ u ∈ isoA (F := F) H H', At (evFin F v) u →
        (GlobalTheory.LatVac.locCo M.co v u).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u).2 = 0) →
      ∃ u ∈ isoA (F := F) H H', At (evFin F v) u ∧ ∃ u' ∈ isoA (F := F) H H', At (evFin F v) u' ∧
        ∃ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evFin F v) z ∧
        w = GlobalTheory.LatVac.locCo M.co v u + GlobalTheory.LatVac.locCo M.co v u' +
          GlobalTheory.LatVac.locCo M.co v (incM F H.ι * z * (incM F H'.ι)ᵀ) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M hB hX hW hH hH' v w hw
  have hσ := sigma_sigma hB.cm
  obtain ⟨a, ⟨a₀, rfl⟩, ha, z, hz, rfl⟩ :=
    (isotropic_orbit_orthogonal_at_place F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M hB hX hW hH' v).2 w fun u hu => hw u (Or.inl hu)
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, Matrix.one_mul] at hw ⊢
  have hox : ∀ u, form σ W.J H'.x (H'.ι *ᵥ u) = 0 := fun u => by
    rw [form_skew hσ hW.skew, (hH'.orth u).1, map_zero, neg_zero]
  have hoy : ∀ u, form σ W.J H'.y (H'.ι *ᵥ u) = 0 := fun u => by
    rw [form_skew hσ hW.skew, (hH'.orth u).2, map_zero, neg_zero]
  obtain ⟨sx, tx, U, hE, hx⟩ := coords hH hX.lat fun u => by
    rw [form_herm hσ hX.herm, (hH.orth u).1, map_zero]
  obtain ⟨sw, tw, U', hE', -⟩ := coords hH' hW.lat hox
  have hq : incM F H'.ι *ᵥ (zᵀ *ᵥ incV F tx) = 0 := by
    refine vanish_of_orth σ hσ W.J (det_skew_ne hW) v _ (at_mulVec_right _ (at_mulVec (at_transpose hz) _))
      fun yv hyv => ?_
    have h := hw (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (incM F U' *ᵥ yv))) (Or.inr ⟨_, rfl⟩)
      (at_vecMulVec_right _ (at_mulVec_right _ (at_mulVec_right _ hyv)))
    rw [← map_add, locCo_form M.co v, symp, hTens_swap, Matrix.transpose_vecMulVec,
      hTens_left σ W.J X.J H.x tx hx] at h
    have e1 : (Matrix.vecMulVec a₀ (incV F H'.x) + z * (incM F H'.ι)ᵀ)ᵀ *ᵥ incV F tx =
        (a₀ ⬝ᵥ incV F tx) • incV F H'.x + incM F H'.ι *ᵥ (zᵀ *ᵥ incV F tx) := by
      rw [Matrix.transpose_add, Matrix.add_mulVec, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mulVec_mulVec, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mulVec]
      simp
    rw [e1] at h
    change evFin F v (Algebra.trace (AF F) (AE F E) (-1 * fA σ W.J _ _)) = 0 at h ⊢
    rw [fA_add_right, fA_smul_right, fA_left_zero σ W.J H'.ι H'.x (fun u => (hH'.orth u).1), mul_zero, zero_add] at h
    rw [decompV H'.x H'.y H'.ι sw tw U' hE' yv, fA_add_left, fA_add_left, fA_smul_left, fA_smul_left,
      fA_right_zero σ W.J H'.ι H'.x hox, fA_right_zero σ W.J H'.ι H'.y hoy, mul_zero, mul_zero, zero_add, add_zero]
    exact h
  refine ⟨_, Or.inl ⟨a₀, rfl⟩, ha, Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (zᵀ *ᵥ incV F sx)), Or.inr ⟨_, rfl⟩,
    at_vecMulVec_right _ (at_mulVec_right _ (at_mulVec (at_transpose hz) _)), incM F U * z, at_mul_left hz _, ?_⟩
  rw [add_assoc, ← map_add _ (Matrix.vecMulVec (incV F H.x) _)]
  congr 2
  conv_lhs => rw [decompL H.x H.y H.ι sx tx U hE z]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
    Matrix.vecMul_transpose, hq]
  have h0 : Matrix.vecMulVec (incV F H.y) (0 : Fin d → AE F E) = 0 := by
    ext i j
    simp only [Matrix.vecMulVec_apply, Pi.zero_apply, mul_zero, Matrix.zero_apply]
  rw [h0, add_zero]
