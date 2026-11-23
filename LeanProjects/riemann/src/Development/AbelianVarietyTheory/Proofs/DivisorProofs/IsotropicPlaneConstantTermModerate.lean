import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanLevelSubgroupClosedMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnitaryApproximation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.DescB.GenKFin

section Local

open Matrix

variable {R : Type} [CommRing R] {n m : ℕ}

private theorem exists_ext (c : R →+* R) (hc : ∀ z, c (c z) = z) {J θ : Matrix (Fin n) (Fin n) R}
    {J₁ θ₁ k k' : Matrix (Fin m) (Fin m) R} {ι : Matrix (Fin n) (Fin m) R} (sk : J.map c = -Jᵀ)
    (gram : ιᵀ * J * ι.map c = J₁) (hdet : IsUnit J₁.det) (t1 : θ * θ = 1) (t2 : θᵀ * J * θ.map c = J)
    (s1 : θ₁ * θ₁ = 1) (s2 : θ₁ᵀ * J₁ * θ₁.map c = J₁) (tie : θ * ι = ι * θ₁) (hk : k * k' = 1)
    (hku : kᵀ * J₁ * k.map c = J₁) (hkc : Commute k θ₁) :
    ∃ κ κ' : Matrix (Fin n) (Fin n) R, κ * κ' = 1 ∧ κᵀ * J * κ.map c = J ∧ Commute κ θ ∧ κ * ι = ι * k ∧
      ∀ z : Fin n → R, (ιᵀ * J) *ᵥ (fun i => c (z i)) = 0 → κ *ᵥ z = z := by
  have mm : ∀ {k l : ℕ} (A : Matrix (Fin k) (Fin l) R), (A.map c).map c = A := fun A => by
    ext i j; exact hc _
  have sk₁ : J₁.map c = -J₁ᵀ := by
    rw [← gram, Matrix.map_mul, Matrix.map_mul, mm, sk, transpose_mul, transpose_mul, transpose_transpose]
    simp [Matrix.mul_assoc, Matrix.transpose_map]
  set P : Matrix (Fin m) (Fin n) R := J₁⁻¹ * (ιᵀ * J) with hP
  have h2 : ιᵀ * J = J₁ * P := by rw [hP, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  have q1 : P.map c * ι = 1 := by
    have : P * ι.map c = 1 := by rw [hP, Matrix.mul_assoc, gram, Matrix.nonsing_inv_mul _ hdet]
    rw [← mm ι, ← Matrix.map_mul, this]
    exact Matrix.map_one _ (map_zero c) (map_one c)
  have q2 : J * ι.map c = (P.map c)ᵀ * J₁ := by
    have := congrArg (fun A => (Matrix.map A c)ᵀ) h2
    simp only [Matrix.map_mul, sk, sk₁, transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul,
      Matrix.mul_neg, neg_inj] at this
    exact this
  have q3 : ιᵀ * J = J₁ * (P.map c).map c := by rw [mm, h2]
  have inv : ∀ {l : ℕ} {A T : Matrix (Fin l) (Fin l) R}, T * T = 1 → Tᵀ * A * T.map c = A → A * T.map c = Tᵀ * A := by
    intro l A T h1 h2
    have h3 : T.map c * T.map c = 1 := by
      rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero c) (map_one c)]
    calc A * T.map c = Tᵀ * A * T.map c * T.map c := by rw [h2]
      _ = Tᵀ * A := by rw [Matrix.mul_assoc, h3, Matrix.mul_one]
  have hPθ : P * θ.map c = θ₁.map c * P := by
    have e : J₁ * (P * θ.map c) = J₁ * (θ₁.map c * P) := by
      rw [← Matrix.mul_assoc, ← h2, Matrix.mul_assoc, inv t1 t2, ← Matrix.mul_assoc, ← transpose_mul, tie, transpose_mul,
        Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← inv s1 s2, Matrix.mul_assoc]
    have := congrArg (fun A => J₁⁻¹ * A) e
    simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hdet] using this
  have hπθ : P.map c * θ = θ₁ * P.map c := by
    have := congrArg (fun A => Matrix.map A c) hPθ
    simpa only [Matrix.map_mul, mm] using this
  refine ⟨1 + ι * (k - 1) * P.map c, 1 + ι * (k' - 1) * P.map c, ?_, ?_, ?_, ?_, fun z hz => ?_⟩
  · rw [GlobalTheory.LeviUnitary.ext_mul q1, hk]; simp
  · exact GlobalTheory.LeviUnitary.ext_unitary c q1 q2 q3 hku
  · have hk' : Commute (k - 1) θ₁ := hkc.sub_left (Commute.one_left _)
    show (1 + ι * (k - 1) * P.map c) * θ = θ * (1 + ι * (k - 1) * P.map c)
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hπθ, ← Matrix.mul_assoc,
      Matrix.mul_assoc ι, hk'.eq, ← Matrix.mul_assoc ι, ← tie]
    simp only [Matrix.mul_assoc]
  · rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one,
      add_sub_cancel]
  · have e2 : P *ᵥ (fun i => c (z i)) = 0 := by rw [hP, ← mulVec_mulVec, hz, mulVec_zero]
    have e3 : P.map c *ᵥ z = 0 := by
      funext j
      have := congrArg c (congrFun e2 j)
      simpa [mulVec, dotProduct, map_sum, map_mul, hc] using this
    rw [add_mulVec, one_mulVec, ← mulVec_mulVec, e3, mulVec_zero, add_zero]

private theorem exists_ext_line (c : R →+* R) (hc : ∀ z, c (c z) = z) {J θ : Matrix (Fin n) (Fin n) R}
    {J₁ θ₁ k k' : Matrix (Fin m) (Fin m) R} {ι : Matrix (Fin n) (Fin m) R} {x : Fin n → R} {a : Fin m → R}
    (sk : J.map c = -Jᵀ) (hxx : x ⬝ᵥ J *ᵥ (fun i => c (x i)) = 0) (hιx : (ιᵀ * J) *ᵥ (fun i => c (x i)) = 0)
    (gram : ιᵀ * J * ι.map c = J₁) (hdet : IsUnit J₁.det) (t1 : θ * θ = 1) (t2 : θᵀ * J * θ.map c = J)
    (s1 : θ₁ * θ₁ = 1) (s2 : θ₁ᵀ * J₁ * θ₁.map c = J₁)
    (tie : θ * (ι + vecMulVec x a) = (ι + vecMulVec x a) * θ₁) (hk : k * k' = 1)
    (hku : kᵀ * J₁ * k.map c = J₁) (hkc : Commute k θ₁) :
    ∃ κ κ' : Matrix (Fin n) (Fin n) R, κ * κ' = 1 ∧ κᵀ * J * κ.map c = J ∧ Commute κ θ ∧ κ *ᵥ x = x ∧
      ∃ b, κ * ι = ι * k + vecMulVec x b := by
  have h1 : ((ι + vecMulVec x a)ᵀ * J) *ᵥ (fun i => c (x i)) = 0 := by
    rw [transpose_add, Matrix.add_mul, add_mulVec, hιx, zero_add, transpose_vecMulVec, ← mulVec_mulVec,
      vecMulVec_mulVec, hxx]
    simp
  have h2 : (x ᵥ* J) ᵥ* ι.map c = 0 := by
    funext j
    have := congrArg c (congrFun hιx j)
    have skij : ∀ i l, c (J i l) = -J l i := fun i l => congrFun (congrFun sk i) l
    simp only [mulVec, dotProduct, Matrix.mul_apply, map_sum, map_mul, hc, skij, transpose_apply, Pi.zero_apply,
      map_zero, Finset.sum_mul] at this
    simp only [vecMul, dotProduct, map_apply, Pi.zero_apply, Finset.sum_mul]
    rw [← neg_eq_zero, ← this, Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have gram' : (ι + vecMulVec x a)ᵀ * J * (ι + vecMulVec x a).map c = J₁ := by
    have e : (vecMulVec x a).map c = vecMulVec (fun i => c (x i)) (fun i => c (a i)) := by
      ext i j; simp [vecMulVec_apply]
    rw [Matrix.map_add _ (map_add c), Matrix.mul_add, e, mul_vecMulVec, h1, zero_vecMulVec, add_zero, transpose_add,
      Matrix.add_mul, Matrix.add_mul, gram, transpose_vecMulVec, vecMulVec_mul, vecMulVec_mul, h2, vecMulVec_zero,
      add_zero]
  obtain ⟨κ, κ', k1, k2, k3, k4, k5⟩ := exists_ext c hc sk gram' hdet t1 t2 s1 s2 tie hk hku hkc
  have hx := k5 x h1
  refine ⟨κ, κ', k1, k2, k3, hx, a ᵥ* k - a, ?_⟩
  rw [Matrix.mul_add, mul_vecMulVec, hx, Matrix.add_mul, vecMulVec_mul] at k4
  rw [vecMulVec_sub, ← add_sub_assoc, ← k4, add_sub_cancel_right]

end Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem det_ne_zero {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : E →+* ℂ) {θ : Matrix (Fin n) (Fin n) ℂ}
    (h : IsCartan (Complex.I • J.map e) θ) : J.det ≠ 0 := by
  intro hd
  have h0 : (J.map e).det = 0 := by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hd, map_zero]
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hx : star z ≠ 0 := fun h' => hz0 (by simpa using congrArg star h')
  have := h.2.2 (star z) hx
  rw [star_star, Matrix.smul_mulVec, hz, smul_zero, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

private theorem isLevi_mul_one {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {γ h₁ : UA σ Y₁.J}
    {m m' : UA σ Y.J} (h : IsLevi (W₁ := Y₁) H 1 γ m) (h' : IsLevi (W₁ := Y₁) H 1 h₁ m') :
    IsLevi (W₁ := Y₁) H 1 (γ * h₁) (m * m') := by
  have e : mat (m * m') = mat m * mat m' := rfl
  have e1 : mat (γ * h₁) = mat γ * mat h₁ := rfl
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, h1', Matrix.mulVec_smul, h1, smul_smul, Units.val_one, one_mul]
  · rw [e, ← Matrix.mulVec_mulVec, h2', Matrix.mulVec_smul, h2, smul_smul, inv_one, Units.val_one, map_one, one_mul]
  · rw [e, e1, Matrix.mul_assoc, h3', ← Matrix.mul_assoc, h3, Matrix.mul_assoc]

private theorem levi_conj_mem {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {γ : UA σ Y₁.J}
    {m : UA σ Y.J} (hm : IsLevi (W₁ := Y₁) H 1 γ m) {u : UA σ Y.J} (hu : u ∈ unip σ Y H) :
    m * u * m⁻¹ ∈ unip σ Y H := by
  obtain ⟨hx, -, hι⟩ := hm
  rw [Units.val_one, one_smul] at hx
  set x := incV F H.x with hxdef
  set A := incM F H.ι with hAdef
  have hinv : mat m⁻¹ * mat m = 1 := Units.inv_mul m.1
  have hγ : mat γ * mat γ⁻¹ = 1 := Units.mul_inv γ.1
  have hxi : mat m⁻¹ *ᵥ x = x := by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hAi : mat m⁻¹ * A = A * mat γ⁻¹ := by
    calc mat m⁻¹ * A = mat m⁻¹ * (A * mat γ) * mat γ⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc A, hγ, Matrix.mul_one]
      _ = A * mat γ⁻¹ := by rw [← hι, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hle : unip σ Y H ≤ (unip σ Y H).comap (MulAut.conj m).toMonoidHom := by
    unfold unip
    rw [Subgroup.closure_le]
    rintro w ⟨hwx, hwz⟩
    refine Subgroup.subset_closure ?_
    have e : mat ((MulAut.conj m).toMonoidHom w) = mat m * mat w * mat m⁻¹ := rfl
    refine ⟨?_, fun z => ?_⟩
    · rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxi, hwx, hx]
    · obtain ⟨a, ha⟩ := hwz (mat γ⁻¹ *ᵥ z)
      refine ⟨a, ?_⟩
      have e1 : mat m⁻¹ *ᵥ (A *ᵥ z) = A *ᵥ (mat γ⁻¹ *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, hAi, Matrix.mulVec_mulVec]
      have e2 : mat m *ᵥ (A *ᵥ (mat γ⁻¹ *ᵥ z)) = A *ᵥ z := by
        rw [Matrix.mulVec_mulVec, hι, Matrix.mulVec_mulVec, Matrix.mul_assoc, hγ, Matrix.mul_one]
      rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, ha, Matrix.mulVec_add, e2, Matrix.mulVec_smul, hx]
  exact hle hu

private theorem inv_mem_kInf {n : ℕ} {Y : Spc F E n} (τ : ∀ w : InfinitePlace F, EmbOver E w) {k : UA σ Y.J}
    (hk : k ∈ KInf σ Y τ) : k⁻¹ ∈ KInf σ Y τ := by
  have hinv : mat k⁻¹ * mat k = 1 := Units.inv_mul k.1
  have hinv' : mat k * mat k⁻¹ = 1 := Units.mul_inv k.1
  refine ⟨fun u hu => ?_, fun w => ?_⟩
  · have e : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by
      rw [Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hk.1 u hu, Matrix.mul_zero, neg_zero]
  · have h1 : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
      rw [← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := by
      rw [← Matrix.map_mul, hinv', Matrix.map_one _ (map_zero _) (map_one _)]
    have h3 := (hk.2 w).eq
    show (mat k⁻¹).map (piInf (τ w)) * Y.θ w = Y.θ w * (mat k⁻¹).map (piInf (τ w))
    calc (mat k⁻¹).map (piInf (τ w)) * Y.θ w
        = (mat k⁻¹).map (piInf (τ w)) * (Y.θ w * (mat k).map (piInf (τ w))) * (mat k⁻¹).map (piInf (τ w)) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc (Y.θ w), h2, Matrix.mul_one]
      _ = Y.θ w * (mat k⁻¹).map (piInf (τ w)) := by
          rw [← h3, ← Matrix.mul_assoc, h1, Matrix.one_mul]

variable (σ) in

private def kInfGrp {n : ℕ} (Y : Spc F E n) (τ : ∀ w : InfinitePlace F, EmbOver E w) : Subgroup (UA σ Y.J) where
  carrier := KInf σ Y τ
  one_mem' := (GlobalTheory.kInf_one_mul_commute_finPt F E σ n Y τ).1
  mul_mem' := fun ha hb => (GlobalTheory.kInf_one_mul_commute_finPt F E σ n Y τ).2.1 _ ha _ hb
  inv_mem' := fun ha => inv_mem_kInf τ ha

private theorem exists_unip_mul_mem_kInf {B : Base F E} (hCM : IsCMExt F E σ) {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {P : Plane E n n₁} (hsk : ∀ i j, σ (Y.J j i) = -Y.J i j) (hx0 : P.x ≠ 0) (hxx : form σ Y.J P.x P.x = 0)
    (horth : ∀ u, form σ Y.J (P.ι *ᵥ u) P.x = 0) (hgram : P.ιᵀ * Y.J * P.ι.map σ = Y₁.J)
    (hcart : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) (hmaj : InducedMaj B P Y Y₁)
    {k₁ : UA σ Y₁.J} (hk₁ : k₁ ∈ KInf σ Y₁ B.emb) {m : UA σ Y.J} (hm : IsLevi (W₁ := Y₁) P 1 k₁ m) :
    ∃ u ∈ unip σ Y P, u * m ∈ KInf σ Y B.emb := by
  have hτσ : ∀ w (e : E), (B.emb w).1 (σ e) = starRingEnd ℂ ((B.emb w).1 e) := fun w e => hCM.2.2.2 (B.emb w).1 e
  have hinc : ∀ w {k l : ℕ} (A : Matrix (Fin k) (Fin l) E), (incM F A).map (piInf (B.emb w)) = A.map (B.emb w).1 :=
    fun w _ _ A => by ext i j; simp [incM, GlobalTheory.ThK.PlaneEv.AdaptedJ.piInf_inclR]
  have hv : ∀ w, (piInf (B.emb w)) ∘ incV F P.x = fun j => (B.emb w).1 (P.x j) := fun w => by
    funext j; simp [incV, GlobalTheory.ThK.PlaneEv.AdaptedJ.piInf_inclR]
  have hcan : ∀ {l : ℕ} {A T : Matrix (Fin l) (Fin l) ℂ}, Tᵀ * (Complex.I • A) * T.map star = Complex.I • A →
      Tᵀ * A * T.map (starRingEnd ℂ) = A := fun {l A T} h => by
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact smul_right_injective _ Complex.I_ne_zero h
  have hdet : Y₁.J.det ≠ 0 := det_ne_zero (B.emb (Classical.arbitrary (InfinitePlace F))).1 (hmaj.cartan _)
  have hloc : ∀ w : InfinitePlace F, ∃ κ κ' : Matrix (Fin n) (Fin n) ℂ, κ * κ' = 1 ∧
      κᵀ * Y.J.map (B.emb w).1 * κ.map (starRingEnd ℂ) = Y.J.map (B.emb w).1 ∧ Commute κ (Y.θ w) ∧
      κ *ᵥ (fun j => (B.emb w).1 (P.x j)) = (fun j => (B.emb w).1 (P.x j)) ∧
      ∃ b, κ * P.ι.map (B.emb w).1 = P.ι.map (B.emb w).1 * (mat k₁).map (piInf (B.emb w)) +
        Matrix.vecMulVec (fun j => (B.emb w).1 (P.x j)) b := by
    intro w
    obtain ⟨a, ha⟩ := hmaj.tie w
    refine exists_ext_line (J₁ := Y₁.J.map (B.emb w).1) (k' := (mat k₁⁻¹).map (piInf (B.emb w))) (starRingEnd ℂ)
      (fun z => Complex.conj_conj z) ?_ ?_ ?_ ?_ ?_ (hcart w).1 (hcan (hcart w).2.1) (hmaj.cartan w).1
      (hcan (hmaj.cartan w).2.1) ha ?_ ?_ (hk₁.2 w)
    · ext i j
      simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, ← hτσ, hsk, map_neg]
    · have := congrArg (B.emb w).1 hxx
      simpa [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hτσ] using this
    · funext j
      have := congrArg (B.emb w).1 (horth (Pi.single j 1))
      rw [form, Matrix.mulVec_single_one] at this
      rw [← Matrix.mulVec_mulVec]
      simpa [dotProduct, Matrix.mulVec, map_sum, map_mul, hτσ] using this
    · rw [← hgram, Matrix.map_mul, Matrix.map_mul]
      congr 1
      ext i j
      simp only [Matrix.map_apply, hτσ]
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero]
      exact (map_ne_zero _).2 hdet
    · have hinv : mat k₁ * mat k₁⁻¹ = 1 := Units.mul_inv k₁.1
      rw [← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _)]
    · have h2 : (mat k₁)ᵀ * incM F Y₁.J * (mat k₁).map (cA σ) = incM F Y₁.J := k₁.2
      have hmapc : ((mat k₁).map (cA σ)).map (piInf (B.emb w)) =
          ((mat k₁).map (piInf (B.emb w))).map (starRingEnd ℂ) := by
        ext i j; exact GlobalTheory.RealPlaceConj.piInf_cA_eq_star F E σ hCM w (B.emb w) _
      have := congrArg (fun A => A.map (piInf (B.emb w))) h2
      simp only [Matrix.map_mul, ← Matrix.transpose_map, hinc, hmapc] at this
      exact this
  choose κ κ' hκ1 hκ2 hκ3 hκ4 b hκ5 using hloc
  obtain ⟨K, hKat, hKmap⟩ := GlobalTheory.ArchGlueMat.exists_unitary_glue σ B.emb Y.J κ κ' hCM hκ1 hκ2
  set x := incV F P.x with hxdef
  set A := incM F P.ι with hAdef
  have hKx : mat K *ᵥ x = x := by
    funext i
    apply sub_eq_zero.1
    apply GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM B.emb
    · intro u hu
      have e : (mat K *ᵥ x) i - x i = ((mat K - 1) *ᵥ x) i := by simp [Matrix.sub_mulVec]
      rw [e, ← Pi.smul_apply, ← Matrix.smul_mulVec, hKat u hu, Matrix.zero_mulVec, Pi.zero_apply]
    · intro w
      rw [map_sub, RingHom.map_mulVec, hKmap, hv, hκ4]
      exact sub_eq_zero.2 (congrFun (hv w) i).symm
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hx0
  have hi₀' : P.x i₀ ≠ 0 := hi₀
  set D := mat K * A - A * mat k₁ with hD
  have hDat : At (evI F) D := by
    intro u hu
    have e : D = (mat K - 1) * A - A * (mat k₁ - 1) := by
      rw [hD, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
    rw [e, smul_sub, ← Matrix.smul_mul, hKat u hu, ← Matrix.mul_smul, hk₁.1 u hu, Matrix.zero_mul, Matrix.mul_zero, sub_self]
  have hDw : ∀ w i j, piInf (B.emb w) (D i j) = (B.emb w).1 (P.x i) * b w j := by
    intro w i j
    have : D.map (piInf (B.emb w)) = Matrix.vecMulVec (fun j => (B.emb w).1 (P.x j)) (b w) := by
      rw [hD, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, hKmap, hinc, hκ5, add_sub_cancel_left]
    exact congrFun (congrFun this i) j
  have hDx : D = Matrix.vecMulVec x fun j => inclR (F := F) (AF F) (P.x i₀)⁻¹ * D i₀ j := by
    ext i j
    apply sub_eq_zero.1
    apply GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM B.emb
    · intro u hu
      have h1 : ∀ i j, u • D i j = 0 := fun i j => congrFun (congrFun (hDat u hu) i) j
      rw [Matrix.vecMulVec_apply, smul_sub, h1, ← mul_smul_comm, ← mul_smul_comm, h1, mul_zero, mul_zero, sub_zero]
    · intro w
      have h0 : (B.emb w).1 (P.x i₀) ≠ 0 := (map_ne_zero _).2 hi₀'
      have h1 : piInf (B.emb w) (x i) = (B.emb w).1 (P.x i) := congrFun (hv w) i
      rw [Matrix.vecMulVec_apply, map_sub, map_mul, map_mul, hDw, hDw, h1, GlobalTheory.ThK.PlaneEv.AdaptedJ.piInf_inclR, map_inv₀,
        inv_mul_cancel_left₀ h0, sub_self]
  obtain ⟨hx, -, hι⟩ := hm
  rw [Units.val_one, one_smul, ← hxdef] at hx
  rw [← hAdef] at hι
  have hinv : mat m⁻¹ * mat m = 1 := Units.inv_mul m.1
  have hγ : mat k₁ * mat k₁⁻¹ = 1 := Units.mul_inv k₁.1
  have hxi : mat m⁻¹ *ᵥ x = x := by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hAi : mat m⁻¹ * A = A * mat k₁⁻¹ := by
    calc mat m⁻¹ * A = mat m⁻¹ * (A * mat k₁) * mat k₁⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc A, hγ, Matrix.mul_one]
      _ = A * mat k₁⁻¹ := by rw [← hι, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  refine ⟨K * m⁻¹, Subgroup.subset_closure ⟨?_, fun z => ?_⟩, ?_⟩
  · show (mat K * mat m⁻¹) *ᵥ x = x
    rw [← Matrix.mulVec_mulVec, hxi, hKx]
  · refine ⟨(fun j => inclR (F := F) (AF F) (P.x i₀)⁻¹ * D i₀ j) ⬝ᵥ (mat k₁⁻¹ *ᵥ z), ?_⟩
    show (mat K * mat m⁻¹) *ᵥ (A *ᵥ z) = A *ᵥ z + _ • x
    have e : mat K * A = A * mat k₁ + Matrix.vecMulVec x fun j => inclR (F := F) (AF F) (P.x i₀)⁻¹ * D i₀ j := by
      rw [← hDx, hD]; abel
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hAi, ← Matrix.mul_assoc, e, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, hγ, Matrix.mul_one, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  · rw [inv_mul_cancel_right]
    exact ⟨hKat, fun w => by rw [hKmap w]; exact hκ3 w⟩

end GlobalTheory.ThK.DescB.GenKFin

open GlobalTheory.ThK.DescB.GenKFin in

theorem _root_.GlobalTheory.T.isotropic_plane_constant_term_moderate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      IsIsoPlane σ B P Y Y₁ →
      ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ fa : UA σ Y.J → ℂ, (∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
        IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => fa ((toGAd hσ Y.J hc).symm x))) →
      ∀ h ∈ finK σ Y B.emb, (∀ h₁ : UA σ Y₁.J, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) P 1 h₁ m) →
      ∀ g : UA σ Y₁.J → ℂ, (∀ h₁ m, IsLevi (W₁ := Y₁) P 1 h₁ m → g h₁ = fa (m * h)) →
      ∀ K₁ : Subgroup (GAd σ (c • Y₁.J.map σ)), (∀ x ∈ K₁, (toGAd hσ Y₁.J hc).symm x ∈ KInf σ Y₁ B.emb) →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K₁ => fun x => (fun x => g ((toGAd hσ Y₁.J hc).symm x)) (x * k))) := by
  intro F E _ _ _ _ _ σ hσ B hB n n₁ Y Y₁ P hsk hI c hc hcσ fa hfa h hh hlev g hg K₁ hK₁
  obtain ⟨hn, hxx, hyy, hxy, horth, hgram, hcart, hmaj⟩ := hI
  obtain ⟨k₀, hk₀, g₀, hg₀, rfl⟩ := hh
  have hx0 : P.x ≠ 0 := by
    intro e
    rw [e] at hxy
    simp [form] at hxy
  set T := toGAd hσ Y.J hc with hT
  set T₁ := toGAd hσ Y₁.J hc with hT₁
  let K : Subgroup (GAd σ (c • Y.J.map σ)) := (kInfGrp σ Y B.emb).comap T.symm.toMonoidHom
  have hA := hfa K (fun x hx => hx)
  have hfin := kfin_iff.2 hA.kfin
  have hleft : ∀ u ∈ unip σ Y P, ∀ y, fa (u * y) = fa y := by
    intro u hu y
    have := hA.left (T u) ⟨u, hu, rfl⟩ (T y)
    simpa using this
  choose M hM using hlev
  let L : (GAd σ (c • Y.J.map σ) → ℂ) →ₗ[ℂ] (GAd σ (c • Y₁.J.map σ) → ℂ) :=
    LinearMap.funLeft ℂ ℂ fun x => T (M (T₁.symm x) * (k₀ * g₀))
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun y =>
    (fun x => fa (T.symm x)) (y * k))).map L) ?_
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨u, hu, hκ⟩ := exists_unip_mul_mem_kInf hB.cm hsk hx0 hxx (fun v => (horth v).1) hgram hcart hmaj
    (hK₁ k k.2) (hM (T₁.symm k))
  have hκ' : k₀⁻¹ * (u * M (T₁.symm k)) * k₀ ∈ kInfGrp σ Y B.emb :=
    mul_mem (mul_mem (inv_mem (show k₀ ∈ kInfGrp σ Y B.emb from hk₀)) hκ) hk₀
  have hcomm := (GlobalTheory.kInf_one_mul_commute_finPt F E σ n Y B.emb).2.2 g₀ hg₀ _ hκ'
  refine ⟨_, Submodule.subset_span ⟨⟨T (k₀⁻¹ * (u * M (T₁.symm k)) * k₀), ?_⟩, rfl⟩, ?_⟩
  · show T.symm (T _) ∈ kInfGrp σ Y B.emb
    rw [MulEquiv.symm_apply_apply]
    exact hκ'
  · funext x
    show fa (T.symm (T (M (T₁.symm x) * (k₀ * g₀)) * T (k₀⁻¹ * (u * M (T₁.symm k)) * k₀))) = g (T₁.symm (x * k))
    rw [← map_mul, MulEquiv.symm_apply_apply, map_mul T₁.symm, hg _ _ (isLevi_mul_one (hM _) (hM _)),
      ← hleft _ (levi_conj_mem (hM (T₁.symm x)) hu) (M (T₁.symm x) * M (T₁.symm k) * (k₀ * g₀)),
      mul_assoc (M (T₁.symm x)) (k₀ * g₀), mul_assoc k₀ g₀, hcomm]
    congr 1
    group

end
