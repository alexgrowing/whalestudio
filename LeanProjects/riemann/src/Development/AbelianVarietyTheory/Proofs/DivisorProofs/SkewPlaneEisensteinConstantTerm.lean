import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd

noncomputable section

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open Matrix

namespace GlobalTheory.ThK.FixIsoAct

section Ring

variable {A : Type} [CommRing A] (c : A →+* A)

def sq {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (p q : Fin n → A) : A := p ⬝ᵥ J *ᵥ fun i => c (q i)

theorem sq_mulVec {n m k : ℕ} (J : Matrix (Fin n) (Fin n) A) (M : Matrix (Fin n) (Fin m) A)
    (N : Matrix (Fin n) (Fin k) A) (p : Fin m → A) (q : Fin k → A) :
    sq c J (M *ᵥ p) (N *ᵥ q) = p ⬝ᵥ (Mᵀ * J * N.map c) *ᵥ fun i => c (q i) := by
  have e : (fun i => c ((N *ᵥ q) i)) = N.map c *ᵥ fun i => c (q i) := by
    funext i; exact RingHom.map_mulVec c N q i
  rw [sq, e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec p Mᵀ, Matrix.vecMul_transpose]

theorem sq_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (p p' q : Fin n → A) :
    sq c J (p + p') q = sq c J p q + sq c J p' q := by
  simp only [sq, add_dotProduct]

theorem sq_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (a : A) (p q : Fin n → A) :
    sq c J (a • p) q = a * sq c J p q := by
  simp only [sq, smul_dotProduct, smul_eq_mul]

theorem sq_add_right {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (p q q' : Fin n → A) :
    sq c J p (q + q') = sq c J p q + sq c J p q' := by
  have e : (fun i => c ((q + q') i)) = (fun i => c (q i)) + fun i => c (q' i) := by
    funext i; simp
  simp only [sq, e, Matrix.mulVec_add, dotProduct_add]

theorem sq_smul_right {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (a : A) (p q : Fin n → A) :
    sq c J p (a • q) = c a * sq c J p q := by
  have e : (fun i => c ((a • q) i)) = c a • fun i => c (q i) := by
    funext i; simp
  simp only [sq, e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem sq_single {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    ((Pi.single i 1 : Fin n → A) ⬝ᵥ J *ᵥ fun l => c ((Pi.single j 1 : Fin n → A) l)) = J i j := by
  have e : (fun l => c ((Pi.single j 1 : Fin n → A) l)) = Pi.single j 1 := by
    funext l; rw [Pi.single_apply]; split_ifs <;> simp
  rw [e]; simp

theorem exists_matrix {n m : ℕ} (J g : Matrix (Fin n) (Fin n) A) (J₁ : Matrix (Fin m) (Fin m) A)
    (ι : Matrix (Fin n) (Fin m) A) (x y : Fin n → A) (hg : gᵀ * J * g.map c = J) (hgx : g *ᵥ x = x)
    (hxx : sq c J x x = 0) (hyx : sq c J y x = -1) (hιx : ∀ z, sq c J (ι *ᵥ z) x = 0)
    (hxι : ∀ z, sq c J x (ι *ᵥ z) = 0) (hJ₁ : ιᵀ * J * ι.map c = J₁)
    (hdec : ∀ v : Fin n → A, ∃ (α β : A) (z : Fin m → A), v = α • x + β • y + ι *ᵥ z) :
    ∃ h : Matrix (Fin m) (Fin m) A, hᵀ * J₁ * h.map c = J₁ ∧
      ∀ z : Fin m → A, ∃ a : A, g *ᵥ (ι *ᵥ z) = a • x + ι *ᵥ (h *ᵥ z) := by
  have hinv : ∀ p q, sq c J (g *ᵥ p) (g *ᵥ q) = sq c J p q := fun p q => by rw [sq_mulVec, hg]; rfl
  have h1 : ∀ z : Fin m → A, ∃ (a : A) (t : Fin m → A), g *ᵥ (ι *ᵥ z) = a • x + ι *ᵥ t := fun z => by
    obtain ⟨α, β, t, e⟩ := hdec (g *ᵥ (ι *ᵥ z))
    have h0 := hinv (ι *ᵥ z) x
    rw [hgx, e, sq_add_left, sq_add_left, sq_smul_left, sq_smul_left, hxx, hyx, hιx, hιx] at h0
    have hβ : β = 0 := by linear_combination -h0
    exact ⟨α, t, by rw [e, hβ, zero_smul, add_zero]⟩
  choose α t ht using fun k : Fin m => h1 (Pi.single k 1)
  have key : ∀ z : Fin m → A, ∃ a : A, g *ᵥ (ι *ᵥ z) = a • x + ι *ᵥ ((Matrix.of t)ᵀ *ᵥ z) := fun z => by
    refine ⟨∑ k, z k * α k, ?_⟩
    have e : (Matrix.of t)ᵀ *ᵥ z = ∑ k, z k • t k := by
      funext i; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [e]
    conv_lhs => rw [show z = ∑ j, z j • (Pi.single j 1 : Fin m → A) from by
      funext i; simp [Finset.sum_apply, Pi.single_apply]]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, ht, smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul]
  refine ⟨(Matrix.of t)ᵀ, ?_, key⟩
  ext i j
  obtain ⟨a, ha⟩ := key (Pi.single i 1)
  obtain ⟨b, hb⟩ := key (Pi.single j 1)
  have h0 := hinv (ι *ᵥ Pi.single i 1) (ι *ᵥ Pi.single j 1)
  rw [ha, hb, sq_add_left, sq_add_right, sq_add_right, sq_smul_left, sq_smul_left, sq_smul_right, sq_smul_right,
    hxx, hxι, hιx, sq_mulVec, sq_mulVec, hJ₁, sq_single] at h0
  have h2 := sq_mulVec c J₁ (Matrix.of t)ᵀ (Matrix.of t)ᵀ (Pi.single i 1) (Pi.single j 1)
  rw [sq_single] at h2
  rw [← h2, ← h0, sq]
  ring

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sq_incV (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (p q : Fin n → E) :
    sq (cA σ : AE F E →+* AE F E) (incM F J) (incV F p) (incV F q) = inclR (F := F) (AF F) (form σ J p q) := by
  simp only [sq, form, incM, incV, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul, RingHom.coe_coe,
    GlobalTheory.UnipCocptForm.cA_inclR]

theorem mulVec_eq_sum {n m : ℕ} (ι : Matrix (Fin n) (Fin m) E) (z : Fin m → AE F E) :
    incM F ι *ᵥ z = ∑ k, z k • incV F (ι *ᵥ Pi.single k 1) := by
  funext i
  simp [incM, incV, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm, Pi.single_apply]

theorem exists_unitary_of_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ g : UA σ W.J, mat g *ᵥ incV F H.x = incV F H.x → ∃ h₁ : UA σ W₁.J, (∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat g *ᵥ (incM F H.ι *ᵥ z) = a • incV F H.x + incM F H.ι *ᵥ (mat h₁ *ᵥ z)) := by
  intro F E _ _ _ _ _ σ _ hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ _ g hgx
  have hd : W₁.J.det ≠ 0 := fun h0 => hN₁.2 (by
    have e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero])
  have hP : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, hι, hJ₁⟩
  have hsum : ∀ (J : Matrix (Fin n) (Fin n) (AE F E)) (f : Fin n₁ → Fin n → AE F E) (q : Fin n → AE F E),
      (∀ k, sq (cA σ : AE F E →+* AE F E) J (f k) q = 0) → sq (cA σ : AE F E →+* AE F E) J (∑ k, f k) q = 0 :=
    fun J f q h => by
      simp only [sq] at h ⊢
      rw [sum_dotProduct]; exact Finset.sum_eq_zero fun k _ => h k
  have hsum' : ∀ (J : Matrix (Fin n) (Fin n) (AE F E)) (f : Fin n₁ → Fin n → AE F E) (q : Fin n → AE F E),
      (∀ k, sq (cA σ : AE F E →+* AE F E) J q (f k) = 0) → sq (cA σ : AE F E →+* AE F E) J q (∑ k, f k) = 0 :=
    fun J f q h => by
      refine Finset.sum_induction f (fun v => sq (cA σ : AE F E →+* AE F E) J q v = 0) (fun a b ha hb => ?_) ?_
        fun k _ => h k
      · rw [sq_add_right, ha, hb, add_zero]
      · have := sq_smul_right (cA σ : AE F E →+* AE F E) J 0 q 0
        rwa [zero_smul, map_zero, zero_mul] at this
  obtain ⟨h, hh, hz⟩ := exists_matrix (cA σ : AE F E →+* AE F E) (incM F W.J) (mat g) (incM F W₁.J) (incM F H.ι)
    (incV F H.x) (incV F H.y) g.2 hgx (by rw [sq_incV, hxx, map_zero])
    (by rw [sq_incV, GlobalTheory.LeviPlaneSection.form_skew hσ hsk H.y H.x, hxy, map_one, map_neg, map_one])
    (fun z => by
      rw [mulVec_eq_sum]
      exact hsum _ _ _ fun k => by rw [sq_smul_left, sq_incV, (hι _).1, map_zero, mul_zero])
    (fun z => by
      rw [mulVec_eq_sum]
      exact hsum' _ _ _ fun k => by
        rw [sq_smul_right, sq_incV, GlobalTheory.LeviPlaneSection.form_skew hσ hsk H.x, (hι _).1, map_zero, neg_zero,
          map_zero, mul_zero])
    (by
      rw [← hJ₁]
      ext i j
      simp only [incM, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul, RingHom.coe_coe,
        GlobalTheory.UnipCocptForm.cA_inclR])
    (hP.decompA hσ hsk hd)
  have hu : IsUnit (incM F W₁.J).det := by
    have e : (incM F W₁.J).det = inclR (F := F) (AF F) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [e]; exact (Ne.isUnit hd).map _
  have hu' : IsUnit h := by
    rw [← hh, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hu
    exact (Matrix.isUnit_iff_isUnit_det h).2 (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu))
  obtain ⟨u, rfl⟩ := hu'
  exact ⟨⟨u, hh⟩, hz⟩

end GlobalTheory.ThK.FixIsoAct

end
