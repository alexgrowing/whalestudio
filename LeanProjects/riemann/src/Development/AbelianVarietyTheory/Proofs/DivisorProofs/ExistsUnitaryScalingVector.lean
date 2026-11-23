import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.PlaneLevi

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def levi (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (s : E) : Matrix (Fin n) (Fin n) E :=
  1 + (s - 1) • Matrix.vecMulVec x (J *ᵥ fun i => σ (y i)) + (s⁻¹ - 1) • Matrix.vecMulVec y (J *ᵥ fun i => σ (x i))

section Form

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

lemma form_add_left (u v w : Fin n → E) : form σ J (u + v) w = form σ J u w + form σ J v w := by
  simp [form, add_dotProduct]

lemma form_smul_left (c : E) (u w : Fin n → E) : form σ J (c • u) w = c * form σ J u w := by
  simp [form, smul_dotProduct]

lemma form_add_right (u v w : Fin n → E) : form σ J u (v + w) = form σ J u v + form σ J u w := by
  simp only [form, Pi.add_apply, map_add]
  rw [show (fun i => σ (v i) + σ (w i)) = (fun i => σ (v i)) + (fun i => σ (w i)) from rfl, Matrix.mulVec_add,
    dotProduct_add]

lemma form_smul_right (c : E) (u v : Fin n → E) : form σ J u (c • v) = σ c * form σ J u v := by
  simp only [form, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => σ c * σ (v i)) = σ c • (fun i => σ (v i)) from rfl, Matrix.mulVec_smul, dotProduct_smul,
    smul_eq_mul]

lemma form_swap (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin n → E) :
    σ (form σ J a b) = form σ J b a := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hJ j i]; ring

lemma vecMulVec_mulVec' (x w v : Fin n → E) : Matrix.vecMulVec x w *ᵥ v = (w ⬝ᵥ v) • x := by
  ext i
  simp [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

lemma smul_vecMulVec_mulVec (c : E) (x w v : Fin n → E) : (c • Matrix.vecMulVec x w) *ᵥ v = (c * (v ⬝ᵥ w)) • x := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, Pi.smul_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma levi_mulVec (x y : Fin n → E) (s : E) (v : Fin n → E) :
    levi σ J x y s *ᵥ v = v + ((s - 1) * form σ J v y) • x + ((s⁻¹ - 1) * form σ J v x) • y := by
  simp only [levi, Matrix.add_mulVec, Matrix.one_mulVec, smul_vecMulVec_mulVec, form]

lemma entry_eq_form (M : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (Mᵀ * J * M.map σ) i j = form σ J (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) := by
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simp only [form, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.col_apply]
  ring

variable (x y : Fin n → E)

structure Hyp : Prop where
  xx : form σ J x x = 0
  yy : form σ J y y = 0
  xy : form σ J x y = 1
  yx : form σ J y x = 1

variable {x y}

lemma levi_mulVec_of_hyp (h : Hyp (σ := σ) (J := J) x y) (s : E) : levi σ J x y s *ᵥ x = s • x := by
  rw [levi_mulVec, h.xy, h.xx]
  simp only [mul_one, mul_zero, zero_smul, add_zero]
  rw [sub_smul, one_smul]; abel

lemma levi_mulVec_y (h : Hyp (σ := σ) (J := J) x y) (s : E) : levi σ J x y s *ᵥ y = s⁻¹ • y := by
  rw [levi_mulVec, h.yy, h.yx]
  simp only [mul_one, mul_zero, zero_smul, add_zero]
  rw [sub_smul, one_smul]; abel

lemma levi_mul_levi (h : Hyp (σ := σ) (J := J) x y) {s : E} (hs : s ≠ 0) :
    levi σ J x y s * levi σ J x y s⁻¹ = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_one,
    LinearMap.id_apply, levi_mulVec, levi_mulVec]
  simp only [form_add_left, form_smul_left, h.xx, h.yy, h.xy, h.yx, inv_inv]
  have h1 : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  match_scalars <;> field_simp <;> ring

lemma levi_unitary (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (h : Hyp (σ := σ) (J := J) x y)
    {s : E} (hs : s ≠ 0) (hσs : σ s = s) : (levi σ J x y s)ᵀ * J * (levi σ J x y s).map σ = J := by
  ext i j
  rw [entry_eq_form]
  have hJ1 : J i j = form σ J (Pi.single i 1) (Pi.single j 1) := by
    have := entry_eq_form (σ := σ) (J := J) 1 i j
    rw [Matrix.one_mulVec, Matrix.one_mulVec, Matrix.transpose_one, Matrix.one_mul,
      Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.mul_one] at this
    exact this
  rw [hJ1]
  generalize (Pi.single i 1 : Fin n → E) = u
  generalize (Pi.single j 1 : Fin n → E) = v
  rw [levi_mulVec, levi_mulVec]
  simp only [form_add_left, form_smul_left, form_add_right, form_smul_right, h.xx, h.yy, h.xy, h.yx, map_mul, map_sub,
    map_one, map_inv₀, hσs, form_swap hσ hJ]
  have h1 : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  linear_combination (form σ J u x * form σ J y v + form σ J u y * form σ J x v) * h1

lemma levi_mul_of_orth {n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) (ho : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0)
    (s : E) : levi σ J x y s * ι = ι := by
  ext i j
  have := congrFun (levi_mulVec (σ := σ) (J := J) x y s (ι *ᵥ Pi.single j 1)) i
  rw [(ho _).1, (ho _).2, Matrix.mulVec_mulVec] at this
  simpa [Matrix.mulVec_single_one] using this

end Form

section Adelic

variable [NumberField F]

lemma cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

def toUA (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : GL (Fin n) E)
    (hg : (g : Matrix (Fin n) (Fin n) E)ᵀ * J * (g : Matrix (Fin n) (Fin n) E).map σ = J) : UA σ J :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) g, by
    show ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)))ᵀ * J.map (inclR (F := F) (AF F)) *
      ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F))).map (cA σ) = J.map (inclR (F := F) (AF F))
    rw [Matrix.map_map, show (cA σ ∘ inclR (F := F) (AF F)) = inclR (F := F) (AF F) ∘ σ from funext (cA_inclR σ),
      ← Matrix.map_map, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hg]⟩

lemma mat_toUA (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : GL (Fin n) E) hg :
    mat (toUA σ (J := J) g hg) = (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := rfl

end Adelic

variable [NumberField F] [NumberField E]

lemma invol_of_good {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) : ∀ e, σ (σ e) = e := by
  intro e
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  have h := hB.cm.2.2.2
  apply τ.injective
  rw [h, h, star_star]

theorem exists_levi_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n)
    (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s r₁ s₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ →
      (∀ e : E, σ (σ e) = e) →
      ∀ t : ℕ, t ≠ 0 → ∃ m : UA σ X.J, mat m *ᵥ incV F H.x = (t : AE F E) • incV F H.x ∧
        (t : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin n₁ → AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hH hX _ hσ t ht
  have hyp : Hyp (σ := σ) (J := X.J) H.x H.y :=
    ⟨hH.xx, hH.yy, hH.xy, by rw [← form_swap hσ hX.herm, hH.xy, map_one]⟩
  have hs : (t : E) ≠ 0 := Nat.cast_ne_zero.2 ht
  have hσs : σ (t : E) = t := map_natCast σ t
  have hinv : levi σ X.J H.x H.y (t : E)⁻¹ * levi σ X.J H.x H.y (t : E) = 1 := by
    have := levi_mul_levi hyp (inv_ne_zero hs); rwa [inv_inv] at this
  let g : GL (Fin n) E := ⟨levi σ X.J H.x H.y t, levi σ X.J H.x H.y (t : E)⁻¹, levi_mul_levi hyp hs, hinv⟩
  refine ⟨toUA σ g (levi_unitary hσ hX.herm hyp hs hσs), ?_, ?_, ?_⟩
  · rw [mat_toUA]
    ext i
    change ((levi σ X.J H.x H.y t).map (inclR (F := F) (AF F)) *ᵥ ((inclR (F := F) (AF F)) ∘ H.x)) i = _
    rw [← RingHom.map_mulVec, levi_mulVec_of_hyp hyp]
    simp [incV, map_natCast]
  · rw [mat_toUA]
    ext i
    change (t : AE F E) * ((levi σ X.J H.x H.y t).map (inclR (F := F) (AF F)) *ᵥ ((inclR (F := F) (AF F)) ∘ H.y)) i = _
    rw [← RingHom.map_mulVec, levi_mulVec_y hyp, ← map_natCast (inclR (F := F) (AF F)) t, ← map_mul]
    simp only [incV, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  · intro z
    rw [mat_toUA, Matrix.mulVec_mulVec]
    congr 1
    change (levi σ X.J H.x H.y t).map (inclR (F := F) (AF F)) * H.ι.map (inclR (F := F) (AF F)) =
      H.ι.map (inclR (F := F) (AF F))
    rw [← Matrix.map_mul, levi_mul_of_orth _ hH.orth]

end GlobalTheory.PlaneLevi
