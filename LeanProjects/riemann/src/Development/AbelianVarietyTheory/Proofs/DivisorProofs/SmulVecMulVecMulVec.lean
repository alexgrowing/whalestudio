import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.RatLeviPlane

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def leviAB (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (a b : E) :
    Matrix (Fin n) (Fin n) E :=
  1 + (a - 1) • Matrix.vecMulVec x (J *ᵥ fun i => σ (y i)) + (b - 1) • Matrix.vecMulVec y (J *ᵥ fun i => σ (x i))

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

lemma smul_vecMulVec_mulVec (c : E) (x w v : Fin n → E) : (c • Matrix.vecMulVec x w) *ᵥ v = (c * (v ⬝ᵥ w)) • x := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, Pi.smul_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma leviAB_mulVec (x y : Fin n → E) (a b : E) (v : Fin n → E) :
    leviAB σ J x y a b *ᵥ v = v + ((a - 1) * form σ J v y) • x + ((b - 1) * form σ J v x) • y := by
  simp only [leviAB, Matrix.add_mulVec, Matrix.one_mulVec, smul_vecMulVec_mulVec, form]

lemma entry_eq_form (M : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (Mᵀ * J * M.map σ) i j = form σ J (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) := by
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simp only [form, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.col_apply]
  ring

variable {x y : Fin n → E}

lemma leviAB_mulVec_eq_smul (hxx : form σ J x x = 0) (hxy : form σ J x y = 1) (a b : E) :
    leviAB σ J x y a b *ᵥ x = a • x := by
  rw [leviAB_mulVec, hxy, hxx]
  simp only [mul_one, mul_zero, zero_smul, add_zero]
  rw [sub_smul, one_smul]; abel

lemma leviAB_mulVec_y (hyy : form σ J y y = 0) (hyx : form σ J y x = 1) (a b : E) :
    leviAB σ J x y a b *ᵥ y = b • y := by
  rw [leviAB_mulVec, hyy, hyx]
  simp only [mul_one, mul_zero, zero_smul, add_zero]
  rw [sub_smul, one_smul]; abel

lemma leviAB_mul (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (hyx : form σ J y x = 1) (a b a' b' : E) :
    leviAB σ J x y a b * leviAB σ J x y a' b' = leviAB σ J x y (a * a') (b * b') := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
    leviAB_mulVec, leviAB_mulVec, leviAB_mulVec]
  simp only [form_add_left, form_smul_left, hxx, hyy, hxy, hyx]
  match_scalars <;> ring

lemma leviAB_one (a : E) : leviAB σ J x y 1 1 = 1 := by
  simp [leviAB]

lemma leviAB_unitary (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (hxx : form σ J x x = 0)
    (hyy : form σ J y y = 0) (hxy : form σ J x y = 1) (hyx : form σ J y x = 1) {a b : E}
    (h1 : b * σ a = 1) (h2 : a * σ b = 1) :
    (leviAB σ J x y a b)ᵀ * J * (leviAB σ J x y a b).map σ = J := by
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
  rw [leviAB_mulVec, leviAB_mulVec]
  simp only [form_add_left, form_smul_left, form_add_right, form_smul_right, hxx, hyy, hxy, hyx, map_mul, map_sub,
    map_one, form_swap hσ hJ]
  linear_combination (form σ J u x * form σ J y v) * h1 + (form σ J u y * form σ J x v) * h2

lemma leviAB_mul_of_orth {n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E)
    (ho : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (a b : E) : leviAB σ J x y a b * ι = ι := by
  ext i j
  have := congrFun (leviAB_mulVec (σ := σ) (J := J) x y a b (ι *ᵥ Pi.single j 1)) i
  rw [(ho _).1, (ho _).2, Matrix.mulVec_mulVec] at this
  simpa [Matrix.mulVec_single_one] using this

end Form

end GlobalTheory.RatLeviPlane

namespace GlobalTheory.RatLeviPlane

lemma cA_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (e : E) :
    cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem exists_ratLevi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∀ ξ : Eˣ, ∃ m ∈ ratU σ X.J, IsLevi (W₁ := X₁) H (Units.map (inclR (F := F) (AF F)).toMonoidHom ξ) 1 m := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H r s i₀ i₁ hB hX hH ξ
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hyx : form σ X.J H.y H.x = 1 := by rw [← form_swap hσ hX.herm, hH.xy, map_one]
  set a : E := (ξ : E) with ha
  set b : E := σ ((ξ⁻¹ : Eˣ) : E) with hb
  have hξ : (ξ : E) * ((ξ⁻¹ : Eˣ) : E) = 1 := by simp
  have hξ' : ((ξ⁻¹ : Eˣ) : E) * (ξ : E) = 1 := by simp
  have h1 : b * σ a = 1 := by rw [hb, ha, ← map_mul, hξ', map_one]
  have h2 : a * σ b = 1 := by rw [hb, ha, hσ, hξ]
  have h1' : σ a * b = 1 := by rw [mul_comm]; exact h1
  set b' : E := σ (ξ : E) with hb'
  have hinv1 : leviAB σ X.J H.x H.y a b * leviAB σ X.J H.x H.y ((ξ⁻¹ : Eˣ) : E) b' = 1 := by
    rw [leviAB_mul hH.xx hH.yy hH.xy hyx, hξ, hb, hb', ← map_mul, hξ', map_one, leviAB_one (1 : E)]
  have hinv2 : leviAB σ X.J H.x H.y ((ξ⁻¹ : Eˣ) : E) b' * leviAB σ X.J H.x H.y a b = 1 := by
    rw [leviAB_mul hH.xx hH.yy hH.xy hyx, hξ', hb, hb', ← map_mul, hξ, map_one, leviAB_one (1 : E)]
  let g : GL (Fin n) E := ⟨leviAB σ X.J H.x H.y a b, leviAB σ X.J H.x H.y ((ξ⁻¹ : Eˣ) : E) b', hinv1, hinv2⟩
  have hg : (g : Matrix (Fin n) (Fin n) E)ᵀ * X.J * (g : Matrix (Fin n) (Fin n) E).map σ = X.J :=
    leviAB_unitary hσ hX.herm hH.xx hH.yy hH.xy hyx h1 h2
  let m : UA σ X.J := ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) g, by
    show ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)))ᵀ * X.J.map (inclR (F := F) (AF F)) *
      ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F))).map (cA σ) = X.J.map (inclR (F := F) (AF F))
    rw [Matrix.map_map, show (cA σ ∘ inclR (F := F) (AF F)) = inclR (F := F) (AF F) ∘ σ from funext (cA_inclR σ),
      ← Matrix.map_map, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hg]⟩
  have hmat : mat m = (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := rfl
  refine ⟨m, Subgroup.mem_subgroupOf.2 ⟨g, rfl⟩, ?_, ?_, ?_⟩
  · rw [hmat]
    ext i
    change ((leviAB σ X.J H.x H.y a b).map (inclR (F := F) (AF F)) *ᵥ ((inclR (F := F) (AF F)) ∘ H.x)) i = _
    rw [← RingHom.map_mulVec, leviAB_mulVec_eq_smul hH.xx hH.xy]
    simp [incV, ha]
  · rw [hmat]
    ext i
    change ((leviAB σ X.J H.x H.y a b).map (inclR (F := F) (AF F)) *ᵥ ((inclR (F := F) (AF F)) ∘ H.y)) i = _
    rw [← RingHom.map_mulVec, leviAB_mulVec_y hH.yy hyx]
    simp [incV, hb, cA_inclR]
  · rw [hmat]
    have h1m : mat (1 : UA σ X₁.J) = 1 := rfl
    rw [h1m, Matrix.mul_one]
    change (leviAB σ X.J H.x H.y a b).map (inclR (F := F) (AF F)) * H.ι.map (inclR (F := F) (AF F)) =
      H.ι.map (inclR (F := F) (AF F))
    rw [← Matrix.map_mul, leviAB_mul_of_orth _ hH.orth]

end GlobalTheory.RatLeviPlane
