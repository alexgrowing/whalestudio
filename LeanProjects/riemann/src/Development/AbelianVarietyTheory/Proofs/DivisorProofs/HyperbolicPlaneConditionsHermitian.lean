import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
noncomputable section

namespace GlobalTheory.UnipLineHyp

open GlobalTheory.UnipLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem span_E {n d₂ : ℕ} {J : Matrix (Fin n) (Fin n) E} {x y : Fin n → E} {ι : Matrix (Fin n) (Fin d₂) E}
    (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (hn : d₂ + 2 = n)
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (ho : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hι : Function.Injective ι.mulVec)
    (w : Fin n → E) : ∃ (a b : E) (v : Fin d₂ → E), w = a • x + ι *ᵥ v + b • y := by
  have hyx : form σ J y x = 1 := by rw [← GlobalTheory.PlaneLevi.form_swap hσ hJ, hxy, map_one]
  let T : (E × E) × (Fin d₂ → E) →ₗ[E] (Fin n → E) :=
    LinearMap.coprod (LinearMap.coprod (LinearMap.id.smulRight x) (LinearMap.id.smulRight y)) (Matrix.mulVecLin ι)
  have hT : ∀ p, T p = p.1.1 • x + p.1.2 • y + ι *ᵥ p.2 := fun p => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨a, b⟩, v⟩ h
    rw [hT] at h
    have e1 := congrArg (fun w => form σ J w x) h
    have e2 := congrArg (fun w => form σ J w y) h
    simp only [GlobalTheory.PlaneLevi.form_add_left, GlobalTheory.PlaneLevi.form_smul_left, hxx, hyy, hxy, hyx, (ho v).1, (ho v).2]
      at e1 e2
    simp only [form, zero_dotProduct] at e1 e2
    simp only [mul_zero, mul_one, zero_add, add_zero] at e1 e2
    subst e1; subst e2
    simp only [zero_smul, zero_add] at h
    have hv : v = 0 := hι (by rw [h, Matrix.mulVec_zero])
    simp [hv]
  have hdim : Module.finrank E ((E × E) × (Fin d₂ → E)) = Module.finrank E (Fin n → E) := by
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]; omega
  have hsurj : Function.Surjective T := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  obtain ⟨⟨⟨a, b⟩, v⟩, hp⟩ := hsurj w
  refine ⟨a, b, v, ?_⟩
  rw [← hp, hT]; dsimp only; abel

theorem span_A {n d₂ : ℕ} {J : Matrix (Fin n) (Fin n) E} {x y : Fin n → E} {ι : Matrix (Fin n) (Fin d₂) E}
    (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (hn : d₂ + 2 = n)
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (ho : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hι : Function.Injective ι.mulVec)
    (w : Fin n → AE F E) :
    ∃ (a b : AE F E) (z : Fin d₂ → AE F E), w = a • incV F x + incM F ι *ᵥ z + b • incV F y := by
  suffices h : w ∈ spanSet (incV F x) (incV F y) (incM F ι) from h
  rw [pi_eq_sum_univ w]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  obtain ⟨a, b, v, h⟩ := span_E hσ hJ hn hxx hyy hxy ho hι (fun j => if i = j then 1 else 0)
  refine ⟨inclR (AF F) a, inclR (AF F) b, incV F v, funext fun j => ?_⟩
  have hj := congrArg (inclR (F := F) (AF F)) (congrFun h j)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, RingHom.map_mulVec] at hj
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  convert hj using 1
  · split_ifs <;> simp
  · rfl

theorem mulVec_y {n d₂ : ℕ} {J : Matrix (Fin n) (Fin n) E} {x y : Fin n → E} {ι : Matrix (Fin n) (Fin d₂) E}
    (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (hn : d₂ + 2 = n)
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (ho : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hι : Function.Injective ι.mulVec)
    (u : UA σ J) (hux : mat u *ᵥ incV F x = incV F x) :
    ∃ (c : AE F E) (z₀ : Fin d₂ → AE F E), mat u *ᵥ incV F y = incV F y + c • incV F x + incM F ι *ᵥ z₀ := by
  have hyx : form σ J y x = 1 := by rw [← GlobalTheory.PlaneLevi.form_swap hσ hJ, hxy, map_one]
  set q := J *ᵥ fun i => σ (x i) with hq
  set g := incV F q
  have hunit : (mat u)ᵀ * incM F J * (mat u).map (cA σ) = incM F J := u.2
  have hg : g = incM F J *ᵥ fun i => cA σ (incV F x i) := by
    simp only [g, hq, ← incM_mulVec_incV]
    congr 1
  have hcx : (mat u).map (cA σ) *ᵥ (fun i => cA σ (incV F x i)) = fun i => cA σ (incV F x i) := by
    funext i
    have := ((cA σ).toRingHom.map_mulVec (mat u) (incV F x) i).symm
    rw [hux] at this
    exact this
  have hinv : ∀ w, (mat u *ᵥ w) ⬝ᵥ g = w ⬝ᵥ g := by
    intro w
    have hT : (mat u)ᵀ *ᵥ g = g := by
      rw [hg, ← hcx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hunit, hcx]
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  have gx : incV F x ⬝ᵥ g = 0 := by rw [incV_dot]; exact (congrArg _ hxx).trans (map_zero _)
  have gy : incV F y ⬝ᵥ g = 1 := by rw [incV_dot]; exact (congrArg _ hyx).trans (map_one _)
  have hιq : ιᵀ *ᵥ q = 0 := by
    funext j
    have := (ho (Pi.single j 1)).1
    simp only [form, Matrix.mulVec_single_one] at this
    rw [Matrix.mulVec_transpose, Pi.zero_apply, ← this, ← hq, dotProduct_comm]
    rfl
  have gi : ∀ z, (incM F ι *ᵥ z) ⬝ᵥ g = 0 := by
    intro z
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have : (incM F ι)ᵀ *ᵥ g = 0 := by
      rw [show (incM F ι)ᵀ = incM F ιᵀ from Matrix.transpose_map.symm, incM_mulVec_incV, hιq]
      funext i; simp [incV]
    rw [this, zero_dotProduct]
  obtain ⟨a, b, z, h⟩ := span_A hσ hJ hn hxx hyy hxy ho hι (mat u *ᵥ incV F y)
  have hb : b = 1 := by
    have e1 := hinv (incV F y)
    rw [h, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, gx, gi, gy, smul_zero, zero_add,
      smul_eq_mul, mul_one] at e1
    simpa using e1
  refine ⟨a, z, ?_⟩
  rw [h, hb, one_smul]
  abel

theorem conj_commutator_eq_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d₂ : ℕ) (X : Spc F E n)
    (H : Plane E n d₂), (∀ i j, σ (X.J j i) = X.J i j) → (∀ e : E, σ (σ e) = e) →
      (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
      ∀ u : UA σ X.J, mat u *ᵥ incV F H.x = incV F H.x →
      (∀ z : Fin d₂ → AE F E, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) →
      ∀ (m m' : UA σ X.J) (t : ℕ),
      mat m *ᵥ incV F H.x = (2 : AE F E) • incV F H.x → (2 : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y →
      (∀ z : Fin d₂ → AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) →
      mat m' *ᵥ incV F H.x = (t : AE F E) • incV F H.x → (t : AE F E) • (mat m' *ᵥ incV F H.y) = incV F H.y →
      (∀ z : Fin d₂ → AE F E, mat m' *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) →
      m' * (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) * m'⁻¹ = (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) ^ (t ^ 2) := by
  intro F E _ _ _ _ _ σ n d₂ X H hJ hσ ⟨hn, hxx, hyy, hxy, ho, hι⟩ u hux hui m m' t hmx hmy hmi hm'x hm'y hm'i
  obtain ⟨c, z₀, huy⟩ := mulVec_y hσ hJ hn hxx hyy hxy ho hι u hux
  exact conj_eq_pow (span_A hσ hJ hn hxx hyy hxy ho hι) u hux hui c z₀ huy m m' t hmx hmy hmi hm'x hm'y hm'i

end GlobalTheory.UnipLineHyp
