import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKLineCusp

open GlobalTheory.ThKLiftCusp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def planeSpan {R : Type} [CommRing R] {d d₁ : ℕ} (x y : Fin d → R) (ι : Matrix (Fin d) (Fin d₁) R) :
    Submodule R (Fin d → R) where
  carrier := {v | ∃ (a b : R) (w : Fin d₁ → R), v = a • x + ι *ᵥ w + b • y}
  add_mem' := by
    rintro _ _ ⟨a, b, w, rfl⟩ ⟨a', b', w', rfl⟩
    exact ⟨a + a', b + b', w + w', by simp only [add_smul, Matrix.mulVec_add]; abel⟩
  zero_mem' := ⟨0, 0, 0, by simp⟩
  smul_mem' := by
    rintro c _ ⟨a, b, w, rfl⟩
    exact ⟨c * a, c * b, c • w, by simp only [smul_add, smul_smul, Matrix.mulVec_smul]⟩

theorem cA_inclR (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (AF F) a) = inclR (AF F) (σ a) := by
  simp [cA, inclR]

theorem formA_incV (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (v w : Fin d → E) :
    formA σ J (incV F v) (incV F w) = inclR (AF F) (form σ J v w) := by
  simp [formA, form, incV, incM, cA_inclR, dotProduct, Matrix.mulVec, map_sum, map_mul]

theorem formA_mat (σ : E →ₐ[F] E) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (u : UA σ J) (v w : Fin d → AE F E) :
    formA σ J (mat u *ᵥ v) (mat u *ᵥ w) = formA σ J v w := by
  have hu : (mat u)ᵀ * incM F J * (mat u).map (cA σ) = incM F J := u.2
  have hc : (fun i => cA σ ((mat u *ᵥ w) i)) = (mat u).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  unfold formA
  rw [hc]
  calc (mat u *ᵥ v) ⬝ᵥ (incM F J *ᵥ ((mat u).map (cA σ) *ᵥ fun i => cA σ (w i)))
      = v ⬝ᵥ ((mat u)ᵀ *ᵥ (incM F J *ᵥ ((mat u).map (cA σ) *ᵥ fun i => cA σ (w i)))) := by
        rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
    _ = v ⬝ᵥ (((mat u)ᵀ * incM F J * (mat u).map (cA σ)) *ᵥ fun i => cA σ (w i)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = _ := by rw [hu]

section Geo
variable {σ : E →ₐ[F] E} {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {r s : ℕ} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ}

theorem mem_planeSpan (hs : W.IsSkew σ B r s) (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (v : Fin d → E) :
    v ∈ planeSpan H'.x H'.y H'.ι := by
  have hL : Submodule.span E (W.L : Set (Fin d → E)) ≤ planeSpan H'.x H'.y H'.ι := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨a, b, w, -, -, -, h⟩ := hA.split z hz
    exact ⟨a, b, w, h⟩
  haveI := hs.lat
  exact hL ((Submodule.IsLattice.span_eq_top (A := E) (M := W.L)).symm ▸ Submodule.mem_top)

theorem x_ne_zero (hA : H'.IsAdapted σ B W W₁ i₀ i₁) : H'.x ≠ 0 := by
  intro h
  have := hA.xy
  rw [h] at this
  simp [form] at this

theorem form_y_x_ne_zero (hs : W.IsSkew σ B r s) (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    form σ W.J H'.y H'.x ≠ 0 := by
  intro h0
  have hall : ∀ v, form σ W.J v H'.x = 0 := by
    intro v
    obtain ⟨a, b, w, rfl⟩ := mem_planeSpan hs hA v
    have h1 := (hA.orth w).1
    have h2 := hA.xx
    simp only [form] at h0 h1 h2 ⊢
    rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, h1, h2, h0]
    simp
  have hJ : W.J *ᵥ (fun i => σ (H'.x i)) = 0 := by
    funext i
    have := hall (Pi.single i 1)
    simpa [form] using this
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hAeq⟩ := hs.sig w
  set e : E →+* ℂ := (B.emb w).1
  set M : Matrix (Fin d) (Fin d) ℂ := Complex.I • W.J.map e with hM
  have hv : M *ᵥ (fun i => e (σ (H'.x i))) = 0 := by
    have : W.J.map e *ᵥ (fun i => e (σ (H'.x i))) = fun i => e ((W.J *ᵥ fun i => σ (H'.x i)) i) := by
      funext i; simp [Matrix.mulVec, dotProduct, map_sum]
    rw [hM, Matrix.smul_mulVec, this, hJ]
    funext i; simp
  have hvne : (fun i => e (σ (H'.x i))) ≠ 0 := by
    intro h
    apply x_ne_zero hA
    funext i
    have := congrFun h i
    simpa using this
  have hker : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨_, by simpa [Matrix.mulVecLin_apply] using hv, hvne⟩
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker M.mulVecLin) :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hker)
  have hsum := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hlt : M.rank < d := by
    have hd : Module.finrank ℂ (Fin d → ℂ) = d := Module.finrank_fin_fun ℂ
    have hr : M.rank = Module.finrank ℂ (LinearMap.range M.mulVecLin) := rfl
    omega
  have hunit : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) := by
    refine IsUnit.of_mul_eq_one_right (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) ?_
    simp [Matrix.fromBlocks_multiply]
  have hfull := Matrix.rank_of_isUnit _ hunit
  rw [← hAeq] at hfull
  have hle : (Aᵀ * M * A.map star).rank ≤ M.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hfull
  omega

end Geo

section Adelic
variable {σ : E →ₐ[F] E} {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {r s : ℕ} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ}

theorem incV_add {n : ℕ} (v w : Fin n → E) : incV F (v + w) = incV F v + incV F w := by
  funext i; simp [incV]

theorem incV_smul {n : ℕ} (a : E) (v : Fin n → E) : incV F (a • v) = inclR (F := F) (AF F) a • incV F v := by
  funext i; simp [incV]

theorem incV_mulVec {n m : ℕ} (M : Matrix (Fin n) (Fin m) E) (w : Fin m → E) :
    incV F (M *ᵥ w) = incM F M *ᵥ incV F w := by
  funext i; simp [incV, incM, Matrix.mulVec, dotProduct, map_sum]

theorem formA_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    formA σ J (v + v') w = formA σ J v w + formA σ J v' w := by
  simp [formA, add_dotProduct]

theorem formA_sub_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    formA σ J (v - v') w = formA σ J v w - formA σ J v' w := by
  simp [formA, sub_dotProduct]

theorem formA_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (v w : Fin n → AE F E) :
    formA σ J (a • v) w = a * formA σ J v w := by
  simp [formA, smul_dotProduct]

theorem mem_planeSpan_A (hs : W.IsSkew σ B r s) (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (z : Fin d → AE F E) :
    z ∈ planeSpan (incV F H'.x) (incV F H'.y) (incM F H'.ι) := by
  have hsingle : ∀ i, incV F (Pi.single i (1 : E)) ∈ planeSpan (incV F H'.x) (incV F H'.y) (incM F H'.ι) := by
    intro i
    obtain ⟨a, b, w, h⟩ := mem_planeSpan hs hA (Pi.single i 1)
    refine ⟨inclR (AF F) a, inclR (AF F) b, incV F w, ?_⟩
    rw [h, incV_add, incV_add, incV_smul, incV_smul, incV_mulVec]
  have hz : z = ∑ i, z i • incV F (Pi.single i (1 : E)) := by
    funext j
    simp [Finset.sum_apply, incV, Pi.single_apply]
  rw [hz]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hsingle i)

theorem formA_iota (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (w : Fin d₁ → AE F E) :
    formA σ W.J (incM F H'.ι *ᵥ w) (incV F H'.x) = 0 := by
  have hk : ∀ k, formA σ W.J (incV F (H'.ι *ᵥ Pi.single k 1)) (incV F H'.x) = 0 := by
    intro k; rw [formA_incV, (hA.orth _).1, map_zero]
  set q := incM F W.J *ᵥ fun i => cA σ (incV F H'.x i) with hq
  have h0 : q ᵥ* incM F H'.ι = 0 := by
    funext k
    have := hk k
    simp only [formA, Matrix.mulVec_single_one, incV_mulVec] at this
    rw [← hq] at this
    simpa [Matrix.vecMul, dotProduct, incM, incV, Matrix.mulVec, Pi.single_apply, mul_comm] using this
  show (incM F H'.ι *ᵥ w) ⬝ᵥ q = 0
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, h0, zero_dotProduct]

end Adelic

section Main
variable {σ : E →ₐ[F] E} {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {r s : ℕ} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ}

theorem incM_col_mulVec (x : Fin d → E) (a : Fin 1 → AE F E) :
    incM F (Matrix.of fun i (_ : Fin 1) => x i) *ᵥ a = a 0 • incV F x := by
  funext i; simp [incM, incV, Matrix.mulVec, dotProduct, mul_comm]

theorem mat_mul_col_iff (u : UA σ W.J) (x : Fin d → E) :
    mat u * incM F (Matrix.of fun i (_ : Fin 1) => x i) = incM F (Matrix.of fun i (_ : Fin 1) => x i) ↔
      mat u *ᵥ incV F x = incV F x := by
  constructor
  · intro h; funext i
    have := congrFun (congrFun h i) 0
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, incM, incV] using this
  · intro h; ext i k; fin_cases k
    have := congrFun h i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, incM, incV] using this

theorem unip_eq (hs : W.IsSkew σ B r s) (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    unip σ W H' = unipSp σ W (Matrix.of fun i (_ : Fin 1) => H'.x i) := by
  unfold unip unipSp
  congr 1
  ext u
  simp only [Set.mem_setOf_eq, mat_mul_col_iff, incM_col_mulVec]
  have hxv : (fun k : Fin 1 => incV F fun i => (Matrix.of fun i (_ : Fin 1) => H'.x i) i k) = fun _ => incV F H'.x := rfl
  constructor
  · rintro ⟨hx, hι⟩
    refine ⟨hx, ?_, ?_⟩
    · intro z hz
      obtain ⟨a, b, w, rfl⟩ := mem_planeSpan_A hs hA z
      have h0 := hz 0
      change formA σ W.J _ (incV F H'.x) = 0 at h0
      rw [formA_add_left, formA_add_left, formA_smul_left, formA_smul_left, formA_iota hA, formA_incV,
        formA_incV, hA.xx, map_zero] at h0
      have hu : IsUnit (inclR (F := F) (AF F) (form σ W.J H'.y H'.x)) :=
        (isUnit_iff_ne_zero.mpr (form_y_x_ne_zero hs hA)).map _
      have hb : b = 0 := by
        have : b * inclR (F := F) (AF F) (form σ W.J H'.y H'.x) = 0 := by simpa using h0
        exact (hu.mul_left_eq_zero).mp this
      subst hb
      obtain ⟨c, hc⟩ := hι w
      refine ⟨fun _ => c, ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hc]
      simp only [zero_smul, add_zero, Matrix.mulVec_zero]
      abel
    · intro z k
      change formA σ W.J (mat u *ᵥ z - z) (incV F H'.x) = 0
      rw [formA_sub_left]
      nth_rewrite 1 [← hx]
      rw [formA_mat, sub_self]
  · rintro ⟨hx, h2, -⟩
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := h2 (incM F H'.ι *ᵥ z) (fun k => formA_iota hA z)
    exact ⟨a 0, ha⟩

end Main

end GlobalTheory.ThKLineCusp

namespace GlobalTheory.ThKLineCusp

theorem const_term_zero (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {d d₁ : ℕ} (W : Spc F E d) (r s : ℕ) (hs : W.IsSkew σ B r s) (W₁ : Spc F E d₁) (H' : Plane E d d₁)
    (i₀ i₁ : ℕ) (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (f : UA σ W.J → ℂ) (hf : GlobalTheory.ThKLiftCusp.IsCuspW W f) :
    IsCT H' f 0 := by
  have heq := unip_eq hs hA
  have hinj : Function.Injective (Matrix.of fun i (_ : Fin 1) => H'.x i).mulVec := by
    intro a b hab
    have hx := x_ne_zero hA
    have hab' : a 0 • H'.x = b 0 • H'.x := by
      funext i
      have := congrFun hab i
      simpa [Matrix.mulVec, dotProduct, mul_comm] using this
    have h0 : a 0 = b 0 := smul_left_injective E hx hab'
    funext j; fin_cases j; exact h0
  have hiso : ∀ k l, form σ W.J (fun i => (Matrix.of fun i (_ : Fin 1) => H'.x i) i k)
      (fun i => (Matrix.of fun i (_ : Fin 1) => H'.x i) i l) = 0 := fun _ _ => hA.xx
  unfold IsCT
  rw [heq]
  intro μ 𝓕 hμ h𝓕 h1 h
  rw [hf 1 _ le_rfl hinj hiso μ 𝓕 hμ h𝓕 h1 h]
  rfl

end GlobalTheory.ThKLineCusp
