import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus GlobalTheory.UnipMass
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviModulus.HCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR' (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  simp [cA, inclR]

section Bilin
variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hA_add_l (v v' w : Fin n → AE F E) : hA σ J (v + v') w = hA σ J v w + hA σ J v' w := by
  simp [hA, add_dotProduct]

theorem hA_sub_l (v v' w : Fin n → AE F E) : hA σ J (v - v') w = hA σ J v w - hA σ J v' w := by
  simp [hA, sub_dotProduct]

theorem hA_smul_l (a : AE F E) (v w : Fin n → AE F E) : hA σ J (a • v) w = a * hA σ J v w := by
  simp [hA, smul_dotProduct]

theorem hA_neg_l (v w : Fin n → AE F E) : hA σ J (-v) w = -hA σ J v w := by
  simp [hA, neg_dotProduct]

theorem hA_add_r (v w w' : Fin n → AE F E) : hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  have : (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + (fun i => cA σ (w' i)) := by
    funext i; simp
  rw [hA, this, Matrix.mulVec_add, dotProduct_add]; rfl

theorem hA_sub_r (v w w' : Fin n → AE F E) : hA σ J v (w - w') = hA σ J v w - hA σ J v w' := by
  have : (fun i => cA σ ((w - w') i)) = (fun i => cA σ (w i)) - (fun i => cA σ (w' i)) := by
    funext i; simp
  rw [hA, this, Matrix.mulVec_sub, dotProduct_sub]; rfl

theorem hA_smul_r (a : AE F E) (v w : Fin n → AE F E) : hA σ J v (a • w) = cA σ a * hA σ J v w := by
  have : (fun i => cA σ ((a • w) i)) = cA σ a • (fun i => cA σ (w i)) := by
    funext i; simp
  rw [hA, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]; rfl

theorem hA_neg_r (v w : Fin n → AE F E) : hA σ J v (-w) = -hA σ J v w := by
  have : (fun i => cA σ ((-w) i)) = -(fun i => cA σ (w i)) := by
    funext i; simp
  rw [hA, this, Matrix.mulVec_neg, dotProduct_neg]; rfl

theorem hA_zero_r (v : Fin n → AE F E) : hA σ J v 0 = 0 := by
  simpa using hA_smul_r σ J 0 v 0

theorem hA_herm (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (v w : Fin n → AE F E) :
    hA σ J w v = cA σ (hA σ J v w) := by
  simp only [hA, dotProduct, Matrix.mulVec, incM, Matrix.map_apply, map_sum, map_mul, cA_cA σ hσ, cA_inclR',
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

end Bilin
end GlobalTheory.LeviModulus.HCoord

namespace GlobalTheory.LeviModulus.HCoord
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem hmat_mulVec (x u : Fin n → AE F E) (c : AE F E) (v : Fin n → AE F E) :
    hmat σ J x u c *ᵥ v = v + hA σ J v x • (u + c • x) - hA σ J v u • x := by
  ext i
  simp only [hmat, hA, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.add_apply,
    Matrix.vecMulVec_mulVec, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
  rw [dotProduct_comm v, dotProduct_comm v]
  ring

theorem hmat_ext {A B : Matrix (Fin n) (Fin n) (AE F E)} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa only [Matrix.toLin'_apply] using h v)

theorem hmat_mul (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x u u' : Fin n → AE F E)
    (c c' : AE F E) (hxx : hA σ J x x = 0) (hux : hA σ J u x = 0) (hu'x : hA σ J u' x = 0) :
    hmat σ J x u c * hmat σ J x u' c' = hmat σ J x (u + u') (c + c' - hA σ J u' u) := by
  have hxu : hA σ J x u = 0 := by rw [hA_herm σ J hσ hJ u x, hux, map_zero]
  refine hmat_ext fun v => ?_
  rw [← Matrix.mulVec_mulVec, hmat_mulVec, hmat_mulVec, hmat_mulVec]
  simp only [hA_add_l, hA_sub_l, hA_smul_l, hA_add_r, hA_smul_r, hxx, hux, hu'x, hxu]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem hmat_zero (x : Fin n → AE F E) : hmat σ J x 0 0 = 1 := by
  refine hmat_ext fun v => ?_
  rw [hmat_mulVec, hA_zero_r]; simp

theorem hA_hmat (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x u : Fin n → AE F E) (c : AE F E)
    (hxx : hA σ J x x = 0) (hux : hA σ J u x = 0) (hc : c + cA σ c = -hA σ J u u) (v w : Fin n → AE F E) :
    hA σ J (hmat σ J x u c *ᵥ v) (hmat σ J x u c *ᵥ w) = hA σ J v w := by
  have hxu : hA σ J x u = 0 := by rw [hA_herm σ J hσ hJ u x, hux, map_zero]
  have hxw : hA σ J x w = cA σ (hA σ J w x) := hA_herm σ J hσ hJ w x
  have huw : hA σ J u w = cA σ (hA σ J w u) := hA_herm σ J hσ hJ w u
  rw [hmat_mulVec, hmat_mulVec]
  simp only [hA_sub_l, hA_sub_r, hA_smul_l, hA_smul_r, hA_add_l, hA_add_r, hxx, hux, hxu, hxw, huw]
  linear_combination (hA σ J v x * cA σ (hA σ J w x)) * hc

theorem entry_eq (T : Matrix (Fin n) (Fin n) (AE F E)) (i j : Fin n) :
    (Tᵀ * incM F J * T.map (cA σ)) i j = hA σ J (T *ᵥ Pi.single i 1) (T *ᵥ Pi.single j 1) := by
  have hs : ∀ m : Fin n, T *ᵥ Pi.single m 1 = fun k => T k m := fun m => by
    funext k; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hs, hs]
  simp only [hA, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem entry_J (i j : Fin n) :
    incM F J i j = hA σ J (Pi.single i 1) (Pi.single j 1) := by
  have hb : (fun l => cA σ ((Pi.single j 1 : Fin n → AE F E) l)) = Pi.single j 1 := by
    funext l; by_cases h : l = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [hA, hb, single_one_dotProduct, Matrix.mulVec_single_one]
  simp

theorem hmat_unitary (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x u : Fin n → AE F E) (c : AE F E)
    (hxx : hA σ J x x = 0) (hux : hA σ J u x = 0) (hc : c + cA σ c = -hA σ J u u) :
    (hmat σ J x u c)ᵀ * incM F J * (hmat σ J x u c).map (cA σ) = incM F J := by
  ext i j
  rw [entry_eq, hA_hmat hσ hJ x u c hxx hux hc, ← entry_J]

theorem hA_mat (g : UA σ J) (v w : Fin n → AE F E) :
    hA σ J (mat g *ᵥ v) (mat g *ᵥ w) = hA σ J v w := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have hc : (fun i => cA σ ((mat g *ᵥ w) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (mat g) w i
  rw [hA, hA, hc, ← Matrix.vecMul_transpose (mat g) v, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, hg]

end GlobalTheory.LeviModulus.HCoord

namespace GlobalTheory.LeviModulus.HCoord
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_mulVec_incV' {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F A *ᵥ incV F v = incV F (A *ᵥ v) := by
  ext i; simp [incM, incV, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem cA_incV' (σ : E →ₐ[F] E) {n : ℕ} (x : Fin n → E) :
    (fun i => cA σ (incV F x i)) = incV F (fun i => σ (x i)) := by
  funext i; simp [incV, cA_inclR']

theorem hA_incV' (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    hA σ J (incV F a) (incV F b) = inclR (F := F) (AF F) (form σ J a b) := by
  rw [hA, cA_incV', incM_mulVec_incV']
  simp [form, incV, dotProduct, map_sum, map_mul]

theorem hA_ι_incV (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (ι : Matrix (Fin d) (Fin d₁) E)
    (w : Fin d → E) (h : ∀ u, form σ J (ι *ᵥ u) w = 0) (z : Fin d₁ → AE F E) :
    hA σ J (incM F ι *ᵥ z) (incV F w) = 0 := by
  have hq : ιᵀ *ᵥ (J *ᵥ fun i => σ (w i)) = 0 := by
    funext k
    have := h (Pi.single k 1)
    rw [form, Matrix.mulVec_single_one] at this
    exact this
  rw [hA, cA_incV', incM_mulVec_incV', ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    show (incM F ι)ᵀ = incM F ιᵀ from rfl, incM_mulVec_incV', hq]
  have : incV F (0 : Fin d₁ → E) = 0 := by funext i; simp [incV]
  rw [this, dotProduct_zero]

theorem incV_add' {n : ℕ} (a b : Fin n → E) : incV F (a + b) = incV F a + incV F b := by
  funext i; simp [incV]

theorem incV_smul' {n : ℕ} (s : E) (a : Fin n → E) : incV F (s • a) = inclR (F := F) (AF F) s • incV F a := by
  funext i; simp [incV]

theorem decomp {d d₁ : ℕ} (x y : Fin d → E) (ι : Matrix (Fin d) (Fin d₁) E)
    (hdec : ∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • x + ι *ᵥ u + t • y) (v : Fin d → AE F E) :
    ∃ (s t : AE F E) (z : Fin d₁ → AE F E), v = s • incV F x + incM F ι *ᵥ z + t • incV F y := by
  choose s t u hu using fun i => hdec (Pi.single i 1)
  have he : ∀ i, incV F (Pi.single i (1 : E)) =
      inclR (F := F) (AF F) (s i) • incV F x + incM F ι *ᵥ incV F (u i) + inclR (F := F) (AF F) (t i) • incV F y := by
    intro i
    rw [hu i, incV_add', incV_add', incV_smul', incV_smul', incM_mulVec_incV']
  have hv : v = ∑ i, v i • incV F (Pi.single i (1 : E)) := by
    funext k; simp [incV, Finset.sum_apply, Pi.single_apply]
  refine ⟨∑ i, v i * inclR (F := F) (AF F) (s i), ∑ i, v i * inclR (F := F) (AF F) (t i), ∑ i, v i • incV F (u i), ?_⟩
  calc v = ∑ i, v i • incV F (Pi.single i (1 : E)) := hv
    _ = _ := by
      simp only [he, smul_add, smul_smul, Finset.sum_add_distrib, Finset.sum_smul, Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem mem_unip_gen (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) (g : UA σ W.J)
    (hg : g ∈ unip σ W H') :
    mat g *ᵥ incV F H'.x = incV F H'.x ∧
      ∀ z, ∃ a : AE F E, mat g *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x := by
  unfold unip at hg
  induction hg using Subgroup.closure_induction with
  | mem u hu => exact hu
  | one => exact ⟨by simp [mat], fun z => ⟨0, by simp [mat]⟩⟩
  | mul u v _ _ hu hv =>
    have hm : mat (u * v) = mat u * mat v := rfl
    refine ⟨?_, fun z => ?_⟩
    · rw [hm, ← Matrix.mulVec_mulVec, hv.1, hu.1]
    · obtain ⟨a, ha⟩ := hv.2 z
      obtain ⟨b, hb⟩ := hu.2 z
      refine ⟨b + a, ?_⟩
      rw [hm, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hu.1, add_smul]
      abel
  | inv u _ hu =>
    have h1 : mat u⁻¹ * mat u = 1 := by
      rw [show mat u⁻¹ * mat u = mat (u⁻¹ * u) from rfl, inv_mul_cancel]; rfl
    have hx : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu.1]
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu.2 z
    have key : mat u⁻¹ *ᵥ (incM F H'.ι *ᵥ z + a • incV F H'.x) = incM F H'.ι *ᵥ z := by
      rw [← ha, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx] at key
    refine ⟨-a, ?_⟩
    rw [eq_sub_of_add_eq key, neg_smul, sub_eq_add_neg]

theorem unip_eq_hmat (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁)
    (hJ : ∀ i j, σ (W.J j i) = W.J i j) (hxx : form σ W.J H'.x H'.x = 0) (hyy : form σ W.J H'.y H'.y = 0)
    (hxy : form σ W.J H'.x H'.y = 1)
    (horth : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0)
    (hdec : ∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y)
    (g : UA σ W.J) (hg : g ∈ unip σ W H') :
    ∃ (b : Fin d₁ → AE F E) (c : AE F E), c + cA σ c = -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) ∧
      mat g = hmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c := by
  have hXX : hA σ W.J (incV F H'.x) (incV F H'.x) = 0 := by rw [hA_incV', hxx, map_zero]
  have hYY : hA σ W.J (incV F H'.y) (incV F H'.y) = 0 := by rw [hA_incV', hyy, map_zero]
  have hXY : hA σ W.J (incV F H'.x) (incV F H'.y) = 1 := by rw [hA_incV', hxy, map_one]
  have hYX : hA σ W.J (incV F H'.y) (incV F H'.x) = 1 := by
    rw [hA_herm σ W.J hσ hJ, hXY, map_one]
  have hιX : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.x) = 0 :=
    hA_ι_incV σ W.J H'.ι H'.x (fun u => (horth u).1)
  have hιY : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.y) = 0 :=
    hA_ι_incV σ W.J H'.ι H'.y (fun u => (horth u).2)
  have hXι : ∀ z, hA σ W.J (incV F H'.x) (incM F H'.ι *ᵥ z) = 0 := fun z => by
    rw [hA_herm σ W.J hσ hJ, hιX, map_zero]
  have hYι : ∀ z, hA σ W.J (incV F H'.y) (incM F H'.ι *ᵥ z) = 0 := fun z => by
    rw [hA_herm σ W.J hσ hJ, hιY, map_zero]
  obtain ⟨hgX, hgι⟩ := mem_unip_gen σ W H' g hg
  have inv : ∀ v w, hA σ W.J (mat g *ᵥ v) (mat g *ᵥ w) = hA σ W.J v w := hA_mat g
  have dec := decomp (F := F) H'.x H'.y H'.ι hdec
  obtain ⟨α, γ, β, hgY⟩ := dec (mat g *ᵥ incV F H'.y)
  have hγ : γ = 1 := by
    have h := inv (incV F H'.y) (incV F H'.x)
    rw [hgX, hgY] at h
    simp only [hA_add_l, hA_smul_l, hXX, hιX, hYX] at h
    linear_combination h
  subst hγ
  have ha : ∀ z (a : AE F E), mat g *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x →
      a = -hA σ W.J (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ β) := by
    intro z a h
    have h2 := inv (incM F H'.ι *ᵥ z) (incV F H'.y)
    rw [h, hgY] at h2
    simp only [hA_add_l, hA_add_r, hA_smul_l, hA_smul_r, hXX, hXY, hιX, hιY, hXι, mul_zero, mul_one, zero_add,
      add_zero, one_smul] at h2
    linear_combination h2
  have hα : α + cA σ α = -hA σ W.J (incM F H'.ι *ᵥ β) (incM F H'.ι *ᵥ β) := by
    have h3 := inv (incV F H'.y) (incV F H'.y)
    rw [hgY] at h3
    simp only [hA_add_l, hA_add_r, hA_smul_l, hA_smul_r, hXX, hXY, hYX, hYY, hιX, hιY, hXι, hYι, mul_zero, mul_one,
      zero_add, add_zero, one_smul, one_mul] at h3
    linear_combination h3
  refine ⟨β, α, hα, ?_⟩
  have key : ∀ v, mat g *ᵥ v = hmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ β) α *ᵥ v := by
    intro v
    obtain ⟨s, t, z, rfl⟩ := dec v
    obtain ⟨a, hz⟩ := hgι z
    have ha' := ha z a hz
    rw [hmat_mulVec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hgX, hz, hgY, hA_add_l, hA_smul_l, hXX, hιX, hYX, hXι, hYι,
      mul_zero, zero_add, add_zero, one_smul, mul_one]
    rw [ha']
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    ring
  exact hmat_ext key

end GlobalTheory.LeviModulus.HCoord
