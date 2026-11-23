import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabAtPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatPair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv GlobalTheory.ThK.LemF.QuotInv.StabCoord

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv.StabCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem mat_ext {n m : ℕ} {A B : Matrix (Fin n) (Fin m) (AE F E)} (h : ∀ z, A *ᵥ z = B *ᵥ z) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext h)

private theorem hAd_mulVec {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin n) (AE F E))
    (z w : Fin n → AE F E) : hAd σ J (A *ᵥ z) (A *ᵥ w) =
      z ⬝ᵥ ((Aᵀ * incM F J * A.map (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom) *ᵥ fun i => cA σ (w i)) := by
  have h : (fun i => cA σ ((A *ᵥ w) i)) = A.map (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom *ᵥ fun i => cA σ (w i) := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  rw [hAd, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z Aᵀ, Matrix.vecMul_transpose]

private theorem hAd_mat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (z w : Fin n → AE F E) :
    hAd σ J (mat g *ᵥ z) (mat g *ᵥ w) = hAd σ J z w := by
  have h : (mat g)ᵀ * incM F J * (mat g).map (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom = incM F J := g.2
  rw [hAd_mulVec, h, hAd]

private theorem unitary_of_hAd {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (A : Matrix (Fin n) (Fin n) (AE F E))
    (h : ∀ z w, hAd σ J (A *ᵥ z) (A *ᵥ w) = hAd σ J z w) :
    Aᵀ * incM F J * A.map (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom = incM F J := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have h2 : (fun k => cA σ ((Pi.single j 1 : Fin n → AE F E) k)) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [hAd_mulVec, hAd, h2] at h1
  simpa using h1

private theorem incM_mulVec_incV {n m : ℕ} (A : Matrix (Fin n) (Fin m) E) (u : Fin m → E) :
    incM F A *ᵥ incV F u = incV F (A *ᵥ u) := by
  ext i
  simp [incM, incV, Matrix.mulVec, dotProduct]

private theorem hAd_iota {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (ι : Matrix (Fin n) (Fin m) E)
    (h : ∀ u, form σ J (ι *ᵥ u) x = 0) (w : Fin m → AE F E) : hAd σ J (incM F ι *ᵥ w) (incV F x) = 0 := by
  have hw : w = ∑ j, w j • incV F (Pi.single j (1 : E)) := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, incV, smul_eq_mul]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_eq_of_ne hj.symm]) (by simp)]
    simp
  have h0 : ∀ s : Finset (Fin m), hAd σ J (incM F ι *ᵥ ∑ j ∈ s, w j • incV F (Pi.single j (1 : E))) (incV F x) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Matrix.mulVec_zero, hAd_zero_left]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Matrix.mulVec_add, hAd_add_left, ih, Matrix.mulVec_smul, hAd_smul_left,
        incM_mulVec_incV, hAd_incV, h, map_zero, mul_zero, add_zero]
  rw [hw]
  exact h0 _

private theorem nMat_mul {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (ι : Matrix (Fin n) (Fin m) E)
    (hXX : hAd σ J (incV F x) (incV F x) = 0) (hIX : ∀ w, hAd σ J (incM F ι *ᵥ w) (incV F x) = 0)
    (hXI : ∀ w, hAd σ J (incV F x) (incM F ι *ᵥ w) = 0) (w : Fin m → AE F E) (c : AE F E) (w' : Fin m → AE F E)
    (c' : AE F E) : nMat σ J x ι w c * nMat σ J x ι w' c' =
      nMat σ J x ι (w + w') (c + c' - hAd σ J (incM F ι *ᵥ w') (incM F ι *ᵥ w)) := by
  refine mat_ext fun z => ?_
  rw [← Matrix.mulVec_mulVec, nMat_mulVec, nMat_mulVec, nMat_mulVec]
  simp only [hAd_add_left, hAd_sub_left, hAd_smul_left, hAd_add_right, hXX, hIX, hXI, Matrix.mulVec_add]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem nMat_zero {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (ι : Matrix (Fin n) (Fin m) E) :
    nMat σ J x ι 0 0 = 1 := by
  refine mat_ext fun z => ?_
  rw [nMat_mulVec, Matrix.mulVec_zero, hAd_zero_right, Matrix.one_mulVec]
  simp

private theorem pair_conj {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin m) E)
    (P : Matrix (Fin m) (Fin n) (AE F E))
    (hP : ∀ z, z = hAd σ J z (incV F y) • incV F x + incM F ι *ᵥ (P *ᵥ z) + hAd σ J z (incV F x) • incV F y)
    (hI : ∀ w, hAd σ J (incM F ι *ᵥ w) (incV F x) = 0 ∧ hAd σ J (incM F ι *ᵥ w) (incV F y) = 0)
    (g : UA σ J) (hx : mat g *ᵥ incV F x = incV F x) (hy : mat g *ᵥ incV F y = incV F y) :
    mat g * incM F ι = incM F ι * (P * mat g * incM F ι) ∧
      (∀ w c, mat g * nMat σ J x ι w c = nMat σ J x ι ((P * mat g * incM F ι) *ᵥ w) c * mat g) ∧
      ∀ w w', hAd σ J (incM F ι *ᵥ ((P * mat g * incM F ι) *ᵥ w)) (incM F ι *ᵥ ((P * mat g * incM F ι) *ᵥ w')) =
        hAd σ J (incM F ι *ᵥ w) (incM F ι *ᵥ w') := by
  have h1 : ∀ w, incM F ι *ᵥ ((P * mat g * incM F ι) *ᵥ w) = mat g *ᵥ (incM F ι *ᵥ w) := fun w => by
    have h := hP (mat g *ᵥ (incM F ι *ᵥ w))
    have hx' : hAd σ J (mat g *ᵥ (incM F ι *ᵥ w)) (incV F x) = 0 := by
      conv_lhs => rw [← hx]
      rw [hAd_mat, (hI w).1]
    have hy' : hAd σ J (mat g *ᵥ (incM F ι *ᵥ w)) (incV F y) = 0 := by
      conv_lhs => rw [← hy]
      rw [hAd_mat, (hI w).2]
    rw [hx', hy', zero_smul, zero_smul, zero_add, add_zero] at h
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h.symm
  refine ⟨mat_ext fun w => ?_, fun w c => mat_ext fun z => ?_, fun w w' => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1]
  · have hx' : hAd σ J (mat g *ᵥ z) (incV F x) = hAd σ J z (incV F x) := by
      conv_lhs => rw [← hx]
      rw [hAd_mat]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, nMat_mulVec, nMat_mulVec, h1, hAd_mat, hx']
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, hx]
  · rw [h1, h1, hAd_mat]

private theorem levi_conj (hσ : ∀ e, σ (σ e) = e) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (ι : Matrix (Fin n) (Fin m) E) (g : UA σ J) (t : (AE F E)ˣ) (hx : mat g *ᵥ incV F x = t.1 • incV F x)
    (hι : mat g * incM F ι = incM F ι) (w : Fin m → AE F E) (c : AE F E) :
    mat g⁻¹ * nMat σ J x ι w c * mat g =
      nMat σ J x ι (cA σ (t⁻¹ : (AE F E)ˣ).1 • w) ((t⁻¹ : (AE F E)ˣ).1 * cA σ (t⁻¹ : (AE F E)ˣ).1 * c) := by
  have key : nMat σ J x ι w c * mat g = mat g *
      nMat σ J x ι (cA σ (t⁻¹ : (AE F E)ˣ).1 • w) ((t⁻¹ : (AE F E)ˣ).1 * cA σ (t⁻¹ : (AE F E)ˣ).1 * c) := by
    refine mat_ext fun z => ?_
    have hI : ∀ w, mat g *ᵥ (incM F ι *ᵥ w) = incM F ι *ᵥ w := fun w => by rw [Matrix.mulVec_mulVec, hι]
    have ht : (t⁻¹ : (AE F E)ˣ).1 * t.1 = 1 := t.inv_mul
    have hx1 : incV F x = (t⁻¹ : (AE F E)ˣ).1 • (mat g *ᵥ incV F x) := by rw [hx, smul_smul, ht, one_smul]
    have hx' : hAd σ J (mat g *ᵥ z) (incV F x) = cA σ (t⁻¹ : (AE F E)ˣ).1 * hAd σ J z (incV F x) := by
      conv_lhs => rw [hx1]
      rw [hAd_smul_right, hAd_mat]
    have hw' : hAd σ J (mat g *ᵥ z) (incM F ι *ᵥ w) = hAd σ J z (incM F ι *ᵥ w) := by
      conv_lhs => rw [← hI]
      rw [hAd_mat]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, nMat_mulVec, nMat_mulVec, hx', hw']
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, hx, hI, hAd_smul_right, cA_cA hσ]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (hAd σ J z (incM F ι *ᵥ w) * incV F x i -
      hAd σ J z (incV F x) * cA σ (t⁻¹ : (AE F E)ˣ).1 * c * incV F x i) * ht
  rw [Matrix.mul_assoc, key, ← Matrix.mul_assoc, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mul]

private theorem frame_exists (hσ : ∀ e, σ (σ e) = e) {B : Base F E} {b : ℕ} {V : Spc F E (b + 2)} {V₁ : Spc F E b}
    {H : Plane E (b + 2) b} {i₀ i₁ : ℕ} (hH : H.IsAdapted σ B V V₁ i₀ i₁) (hJ : ∀ i j, σ (V.J j i) = V.J i j)
    (hL : Submodule.span E (V.L : Set (Fin (b + 2) → E)) = ⊤) :
    ∃ P : Matrix (Fin b) (Fin (b + 2)) (AE F E), P * incM F H.ι = 1 ∧
      ∀ z, z = hAd σ V.J z (incV F H.y) • incV F H.x + incM F H.ι *ᵥ (P *ᵥ z) + hAd σ V.J z (incV F H.x) • incV F H.y := by
  let T : (Fin b → E) × E × E →ₗ[E] (Fin (b + 2) → E) :=
    (Matrix.toLin' H.ι).coprod ((LinearMap.toSpanSingleton E _ H.x).coprod (LinearMap.toSpanSingleton E _ H.y))
  have hT : ∀ u s t, T (u, s, t) = H.ι *ᵥ u + (s • H.x + t • H.y) := fun u s t => by simp [T]
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hL, Submodule.span_le]
    intro z hz
    obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
    exact ⟨(u, s, t), by rw [hT, h]; abel⟩
  have hinj : Function.Injective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).2 hsurj
  let e := LinearEquiv.ofBijective T ⟨hinj, hsurj⟩
  let p : (Fin (b + 2) → E) →ₗ[E] (Fin b → E) := (LinearMap.fst E _ _).comp e.symm.toLinearMap
  have hp : ∀ u s t, p (T (u, s, t)) = u := fun u s t => by
    show (e.symm (e (u, s, t))).1 = u
    rw [e.symm_apply_apply]
  let P₀ := LinearMap.toMatrix' p
  have hP₀ : ∀ z, P₀ *ᵥ z = p z := fun z => LinearMap.toMatrix'_mulVec p z
  have h1 : P₀ * H.ι = 1 := by
    refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
    have := hp u 0 0
    rw [hT, zero_smul, zero_smul, add_zero, add_zero] at this
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hP₀, this, Matrix.one_mulVec]
  have hXX : hAd σ V.J (incV F H.x) (incV F H.x) = 0 := by rw [hAd_incV, hH.xx, map_zero]
  have hYY : hAd σ V.J (incV F H.y) (incV F H.y) = 0 := by rw [hAd_incV, hH.yy, map_zero]
  have hXY : hAd σ V.J (incV F H.x) (incV F H.y) = 1 := by rw [hAd_incV, hH.xy, map_one]
  have hYX : hAd σ V.J (incV F H.y) (incV F H.x) = 1 := by rw [← hAd_herm hσ hJ, hXY, map_one]
  have hIX := hAd_iota (F := F) V.J H.x H.ι (fun u => (hH.orth u).1)
  have hIY := hAd_iota (F := F) V.J H.y H.ι (fun u => (hH.orth u).2)
  have h1' : incM F P₀ * incM F H.ι = 1 := by
    simp only [incM]
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hb : ∀ z : Fin (b + 2) → E, incV F z = hAd σ V.J (incV F z) (incV F H.y) • incV F H.x +
      incM F H.ι *ᵥ (incM F P₀ *ᵥ incV F z) + hAd σ V.J (incV F z) (incV F H.x) • incV F H.y := fun z => by
    obtain ⟨⟨u, s, t⟩, rfl⟩ := hsurj z
    rw [incM_mulVec_incV P₀, hP₀, hp, hT]
    have h2 : incV F (H.ι *ᵥ u + (s • H.x + t • H.y)) = incM F H.ι *ᵥ incV F u +
        (inclR (F := F) (AF F) s • incV F H.x + inclR (F := F) (AF F) t • incV F H.y) := by
      rw [incM_mulVec_incV]
      funext i
      simp only [incV, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    rw [h2]
    simp only [hAd_add_left, hAd_smul_left, hXX, hYY, hXY, hYX, hIX, hIY, mul_zero, mul_one, zero_add, add_zero]
    abel
  refine ⟨incM F P₀, h1', fun w => ?_⟩
  have hw : w = ∑ j, w j • incV F (Pi.single j (1 : E)) := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, incV, smul_eq_mul]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_eq_of_ne hj.symm]) (by simp)]
    simp
  have h0 : ∀ s : Finset (Fin (b + 2)), ∀ z, z = ∑ j ∈ s, w j • incV F (Pi.single j (1 : E)) →
      z = hAd σ V.J z (incV F H.y) • incV F H.x + incM F H.ι *ᵥ (incM F P₀ *ᵥ z) +
        hAd σ V.J z (incV F H.x) • incV F H.y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rintro z rfl
      simp [hAd_zero_left]
    | insert a s ha ih =>
      rintro z rfl
      have e1 := ih _ rfl
      have e2 := hb (Pi.single a 1)
      rw [Finset.sum_insert ha]
      simp only [hAd_add_left, hAd_smul_left, Matrix.mulVec_add, Matrix.mulVec_smul, add_smul, mul_smul]
      funext i
      have e3 := congrFun e1 i
      have e4 := congrFun e2 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e3 e4 ⊢
      linear_combination e3 + w a * e4
  exact h0 _ w hw

private theorem half_two : algebraMap (AF F) (AE F E) (⅟2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one]

private theorem nMat_unitary (hσ : ∀ e, σ (σ e) = e) {n m : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin n → E) (ι : Matrix (Fin n) (Fin m) E)
    (hXX : hAd σ J (incV F x) (incV F x) = 0) (hIX : ∀ w, hAd σ J (incM F ι *ᵥ w) (incV F x) = 0)
    (w : Fin m → AE F E) (d : AE F E) (hd : d + cA σ d + hAd σ J (incM F ι *ᵥ w) (incM F ι *ᵥ w) = 0)
    (z z' : Fin n → AE F E) : hAd σ J (nMat σ J x ι w d *ᵥ z) (nMat σ J x ι w d *ᵥ z') = hAd σ J z z' := by
  have hXI : ∀ w, hAd σ J (incV F x) (incM F ι *ᵥ w) = 0 := fun w => by rw [← hAd_herm hσ hJ, hIX, map_zero]
  rw [nMat_mulVec, nMat_mulVec]
  simp only [hAd_add_left, hAd_sub_left, hAd_smul_left, hAd_add_right, hAd_sub_right, hAd_smul_right, hXX, hIX, hXI,
    hAd_herm hσ hJ]
  linear_combination (hAd σ J z (incV F x) * hAd σ J (incV F x) z') * hd

private theorem nMat_at {R : Type} [Zero R] {ev : AF F → R} {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (ι : Matrix (Fin n) (Fin m) E) {w : Fin m → AE F E} {d : AE F E} (hw : At ev w) (hd : At ev d) :
    At ev (nMat σ J x ι w d - 1) := fun u hu => by
  refine mat_ext fun z => ?_
  have h1 := at_mulVec (incM F ι) hw u hu
  have h2 := at_hAd_right (σ := σ) (J := J) z (at_mulVec (incM F ι) hw) u hu
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, nMat_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec]
  have e : z + hAd σ J z (incV F x) • (incM F ι *ᵥ w + d • incV F x) - hAd σ J z (incM F ι *ᵥ w) • incV F x - z =
      hAd σ J z (incV F x) • (incM F ι *ᵥ w + d • incV F x) - hAd σ J z (incM F ι *ᵥ w) • incV F x := by abel
  rw [e, smul_sub, smul_comm u, smul_add, h1, ← smul_assoc, ← smul_assoc, hd u hu, h2]
  simp

private theorem continuous_nMat {α : Type} [TopologicalSpace α] {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (ι : Matrix (Fin n) (Fin m) E) {p : α → Fin m → AE F E} {q : α → AE F E} (hp : Continuous p) (hq : Continuous q) :
    Continuous fun a => nMat σ J x ι (p a) (q a) := by
  haveI : IsTopologicalRing (AE F E) := topRing
  have hA : Continuous fun a => incM F ι *ᵥ p a := continuous_const.matrix_mulVec hp
  have hB : Continuous fun a => (fun i => cA σ ((incM F ι *ᵥ p a) i)) :=
    continuous_pi fun i => (cA_cont σ).comp ((continuous_apply i).comp hA)
  exact (continuous_const.add ((hA.add (hq.smul continuous_const)).matrix_vecMulVec continuous_const)).sub
    (continuous_const.matrix_vecMulVec (continuous_const.matrix_mulVec hB))

private theorem exists_unip (hσ : ∀ e, σ (σ e) = e) {R : Type} [Zero R] (ev : AF F → R) {n m : ℕ} (V : Spc F E n)
    (hJ : ∀ i j, σ (V.J j i) = V.J i j) (x : Fin n → E) (ι : Matrix (Fin n) (Fin m) E)
    (hXX : hAd σ V.J (incV F x) (incV F x) = 0) (hIX : ∀ w, hAd σ V.J (incM F ι *ᵥ w) (incV F x) = 0) :
    ∃ N : vecAt F E m ev × skewAt σ ev → stabAt σ V ev x, Continuous N ∧ ∀ p, mat (N p).1.1 =
      nMat σ V.J x ι p.1.1 (p.2.1 - (⅟2 : AF F) • hAd σ V.J (incM F ι *ᵥ p.1.1) (incM F ι *ᵥ p.1.1)) := by
  haveI : IsTopologicalRing (AE F E) := topRing
  have hXI : ∀ w, hAd σ V.J (incV F x) (incM F ι *ᵥ w) = 0 := fun w => by rw [← hAd_herm hσ hJ, hIX, map_zero]
  obtain ⟨d, hd⟩ : ∃ d : vecAt F E m ev × skewAt σ ev → AE F E,
      ∀ p, d p = p.2.1 - (⅟2 : AF F) • hAd σ V.J (incM F ι *ᵥ p.1.1) (incM F ι *ᵥ p.1.1) := ⟨_, fun _ => rfl⟩
  have hw : Continuous fun p : vecAt F E m ev × skewAt σ ev => p.1.1 := continuous_subtype_val.comp continuous_fst
  have hA : Continuous fun p : vecAt F E m ev × skewAt σ ev => incM F ι *ᵥ p.1.1 := continuous_const.matrix_mulVec hw
  have hdc : Continuous d := by
    rw [funext hd]
    exact (continuous_subtype_val.comp continuous_snd).sub
      (((continuous_hAd (σ := σ) (J := V.J)).comp (hA.prodMk hA)).const_smul (⅟2 : AF F))
  have hd0 : ∀ p, d p + cA σ (d p) + hAd σ V.J (incM F ι *ᵥ p.1.1) (incM F ι *ᵥ p.1.1) = 0 := fun p => by
    rw [hd, map_sub, map_smul, hAd_herm hσ hJ, p.2.2.2, Algebra.smul_def]
    linear_combination (-hAd σ V.J (incM F ι *ᵥ p.1.1) (incM F ι *ᵥ p.1.1)) * half_two (F := F) (E := E)
  have hdat : ∀ p, At ev (d p) := fun p u hu => by
    rw [hd, smul_sub, p.2.2.1 u hu, smul_comm, at_hAd_left (at_mulVec (incM F ι) p.1.2) _ u hu, smul_zero, sub_zero]
  have h1 : ∀ p, nMat σ V.J x ι p.1.1 (d p) * nMat σ V.J x ι (-p.1.1) (cA σ (d p)) = 1 := fun p => by
    rw [nMat_mul V.J x ι hXX hIX hXI, Matrix.mulVec_neg, hAd_neg_left, sub_neg_eq_add, hd0, add_neg_cancel, nMat_zero]
  have h2 : ∀ p, nMat σ V.J x ι (-p.1.1) (cA σ (d p)) * nMat σ V.J x ι p.1.1 (d p) = 1 := fun p => by
    rw [nMat_mul V.J x ι hXX hIX hXI, Matrix.mulVec_neg, hAd_neg_right, sub_neg_eq_add, add_comm (cA σ (d p)), hd0,
      neg_add_cancel, nMat_zero]
  let u : vecAt F E m ev × skewAt σ ev → GL (Fin n) (AE F E) := fun p => ⟨_, _, h1 p, h2 p⟩
  have hu : Continuous u := Units.continuous_iff.2
    ⟨continuous_nMat V.J x ι hw hdc, continuous_nMat V.J x ι hw.neg ((cA_cont σ).comp hdc)⟩
  have m1 : ∀ p, u p ∈ UG (cA σ) (incM F V.J) := fun p =>
    unitary_of_hAd _ (nMat_unitary hσ hJ x ι hXX hIX _ _ (hd0 p))
  have m2 : ∀ p, (⟨u p, m1 p⟩ : UA σ V.J) ∈ UAtSub σ V ev := fun p => nMat_at V.J x ι p.1.2 (hdat p)
  have m3 : ∀ p, (⟨⟨u p, m1 p⟩, m2 p⟩ : UAtSub σ V ev) ∈ stabAt σ V ev x := fun p => by
    show nMat σ V.J x ι p.1.1 (d p) *ᵥ incV F x = incV F x
    rw [nMat_mulVec, hXX, hXI, zero_smul, zero_smul, add_zero, sub_zero]
  refine ⟨fun p => ⟨_, m3 p⟩, ((hu.subtype_mk m1).subtype_mk m2).subtype_mk m3, fun p => ?_⟩
  rw [← hd]
  rfl

private theorem exists_homeo (hσ : ∀ e, σ (σ e) = e) {R : Type} [Zero R] (ev : AF F → R) {n m : ℕ} (V : Spc F E n)
    (hJ : ∀ i j, σ (V.J j i) = V.J i j) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin m) E)
    (P : Matrix (Fin m) (Fin n) (AE F E)) (hPI : P * incM F ι = 1)
    (hP : ∀ z, z = hAd σ V.J z (incV F y) • incV F x + incM F ι *ᵥ (P *ᵥ z) + hAd σ V.J z (incV F x) • incV F y)
    (hXX : hAd σ V.J (incV F x) (incV F x) = 0) (hYY : hAd σ V.J (incV F y) (incV F y) = 0)
    (hXY : hAd σ V.J (incV F x) (incV F y) = 1)
    (hI : ∀ w, hAd σ V.J (incM F ι *ᵥ w) (incV F x) = 0 ∧ hAd σ V.J (incM F ι *ᵥ w) (incV F y) = 0) :
    ∃ Φ : stabAtPair σ V ev x y × (vecAt F E m ev × skewAt σ ev) ≃ₜ stabAt σ V ev x,
      ∀ l a c, mat (Φ (l, (a, c))).1.1 =
        nMat σ V.J x ι a.1 (c.1 - (⅟2 : AF F) • hAd σ V.J (incM F ι *ᵥ a.1) (incM F ι *ᵥ a.1)) * mat l.1.1.1 := by
  haveI : IsTopologicalRing (AE F E) := topRing
  have hIX := fun w => (hI w).1
  have hIY := fun w => (hI w).2
  have hXI : ∀ w, hAd σ V.J (incV F x) (incM F ι *ᵥ w) = 0 := fun w => by rw [← hAd_herm hσ hJ, hIX, map_zero]
  have hYI : ∀ w, hAd σ V.J (incV F y) (incM F ι *ᵥ w) = 0 := fun w => by rw [← hAd_herm hσ hJ, hIY, map_zero]
  have hYX : hAd σ V.J (incV F y) (incV F x) = 1 := by rw [← hAd_herm hσ hJ, hXY, map_one]
  have hPI' : ∀ w, P *ᵥ (incM F ι *ᵥ w) = w := fun w => by rw [Matrix.mulVec_mulVec, hPI, Matrix.one_mulVec]
  have hPX : P *ᵥ incV F x = 0 := by
    have h := hP (incV F x)
    rw [hXY, hXX, one_smul, zero_smul, add_zero] at h
    rw [← hPI' (P *ᵥ incV F x), (left_eq_add.1 h), Matrix.mulVec_zero]
  obtain ⟨N, hNc, hN⟩ := exists_unip hσ ev V hJ x ι hXX hIX
  have hNY : ∀ p, mat (N p).1.1 *ᵥ incV F y - incV F y = incM F ι *ᵥ p.1.1 +
      (p.2.1 - (⅟2 : AF F) • hAd σ V.J (incM F ι *ᵥ p.1.1) (incM F ι *ᵥ p.1.1)) • incV F x := fun p => by
    rw [hN, nMat_mulVec, hYX, hYI, one_smul, zero_smul, sub_zero, add_sub_cancel_left]
  obtain ⟨D, hD⟩ : ∃ D : stabAt σ V ev x → Fin n → AE F E, ∀ q, D q = mat q.1.1 *ᵥ incV F y - incV F y :=
    ⟨_, fun _ => rfl⟩
  have hDc : Continuous D := by
    rw [funext hD]
    have : Continuous fun q : stabAt σ V ev x => mat q.1.1 :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))
    exact (this.matrix_mulVec continuous_const).sub continuous_const
  have hDat : ∀ q, At ev (D q) := fun q u hu => by
    have h : u • (mat q.1.1 - 1) = 0 := q.1.2 u hu
    have e : D q = (mat q.1.1 - 1) *ᵥ incV F y := by rw [hD, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [e, ← Matrix.smul_mulVec, h, Matrix.zero_mulVec]
  have hDdec : ∀ q, D q = incM F ι *ᵥ (P *ᵥ D q) + hAd σ V.J (D q) (incV F y) • incV F x := fun q => by
    have h := hP (D q)
    have hx : hAd σ V.J (D q) (incV F x) = 0 := by
      have hq : mat q.1.1 *ᵥ incV F x = incV F x := q.2
      have h1 := hAd_mat q.1.1 (incV F y) (incV F x)
      rw [hq] at h1
      rw [hD, hAd_sub_left, h1, sub_self]
    rw [hx, zero_smul, add_zero, add_comm] at h
    exact h
  have hD0 : ∀ q, hAd σ V.J (D q) (incV F y) + cA σ (hAd σ V.J (D q) (incV F y)) +
      hAd σ V.J (incM F ι *ᵥ (P *ᵥ D q)) (incM F ι *ᵥ (P *ᵥ D q)) = 0 := fun q => by
    have h1 := hAd_mat q.1.1 (incV F y) (incV F y)
    have e : mat q.1.1 *ᵥ incV F y =
        incV F y + (incM F ι *ᵥ (P *ᵥ D q) + hAd σ V.J (D q) (incV F y) • incV F x) := by
      rw [← hDdec, hD, add_sub_cancel]
    rw [e] at h1
    simp only [hAd_add_left, hAd_add_right, hAd_smul_left, hAd_smul_right, hXX, hYY, hXY, hYX, hIX, hIY, hXI, hYI] at h1
    linear_combination h1
  obtain ⟨C, hCc, hC1, hC2⟩ : ∃ C : stabAt σ V ev x → vecAt F E m ev × skewAt σ ev, Continuous C ∧
      (∀ q, (C q).1.1 = P *ᵥ D q) ∧ ∀ q, (C q).2.1 = hAd σ V.J (D q) (incV F y) +
        (⅟2 : AF F) • hAd σ V.J (incM F ι *ᵥ (P *ᵥ D q)) (incM F ι *ᵥ (P *ᵥ D q)) := by
    have hs : ∀ q, hAd σ V.J (D q) (incV F y) +
        (⅟2 : AF F) • hAd σ V.J (incM F ι *ᵥ (P *ᵥ D q)) (incM F ι *ᵥ (P *ᵥ D q)) ∈ skewAt σ ev := fun q => by
      refine ⟨fun u hu => ?_, ?_⟩
      · rw [smul_add, at_hAd_left (hDat q) _ u hu, smul_comm,
          at_hAd_left (at_mulVec (incM F ι) (at_mulVec P (hDat q))) _ u hu, smul_zero, add_zero]
      · have := hD0 q
        rw [map_add, map_smul, hAd_herm hσ hJ (incM F ι *ᵥ (P *ᵥ D q)), Algebra.smul_def]
        linear_combination this + (hAd σ V.J (incM F ι *ᵥ (P *ᵥ D q)) (incM F ι *ᵥ (P *ᵥ D q))) *
          half_two (F := F) (E := E)
    have c1 : Continuous fun q => P *ᵥ D q := continuous_const.matrix_mulVec hDc
    have c2 : Continuous fun q => incM F ι *ᵥ (P *ᵥ D q) := continuous_const.matrix_mulVec c1
    have c3 : Continuous fun q => hAd σ V.J (D q) (incV F y) :=
      (continuous_hAd (σ := σ) (J := V.J)).comp (hDc.prodMk continuous_const)
    have c4 := c3.add (((continuous_hAd (σ := σ) (J := V.J)).comp (c2.prodMk c2)).const_smul (⅟2 : AF F))
    exact ⟨fun q => (⟨_, at_mulVec P (hDat q)⟩, ⟨_, hs q⟩), (c1.subtype_mk _).prodMk (c4.subtype_mk hs),
      fun _ => rfl, fun _ => rfl⟩
  have hCY : ∀ q, mat (N (C q)).1.1 *ᵥ incV F y = mat q.1.1 *ᵥ incV F y := fun q => by
    have h := hNY (C q)
    rw [hC1, hC2, add_sub_cancel_right, ← hDdec, hD] at h
    exact sub_left_injective h
  have hmem : ∀ q, (N (C q))⁻¹ * q ∈ stabAtPair σ V ev x y := fun q => by
    show (mat (N (C q)).1.1⁻¹ * mat q.1.1) *ᵥ incV F y = incV F y
    rw [← Matrix.mulVec_mulVec, ← hCY, Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
  have hCN : ∀ (p) (l : stabAtPair σ V ev x y), C (N p * l.1) = p := fun p l => by
    have e : D (N p * l.1) = incM F ι *ᵥ p.1.1 +
        (p.2.1 - (⅟2 : AF F) • hAd σ V.J (incM F ι *ᵥ p.1.1) (incM F ι *ᵥ p.1.1)) • incV F x := by
      have hl : mat l.1.1.1 *ᵥ incV F y = incV F y := l.2
      rw [hD, ← hNY]
      show (mat (N p).1.1 * mat l.1.1.1) *ᵥ incV F y - _ = _
      rw [← Matrix.mulVec_mulVec, hl]
    have e1 : P *ᵥ D (N p * l.1) = p.1.1 := by
      rw [e, Matrix.mulVec_add, Matrix.mulVec_smul, hPI', hPX, smul_zero, add_zero]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [hC1, e1]
    · rw [hC2, e1, e, hAd_add_left, hAd_smul_left, hIY, hXY, mul_one, zero_add, sub_add_cancel]
  refine ⟨{ toFun := fun p => N p.2 * p.1.1
            invFun := fun q => (⟨_, hmem q⟩, C q)
            left_inv := fun p => ?_
            right_inv := fun q => mul_inv_cancel_left _ _
            continuous_toFun := (hNc.comp continuous_snd).mul (continuous_subtype_val.comp continuous_fst)
            continuous_invFun := (((hNc.comp hCc).inv.mul continuous_id).subtype_mk hmem).prodMk hCc }, fun l a c => ?_⟩
  · refine Prod.ext (Subtype.ext ?_) (hCN _ _)
    show (N (C (N p.2 * p.1.1)))⁻¹ * (N p.2 * p.1.1) = p.1.1
    rw [hCN, inv_mul_cancel_left]
  · show mat (N (a, c)).1.1 * mat l.1.1.1 = _
    rw [hN]

private theorem skew_mem (hσ : ∀ e, σ (σ e) = e) {n m : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (ι : Matrix (Fin n) (Fin m) E) {R : Type} [Zero R] {ev : AF F → R} {w : Fin m → AE F E} (hw : At ev w)
    (w' : Fin m → AE F E) :
    (⅟2 : AF F) • (hAd σ J (incM F ι *ᵥ w) (incM F ι *ᵥ w') - hAd σ J (incM F ι *ᵥ w') (incM F ι *ᵥ w)) ∈ skewAt σ ev := by
  refine ⟨fun u hu => ?_, ?_⟩
  · have h1 := at_hAd_left (σ := σ) (J := J) (at_mulVec (incM F ι) hw) (incM F ι *ᵥ w') u hu
    have h3 := at_hAd_right (σ := σ) (J := J) (incM F ι *ᵥ w') (at_mulVec (incM F ι) hw) u hu
    rw [smul_comm, smul_sub, h1, h3, sub_zero, smul_zero]
  · rw [map_smul, map_sub, hAd_herm hσ hJ, hAd_herm hσ hJ, ← smul_neg, neg_sub]

private theorem cont_skew {α : Type} [TopologicalSpace α] {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin m) E)
    {p q : α → Fin m → AE F E} (hp : Continuous p) (hq : Continuous q) :
    Continuous fun a => (⅟2 : AF F) • (hAd σ J (incM F ι *ᵥ p a) (incM F ι *ᵥ q a) -
      hAd σ J (incM F ι *ᵥ q a) (incM F ι *ᵥ p a)) := by
  haveI : IsTopologicalRing (AE F E) := topRing
  have hA : Continuous fun a => incM F ι *ᵥ p a := continuous_const.matrix_mulVec hp
  have hB : Continuous fun a => incM F ι *ᵥ q a := continuous_const.matrix_mulVec hq
  exact (((continuous_hAd (σ := σ) (J := J)).comp (hA.prodMk hB)).sub
    ((continuous_hAd (σ := σ) (J := J)).comp (hB.prodMk hA))).const_smul (⅟2 : AF F)

end GlobalTheory.ThK.LemF.QuotInv.StabCoord

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.config_a_local_measure_preserving : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (hσ : ∀ e, σ (σ e) = e) (v : Pl F),
    ∃ Φ : stabAtPair σ G.V (evFin F v) H.x H.y × (vecAt F E b (evFin F v) × skewAt σ (evFin F v)) ≃ₜ
        stabAt σ G.V (evFin F v) H.x,
      (∀ q', ∃ (l' : stabAtPair σ G.V (evFin F v) H.x H.y)
        (f : stabAtPair σ G.V (evFin F v) H.x H.y → vecAt F E b (evFin F v))
        (g : stabAtPair σ G.V (evFin F v) H.x H.y × vecAt F E b (evFin F v) → skewAt σ (evFin F v)),
        Continuous f ∧ Continuous g ∧ ∀ l a c, Φ (l, (a, c)) * q' = Φ (l * l', (a + f l, c + g (l, a)))) ∧
      ∀ (t : (AE F E)ˣ) (m : UA σ G.V.J), IsLevi H t (1 : UA σ G₁.V.J) m → ∀ l a c,
        ((Φ (l, (vecAtSmul (cA σ (t⁻¹ : (AE F E)ˣ).1) a, normSmul hσ (t⁻¹ : (AE F E)ˣ).1 c))).1.1 : UA σ G.V.J) =
          m⁻¹ * (Φ (l, (a, c))).1.1 * m := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ hσ v
  haveI : IsTopologicalRing (AE F E) := topRing
  have hJ : ∀ i j, σ (G.V.J j i) = G.V.J i j := hT.geo.hV.herm
  have hH := hC.hH
  have hXX : hAd σ G.V.J (incV F H.x) (incV F H.x) = 0 := by rw [hAd_incV, hH.xx, map_zero]
  have hYY : hAd σ G.V.J (incV F H.y) (incV F H.y) = 0 := by rw [hAd_incV, hH.yy, map_zero]
  have hXY : hAd σ G.V.J (incV F H.x) (incV F H.y) = 1 := by rw [hAd_incV, hH.xy, map_one]
  have hIX : ∀ w, hAd σ G.V.J (incM F H.ι *ᵥ w) (incV F H.x) = 0 :=
    hAd_iota G.V.J H.x H.ι (fun u => (hH.orth u).1)
  have hIY : ∀ w, hAd σ G.V.J (incM F H.ι *ᵥ w) (incV F H.y) = 0 :=
    hAd_iota G.V.J H.y H.ι (fun u => (hH.orth u).2)
  have hXI : ∀ w, hAd σ G.V.J (incV F H.x) (incM F H.ι *ᵥ w) = 0 := fun w => by
    rw [← hAd_herm hσ hJ, hIX, map_zero]
  obtain ⟨P, hPI, hP⟩ := frame_exists hσ hH hJ hT.geo.hV.lat.span_eq_top
  obtain ⟨Φ, hΦ⟩ := exists_homeo hσ (evFin F v) G.V hJ H.x H.y H.ι P hPI hP hXX hYY hXY (fun w => ⟨hIX w, hIY w⟩)
  have hmul := nMat_mul (σ := σ) G.V.J H.x H.ι hXX hIX hXI
  have hpair := pair_conj (σ := σ) G.V.J H.x H.y H.ι P hP (fun w => ⟨hIX w, hIY w⟩)
  have h2 : algebraMap (AF F) (AE F E) (⅟2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one]
  have key : ∀ (l' : stabAtPair σ G.V (evFin F v) H.x H.y) (a' : vecAt F E b (evFin F v)) (c' : skewAt σ (evFin F v)), ∃ (f : stabAtPair σ G.V (evFin F v) H.x H.y → vecAt F E b (evFin F v)) (g : stabAtPair σ G.V (evFin F v) H.x H.y × vecAt F E b (evFin F v) → skewAt σ (evFin F v)),
      Continuous f ∧ Continuous g ∧ ∀ l a c, Φ (l, (a, c)) * Φ (l', (a', c')) = Φ (l * l', (a + f l, c + g (l, a))) := by
    intro l' a' c'
    have hc0 : Continuous (fun l : stabAtPair σ G.V (evFin F v) H.x H.y => mat l.1.1.1) :=
      continuous_mat_pair (σ := σ) G.V (evFin F v) H.x H.y
    have hc1 : Continuous (fun l : stabAtPair σ G.V (evFin F v) H.x H.y => HMul.hMul P (mat l.1.1.1)) :=
      Continuous.matrix_mul (continuous_const (y := P)) hc0
    have hl0 : Continuous (fun l : stabAtPair σ G.V (evFin F v) H.x H.y => HMul.hMul (HMul.hMul P (mat l.1.1.1)) (incM F H.ι)) :=
      Continuous.matrix_mul hc1 (continuous_const (y := incM F H.ι))
    have hl1 : Continuous (fun l : stabAtPair σ G.V (evFin F v) H.x H.y => (HMul.hMul (HMul.hMul P (mat l.1.1.1)) (incM F H.ι)) *ᵥ a'.1) :=
      Continuous.matrix_mulVec hl0 (continuous_const (y := a'.1))
    obtain ⟨f, hf, hfdef⟩ : ∃ f : stabAtPair σ G.V (evFin F v) H.x H.y → vecAt F E b (evFin F v), Continuous f ∧
        ∀ l, (f l).1 = (HMul.hMul (HMul.hMul P (mat l.1.1.1)) (incM F H.ι)) *ᵥ a'.1 :=
      ⟨fun l => ⟨_, at_mulVec _ a'.2⟩, hl1.subtype_mk _, fun l => rfl⟩
    obtain ⟨g, hg, hgdef⟩ : ∃ g : stabAtPair σ G.V (evFin F v) H.x H.y × vecAt F E b (evFin F v) → skewAt σ (evFin F v),
        Continuous g ∧ ∀ p, (g p).1 = c'.1 + (⅟2 : AF F) • (hAd σ G.V.J (incM F H.ι *ᵥ p.2.1) (incM F H.ι *ᵥ (f p.1).1) -
          hAd σ G.V.J (incM F H.ι *ᵥ (f p.1).1) (incM F H.ι *ᵥ p.2.1)) :=
      ⟨fun p => ⟨_, (skewAt σ (evFin F v)).add_mem c'.2 (skew_mem hσ hJ H.ι p.2.2 (f p.1).1)⟩,
        (continuous_const.add (cont_skew (σ := σ) G.V.J H.ι (p := fun p : stabAtPair σ G.V (evFin F v) H.x H.y × vecAt F E b (evFin F v) => p.2.1)
          (q := fun p : stabAtPair σ G.V (evFin F v) H.x H.y × vecAt F E b (evFin F v) => (f p.1).1) (continuous_subtype_val.comp continuous_snd)
          (continuous_subtype_val.comp (hf.comp continuous_fst)))).subtype_mk _, fun p => rfl⟩
    refine ⟨f, g, hf, hg, fun l a c => ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Units.ext
    show mat (Φ (l, (a, c))).1.1 * mat (Φ (l', (a', c'))).1.1 = mat (Φ (l * l', (a + f l, c + g (l, a)))).1.1
    rw [hΦ, hΦ, hΦ]
    obtain ⟨-, hcom, hh0⟩ := hpair l.1.1.1 l.1.2 l.2
    rw [AddSubgroup.coe_add, AddSubgroup.coe_add, hfdef, hgdef]
    show _ = _ * (mat l.1.1.1 * mat l'.1.1.1)
    rw [Matrix.mul_assoc (nMat _ _ _ _ a.1 _) (mat l.1.1.1), ← Matrix.mul_assoc (mat l.1.1.1), hcom,
      Matrix.mul_assoc _ (mat l.1.1.1), ← Matrix.mul_assoc (nMat _ _ _ _ a.1 _), hmul]
    congr 2
    have e0 := hh0 a'.1 a'.1
    simp only [hfdef, Matrix.mulVec_add, hAd_add_left, hAd_add_right, Algebra.smul_def] at e0 ⊢
    rw [e0]
    linear_combination (hAd σ G.V.J (incM F H.ι *ᵥ ((HMul.hMul (HMul.hMul P (mat l.1.1.1)) (incM F H.ι)) *ᵥ a'.1)) (incM F H.ι *ᵥ a.1)) * h2
  refine ⟨Φ, fun q' => ?_, fun t m hm l a c => ?_⟩
  · obtain ⟨f, g, hf, hg, h⟩ := key (Φ.symm q').1 (Φ.symm q').2.1 (Φ.symm q').2.2
    refine ⟨(Φ.symm q').1, f, g, hf, hg, fun l a c => ?_⟩
    have hp : Φ ((Φ.symm q').1, ((Φ.symm q').2.1, (Φ.symm q').2.2)) = q' := Φ.apply_symm_apply q'
    rw [← h l a c, hp]
  · have hm3 : mat m * incM F H.ι = incM F H.ι := by
      rw [hm.2.2]; exact Matrix.mul_one _
    have hlev := levi_conj hσ G.V.J H.x H.ι m t hm.1 hm3
    obtain ⟨hLI, -, -⟩ := hpair l.1.1.1 l.1.2 l.2
    have hLm : mat l.1.1.1 * mat m = mat m * mat l.1.1.1 := by
      refine ext_of_frame hP ?_ ?_ ?_
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hm.1, Matrix.mulVec_smul, l.1.2, hm.1]
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hm.2.1, Matrix.mulVec_smul, l.2, hm.2.1]
      · rw [Matrix.mul_assoc (mat l.1.1.1) (mat m) (incM F H.ι), hm3, hLI, Matrix.mul_assoc (mat m) (mat l.1.1.1) (incM F H.ι),
          hLI, ← Matrix.mul_assoc (mat m) (incM F H.ι), hm3]
    apply Subtype.ext; apply Units.ext
    show mat (Φ (l, _)).1.1 = mat m⁻¹ * mat (Φ (l, (a, c))).1.1 * mat m
    rw [hΦ, hΦ, Matrix.mul_assoc (mat m⁻¹), Matrix.mul_assoc _ (mat l.1.1.1), hLm, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hlev]
    congr 2
    show (t⁻¹ : (AE F E)ˣ).1 * cA σ (t⁻¹ : (AE F E)ˣ).1 * c.1 - (⅟2 : AF F) • hAd σ G.V.J
      (incM F H.ι *ᵥ (cA σ (t⁻¹ : (AE F E)ˣ).1 • a.1)) (incM F H.ι *ᵥ (cA σ (t⁻¹ : (AE F E)ˣ).1 • a.1)) = _
    rw [Matrix.mulVec_smul, hAd_smul_left, hAd_smul_right, cA_cA hσ]
    simp only [Algebra.smul_def]
    ring

end
