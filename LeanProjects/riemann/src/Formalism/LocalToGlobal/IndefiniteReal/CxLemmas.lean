import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section SlopeTestRemainingChoices

theorem kOf_spec (σ : K →+* ℂ) {z : ℂ} (h : ∃ a : K, σ a = z) : σ (kOf σ z) = z := by
  unfold kOf
  rw [dif_pos h]
  exact h.choose_spec

theorem kOf_of (σ : K →+* ℂ) (a : K) : kOf σ (σ a) = a :=
  σ.injective (kOf_spec σ ⟨a, rfl⟩)

theorem kMat_map (σ : K →+* ℂ) {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℂ} (h : IsRat σ M) :
    (kMat σ M).map σ = M := by
  ext i k
  simp [kMat, kOf_spec σ (h i k)]

theorem kMat_one (σ : K →+* ℂ) (n : ℕ) : kMat σ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i k
  simp only [kMat, Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · simpa using kOf_of σ 1
  · simpa using kOf_of σ 0

theorem cpt_mulVec (σ : K →+* ℂ) {m n : ℕ} (M : Matrix (Fin m) (Fin n) K) (x : Fin n → K) :
    cpt σ (M.mulVec x) = (M.map σ).mulVec (cpt σ x) := by
  ext i
  simp [cpt, Matrix.mulVec, dotProduct, map_sum]

theorem cpt_injective (σ : K →+* ℂ) {n : ℕ} : Function.Injective (cpt σ (n := n)) := by
  intro x y h
  funext i
  exact σ.injective (congrFun h i)

theorem cpt_add (σ : K →+* ℂ) {n : ℕ} (x y : Fin n → K) : cpt σ (x + y) = cpt σ x + cpt σ y := by
  funext i
  simp [cpt]

theorem lin_apply {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (v : Fin n → E) (y : Fin n → ℂ) :
    lin v y = ∑ i, y i • v i := rfl

theorem lin_single {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (v : Fin n → E) (k : Fin n) :
    lin v (Pi.single k 1) = v k := by
  classical
  simp [lin, Fintype.linearCombination_apply, Pi.single_apply]

theorem lin_injective {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} {v : Fin n → E}
    (h : LinearIndependent ℂ v) : Function.Injective (lin v) := by
  intro y z hyz
  have h0 : ∑ i, (y - z) i • v i = 0 := by
    have := sub_eq_zero.2 hyz
    simpa [lin, Fintype.linearCombination_apply, sub_smul, Finset.sum_sub_distrib] using this
  funext i
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 h (y - z) h0 i)

theorem li_of_lin_injective {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} {v : Fin n → E}
    (h : Function.Injective (lin v)) : LinearIndependent ℂ v := by
  refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
  have h1 : lin v g = lin v 0 := by
    simp [lin, Fintype.linearCombination_apply, hg]
  exact congrFun (h h1) i

theorem solve_spec {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] E) {e : E}
    (h : e ∈ LinearMap.range f) : f (solve f e) = e := by
  have h' : ∃ y, f y = e := LinearMap.mem_range.1 h
  unfold solve
  rw [dif_pos h']
  exact h'.choose_spec

theorem relMat_spec {E : Type} [AddCommGroup E] [Module ℂ E] {D n : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E)
    (g : (Fin n → ℂ) →ₗ[ℂ] E) (h : ∀ k, g (Pi.single k 1) ∈ LinearMap.range f) (y : Fin n → ℂ) :
    f ((relMat f g).mulVec y) = g y := by
  classical
  have hy : y = ∑ k, y k • Pi.single k (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  have hm : (relMat f g).mulVec y = ∑ k, y k • solve f (g (Pi.single k 1)) := by
    ext i
    simp [relMat, Matrix.mulVec, dotProduct, mul_comm]
  rw [hm, map_sum]
  simp only [map_smul, solve_spec f (h _)]
  conv_rhs => rw [hy]
  rw [map_sum]
  simp only [map_smul]

theorem relMat_self {E : Type} [AddCommGroup E] [Module ℂ E] {D : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E)
    (hf : Function.Injective f) : relMat f f = 1 := by
  classical
  ext i k
  have hs : solve f (f (Pi.single k 1)) = Pi.single k 1 :=
    hf (solve_spec f (LinearMap.mem_range_self f _))
  simp only [relMat, Matrix.of_apply, hs, Matrix.one_apply, Pi.single_apply]

theorem relMat_bij {E : Type} [AddCommGroup E] [Module ℂ E] {D n : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E)
    (g : (Fin n → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f) (hg : Function.Injective g)
    (hr : LinearMap.range g = LinearMap.range f) : Function.Bijective (relMat f g).mulVec := by
  have hspec := relMat_spec f g (fun k => hr ▸ LinearMap.mem_range_self g _)
  refine ⟨fun y y' h => hg ?_, fun x => ?_⟩
  · rw [← hspec y, ← hspec y', h]
  · obtain ⟨y, hy⟩ := LinearMap.mem_range.1 (hr ▸ LinearMap.mem_range_self f x : f x ∈ LinearMap.range g)
    exact ⟨y, hf (by rw [hspec y, hy])⟩

theorem bij_of_map (σ : K →+* ℂ) {m n : ℕ} (M : Matrix (Fin m) (Fin n) K)
    (h : Function.Bijective (M.map σ).mulVec) : Function.Bijective M.mulVec := by
  have hinj : Function.Injective M.mulVec := by
    intro x y hxy
    apply cpt_injective σ
    apply h.1
    rw [← cpt_mulVec, ← cpt_mulVec, hxy]
  have hmn : m = n := by
    have e := (LinearEquiv.ofBijective (M.map σ).mulVecLin h).finrank_eq
    simpa using e.symm
  subst hmn
  exact ⟨hinj, (Matrix.mulVecLin M).injective_iff_surjective.1 hinj⟩

private theorem inner_lin_lemma {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ}
    (w : Fin n → E) (a b : Fin n → ℂ) :
    star a ⬝ᵥ (Matrix.gram ℂ w *ᵥ b) = ⟪lin w a, lin w b⟫_ℂ := by
  simp only [lin_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, dotProduct,
    Matrix.mulVec, Matrix.gram_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def]
  ring

theorem majAt_gram {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (w : Fin n → E)
    (hli : LinearIndependent ℂ w) (hX : X v = frameOf (Matrix.gram ℂ w)) (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y = ⟪lin w (cpt v.embedding x), lin w (cpt v.embedding y)⟫_ℂ := by
  have hmet := (frameOfSpec n _ (Matrix.posDef_gram_of_linearIndependent hli)).2
  have hmet' : ((X v)⁻¹)ᴴ * (X v)⁻¹ = Matrix.gram ℂ w := by rw [hX]; exact hmet
  have hva : ∀ z : Fin n → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v z = cpt v.embedding z := fun z => by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, cpt]
  unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord
  rw [hva, hva]
  change star ((X v)⁻¹ *ᵥ cpt v.embedding x) ⬝ᵥ ((X v)⁻¹ *ᵥ cpt v.embedding y) = _
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hmet', inner_lin_lemma]

theorem frame_gram_unit {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ} (w : Fin n → E)
    (hli : LinearIndependent ℂ w) : IsUnit (frameOf (Matrix.gram ℂ w)).det :=
  (frameOfSpec n _ (Matrix.posDef_gram_of_linearIndependent hli)).1

theorem majAt_gram_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (w : Fin n → E)
    (hli : LinearIndependent ℂ w) (c : ℝ) (hc : 0 < c) (hX : X v = frameOf ((c : ℂ) • Matrix.gram ℂ w))
    (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y =
      (c : ℂ) * ⟪lin w (cpt v.embedding x), lin w (cpt v.embedding y)⟫_ℂ := by
  have hc' : (0 : ℂ) < (c : ℂ) := Complex.zero_lt_real.2 hc
  have hmet := (frameOfSpec n _ ((Matrix.posDef_gram_of_linearIndependent hli).smul hc')).2
  have hmet' : ((X v)⁻¹)ᴴ * (X v)⁻¹ = (c : ℂ) • Matrix.gram ℂ w := by rw [hX]; exact hmet
  have hva : ∀ z : Fin n → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v z = cpt v.embedding z := fun z => by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, cpt]
  unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord
  rw [hva, hva]
  change star ((X v)⁻¹ *ᵥ cpt v.embedding x) ⬝ᵥ ((X v)⁻¹ *ᵥ cpt v.embedding y) = _
  have hsm : ((c : ℂ) • Matrix.gram ℂ w) *ᵥ cpt v.embedding y =
      (c : ℂ) • (Matrix.gram ℂ w *ᵥ cpt v.embedding y) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hmet', hsm,
    dotProduct_smul, smul_eq_mul, inner_lin_lemma]

theorem frame_gram_smul_unit {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ} (w : Fin n → E)
    (hli : LinearIndependent ℂ w) (c : ℝ) (hc : 0 < c) : IsUnit (frameOf ((c : ℂ) • Matrix.gram ℂ w)).det :=
  (frameOfSpec n _ ((Matrix.posDef_gram_of_linearIndependent hli).smul (Complex.zero_lt_real.2 hc))).1

theorem majAt_add_right {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K)
    (x y z : Fin n → K) : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x (y + z) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y + Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x z := by
  have hv : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v (y + z) =
      Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v y + Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v z := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord
  rw [hv, Matrix.mulVec_add]
  simp [mul_add, Finset.sum_add_distrib]

theorem majAt_zero_left {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K)
    (y : Fin n → K) : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v 0 y = 0 := by
  have hv : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v 0 = 0 := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord
  rw [hv, Matrix.mulVec_zero]
  simp

theorem majAt_sum_right {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K)
    (x : Fin n → K) {ι : Type} (s : Finset ι) (y : ι → Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x (∑ q ∈ s, y q) =
      ∑ q ∈ s, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x (y q) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hv : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v 0 = 0 := by
      funext i
      simp [Formalism.HermitianLatticesTheory.vecAt]
    simp only [Finset.sum_empty]
    unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord
    rw [hv, Matrix.mulVec_zero]
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, majAt_add_right, ih]

end SlopeTestRemainingChoices

section Parts

variable {Bs : DefBase K} (Df : DefSide Bs) (t : Bs.Tup) (hi : iSupIndep (Df.Qp t)) (ht : (⨆ p, Df.Qp t p) = ⊤)

include hi ht in
theorem partPr_eq (q : Bs.Ix) :
    ∃ hc : IsCompl (Df.Qp t q) (⨆ (p' : Bs.Ix) (_ : p' ≠ q), Df.Qp t p'),
      partPr Df t q = LinearMap.toMatrix' ((Df.Qp t q).subtype ∘ₗ Submodule.projectionOnto _ _ hc) := by
  have hc : IsCompl (Df.Qp t q) (⨆ (p' : Bs.Ix) (_ : p' ≠ q), Df.Qp t p') :=
    ⟨hi q, codisjoint_iff.2 (by rw [← iSup_split_single (Df.Qp t) q]; exact ht)⟩
  exact ⟨hc, by unfold partPr; rw [dif_pos hc]⟩

include hi ht in
theorem partPr_mem (q : Bs.Ix) (y : Fin (Df.dQ t) → K) : (partPr Df t q).mulVec y ∈ Df.Qp t q := by
  obtain ⟨hc, heq⟩ := partPr_eq Df t hi ht q
  rw [heq, LinearMap.toMatrix'_mulVec]
  exact Submodule.coe_mem _

include hi ht in
theorem partPr_self {p : Bs.Ix} {x : Fin (Df.dQ t) → K} (hx : x ∈ Df.Qp t p) : (partPr Df t p).mulVec x = x := by
  obtain ⟨hc, heq⟩ := partPr_eq Df t hi ht p
  rw [heq, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply]
  have := Submodule.projectionOnto_apply_left hc ⟨x, hx⟩
  rw [this]
  rfl

include hi ht in
theorem partPr_other {p q : Bs.Ix} {x : Fin (Df.dQ t) → K} (hx : x ∈ Df.Qp t p) (hq : q ≠ p) :
    (partPr Df t q).mulVec x = 0 := by
  obtain ⟨hc, heq⟩ := partPr_eq Df t hi ht q
  rw [heq, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply]
  have hx' : x ∈ ⨆ (p' : Bs.Ix) (_ : p' ≠ q), Df.Qp t p' :=
    (le_biSup (fun p' => Df.Qp t p') (Ne.symm hq)) hx
  have := Submodule.linearProjOfIsCompl_apply_right hc ⟨x, hx'⟩
  rw [this]
  rfl

include hi ht in
theorem sum_partPr_mulVec (y : Fin (Df.dQ t) → K) : ∑ q, (partPr Df t q).mulVec y = y := by
  classical
  let T : (Fin (Df.dQ t) → K) →ₗ[K] (Fin (Df.dQ t) → K) :=
    (∑ q, (partPr Df t q).mulVecLin) - LinearMap.id
  have hT : ∀ z, T z = ∑ q, (partPr Df t q).mulVec z - z := by
    intro z
    simp [T, LinearMap.sum_apply]
  have hle : (⨆ p, Df.Qp t p) ≤ LinearMap.ker T := by
    refine iSup_le fun p x hx => ?_
    rw [LinearMap.mem_ker, hT, Finset.sum_eq_single p]
    · rw [partPr_self Df t hi ht hx, sub_self]
    · intro q _ hq
      exact partPr_other Df t hi ht hx hq
    · intro h
      exact absurd (Finset.mem_univ p) h
  have hy : y ∈ LinearMap.ker T := hle (ht ▸ Submodule.mem_top)
  rw [LinearMap.mem_ker, hT] at hy
  exact sub_eq_zero.1 hy

theorem rowXE_part (hW : Df.WF) (Y : Matrix (Fin (Df.dQ Bs.μ0)) (Fin (Df.dQ Bs.μ0)) ℂ) (hY : IsUnit Y.det)
    (κ : InfinitePlace K → ℝ) (hκ : ∀ v, 0 < κ v) (lam : Bs.J → Bs.Ix → InfinitePlace K → ℝ)
    (hlam : ∀ j p v, 0 < lam j p v) (v : InfinitePlace K) (hv : v ≠ Bs.v0)
    (horth : ∀ p q, p ≠ q → ∀ x ∈ Df.Qp Bs.μ0 p, ∀ y ∈ Df.Qp Bs.μ0 q,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (Df.XQ Bs.μ0) v x y = 0)
    (p : Bs.Ix) (x : Fin (Df.dQ Bs.μ0) → K) (hx : x ∈ Df.Qp Bs.μ0 p) (y : Fin (Df.dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (rowXE Df Y κ lam) v x y =
      ((κ v * ∏ j, lam j p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (Df.XQ Bs.μ0) v x y := by
  classical
  have hi := hW.Qp_indep
  have ht := hW.Qp_top
  have hdet : ∀ v, IsUnit ((Df.XQ Bs.μ0) v).det := fun v => (hW.XQ_quot Bs.μ0 v).1
  have hsum : ∑ q, partPr Df Bs.μ0 q = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun z => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.sum_mulVec, Matrix.one_mulVec]
    exact sum_partPr_mulVec Df Bs.μ0 hi ht z
  have hmul : ∀ q q', q ≠ q' → partPr Df Bs.μ0 q * partPr Df Bs.μ0 q' = 0 := by
    intro q q' hqq'
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun z => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    exact partPr_other Df Bs.μ0 hi ht (partPr_mem Df Bs.μ0 hi ht q' z) hqq'
  have key := weightFramePart K _ Bs.Ix (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam j p v) (Df.XQ Bs.μ0)
    hdet (fun p v => mul_pos (hκ v) (Finset.prod_pos fun j _ => hlam j p v)) hsum hmul v
    (fun q q' hqq' x' y' => horth q q' hqq' _ (partPr_mem Df Bs.μ0 hi ht q x') _ (partPr_mem Df Bs.μ0 hi ht q' y'))
    p x y (partPr_self Df Bs.μ0 hi ht hx)
  have hrow : rowXE Df Y κ lam v =
      weightFrame (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam j p v) (Df.XQ Bs.μ0) v := by
    simp [rowXE, rowFrame, spliceFrame, pushFrame, Function.update_of_ne hv]
  have hmaj : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (rowXE Df Y κ lam) v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _)
        (weightFrame (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam j p v) (Df.XQ Bs.μ0)) v x y := by
    unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord
    rw [hrow]
  rw [hmaj, key]

end Parts

theorem lin_basis {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] E) :
    lin (fun i => f (Pi.single i 1)) = f := by
  classical
  apply LinearMap.pi_ext
  intro i x
  simp only [lin, Fintype.linearCombination_apply, Pi.single_apply, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← map_smul]
  congr 1
  ext j
  simp [Pi.single_apply]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem mem_Ep (p : Bs.Ix) (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    y ∈ X.Ep cr b p ↔ X.iC cr b Bs.μ0 (cpt Bs.v0.embedding y) ∈ X.EEp p := Iff.rfl

theorem mem_WpK (j : Bs.J) (p : Bs.Ix) (y : Fin (X.dW b j) → K) :
    y ∈ X.WpK b j p ↔ X.w0C b j (cpt Bs.v0.embedding y) ∈ X.Wp j p := Iff.rfl

theorem key_row (h2 : X.H2 cr b) (hr : X.RATmu cr b) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b Bs.μ0 (cpt Bs.v0.embedding ((X.rowMat cr b t).mulVec x)) = X.iC cr b t (cpt Bs.v0.embedding x) := by
  rw [cpt_mulVec, rowMat, kMat_map _ (hr t), rowMatC]
  exact relMat_spec _ _ (fun k => (h2.2.1 t).2 ▸ LinearMap.mem_range_self _ _) _

theorem rowMat_bij (h2 : X.H2 cr b) (hr : X.RATmu cr b) (t : Bs.Tup) :
    Function.Bijective (X.rowMat cr b t).mulVec := by
  refine bij_of_map Bs.v0.embedding _ ?_
  rw [rowMat, kMat_map _ (hr t), rowMatC]
  exact relMat_bij _ _ h2.1 (h2.2.1 t).1 (h2.2.1 t).2

theorem rowMat_base (h2 : X.H2 cr b) : X.rowMat cr b Bs.μ0 = 1 := by
  rw [rowMat, rowMatC, relMat_self _ h2.1, kMat_one]

theorem eW_inj (he : X.EWnorm b) (hn : 0 < X.nP b) (j : Bs.J) : Function.Injective (X.eW b j) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h1 := he j x x
  rw [hx, inner_zero_left] at h1
  have hn' : ((X.nP b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact inner_self_eq_zero.1 ((mul_eq_zero.1 h1.symm).resolve_left hn')

theorem principal_form_injective (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (j : Bs.J) :
    Function.Injective (X.w0C b j) := by
  rw [w0C, LinearMap.coe_comp]
  exact (X.eW_inj b he hn j).comp (lin_injective (hk j Bs.v0).1)

theorem key_lift (h5 : X.H5 cr b) (hr : X.RATth cr b) (j : Bs.J) (t : Bs.Tup)
    (x : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.w0C b j (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec x)) = X.tC cr b j t (cpt Bs.v0.embedding x) := by
  rw [cpt_mulVec, liftMat, kMat_map _ (hr j t), liftMatC]
  exact relMat_spec _ _ (fun k => (h5 j t).2 ▸ LinearMap.mem_range_self _ _) _

theorem liftMat_bij (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (h5 : X.H5 cr b) (hr : X.RATth cr b)
    (j : Bs.J) (t : Bs.Tup) :
    Function.Bijective (X.liftMat cr b j t).mulVec := by
  refine bij_of_map Bs.v0.embedding _ ?_
  rw [liftMat, kMat_map _ (hr j t), liftMatC]
  exact relMat_bij _ _ (X.principal_form_injective b hk he hn j) (h5 j t).1 (h5 j t).2

theorem gramE_unit (h2 : X.H2 cr b) (hn : 0 < X.nP b) : IsUnit (frameOf (X.gramE cr b)).det := by
  have hli : LinearIndependent ℂ fun i => X.iC cr b Bs.μ0 (Pi.single i 1) := by
    apply li_of_lin_injective
    rw [lin_basis]
    exact h2.1
  exact frame_gram_smul_unit _ hli _ (inv_pos.2 hn)

variable {Y : CxCol (fc := fc) X} {C CH : ℝ}

theorem XE_spec (hL : X.CxLinks cr Y C CH) (hW : ∀ b, (lv (fc X.zs) b).WF) :
    (∀ v, IsUnit (X.XE cr b v).det) ∧ X.XE cr b Bs.v0 = frameOf (X.gramE cr b) := by
  classical
  have hi := (hW b).Qp_indep
  have ht := (hW b).Qp_top
  have hsum : ∑ q, partPr (lv (fc X.zs) b) Bs.μ0 q = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun z => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.sum_mulVec, Matrix.one_mulVec]
    exact sum_partPr_mulVec _ Bs.μ0 hi ht z
  have hdet : ∀ v, IsUnit (((lv (fc X.zs) b).XQ Bs.μ0) v).det := fun v => ((hW b).XQ_quot Bs.μ0 v).1
  refine ⟨fun v => ?_, ?_⟩
  · by_cases hv : v = Bs.v0
    · subst hv
      simp only [XE, rowXE, rowFrame, spliceFrame, Function.update_self]
      exact X.gramE_unit cr b (hL.h2 b) (hL.h4pos.2.2 b)
    · have h := (weightFrameSpec K _ Bs.Ix (partPr (lv (fc X.zs) b) Bs.μ0)
        (fun p v => X.κ v * ∏ j, X.lam j Bs.μ0 p v) ((lv (fc X.zs) b).XQ Bs.μ0) hdet
        (fun p v => mul_pos (hL.h4pos.1 v) (Finset.prod_pos fun j _ => hL.h4pos.2.1 j Bs.μ0 p v)) hsum v).1
      simpa [XE, rowXE, rowFrame, spliceFrame, pushFrame, Function.update_of_ne hv] using h
  · simp [XE, rowXE, rowFrame, spliceFrame]

theorem scal_rows (hL : X.CxLinks cr Y C CH) (hW : ∀ b, (lv (fc X.zs) b).WF) (t : Bs.Tup) (v : InfinitePlace K)
    (htv : t = Bs.μ0 ∨ v = Bs.v0) (p : Bs.Ix) :
    IsScalarOn ((lv (fc X.zs) b).XQ t) (X.data cr b).XE v ((X.data cr b).ι t) ((X.data cr b).Qpart t p)
      ((X.data cr b).κ v * ∏ j, (X.data cr b).lam j t p v) := by
  classical
  intro x hx y
  show Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0))) (X.XE cr b) v
      ((X.rowMat cr b t).mulVec x) ((X.rowMat cr b t).mulVec y) =
    (((X.κ v * ∏ j, X.lam j t p v : ℝ)) : ℂ) *
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ t))) ((lv (fc X.zs) b).XQ t) v x y
  have hxE : (X.rowMat cr b t).mulVec x ∈ X.Ep cr b p := hx
  by_cases hv : v = Bs.v0
  · subst hv
    have hli : LinearIndependent ℂ fun i => X.iC cr b Bs.μ0 (Pi.single i 1) := by
      apply li_of_lin_injective
      rw [lin_basis]
      exact (hL.h2 b).1
    have hX0 : X.XE cr b Bs.v0 = frameOf ((((X.nP b)⁻¹ : ℝ) : ℂ) •
        Matrix.gram ℂ fun i => X.iC cr b Bs.μ0 (Pi.single i 1)) := (X.XE_spec cr b hL hW).2
    rw [majAt_gram_smul _ _ _ hli _ (inv_pos.2 (hL.h4pos.2.2 b)) hX0, lin_basis,
      key_row X cr b (hL.h2 b) (hL.ratMu b), key_row X cr b (hL.h2 b) (hL.ratMu b)]
    have hin : X.iC cr b t (cpt Bs.v0.embedding x) ∈ X.EEp p := by
      rw [← key_row X cr b (hL.h2 b) (hL.ratMu b)]
      exact (mem_Ep X cr b p _).1 hxE
    rw [(hL.h4 b) t p x hin y]
    have hn' : ((X.nP b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hL.h4pos.2.2 b).ne'
    push_cast
    field_simp
  · have ht : t = Bs.μ0 := htv.resolve_right hv
    subst ht
    rw [X.rowMat_base cr b (hL.h2 b)] at hxE ⊢
    rw [Matrix.one_mulVec, Matrix.one_mulVec]
    rw [Matrix.one_mulVec] at hxE
    have hxQ : x ∈ (lv (fc X.zs) b).Qp Bs.μ0 p := ((hL.h3 b) p x).2 ((mem_Ep X cr b p x).1 hxE)
    exact rowXE_part (lv (fc X.zs) b) (hW b) (frameOf (X.gramE cr b)) (X.gramE_unit cr b (hL.h2 b) (hL.h4pos.2.2 b))
      X.κ hL.h4pos.1 (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hL.h4pos.2.1 j Bs.μ0 p v) v hv
      (hL.partsOrth b v hv) p x hxQ y

theorem scal_lifts (hL : X.CxLinks cr Y C CH) (j : Bs.J) (t : Bs.Tup) (v : InfinitePlace K)
    (htv : t = Bs.μ0 ∨ v = Bs.v0) (p : Bs.Ix) :
    IsScalarOn ((lv (fc X.zs) b).XT j t) ((X.data cr b).XW j) v ((X.data cr b).θ j t) ((X.data cr b).Zpart j t p)
      ((X.data cr b).lam j t p v) := by
  classical
  intro x hx y
  show Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (X.dW b j))) (X.XW b j) v
      ((X.liftMat cr b j t).mulVec x) ((X.liftMat cr b j t).mulVec y) =
    ((X.lam j t p v : ℝ) : ℂ) *
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin ((lv (fc X.zs) b).dZ j t))) ((lv (fc X.zs) b).XT j t) v x y
  have hxW : (X.liftMat cr b j t).mulVec x ∈ X.WpK b j p := hx
  have hin : X.tC cr b j t (cpt Bs.v0.embedding x) ∈ X.Wp j p := by
    rw [← key_lift X cr b (hL.h5 b) (hL.ratTh b)]
    exact (mem_WpK X b j p _).1 hxW
  by_cases hv : v = Bs.v0
  · subst hv
    have hX0 : X.XW b j Bs.v0 = frameOf (Matrix.gram ℂ (X.bW b j Bs.v0)) := rfl
    rw [majAt_gram _ _ _ ((hL.kForm b) j Bs.v0).1 hX0]
    have hw : ∀ z, lin (X.bW b j Bs.v0) z = X.wC b j Bs.v0 z := fun z => rfl
    rw [hw, hw]
    have hE := (hL.ewNorm b) j (X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec x)))
      (X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec y)))
    have hw0 : ∀ z, X.eW b j (X.wC b j Bs.v0 z) = X.w0C b j z := fun z => rfl
    rw [hw0, hw0, key_lift X cr b (hL.h5 b) (hL.ratTh b), key_lift X cr b (hL.h5 b) (hL.ratTh b),
      (hL.thmA b) j t p x hin y] at hE
    have hn' : ((X.nP b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hL.h4pos.2.2 b).ne'
    push_cast at hE ⊢
    apply mul_left_cancel₀ hn'
    rw [← hE]
    ring
  · have ht : t = Bs.μ0 := htv.resolve_right hv
    subst ht
    have hX0 : X.XW b j v = frameOf (Matrix.gram ℂ (X.bW b j v)) := rfl
    rw [majAt_gram _ _ _ ((hL.kForm b) j v).1 hX0]
    exact (hL.galD b) j v hv p x hin y

def rowsOf (hL : X.CxLinks cr Y C CH) (hW : ∀ b, (lv (fc X.zs) b).WF) : IndefRows (lv (fc X.zs) b) where
  toIndefData := X.data cr b
  pos := hL.pos b
  proviso := hL.proviso b
  types := hL.types b
  h0 := hL.h0
  frames := ⟨(X.XE_spec cr b hL hW).1, fun j v => frame_gram_unit _ ((hL.kForm b) j v).1, hL.mLat b⟩
  l1a := by
    refine ⟨fun p => ?_, fun j p => ?_⟩
    · change ((lv (fc X.zs) b).Qp Bs.μ0 p).map (X.rowMat cr b Bs.μ0).mulVecLin = X.Ep cr b p
      rw [X.rowMat_base cr b (hL.h2 b), Matrix.mulVecLin_one, Submodule.map_id]
      ext x
      rw [mem_Ep]
      exact (hL.h3 b) p x
    · change ((lv (fc X.zs) b).Zp j Bs.μ0 p).map (X.liftMat cr b j Bs.μ0).mulVecLin = X.WpK b j p
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Matrix.mulVecLin_apply, mem_WpK, key_lift X cr b (hL.h5 b) (hL.ratTh b)]
        exact ((hL.h3W b) j p x).1 hx
      · intro hy
        obtain ⟨x, rfl⟩ := (X.liftMat_bij cr b (hL.kForm b) (hL.ewNorm b) (hL.h4pos.2.2 b) (hL.h5 b) (hL.ratTh b) j Bs.μ0).2 y
        refine ⟨x, ?_, rfl⟩
        rw [mem_WpK, key_lift X cr b (hL.h5 b) (hL.ratTh b)] at hy
        exact ((hL.h3W b) j p x).2 hy
  l1c := ⟨fun t => X.rowMat_bij cr b (hL.h2 b) (hL.ratMu b) t,
    fun j t => X.liftMat_bij cr b (hL.kForm b) (hL.ewNorm b) (hL.h4pos.2.2 b) (hL.h5 b) (hL.ratTh b) j t, hL.h4pos.1,
    fun j t p v => hL.h4pos.2.1 j t p v, fun t v htv p => X.scal_rows cr b hL hW t v htv p,
    fun j t v htv p => X.scal_lifts cr b hL j t v htv p⟩
  l1d := hL.l1d b

end CxData

def cxPkg {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (X : CxData A)
    (Y : CxData.CxCol (fc := fc) X) (C CH : ℝ) (hL : X.CxLinks cr Y C CH) (hW : ∀ b, (lv (fc X.zs) b).WF) :
    IndefPkg A fc C CH :=
  { Zs := X.zs
    stable := hL.stable
    inBlock := hL.inBlock
    core :=
      { base := { toIndefRows := X.rowsOf cr false hL hW, l3 := hL.l3, on := hL.on }
        cols := { toIndefRows := X.rowsOf cr true hL hW, l6 := hL.l6, col := X.colOf cr Y, l1b := hL.l1b,
                  l1e := hL.l1e }
        extra := { untw := hL.untw, level := ⟨rfl, rfl, rfl⟩, passage := hL.passage, fun0 := hL.fun0 } } }

theorem cxPkg_spec {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (X : CxData A)
    (Y : CxData.CxCol (fc := fc) X) (C CH : ℝ) (hL : X.CxLinks cr Y C CH) (hW : ∀ b, (lv (fc X.zs) b).WF) :
    (cxPkg cr X Y C CH hL hW).Zs = X.zs ∧ (cxPkg cr X Y C CH hL hW).core.base.toIndefData = X.data cr false ∧
      (cxPkg cr X Y C CH hL hW).core.cols.toIndefData = X.data cr true ∧
      (cxPkg cr X Y C CH hL hW).core.cols.col = X.colOf cr Y ∧ (cxPkg cr X Y C CH hL hW).core.base.μ = X.μ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cxToPkg {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (X : CxData A)
    (Y : CxData.CxCol (fc := fc) X) (C CH : ℝ) (hL : X.CxLinks cr Y C CH) (hW : ∀ b, (lv (fc X.zs) b).WF) :
    Nonempty (IndefPkg A fc C CH) := ⟨cxPkg cr X Y C CH hL hW⟩

theorem cx_exists_Q {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (X : CxData A)
    (Y : CxData.CxCol (fc := fc) X) (C CH : ℝ) (hL : X.CxLinks cr Y C CH) (hW : ∀ b, (lv (fc X.zs) b).WF)
    (Q : DefSub A → (HeightOneSpectrum (𝓞 K) → Bs.Tup) → Prop) (hQ : Q X.zs X.μ) :
    ∃ P : IndefPkg A fc C CH, Q P.Zs P.core.base.μ := by
  exact ⟨cxPkg cr X Y C CH hL hW, hQ⟩

end Formalism.IndefR.Cx
