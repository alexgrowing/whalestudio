import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.LocFlagPf

def vm {K L : Type} [Field K] [Field L] (ι : K →+* L) {n : ℕ} (x : Fin n → K) : Fin n → L := fun i => ι (x i)

theorem exists_ginv {K : Type} [Field K] {k n : ℕ} (A : Matrix (Fin k) (Fin n) K) :
    ∃ B : Matrix (Fin n) (Fin k) K, A * B * A = A := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective A.mulVecLin.rangeRestrict
    (LinearMap.range_rangeRestrict _)
  obtain ⟨h, hh⟩ := LinearMap.exists_extend g
  refine ⟨LinearMap.toMatrix' h, ?_⟩
  apply Matrix.mulVec_injective
  funext z
  have hz : A *ᵥ z ∈ LinearMap.range A.mulVecLin := ⟨z, rfl⟩
  have h1 : h (A *ᵥ z) = g ⟨A *ᵥ z, hz⟩ := LinearMap.congr_fun hh ⟨A *ᵥ z, hz⟩
  have h2 : A *ᵥ g ⟨A *ᵥ z, hz⟩ = A *ᵥ z :=
    congrArg Subtype.val (LinearMap.congr_fun hg ⟨A *ᵥ z, hz⟩)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, h1, h2]

theorem ker_base {K L : Type} [Field K] [Field L] (ι : K →+* L) {k n : ℕ} (A : Matrix (Fin k) (Fin n) K)
    (z : Fin n → L) (hz : A.map ι *ᵥ z = 0) : z ∈ Submodule.span L (vm ι '' {x | A *ᵥ x = 0}) := by
  obtain ⟨B, hB⟩ := exists_ginv A
  have hAP : A * (1 - B * A) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hB, sub_self]
  have hP : (1 - B * A).map ι = 1 - B.map ι * A.map ι := by
    ext i j
    simp [Matrix.one_apply, Matrix.mul_apply, apply_ite ι]
  have e : z = (1 - B * A).map ι *ᵥ z := by
    rw [hP, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, sub_zero]
  rw [e, Matrix.mulVec_eq_sum]
  simp only [op_smul_eq_smul]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨fun i => (1 - B * A : Matrix (Fin n) (Fin n) K) i j, ?_, ?_⟩
  · funext i
    exact congrFun (congrFun hAP i) j
  · rfl

theorem mem_perp_span {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (S : Set (Fin n → K)) (y : Fin n → K) :
    y ∈ perp σ (Submodule.span K S) ↔ ∀ x ∈ S, ∑ i, σ (x i) * y i = 0 := by
  refine ⟨fun h x hx => h x (Submodule.subset_span hx), fun h x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add a b _ _ ha hb => simp [add_mul, Finset.sum_add_distrib, ha, hb]
  | smul c a _ ha =>
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum, ha, mul_zero]

theorem span_cols {E : Type} [Field E] [NumberField E] {n : ℕ} (W : Submodule E (Fin n → E)) :
    W = Submodule.span E (Set.range fun j => (Module.finBasis E W j : Fin n → E)) := by
  have h := congrArg (Submodule.map W.subtype) (Module.finBasis E W).span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
  exact h.symm

section Place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem emb_conj (v : InfinitePlace E) (x : E) : v.embedding (conjE E x) = starRingEnd ℂ (v.embedding x) :=
  IsCMField.complexEmbedding_complexConj E v.embedding x

theorem locSub_eq (v : InfinitePlace E) (W : Submodule E (Fin n → E)) :
    locSub v W = Submodule.span ℂ (vm v.embedding '' (W : Set (Fin n → E))) := rfl

theorem vm_mem (v : InfinitePlace E) {W : Submodule E (Fin n → E)} {x : Fin n → E} (hx : x ∈ W) :
    vm v.embedding x ∈ locSub v W := Submodule.subset_span ⟨x, hx, rfl⟩

theorem locSub_mono (v : InfinitePlace E) {W W' : Submodule E (Fin n → E)} (h : W ≤ W') : locSub v W ≤ locSub v W' :=
  Submodule.span_mono (Set.image_mono h)

theorem locSub_span (v : InfinitePlace E) (S : Set (Fin n → E)) :
    locSub v (Submodule.span E S) = Submodule.span ℂ (vm v.embedding '' S) := by
  have key : ∀ x ∈ Submodule.span E S, vm v.embedding x ∈ Submodule.span ℂ (vm v.embedding '' S) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : vm v.embedding (0 : Fin n → E) = 0 := by funext i; simp [vm]
      rw [this]; exact zero_mem _
    | add a b _ _ ha hb =>
      have : vm v.embedding (a + b) = vm v.embedding a + vm v.embedding b := by funext i; simp [vm]
      rw [this]; exact add_mem ha hb
    | smul c a _ ha =>
      have : vm v.embedding (c • a) = v.embedding c • vm v.embedding a := by funext i; simp [vm]
      rw [this]; exact Submodule.smul_mem _ _ ha
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  exact key x hx

theorem locGL_val (v : InfinitePlace E) (d : GL (Fin n) E) :
    (PositivityTheory.Rg.BcB.D4.locGL v d).val = d.val.map v.embedding := rfl

theorem locSub_img (v : InfinitePlace E) (d : GL (Fin n) E) (U : Submodule E (Fin n → E)) :
    locSub v (img d U) = img (PositivityTheory.Rg.BcB.D4.locGL v d) (locSub v U) := by
  rw [img, img, locSub_eq, locSub_eq, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  funext i
  simp only [vm, Matrix.toLin'_apply, locGL_val]
  exact RingHom.map_mulVec v.embedding d.val x i

theorem locSub_perp (v : InfinitePlace E) (W : Submodule E (Fin n → E)) :
    perp (starRingEnd ℂ) (locSub v W) = locSub v (perp (conjE E) W) := by
  refine le_antisymm (fun z hz => ?_) ?_
  · have hz' := (mem_perp_span _ _ z).1 hz
    let M : Matrix (Fin n) (Fin (Module.finrank E W)) E := basisMat W
    have hk := ker_base v.embedding (M.map (conjE E))ᵀ z (by
      funext j
      have := hz' _ ⟨_, (Module.finBasis E W j).2, rfl⟩
      simpa [Matrix.mulVec, dotProduct, M, basisMat, vm, emb_conj] using this)
    refine Submodule.span_mono (Set.image_mono fun x hx => ?_) hk
    rw [span_cols W]
    refine (mem_perp_span _ _ x).2 ?_
    rintro _ ⟨j, rfl⟩
    simpa [Matrix.mulVec, dotProduct, M, basisMat] using congrFun hx j
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    refine (mem_perp_span _ _ _).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have := congrArg v.embedding (hy x hx)
    simpa [vm, emb_conj] using this

theorem locSub_perpD (v : InfinitePlace E) (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) :
    perpD (starRingEnd ℂ) (PositivityTheory.Rg.BcB.D4.locGL v d) (locSub v W) = locSub v (perpD (conjE E) d W) := by
  rw [perpD, perpD, locSub_img, locSub_perp]

end Place

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n k : ℕ}

theorem cV_alg (v : InfinitePlace E) (x : E) : cV v (algebraMap E (GlobalTheory.CuspRep.Ad E) x) = v.embedding x :=
  GlobalTheory.CuspRep.pInf_algebraMap x v

theorem map_cV_infGL (v : InfinitePlace E) (u : GL (Fin n) (GlobalTheory.CuspRep.Cinf E)) :
    GeneralLinearGroup.map (cV v) (GlobalTheory.CuspRep.infGL E n u) =
      GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) u := by
  ext i j
  exact congrArg (fun w : GL (Fin n) (GlobalTheory.CuspRep.Cinf E) => (w.val i j) v) (GlobalTheory.CuspRep.pInf_infGL (E := E) u)

theorem map_cV_embInf (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cV v) (embInf n v y) = y := by
  classical
  rw [embInf, MonoidHom.comp_apply, map_cV_infGL]
  ext i j
  change ((Pi.mulSingle v y : InfinitePlace E → GL (Fin n) ℂ) v).val i j = y.val i j
  rw [Pi.mulSingle_eq_same]

theorem det_one_add_of_sq (N : Matrix (Fin k) (Fin k) ℂ) (hN : N * N = 0) : (1 + N).det = 1 := by
  have hM : IsNilpotent (-N) := ⟨2, by simp [pow_two, hN]⟩
  have hu := Matrix.isUnit_charpolyRev_of_isNilpotent hM
  obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp hu
  have h0 : r = 1 := by
    have h := Matrix.eval_charpolyRev (M := -N)
    rw [← hr, Polynomial.eval_C] at h
    exact h
  have hrev : (-N).charpolyRev = 1 := by rw [← hr, h0, Polynomial.C_1]
  have key : Polynomial.eval 1 (-N).charpolyRev = (1 + N).det := by
    rw [Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [← key, hrev, Polynomial.eval_one]

theorem gram_det (A : Matrix (Fin n) (Fin n) ℂ) (M : Matrix (Fin n) (Fin k) ℂ) (S : Matrix (Fin k) (Fin k) ℂ)
    (hS : S.det = 1) : ((A * (M * S))ᴴ * (A * (M * S))).det = ((A * M)ᴴ * (A * M)).det := by
  have e : (A * (M * S))ᴴ * (A * (M * S)) = Sᴴ * ((A * M)ᴴ * (A * M)) * S := by
    rw [← Matrix.mul_assoc A M S, Matrix.conjTranspose_mul (A * M) S]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hS]
  simp

theorem inv_mul_frame (M : Matrix (Fin n) (Fin k) ℂ) (L : Matrix (Fin k) (Fin n) ℂ) (hLM : L * M = 1)
    (X Yi : Matrix (Fin n) (Fin n) ℂ) (N : Matrix (Fin k) (Fin k) ℂ) (hY : Yi * (1 + X) = 1)
    (hXM : X * M = M * N) (hXX : X * (X * M) = 0) : N * N = 0 ∧ Yi * M = M * (1 + -N) := by
  have hNN : N * N = 0 := by
    have h1 : M * (N * N) = 0 := by
      rw [← Matrix.mul_assoc, ← hXM, Matrix.mul_assoc, ← hXM, hXX]
    calc N * N = (L * M) * (N * N) := by rw [hLM, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
  refine ⟨hNN, ?_⟩
  have h2 : (1 + X) * M = M * (1 + N) := by
    rw [Matrix.add_mul, Matrix.one_mul, hXM, Matrix.mul_add, Matrix.mul_one]
  have h3 : Yi * M * (1 + N) = M := by
    rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, hY, Matrix.one_mul]
  have h4 : (1 + N) * (1 + -N) = 1 := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_neg, hNN]
    simp
  calc Yi * M = Yi * M * ((1 + N) * (1 + -N)) := by rw [h4, Matrix.mul_one]
    _ = M * (1 + -N) := by rw [← Matrix.mul_assoc, h3]

theorem frame_map (v : InfinitePlace E) (x : GlobalTheory.CuspRep.GA E n) (M : Matrix (Fin n) (Fin k) E) :
    (frame x M).map (cV v) = ((GeneralLinearGroup.map (cV v) x)⁻¹ : GL (Fin n) ℂ).val * M.map v.embedding := by
  have h : (M.map (algebraMap E (GlobalTheory.CuspRep.Ad E))).map (cV v) = M.map v.embedding := by
    ext i j
    exact cV_alg v (M i j)
  rw [frame, Matrix.map_mul, h, ← map_inv]
  rfl

theorem exists_left (v : InfinitePlace E) (W : Submodule E (Fin n → E)) :
    ∃ L : Matrix (Fin (Module.finrank E W)) (Fin n) ℂ, L * (basisMat W).map v.embedding = 1 := by
  obtain ⟨B, hB⟩ := exists_ginv (basisMat W)
  have hinj : Function.Injective (basisMat W).mulVec := by
    refine Matrix.mulVec_injective_iff.2 ?_
    exact (Module.finBasis E W).linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hBM : B * basisMat W = 1 := by
    apply Matrix.mulVec_injective
    funext c
    apply hinj
    rw [Matrix.one_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hB]
  refine ⟨B.map v.embedding, ?_⟩
  rw [← Matrix.map_mul, hBM, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_coords (v : InfinitePlace E) (W : Submodule E (Fin n → E)) (z : Fin n → ℂ) (hz : z ∈ locSub v W) :
    ∃ c, z = (basisMat W).map v.embedding *ᵥ c := by
  have h : z ∈ locSub v (Submodule.span E (Set.range fun j => (Module.finBasis E W j : Fin n → E))) := by
    rw [← span_cols W]; exact hz
  rw [locSub_span, ← Set.range_comp, Submodule.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, rfl⟩ := h
  refine ⟨c, ?_⟩
  funext i
  simp [Matrix.mulVec, dotProduct, basisMat, vm, mul_comm]

theorem logn_flag (v : InfinitePlace E) (W W₂ W' : Submodule E (Fin n → E)) (x : GlobalTheory.CuspRep.GA E n)
    (y : GL (Fin n) ℂ) (hX : y.val - 1 ∈ nilrad (locSub v W) (locSub v W₂))
    (hW' : W' ≤ W ∨ (W ≤ W' ∧ W' ≤ W₂)) :
    lognInf v (frame (embInf n v y * x) (basisMat W')) = lognInf v (frame x (basisMat W')) := by
  obtain ⟨L, hL⟩ := exists_left v W'
  set M := (basisMat W').map v.embedding with hM
  set X := y.val - 1 with hXdef
  have cols : ∀ j, (fun i => M i j) ∈ locSub v W' := fun j => vm_mem v (Module.finBasis E W' j).2
  have colmul : ∀ (T : Matrix (Fin n) (Fin n) ℂ) j i, (T * M) i j = (T *ᵥ fun l => M l j) i := fun _ _ _ => rfl
  obtain ⟨N, hXM, hXX⟩ : ∃ N : Matrix (Fin (Module.finrank E W')) (Fin (Module.finrank E W')) ℂ,
      X * M = M * N ∧ X * (X * M) = 0 := by
    rcases hW' with h | ⟨h1, h2⟩
    · have h0 : X * M = 0 := by
        ext i j
        rw [colmul, hX.2.2 _ (locSub_mono v h (cols j))]
        rfl
      exact ⟨0, by rw [h0, Matrix.mul_zero], by rw [h0, Matrix.mul_zero]⟩
    · have hc : ∀ j, ∃ c, (X *ᵥ fun l => M l j) = M *ᵥ c := fun j =>
        exists_coords v W' _ (locSub_mono v h1 (hX.2.1 _ (locSub_mono v h2 (cols j))))
      choose c hc using hc
      refine ⟨Matrix.of fun i j => c j i, ?_, ?_⟩
      · ext i j
        rw [colmul, hc j]
        rfl
      · ext i j
        have h3 : X *ᵥ (X *ᵥ fun l => M l j) = 0 := hX.2.2 _ (hX.2.1 _ (locSub_mono v h2 (cols j)))
        exact congrFun h3 i
  have hY : (y⁻¹ : GL (Fin n) ℂ).val * (1 + X) = 1 := by
    rw [hXdef, add_sub_cancel, Units.inv_mul]
  obtain ⟨hNN, hYM⟩ := inv_mul_frame M L hL X _ N hY hXM hXX
  have hdet : (1 + -N).det = 1 := det_one_add_of_sq (-N) (by simpa using hNN)
  have hinv : ((GeneralLinearGroup.map (cV v) (embInf n v y * x))⁻¹ : GL (Fin n) ℂ).val =
      ((GeneralLinearGroup.map (cV v) x)⁻¹ : GL (Fin n) ℂ).val * (y⁻¹ : GL (Fin n) ℂ).val := by
    rw [map_mul, map_cV_embInf, _root_.mul_inv_rev, Units.val_mul]
  simp only [lognInf]
  rw [frame_map, frame_map, hinv, ← hM, Matrix.mul_assoc, hYM, gram_det _ _ _ hdet]

end Frame

theorem locFlag : LocFlag := by
  intro E _ _ _ n d W v hI hW hpp
  refine ⟨?_, locSub_mono v hI.2, locSub_perpD v d W, ?_, ?_⟩
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    intro hbot
    have h1 : vm v.embedding w = 0 := by
      have := vm_mem v hw
      rwa [hbot, Submodule.mem_bot] at this
    refine hw0 (funext fun i => ?_)
    exact v.embedding.injective ((congrFun h1 i).trans (map_zero _).symm)
  · rw [locSub_perpD, hpp]
  · intro x y hy W' hW'
    exact logn_flag v W _ W' x y hy hW'

end GlobalTheory.CompanionTheory.LocFlagPf
