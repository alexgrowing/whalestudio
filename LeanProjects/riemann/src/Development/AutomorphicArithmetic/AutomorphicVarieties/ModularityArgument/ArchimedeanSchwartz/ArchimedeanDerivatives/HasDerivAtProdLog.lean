import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ShiftOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.IsRegConj

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep
open scoped ContDiff

namespace UpperTheory.V.Z.Inf

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ}

private theorem prod_coord (d : Cinf K) : ∏ σ : K →+* ℂ, coord σ d = ((∏ w, ‖d w‖ ^ 2 : ℝ) : ℂ) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ (fun σ : K →+* ℂ => InfinitePlace.mk σ), Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
      (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))
  have hf : (Finset.univ.filter fun σ : K →+* ℂ => InfinitePlace.mk σ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq σ with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; simp)
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding w
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.prod_pair hne, GlobalTheory.IsoPull.coord_conj, GlobalTheory.IsoPull.coord_embedding, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

private theorem nrm_eq (x : Lie K n) : ((nrm x : ℝ) : ℂ) = ∏ σ, detAt σ x := (prod_coord _).symm

omit [NumberField K] [IsTotallyComplex K] in
private theorem detAt_ne {x : Lie K n} (hx : x ∈ invSet K n) (σ : K →+* ℂ) : detAt σ x ≠ 0 :=
  (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (coord σ)).ne_zero

private theorem nrm_slit {x : Lie K n} (hx : x ∈ invSet K n) : ∏ σ, detAt σ x ∈ Complex.slitPlane := by
  have h0 : ((nrm x : ℝ) : ℂ) ≠ 0 := by
    rw [nrm_eq]; exact Finset.prod_ne_zero_iff.2 fun σ _ => detAt_ne hx σ
  have h1 : 0 ≤ nrm x := Finset.prod_nonneg fun w _ => by positivity
  rw [← nrm_eq]
  exact Complex.ofReal_mem_slitPlane.2 (lt_of_le_of_ne h1 fun h => h0 (by rw [← h]; simp))

private theorem wt_eq (u : ℂ) (e : (K →+* ℂ) → ℕ) :
    (wt u e : Lie K n → ℂ) = fun x => (∏ σ, detAt σ x) ^ u * ∏ σ, (detAt σ x)⁻¹ ^ e σ := by
  funext x; rw [wt, nrm_eq]

omit [IsTotallyComplex K] in
private theorem contDiff_detAt (σ : K →+* ℂ) : ContDiff ℝ ∞ (detAt σ : Lie K n → ℂ) := by
  let l : Cinf K →ₗ[ℝ] ℂ :=
    { toFun := coord σ, map_add' := map_add _, map_smul' := GlobalTheory.IsoPull.coord_smul σ }
  exact (LinearMap.toContinuousLinearMap l).contDiff.comp contDiff_det

private theorem contDiffAt_wt (u : ℂ) (e : (K →+* ℂ) → ℕ) {x : Lie K n} (hx : x ∈ invSet K n) :
    ContDiffAt ℝ ∞ (wt u e) x := by
  rw [wt_eq]
  refine ContDiffAt.mul ?_ (contDiffAt_prod fun σ _ => ((contDiff_detAt σ).contDiffAt.inv (detAt_ne hx σ)).pow _)
  have h1 : ContDiffAt ℂ ∞ (fun z : ℂ => z ^ u) (∏ σ, detAt σ x) :=
    (analyticAt_id.cpow analyticAt_const (nrm_slit hx)).contDiffAt
  exact (h1.restrict_scalars ℝ).comp x (f := fun x => ∏ σ, detAt σ x)
    (contDiffAt_prod fun σ _ => (contDiff_detAt σ).contDiffAt)

private theorem det_one_add_single {R : Type} [CommRing R] (a b : Fin n) (c : R) :
    (1 + Matrix.single a b c).det = 1 + if a = b then c else 0 := by
  have h : Matrix.single a b c = replicateCol Unit (Pi.single a c) * replicateRow Unit (Pi.single b (1 : R)) := by
    ext i j
    simp only [Matrix.single_apply, Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Pi.single_apply,
      Finset.univ_unique, Finset.sum_singleton]
    split_ifs <;> simp_all
  rw [h, det_one_add_replicateCol_mul_replicateRow]
  by_cases hab : a = b
  · subst hab; simp [dotProduct, Pi.single_apply]
  · simp [dotProduct, Pi.single_apply, hab]

omit [IsTotallyComplex K] in
private theorem detAt_line (σ : K →+* ℂ) (a b : Fin n) (c : Cinf K) (x : Lie K n) (s : ℝ) :
    detAt σ (x + s • rmul (toL (single a b c)) x) =
      detAt σ x * (1 + (s : ℂ) * if a = b then coord σ c else 0) := by
  have hm : Matrix.of (x + s • rmul (toL (single a b c)) x) = Matrix.of x * (1 + single a b (s • c)) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.smul_single, Matrix.mul_smul]
    rfl
  unfold detAt
  rw [hm, Matrix.det_mul, map_mul, det_one_add_single, map_add, map_one]
  split_ifs
  · rw [GlobalTheory.IsoPull.coord_smul, Complex.real_smul]
  · simp

private theorem hasDerivAt_prod_log {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ) (l : ι → ℂ) (z : ℂ)
    (h : ∀ i, HasDerivAt (f i) (l i * f i z) z) :
    HasDerivAt (fun s => ∏ i ∈ S, f i s) ((∑ i ∈ S, l i) * ∏ i ∈ S, f i z) z := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hasDerivAt_const z (1 : ℂ)
  | insert j S hj ih =>
    simp only [Finset.prod_insert hj, Finset.sum_insert hj]
    exact ((h j).fun_mul ih).congr_deriv (by ring)

private theorem hasDerivAt_k {ι : Type} [Fintype ι] (d c : ι → ℂ) (hd : ∀ i, d i ≠ 0) (hs : ∏ i, d i ∈ Complex.slitPlane)
    (u : ℂ) (e : ι → ℕ) :
    HasDerivAt (fun s : ℂ => (∏ i, d i * (1 + s * c i)) ^ u * ∏ i, (d i * (1 + s * c i))⁻¹ ^ e i)
      ((∑ i, (u - e i) * c i) * ((∏ i, d i) ^ u * ∏ i, (d i)⁻¹ ^ e i)) 0 := by
  have h1 : ∀ i, HasDerivAt (fun s : ℂ => d i * (1 + s * c i)) (c i * (d i * (1 + 0 * c i))) 0 := fun i =>
    ((((hasDerivAt_id (0 : ℂ)).mul_const (c i)).const_add 1).const_mul (d i)).congr_deriv (by ring)
  have h2 : ∀ i, HasDerivAt (fun s : ℂ => (d i * (1 + s * c i))⁻¹ ^ e i)
      ((-(e i : ℂ) * c i) * (d i * (1 + 0 * c i))⁻¹ ^ e i) 0 := fun i => by
    have hi := hd i
    refine (((h1 i).fun_inv (by simpa using hi)).fun_pow (e i)).congr_deriv ?_
    cases e i with
    | zero => simp
    | succ k => simp only [zero_mul, add_zero, mul_one, Nat.add_sub_cancel, pow_succ]; field_simp
  have h3 := (hasDerivAt_prod_log Finset.univ _ _ 0 h1).cpow_const (c := u) (by simpa using hs)
  have h4 := hasDerivAt_prod_log Finset.univ _ _ 0 h2
  refine (h3.fun_mul h4).congr_deriv ?_
  have hP := Complex.slitPlane_ne_zero hs
  simp only [zero_mul, add_zero, mul_one, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, neg_mul,
    Finset.sum_neg_distrib, Complex.cpow_sub _ _ hP, Complex.cpow_one]
  field_simp
  ring

private theorem fderiv_wt (u : ℂ) (e : (K →+* ℂ) → ℕ) (a b : Fin n) (c : Cinf K) {x : Lie K n} (hx : x ∈ invSet K n) :
    fderiv ℝ (wt u e) x (rmul (toL (single a b c)) x) =
      (∑ σ, (u - e σ) * if a = b then coord σ c else 0) * wt u e x := by
  obtain ⟨w, hw⟩ : ∃ w, w = rmul (toL (single a b c)) x := ⟨_, rfl⟩
  rw [← hw]
  have hd : DifferentiableAt ℝ (wt u e) x := (contDiffAt_wt u e hx).differentiableAt (by simp)
  have hline : HasDerivAt (fun s : ℝ => x + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have hd' : HasFDerivAt (wt u e) (fderiv ℝ (wt u e) x) ((fun s : ℝ => x + s • w) 0) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hline
  have h2 := hasDerivAt_k (fun σ => detAt σ x) (fun σ => if a = b then coord σ c else 0) (detAt_ne hx) (nrm_slit hx) u e
  have h3 := HasDerivAt.comp_ofReal (z := 0) h2
  have e1 : (wt u e ∘ fun s : ℝ => x + s • w) = fun s : ℝ =>
      (∏ σ, detAt σ x * (1 + (s : ℂ) * if a = b then coord σ c else 0)) ^ u *
        ∏ σ, (detAt σ x * (1 + (s : ℂ) * if a = b then coord σ c else 0))⁻¹ ^ e σ := by
    funext s
    simp only [Function.comp_apply, hw, wt_eq, detAt_line]
  rw [e1] at h1
  rw [h1.unique h3, wt_eq]

private theorem rd_wt (u : ℂ) (e : (K →+* ℂ) → ℕ) (τ : K →+* ℂ) (a b : Fin n) {x : Lie K n} (hx : x ∈ invSet K n) :
    rd τ a b (wt u e) x = (if a = b then u - e τ else 0) * wt u e x := by
  classical
  rw [rd, fderiv_wt u e a b _ hx, fderiv_wt u e a b _ hx]
  split_ifs with h
  · have : ∑ σ, (u - e σ) * ((1 / 2 : ℂ) * (coord σ (atEmb τ 1) - Complex.I * coord σ (atEmb τ Complex.I))) = u - e τ := by
      simp only [UpperTheory.V.WeylC.coord_hol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← this]
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun σ _ => by ring
  · simp

omit [IsTotallyComplex K] in
private theorem rd_congr (τ : K →+* ℂ) (a b : Fin n) {F G : Lie K n → ℂ} {x : Lie K n}
    (h : ∀ᶠ y in nhds x, F y = G y) : rd τ a b F x = rd τ a b G x := by
  unfold rd
  rw [Filter.EventuallyEq.fderiv_eq h]

private def chartL (g : GA K n) (x : Lie K n) : Sm K n →ₗ[ℂ] ℂ where
  toFun ψ := chart ψ.1 g x
  map_add' ψ ψ' := by unfold chart; split_ifs <;> simp
  map_smul' c ψ := by unfold chart; split_ifs <;> simp

private theorem chartL_apply (g : GA K n) (x : Lie K n) (ψ : Sm K n) : chartL g x ψ = chart ψ.1 g x := rfl

private theorem chart_Eop (τ : K →+* ℂ) (a b : Fin n) (ψ : Sm K n) (g : GA K n) {x : Lie K n} (hx : x ∈ invSet K n) :
    chart (Eop τ a b ψ).1 g x = rd τ a b (chart ψ.1 g) x := by
  have hE : Eop τ a b ψ = (1 / 2 : ℂ) • (lie K n (toL (single a b (atEmb τ 1))) ψ -
      Complex.I • lie K n (toL (single a b (atEmb τ Complex.I))) ψ) := rfl
  have hl : ∀ X, chartL g x (lie K n X ψ) = fderiv ℝ (chart ψ.1 g) x (rmul X x) := fun X => chart_lieD ψ.2 X g hx
  rw [← chartL_apply, hE, map_smul, map_sub, map_smul, hl, hl, rd, smul_eq_mul, smul_eq_mul]

private theorem rd_chart_wt (u : ℂ) (e : (K →+* ℂ) → ℕ) (τ : K →+* ℂ) (a b : Fin n)
    (ψ : Sm K n) (g : GA K n) {x : Lie K n} (hx : x ∈ invSet K n) :
    rd τ a b (fun y => chart ψ.1 g y * wt u e y) x =
      chart (Eop τ a b ψ).1 g x * wt u e x + (if a = b then u - e τ else 0) * (chart ψ.1 g x * wt u e x) := by
  have hc : DifferentiableAt ℝ (chart ψ.1 g) x := (contDiffAt_chart ψ.2 g hx).differentiableAt (by simp)
  have ho : DifferentiableAt ℝ (wt u e) x := (contDiffAt_wt u e hx).differentiableAt (by simp)
  have h : rd τ a b (fun y => chart ψ.1 g y * wt u e y) x =
      rd τ a b (chart ψ.1 g) x * wt u e x + chart ψ.1 g x * rd τ a b (wt u e) x := by
    unfold rd
    rw [fderiv_fun_mul hc ho]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [h, rd_wt u e τ a b hx, chart_Eop τ a b ψ g hx]
  ring

private theorem foldr_chart_wt (u : ℂ) (e : (K →+* ℂ) → ℕ) (τ : K →+* ℂ) (g : GA K n)
    (p : Equiv.Perm (Fin n)) (ψ : Sm K n) (l : List (Fin n)) :
    ∀ x ∈ invSet K n, l.foldr (fun j G y => rd τ (p j) j G y + (if p j = j then ((n - 1 - j.val : ℕ) : ℂ) else 0) * G y)
      (fun y => chart ψ.1 g y * wt u e y) x =
      chart ((l.map fun j : Fin n => Formalism.REAL.Tm (Eop τ) (u - e τ + n - 1 - ((j : ℕ) : ℂ)) (p j) j).prod ψ).1 g x *
        wt u e x := by
  induction l with
  | nil => intro x _; simp
  | cons j l ih =>
    intro x hx
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [rd_congr τ (p j) j (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) ih), rd_chart_wt u e τ _ _ _ g hx,
      ih x hx, Module.End.mul_apply]
    simp only [← chartL_apply, Formalism.REAL.Tm, LinearMap.add_apply, map_add]
    have hj : ((n - 1 - j.val : ℕ) : ℂ) = (n : ℂ) - 1 - (j.val : ℂ) := by
      have := j.isLt
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      simp
    by_cases hpj : p j = j
    · simp only [if_pos hpj, Module.algebraMap_end_apply, map_smul, smul_eq_mul, hj]
      ring
    · simp only [if_neg hpj, LinearMap.zero_apply, map_zero]
      ring

end UpperTheory.V.Z.Inf

open UpperTheory.V.Z.Inf in
theorem UpperTheory.V.Z.Inf.ptwOf :
    UpperTheory.V.Z.Inf.PtwOf := by
  intro hWeyl K _ _ _ n τ φ m hm g u e x hx
  have hs : ContDiffOn ℝ ∞ (fun y => chart φ.1 g y * wt u e y) (invSet K n) := fun y hy =>
    ((contDiffAt_chart φ.2 g hy).mul (contDiffAt_wt u e hy)).contDiffWithinAt
  have hW := hWeyl K n τ (invSet K n) isOpen_invSet _ hs x hx
  have hfold := fun p => foldr_chart_wt u e τ g p φ (List.finRange n) x hx
  simp only [hfold] at hW
  have hq : chart (Formalism.REAL.qdet (Eop τ) (u - e τ + n - 1) φ).1 g x =
      ∑ p : Equiv.Perm (Fin n), (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) *
        chart (((List.finRange n).map fun j : Fin n =>
          Formalism.REAL.Tm (Eop τ) (u - e τ + n - 1 - ((j : ℕ) : ℂ)) (p j) j).prod φ).1 g x := by
    simp only [← chartL_apply, Formalism.REAL.qdet, Formalism.REAL.qminor, LinearMap.sum_apply, map_sum,
      Module.End.mul_apply, Module.End.intCast_apply, map_zsmul, zsmul_eq_mul, List.ofFn_eq_map, id]
  have hcap : Formalism.REAL.qdet (Eop (a := n) τ) (u - e τ + n - 1) =
      (cap τ (u - e τ + ((n : ℂ) - 1) / 2) : Module.End ℂ (Sm K n)) := by
    change _ = Formalism.REAL.qdet (Eop (a := n) τ) (u - e τ + ((n : ℂ) - 1) / 2 + ((n : ℂ) - 1) / 2)
    congr 1
    ring
  rw [hcap, hm, ← chartL_apply, map_smul, chartL_apply, smul_eq_mul] at hq
  have hd := detAt_ne hx τ
  have hW' : detAt τ x * detD τ (fun y => chart φ.1 g y * wt u e y) x =
      (m.map (u - e τ + ((n : ℂ) - 1) / 2 + ·)).prod * chart φ.1 g x * wt u e x := by
    rw [hW, hq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  calc detD τ (fun y => chart φ.1 g y * wt u e y) x
      = (detAt τ x)⁻¹ * (detAt τ x * detD τ (fun y => chart φ.1 g y * wt u e y) x) := by
        field_simp
    _ = _ := by
        rw [hW']
        ring
