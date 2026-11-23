import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff

open Filter Topology

namespace GlobalTheory.ChernWeight

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type} [Fintype ι] {n : ℕ}

theorem adaptedGram_posDef {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ} {Y : Set E}
    {π : E → ι → ℂ} {A : E → Matrix (Fin n) (Fin n) ℂ} (hH : IsPosFrame U H)
    (hA : IsFlagFamily Y U π A) {y : E} (hy : y ∈ Y) : (adaptedGram H π A y).PosDef := by
  have h := hH.posDef _ (hA.mapsTo hy)
  have hu : IsUnit (A y)ᵀ := (isUnit_iff_isUnit_det _).2 (by rw [det_transpose]; exact hA.isUnit y hy)
  have e : (A y)ᵀᴴ = (A y)ᴴᵀ := by ext; rfl
  have := h.conjTranspose_mul_mul_same (B := (A y)ᵀᴴ) (mulVec_injective_iff_isUnit.2 hu.star)
  rw [conjTranspose_conjTranspose, e] at this
  exact this

theorem adaptedGram_smooth {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ} {Y : Set E}
    {π : E → ι → ℂ} {A : E → Matrix (Fin n) (Fin n) ℂ} (hH : IsPosFrame U H)
    (hA : IsFlagFamily Y U π A) {y : E} (hy : y ∈ Y) :
    MContDiffAt ∞ (fun x => adaptedGram H π A x) y := by
  have hA' : MContDiffAt ∞ A y := fun a b =>
    ((hA.hol_frame a b).contDiffAt (hA.isOpen.mem_nhds hy)).restrict_scalars ℝ
  have hπ : ContDiffAt ℝ ∞ π y :=
    (hA.hol_proj.contDiffAt (hA.isOpen.mem_nhds hy)).restrict_scalars ℝ
  have hHπ : MContDiffAt ∞ (fun x => H (π x)) y := fun a b =>
    ContDiffAt.comp (g := fun z => H z a b) y
      ((hH.smooth a b).contDiffAt (hH.isOpen.mem_nhds (hA.mapsTo hy))) hπ
  exact (hA'.transpose.mul hHπ).mul hA'.conjTranspose.transpose

theorem lineGram_pos {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ} {Y : Set E}
    {π : E → ι → ℂ} {A : E → Matrix (Fin n) (Fin n) ℂ} (hH : IsPosFrame U H)
    (hA : IsFlagFamily Y U π A) {y : E} (hy : y ∈ Y) (i : Fin n) :
    0 < (lineGram H π A i y () ()).re ∧
      lineGram H π A i y () () = ((lineGram H π A i y () ()).re : ℂ) := by
  have h := (posDef_gradedGram (adaptedGram_posDef hH hA hy) i).diag_pos (i := ())
  rw [Complex.lt_def] at h
  exact ⟨h.1, Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im]; exact h.2.symm)⟩

theorem lineGram_smooth {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ} {Y : Set E}
    {π : E → ι → ℂ} {A : E → Matrix (Fin n) (Fin n) ℂ} (hH : IsPosFrame U H)
    (hA : IsFlagFamily Y U π A) {y : E} (hy : y ∈ Y) (i : Fin n) :
    ContDiffAt ℝ 2 (fun x => (lineGram H π A i x () ()).re) y := by
  have hs : MContDiffAt 2 (fun x => stepGram (adaptedGram H π A x) i) y :=
    ((adaptedGram_smooth hH hA hy).of_le (by norm_cast)).submatrix _ _
  have hp : (stepGram (adaptedGram H π A y) i).PosDef := by
    refine (adaptedGram_posDef hH hA hy).submatrix ?_
    rintro (a | a) (b | b) hab
    · exact congrArg _ (Fin.castLE_injective i.2.le hab)
    · exact absurd (congrArg Fin.val hab) a.2.ne
    · exact absurd (congrArg Fin.val hab) b.2.ne'
    · rfl
  have hu : IsUnit (subGram (stepGram (adaptedGram H π A y) i)).det :=
    (isUnit_iff_isUnit_det _).1 (posDef_subGram hp).isUnit
  exact reCLM.contDiff.contDiffAt.comp y (hs.quotGram hu () ())

theorem sum_reindex (kap : ℂ) (lam : Fin n → ℝ) (c : Fin n → ℂ) (θ : Fin n → Fin n → ℂ) :
    -(kap * ∑ i, ((-lam i : ℝ) : ℂ) *
        -(c i - ∑ l ∈ Finset.Ioi i, θ l i + ∑ l ∈ Finset.Iio i, θ i l)) =
      kap * ∑ i, ∑ l ∈ Finset.Ioi i, ((lam i - lam l : ℝ) : ℂ) * θ l i +
        -(kap * ∑ i, (lam i : ℂ) * c i) := by
  have hre : ∑ i, (lam i : ℂ) * ∑ l ∈ Finset.Iio i, θ i l =
      ∑ i, ∑ l ∈ Finset.Ioi i, (lam l : ℂ) * θ l i := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm' fun i l => by simp [Finset.mem_Iio, Finset.mem_Ioi]
  have h1 : ∑ i, ((-lam i : ℝ) : ℂ) *
        -(c i - ∑ l ∈ Finset.Ioi i, θ l i + ∑ l ∈ Finset.Iio i, θ i l) =
      ∑ i, (lam i : ℂ) * c i - ∑ i, ∑ l ∈ Finset.Ioi i, (lam i : ℂ) * θ l i +
        ∑ i, (lam i : ℂ) * ∑ l ∈ Finset.Iio i, θ i l := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]; push_cast; ring
  have h2 : ∑ i, ∑ l ∈ Finset.Ioi i, ((lam i - lam l : ℝ) : ℂ) * θ l i =
      ∑ i, ∑ l ∈ Finset.Ioi i, (lam i : ℂ) * θ l i -
        ∑ i, ∑ l ∈ Finset.Ioi i, (lam l : ℂ) * θ l i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  rw [h1, h2, hre]; ring

theorem lineChern_weightNormSq : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y, (∀ i ξ η, curv (lineGram H π A i) y ξ η () () =
      curvDiag H π e i y ξ η - ∑ l ∈ Finset.Ioi i, thetaSq H π e l i y ξ η
        + ∑ l ∈ Finset.Iio i, thetaSq H π e i l y ξ η) →
    ∀ (lam : Fin n → ℝ) ξ η, lineChern (weightNormSq H π A lam) y ξ η =
      vertForm H π e lam y ξ η + horizForm H π e lam y ξ η := by
  intro E _ _ _ _ _ ι _ n U H Y π A e hH hA he y hy hcurv lam ξ η
  have hnY : Y ∈ 𝓝 y := hA.isOpen.mem_nhds hy
  have hp := fun i => lineGram_pos hH hA hy i
  have hfs := lineGram_smooth hH hA hy
  have hW : ContDiffAt ℝ 2 (weightNormSq H π A lam) y := by
    show ContDiffAt ℝ 2 (fun x => ∏ i, (lineGram H π A i x () ()).re ^ (-lam i)) y
    exact contDiffAt_prod fun i _ => (hfs i).rpow_const_of_ne (hp i).1.ne'
  have hW0 : weightNormSq H π A lam y ≠ 0 :=
    (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hp i).1 _).ne'
  have hlog : (fun x => Real.log (weightNormSq H π A lam x)) =ᶠ[𝓝 y]
      fun x => ∑ i, -lam i * Real.log ((lineGram H π A i x () ()).re) := by
    filter_upwards [hnY] with x hx
    rw [weightNormSq, Real.log_prod fun i _ =>
      (Real.rpow_pos_of_pos (lineGram_pos hH hA hx i).1 _).ne']
    exact Finset.sum_congr rfl fun i _ => Real.log_rpow (lineGram_pos hH hA hx i).1 _
  have hlogs : ∀ i, ContDiffAt ℝ 2 (fun x => Real.log ((lineGram H π A i x () ()).re)) y :=
    fun i => (hfs i).log (hp i).1.ne'
  have hlev : leviForm (fun x => Real.log (weightNormSq H π A lam x)) y ξ η =
      ∑ i, ((-lam i : ℝ) : ℂ) * leviForm (fun x => Real.log ((lineGram H π A i x () ()).re)) y ξ η := by
    rw [leviForm_congr hlog, leviForm_sum fun i _ => contDiffAt_const.mul (hlogs i),
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [leviForm_const_mul _ (hlogs i)]; rfl
  have hcv : ∀ i, leviForm (fun x => Real.log ((lineGram H π A i x () ()).re)) y ξ η =
      -curv (lineGram H π A i) y ξ η () () := fun i => by
    rw [curv_line (hfs i) (hp i).1.ne'
      (Filter.mem_of_superset hnY fun x hx => (lineGram_pos hH hA hx i).2) ξ η () (), neg_neg]
  have hlc : lineChern (weightNormSq H π A lam) y ξ η =
      -ddc (fun x => Real.log (weightNormSq H π A lam x)) y ξ η :=
    chernOne_line hW hW0 (Filter.Eventually.of_forall fun x => rfl) ξ η
  rw [hlc, ddc, hlev]
  simp only [hcv, hcurv]
  exact sum_reindex kappa lam (fun i => curvDiag H π e i y ξ η) (fun l i => thetaSq H π e l i y ξ η)

end GlobalTheory.ChernWeight
