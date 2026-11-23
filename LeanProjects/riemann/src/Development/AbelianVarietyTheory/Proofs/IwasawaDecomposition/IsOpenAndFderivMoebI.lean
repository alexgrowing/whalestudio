import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.HodgeDomain.ActionDeriv

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domFlat : IsOpen (DomFlat ι p q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  have h : ∀ᶠ x in nhds x0, ∀ τ, (1 - (unflat x τ)ᴴ * unflat x τ).PosDef := by
    refine Filter.eventually_all.2 fun τ => ExhB.posDef_eventually _ (fun a b => ?_)
      (fun x => isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)) x0 (hx0 τ)
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, unflat, Matrix.of_apply]
    fun_prop
  exact h

theorem diffOn_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V} {n : ℕ}
    {M : V → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, ContDiffOn ℂ 1 (fun z => M z a b) s) :
    ContDiffOn ℂ 1 (fun z => (M z).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem diffOn_inv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V} {n : ℕ}
    {M : V → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, ContDiffOn ℂ 1 (fun z => M z a b) s)
    (hd : ∀ z ∈ s, (M z).det ≠ 0) (a b : Fin n) : ContDiffOn ℂ 1 (fun z => (M z)⁻¹ a b) s := by
  have hadj : ContDiffOn ℂ 1 (fun z => (M z).adjugate a b) s := by
    simp only [adjugate_apply]
    refine diffOn_det fun i j => ?_
    by_cases e : i = b
    · simp only [e, updateRow_self]; exact contDiffOn_const
    · simp only [updateRow_ne e]; exact h i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ContDiffOn.mul (ContDiffOn.inv (diffOn_det h) hd) hadj

theorem diffOn_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) :
    DifferentiableOn ℂ (fun v => flat (moebI g (unflat v))) (DomFlat ι p q) := by
  refine differentiableOn_pi.2 fun x => ?_
  obtain ⟨τ, a, b⟩ := x
  refine ContDiffOn.differentiableOn (n := 1) ?_ one_ne_zero
  have hinv : ∀ k, ContDiffOn ℂ 1 (fun v => (kapQ (g τ) (unflat v τ))⁻¹ k b) (DomFlat ι p q) := by
    intro k
    refine diffOn_inv (s := DomFlat ι p q) (M := fun v => kapQ (g τ) (unflat v τ)) (fun i j => ?_) (fun v hv => (kapQ_isUnit (hg τ (Set.mem_univ _)) (hv τ)).ne_zero) k b
    simp only [kapQ, Matrix.add_apply, Matrix.mul_apply, unflat, Matrix.of_apply]
    fun_prop
  simp only [flat, moebI, moeb, Matrix.mul_apply]
  refine ContDiffOn.sum fun k _ => ContDiffOn.mul ?_ (hinv k)
  simp only [Matrix.add_apply, Matrix.mul_apply, unflat, Matrix.of_apply]
  fun_prop

theorem hasDerivAt_affine {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) (Fin k) ℂ)
    (z ξ : Matrix (Fin n) (Fin k) ℂ) (a : Fin m) (b : Fin k) :
    HasDerivAt (fun t : ℂ => (A * (z + t • ξ) + B) a b) ((A * ξ) a b) 0 := by
  have e : (fun t : ℂ => (A * (z + t • ξ) + B) a b) = fun t => t * (A * ξ) a b + (A * z + B) a b := by
    funext t
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e]
  simpa using ((hasDerivAt_id (0 : ℂ)).mul_const ((A * ξ) a b)).add_const ((A * z + B) a b)

theorem fderiv_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : Pt ι p q} (hz : z ∈ DomI ι p q)
    (ξ : Pt ι p q) :
    fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) =
      flat (fun τ => tanAct (g τ) (z τ) (ξ τ)) := by
  have hz' : flat z ∈ DomFlat ι p q := hz
  have hn := isOpen_domFlat.mem_nhds hz'
  have hF := ((diffOn_moebI hg).differentiableAt hn).hasFDerivAt
  set D := fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) with hD
  have hc : HasDerivAt (fun t : ℂ => flat z + t • flat ξ) (flat ξ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (flat ξ)).const_add (flat z)
  have hW : HasDerivAt (fun t : ℂ => flat (moebI g (unflat (flat z + t • flat ξ)))) D 0 :=
    hF.comp_hasDerivAt_of_eq (0 : ℂ) hc (by simp)
  have hev : ∀ᶠ t : ℂ in nhds 0, flat z + t • flat ξ ∈ DomFlat ι p q :=
    hc.continuousAt.eventually_mem (by simpa using hn)
  funext x
  obtain ⟨τ, a, b⟩ := x
  have hgτ := hg τ (Set.mem_univ _)
  have key : unflat D τ * kapQ (g τ) (z τ) = jW (g τ) (z τ) * ξ τ := by
    rw [jW, Matrix.sub_mul, eq_sub_iff_add_eq, Matrix.mul_assoc]
    ext i j
    have h1 := hasDerivAt_affine (g τ).1.toBlocks₁₁ (g τ).1.toBlocks₁₂ (z τ) (ξ τ) i j
    have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hasDerivAt_pi.1 hW (τ, i, k)).mul (hasDerivAt_affine (g τ).1.toBlocks₂₁ (g τ).1.toBlocks₂₂ (z τ) (ξ τ) k j)
    have h3 := h2.congr_of_eventuallyEq (f₁ := fun t : ℂ =>
      ((g τ).1.toBlocks₁₁ * (z τ + t • ξ τ) + (g τ).1.toBlocks₁₂) i j) (by
        filter_upwards [hev] with t ht
        have := moeb_mul_kapQ hgτ (ht τ)
        exact (congrFun (congrFun this i) j).symm)
    rw [h1.unique h3, Finset.sum_add_distrib, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [zero_smul, add_zero]
    rfl
  have e : unflat D τ = tanAct (g τ) (z τ) (ξ τ) := by
    rw [tanAct, ← key, mul_nonsing_inv_cancel_right _ _ (kapQ_isUnit hgτ (hz τ))]
  exact congrFun (congrFun e a) b

theorem isOpen_and_fderiv_moebI : ∀ (ι : Type) [Fintype ι] (p q : ℕ), IsOpen (DomFlat ι p q) ∧ ∀ g ∈ UpqI ι p q, DifferentiableOn ℂ (fun v => flat (moebI g (unflat v))) (DomFlat ι p q) ∧ ∀ z ∈ DomI ι p q, ∀ ξ : Pt ι p q, fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) = flat (fun τ => tanAct (g τ) (z τ) (ξ τ)) :=
  fun _ _ _ _ => ⟨isOpen_domFlat, fun _ hg => ⟨diffOn_moebI hg, fun _ hz ξ => fderiv_moebI hg hz ξ⟩⟩

end GlobalTheory.HodgeDomain.ActionDeriv
