import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.HalfOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KcDual
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.InvContDiffOn

noncomputable section

open Matrix Finset
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.LfSt.Kchain.KcHalf1

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hOf_single (i : Fin n × Fin n) : hOf (Pi.single i (1 : ℝ)) = hb i := by
  simp only [hOf]
  rw [Finset.sum_eq_single i]
  · simp
  · intro p _ hp
    simp [Pi.single_apply, hp]
  · simp

theorem herm_inv_conj {x H : Mat n} (hH : H.IsHermitian) : (x⁻¹ * H * xᴴ⁻¹).IsHermitian := by
  rw [← conjTranspose_nonsing_inv]
  exact isHermitian_mul_mul_conjTranspose _ hH

def phiL {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Fr k : Mat n → (V →L[ℂ] V)) (w : Mat n) :
    Mat n →ₗ[ℝ] (V →L[ℂ] V) where
  toFun X := fderiv ℝ Fr 1 X * k w + Ld X k w
  map_add' X Y := by
    simp only [Ld, map_add, add_mul, Matrix.add_mul, neg_add]
    abel
  map_smul' r X := by
    simp only [Ld, map_smul, smul_mul_assoc, Matrix.smul_mul, RingHom.id_apply, smul_add, smul_neg]

private theorem smul_add_smul_mul_mul_smul_add_smul_of_mul_eq_zero (hH : HbFacts) {H : Mat n} (h : H.IsHermitian) :
    ∑ p, coords H p • hb p = H := by
  conv_rhs => rw [← (hH n).2.2.1 H h]
  unfold hOf
  refine Finset.sum_congr rfl fun p _ => ?_
  ext a b
  simp [Complex.real_smul]

private theorem trace_mul_mul_mul_rotate_two (a B c D : Mat n) : trace (a * B * c * D) = trace (c * D * a * B) := by
  rw [Matrix.mul_assoc (a * B) c D, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

private theorem exists_dual_basis_dlog_of_isCoord (hH : HbFacts) {W : Type*} [Ring W] [Module ℝ W] [IsScalarTower ℝ W W]
    [SMulCommClass ℝ W W] (α β : Mat n →ₗ[ℝ] W) {x : Mat n} (hx : x.det ≠ 0) :
    ∑ i, α (xᴴ * hb i * x) * β (x⁻¹ * hb i * xᴴ⁻¹) = ∑ p, α (hb p) * β (hb p) := by
  have hbh : ∀ p, (hb p).IsHermitian := (hH n).1
  have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have huH : IsUnit xᴴ.det := by
    rw [det_conjTranspose]
    exact hu.star
  have hA' : ∀ i, (x⁻¹ * hb i * xᴴ⁻¹).IsHermitian := fun i => by
    rw [← conjTranspose_nonsing_inv]
    exact isHermitian_mul_mul_conjTranspose _ (hbh i)
  have hQ : ∀ q, (xᴴ⁻¹ * hb q * x⁻¹).IsHermitian := fun q => by
    rw [← conjTranspose_nonsing_inv]
    exact isHermitian_conjTranspose_mul_mul _ (hbh q)
  have hexp : ∀ i, β (x⁻¹ * hb i * xᴴ⁻¹) = ∑ q, coords (x⁻¹ * hb i * xᴴ⁻¹) q • β (hb q) := by
    intro i
    conv_lhs => rw [← smul_add_smul_mul_mul_smul_add_smul_of_mul_eq_zero hH (hA' i)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul]
  have hcoef : ∀ i q, coords (x⁻¹ * hb i * xᴴ⁻¹) q = coords (xᴴ⁻¹ * hb q * x⁻¹) i := by
    intro i q
    simp only [coords]
    rw [trace_mul_mul_mul_rotate_two]
  calc ∑ i, α (xᴴ * hb i * x) * β (x⁻¹ * hb i * xᴴ⁻¹)
      = ∑ i, ∑ q, coords (xᴴ⁻¹ * hb q * x⁻¹) i • (α (xᴴ * hb i * x) * β (hb q)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hexp i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hcoef, mul_smul_comm]
    _ = ∑ q, ∑ i, coords (xᴴ⁻¹ * hb q * x⁻¹) i • (α (xᴴ * hb i * x) * β (hb q)) := Finset.sum_comm
    _ = ∑ q, α (∑ i, coords (xᴴ⁻¹ * hb q * x⁻¹) i • (xᴴ * hb i * x)) * β (hb q) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_mul_assoc]
    _ = ∑ p, α (hb p) * β (hb p) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        have hs : ∑ i, coords (xᴴ⁻¹ * hb q * x⁻¹) i • (xᴴ * hb i * x)
            = xᴴ * (∑ i, coords (xᴴ⁻¹ * hb q * x⁻¹) i • hb i) * x := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mul_smul, Matrix.smul_mul]
        rw [hs, smul_add_smul_mul_mul_smul_add_smul_of_mul_eq_zero hH (hQ q)]
        simp only [Matrix.mul_assoc]
        rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ huH, Matrix.one_mul]

set_option maxHeartbeats 800000 in
theorem halfOne_of (hH : HbFacts) (hF : FrameDer) (hO : ∀ n, IsOpen (cone n)) (h1 : DerOne) : HalfOne := by
  intro n lam E Fr ε ι S Γ T hcx σ hσ hσh k hk hkeq d hd c v hv w hw
  obtain ⟨hxG, hdetv⟩ := KcInv.coneGL n σ hσh v hv
  obtain ⟨hyG, hdetw⟩ := KcInv.coneGL n σ hσh w hw
  set F : Mat n → (E.V →L[ℂ] E.V) := fun x' => Kf Fr k Γ T d x' (σ w) with hFdef
  have hFs : ContDiffOn ℝ ∞ F (GLs n) := by
    have hinner : ContDiffOn ℝ ∞ (fun x' : Mat n => x'⁻¹ * d * (σ w)ᴴ⁻¹) (GLs n) :=
      KcInv.mul_contDiffOn (KcInv.mul_contDiffOn KcInv.inv_contDiffOn contDiffOn_const)
        contDiffOn_const
    have hmaps : Set.MapsTo (fun x' : Mat n => x'⁻¹ * d * (σ w)ᴴ⁻¹) (GLs n) (GLs n) :=
      fun x' hx' => KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx') hd)
        (KcInv.inv_mem (KcInv.conjT_mem hyG))
    have h2 := hk.comp hinner hmaps
    exact (((hcx.smooth.mul h2).mul contDiffOn_const).mul contDiffOn_const).mul contDiffOn_const
  have hFinv : ∀ x' ∈ GLs n, ∀ u : unitaryGroup (Fin n) ℂ, F (x' * ↑u) = F x' := by
    intro x' hx' u
    have hu1 : ((u⁻¹ : unitaryGroup (Fin n) ℂ) : Mat n) * (u : Mat n) = 1 := by simp
    have huG : (u : Mat n) ∈ GLs n := by
      show (u : Mat n).det ≠ 0
      intro h0
      have h3 := congrArg Matrix.det hu1
      rw [det_mul, h0, mul_zero, det_one] at h3
      exact zero_ne_one h3
    have hinvu : (u : Mat n)⁻¹ = ((u⁻¹ : unitaryGroup (Fin n) ℂ) : Mat n) :=
      Matrix.inv_eq_left_inv hu1
    have hmG : x'⁻¹ * d * (σ w)ᴴ⁻¹ ∈ GLs n :=
      KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx') hd) (KcInv.inv_mem (KcInv.conjT_mem hyG))
    have hk' : k (((u⁻¹ : unitaryGroup (Fin n) ℂ) : Mat n) * x'⁻¹ * d * (σ w)ᴴ⁻¹)
        = E.ρ u⁻¹ * k (x'⁻¹ * d * (σ w)ᴴ⁻¹) := by
      have h := hkeq _ hmG u⁻¹ 1
      rw [show ((1 : unitaryGroup (Fin n) ℂ) : Mat n) = 1 from rfl, Matrix.mul_one, map_one,
        mul_one] at h
      rw [← h]
      simp only [Matrix.mul_assoc]
    simp only [hFdef, Kf]
    rw [hcx.mul x' hx' _ huG, hcx.onK u, Matrix.mul_inv_rev, hinvu, hk',
      ← mul_assoc (Fr x' * E.ρ u), mul_assoc (Fr x'), ← map_mul, mul_inv_cancel, map_one, mul_one]
  have hDσ : ContDiffOn ℝ ∞ (fun w' => F (σ w')) (cone n) :=
    hFs.comp hσ (fun v' hv' => (KcInv.coneGL n σ hσh v' hv').1)
  have hDσd : DifferentiableAt ℝ (fun w' => F (σ w')) v :=
    (hDσ.contDiffAt ((hO n).mem_nhds hv)).differentiableAt (by simp)
  have hKc : ∀ e, (fderiv ℝ (Kc σ c Fr k Γ T d) (v, w)) (e, 0)
      = ((c : ℂ) * ((hOf w).det ^ n)⁻¹) • (fderiv ℝ (fun w' => F (σ w')) v) e := by
    have hKs := KcInv.kcSmooth n E.V σ c Fr k Γ T d hd hσ hσh hcx.smooth hk
    have hmem : cone n ×ˢ cone n ∈ nhds (v, w) := ((hO n).prod (hO n)).mem_nhds ⟨hv, hw⟩
    have hKd : DifferentiableAt ℝ (Kc σ c Fr k Γ T d) (v, w) :=
      (hKs.contDiffAt hmem).differentiableAt (by simp)
    have h1 := hKd.hasFDerivAt.comp v (hasFDerivAt_prodMk_left (𝕜 := ℝ) v w)
    have h2 := hDσd.hasFDerivAt.const_smul ((c : ℂ) * ((hOf w).det ^ n)⁻¹)
    have heq : (Kc σ c Fr k Γ T d) ∘ (fun e => (e, w))
        = fun v' => ((c : ℂ) * ((hOf w).det ^ n)⁻¹) • F (σ v') := by
      funext v'
      rfl
    rw [heq] at h1
    intro e
    have h3 := congrArg (fun L => L e) (h1.unique h2)
    simpa using h3
  have hfr := hF n (E.V →L[ℂ] E.V) σ F hσ hσh hFs hFinv v hv (σ v) hxG (hσh v hv)
  set x := σ v with hxdef
  set y := σ w with hydef
  set m := x⁻¹ * d * yᴴ⁻¹ with hmdef
  set C : ℂ := (c : ℂ) * ((hOf w).det ^ n)⁻¹ with hCdef
  set φ := phiL Fr k m with hφ
  have hbh := (hH n).1
  have hstep : ∀ i, (fderiv ℝ (fun w' => F (σ w')) v) (Pi.single i 1)
      = (1/2 : ℝ) • (Fr x * φ (x⁻¹ * hb i * xᴴ⁻¹) * Γ * T * Fr y⁻¹) := by
    intro i
    have hXi : (x⁻¹ * hb i * xᴴ⁻¹).IsHermitian := herm_inv_conj (hbh i)
    have hxX : x * (x⁻¹ * hb i * xᴴ⁻¹) * xᴴ = hb i := by
      have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hxG
      have huH : IsUnit xᴴ.det := by
        rw [det_conjTranspose]
        exact hu.star
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ huH, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    have hc1 : coords (hb i) = Pi.single i 1 := by
      have h6 := (hH n).2.2.2.1 (Pi.single i 1)
      rwa [hOf_single] at h6
    have hc2 : coords (hb i + hb i) = Pi.single i 1 + Pi.single i 1 := by
      rw [← hc1]
      funext p
      simp only [coords, Matrix.add_mul, Matrix.trace_add, Complex.add_re, Pi.add_apply]
    have h5 := hfr _ hXi
    rw [hxX] at h5
    first
      | rw [two_smul] at h5
      | rw [two_nsmul] at h5
    rw [hc2, map_add] at h5
    have hder : (fderiv ℝ F x) (x * (x⁻¹ * hb i * xᴴ⁻¹))
        = Fr x * φ (x⁻¹ * hb i * xᴴ⁻¹) * Γ * T * Fr y⁻¹ :=
      h1 n lam E Fr ε ι S Γ T hcx k hk d y hd hyG x hxG _
    rw [hder] at h5
    rw [← h5, ← two_smul ℝ, smul_smul]
    norm_num
  have hfe : ∀ i, ε (hb i) * Fr x = Fr x * ε (xᴴ * hb i * x) :=
    fun i => hcx.frε x hxG (hb i) (hbh i)
  have hdual := exists_dual_basis_dlog_of_isCoord hH ε φ hxG
  rw [show (∑ i, ε (hb i) * (fderiv ℝ (Kc σ c Fr k Γ T d) (v, w)) (Pi.single i 1, 0))
      = ∑ i, ε (hb i) * (C • (1/2 : ℝ) • (Fr x * φ (x⁻¹ * hb i * xᴴ⁻¹) * Γ * T * Fr y⁻¹)) from
      Finset.sum_congr rfl fun i _ => by rw [hKc, hstep]]
  calc ∑ i, ε (hb i) * (C • (1/2 : ℝ) • (Fr x * φ (x⁻¹ * hb i * xᴴ⁻¹) * Γ * T * Fr y⁻¹))
      = C • (1/2 : ℝ) • (Fr x * (∑ i, ε (xᴴ * hb i * x) * φ (x⁻¹ * hb i * xᴴ⁻¹)) * Γ * T
          * Fr y⁻¹) := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.smul_sum,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, mul_smul_comm]
        congr 2
        simp only [← mul_assoc]
        rw [hfe i]
    _ = _ := by
        rw [hdual, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
        congr 1
        rw [show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.coe_smul]
        rfl

end PositivityTheory.RgBcC.LfSt.Kchain.KcHalf1
