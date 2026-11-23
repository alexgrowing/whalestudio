import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR GlobalTheory.HermFrame
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart cov per)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff ComplexOrder ComplexConjugate

namespace GlobalTheory.ThetaRR.HodgeDens

section Analysis

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
  {τ C : E → Matrix (Fin g) (Fin g) ℂ} {z : E}

theorem two_imPart (τ : E → Matrix (Fin g) (Fin g) ℂ) :
    (fun x => (2 : ℂ) • imPart τ x) = fun x => (-Complex.I) • τ x + Complex.I • (τ x)ᴴᵀ := by
  funext x
  ext a b
  apply Complex.ext <;> simp [imPart, two_mul]

theorem mContDiffAt_two_imPart (h : ∀ a b, ContDiffAt ℂ 2 (fun x => τ x a b) z) :
    MContDiffAt 2 (fun x => (2 : ℂ) • imPart τ x) z := by
  have h' : MContDiffAt 2 τ z := fun a b => (h a b).restrict_scalars ℝ
  rw [two_imPart]
  exact (MContDiffAt.smul contDiffAt_const h').add
    (MContDiffAt.smul contDiffAt_const h'.conjTranspose.transpose)

theorem mdel_two_imPart (h : ∀ a b, ContDiffAt ℂ 2 (fun x => τ x a b) z) (ξ : E) :
    mdel (fun x => (2 : ℂ) • imPart τ x) z ξ = (-Complex.I) • mdel τ z ξ ∧
      mdbar (fun x => (2 : ℂ) • imPart τ x) z ξ = Complex.I • (mdel τ z ξ)ᴴᵀ := by
  have h' : MContDiffAt 1 τ z := fun a b => ((h a b).restrict_scalars ℝ).of_le one_le_two
  have h0 : mdbar τ z ξ = 0 := by
    ext a b
    simp [dbar_eq_zero ((h a b).differentiableAt two_ne_zero)]
  have h'' := h'.conjTranspose.transpose
  rw [two_imPart, mdel_add (MContDiffAt.smul contDiffAt_const h')
    (MContDiffAt.smul contDiffAt_const h''), mdbar_add (MContDiffAt.smul contDiffAt_const h')
    (MContDiffAt.smul contDiffAt_const h''), mdel_smul (differentiableAt_const _) h',
    mdel_smul (differentiableAt_const _) h'', mdbar_smul (differentiableAt_const _) h',
    mdbar_smul (differentiableAt_const _) h'', mdel_transpose (fun x => (τ x)ᴴ),
    mdbar_transpose (fun x => (τ x)ᴴ), mdel_conjTranspose, mdbar_conjTranspose, h0]
  simp

theorem mddbar_two_imPart (h : ∀ a b, ContDiffAt ℂ 2 (fun x => τ x a b) z) (ξ η : E) :
    mddbar (fun x => (2 : ℂ) • imPart τ x) z ξ η = 0 := by
  have h' : MContDiffAt 2 τ z := fun a b => (h a b).restrict_scalars ℝ
  ext a b
  have h0 := ddbar_eq_zero_of_holomorphic (eventually_differentiableAt_of_contDiffAt_two (h a b))
  have hc : ContDiffAt ℝ 2 (fun x => conj (τ x a b)) z := h'.conjTranspose b a
  have e : (fun x => ((2 : ℂ) • imPart τ x) a b) =
      fun x => (-Complex.I) • τ x a b + Complex.I • conj (τ x a b) :=
    funext fun x => congrFun (congrFun (congrFun (two_imPart τ) x) a) b
  rw [mddbar_apply, e, ddbar_add ((h' a b).const_smul _) (hc.const_smul _),
    ddbar_const_smul _ (h' a b), ddbar_const_smul _ hc]
  simp [ddbar_conj (h' a b), h0]

theorem trace_curv_two_imPart (h : ∀ a b, ContDiffAt ℂ 2 (fun x => τ x a b) z)
    (hu : IsUnit (imPart τ z).det) (ξ : E) :
    (curv (fun x => (2 : ℂ) • imPart τ x) z ξ ξ).trace =
      (1 / 4) * ((imPart τ z)⁻¹ * mdel τ z ξ * (imPart τ z)⁻¹ * (mdel τ z ξ).map star).trace := by
  have hu2 : IsUnit ((2 : ℂ) • imPart τ z).det := by
    rw [det_smul]; exact (IsUnit.mk0 _ (pow_ne_zero _ two_ne_zero)).mul hu
  have ei : ((2 : ℂ) • imPart τ z)⁻¹ = (1 / 2 : ℂ) • (imPart τ z)⁻¹ :=
    inv_eq_right_inv (by rw [smul_mul_smul_comm, mul_nonsing_inv _ hu]; norm_num)
  rw [curv_eq (mContDiffAt_two_imPart h) hu2, mddbar_two_imPart h, (mdel_two_imPart h ξ).1,
    (mdel_two_imPart h ξ).2, ← transpose_nonsing_inv, ei, transpose_zero, Matrix.mul_zero, sub_zero,
    ← transpose_mul, ← transpose_mul, ← transpose_mul, trace_transpose,
    show (mdel τ z ξ)ᴴᵀ = (mdel τ z ξ).map star from rfl]
  simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  linear_combination (-(1 / 4) *
    ((imPart τ z)⁻¹ * mdel τ z ξ * (imPart τ z)⁻¹ * (mdel τ z ξ).map star).trace) * Complex.I_mul_I

theorem leviForm_log_det (h : ∀ a b, ContDiffAt ℂ 2 (fun x => τ x a b) z)
    (hu : IsUnit (imPart τ z).det) (hC : ∀ a b, ContDiffAt ℂ 2 (fun x => C x a b) z)
    (hh : ∀ᶠ x in 𝓝 z, (chg (C x) ((2 : ℂ) • imPart τ x)).IsHermitian)
    (hG : IsUnit (chg (C z) ((2 : ℂ) • imPart τ z)).det) (ξ : E) :
    -leviForm (fun x => Real.log (chg (C x) ((2 : ℂ) • imPart τ x)).det.re) z ξ ξ =
      (1 / 4) * ((imPart τ z)⁻¹ * mdel τ z ξ * (imPart τ z)⁻¹ * (mdel τ z ξ).map star).trace := by
  have hC' : MContDiffAt 2 C z := fun a b => (hC a b).restrict_scalars ℝ
  have hY := mContDiffAt_two_imPart h
  have hd := hG
  rw [chg, det_mul, det_mul, det_transpose] at hd
  have hCu : IsUnit (C z).det := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hd)
  have hYu := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hd)
  have h0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar C x η = 0 := by
    filter_upwards [eventually_all.2 fun a => eventually_all.2 fun b =>
      eventually_differentiableAt_of_contDiffAt_two (hC a b)] with x hx η
    ext a b
    simp [dbar_eq_zero (hx a b)]
  rw [← trace_curv (H := fun x => chg (C x) ((2 : ℂ) • imPart τ x))
    ((hC'.transpose.mul hY).mul hC'.conjTranspose.transpose) hh hG, ← trace_curv_two_imPart h hu]
  refine (congrArg trace (curv_changeFrame hY hYu hC' hCu h0 ξ ξ)).trans ?_
  rw [trace_mul_comm, mul_nonsing_inv_cancel_left _ _ hCu]

theorem tauU_fderiv_symPart (h : ∀ a b, DifferentiableAt ℂ (fun x => τ x a b) z)
    (hs : ∀ᶠ x in 𝓝 z, (τ x).IsSymm) (ξ : E) :
    tauU (fderiv ℂ (fun x => symPart (τ x)) z ξ) = mdel τ z ξ := by
  let L : (Fin g → Fin g → ℂ) →L[ℂ] symMat g := LinearMap.toContinuousLinearMap
    { toFun := fun A => symPart (Matrix.of A)
      map_add' := fun A B => Subtype.ext (by
        funext i j
        simp only [symPart, of_apply, Pi.add_apply, Submodule.coe_add]
        ring)
      map_smul' := fun t A => Subtype.ext (by
        funext i j
        simp only [symPart, of_apply, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul,
          RingHom.id_apply]
        ring) }
  have hd : DifferentiableAt ℂ (fun x => symPart (τ x)) z :=
    L.differentiableAt.comp z (f := fun x a b => τ x a b)
      (differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun b => h a b)
  ext a b
  let M : symMat g →L[ℂ] ℂ := ((ContinuousLinearMap.proj b).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => Fin g → ℂ) a)).comp (symMat g).subtypeL
  have e : (fun x => τ x a b) =ᶠ[𝓝 z] fun x => M (symPart (τ x)) := hs.mono fun x hx => by
    change τ x a b = (τ x a b + τ x b a) / 2
    rw [hx.apply a b]
    ring
  rw [mdel_apply, del_eq_fderiv (h a b), e.fderiv_eq]
  exact (congrArg (· ξ) (M.hasFDerivAt.comp z hd.hasFDerivAt).fderiv).symm

end Analysis

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} {A : Over S} [GrpObj A]
  {g D : ℕ} {h : VMetric p (omega A) g} {c : AlgChart p σ D}
  {τ : V D → Matrix (Fin g) (Fin g) ℂ} {ex : Pt (V D) g → CxPts (A.hom ≫ p) σ}

theorem contDiffAt_cot (H : IsPeriodChart h c τ ex) {U : S.Opens} {W : A.left.Opens}
    (hU : U ≤ unitSec A ⁻¹ᵁ W) (f : Γ(A.left, W)) {v : V D} (hv : v ∈ c.e.target)
    (hy : c.e.symm v ∈ ptsIn p σ U) (a : Fin g) : ContDiffAt ℂ 2 (fun x => cot ex W f x a) v := by
  obtain ⟨ho, hd⟩ := H.2.1 W f
  have e : (ex (v, 0)).1 = (c.e.symm v).1 ≫ unitSec A :=
    ((H.2.2 v hv).2.2.2.1 0).2 ⟨0, zero_mem _, by funext i; simp [per, vecMul, dotProduct]⟩
  have hm : ((v, 0) : Pt (V D) g) ∈ {b ∈ cov c.e.target g | ⊤ ≤ (ex b).1 ⁻¹ᵁ W} := by
    refine ⟨⟨hv, trivial⟩, ?_⟩
    rw [e]
    exact fun x hx => hU (hy hx)
  have hF : ContDiffAt ℂ 3 (fun P : Pt (V D) g => ev (A.hom ≫ p) σ W f (ex P)) (v, 0) :=
    SCV.contDiffAt_of_differentiableOn hd (ho.mem_nhds hm) 3
  exact (ContDiffAt.fderiv (𝕜 := ℂ) (f := fun x z => ev (A.hom ≫ p) σ W f (ex (x, z)))
    (g := fun _ => 0) (m := 2) hF contDiffAt_const (by norm_num)).clm_apply contDiffAt_const

theorem chernDens_det_omega : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (σ : k →+* ℂ)
    (P : PPAS S) (h : VMetric p (omega P.A) P.g) (H : h.IsCInf) (c : AlgChart p σ 1)
    (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ),
    IsPeriodChart h c τ ex → ∀ y ∈ c.e.source, c.chernDens ((VMetric.det H).φ σ) y =
      sdens (τ (c.e y)) (tauU (fderiv ℂ (fun x => symPart (τ x)) (c.e y)
        (EuclideanSpace.single 0 1))) / (4 * Real.pi) := by
  intro k _ S p σ P h H c τ ex HP y hy
  have hs := LieVB.sec_hom (MonObj.one (X := P.A))
  obtain ⟨U, W, hx, hle, ch⟩ := Conormal.exists_isChart hs (mem_ptsIn.1 (h.isVB.mem_pick y))
  have hU : y ∈ ptsIn p σ U := mem_ptsIn.2 hx
  let c₀ : VB.Chart (omega P.A) P.g := ⟨U, _, (h.isVB.pick y).isFrame.res hle⟩
  choose f hf using fun a => ch.d_surjective hs (c₀.e a)
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)
  have hm := ChartGlue.mem_over c.e hy hU
  let C : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ := fun x => of fun a b => cot ex W (f b) x a
  have hG : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ U,
      (h.met σ).G c₀ (c.e.symm v) = chg (C v) ((2 : ℂ) • imPart τ v) := fun v hv => by
    ext a b
    rw [← (h.met σ).form_frame c₀ hv.2, ← hf, ← hf, chg_apply]
    exact (HP.2.2 v hv.1).2.2.2.2 U W ch.le _ _ hv.2
  have hP : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ U,
      (chg (C v) ((2 : ℂ) • imPart τ v)).PosDef := fun v hv =>
    hG v hv ▸ (h.met σ).posDef c₀ _ hv.2
  have hτ : ∀ a b, ContDiffAt ℂ 2 (fun x => τ x a b) (c.e y) := fun a b =>
    SCV.contDiffAt_of_differentiableOn (HP.1.2.1 a b) (HP.1.1.mem_nhds hm.1) 2
  have hu : IsUnit (imPart τ (c.e y)).det := by
    have := (hP _ hm).det_pos.ne'.isUnit
    rw [chg, det_mul, det_mul, det_smul] at this
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left this))
  have key := leviForm_log_det (C := C) hτ hu (fun a b => contDiffAt_cot HP ch.le (f b) hm.1 hm.2 a)
    (eventually_of_mem (ho.mem_nhds hm) fun v hv => (hP v hv).isHermitian)
    (hP _ hm).det_pos.ne'.isUnit (EuclideanSpace.single 0 1)
  have hi : y ∈ ptsIn p σ ((VB.det (omega P.A) P.g).U c₀) := hU
  have e : (fun v => (((h.met σ).detWeight.φ c₀ (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => -((Real.log (chg (C v) ((2 : ℂ) • imPart τ v)).det.re : ℝ) : ℂ) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    rw [← Complex.ofReal_neg, ← hG v hv]
    rfl
  have hd : ContDiffAt ℝ 2 (fun v => (h.met σ).detWeight.φ c₀ (c.e.symm v)) (c.e y) :=
    (H σ).detWeight.contDiffAt c hy hi
  have hw := (contDiffAt_ofReal_comp hd).congr_of_eventuallyEq e.symm
  rw [tauU_fderiv_symPart (fun a b => (hτ a b).differentiableAt two_ne_zero)
    (eventually_of_mem (HP.1.1.mem_nhds hm.1) fun v hv => (HP.1.2.2 v hv).1)]
  refine (c.chernDens_eq (H σ).detWeight hy hi).trans ?_
  simp only [AlgChart.hess, Matrix.det_unique]
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e, CurveDens.cHess_apply_eq_ddbar hw]
  erw [ddbar_neg]
  refine (congrArg (fun t : ℂ => _ * t.re) key).trans ?_
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by simp, Complex.re_ofReal_mul]
  change _ * (_ * sdens _ _) = _
  simp only [Nat.factorial_one, Nat.cast_one, pow_one]
  ring

end GlobalTheory.ThetaRR.HodgeDens
