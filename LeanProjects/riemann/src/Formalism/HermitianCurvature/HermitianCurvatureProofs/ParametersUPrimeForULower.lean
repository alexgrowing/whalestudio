import Formalism.HermitianCurvature.StatementTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealInputsBuiltClosedForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion

section PartBasic

open Finset MeasureTheory NumberField Formalism.FourierDecayAlt
open scoped Matrix

namespace Formalism.FourierDecayAlt.P.Topx1

noncomputable section

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem hsInner_eq [FiniteDimensional ℂ Wq] (X Y : Wq →L[ℂ] Wp) :
    Formalism.FourierDecayAlt.B.hsInner X Y = ∑ i, inner ℂ (Y (stdOrthonormalBasis ℂ Wq i)) (X (stdOrthonormalBasis ℂ Wq i)) := by
  first
    | (simp only [Formalism.FourierDecayAlt.B.hsInner, Formalism.FourierDecayAlt.B.hsVec, PiLp.inner_apply, PiLp.toLp_apply]; done)
    | (unfold Formalism.FourierDecayAlt.B.hsInner Formalism.FourierDecayAlt.B.hsVec; rw [PiLp.inner_apply]; rfl)
    | (simp [Formalism.FourierDecayAlt.B.hsInner, Formalism.FourierDecayAlt.B.hsVec, PiLp.inner_apply]; done)

theorem hsInner_sum_smul_left [FiniteDimensional ℂ Wq] {ι : Type} (s : Finset ι) (a : ι → ℂ)
    (X : ι → Wq →L[ℂ] Wp) (Y : Wq →L[ℂ] Wp) :
    Formalism.FourierDecayAlt.B.hsInner (∑ j ∈ s, a j • X j) Y = ∑ j ∈ s, a j * Formalism.FourierDecayAlt.B.hsInner (X j) Y := by
  first
    | (simp only [hsInner_eq, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, inner_sum, inner_smul_right, Finset.mul_sum]; exact Finset.sum_comm)
    | (simp only [hsInner_eq, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, inner_sum, inner_smul_right, Finset.mul_sum]; exact Finset.sum_comm)
    | (simp [hsInner_eq, inner_sum, inner_smul_right, Finset.mul_sum]; exact Finset.sum_comm)
    | (simp [hsInner_eq, inner_sum, inner_smul_right, Finset.mul_sum, Finset.sum_comm]; done)

theorem hsInner_proj (E : Wp →L[ℂ] Wp) (hidem : E.comp E = E) (hsa : ∀ v v' : Wp, inner ℂ (E v) v' = inner ℂ v (E v'))
    [FiniteDimensional ℂ Wq] (X Y : Wq →L[ℂ] Wp) :
    Formalism.FourierDecayAlt.B.hsInner (E.comp X) (E.comp Y) = Formalism.FourierDecayAlt.B.hsInner (E.comp X) Y := by
  rw [hsInner_eq, hsInner_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.comp_apply]
  rw [hsa, ← ContinuousLinearMap.comp_apply E E, hidem]

end hs

theorem dH_nil (P : M.Par) (l0 : ℕ) (TT : ℝ) (p : C.LPt) (e : Wd.Ix (Fin ([] : List C.Letter).length))
    (ρ : M.Ty P) : Top.dH P l0 TT [] p e ρ = 1 := by
  have hs : D.positionted ([] : List C.Letter) = [] := by
    first
    | rfl
    | (unfold D.positionted; simp)
  unfold Top.dH Top.cW
  rw [hs]
  first
    | (simp only [Fr.cs, List.length_nil, pow_zero, Complex.one_re, one_mul, Real.sqrt_one]; done)
    | (simp [Fr.cs]; done)

theorem hsInner_types {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : B.Mat P.k P.r → (Wp →L[ℂ] Wp)} {z e : Fin (2 * P.r + P.k + 1) → ℂ} (TP : Top.TypeProj P π z e)
    (X Y : Wq →L[ℂ] Wp) (hX : ∑ ρ : M.Ty P, (TP.E ρ).comp X = X) :
    ∑ ρ : M.Ty P, B.hsInner ((TP.E ρ).comp X) ((TP.E ρ).comp Y) = B.hsInner X Y := by
  calc ∑ ρ : M.Ty P, B.hsInner ((TP.E ρ).comp X) ((TP.E ρ).comp Y)
      = ∑ ρ : M.Ty P, B.hsInner ((TP.E ρ).comp X) Y :=
        Finset.sum_congr rfl fun ρ _ => hsInner_proj (TP.E ρ) (TP.idem ρ) (TP.selfAdj ρ) X Y
    _ = B.hsInner (∑ ρ : M.Ty P, (1 : ℂ) • (TP.E ρ).comp X) Y := by
        rw [hsInner_sum_smul_left]
        simp
    _ = B.hsInner X Y := by simp only [one_smul, hX]

theorem _root_.Formalism.FourierDecayAlt.P.top_of_empty : Top.TopOfEmpty := by
  intro hVT Wp Wq _ _ _ _ _ _ P l0 T ν' m₀ Θ TP F p q hpl hbf hp hq _ _
  unfold Top.topOf
  simp only [dH_nil, mul_one, Complex.ofReal_one, one_mul, Θ.nil]
  have hU : Unique (Wd.Ix (Fin ([] : List C.Letter).length)) := ⟨⟨fun i => Fin.elim0 i⟩, fun f => funext fun i => Fin.elim0 i⟩
  rw [Fintype.sum_unique]
  exact hsInner_types TP _ _ (hVT Wp Wq P T.base ν' m₀ TP F p hpl hbf hp)

theorem act_mul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (M N : Wd.SlopeTestRemainingChoices S (Q.Pr (Q.RadSp k r z z' π π'))) (x : Wd.Ix S → Q.RadSp k r z z' π π') :
    P5.act (M * N) x = P5.act M (P5.act N x) := by
  funext a
  simp only [P5.act, Matrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have key : ∀ s : Finset (Wd.Ix S),
      (∑ j ∈ s, M a j * N j b).1 (x b) = ∑ j ∈ s, (M a j).1 ((N j b).1 (x b)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]; rfl
  exact key Finset.univ

theorem _root_.Formalism.FourierDecayAlt.P.top_of_radial : Top.TopOfRadial := by
  intro Wp Wq _ _ _ _ _ _ P l0 T ν' m₀ Θ TP X μ L st hD hTL w A ε F hA hcl Φ hΦ p c g e' TP' τ hp hcg hτ hint
    hV hex hd
  unfold Top.topOf P5.topDens
  refine Finset.sum_congr rfl fun e _ => ?_
  set x := P5.act (P5.bTall L (D.positionted w)) (Top.firstStateVector Φ) with hx
  set y := P5.act (Fr.ofWord L st (D.positionted w)).F x with hy
  have hVe : D.vecV T.base ν' m₀ (Θ.Θ w e F) p = τ ((y e : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) := by
    rw [hV e, act_mul]
  rw [hVe, act_mul, hd y e, hsInner_sum_smul_left]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [hint, hτ, hsInner_proj (TP'.E ρ) (TP'.idem ρ) (TP'.selfAdj ρ)]
  push_cast
  ring

theorem isBuiltPlaceT_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {Θ : ∀ v : Fin S.f, Top.TopLift S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {TP : ∀ v : Fin S.f, Top.TypeProj (D.parOf S v) (T v).base.π (T v).base.z (m₀ v *ᵥ ν' v)}
    {A₀ Cc c : ℝ} (hc : c ≤ Cc) (h : Top.IsBuiltPlaceT Cc S T f χ ν' m₀ Θ TP A₀) :
    Top.IsBuiltPlaceT c S T f χ ν' m₀ Θ TP A₀ := by
  unfold Top.IsBuiltPlaceT JCT.IsBuiltPlace at h ⊢
  obtain ⟨⟨g1, g2, hU, hB, hl1, hl2, hG, hL, hCA, hCk, hk2, hA, hOn⟩, hT⟩ := h
  refine ⟨⟨g1, g2, hU, hB, hl1, hl2, hG, ?_, le_trans hc hCA, hCk, hk2, ?_, hOn⟩, hT⟩
  · intro v
    have h1 := hL v
    have hY : (0 : ℝ) ≤ (S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2 +
        (S.Ntop : ℝ) ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hc hY]
  · have hY : (0 : ℝ) ≤ ((S.G.r : ℝ) + 1) ^ 4 *
        ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hc hY]

theorem _root_.Formalism.FourierDecayAlt.P.typed_inputs_of_inputs : Top.InputsTOfInputs := by
  intro hW hL hS hP hI
  obtain ⟨c1, hW⟩ := hW
  obtain ⟨c2, hL⟩ := hL
  obtain ⟨c3, C₄, hC₄, hS⟩ := hS
  refine ⟨max c1 (max c2 c3), C₄, hC₄, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ Θ TP A₀ hBP
  refine ⟨hW E Wp Wq S T f χ ν' m₀ Θ TP A₀ (isBuiltPlaceT_mono (by simp) hBP),
    hL E Wp Wq S T f χ ν' m₀ Θ TP A₀ (isBuiltPlaceT_mono (by simp) hBP),
    hS E Wp Wq S T f χ ν' m₀ Θ TP A₀ (isBuiltPlaceT_mono (by simp) hBP), fun v => ?_,
    hI E Wp Wq S T f χ ν' m₀ Θ TP A₀ hBP.1.1 hBP.1.2.1 hBP.1.2.2.1 hBP.2⟩
  exact hP (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (S.l + 1) (T v) (ν' v) (m₀ v) (Θ v) (TP v) (f v) χ (D.AdmAt S v)

theorem _root_.Formalism.FourierDecayAlt.P.real_inputs_closed_typed : Top.RealInputsBuiltClosedT := by
  intro hPA hRMF hPD hFS hMA hIB hMu hLEM hLA hSL hWv hLB hLT hSF hMP hTP
  obtain ⟨C₆, hC₆, hLE⟩ := lemma_E_of_model lemma_E_of_residue level_zero_holds good_of_admissible hLEM
  obtain ⟨c1, hLA⟩ := hLA
  obtain ⟨c2, hSL⟩ := hSL
  obtain ⟨c3, hWv⟩ := hWv
  obtain ⟨c4, hLB⟩ := hLB
  obtain ⟨c5, hLT⟩ := hLT
  obtain ⟨c6, C₄, hC₄, hSF⟩ := hSF
  obtain ⟨c7, hMP⟩ := hMP
  refine ⟨C₆, max c1 (max c2 (max c3 (max c4 (max c5 (max c6 c7))))), C₄, hC₆, hC₄, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ Θ TP A₀ c H _ _ Vt hBPT hSB hc hcut hVt
  set top := Top.topsOf S T ν' m₀ Θ TP with htopdef
  have hBP : JCT.IsBuiltPlace (max c1 (max c2 (max c3 (max c4 (max c5 (max c6 c7)))))) S T f χ ν' m₀ top A₀ := hBPT.1
  have m1 := jct_isBuiltPlace_mono (by simp) hBP (c := c1)
  have m2 := jct_isBuiltPlace_mono (by simp) hBP (c := c2)
  have m3 := isBuiltPlaceT_mono (by simp) hBPT (c := c3)
  have m4 := jct_isBuiltPlace_mono (by simp) hBP (c := c4)
  have m5 := isBuiltPlaceT_mono (by simp) hBPT (c := c5)
  have m6 := isBuiltPlaceT_mono (by simp) hBPT (c := c6)
  have m7 := jct_isBuiltPlace_mono (by simp) hBP (c := c7)
  have htop : ∀ v, D.TopPSD (T v) (f v) χ (D.AdmAt S v) (top v) := fun v =>
    hTP (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (S.l + 1) (T v) (ν' v) (m₀ v) (Θ v) (TP v) (f v) χ (D.AdmAt S v)
  obtain ⟨hg1, hg2, hU, hB, hl1, hl2, hGr, -, -, hsm, -, -⟩ := hBP
  choose L j lam Cm σ hmod using hMP E Wp Wq S T f χ ν' m₀ top A₀ m7 c hc
  obtain ⟨Lw, hW, hTW⟩ := hWv E Wp Wq S T f χ ν' m₀ Θ TP A₀ m3
  obtain ⟨Ll, hLB1, hTL1⟩ := hLB E Wp Wq S T f χ ν' m₀ top A₀ m4
  obtain ⟨Ll', hLT1, hTL2⟩ := hLT E Wp Wq S T f χ ν' m₀ Θ TP A₀ m5
  have hTL : JC.ThresholdsLift S Ll Ll' := by
    unfold JC.ThresholdsLift
    exact ⟨hTL1, hTL2⟩
  have hIn : JCT.BuiltInputs C₄ C₆ S T f χ ν' m₀ top L j lam c Cm σ Lw Ll Ll' Vt := by
    unfold JCT.BuiltInputs
    exact ⟨hl1, hl2, hLA E Wp Wq S T f χ ν' m₀ top A₀ m1, hSL E Wp Wq S T f χ ν' m₀ top A₀ m2 hSB, htop, hGr, hW,
      hTW, hLB1, hLT1, hTL, hSF E Wp Wq S T f χ ν' m₀ Θ TP A₀ m6, hsm, hcut, hmod, hVt⟩
  refine ⟨L, j, lam, Cm, σ, hmod, ?_⟩
  intro Kr hK0 Th e
  obtain ⟨hPos, hGr', hInt, hP1, hP23, hT, hPG⟩ :=
    jct_parts_loc hPA hRMF hPD hFS hMA hMu C₄ C₆ E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' H Vt
      hg1 hg2 hU hB (hIB E Wp Wq S T f χ ν' m₀ Θ TP A₀ hg1 hg2 hU hBPT.2) hIn
  have hE : C.LemmaE S (JCT.jvModel S j Cm) :=
    hLE E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ hB
      (fun v ε hε => cutoff_smooth _ _ _ _ (T v).base χ (f v) ε hB.1 (hsm v) hε) hcut hmod
  exact real_inputs_concrete_holds E Wp Wq S (JCT.jvModel S j Cm) H Vt C₄ hg1 hg2 hPos hGr' hInt hP1 hP23 hT hE
    hPG Kr hK0 Th e

end

end Formalism.FourierDecayAlt.P.Topx1

end PartBasic

noncomputable section PartTypes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped InnerProductSpace ComplexConjugate

namespace Formalism.FourierDecayAlt.P.Topx1

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section adj

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem typ_inner_pres (hu : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {h : Mx k r} (hh : h ∈ UWset k r z)
    (v v' : W) : inner ℂ (π h v) (π h v') = inner ℂ v v' := by
  first
    | exact (⟨(π h).toLinearMap, hu h hh⟩ : W →ₗᵢ[ℂ] W).inner_map_map v v'
    | (have key := (⟨(π h).toLinearMap, hu h hh⟩ : W →ₗᵢ[ℂ] W).inner_map_map v v'; simpa using key)
    | (rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]; simp only [← map_add, ← map_sub, ← map_smul, hu h hh]; done)

theorem typ_dOp_skew (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z))
    (hu : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {X : Mx k r} (hX : QrD.InLieW k r z X) (v v' : W) :
    inner ℂ (QrD.dOp π X v) v' = - inner ℂ v (QrD.dOp π X v') := by
  have hd := QrD.dOp_hasDeriv hπ hc hX
  have hv : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (QrD.dOp π X v) 0 :=
    ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have hv' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v') (QrD.dOp π X v') 0 :=
    ((ContinuousLinearMap.apply ℂ W v').restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have hi := hv.inner ℂ hv'
  have hconst : HasDerivAt (fun t : ℝ => inner ℂ (π (NormedSpace.exp ((t : ℂ) • X)) v)
      (π (NormedSpace.exp ((t : ℂ) • X)) v')) 0 0 := by
    have : (fun t : ℝ => inner ℂ (π (NormedSpace.exp ((t : ℂ) • X)) v)
        (π (NormedSpace.exp ((t : ℂ) • X)) v')) = fun _ => inner ℂ v v' := by
      funext t
      exact typ_inner_pres hu (QrD.exp_uw hX t) v v'
    rw [this]
    exact hasDerivAt_const _ _
  have h0 := hi.unique hconst
  have he : π (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 1 := by
    simp [NormedSpace.exp_zero, hπ.1]
  simp only [he, ContinuousLinearMap.one_apply] at h0
  linear_combination h0

theorem typ_EB_adj (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z))
    (hu : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z] Bs) (a b : Fin m) (v v' : W) :
    inner ℂ (Qr.EB π Bs a b v) v' = inner ℂ v (Qr.EB π Bs b a v') := by
  obtain ⟨h1, h2⟩ := QrD.frame_lie hB a b
  have e1 : hpart1 (Hpk k r) (unitB (Hpk k r) Bs b a) =
      ((-1 : ℝ) : ℂ) • hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b) := by
    rw [Qx8.hpart1_unitB, Qx8.hpart1_unitB, smul_smul, ← neg_sub, smul_neg, ← neg_smul]
    congr 1
    push_cast
    ring
  have e2 : hpart2 (Hpk k r) (unitB (Hpk k r) Bs b a) = hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b) := by
    rw [Qx8.hpart2_unitB, Qx8.hpart2_unitB]
    congr 1
    exact add_comm _ _
  have hlin := (differential_operator_linear W k r z π ⟨hπ, hc⟩ _ _ h1 h1).2 (-1)
  show inner ℂ (QrD.ecOp π (unitB (Hpk k r) Bs a b) v) v' = inner ℂ v (QrD.ecOp π (unitB (Hpk k r) Bs b a) v')
  unfold QrD.ecOp
  rw [e1, e2, hlin]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_I]
  rw [typ_dOp_skew hπ hc hu h1, typ_dOp_skew hπ hc hu h2]
  simp only [neg_smul, one_smul, ContinuousLinearMap.neg_apply, inner_neg_right]
  ring

end adj

section proj

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

theorem typ_proj_orth (K : Submodule ℂ W) {u : W} (hu : u ∈ Kᗮ) : K.starProjection u = 0 := by
  first
    | exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero K.zero_mem (fun w hw => by rw [sub_zero]; exact Submodule.inner_left_of_mem_orthogonal hw hu)
    | (apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero K.zero_mem; intro w hw; rw [sub_zero]; exact Submodule.inner_left_of_mem_orthogonal hw hu)
    | (apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero K.zero_mem; intro w hw; simpa using (Submodule.mem_orthogonal' K u).mp hu w hw)

theorem typ_proj_comm {n : ℕ} (E : Fin n → Fin n → Module.End ℂ W) (K : Submodule ℂ W)
    (hst : ∀ a b, ∀ v ∈ K, E a b v ∈ K) (hadj : ∀ a b (v v' : W), inner ℂ (E a b v) v' = inner ℂ v (E b a v'))
    (a b : Fin n) (x : W) : K.starProjection (E a b x) = E a b (K.starProjection x) := by
  have hP : K.starProjection x ∈ K := by
    first
    | exact K.starProjection_apply_mem x
    | exact (K.orthogonalProjection x).2
  have hQ : x - K.starProjection x ∈ Kᗮ := by
    first
    | exact K.sub_starProjection_mem_orthogonal x
    | exact Submodule.sub_starProjection_mem_orthogonal x
    | exact Submodule.sub_orthogonalProjection_mem_orthogonal x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hst a b _ hP)
  intro w hw
  rw [show E a b x - E a b (K.starProjection x) = E a b (x - K.starProjection x) from (map_sub _ _ _).symm, hadj]
  exact Submodule.inner_left_of_mem_orthogonal (hst b a w hw) hQ

theorem typ_capSp_orth {n : ℕ} (E : Fin n → Fin n → Module.End ℂ W) (hE : GlRel E)
    (hadj : ∀ a b (v v' : W), inner ℂ (E a b v) v' = inner ℂ v (E b a v')) (m m' : Fin n → ℂ)
    (hne : ∃ w, Qr.cpol m w ≠ Qr.cpol m' w) {v : W} (hv : v ∈ Qr.CapSp E m) : v ∈ (Qr.CapSp E m')ᗮ := by
  set K := Qr.CapSp E m' with hK
  have hst := (capelli_stabilizer W n E m' hE).1
  have hcomm : ∀ a b, (K.starProjection : W →L[ℂ] W).toLinearMap * E a b = E a b * (K.starProjection).toLinearMap := by
    intro a b
    ext x
    exact typ_proj_comm E K hst hadj a b x
  have h1 : K.starProjection v ∈ Qr.CapSp E m := (capelli_stabilizer W n E m hE).2 _ hcomm v hv
  have h2 : K.starProjection v ∈ K := K.starProjection_apply_mem v
  obtain ⟨w, hw⟩ := hne
  have e1 := (Qr.mem_CapSp.1 h1) w
  have e2 := (Qr.mem_CapSp.1 h2) w
  have h0 : (Qr.cpol m w - Qr.cpol m' w) • K.starProjection v = 0 := by
    rw [sub_smul, ← e1, ← e2, sub_self]
  have hz : K.starProjection v = 0 := (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hw)
  have := Submodule.sub_starProjection_mem_orthogonal (K := K) v
  rwa [hz, sub_zero] at this

end proj

section frames

theorem typ_frame_exists (k r : ℕ) (hk : 1 ≤ k) (z e : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (hT : 0 < Tz k r z) (he : inWb k r e) (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) :
    ∃ Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, e] Bs := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact exists_frame_two n r z e hz hT he hez hee

theorem typ_frame_change {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (k r : ℕ)
    (hk : 1 ≤ k) (z e : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (W →L[ℂ] W))
    (Bs Bs' : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) (he : inWb k r e)
    (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) (hπ : Qr.IsRepW k r z π)
    (hB : IsFrameOf k r [z, e] Bs) (hB' : IsFrameOf k r [z, e] Bs') (w : ℂ) (v : W) :
    capRep k r π Bs w v = capRep k r π Bs' w v := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [(frame_general_linear W (n + 1) r n z π Bs hπ (HermitianFormSums.frame_sub hB)).2 w v,
    (frame_general_linear W (n + 1) r n z π Bs' hπ (HermitianFormSums.frame_sub hB')).2 w v,
    qr_frameChange_proof W n r z e π Bs Bs' hz hT he hez hee hπ hB hB' w]

end frames

section types

def typM (P : M.Par) (ρ : M.Ty P) : Fin (P.k - 1) → ℂ :=
  fun j => (M.rho P ρ ((j : ℕ) + 1) : ℂ) - ((P.k : ℂ) - 2) / 2

theorem typ_prod_Icc (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Finset.Icc 1 n, f i = ∏ j : Fin n, f ((j : ℕ) + 1) := by
  induction n with
  | zero => first | simp | rfl
  | succ n ih =>
    first
    | (rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc]; simp)
    | (rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc]; rfl)
    | (rw [← Nat.Ico_succ_right, Finset.prod_Ico_eq_prod_range, Finset.prod_range]; simp [add_comm])

theorem typ_xC (P : M.Par) (ρ : M.Ty P) (w : ℂ) :
    M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) = Qr.cpol (typM P ρ) w := by
  unfold M.xC Qr.cpol
  rw [typ_prod_Icc]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [typM]
  ring

theorem typ_rho_succ (P : M.Par) (ρ : M.Ty P) (j : Fin (P.k - 1)) :
    M.rho P ρ ((j : ℕ) + 1) = P.lo ((j : ℕ) + 1) + ((ρ j : ℕ) : ℝ) := by
  have hj := j.isLt
  unfold M.rho
  rw [dif_pos (show 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ P.k - 1 by omega)]
  all_goals first | rfl | simp

private theorem u_add_le_u_of_ok {Q : M.Par} (h : Q.OK) {i : ℕ} (hi1 : 1 ≤ i) :
    ∀ d : ℕ, i + d ≤ Q.k - 1 → Q.u (i + d) ≤ Q.u i := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h2 : max (Q.u (i + d + 1)) (Q.u' (i + d + 1)) + 1 / 2 ≤ min (Q.u (i + d)) (Q.u' (i + d)) - 1 / 2 :=
      h.gap (i + d) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have a1 := le_max_left (Q.u (i + d + 1)) (Q.u' (i + d + 1))
    have a2 := min_le_left (Q.u (i + d)) (Q.u' (i + d))
    have h3 := ih (by omega)
    show Q.u (i + d + 1) ≤ Q.u i
    linarith

private theorem rho_succ_le_hi_of_ok {Q : M.Par} (h : Q.OK) (π : M.Ty Q) (j : Fin (Q.k - 1)) :
    M.rho Q π ((j : ℕ) + 1) ≤ Q.hi ((j : ℕ) + 1) := by
  rw [typ_rho_succ]
  have hj := j.isLt
  have hg : Q.lo ((j : ℕ) + 1) ≤ Q.hi ((j : ℕ) + 1) := h.gap _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have h1 := (π j).isLt
  have hw : (Q.wid ((j : ℕ) + 1) : ℝ) ≤ Q.hi ((j : ℕ) + 1) - Q.lo ((j : ℕ) + 1) := by
    first
    | exact Nat.floor_le (by linarith)
    | (unfold M.Par.wid; exact Nat.floor_le (by linarith))
  have h2 : ((π j : Fin _) : ℕ) ≤ Q.wid ((j : ℕ) + 1) := by omega
  have h3 : (((π j : Fin _) : ℕ) : ℝ) ≤ Q.wid ((j : ℕ) + 1) := by exact_mod_cast h2
  linarith

theorem typ_rho_gap (P : M.Par) (hOK : P.OK) (ρ : M.Ty P) (a b : Fin (P.k - 1)) (hab : a < b) :
    ∃ N : ℕ, M.rho P ρ ((a : ℕ) + 1) - M.rho P ρ ((b : ℕ) + 1) = (N : ℝ) + 1 := by
  have ha := a.isLt
  have hb := b.isLt
  have hlt : (a : ℕ) < b := hab
  have r1 := typ_rho_succ P ρ a
  have r3 := typ_rho_succ P ρ b
  have r2 := rho_succ_le_hi_of_ok hOK ρ b
  have hlo : P.lo ((a : ℕ) + 1) = max (P.u ((a : ℕ) + 1 + 1)) (P.u' ((a : ℕ) + 1 + 1)) + 1 / 2 := rfl
  have hloB : P.lo ((b : ℕ) + 1) = max (P.u ((b : ℕ) + 1 + 1)) (P.u' ((b : ℕ) + 1 + 1)) + 1 / 2 := rfl
  have hhi : P.hi ((b : ℕ) + 1) = min (P.u ((b : ℕ) + 1)) (P.u' ((b : ℕ) + 1)) - 1 / 2 := rfl
  have hmono := u_add_le_u_of_ok hOK (i := (a : ℕ) + 1 + 1) (by omega) ((b : ℕ) - a - 1) (by omega)
  have he : (a : ℕ) + 1 + 1 + ((b : ℕ) - a - 1) = (b : ℕ) + 1 := by omega
  rw [he] at hmono
  have hmemA : (a : ℕ) + 1 + 1 ∈ Finset.Icc 1 P.k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hmemB : (b : ℕ) + 1 + 1 ∈ Finset.Icc 1 P.k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨x1, hx1⟩ := hOK.int_u _ hmemA
  obtain ⟨x2, hx2⟩ := hOK.int_u' _ hmemA
  obtain ⟨y1, hy1⟩ := hOK.int_u _ hmemB
  obtain ⟨y2, hy2⟩ := hOK.int_u' _ hmemB
  obtain ⟨c1, hc1⟩ : ∃ c : ℤ, max (P.u ((a : ℕ) + 1 + 1)) (P.u' ((a : ℕ) + 1 + 1)) - P.u 1 = c := by
    rcases max_choice (P.u ((a : ℕ) + 1 + 1)) (P.u' ((a : ℕ) + 1 + 1)) with hm | hm
    · exact ⟨x1, by rw [hm]; exact hx1⟩
    · exact ⟨x2, by rw [hm]; exact hx2⟩
  obtain ⟨c2, hc2⟩ : ∃ c : ℤ, max (P.u ((b : ℕ) + 1 + 1)) (P.u' ((b : ℕ) + 1 + 1)) - P.u 1 = c := by
    rcases max_choice (P.u ((b : ℕ) + 1 + 1)) (P.u' ((b : ℕ) + 1 + 1)) with hm | hm
    · exact ⟨y1, by rw [hm]; exact hy1⟩
    · exact ⟨y2, by rw [hm]; exact hy2⟩
  obtain ⟨z, hz⟩ : ∃ z : ℤ, M.rho P ρ ((a : ℕ) + 1) - M.rho P ρ ((b : ℕ) + 1) = z :=
    ⟨c1 - c2 + ((ρ a : ℕ) : ℤ) - ((ρ b : ℕ) : ℤ), by rw [r1, r3, hlo, hloB]; push_cast; linarith⟩
  have m1 := le_max_left (P.u ((a : ℕ) + 1 + 1)) (P.u' ((a : ℕ) + 1 + 1))
  have m2 := min_le_left (P.u ((b : ℕ) + 1)) (P.u' ((b : ℕ) + 1))
  have n0 : (0 : ℝ) ≤ ((ρ a : ℕ) : ℝ) := Nat.cast_nonneg _
  have hge : (1 : ℝ) ≤ M.rho P ρ ((a : ℕ) + 1) - M.rho P ρ ((b : ℕ) + 1) := by linarith
  have hd : (1 : ℝ) ≤ (z : ℝ) := by rw [← hz]; exact hge
  have hd' : (1 : ℤ) ≤ z := by exact_mod_cast hd
  refine ⟨(z - 1).toNat, ?_⟩
  have e1 : ((z - 1).toNat : ℤ) = z - 1 := Int.toNat_of_nonneg (by omega)
  have e2 : (((z - 1).toNat : ℕ) : ℝ) = (z : ℝ) - 1 := by exact_mod_cast e1
  rw [e2, hz]
  ring

theorem typ_sdec (P : M.Par) (hOK : P.OK) (ρ : M.Ty P) : Qr.SDec (typM P ρ) := by
  intro a b hab
  obtain ⟨N, hN⟩ := typ_rho_gap P hOK ρ a b hab
  refine ⟨N, ?_⟩
  simp only [typM]
  have h2 : ((M.rho P ρ ((a : ℕ) + 1) : ℝ) : ℂ) - ((M.rho P ρ ((b : ℕ) + 1) : ℝ) : ℂ) = (N : ℂ) + 1 := by
    exact_mod_cast hN
  linear_combination h2

private theorem re_add_one_le_re_of_sDec_of_lt {n : ℕ} {a : Fin n → ℂ} (ha : Qr.SDec a) {x y : Fin n} (hxy : x < y) :
    (a y).re + 1 ≤ (a x).re := by
  obtain ⟨N, hN⟩ := ha x y hxy
  have h1 := congrArg Complex.re hN
  simp at h1
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

private theorem eq_of_cpol_eq_of_sDec {n : ℕ} (a b : Fin n → ℂ) (ha : Qr.SDec a) (hb : Qr.SDec b)
    (h : ∀ w, Qr.cpol a w = Qr.cpol b w) : a = b := by
  have root : ∀ (c d : Fin n → ℂ), (∀ w, Qr.cpol c w = Qr.cpol d w) → ∀ i, ∃ j, d j = c i := by
    intro c d hcd i
    have h0 : Qr.cpol d (-c i) = 0 := by
      rw [← hcd]
      unfold Qr.cpol
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
    unfold Qr.cpol at h0
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp h0
    exact ⟨j, by linear_combination hj⟩
  have hba := root a b h
  have hab := root b a (fun w => (h w).symm)
  suffices H : ∀ m : ℕ, ∀ i : Fin n, (i : ℕ) = m → a i = b i from funext fun i => H _ i rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i hi
    obtain ⟨j, hj⟩ := hba i
    obtain ⟨j', hj'⟩ := hab i
    have hij : i ≤ j := by
      by_contra hlt
      push_neg at hlt
      have hlt' : (j : ℕ) < i := hlt
      have e := ih j (by omega) j rfl
      have h1 := re_add_one_le_re_of_sDec_of_lt ha hlt
      rw [← hj, ← e] at h1
      linarith
    have hij' : i ≤ j' := by
      by_contra hlt
      push_neg at hlt
      have hlt' : (j' : ℕ) < i := hlt
      have e := ih j' (by omega) j' rfl
      have h1 := re_add_one_le_re_of_sDec_of_lt hb hlt
      rw [← hj', e] at h1
      linarith
    have le1 : (b j).re ≤ (b i).re := by
      rcases eq_or_lt_of_le hij with e | lt
      · rw [e]
      · have h1 := re_add_one_le_re_of_sDec_of_lt hb lt
        linarith
    rcases eq_or_lt_of_le hij' with e | lt
    · subst e
      exact hj'
    · exfalso
      have h1 := re_add_one_le_re_of_sDec_of_lt ha lt
      have h2 : (a i).re = (b j).re := by rw [hj]
      have h3 : (b i).re = (a j').re := by rw [hj']
      linarith

theorem typ_poly_ne (P : M.Par) (hOK : P.OK) (ρ ρ' : M.Ty P) (h : ρ ≠ ρ') :
    ∃ w, Qr.cpol (typM P ρ) w ≠ Qr.cpol (typM P ρ') w := by
  by_contra hcon
  push_neg at hcon
  apply h
  have e := eq_of_cpol_eq_of_sDec _ _ (typ_sdec P hOK ρ) (typ_sdec P hOK ρ') hcon
  funext j
  have ej := congrFun e j
  simp only [typM] at ej
  have ej2 : M.rho P ρ ((j : ℕ) + 1) = M.rho P ρ' ((j : ℕ) + 1) := by
    have h3 : ((M.rho P ρ ((j : ℕ) + 1) : ℝ) : ℂ) = ((M.rho P ρ' ((j : ℕ) + 1) : ℝ) : ℂ) := by
      linear_combination ej
    exact_mod_cast h3
  rw [typ_rho_succ, typ_rho_succ] at ej2
  have ej3 : ((ρ j : ℕ) : ℝ) = ((ρ' j : ℕ) : ℝ) := by linarith
  exact Fin.ext (by exact_mod_cast ej3)

end types

end Formalism.FourierDecayAlt.P.Topx1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.Topx1

theorem type_projectors_exist : Formalism.FourierDecayAlt.Top.TypeProjExists := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' e hPl he hez hee
  obtain ⟨hOK, hz, -, hTz, -, hT, -⟩ := hPl
  obtain ⟨-, hrep, hcont, hunit, -, -⟩ := hT
  have hTpos : 0 < Tz P.k P.r z := hTz ▸ hOK.T_pos
  obtain ⟨Bs₀, hB₀⟩ := typ_frame_exists P.k P.r hOK.k_pos z e hz hTpos he hez hee
  have hB₀' := HermitianFormSums.frame_sub hB₀
  obtain ⟨hGl, hcap⟩ := frame_general_linear Wp P.k P.r (P.k - 1) z π Bs₀ ⟨hrep, hcont⟩ hB₀'
  have hadj := typ_EB_adj hrep hcont hunit hB₀'
  let J : M.Ty P → Submodule ℂ Wp := fun ρ => Qr.CapSp (Qr.EB π Bs₀) (typM P ρ)
  have hch : ∀ Bs, IsFrameOf P.k P.r [z, e] Bs → ∀ w v, capRep P.k P.r π Bs w v = capRep P.k P.r π Bs₀ w v :=
    fun Bs hB w v => typ_frame_change P.k P.r hOK.k_pos z e π Bs Bs₀ hz hTpos he hez hee ⟨hrep, hcont⟩ hB hB₀ w v
  have hJ : ∀ ρ v, v ∈ J ρ ↔ ∀ w, capRep P.k P.r π Bs₀ w v = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • v := by
    intro ρ v
    rw [Qr.mem_CapSp]
    refine forall_congr' fun w => ?_
    rw [hcap w v, typ_xC]
  have horth : ∀ ρ ρ', ρ ≠ ρ' → ∀ v ∈ J ρ, v ∈ (J ρ')ᗮ := fun ρ ρ' h v hv =>
    typ_capSp_orth (Qr.EB π Bs₀) hGl hadj _ _ (typ_poly_ne P hOK ρ ρ' h) hv
  refine ⟨{ E := fun ρ => (J ρ).starProjection, idem := ?_, orth := ?_, selfAdj := ?_, eigen := ?_, full := ?_ }⟩
  · intro ρ
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    exact Submodule.starProjection_eq_self_iff.mpr ((J ρ).starProjection_apply_mem v)
  · intro ρ ρ' h
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
    exact typ_proj_orth _ (horth ρ' ρ (Ne.symm h) _ ((J ρ').starProjection_apply_mem v))
  · intro ρ v v'
    exact Submodule.inner_starProjection_left_eq_right _ v v'
  · intro Bs hB ρ w v
    rw [hch Bs hB]
    exact (hJ ρ _).1 ((J ρ).starProjection_apply_mem v) w
  · intro Bs hB ρ v hv
    apply Submodule.starProjection_eq_self_iff.mpr
    rw [hJ]
    intro w
    rw [← hch Bs hB]
    exact hv w

end Formalism.FourierDecayAlt.P

end PartTypes

noncomputable section PartVec

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.Topx1

section group
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem vecw_fix_of_fix {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hu : IsUnit g.det)
    {v : Fin (2 * r + k + 1) → ℂ} (h : g *ᵥ v = v) : g⁻¹ *ᵥ v = v := by
  calc g⁻¹ *ᵥ v = g⁻¹ *ᵥ (g *ᵥ v) := by rw [h]
    _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem vecw_conj_mem (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) {hB : B.Mat k r} (hhB : hB ∈ UWset k r S.z') :
    m₀ * hB * m₀⁻¹ ∈ UWset k r S.z := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  have um := WeylGroupFacts.isUnit_of_uh hmU
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hmU hhB.1) (WeylGroupFacts.uh_inv hmU), fun a => ?_, ?_⟩
  · have h1 := hmfix a a.isLt
    have i1 := vecw_fix_of_fix um h1.1
    have i2 := vecw_fix_of_fix um h1.2
    refine ⟨?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, i1, (hhB.2.1 a).1, h1.1]
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, i2, (hhB.2.1 a).2, h1.2]
  · have hμ : ((√(Tz k r S.z' / Tz k r S.z) : ℝ) : ℂ) ≠ 0 := by
      have := Real.sqrt_pos.2 (div_pos S.T'_pos S.T_pos)
      exact_mod_cast this.ne'
    have hz : S.z = (((√(Tz k r S.z' / Tz k r S.z) : ℝ) : ℂ))⁻¹ • (m₀ *ᵥ S.z') := by
      rw [hmz, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    have hmi : m₀⁻¹ *ᵥ (m₀ *ᵥ S.z') = S.z' := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec]
    calc (m₀ * hB * m₀⁻¹) *ᵥ S.z
        = (m₀ * hB * m₀⁻¹) *ᵥ ((((√(Tz k r S.z' / Tz k r S.z) : ℝ) : ℂ))⁻¹ • (m₀ *ᵥ S.z')) := by
          rw [← hz]
      _ = (((√(Tz k r S.z' / Tz k r S.z) : ℝ) : ℂ))⁻¹ • (m₀ *ᵥ S.z') := by
          rw [Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmi, hhB.2.2]
      _ = S.z := hz.symm

theorem vecw_vec_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (p : C.LPt)
    {hB : B.Mat k r} (hhB : hB ∈ UWset k r S.z') (hBν : hB *ᵥ ν' = ν') :
    (S.π (m₀ * hB * m₀⁻¹)).comp ((D.vecV S ν' m₀ F p).comp (S.π' hB⁻¹)) = D.vecV S ν' m₀ F p := by
  by_cases h : D.IsLocPt p (r + 1) ∧ 0 < D.ptG (Tz k r S.z * Tz k r S.z') r p
  · obtain ⟨σ, hE⟩ := Dx2.VV.exE S ν' m₀ hbase p h.1 h.2
    obtain ⟨hγe, hZe, hDe, hσU, hE3, hE2⟩ := hE
    rw [isotropic_vectors_linear_indep k r Wp Wq S ν' m₀ F p h.1 (m₀ * σ) hbase h.2 hγe hZe hDe]
    have hpos : 0 < Gf k r S.z S.z' (m₀ * σ) := by
      rw [← ptG_spec k r S.z S.z' p _ h.1 hZe]; exact h.2
    have hA := vecw_conj_mem S hbase hhB
    have h1 := Dx2.VV.orbJ_pt S p h.1 hγe hZe hpos hA WeylGroupFacts.mem_n_one (fun b => Matrix.one_mulVec _) hhB
      WeylGroupFacts.mem_n_one (fun b => Matrix.one_mulVec _) F
    have hcomm : σ * hB = hB * σ := hE2 hB hhB.1 (fun a => hhB.2.1 a) hhB.2.2 hBν
    have um := WeylGroupFacts.isUnit_of_uh hbase.2.2.2.1.1
    have uB := WeylGroupFacts.isUnit_of_uh hhB.1
    have hfix : (m₀ * hB * m₀⁻¹ * 1)⁻¹ * (m₀ * σ) * (hB * 1) = m₀ * σ := by
      rw [Matrix.mul_one, Matrix.mul_one, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ um]
      calc m₀ * (hB⁻¹ * m₀⁻¹) * (m₀ * σ) * hB = m₀ * hB⁻¹ * (m₀⁻¹ * m₀) * (σ * hB) := by
            simp only [Matrix.mul_assoc]
        _ = m₀ * (hB⁻¹ * hB) * σ := by
            rw [Matrix.nonsing_inv_mul _ um, hcomm]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = m₀ * σ := by rw [Matrix.nonsing_inv_mul _ uB, Matrix.mul_one]
    rw [hfix] at h1
    exact h1
  · unfold D.vecV
    rw [dif_neg h]
    ext v
    simp

end group

section lie
variable {k r : ℕ}

theorem vecw_frame_map {g : B.Mat k r} (hgU : g ∈ UH (Hpk k r))
    (hgW : ∀ w, inWb k r w → inWb k r (g *ᵥ w)) {m : ℕ} {vs vs' : List (Fin (2 * r + k + 1) → ℂ)}
    (hvs : ∀ v ∈ vs', ∃ c : ℂ, ∃ v0 ∈ vs, v = c • (g *ᵥ v0))
    {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r vs Bs) :
    Q.IsFrameOf k r vs' (fun a => g *ᵥ Bs a) := by
  obtain ⟨h1, h2, h3⟩ := hB
  refine ⟨fun a => hgW _ (h1 a), fun a b => ?_, fun a v hv => ?_⟩
  · rw [Dx2.DF.herm_m0_mulVec_invariant g hgU]; exact h2 a b
  · obtain ⟨c, v0, hv0, rfl⟩ := hvs v hv
    rw [Qx8.herm_smul_right', Dx2.DF.herm_m0_mulVec_invariant g hgU, h3 a v0 hv0, mul_zero]

theorem vecw_frame_sub {m : ℕ} {vs vs' : List (Fin (2 * r + k + 1) → ℂ)} (hsub : ∀ v ∈ vs', v ∈ vs)
    {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r vs Bs) : Q.IsFrameOf k r vs' Bs := by
  unfold Q.IsFrameOf at hB ⊢
  exact ⟨hB.1, hB.2.1, fun a v hv => hB.2.2 a v (hsub v hv)⟩

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem vecw_base_parts (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) :
    m₀ ∈ UH (Hpk k r) ∧ (∀ w, inWb k r w → inWb k r (m₀ *ᵥ w)) ∧
    m₀⁻¹ ∈ UH (Hpk k r) ∧ (∀ w, inWb k r w → inWb k r (m₀⁻¹ *ᵥ w)) ∧ IsUnit m₀.det ∧
    S.z = (((√(Tz k r S.z' / Tz k r S.z) : ℝ) : ℂ))⁻¹ • (m₀ *ᵥ S.z') ∧
    S.z' = (((√(Tz k r S.z' / Tz k r S.z) : ℝ) : ℂ)) • (m₀⁻¹ *ᵥ S.z) := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  have um := WeylGroupFacts.isUnit_of_uh hmU
  have hme : ∀ a : Fin r, m₀ *ᵥ Dx2.DF.ee k r a = Dx2.DF.ee k r a := fun a => (hmfix a a.isLt).1
  have hms : ∀ a : Fin r, m₀ *ᵥ Dx2.DF.es k r a = Dx2.DF.es k r a := fun a => (hmfix a a.isLt).2
  have hiU := WeylGroupFacts.uh_inv hmU
  have hie : ∀ a : Fin r, m₀⁻¹ *ᵥ Dx2.DF.ee k r a = Dx2.DF.ee k r a := fun a => vecw_fix_of_fix um (hme a)
  have his : ∀ a : Fin r, m₀⁻¹ *ᵥ Dx2.DF.es k r a = Dx2.DF.es k r a := fun a => vecw_fix_of_fix um (hms a)
  have hμ : ((√(Tz k r S.z' / Tz k r S.z) : ℝ) : ℂ) ≠ 0 := by
    have := Real.sqrt_pos.2 (div_pos S.T'_pos S.T_pos)
    exact_mod_cast this.ne'
  have hz : S.z = (((√(Tz k r S.z' / Tz k r S.z) : ℝ) : ℂ))⁻¹ • (m₀ *ᵥ S.z') := by
    rw [hmz, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  refine ⟨hmU, fun w hw => Dx2.DF.m0_mulVec_mem_orthogonal m₀ hmU hme hms hw, hiU,
    fun w hw => Dx2.DF.m0_mulVec_mem_orthogonal m₀⁻¹ hiU hie his hw, um, hz, ?_⟩
  calc S.z' = m₀⁻¹ *ᵥ (m₀ *ᵥ S.z') := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec]
    _ = m₀⁻¹ *ᵥ ((((√(Tz k r S.z' / Tz k r S.z) : ℝ) : ℂ)) • S.z) := by rw [hmz]
    _ = (((√(Tz k r S.z' / Tz k r S.z) : ℝ) : ℂ)) • (m₀⁻¹ *ᵥ S.z) := Matrix.mulVec_smul _ _ _

theorem vecw_frame_fwd (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) {m : ℕ} {Bs' : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [S.z', ν'] Bs') : Q.IsFrameOf k r [S.z, m₀ *ᵥ ν'] (fun a => m₀ *ᵥ Bs' a) := by
  obtain ⟨hmU, hmW, -, -, -, hz, -⟩ := vecw_base_parts S hbase
  refine vecw_frame_map hmU hmW (fun v hv => ?_) hB
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact ⟨_, S.z', by simp, hz⟩
  · exact ⟨1, ν', by simp, by rw [one_smul]⟩

theorem vecw_conj_eq {m₀ : B.Mat k r} (hmU : m₀ ∈ UH (Hpk k r)) (um : IsUnit m₀.det) {m : ℕ}
    (Bs' : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m) :
    Q.unitB (Hpk k r) (fun a => m₀ *ᵥ Bs' a) a b = m₀ * Q.unitB (Hpk k r) Bs' a b * m₀⁻¹ ∧
    hpart1 (Hpk k r) (m₀ * Q.unitB (Hpk k r) Bs' a b * m₀⁻¹) = m₀ * hpart1 (Hpk k r) (Q.unitB (Hpk k r) Bs' a b) * m₀⁻¹ ∧
    hpart2 (Hpk k r) (m₀ * Q.unitB (Hpk k r) Bs' a b * m₀⁻¹) = m₀ * hpart2 (Hpk k r) (Q.unitB (Hpk k r) Bs' a b) * m₀⁻¹ := by
  have hiU := WeylGroupFacts.uh_inv hmU
  have hii : (m₀⁻¹)⁻¹ = m₀ := Matrix.nonsing_inv_nonsing_inv _ um
  have e1 := LeftDerivativeCurves.unitB_conj hiU Bs' a b
  have e2 := LeftDerivativeCurves.hpart1_conj hiU (Q.unitB (Hpk k r) Bs' a b)
  have e3 := LeftDerivativeCurves.hpart2_conj hiU (Q.unitB (Hpk k r) Bs' a b)
  rw [hii] at e1 e2 e3
  exact ⟨e1, e2, e3⟩

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem vecw_dOp_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (p : C.LPt) {X : B.Mat k r}
    (hX : QrD.InLieW k r S.z' X) (hXν : X *ᵥ ν' = 0) (hY : QrD.InLieW k r S.z (m₀ * X * m₀⁻¹)) :
    (QrD.dOp S.π (m₀ * X * m₀⁻¹)).comp (D.vecV S ν' m₀ F p) =
      (D.vecV S ν' m₀ F p).comp (QrD.dOp S.π' X) := by
  set V := D.vecV S ν' m₀ F p with hV
  obtain ⟨hmU, -, hiU, -, um, -, -⟩ := vecw_base_parts S hbase
  have key : ∀ t : ℝ, (S.π (NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)))).comp V =
      V.comp (S.π' (NormedSpace.exp ((t : ℂ) • X))) := by
    intro t
    have hhB := QrD.exp_uw hX t
    have hBν := Qx8.exp_fix hXν t
    set hB := NormedSpace.exp ((t : ℂ) • X) with hhBdef
    have hconj : NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)) = m₀ * hB * m₀⁻¹ := by
      have h := LeftDerivativeCurves.exp_swap hiU X t
      rw [Matrix.nonsing_inv_nonsing_inv _ um] at h
      calc NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹))
          = m₀ * (m₀⁻¹ * NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹))) := by
            rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ um, Matrix.one_mul]
        _ = m₀ * hB * m₀⁻¹ := by rw [h, Matrix.mul_assoc]
    have h := vecw_vec_intertwine S hbase F p hhB hBν
    have hinv := WeylGroupFacts.uw_inv hhB
    have uB := WeylGroupFacts.isUnit_of_uh hhB.1
    rw [hconj]
    calc (S.π (m₀ * hB * m₀⁻¹)).comp V
        = ((S.π (m₀ * hB * m₀⁻¹)).comp (V.comp (S.π' hB⁻¹))).comp (S.π' hB) := by
          rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, ← S.π'_rep.2 _ hinv _ hhB,
            Matrix.nonsing_inv_mul _ uB, S.π'_rep.1]
          rfl
      _ = V.comp (S.π' hB) := by rw [h]
  have hd1 := QrD.dOp_hasDeriv S.π'_rep S.π'_cont hX
  have hd2 := QrD.dOp_hasDeriv S.π_rep S.π_cont hY
  let L1 : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wq Wp V
  let L2 : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq Wp Wp).flip V
  have h1 := (L1.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd1
  have h2 := (L2.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd2
  have hfun : ((L2.restrictScalars ℝ) ∘ fun t : ℝ => S.π (NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)))) =
      ((L1.restrictScalars ℝ) ∘ fun t : ℝ => S.π' (NormedSpace.exp ((t : ℂ) • X))) := by
    funext t
    exact key t
  rw [hfun] at h2
  exact h2.unique h1

end lie

section cap

theorem vecw_fold {X Y : Type*} (V : X → Y) :
    ∀ {t : ℕ} (f : Fin t → X → X) (g : Fin t → Y → Y), (∀ i x, g i (V x) = V (f i x)) → ∀ x : X,
      (List.ofFn g).foldr (fun T h => T h) (V x) = V ((List.ofFn f).foldr (fun T h => T h) x)
  | 0, f, g, _, x => by simp
  | t + 1, f, g, h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.foldr_cons,
      vecw_fold V (fun i => f i.succ) (fun i => g i.succ) (fun i y => h i.succ y) x, h]

theorem vecw_qmF {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (V : X →ₗ[ℂ] Y)
    {n t : ℕ} (E : Fin n → Fin n → X → X) (E' : Fin n → Fin n → Y → Y)
    (hE : ∀ i j x, E' i j (V x) = V (E i j x)) (a b : Fin t → Fin n) (u : ℂ) (x : X) :
    Q.qmF E' a b u (V x) = V (Q.qmF E a b u x) := by
  unfold Q.qmF
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_smul]
  congr 1
  exact vecw_fold V _ _ (fun k y => by split_ifs <;> simp [hE]) x

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem vecw_ecOp_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (p : C.LPt) {m : ℕ}
    {Bs' : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs') (a b : Fin m) :
    (QrD.ecOp S.π (Q.unitB (Hpk k r) (fun a => m₀ *ᵥ Bs' a) a b)).comp (D.vecV S ν' m₀ F p) =
      (D.vecV S ν' m₀ F p).comp (QrD.ecOp S.π' (Q.unitB (Hpk k r) Bs' a b)) := by
  obtain ⟨hmU, -, -, -, um, -, -⟩ := vecw_base_parts S hbase
  have hBz : Q.IsFrameOf k r [S.z] (fun a => m₀ *ᵥ Bs' a) :=
    vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (vecw_frame_fwd S hbase hB)
  have hBz' : Q.IsFrameOf k r [S.z'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  have hBν : Q.IsFrameOf k r [ν'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  obtain ⟨e1, e2, e3⟩ := vecw_conj_eq hmU um Bs' a b
  have lY := QrD.frame_lie hBz a b
  have lX := QrD.frame_lie hBz' a b
  have lν := QrD.frame_lie hBν a b
  rw [e1, e2, e3] at lY
  unfold QrD.ecOp
  rw [e1, e2, e3, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, vecw_dOp_intertwine S hbase F p lX.1 lν.1.2 lY.1,
    vecw_dOp_intertwine S hbase F p lX.2 lν.2.2 lY.2]

theorem vecw_capRep_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (p : C.LPt) {m : ℕ}
    {Bs' : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs') (w : ℂ) (v : Wq) :
    Q.capRep k r S.π (fun a => m₀ *ᵥ Bs' a) w (D.vecV S ν' m₀ F p v) =
      D.vecV S ν' m₀ F p (Q.capRep k r S.π' Bs' w v) := by
  have hBz : Q.IsFrameOf k r [S.z] (fun a => m₀ *ᵥ Bs' a) :=
    vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (vecw_frame_fwd S hbase hB)
  have hBz' : Q.IsFrameOf k r [S.z'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  unfold Q.capRep
  refine vecw_qmF (D.vecV S ν' m₀ F p).toLinearMap _ _ (fun i j y => ?_) id id w v
  have lY := QrD.frame_lie hBz i j
  have lX := QrD.frame_lie hBz' i j
  simp only [ContinuousLinearMap.coe_coe]
  rw [QrD.ecRep_eq S.π_rep S.π_cont lY.1 lY.2, QrD.ecRep_eq S.π'_rep S.π'_cont lX.1 lX.2]
  have h := congrArg (fun L : Wq →L[ℂ] Wp => L y) (vecw_ecOp_intertwine S hbase F p hB i j)
  simpa using h

end cap

section par
open Finset

def parametersUForUPrime (P : M.Par) : M.Par := { P with u' := P.u }

def parametersUPrimeForU (P : M.Par) : M.Par := { P with u := P.u' }

theorem parameters_u_for_u_prime_ok {P : M.Par} (h : P.OK) : (parametersUForUPrime P).OK where
  k_pos := h.k_pos
  T_pos := h.T_pos
  T'_pos := h.T'_pos
  int_u := h.int_u
  int_u' := h.int_u
  gap := by
    intro i hi
    have g := h.gap i hi
    simp only [M.Par.lo, M.Par.hi, parametersUForUPrime, max_self, min_self] at g ⊢
    have a1 := le_max_left (P.u (i + 1)) (P.u' (i + 1))
    have a2 := min_le_left (P.u i) (P.u' i)
    linarith

theorem parameters_u_prime_for_u_ok {P : M.Par} (h : P.OK) : (parametersUPrimeForU P).OK where
  k_pos := h.k_pos
  T_pos := h.T_pos
  T'_pos := h.T'_pos
  int_u := by
    intro i hi
    obtain ⟨a, ha⟩ := h.int_u' i hi
    obtain ⟨b, hb⟩ := h.int_u' 1 (by simp [Finset.mem_Icc]; exact h.k_pos)
    exact ⟨a - b, by simp only [parametersUPrimeForU]; push_cast; linarith⟩
  int_u' := by
    intro i hi
    obtain ⟨a, ha⟩ := h.int_u' i hi
    obtain ⟨b, hb⟩ := h.int_u' 1 (by simp [Finset.mem_Icc]; exact h.k_pos)
    exact ⟨a - b, by simp only [parametersUPrimeForU]; push_cast; linarith⟩
  gap := by
    intro i hi
    have g := h.gap i hi
    simp only [M.Par.lo, M.Par.hi, parametersUPrimeForU, max_self, min_self] at g ⊢
    have a1 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
    have a2 := min_le_right (P.u i) (P.u' i)
    linarith

theorem vecw_rho_eq {Q : M.Par} (π : M.Ty Q) {i : ℕ} (hi : i ∈ Icc 1 (Q.k - 1)) :
    ∃ n : ℕ, n ≤ Q.wid i ∧ M.rho Q π i = Q.lo i + n := by
  rw [Finset.mem_Icc] at hi
  refine ⟨((π ⟨i - 1, by omega⟩ : Fin _) : ℕ), ?_, ?_⟩
  · have := (π ⟨i - 1, by omega⟩).isLt
    have e : i - 1 + 1 = i := by omega
    simp only [e] at this
    omega
  · unfold M.rho
    rw [dif_pos hi]

theorem vecw_lo_le_hi {Q : M.Par} (h : Q.OK) {i : ℕ} (hi : i ∈ Icc 1 (Q.k - 1)) : Q.lo i ≤ Q.hi i := by
  exact h.gap i hi

theorem vecw_rho_bounds {Q : M.Par} (h : Q.OK) (π : M.Ty Q) {i : ℕ} (hi : i ∈ Icc 1 (Q.k - 1)) :
    Q.lo i ≤ M.rho Q π i ∧ M.rho Q π i ≤ Q.hi i := by
  obtain ⟨n, hn, he⟩ := vecw_rho_eq π hi
  have g := vecw_lo_le_hi h hi
  have hf : (n : ℝ) ≤ Q.hi i - Q.lo i := by
    have := Nat.floor_le (sub_nonneg.2 g)
    have h2 : (n : ℝ) ≤ (Q.wid i : ℝ) := by exact_mod_cast hn
    unfold M.Par.wid at h2
    linarith
  constructor <;> [ (rw [he]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) ; (rw [he]; linarith) ]

theorem vecw_u_step {Q : M.Par} (h : Q.OK) {l : ℕ} (hl : l ∈ Icc 1 (Q.k - 1)) : Q.u (l + 1) + 1 ≤ Q.u l := by
  have h2 : max (Q.u (l + 1)) (Q.u' (l + 1)) + 1 / 2 ≤ min (Q.u l) (Q.u' l) - 1 / 2 := h.gap l hl
  have a1 := le_max_left (Q.u (l + 1)) (Q.u' (l + 1))
  have a2 := min_le_left (Q.u l) (Q.u' l)
  linarith

theorem vecw_u_mono {Q : M.Par} (h : Q.OK) {i : ℕ} (hi1 : 1 ≤ i) :
    ∀ d : ℕ, i + d ≤ Q.k - 1 → Q.u (i + d) ≤ Q.u i
  | 0, _ => by simp
  | d + 1, hd => by
    have s := vecw_u_step h (l := i + d) (by rw [Finset.mem_Icc]; omega)
    have ih := vecw_u_mono h hi1 d (by omega)
    rw [show i + (d + 1) = i + d + 1 by omega]
    linarith

theorem vecw_rho_int {Q : M.Par} (h : Q.OK) (π : M.Ty Q) {i : ℕ} (hi : i ∈ Icc 1 (Q.k - 1)) :
    ∃ n : ℤ, M.rho Q π i - Q.u 1 - 1 / 2 = n := by
  obtain ⟨N, -, he⟩ := vecw_rho_eq π hi
  rw [Finset.mem_Icc] at hi
  have hi1 : i + 1 ∈ Icc 1 Q.k := by rw [Finset.mem_Icc]; omega
  rw [he]
  unfold M.Par.lo
  rcases max_choice (Q.u (i + 1)) (Q.u' (i + 1)) with hm | hm
  · obtain ⟨a, ha⟩ := h.int_u (i + 1) hi1
    exact ⟨a + N, by rw [hm]; push_cast; linarith⟩
  · obtain ⟨a, ha⟩ := h.int_u' (i + 1) hi1
    exact ⟨a + N, by rw [hm]; push_cast; linarith⟩

theorem vecw_rho_gap {Q : M.Par} (h : Q.OK) (π : M.Ty Q) {i j : ℕ} (hi : i ∈ Icc 1 (Q.k - 1))
    (hj : j ∈ Icc 1 (Q.k - 1)) (hij : i < j) : ∃ N : ℕ, M.rho Q π i - M.rho Q π j = N + 1 := by
  have hi' := Finset.mem_Icc.mp hi
  have hj' := Finset.mem_Icc.mp hj
  obtain ⟨a, ha⟩ := vecw_rho_int h π hi
  obtain ⟨b, hb⟩ := vecw_rho_int h π hj
  have b1 := (vecw_rho_bounds h π hi).1
  have b2 := (vecw_rho_bounds h π hj).2
  have hlo : Q.lo i = max (Q.u (i + 1)) (Q.u' (i + 1)) + 1 / 2 := rfl
  have hhi : Q.hi j = min (Q.u j) (Q.u' j) - 1 / 2 := rfl
  have m1 := le_max_left (Q.u (i + 1)) (Q.u' (i + 1))
  have m2 := min_le_left (Q.u j) (Q.u' j)
  have hmono : Q.u (i + 1 + (j - (i + 1))) ≤ Q.u (i + 1) := vecw_u_mono h (by omega) (j - (i + 1)) (by omega)
  have hj2 : i + 1 + (j - (i + 1)) = j := by omega
  rw [hj2] at hmono
  have hd : (1 : ℝ) ≤ (a : ℝ) - b := by linarith
  have hd' : (1 : ℤ) ≤ a - b := by exact_mod_cast hd
  refine ⟨(a - b - 1).toNat, ?_⟩
  have e1 : ((a - b - 1).toNat : ℤ) = a - b - 1 := Int.toNat_of_nonneg (by omega)
  have e2 : (((a - b - 1).toNat : ℕ) : ℝ) = (a : ℝ) - b - 1 := by exact_mod_cast e1
  rw [e2]
  linarith

def vecwM (Q : M.Par) (π : M.Ty Q) : Fin (Q.k - 1) → ℂ := fun j => ((M.rho Q π ((j : ℕ) + 1) : ℝ) : ℂ)

theorem vecw_xC_cpol (Q : M.Par) (π : M.Ty Q) (Y : ℂ) : M.xC Q π Y = Qr.cpol (vecwM Q π) Y := by
  unfold M.xC Qr.cpol
  rw [typ_prod_Icc]
  all_goals rfl

theorem vecw_sdec {Q : M.Par} (h : Q.OK) (π : M.Ty Q) : Qr.SDec (vecwM Q π) := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  have hlt : (a : ℕ) < b := hab
  obtain ⟨N, hN⟩ := vecw_rho_gap h π (i := (a : ℕ) + 1) (j := (b : ℕ) + 1)
    (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (by omega)
  refine ⟨N, ?_⟩
  simp only [vecwM]
  first
    | exact_mod_cast hN
    | (rw [← Complex.ofReal_sub, hN]; push_cast; ring)

theorem vecw_rho_match {P : M.Par} (h : P.OK) (τ : M.Ty (parametersUForUPrime P)) (σ : M.Ty (parametersUPrimeForU P))
    (he : ∀ Y, M.xC (parametersUForUPrime P) τ Y = M.xC (parametersUPrimeForU P) σ Y) :
    ∀ i ∈ Icc 1 (P.k - 1), M.rho (parametersUForUPrime P) τ i = M.rho (parametersUPrimeForU P) σ i := by
  have e := eq_of_cpol_eq_of_sDec _ _ (vecw_sdec (parameters_u_for_u_prime_ok h) τ) (vecw_sdec (parameters_u_prime_for_u_ok h) σ)
    (fun w => (vecw_xC_cpol (parametersUForUPrime P) τ w).symm.trans ((he w).trans (vecw_xC_cpol (parametersUPrimeForU P) σ w)))
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  obtain ⟨j, rfl⟩ : ∃ j : Fin (P.k - 1), (j : ℕ) + 1 = i := ⟨⟨i - 1, by omega⟩, by show i - 1 + 1 = i; omega⟩
  have ej := congrFun e j
  simp only [vecwM] at ej
  exact_mod_cast ej

theorem parameters_u_for_u_prime_lower (P : M.Par) (i : ℕ) : (parametersUForUPrime P).lo i = P.u (i + 1) + 1 / 2 := by
  first
    | (simp only [parametersUForUPrime, M.Par.lo, max_self]; done)
    | (show max (P.u (i + 1)) (P.u (i + 1)) + 1 / 2 = P.u (i + 1) + 1 / 2; rw [max_self])
theorem parameters_u_for_u_prime_upper (P : M.Par) (i : ℕ) : (parametersUForUPrime P).hi i = P.u i - 1 / 2 := by
  first
    | (simp only [parametersUForUPrime, M.Par.hi, min_self]; done)
    | (show min (P.u i) (P.u i) - 1 / 2 = P.u i - 1 / 2; rw [min_self])
theorem parameters_u_prime_for_u_lower (P : M.Par) (i : ℕ) : (parametersUPrimeForU P).lo i = P.u' (i + 1) + 1 / 2 := by
  first
    | (simp only [parametersUPrimeForU, M.Par.lo, max_self]; done)
    | (show max (P.u' (i + 1)) (P.u' (i + 1)) + 1 / 2 = P.u' (i + 1) + 1 / 2; rw [max_self])
theorem parameters_u_prime_for_u_upper (P : M.Par) (i : ℕ) : (parametersUPrimeForU P).hi i = P.u' i - 1 / 2 := by
  first
    | (simp only [parametersUPrimeForU, M.Par.hi, min_self]; done)
    | (show min (P.u' i) (P.u' i) - 1 / 2 = P.u' i - 1 / 2; rw [min_self])

theorem vecw_ty_exists {P : M.Par} (h : P.OK) (τ : M.Ty (parametersUForUPrime P)) (σ : M.Ty (parametersUPrimeForU P))
    (he : ∀ i ∈ Icc 1 (P.k - 1), M.rho (parametersUForUPrime P) τ i = M.rho (parametersUPrimeForU P) σ i) :
    ∃ ρ : M.Ty P, ∀ i ∈ Icc 1 (P.k - 1), M.rho P ρ i = M.rho (parametersUForUPrime P) τ i := by
  have key : ∀ j : Fin (P.k - 1), ∃ n : Fin (P.wid ((j : ℕ) + 1) + 1),
      P.lo ((j : ℕ) + 1) + ((n : ℕ) : ℝ) = M.rho (parametersUForUPrime P) τ ((j : ℕ) + 1) := by
    intro j
    have hj := j.isLt
    have hmem : (j : ℕ) + 1 ∈ Finset.Icc 1 (P.k - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have e1 := he _ hmem
    have t1 := typ_rho_succ (parametersUForUPrime P) τ j
    have t2 := typ_rho_succ (parametersUPrimeForU P) σ j
    have b1 := vecw_rho_bounds (parameters_u_for_u_prime_ok h) τ hmem
    have b2 := vecw_rho_bounds (parameters_u_prime_for_u_ok h) σ hmem
    have hlo1 : (parametersUForUPrime P).lo ((j : ℕ) + 1) = P.u ((j : ℕ) + 1 + 1) + 1 / 2 := parameters_u_for_u_prime_lower P _
    have hlo2 : (parametersUPrimeForU P).lo ((j : ℕ) + 1) = P.u' ((j : ℕ) + 1 + 1) + 1 / 2 := parameters_u_prime_for_u_lower P _
    have hhi1 : (parametersUForUPrime P).hi ((j : ℕ) + 1) = P.u ((j : ℕ) + 1) - 1 / 2 := parameters_u_for_u_prime_upper P _
    have hhi2 : (parametersUPrimeForU P).hi ((j : ℕ) + 1) = P.u' ((j : ℕ) + 1) - 1 / 2 := parameters_u_prime_for_u_upper P _
    have hPlo : P.lo ((j : ℕ) + 1) = max (P.u ((j : ℕ) + 1 + 1)) (P.u' ((j : ℕ) + 1 + 1)) + 1 / 2 := rfl
    have hPhi : P.hi ((j : ℕ) + 1) = min (P.u ((j : ℕ) + 1)) (P.u' ((j : ℕ) + 1)) - 1 / 2 := rfl
    have hx : M.rho (parametersUForUPrime P) τ ((j : ℕ) + 1) ≤ P.hi ((j : ℕ) + 1) := by
      rw [hPhi]
      rcases min_choice (P.u ((j : ℕ) + 1)) (P.u' ((j : ℕ) + 1)) with hm | hm <;> rw [hm] <;>
        linarith [b1.2, b2.2, e1, hhi1, hhi2]
    rcases le_total (P.u' ((j : ℕ) + 1 + 1)) (P.u ((j : ℕ) + 1 + 1)) with hc | hc
    · have hm : max (P.u ((j : ℕ) + 1 + 1)) (P.u' ((j : ℕ) + 1 + 1)) = P.u ((j : ℕ) + 1 + 1) := max_eq_left hc
      have ht : M.rho (parametersUForUPrime P) τ ((j : ℕ) + 1) = P.u ((j : ℕ) + 1 + 1) + 1 / 2 + ((τ j : ℕ) : ℝ) := by
        rw [t1, hlo1]
      refine ⟨⟨(τ j : ℕ), ?_⟩, ?_⟩
      · have hw : ((τ j : ℕ) : ℝ) ≤ P.hi ((j : ℕ) + 1) - P.lo ((j : ℕ) + 1) := by
          rw [hPlo, hm]
          linarith
        have hn : (τ j : ℕ) ≤ P.wid ((j : ℕ) + 1) := by
          first
          | exact Nat.le_floor hw
          | (unfold M.Par.wid; exact Nat.le_floor hw)
        omega
      · show P.lo ((j : ℕ) + 1) + ((τ j : ℕ) : ℝ) = _
        rw [hPlo, hm, ht]
    · have hm : max (P.u ((j : ℕ) + 1 + 1)) (P.u' ((j : ℕ) + 1 + 1)) = P.u' ((j : ℕ) + 1 + 1) := max_eq_right hc
      have ht : M.rho (parametersUPrimeForU P) σ ((j : ℕ) + 1) = P.u' ((j : ℕ) + 1 + 1) + 1 / 2 + ((σ j : ℕ) : ℝ) := by
        rw [t2, hlo2]
      refine ⟨⟨(σ j : ℕ), ?_⟩, ?_⟩
      · have hw : ((σ j : ℕ) : ℝ) ≤ P.hi ((j : ℕ) + 1) - P.lo ((j : ℕ) + 1) := by
          rw [hPlo, hm]
          linarith
        have hn : (σ j : ℕ) ≤ P.wid ((j : ℕ) + 1) := by
          first
          | exact Nat.le_floor hw
          | (unfold M.Par.wid; exact Nat.le_floor hw)
        omega
      · show P.lo ((j : ℕ) + 1) + ((σ j : ℕ) : ℝ) = _
        rw [hPlo, hm, e1, ht]
  choose f hf using key
  refine ⟨f, fun i hi => ?_⟩
  have hi' := Finset.mem_Icc.mp hi
  obtain ⟨j, rfl⟩ : ∃ j : Fin (P.k - 1), (j : ℕ) + 1 = i := ⟨⟨i - 1, by omega⟩, by show i - 1 + 1 = i; omega⟩
  rw [typ_rho_succ P f j, hf j]

theorem vecw_xC_match {P : M.Par} (τ : M.Ty (parametersUForUPrime P)) (ρ : M.Ty P)
    (hρ : ∀ i ∈ Icc 1 (P.k - 1), M.rho P ρ i = M.rho (parametersUForUPrime P) τ i) (Y : ℂ) :
    M.xC P ρ Y = M.xC (parametersUForUPrime P) τ Y := by
  unfold M.xC
  exact Finset.prod_congr rfl (fun i hi => by rw [hρ i hi])

end par

section final
open Finset

theorem vecw_frame_exists (k r : ℕ) (hk : 1 ≤ k) (z e : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (hT : 0 < Tz k r z) (he : inWb k r e) (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) :
    ∃ Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z, e] Bs := by
  exact typ_frame_exists k r hk z e hz hT he hez hee

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem vecw_good_of_type {P : M.Par} {π : B.Mat P.k P.r → (Wp →L[ℂ] Wp)} {z e : Fin (2 * P.r + P.k + 1) → ℂ}
    (TP : Formalism.FourierDecayAlt.Top.TypeProj P π z e) {Bs₀ : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ}
    (hB₀ : Q.IsFrameOf P.k P.r [z, e] Bs₀) (ρ0 : M.Ty P) (x : Wp)
    (hx : ∀ w : ℂ, Q.capRep P.k P.r π Bs₀ w x = M.xC P ρ0 (w - ((P.k : ℂ) - 2) / 2) • x) :
    ∑ ρ, TP.E ρ x = x := by
  have h0 : TP.E ρ0 x = x := TP.full Bs₀ hB₀ ρ0 x hx
  rw [Finset.sum_eq_single ρ0]
  · exact h0
  · intro ρ _ hne
    have h1 : (TP.E ρ).comp (TP.E ρ0) = 0 := TP.orth ρ ρ0 hne
    calc TP.E ρ x = TP.E ρ (TP.E ρ0 x) := by rw [h0]
      _ = ((TP.E ρ).comp (TP.E ρ0)) x := rfl
      _ = 0 := by rw [h1, ContinuousLinearMap.zero_apply]
  · intro hn
    exact absurd (Finset.mem_univ ρ0) hn

theorem vecw_good_of_eig {P : M.Par} (hOK : P.OK) {π : B.Mat P.k P.r → (Wp →L[ℂ] Wp)}
    {z e : Fin (2 * P.r + P.k + 1) → ℂ} (hz : inWb P.k P.r z) (hT : 0 < Tz P.k P.r z)
    (hty : Q.IsType P.k P.r z π P.u) (he : inWb P.k P.r e) (hez : herm (Hpk P.k P.r) e z = 0)
    (hee : herm (Hpk P.k P.r) e e = 1) (TP : Formalism.FourierDecayAlt.Top.TypeProj P π z e)
    {Bs₀ : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ} (hB₀ : Q.IsFrameOf P.k P.r [z, e] Bs₀)
    (σ : M.Ty (parametersUPrimeForU P)) (x : Wp)
    (hx : ∀ w : ℂ, Q.capRep P.k P.r π Bs₀ w x = M.xC (parametersUPrimeForU P) σ (w - ((P.k : ℂ) - 2) / 2) • x) :
    ∑ ρ, TP.E ρ x = x := by
  obtain ⟨S, hInt, -, heig⟩ := branching_proof Wp (parametersUForUPrime P) (parameters_u_for_u_prime_ok hOK) rfl z e π hz hT hty he hez hee
  have heig' : ∀ (τ : M.Ty (parametersUForUPrime P)) (w : ℂ), ∀ v ∈ S τ,
      Q.capRep P.k P.r π Bs₀ w v = M.xC (parametersUForUPrime P) τ (w - ((P.k : ℂ) - 2) / 2) • v :=
    fun τ w v hv => heig Bs₀ hB₀ τ w v hv
  have hgl := frame_general_linear Wp P.k P.r (P.k - 1) z π Bs₀ ⟨hty.2.1, hty.2.2.1⟩
    (vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB₀)
  have hx_mem : x ∈ ⨆ τ ∈ (Finset.univ : Finset (M.Ty (parametersUForUPrime P))), S τ := by
    simp only [Finset.mem_univ, iSup_pos]
    rw [hInt.submodule_iSup_eq_top]; exact Submodule.mem_top
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum S x).1 hx_mem
  have hcomp : ∀ τ, ∑ ρ, TP.E ρ (μ τ : Wp) = μ τ := by
    intro τ
    by_cases hpoly : ∀ Y, M.xC (parametersUForUPrime P) τ Y = M.xC (parametersUPrimeForU P) σ Y
    · obtain ⟨ρ, hρ⟩ := vecw_ty_exists hOK τ σ (vecw_rho_match hOK τ σ hpoly)
      refine vecw_good_of_type TP hB₀ ρ _ fun w => ?_
      rw [heig' τ w _ (μ τ).2, vecw_xC_match τ ρ hρ]
    · simp only [not_forall] at hpoly
      obtain ⟨Y, hY⟩ := hpoly
      have hw : Y + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Y := by ring
      have hsum : ∑ τ' ∈ Finset.univ,
          (M.xC (parametersUForUPrime P) τ' Y - M.xC (parametersUPrimeForU P) σ Y) • (μ τ' : Wp) = 0 := by
        have h1 := hx (Y + ((P.k : ℂ) - 2) / 2)
        rw [hw, hgl.2] at h1
        have h2 : ∀ τ', qdet (Qr.EB π Bs₀) (Y + ((P.k : ℂ) - 2) / 2) (μ τ' : Wp) =
            M.xC (parametersUForUPrime P) τ' Y • (μ τ' : Wp) := by
          intro τ'
          rw [← hgl.2, heig' τ' _ _ (μ τ').2, hw]
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← Finset.smul_sum, hμ]
        simp only [← h2]
        rw [← map_sum, hμ, h1, sub_self]
      have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero S).1 hInt.submodule_iSupIndep Finset.univ
        (fun τ' => (M.xC (parametersUForUPrime P) τ' Y - M.xC (parametersUPrimeForU P) σ Y) • (μ τ' : Wp))
        (fun τ' _ => Submodule.smul_mem _ _ (μ τ').2) hsum τ (Finset.mem_univ τ)
      have hz0 : (μ τ : Wp) = 0 := by
        rcases smul_eq_zero.1 hind with h | h
        · exact absurd (sub_eq_zero.1 h) hY
        · exact h
      rw [hz0]
      simp
  rw [← hμ]
  simp only [map_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun τ _ => hcomp τ

end final

theorem vecw_main : Formalism.FourierDecayAlt.Top.VecVTypes := by
  intro Wp Wq _ _ _ _ _ _ P S ν' m₀ TP F p hPl hbase hp
  obtain ⟨hOK, hz, hz', -, -, hty, hty'⟩ := hPl
  obtain ⟨hmU, hmW, -, -, -, hzeq, -⟩ := vecw_base_parts S hbase
  obtain ⟨hν, hνz, hνν, -, -⟩ := id hbase
  have he : inWb P.k P.r (m₀ *ᵥ ν') := hmW ν' hν
  have hee : herm (Hpk P.k P.r) (m₀ *ᵥ ν') (m₀ *ᵥ ν') = 1 := by rw [Dx2.DF.herm_m0_mulVec_invariant m₀ hmU]; exact hνν
  have hez : herm (Hpk P.k P.r) (m₀ *ᵥ ν') S.z = 0 := by
    rw [hzeq, Qx8.herm_smul_right', Dx2.DF.herm_m0_mulVec_invariant m₀ hmU, hνz, mul_zero]
  obtain ⟨Bs₀', hB₀'⟩ := vecw_frame_exists P.k P.r hOK.k_pos S.z' ν' hz' S.T'_pos hν hνz hνν
  have hB₀ := vecw_frame_fwd S hbase hB₀'
  obtain ⟨S', hInt', -, heig⟩ := branching_proof Wq (parametersUPrimeForU P) (parameters_u_prime_for_u_ok hOK) rfl S.z' ν' S.π' hz'
    S.T'_pos hty' hν hνz hνν
  have heig' : ∀ (σ : M.Ty (parametersUPrimeForU P)) (w : ℂ), ∀ v ∈ S' σ,
      Q.capRep P.k P.r S.π' Bs₀' w v = M.xC (parametersUPrimeForU P) σ (w - ((P.k : ℂ) - 2) / 2) • v :=
    fun σ w v hv => heig Bs₀' hB₀' σ w v hv
  refine ContinuousLinearMap.ext fun f => ?_
  rw [_root_.sum_apply]
  simp only [ContinuousLinearMap.comp_apply]
  have hf : f ∈ ⨆ σ, S' σ := by rw [hInt'.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction S' (motive := fun f => ∑ ρ, TP.E ρ (D.vecV S ν' m₀ F p f) =
    D.vecV S ν' m₀ F p f) hf ?_ ?_ ?_
  · intro σ v hv
    refine vecw_good_of_eig hOK hz S.T_pos hty he hez hee TP hB₀ σ _ fun w => ?_
    rw [vecw_capRep_intertwine S hbase F p hB₀' w v, heig' σ w v hv, map_smul]
  · simp
  · intro a b ha hb
    simp only [map_add, Finset.sum_add_distrib, ha, hb]

end Formalism.FourierDecayAlt.P.Topx1

theorem Formalism.FourierDecayAlt.P.vector_valued_types : Formalism.FourierDecayAlt.Top.VecVTypes := by
  exact Formalism.FourierDecayAlt.P.Topx1.vecw_main

end PartVec
