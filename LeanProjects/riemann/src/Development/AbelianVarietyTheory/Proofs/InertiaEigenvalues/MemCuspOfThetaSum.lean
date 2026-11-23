import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaClassSumDominantWeightIsCuspForm
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecOfMoveInv

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ThetaSumDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

noncomputable def evHom {S : Type} [CommRing S] [_root_.IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) : Rul Xo c →+* S where
  toFun f := evR Xo c f y
  map_one' := evalAt_one _ _ y
    (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S y)
  map_mul' f f' := evalAt_mul _ _ f f' y
  map_zero' := evalAt_zero _ _ y
  map_add' f f' := evalAt_add _ _ f f' y

noncomputable def secZero (Xo : Moduli Dw l) (c : Coeff l) : Subring (Rul Xo c) :=
  { (sec Xo c 0 0).toAddSubgroup with
    one_mem' := ⟨fun _ _ φ _ _ _ => (map_one φ).symm, fun p t _ _ _ => by
      have h0 : wchar (S := p.R) (ex Dw 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _
      rw [h0, one_mul]
      rfl⟩
    mul_mem' := fun ha hb => by simpa using sec_mul Xo c 0 0 0 0 ha hb }

theorem cases_of_pow_succ {z : ℂ} {e : ℕ} (he : 0 < e) (hz : z ^ (e + 1) = z) :
    ‖z + 1 - z ^ e‖ = 1 ∧ ‖1 - (z ^ e + z ^ e)‖ = 1 := by
  by_cases h0 : z = 0
  · simp [h0, he.ne']
  · have h1 : z ^ e = 1 := mul_right_cancel₀ h0 (by rw [← pow_succ, hz, one_mul])
    have h2 : ‖z‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg z) he.ne').1 (by rw [← norm_pow, h1, norm_one])
    rw [h1]
    norm_num [h2]

theorem evR_eq_of_marked_pow [inst : Algebra c.F ℂ] (hσ : GoodEmb c (algebraMap c.F ℂ)) (hA : l.A = 1) {f : Rul Xo c}
    (hf : f ∈ sec Xo c 0 0) {m : ℕ} (hm0 : 0 < m) (hfm : f ^ (m + 1) = f) {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {L : Lt E r} (hr : 1 ≤ r)
    (hs : IsSympl X bas) {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : ∀ a, mk a ∈ L) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hx' : x' ∈ X.dom) {y y' : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x' L y')
    (hk : A.Marked mk) (hk' : A'.Marked mk) : evR Xo c f y = evR Xo c f y' := by
  obtain ⟨σ, rfl⟩ : ∃ σ : c.F →+* ℂ, inst = σ.toAlgebra := ⟨algebraMap c.F ℂ, Algebra.algebra_ext _ _ fun _ => rfl⟩
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hf' : f ∈ secZero Xo c := hf
  have hz : ∀ z : FrPt Xo c ℂ, evHom z f ^ (m + 1) = evHom z f := fun z => by rw [← map_pow, hfm]
  have e1 : ∀ z : FrPt Xo c ℂ, evR Xo c (f + 1 - f ^ m) z = evHom z f + 1 - evHom z f ^ m := fun z => by
    change evHom z _ = _
    rw [map_sub, map_add, map_one, map_pow]
  have e2 : ∀ z : FrPt Xo c ℂ, evR Xo c (1 - (f ^ m + f ^ m)) z = 1 - (evHom z f ^ m + evHom z f ^ m) := fun z => by
    change evHom z _ = _
    rw [map_sub, map_add, map_one, map_pow]
  have h1 := evR_eq_of_marked σ hσ hA (f := f + 1 - f ^ m) (show _ ∈ secZero Xo c from sub_mem (add_mem hf' (one_mem _)) (pow_mem hf' m))
    (fun z => (congrArg norm (e1 z)).trans (cases_of_pow_succ hm0 (hz z)).1) hr hs hm x hx x' hx' y y' A A' hk hk'
  have h2 := evR_eq_of_marked σ hσ hA (f := 1 - (f ^ m + f ^ m))
    (show _ ∈ secZero Xo c from sub_mem (one_mem _) (add_mem (pow_mem hf' m) (pow_mem hf' m)))
    (fun z => (congrArg norm (e2 z)).trans (cases_of_pow_succ hm0 (hz z)).2) hr hs hm x hx x' hx' y y' A A' hk hk'
  rw [e1, e1] at h1
  rw [e2, e2] at h2
  change evHom y f = evHom y' f
  linear_combination h1 - (1 / 2 : ℂ) * h2

set_option maxHeartbeats 1000000 in

theorem mem_cusp_of_thetaSum (d : DeltaDat Xo c n) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (hr1 : 1 ≤ r)
    (hU : ∀ σ, GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) (hA : l.A = 1) (hlev : d.IsLev) (hA₂ : d.l₂.A = 1)
    [StarRing (𝓞 E)] (hnab : IsNab d.Xo₂ d.c₂ d.nab₂) (Λ : GenLat E n) (N : ℕ) (hun : Λ.Unimod) (hT : Λ.TrivAt d.l₂.M)
    (hO : Λ.LevOK N d.l₂.M) (a : (E →+* ℂ) × ℕ → ℕ) (hD : Dom a n) (hL : LastPos Dw a)
    {T : Type} [Fintype T] (cs : T → Rul d.Xo₂ d.c₂) (m : ℕ) (hm : 0 < m) (w : T → (Fin n → LevQ Dw d.l₂) → c.F)
    (P : T → MvPolynomial (LtN Dw n) c.F) (hcs : ∀ t, cs t ∈ sec d.Xo₂ d.c₂ 0 0 ∧ cs t ^ (m + 1) = cs t)
    (hP : ∀ t, P t ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (f : Rul Xo c) (hsec : f ∈ sec Xo c a n)
    (hval : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x) →
      ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∃ v : T → k,
        (∀ t, thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w t q)) Λ N
          (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (P t)) y₂ (v t)) ∧
        evR Xo c f y = ∑ t, evR d.Xo₂ d.c₂ (cs t) y₂ * v t) :
    f ∈ Formalism.L2.PjFree.cusp Xo c U a n := by
  have hci := GlobalTheory.chartIndependence_unconditional
  refine (Formalism.L2.PjFree.mem_cusp Xo c U a n f).2
    ⟨hsec, fun σ hσ => Formalism.L2.PjFree.holCusp_mem_holSub _ _ fun k => ?_⟩
  have hu := hU σ hσ
  obtain ⟨W⟩ := nonempty_uw hu
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI A₂ : Algebra d.c₂.F ℂ := (σ.comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have halg : ∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t := fun t => by
    change σ (d.eF.symm (d.eF t)) = σ t
    rw [AlgEquiv.symm_apply_apply]
  have hcomp : (algebraMap d.c₂.F ℂ).comp (d.eF : c.F →+* d.c₂.F) = σ := RingHom.ext fun t => halg t
  have hσ₂ : GoodEmb d.c₂ (algebraMap d.c₂.F ℂ) := by
    have h1 : d.eF (IntermediateField.inclusion c.le (baseKA l).ρ) =
        IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ := Subtype.ext rfl
    change algebraMap d.c₂.F ℂ (IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ) = _
    rw [← h1, halg]
    exact hσ
  have hn : Even n := hD.2
  obtain ⟨-, hsd, hmk, -⟩ := uw_lattice E H Dw l Xo c σ r (U σ) hσ hu hr1 W k
  obtain ⟨Dc, hDe, hk⟩ := exists_dic E H Dw l c σ r W.g n ((U σ).X k) a W.e hσ hu.1 (hu.2.1 k).1
    (hu.2.1 k).2 hsd hD
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ShortRead.halfIntegralGenerator_add_conj_eq_one H
  have hM : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hΛ : Λ.La ∈ Vset E n d.l₂.M := (GenLatCmp.genLat_vset E n Λ.La).2.1 _ N hM hun hT hO
  obtain ⟨v, hv⟩ :=
    (TensVac.vacua E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd 1 _ (Base.stdL_mem_Vset n 1)).1
  obtain ⟨x₁, hx₁⟩ := (GlobalTheory.frames_isConnected E r ((U σ).X k)).nonempty
  obtain ⟨b, -, hx₀, hux₀⟩ := exists_unitFr_rmul ((U σ).X k) hx₁
  obtain ⟨A₀, hAm, -⟩ := uw_anFib E H Dw l Xo c σ r (U σ) hσ hu hr1 W k Dc.bas Dc.idx Dc.sympl
    (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨_, hx₀⟩ hux₀
  obtain ⟨z₀, hz₀⟩ := hlev.2.2.2.2.2.2.1 ℂ halg (unC (U σ) k ⟨_, hx₀⟩)
  obtain ⟨B₀, -, mk₂, hmk₂, hB₀, hover⟩ := Lift.anFib_lift E H Dw l Xo c n d halg hlev r _ _ Dc.bas Dc.idx W.e _ _
    _ A₀ Dc.sympl hx₀ hsd z₀ hz₀ _ hAm
  obtain ⟨Y, hY⟩ := (DualMark.dual_marking E H Dw d.l₂ r _ _ mk₂ _ hsd hmk₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n N hO.1.pos
  obtain ⟨ρ, hρ, hnorm⟩ := VacNorm.norm_factor_eq E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd v hv
  have hpt : ∀ x (hx : x ∈ ((U σ).X k).dom), IsUnitFr ((U σ).X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧
      ∃ (A : AnFib ((U σ).X k) Dc.bas Dc.idx W.e x ((U σ).X k).Λ (unC (U σ) k ⟨x, hx⟩)) (θ : (Fin W.g → ℂ) → ℂ),
        A.Marked (W.mark k) ∧ A.Reads 1 (unC (U σ) k ⟨x, hx⟩).s θ ∧
        ∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA ((U σ).X k) Dc.bas Dc.idx v x z := by
    intro x hx hux
    obtain ⟨A, hA, θ, hθ, hmean⟩ := uw_anFib E H Dw l Xo c σ r (U σ) hσ hu hr1 W k Dc.bas Dc.idx Dc.sympl
      (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨x, hx⟩ hux
    have hT := isTheta1_of_reads_generator E H Dw l Xo c r _ _ Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hsd θ hθ
    obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd v hv x hx θ hT
    exact ⟨κ, hnorm x hx hux θ κ hT hmean hκ, A, θ, hA, hθ, hκ⟩
  choose κ hκ hpt using hpt
  obtain ⟨C, -, hCe⟩ := Const.exists_const ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k) ρ hρ κ hκ
  have hG := fun j => ShortRead.sb_gphi Dc.idx Dc.sympl hn hw hw' hsd hΛ hv.1 (fun q => σ (w j q)) Y
  have hth := fun j => theta_holomorphic_weight E r _ _ _ Dc.hr Dc.bas Dc.idx n Dc.sympl hn _ _ _ (hG j) _ (Dc.mem _ (hP j))
  rw [Dc.wt_eq] at hth
  have hs := hu.2.2.2.2.1 a n hD f hsec k
  let co : T → ℂ := fun j => evR d.Xo₂ d.c₂ (cs j) z₀ * algebraMap d.c₂.F ℂ
    (1⁻¹ * ((Λ.mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ * (Λ.zCard N r : d.c₂.F))
  have hrd := hCe (Formalism.L2.PjFree.rdU (U σ) f k) (fun x => ∑ j, co j * thP ((U σ).X k) Dc.hr Dc.bas Dc.idx
      (gphi ((U σ).X k) Dc.bas (H.w0 : E) Λ.La ((U σ).X k).Λ v (fun q => σ (w j q)) Y)
      (MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P j))) x) hs.1
    (DifferentiableOn.fun_sum fun j _ => (hth j).1.const_mul _) (fun x hx b hb => ⟨hs.2.1 x hx b hb, by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hth j).2.1 x hx b hb, mul_left_comm]
      rfl⟩) (by
      intro x hx hux
      obtain ⟨A, θ, hAk, hθ, hprod⟩ := hpt x hx hux
      obtain ⟨y₂, B, hy₂, hB, hrd⟩ := Reach.exists_lift_of_reached d halg hσ₂ hlev hA hA₂ hr1 A Dc.sympl hx hsd hmk hAk
        hmk₂ hover hx₀ B₀ hz₀ hB₀
      obtain ⟨vc, hvc, hev⟩ := hval ℂ halg _ y₂ hy₂
      have hrd' : Formalism.L2.PjFree.rdU (U σ) f k x = evR Xo c f (unC (U σ) k ⟨x, hx⟩) := dif_pos hx
      rw [hrd', hev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw d.l₂ d.Xo₂ d.c₂ r _ _ Dc.bas Dc.idx W.e x _ y₂ B Dc.sympl hx hsd _ n Dc.hr Dc.eL
        hu.1 hn (hDe ▸ Dc.dir_eq) d.nab₂ hnab θ v _ (hrd θ hθ) hv hprod mk₂ hmk₂ hB Λ.La hΛ N hO Y hY a _
        ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hP j)) _ 1 (vc j) (hvc j)
      rw [h, MvPolynomial.map_map, hcomp, evR_eq_of_marked_pow hσ₂ hA₂ (hcs j).1 hm (hcs j).2 hr1 Dc.sympl hmk₂.mem hx hx₀
        B B₀ hB hB₀]
      simp only [halg, co]
      change _ * (_ * _ * thP _ _ _ _ (gphi _ _ _ _ _ _ (fun q => σ (w j q)) _) _ _) = _
      ring)
  have hwt : Formalism.L2.PjFree.laU (U σ) a n k = wtOf ((U σ).X k) Dc.hr Dc.k Dc.k' n := Dc.wt_eq.symm
  rw [hwt] at hs ⊢
  refine CuspSum.mem_SS_of_eq_sum_thP E r ((U σ).X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn Dc.k Dc.k' ?_ T
    _ _ (fun j => ShortRead.sb_smul (C * co j) (hG j)) (fun j => Dc.mem _ (hP j)) _ (fun x hx => ?_) hs.2.2
  · rcases Nat.eq_zero_or_pos Dw.p with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (hk hL h0)
  · rw [hrd x hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ShortRead.theta_smul₂ Dc.hr Dc.idx Dc.sympl hn (hG j) (Dc.mem _ (hP j)) hx, mul_assoc C]

end GlobalTheory.ThetaSumDescent
