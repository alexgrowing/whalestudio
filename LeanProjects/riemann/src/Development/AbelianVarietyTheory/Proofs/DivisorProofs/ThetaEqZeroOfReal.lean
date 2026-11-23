import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FrameConstantTwistFactor
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTwistColumns
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilRepRationalPointsThetaFunctionsFock
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AhFrameFactorEqNegOnePowRiemannForm
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactor
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicThetaConstants

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorCompare

section Theta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix
open GlobalTheory.Ker GlobalTheory.Ker.HatLat GlobalTheory.ThetaSpace
open scoped TensorProduct

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}

theorem parts_eInf_smul (a : AE D) :
    finPart D (FinTranslate.eInf D • a) = 0 ∧ infPart D (a - FinTranslate.eInf D • a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [smul_zero, sub_zero, map_zero, and_self]
  | add a b ha hb =>
    refine ⟨by rw [smul_add, RingHom.map_add, ha.1, hb.1, add_zero], ?_⟩
    rw [smul_add, add_sub_add_comm, RingHom.map_add, ha.2, hb.2, add_zero]
  | tmul a x =>
    rw [TensorProduct.smul_tmul', ← TensorProduct.sub_tmul]
    constructor
    · show (sndA D.host.F (FinTranslate.eInf D • a)) ⊗ₜ[D.host.F] x = 0
      rw [show sndA D.host.F (FinTranslate.eInf D • a) = 0 from zero_mul _, TensorProduct.zero_tmul]
    · show (fstA D.host.F (a - FinTranslate.eInf D • a)) ⊗ₜ[D.host.F] x = 0
      rw [show fstA D.host.F (a - FinTranslate.eInf D • a) = 0 from
        (show a.1 - 1 * a.1 = 0 by rw [one_mul, sub_self]), TensorProduct.zero_tmul]

theorem exists_fin_add_real (w : WO S T) : ∃ u v, IsFinPt u ∧ IsRealPt v ∧ w = u + v :=
  ⟨w - FinTranslate.eInf D • w, FinTranslate.eInf D • w, Matrix.ext fun i j => (parts_eInf_smul (w i j)).2,
    Matrix.ext fun i j => (parts_eInf_smul (w i j)).1, (sub_add_cancel _ _).symm⟩

theorem isTheta_heisO (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    IsThetaFunO ψ S T (heisO ψ S T w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real w
  have h := GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hu (WeilVacMove.isTheta_heisO_real hψ hv hf)
  rwa [WeilVacMove.heisO_heisO, (WeilVacMove.symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one,
    one_smul] at h

theorem theta_eq_zero_of_real {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : ∀ w, IsRealPt w → f w = 0) :
    f = 0 := by
  have hΛ := stdL_full D.host.E S.rank
  have hL := stdL_full D.host.E T.rank
  have hO : ∀ c : 𝓞 D.host.F, ∀ y ∈ GlobalTheory.SW.tens (GlobalTheory.SW.stdL D.host.E S.rank) (GlobalTheory.SW.stdL D.host.E T.rank),
      (c : D.host.F) • y ∈ GlobalTheory.SW.tens (GlobalTheory.SW.stdL D.host.E S.rank) (GlobalTheory.SW.stdL D.host.E T.rank) := fun c y hy =>
    smul_mem_tens _ _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) hy
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨N, hN, hNU⟩ := exists_nsmul_mem_open (F := D.host.F) (tens_fg _ _ hΛ.1 hL.1) U hU
  funext w
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real w
  obtain ⟨y, hy⟩ := exists_rat (F := D.host.F) (tens_den _ _ hΛ.2 hL.2) hu
  obtain ⟨y', -, u', hu', e⟩ := exists_mod hO hN hy
  have hfin : IsFinPt (S := S) (T := T) (N • u') := isFinPt_nsmul (inf_eq_zero_of_mem (F := D.host.F) hu') N
  have hr0 : IsRealPt (ratW T S (y + y')ᵀ - finW S T (y + y')) := by
    funext a k
    show finPart D (incA D ((y + y') k a) - finW S T (y + y') a k) = 0
    rw [RingHom.map_sub]
    exact sub_eq_zero.2 rfl
  have hr := isRealPt_sub hv hr0
  have e0 : finW S T (y + y') = fT D.host.F 1 y + fT D.host.F 1 y' := (fT D.host.F 1).map_add y y'
  have e1 : u + v = ratW T S (y + y')ᵀ + ((v - (ratW T S (y + y')ᵀ - finW S T (y + y'))) + N • u') := by
    rw [e0, sub_eq_iff_eq_add.1 e]
    abel
  have e2 := congrFun (hl _ (hNU u' hu') hfin) (v - (ratW T S (y + y')ᵀ - finW S T (y + y')))
  rw [h0 _ hr] at e2
  unfold heisO at e2
  rw [(WeilVacMove.symplOH_fin_real S T _ _ hfin hr).2, AddChar.map_zero_eq_one, one_mul] at e2
  rw [e1, hf.quasi, e2, mul_zero, Pi.zero_apply]

theorem om_subst {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) {γ : GA D T} (hγ : γ ∈ GQ T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (w : WO S T) : om (1, γ) f w = f (actO S T 1⁻¹ γ⁻¹ w) := by
  have h1 := H.om_heis 1 γ (actO S T 1⁻¹ γ⁻¹ w) f hf
  have h2 := H.om_aut 1 (one_mem _) γ hγ _ (isTheta_heisO H.std hf (actO S T 1⁻¹ γ⁻¹ w))
  rw [OmRat.actO_inv_cancel] at h1
  rw [← OmRat.heisO_at_zero ψ w (om (1, γ) f), ← h1]
  exact h2.trans (OmRat.heisO_at_zero _ _ _)

end Theta

section Can

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem isCanTheta_unique {g : ℕ} {lab : Fin g → E →+* ℂ}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab} {k : Fin F.n}
    {Pm : (F.Di k).La →+ (Fin g → ℂ)} {y : FrPt Xo c (CAt σ)} {Hm Hm' : Matrix (Fin g) (Fin g) ℂ}
    {θ θ' : (Fin g → ℂ) → ℂ} (h : IndefiniteRowSideFullHecke.WeilTwistColumns.IsCanTheta F k Pm y Hm θ)
    (h' : IndefiniteRowSideFullHecke.WeilTwistColumns.IsCanTheta F k Pm y Hm' θ') : Hm = Hm' ∧ θ = θ' := by
  obtain ⟨hP, hy, -, -, him, χ, fr, f1, f2, f3, f4, f5, f6⟩ := h
  obtain ⟨-, -, -, -, him', χ', fr', g1, g2, g3, g4, g5, g6⟩ := h'
  obtain rfl : Hm = Hm' := TorusFamilyTheta.matrix_eq_of_im hP.2.2.2.1 (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; rw [him, him'])
  refine ⟨rfl, ?_⟩
  obtain ⟨R, hR⟩ := FrameSign.exists_period_norm_le' Pm hP.2.2.1 hP.2.2.2.1
  have hch : ∀ z, ∃ j, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    PullHermitian.exists_chart _ Xo.univ.t.PP.isLB
  have hex : ∀ b z, F.ex k Pm (z + Pm b) = F.ex k Pm z := fun b z => by
    rw [F.ex_add k Pm hP, (F.ex_ker k Pm hP (Pm b)).2 ⟨b, rfl⟩, _root_.mul_one]
  have ho : ∀ j, IsOpen {z | ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := fun j => by
    have h0 := (EtaAn.isHolTo_ex_of_isPeriod F k Pm hP (Xo.univ.t.PP.L.U j) 0).1
    simpa only [Set.mem_univ, true_and] using h0
  obtain ⟨q, hq, hG⟩ := PullHermitian.exists_glue _ ho hch (fun j z => fr j z * (fr' j z)⁻¹)
    (fun j => (f1 j).mul ((g1 j).inv (g2 j))) (fun j j' z hz hz' => by
      have hm := (CubeValues.le_preimage_inf _ _ _).2 ⟨hz, hz'⟩
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff (g2 _ _ hz) (g2 _ _ hz'), f3 j j' z hm, g3 j j' z hm]
      ring)
  have hq0 : ∀ z, q z ≠ 0 := fun z => by
    obtain ⟨j, hj⟩ := hch z
    rw [hG j z hj]
    exact mul_ne_zero (f2 j z hj) (inv_ne_zero (g2 j z hj))
  obtain ⟨-, hc⟩ := FrameUnits.form_eq_zero_and_const hR q hq hq0 (fun _ _ => 0) continuous_const
    (by simp) (by simp) (by simp) (by
      rintro _ ⟨b, rfl⟩
      obtain ⟨j0, -⟩ := hch 0
      have n1 := (f5 b j0 0).1
      have n2 := (g5 b j0 0).1
      refine ⟨χ' (Pm b) / χ (Pm b), by rw [norm_div, n1, n2, div_one], fun z => ?_⟩
      obtain ⟨j, hj⟩ := hch z
      have hj' : ⊤ ≤ (F.ex k Pm (z + Pm b)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hex]; exact hj
      have m1 : χ (Pm b) ≠ 0 := norm_ne_zero_iff.1 (by rw [n1]; exact one_ne_zero)
      have m2 : χ' (Pm b) ≠ 0 := norm_ne_zero_iff.1 (by rw [n2]; exact one_ne_zero)
      have m3 := g2 j _ hj'
      rw [hG j z hj, hG j _ hj', (f5 b j z).2 hj, (g5 b j z).2 hj]
      simp only [mul_zero, add_zero, Complex.exp_zero]
      field_simp)
  have h1 : q 0 = 1 := by
    obtain ⟨j, hj⟩ := hch 0
    rw [hG j 0 hj, f4 j hj, ← g4 j hj, mul_inv_cancel₀ (g2 j 0 hj)]
  funext z
  obtain ⟨j, hj⟩ := hch z
  have hfr : fr j z = fr' j z := by
    have := hG j z hj
    rw [hc, h1] at this
    exact (mul_inv_eq_one₀ (g2 j z hj)).1 this.symm
  obtain ⟨pt, p1, p2⟩ : ∃ pt : Sp ℂ ⟶ Gx y.x, pt ≫ gxFst y.x = (F.ex k Pm z).left ∧ pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) := by
    have key : ∀ x : Sp ℂ ⟶ Xo.X, x = F.u k Pm →
        ∃ pt : Sp ℂ ⟶ Gx x, pt ≫ gxFst x = (F.ex k Pm z).left ∧ pt ≫ gxSnd x = 𝟙 (Sp ℂ) := by
      rintro _ rfl
      exact ⟨(lift (𝟙 (Over.mk (F.u k Pm))) (F.ex k Pm z)).left,
        congrArg CommaMorphism.left (lift_snd (𝟙 (Over.mk (F.u k Pm))) (F.ex k Pm z)),
        congrArg CommaMorphism.left (lift_fst (𝟙 (Over.mk (F.u k Pm))) (F.ex k Pm z))⟩
    exact key _ hy
  apply mul_right_cancel₀ (g2 j z hj)
  rw [← g6 j z pt p1 p2 hj, f6 j z pt p1 p2 hj, hfr]

end Can

section Const

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct

variable {D : D7}

theorem archM_mul (W : HSp D) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g g' : GA D W) :
    archM W th (g * g') = archM W th g * archM W th g' := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem rat_eq_of_archM {W : HSp D} {τ : D.host.E →+* ℂ} {th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (hth : Formalism.MainNotions.StandardLattice.IsInfEmb τ th) {γ γ' h : GA D W} (hγ : γ ∈ GQ W) (hγ' : γ' ∈ GQ W)
    (e : archM W th (γ * h) = archM W th (γ' * h)) : γ = γ' := by
  have e1 : archM W th γ = archM W th γ' := by
    rw [← mul_inv_cancel_right γ h, ← mul_inv_cancel_right γ' h, archM_mul W th (γ * h), archM_mul W th (γ' * h), e]
  obtain ⟨m, hm⟩ := ThetaSpace.exists_mt_eq W hγ
  obtain ⟨m', hm'⟩ := ThetaSpace.exists_mt_eq W hγ'
  have key : ∀ (g : GA D W) (n : Matrix (Fin W.rank) (Fin W.rank) D.host.E), mt W g = n.map (incA D) →
      ∀ a b, archM W th g a b = τ (n a b) := fun g n hn a b => by
    have : archM W th g a b = th (infPart D (mt W g a b)) := rfl
    rw [this, hn]
    exact hth.1 _
  have e2 : m = m' := Matrix.ext fun a b => τ.injective (by rw [← key γ m hm, ← key γ' m' hm', e1])
  exact Subtype.ext (Units.ext (hm.trans (e2 ▸ hm'.symm)))

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem frame_iff_const {U : Unf Xo c σ r} {V W : HSp D} {hr : W.rank = r} {dict : GA D W → Σ k, Frame (U.X k).Ψ r}
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)} {g : ℕ} {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {ψ : AddChar (AF D.host.F) ℂ}
    {χV χW χV' χW' : (AE D)ˣ →* Circle} {om om' : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {vac : WO V W → ℂ}
    {cst cst' : GA D W → ℂ} (hΨ : ∀ k, (U.X k).Ψ.Nonempty) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (ho : IsWeilDatumO ψ V W χV χW om) (ho' : IsWeilDatumO ψ V W χV' χW' om')
    (hv : IsThetaFunO ψ V W vac) (hv0 : vac ≠ 0)
    (hc : IndefiniteRowSideFullHecke.WeilTwistColumns.IsFrameConst U V W hr dict ι e F ik φ th x₀ om vac cst)
    (hc' : IndefiniteRowSideFullHecke.WeilTwistColumns.IsFrameConst U V W hr dict ι e F ik φ th x₀ om' vac cst') (h : GA D W) (a b : ℂ) :
    a • IndefiniteRowSideFullHecke.FrameConstantVectors.frameVec om' vac h = b • IndefiniteRowSideFullHecke.FrameConstantVectors.frameVec om vac h ↔ a * cst' h = b * cst h := by
  obtain ⟨γ, ⟨hγ, -⟩, hm, hx, Pm, Hm, θ, hP, hθ, hw⟩ := hc h
  obtain ⟨γ', ⟨hγ', -⟩, hm', hx', Pm', Hm', θ', hP', hθ', hw'⟩ := hc' h
  obtain rfl : γ = γ' := by
    obtain ⟨τ, hτ⟩ := hΨ (dict h).1
    have hd : (mat (dict h).2 ⟨τ, hτ⟩).det ≠ 0 := (hx ⟨τ, hτ⟩).1
    rw [hm, Matrix.det_mul] at hd
    have hu : IsUnit (x₀ τ) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hd))
    exact rat_eq_of_archM (hth _ ⟨τ, hτ⟩) hγ hγ' ((Matrix.reindex _ _).injective
      (hu.mul_right_cancel ((hm ⟨τ, hτ⟩).symm.trans (hm' ⟨τ, hτ⟩))))
  obtain rfl : Pm = Pm' := AddMonoidHom.ext fun x => funext fun j => (hP x j).trans (hP' x j).symm
  obtain ⟨rfl, rfl⟩ := isCanTheta_unique hθ hθ'
  have hs : ∀ {χ₁ χ₂ : (AE D)ˣ →* Circle} {o : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)},
      IsWeilDatumO ψ V W χ₁ χ₂ o → ∀ w,
        o (1, γ * h) vac w = IndefiniteRowSideFullHecke.FrameConstantVectors.frameVec o vac h (actO V W 1⁻¹ γ⁻¹ w) := fun {_ _ o} H w => by
    have : ((1, γ * h) : GA D V × GA D W) = (1, γ) * (1, h) := by rw [Prod.mk_mul_mk, one_mul]
    rw [this, map_mul, Module.End.mul_apply]
    exact om_subst H hγ (H.om_pres _ _ hv) w
  have h1 : a • IndefiniteRowSideFullHecke.FrameConstantVectors.frameVec om' vac h = b • IndefiniteRowSideFullHecke.FrameConstantVectors.frameVec om vac h ↔
      ∀ w, a * om' (1, γ * h) vac w = b * om (1, γ * h) vac w := by
    simp only [hs ho, hs ho']
    refine ⟨fun H w => congrFun H _, fun H => funext fun w => ?_⟩
    have := H (actO V W 1 γ w)
    have e1 := Ker.OmRat.actO_inv_cancel (1 : GA D V)⁻¹ γ⁻¹ w
    rw [inv_inv, inv_inv] at e1
    rwa [e1] at this
  rw [h1]
  constructor
  · intro H
    obtain ⟨w, hw0, hne⟩ : ∃ w, Ker.IsRealPt w ∧ om (1, γ * h) vac w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact IndefiniteRowSideFullHecke.FrameConstantVectors.frameVec_ne_zero om hv0 (γ * h) (theta_eq_zero_of_real (ho.om_pres _ _ hv) hcon)
    have e1 := hw w hw0 _ fun _ _ => rfl
    have e2 := hw' w hw0 _ fun _ _ => rfl
    refine mul_right_cancel₀ (right_ne_zero_of_mul (e1 ▸ mul_ne_zero (Complex.exp_ne_zero _) hne)) ?_
    rw [mul_assoc, mul_assoc, ← e1, ← e2, mul_left_comm, H w, mul_left_comm]
  · intro H w
    have hz := theta_eq_zero_of_real (WeilVacMove.isTheta_sub
      (WeilVacMove.isTheta_smul a (ho'.om_pres (1, γ * h) _ hv)) (WeilVacMove.isTheta_smul b (ho.om_pres (1, γ * h) _ hv)))
      fun u hu => by
        have e1 := hw u hu _ fun _ _ => rfl
        have e2 := hw' u hu _ fun _ _ => rfl
        rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        refine (mul_eq_zero.1 ?_).resolve_left (Complex.exp_ne_zero (Real.pi / 2 * ∑ b, hermForm Hm
          (fun j => IndefiniteRowSideFullHecke.WeilTwistColumns.perReal (U.X (dict h).1) (dict h).2 (IndefiniteRowSideFullHecke.WeilTwistColumns.colAt hr (th (dict h).1) u b)
            (relab c σ (e j).1) (e j).2)
          (fun j => IndefiniteRowSideFullHecke.WeilTwistColumns.perReal (U.X (dict h).1) (dict h).2 (IndefiniteRowSideFullHecke.WeilTwistColumns.colAt hr (th (dict h).1) u b)
            (relab c σ (e j).1) (e j).2)))
        rw [mul_sub, mul_left_comm, e2, mul_left_comm _ b, e1, ← mul_assoc, ← mul_assoc, H, sub_self]
    exact sub_eq_zero.1 (congrFun hz w)

theorem cXi_value {n : ℕ} {W : HSp D} {hr : W.rank = r} {T0 : Type} {dδ : T0 → DeltaDat Xo c n}
    {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r}
    {dict₂ : ∀ t, GA D W → Σ k, Frame ((U₂ t).X k).Ψ r} {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ}
    (h : CXiVal W hr σ dδ U₂ dict₂ ι x₀ xi) :
    ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧ ∀ t g, ∃ γ ∈ GQ W, IndefiniteRowSideFullHecke.WeilTwistColumns.cXi (dδ t) (U₂ t) (dict₂ t) g =
      c0 * ((xi t (Matrix.GeneralLinearGroup.det (finHom W (γ * g))) : ℂˣ) : ℂ) := by
  obtain ⟨c0, hc, H⟩ := h
  refine ⟨c0, hc, fun t g => ?_⟩
  obtain ⟨-, -, _, _, _, _, _, _, -, hD, hval⟩ := H t
  obtain ⟨γ, hγ, h1, h2, -⟩ := hD.2 g
  exact ⟨γ, hγ, hval g γ ⟨hγ, h1, h2⟩⟩

end Const

end GlobalTheory.TwistFactorCompare

end
