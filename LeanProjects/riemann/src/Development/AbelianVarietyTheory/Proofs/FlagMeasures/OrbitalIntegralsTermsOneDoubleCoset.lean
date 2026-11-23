import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameNormal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormTransp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCosetStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.CosetOrbital

open Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.Pf.FormTranspose

theorem sum_norm_sq_basis_indep {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {ι : Type} [Fintype ι] (T : Wq →L[ℂ] Wp) (b e : OrthonormalBasis ι ℂ Wq) :
    ∑ i, ‖T (b i)‖ ^ 2 = ∑ i, ‖T (e i)‖ ^ 2 := by
  haveI := FiniteDimensional.complete ℂ Wq
  haveI := FiniteDimensional.complete ℂ Wp
  set c := stdOrthonormalBasis ℂ Wp
  have key : ∀ f : OrthonormalBasis ι ℂ Wq,
      ∑ i, ‖T (f i)‖ ^ 2 = ∑ k, ‖ContinuousLinearMap.adjoint T (c k)‖ ^ 2 := by
    intro f
    have h1 : ∀ i, ‖T (f i)‖ ^ 2 = ∑ k, ‖⟪ContinuousLinearMap.adjoint T (c k), f i⟫_ℂ‖ ^ 2 := by
      intro i
      rw [← c.sum_sq_norm_inner_right (T (f i))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ContinuousLinearMap.adjoint_inner_left]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact f.sum_sq_norm_inner_left _
  rw [key b, key e]

theorem norm_hsEmb_unitary {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (c : ℂ) (hc : ‖c‖ = 1) (A : Wp ≃ₗᵢ[ℂ] Wp) (B : Wq ≃ₗᵢ[ℂ] Wq) (O : Wq →L[ℂ] Wp) :
    ‖Formalism.L2.SG.PackageTie.hsEmb (c • ((A.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp
      (O.comp (B.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq))))‖ =
      ‖Formalism.L2.SG.PackageTie.hsEmb O‖ := by
  have hsq : ∀ T : Wq →L[ℂ] Wp, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ ^ 2 =
      ∑ i, ‖T (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
    intro T
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Formalism.L2.SG.PackageTie.hsEmb]
  have h2 : ‖Formalism.L2.SG.PackageTie.hsEmb (c • ((A.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp
      (O.comp (B.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq))))‖ ^ 2 =
      ‖Formalism.L2.SG.PackageTie.hsEmb O‖ ^ 2 := by
    rw [hsq, hsq]
    have e1 : ∀ i, ‖(c • ((A.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp
        (O.comp (B.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq)))) (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 =
        ‖O (((stdOrthonormalBasis ℂ Wq).map B.symm) i)‖ ^ 2 := by
      intro i
      simp [norm_smul, hc]
    simp_rw [e1]
    exact sum_norm_sq_basis_indep O _ _
  have h0 : 0 ≤ ‖Formalism.L2.SG.PackageTie.hsEmb O‖ := norm_nonneg _
  have h0' := norm_nonneg (Formalism.L2.SG.PackageTie.hsEmb (c • ((A.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp
      (O.comp (B.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq)))))
  nlinarith [sq_nonneg (‖Formalism.L2.SG.PackageTie.hsEmb O‖ - ‖Formalism.L2.SG.PackageTie.hsEmb (c • ((A.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp
      (O.comp (B.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq))))‖)]

variable {D : D7} (X : HidaSetting D)

theorem psi_inv (u : D.what₂.Word) {n : X.B.I.Ginf} (hn : n ∈ X.NinfU u) :
    X.psiInfU u n⁻¹ = (X.psiInfU u n)⁻¹ := by
  have hC := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  have hne : ∀ s, X.psiInfU u s ≠ 0 := by
    intro s h0; have := psiInfU_norm X u s; rw [h0, norm_zero] at this; exact zero_ne_one this
  have h1 : X.psiInfU u 1 = 1 := by
    have e := (hC.2.1 1 hC.1 1 hC.1).2
    rw [one_mul] at e
    have e2 : X.psiInfU u 1 * (X.psiInfU u 1 - 1) = 0 := by rw [mul_sub, ← e]; ring
    rcases mul_eq_zero.1 e2 with h | h
    · exact absurd h (hne 1)
    · exact sub_eq_zero.1 h
  have e := (hC.2.1 n hn n⁻¹ (hC.2.2 n hn)).2
  rw [mul_inv_cancel, h1] at e
  exact eq_inv_of_mul_eq_one_right e.symm

end GlobalTheory.CosetOrbital

namespace GlobalTheory.CosetOrbital
open Formalism.L2.SG.Pf.FormTranspose

theorem wu_move {D : D7} (X : HidaSetting D) (v : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.NinfU v) (h : X.B.I.Ginf)
    (hh : h ∈ X.SinfU v) (x : X.B.I.Ginf) :
    X.Wu v ((s⁻¹ * h) * x) = (X.psiInfU v s⁻¹ * X.psiInfU v h) •
      (Formalism.L2.SG.RealObj.InfCut.piIso X v h hh) (X.Wu v x) := by
  have hNS : ∀ {s : X.B.I.Ginf}, s ∈ X.NinfU v → s ∈ X.SinfU v := fun hs p => (hs p).1
  have hsi : s⁻¹ ∈ X.NinfU v := ninf_inv X v hs
  rw [mul_assoc, (X.Wu_spec v).1 s⁻¹ (hNS hsi) (h * x), (X.piU_rep v).2.2.2.1 s⁻¹ hsi,
    ContinuousLinearMap.one_apply, (X.Wu_spec v).1 h hh x, Formalism.L2.SG.RealObj.InfCut.piIso_apply, smul_smul]
  rfl

end GlobalTheory.CosetOrbital

namespace GlobalTheory.CosetOrbital

open Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.Pf.FormTranspose Set

variable {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)

theorem pinned_form (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hP : Formalism.L2.SG.RealObj.NuQPin X u u' νq)
    (t : TauC Y u u') (hrel : t.relevant) (w : Point D.host.E (D.R.rS + 1))
    (hreal : ∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ)
    (g : X.B.I.Ginf) (hg : g ∈ X.SinfU u) (g' : X.B.I.Ginf) (hg' : g' ∈ X.SinfU u')
    (hdec : t.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' w * g'⁻¹) :
    ∃ μR : Measure X.B.I.Ginf, Formalism.L2.SG.VolPin.IsPinnedR t w μR ∧
      (MeasurableSet (FundOf t) ∧ ∀ y ∈ Rset t, ∃! s, s ∈ ROinf t ∧ s * y ∈ FundOf t) ∧
      OOt t = (μR (FundOf t)).toReal •
        (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
         OO ((νq (Formalism.L2.SG.RealObj.gamW X u u' w)).map (fun x => g * x)) Set.univ (X.Wu u) (X.Wu u') t.pt.1) := by
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  set γw := Formalism.L2.SG.RealObj.gamW X u u' w with hγw
  have hγwP : Formalism.L2.SG.RealObj.IsPtRep X u u' w γw := by
    simp only [hγw, Formalism.L2.SG.RealObj.gamW, dif_pos hreal]; exact hreal.choose_spec
  obtain ⟨μw, hμwH, hμwQ, hμwS⟩ := hP.2 w hreal
  set cj : X.B.I.Ginf → X.B.I.Ginf := fun y => g * y * g⁻¹ with hcj
  have hcjm : Measurable cj := (measurable_const_mul g).mul_const g⁻¹
  set μR := μw.map cj with hμR
  set ν := (νq γw).map (fun x => g * x) with hν
  have hRset : ∀ z, cj z ∈ Rset t ↔ z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := by
    intro z
    have e2 : t.pt.1⁻¹ * (g * z * g⁻¹) * t.pt.1 = g' * (γw⁻¹ * z * γw) * g'⁻¹ := by
      rw [show t.pt.1 = g * γw * g'⁻¹ from hdec]; group
    show (g * z * g⁻¹ ∈ X.NinfU u ∧ t.pt.1⁻¹ * (g * z * g⁻¹) * t.pt.1 ∈ X.NinfU u') ↔
      (z ∈ X.NinfU u ∧ γw⁻¹ * z * γw ∈ X.NinfU u')
    rw [e2, sinf_conj_iff X u hg, sinf_conj_iff X u' hg']
  have hHaar : IsHaarOnSet X.B.I (Rset t) μR := by
    obtain ⟨h1, h2, h3, h4⟩ := hμwH
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : SigmaFinite μw := h1
      exact ((MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)).sigmaFinite_map
    · intro h0
      apply h2
      have := congrArg (fun m : Measure X.B.I.Ginf => m univ) h0
      simp only [hμR, Measure.map_apply hcjm MeasurableSet.univ, preimage_univ, Measure.coe_zero,
        Pi.zero_apply] at this
      exact Measure.measure_univ_eq_zero.1 this
    · have hcje : ⇑((MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)) = cj := rfl
      rw [hμR, ← hcje, MeasurableEquiv.map_apply]
      refine measure_mono_null (fun z hz => ?_) h3
      intro hzS; exact hz ((hRset z).2 hzS)
    · intro r hr
      set z := g⁻¹ * r * g with hz
      have hcz : cj z = r := by simp only [hcj, hz]; group
      have hzS : z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := (hRset z).1 (hcz ▸ hr)
      have hcomp : (fun y => r * y) ∘ cj = cj ∘ (fun y => z * y) := by
        funext y; simp only [Function.comp, hcj, hz]; group
      rw [hμR, Measure.map_map (measurable_const_mul r) hcjm, hcomp,
        ← Measure.map_map hcjm (measurable_const_mul z), h4 z hzS]
  have hmulm : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_mul
  have hQ' : IsQuotMeasS X.B.I μR ν := by
    intro f hf
    have hσ : SigmaFinite μw := hμwH.1
    have hσR : SigmaFinite μR := hHaar.1
    have hF : Measurable fun x => ∫⁻ s, f (s * x) ∂μR := (hf.comp hmulm).lintegral_prod_left'
    rw [hν, lintegral_map hF (measurable_const_mul g)]
    have e1 : ∀ x0, ∫⁻ s, f (s * (g * x0)) ∂μR = ∫⁻ z, (fun y => f (g * y)) (z * x0) ∂μw := by
      intro x0
      rw [hμR, lintegral_map (f := fun s => f (s * (g * x0))) (hf.comp (measurable_mul_const _)) hcjm]
      refine lintegral_congr fun z => ?_
      simp only [hcj]
      congr 1
      group
    simp only [e1]
    rw [← hμwQ (fun y => f (g * y)) (hf.comp (measurable_const_mul g))]
    exact (lintegral_mul_left_eq_self f g).symm
  have hFE : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u' t
  have hFO : IsSFund X.B.I (ROinf t) (FundOf t) := by
    unfold FundOf; rw [dif_pos hFE]; exact hFE.choose_spec
  set Γ0 := ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin with hΓ0
  have hKu : ∀ r ∈ Rset t, ∃! s, s ∈ ROinf t ∧ s * r ∈ FundOf t := by
    intro r _
    obtain ⟨s0, hs0, hs0F⟩ := hFO.2.1 r
    refine ⟨s0, ⟨hs0, hs0F⟩, fun s' ⟨hs', hs'F⟩ => ?_⟩
    have h2 : (s0 * s'⁻¹) * (s' * r) ∈ FundOf t := by simpa [mul_assoc] using hs0F
    have := hFO.2.2 _ hs'F _ (Γ0.mul_mem hs0 (Γ0.inv_mem hs')) h2
    exact (mul_inv_eq_one.1 this).symm
  have hFA := Formalism.L2.SG.Pf.formAllC_holds D X Y u u' t μR ν (FundOf t)
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u' t hrel) hHaar hQ' hFO.1 hKu
  exact ⟨μR, ⟨γw, g, g', μw, hγwP, hg, hg', hdec, hμwH, hμwS, rfl⟩, ⟨hFO.1, hKu⟩, hFA⟩

end GlobalTheory.CosetOrbital

namespace GlobalTheory.CosetOrbital

open Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.Pf.FormTranspose

theorem conj_inv_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) : conj (z⁻¹) = z := by
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have h1 : conj z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [map_inv₀]
  exact inv_eq_of_mul_eq_one_right h1

theorem coset_orbital_form : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ t₀ : TauC Y u u', t₀.relevant → t₀.G ≠ 0 → ∀ w, w = Formalism.L2.SG.PairVal.ptOf t₀.toTerm → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧ ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u); OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' w))‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (xn xm : X.B.I.GA), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → RatLink X xn n → RatLink X xm m → ∃ (μR : Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), Formalism.L2.SG.VolPin.IsPinnedR t w μR ∧ (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ ROinf t ∧ s * y ∈ K) ∧ OOt t = (((μR K).toReal : ℂ) * ((X.psiInfU u xn.1)⁻¹ * X.psiInfU u' xm.1)) • T := by
  intro D X Y u u' hSt ν hν t₀ hrel₀ hG₀ w hw
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  have hRD := Formalism.L2.SG.Pf.RowForm.RealDecompL.realDecompC_of X Y u u'
    (Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := Formalism.L2.SG.Pf.RowForm.realDecompC_gamW X Y u u' hRD t₀ hrel₀ hG₀
  subst hw
  set O := OO (ν (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm))) Set.univ (X.Wu u) (X.Wu u')
    (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm)) with hO
  set A := Formalism.L2.SG.RealObj.InfCut.piIso X u g hg with hA
  set B := Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg' with hB
  set c0 := X.psiInfU u g * conj (X.psiInfU u' g') with hc0
  have hc0n : ‖c0‖ = 1 := by
    rw [hc0, norm_mul, Complex.norm_conj, psiInfU_norm, psiInfU_norm, one_mul]
  refine ⟨hpt, c0 • ((A.toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u).comp
    (O.comp (B.symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'))), norm_hsEmb_unitary c0 hc0n A B O, ?_⟩
  rintro t n m xn xm ⟨hn, hm, hlin⟩ hxn hxm
  obtain ⟨hrel, -, hptt, -⟩ := GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset D X Y u u' hSt t₀ t n m hrel₀ hG₀ ⟨hn, hm, hlin⟩
  have hL := GlobalTheory.RatIsomPoint.ratLink_points D X
  have hxnN : xn.1 ∈ X.NinfU u := ((hL.2.2 u xn n hxn).1).1 hn
  have hxmN : xm.1 ∈ X.NinfU u' := ((hL.2.2 u' xm m hxm).1).1 hm
  have hlink : RatLink X (xn⁻¹ * t₀.pt * xm) t.lin := by
    rw [hlin]
    have h1 := (hL.2.1 _ _ _ _ hxn t₀.rep.2.1).2.1
    exact (hL.2.1 _ _ _ _ (hL.2.1 _ _ _ _ h1 t₀.rep.2.1).1 hxm).1
  have hpt_eq : t.pt = xn⁻¹ * t₀.pt * xm := (hL.1 t.lin t.rep.2.2.1).unique t.rep.2.1 hlink
  have hpt1 : t.pt.1 = xn.1⁻¹ * t₀.pt.1 * xm.1 := by rw [hpt_eq]; rfl
  have hNS : ∀ (v : D.what₂.Word) {s : X.B.I.Ginf}, s ∈ X.NinfU v → s ∈ X.SinfU v := fun v s hs => fun p => (hs p).1
  have hgt : xn.1⁻¹ * g ∈ X.SinfU u :=
    (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)).mul_mem (hNS u (ninf_inv X u hxnN)) hg
  have hgt' : xm.1⁻¹ * g' ∈ X.SinfU u' :=
    (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u')).mul_mem (hNS u' (ninf_inv X u' hxmN)) hg'
  have hdect : t.pt.1 = (xn.1⁻¹ * g) * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm) *
      (xm.1⁻¹ * g')⁻¹ := by
    rw [hpt1, hdec]; group
  obtain ⟨μR, hPin, hK, hFA⟩ := pinned_form X Y u u' ν hν t hrel _ hpt _ hgt _ hgt' hdect
  refine ⟨μR, FundOf t, hPin, hK, ?_⟩

  have hmove := Formalism.L2.SG.Pf.RowForm.ClassFrameNormal.oo_map_mulLeft
    (ν (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm))) (X.Wu u) (X.Wu u')
    (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm)) (xn.1⁻¹ * g) (xm.1⁻¹ * g')
    (X.psiInfU u xn.1⁻¹ * X.psiInfU u g) (X.psiInfU u' xm.1⁻¹ * X.psiInfU u' g') A B
    (wu_move X u xn.1 hxnN g hg) (wu_move X u' xm.1 hxmN g' hg')
  rw [hFA, hdect, hmove]
  rw [psi_inv X u hxnN, psi_inv X u' hxmN, map_mul, conj_inv_of_norm_one _ (psiInfU_norm X u' xm.1),
    ← Complex.coe_smul, smul_smul, smul_smul, hc0]
  congr 1
  ring

end GlobalTheory.CosetOrbital
