import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSerA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutDef
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GamQFEqOneIffK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsStdCharFOfIsGoodK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HermitianFormSelfadjointGlobal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutLat

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
open scoped ContDiff
namespace SerA
theorem sig_sig'_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
theorem chi_add_lat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ))
    (hw : w + sgOF σ w = 1) {u : XFF F E nS nT} (hu : u ∈ latF F E nS nT Λ) (x : WOF F E nS nT) :
    phaseF σ JS JT ξ₀ B.ψ w u * (B.ψ (symplOHF σ JS JT ξ₀ x u) * chiLatF σ JS JT ξ₀ B.ψ Λ w (x + u)) =
      chiLatF σ JS JT ξ₀ B.ψ Λ w x := by
  have hσ := _root_.PositivityTheory.ThKW.SerA.sig_sig'_k C.good
  have e : finIdem F E • (x + (u : WOF F E nS nT)) = finIdem F E • x + u := by
    rw [smul_add, finIdem_smul_of_fin u.fin]
  have e2 : B.ψ (symplOHF σ JS JT ξ₀ x u) = B.ψ (symplOHF σ JS JT ξ₀ (finIdem F E • x) u) := by
    have hx := finIdem_add_iota C.chart x
    have h3 := _root_.PositivityTheory.ThKW.beta_iota_left_k C (piWF θ x) (u : WOF F E nS nT)
    rw [piWF_fin u.fin, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h3
    conv_lhs => rw [hx]
    rw [GlobalTheory.HeisLineF.symplOHF_add_left, AddChar.map_add_eq_mul, h3, mul_one]
  unfold chiLatF
  rw [e, e2]
  have hy := finIdem_smul_fin (F := F) (E := E) x
  generalize finIdem F E • x = y at hy ⊢
  by_cases h : y ∈ latOF F E nS nT Λ
  · rw [if_pos h, if_pos (add_mem h hu)]
    have h0 : B.ψ (symplOF σ JS JT ξ₀ (intAF F w • y) u) = 1 :=
      (hA _).1 ((latF F E nS nT Λ).smul_mem w (show XFF.mk y hy ∈ latF F E nS nT Λ from h)) u hu
    rw [phaseF, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad hσ C.hS C.hT C.hξ hw,
      AddChar.map_add_eq_mul, h0, mul_one]
  · have h2 : y + (u : WOF F E nS nT) ∉ latOF F E nS nT Λ := fun h' => h (by
      have h3 := sub_mem h' (mem_latF.1 hu)
      rwa [add_sub_cancel_right] at h3)
    rw [if_neg h, if_neg h2, mul_zero, mul_zero]
theorem main_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) (a : IxF F nS nT → ℂ) :
    ∃ hf : IsThetaFunOF σ JS JT ξ₀ B.ψ (serF σ JS JT ξ₀ B θ ι s Λ w a),
      Fixes (opFF hc w) (latF F E nS nT Λ) (⟨_, hf⟩ : thetaSubF σ JS JT ξ₀ B.ψ) ∧
      IsVacF σ JS JT ξ₀ B.ψ ι s (serF σ JS JT ξ₀ B θ ι s Λ w a) := by
  have hσ := _root_.PositivityTheory.ThKW.SerA.sig_sig'_k C.good
  have hψ : IsCharAF F B.ψ := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B C.good).1
  have hA := hO.sd
  have hw := hO.hw
  obtain ⟨-, hJ, hsym, hpos⟩ := omV_laws
    (_root_.PositivityTheory.ThKW.hermitian_form_selfadjoint_global F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ).1 hs.sq hs.pos
  have hl : ∀ x y z : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ (x + y) z) =
      B.ψ (symplOHF σ JS JT ξ₀ x z) * B.ψ (symplOHF σ JS JT ξ₀ y z) :=
    fun x y z => by rw [GlobalTheory.HeisLineF.symplOHF_add_left, AddChar.map_add_eq_mul]
  have hr : ∀ x y z : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ x (y + z)) =
      B.ψ (symplOHF σ JS JT ξ₀ x y) * B.ψ (symplOHF σ JS JT ξ₀ x z) :=
    fun x y z => by rw [GlobalTheory.HeisLineF.symplOHF_add_right, AddChar.map_add_eq_mul]
  have hd : ∀ x : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ x x) = 1 := fun x => by
    rw [symplOHF, GlobalTheory.HeisLineF.symplOF_self σ JS JT hσ C.hS C.hT ξ₀ C.hξ, mul_zero, AddChar.map_zero_eq_one]
  have hβ : ∀ (x : WOF F E nS nT) (v : IxF F nS nT → ℂ), B.ψ (symplOHF σ JS JT ξ₀ x (iotaA ι v)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWA θ x) v : ℝ)) :=
    fun x v => _root_.PositivityTheory.ThKW.beta_iota_right_k C x v
  have fl : ∀ u ∈ latF F E nS nT Λ, ∀ x : WOF F E nS nT, phaseF σ JS JT ξ₀ B.ψ w u *
      (B.ψ (symplOHF σ JS JT ξ₀ x u) * serF σ JS JT ξ₀ B θ ι s Λ w a (x + u)) = serF σ JS JT ξ₀ B θ ι s Λ w a x :=
    fun u hu x => GlobalTheory.GaussSeriesVacuum.series_inv_scalar (G := WOF F E nS nT)
      (β := fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) hl hr hd hβ a u (piWF_fin u.fin) _ (_root_.PositivityTheory.ThKW.SerA.chi_add_lat_k C hA hw hu) x
  obtain ⟨U, hUo, hlev⟩ := exists_level (F := F) (E := E) (nS := nS) (nT := nT) hG 2 two_pos
  let U₀ : AddSubgroup (WOF F E nS nT) :=
    (latOF F E nS nT Λ).comap (DistribSMul.toAddMonoidHom (WOF F E nS nT) (finIdem F E))
  obtain ⟨fc, fs, fv⟩ := GlobalTheory.GaussSeriesVacuum.series_regular (piWA θ) (iotaA ι)
    (fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) (omV (HMF JS JT ξ₀ (tauB B))) (jV s) (ratLF F E nS nT) U₀ U
    (chiLatF σ JS JT ξ₀ B.ψ Λ w) (_root_.PositivityTheory.ThKW.continuous_piWF_k C) (continuous_iotaVF C.chart) (piWF_iotaVF C.chart) hl hr hd
    (fun x y => hψ.2.1 _)
    (hψ.1.comp (GlobalTheory.RealWeilF.continuous_symplOHF σ JS JT ξ₀ continuous_fst continuous_snd)) hβ hJ hsym hpos
    (by
      rintro _ ⟨y, rfl⟩ h
      have e : piWF θ (ratWF (F := F) y) = 0 := h
      rw [_root_.PositivityTheory.ThKW.piWF_ratWF_k C] at e
      have : y = 0 := infRatF_injective B (by rw [e, map_zero])
      subst this
      exact map_zero _)
    (fun R => by
      refine ((_root_.PositivityTheory.ThKW.finite_lat_k C.good hG R).image (fun y => ratWF (F := F) y)).subset ?_
      rintro _ ⟨⟨y, rfl⟩, h1, h2⟩
      refine ⟨y, ⟨(_root_.PositivityTheory.ThKW.finRatF_mem_iff_k C hG hR hA y).1 h1, ?_⟩, rfl⟩
      have e : piWF θ (ratWF (F := F) y) = infRatF (tauB B) y := _root_.PositivityTheory.ThKW.piWF_ratWF_k C y
      rw [← e]
      exact h2)
    (fun x hx => by unfold chiLatF; exact if_neg hx)
    (fun x => by
      unfold chiLatF
      split_ifs
      · exact (hψ.2.1 _).le
      · rw [norm_zero]; exact zero_le_one)
    (fun x v => by
      show chiLatF σ JS JT ξ₀ B.ψ Λ w (x + iotaVF ι v) = _
      unfold chiLatF
      rw [smul_add, finIdem_smul_of_real (real_iotaVF C.chart v), add_zero])
    hUo
    (fun u hu x => by
      obtain ⟨l, hl', e⟩ := hlev u hu
      have e3 : u - iotaA ι (piWA θ u) = ((2 • l : XFF F E nS nT) : WOF F E nS nT) :=
        (sub_eq_of_eq_add (finIdem_add_iota C.chart u)).trans e
      rw [e3]
      have e2 := _root_.PositivityTheory.ThKW.SerA.chi_add_lat_k C hA hw (nsmul_mem hl' 2) x
      rw [phase_two' hA w hl', one_mul] at e2
      exact e2) a
  have hquasi : ∀ (γ : Matrix (Fin nT) (Fin nS) E) (x : WOF F E nS nT),
      serF σ JS JT ξ₀ B θ ι s Λ w a (ratWF γ + x) =
        B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) x)) * serF σ JS JT ξ₀ B θ ι s Λ w a x := by
    intro γ x
    have e : B.ψ (symplOHF σ JS JT ξ₀ (ratWF γ) x) * serF σ JS JT ξ₀ B θ ι s Λ w a (ratWF γ + x) =
        serF σ JS JT ξ₀ B θ ι s Λ w a x :=
      GlobalTheory.HeisenbergGaussianSeries.series_quasi (G := WOF F E nS nT) (p := piWA θ) (ι := iotaA ι)
        (β := fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) (om := omV (HMF JS JT ξ₀ (tauB B))) (J := jV s)
        (Γ := ratLF F E nS nT) (χ := chiLatF σ JS JT ξ₀ B.ψ Λ w) hl hr
        (by rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩; exact _root_.PositivityTheory.ThKW.psi_rat_k C y y') a (ratWF γ) ⟨γ, rfl⟩ x
    rw [← e, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have hlevel : ∀ u ∈ U, u.map (infPartF F E) = 0 →
      heisOF σ JS JT ξ₀ B.ψ u (serF σ JS JT ξ₀ B θ ι s Λ w a) = serF σ JS JT ξ₀ B θ ι s Λ w a := by
    intro u hu h
    obtain ⟨l, hl', e⟩ := hlev u hu
    rw [finIdem_smul_of_fin h] at e
    subst e
    funext x
    have e2 := fl _ (nsmul_mem hl' 2) x
    rw [phase_two' hA w hl', one_mul] at e2
    exact e2
  have hsm : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L → (∀ t, (L t).map (finPartF F E) = 0) →
      ∀ x, ContDiff ℝ ∞ fun t => serF σ JS JT ξ₀ B θ ι s Λ w a (x + L t) := by
    intro k L hL hL0 x
    let c : (Fin k → ℝ) →+ (IxF F nS nT → ℂ) := (piWA θ).comp L
    have hc : Continuous c := (_root_.PositivityTheory.ThKW.continuous_piWF_k C).comp hL
    have hLc : ∀ t, L t = iotaA ι (c t) := fun t => by
      have := finIdem_add_iota C.chart (L t)
      rw [finIdem_smul_of_real (hL0 t), zero_add] at this
      exact this
    have h := (fs x).comp (c.toRealLinearMap hc).contDiff
    refine (congrArg (ContDiff ℝ ∞) (funext fun t => ?_)).mp h
    show _ = serF σ JS JT ξ₀ B θ ι s Λ w a (x + L t)
    rw [hLc t]
    rfl
  refine ⟨⟨hquasi, ⟨U, hUo, hlevel⟩, fc, hsm⟩, fun u hu => Subtype.ext (funext fun x => ?_), fun x z => fv x z⟩
  rw [coe_opFF]
  exact fl u hu x
end SerA
end PositivityTheory.ThKW
end
end
