import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchLineTransposeGramUnitaryEqExpStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.LieLines

theorem line_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X)
    (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ), IsInfFam θ →
    IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
    ∀ (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
      (hJ : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws,
      ∃ (h : ℝ → GA D X) (Y : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ τ, Y τ ∈ lieAt X τ) ∧
        (∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (h t)) ∧
        ∀ f₀ : WO (sgn ε M) X → ℂ, IsVacF ψ θ (frSgn ε A) B f₀ → ∀ (P : PolF D X.rank M.rank) (z : WO (sgn ε M) X),
          HasDerivAt (fun t : ℝ => ω (1, h t) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z)
            (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (∑ τ, GlobalTheory.RealQuot.actT ε A B eS τ (Y τ) P) z) 0 := by
  classical
  intro D ψ θ ε M X A B χS χT ω eS eT hθ hω hexp Ws hJ γ hγ
  obtain ⟨L, hL⟩ : ∃ L : GlobalTheory.SmoothForms.LieN X, ∀ t : ℝ, γ (Multiplicative.ofAdd t) =
      GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (GlobalTheory.SmoothForms.expInf θ X (t • L)) :=
    GlobalTheory.T.archLine_transposeGramUnitary_eq_exp D θ hθ X Ws hJ γ hγ
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ X
  refine ⟨fun t => GlobalTheory.SmoothForms.expInf θ X (t • L), fun τ => (L τ).1, fun τ => (L τ).2, hL, ?_⟩
  intro f₀ hf P z
  have hω' : IsWeilDatumO ψ (sgn ε M) X χS χT (WRep.toSgn ε ω) := hω
  have hψ := hω'.std
  have h1g : ∀ (g : GA D X), WRep.toSgn ε ω (1, g) = ω (1, g) := fun g => by
    simp [WRep.toSgn]
  have hlin : ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (∑ τ, GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) =
      ∑ τ, ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) := map_sum _ _ _
  rcases isEmpty_or_nonempty D.what₂.Tau with hT | ⟨⟨τ₀⟩⟩
  · have e : ∀ t : ℝ, t • L = L := fun t => funext fun τ => (IsEmpty.false τ).elim
    simp only [e, hlin, Finset.univ_eq_empty, Finset.sum_empty, Pi.zero_apply]
    exact hasDerivAt_const _ _
  have hth : ∀ Q, IsThetaFunO ψ (sgn ε M) X (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ Q) :=
    (GlobalTheory.LieScalar.ptF_laws hθ hψ (frSgn ε A) B hf).1 τ₀
  let 𝒮 : Set (GA D X → ℂ) :=
    {φ | ∃ f z, IsThetaFunO ψ (sgn ε M) X f ∧ φ = fun g => WRep.toSgn ε ω (1, g) f z}
  have hc : ∀ φ ∈ 𝒮, Continuous φ := by
    rintro _ ⟨f, z, hf, rfl⟩
    exact (hω'.om_cont f hf z).comp (continuous_const.prodMk continuous_id)
  have hd : ∀ φ ∈ 𝒮, ∀ τ', ∀ Z ∈ lieAt X τ', ∃ φ' ∈ 𝒮, ∀ g,
      HasDerivAt (fun t : ℝ => φ (g * oneP θ X τ' Z t)) (φ' g) 0 := by
    rintro _ ⟨f, z, hf, rfl⟩ τ' Z hZ
    obtain ⟨G, hG', h⟩ := GlobalTheory.LieScalar.genT hθ hω' τ' Z hZ f hf
    refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
    have := h (MonoidHom.inr (GA D (sgn ε M)) (GA D X) g) z
    simpa only [MonoidHom.inr_apply, Prod.mk_mul_mk, mul_one] using this
  let φ : GA D X → ℂ := fun g => WRep.toSgn ε ω (1, g) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z
  have hφ : φ ∈ 𝒮 := ⟨_, z, hth P, rfl⟩
  have h1 := GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ X 𝒮 hc hd φ hφ
  have h2 : GlobalTheory.SmoothForms.Sm (GlobalTheory.SmoothForms.expInf θ X) φ :=
    (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 h1)
  have h3 := ((h2 1).differentiable (by simp) 0).hasFDerivAt
  have hline : ∀ V : GlobalTheory.SmoothForms.LieN X, HasDerivAt (fun t : ℝ => φ (GlobalTheory.SmoothForms.expInf θ X (t • V)))
      (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 V) 0 := by
    intro V
    have h4 : HasDerivAt (fun t : ℝ => t • V) V 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).smul_const V
      rwa [one_smul] at h
    have h3' : HasFDerivAt (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y))
        (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0) ((0 : ℝ) • V) := by
      rw [zero_smul]
      exact h3
    have h5 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h3' h4
    simpa only [Function.comp_def, one_mul] using h5
  have hτ : ∀ τ, fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0
      (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X) =
      ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) z := by
    intro τ
    have hl := (GlobalTheory.LieScalar.lieFockAll D (sgn ε M) X (frSgn ε A) B θ ψ χS χT (WRep.toSgn ε ω) f₀ τ (eS τ) (eT τ)
      hθ hω' (hexp τ).1 (hexp τ).2 hf).2 (L τ).1 (L τ).2 P z
    have e := (hline (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X)).unique
      (hl.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        show φ _ = _
        simp only [φ]
        rw [GlobalTheory.SmoothForms.oneP_eq R τ (L τ) t]
        rfl))
    rw [e]
    rfl
  have hsum : ∑ τ, (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X) = L := Finset.univ_sum_single L
  have e1 : (fun t : ℝ => ω (1, GlobalTheory.SmoothForms.expInf θ X (t • L)) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z) =
      fun t => φ (GlobalTheory.SmoothForms.expInf θ X (t • L)) := funext fun t => by simp only [φ, h1g]
  rw [e1, hlin, Finset.sum_apply]
  have e2 : fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 L =
      ∑ τ, ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) z := by
    have h7 := map_sum (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0)
      (fun τ => (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X)) Finset.univ
    have h8 : fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 L =
        fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0
          (∑ τ, (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X)) := by
      congr 1
      exact hsum.symm
    have h9 : fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 L =
        ∑ τ, fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0
          (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X) := by
      exact h8.trans h7
    rw [h9]
    exact Finset.sum_congr rfl fun τ _ => hτ τ
  have h6 := hline L
  rwa [e2] at h6

end GlobalTheory.LieLines

end
