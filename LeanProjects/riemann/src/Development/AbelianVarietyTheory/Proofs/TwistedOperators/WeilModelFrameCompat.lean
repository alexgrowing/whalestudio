import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelHermitianScalingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplaceStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealDict

theorem lieDer_mem_coinv : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
          f₁ ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ := by
  intro hPr D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs Ws Mo ψ' χX χW om τ hP hR Φ hinj hrange hF γ hγ f hf f₁ hact
  obtain ⟨hcm, hstd, hherm, hdetX, hskew, hdetW, -, -, -, -, hweil, -, -⟩ := hP
  have hpsi := hR.psi
  subst hpsi
  obtain ⟨f₀, r, hvac, hne, hFr⟩ := hF
  rw [← hrange] at hf
  obtain ⟨P, rfl⟩ := hf
  obtain ⟨g, hg, hder⟩ := GlobalTheory.T.weil_model_hermitian_scaling hPr D ψ' θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs hR.JX f₀ hvac γ hγ
  obtain ⟨Q, hQ, hQd⟩ := hder P
  have hGM : M.gram.det ≠ 0 := by
    intro h0
    apply hdetX
    rw [hR.JX, Matrix.det_smul, h0, mul_zero]
  have hG : (sgn ε M).gram.det ≠ 0 := by
    cases ε
    · exact hGM
    · change (-M.gram).det ≠ 0
      rw [Matrix.det_neg]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hGM
  obtain ⟨T, hT, hTinj⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Mo ψ' (sgn ε M).gram (Equiv.refl _) hR.good hstd hdetX hdetW hG
  have hΦ1 : Φ 1 ≠ 0 := fun h => one_ne_zero (hinj (h.trans (map_zero Φ).symm))
  have hRf₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r := GlobalTheory.T.complementaryAdelicSchwartz_archimedean_replace _ f₁ r (hFr 1).1 hΦ1
  have hRQ := (hFr Q).1
  have hone : GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hR.JW 1 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show (GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hR.JW 1).1.1 = 1
    rw [GlobalTheory.TripleRead.toUX_val, GlobalTheory.WeilVacMove.mt_one]
    exact Matrix.submatrix_one_equiv _
  have key : ∀ x, GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl _) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) x =
      GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl _) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ Q) r) x := by
    intro x
    have h1 := GlobalTheory.T.weil_line_good_model hPr Mo ψ' χX χW om hstd hR.good hweil γ hγ (Φ P) f₁ r (hFr P).1 hact
      (GlobalTheory.TripleRead.ptO (sgn ε M).gram (Equiv.refl _) x)
    have h2 : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum D.host.F (Mo.co.rho ψ' (GlobalTheory.TripleRead.ptO (sgn ε M).gram (Equiv.refl _) x)
        (om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r))) =
        ω (g t, 1) (ptF (V := sgn ε M) ψ' θ (frSgn ε A) B f₀ P) x := by
      intro t
      have h3 := hR.transp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r) (hFr P).1.2 (g t) 1
      rw [hg t, hone, (hFr P).2] at h3
      exact congrFun h3 x
    simp only [h2] at h1
    have h4 := h1.unique (hQd x)
    rw [(hFr Q).2]
    exact h4
  obtain ⟨d, hd⟩ : ∃ d : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank), d = f₁ - Φ Q := ⟨_, rfl⟩
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) d r =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ Q) r := by
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, sub_mul, hd]
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) d r ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin X.rank) := by
    rw [e1]; exact sub_mem hRf₁.2 hRQ.2
  have hT0 : T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) d r) = 0 := by
    rw [e1, map_sub, hT _ hRf₁.2, hT _ hRQ.2, funext key, sub_self]
  have hz := hTinj _ hmem hT0
  have hr : ∃ x₀, r x₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ 1) r = 0 := funext fun x => by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hcon]
    have h2 := (hFr 1).2
    rw [h0, ← hT 0 (zero_mem _), map_zero, GlobalTheory.LieScalar.ptF_one] at h2
    exact hne h2.symm
  have hfeq : f₁ = Φ Q := by
    obtain ⟨x₀, hx₀⟩ := hr
    rw [← sub_eq_zero, ← hd]
    refine DFunLike.ext _ _ fun y => ?_
    let z : Fin M.rank × Fin X.rank → AF D.host.F := fun i => LinearMap.inl D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (x₀ i)))
    have hzAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) z := by
      intro u hu
      have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective (by rw [map_zero]; exact hu)
      funext i
      show u * z i = 0
      refine Prod.ext ?_ ?_
      · show u.1 * (z i).1 = 0
        rw [hu1, zero_mul]
      · show u.2 * (z i).2 = 0
        simp [z]
    have hev : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F ((x₀ + z) i)) = y := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F ((x₀ i).1 + (z i).1) = y i
      rw [map_add]
      show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (x₀ i) + InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
        ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (x₀ i))) = y i
      rw [RingEquiv.apply_symm_apply, add_sub_cancel]
    have h5 := congrFun hz (x₀ + z)
    have h6 : r (x₀ + z) = r x₀ := (hFr 1).1.1 x₀ z hzAt
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.zero_apply] at h5
    rw [hev, h6] at h5
    simpa [hx₀] using h5
  rw [hfeq]
  exact Submodule.mem_map_of_mem hQ

end GlobalTheory.RealDict
