import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilDoublingFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaGlobalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianThetaImagesAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaContinuationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableLineDerivativeStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DarbImage

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pure_add {κ : Type} [Fintype κ] (f g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul {κ : Type} [Fintype κ] (c : ℂ) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pure_zero {κ : Type} [Fintype κ] (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) φ = 0 := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]

theorem map_eq {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w)
    {Q : Type} [AddCommGroup Q] [Module ℂ Q] (Th : ((Fin n × Fin d → AF F) → ℂ) → Q)
    (T : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] Q) (Alg : Submodule ℂ Q)
    (hsub : GlobalTheory.TripleAssembly.darbAlg M ψ τ ≤ GlobalTheory.WeilM.schA F (Fin n × Fin d))
    (hT : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ = Th Φ)
    (hvac : ∀ (f₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      M.IsGauss ψ τ f₀ → (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      Th (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) ∈ Alg)
    (hder : ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ)
      (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      f ∈ M.Pol ψ τ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) f f₁ →
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      Th (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ Alg → Th (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ) ∈ Alg)
    (hrev : Alg ≤ (GlobalTheory.TripleAssembly.darbAlg M ψ τ).map T) :
    (GlobalTheory.TripleAssembly.darbAlg M ψ τ).map T = Alg := by
  refine le_antisymm ?_ hrev
  have hmem : ∀ f ∈ M.Pol ψ τ, ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = Th (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := fun f hf φ h1 h2 =>
    hT _ (hsub (Submodule.subset_span ⟨f, φ, hf, h1, h2, rfl⟩))
  have hG : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hC : ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → ∀ f ∈ M.Pol ψ τ,
      ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ :=
    fun u hu f hf f₁ hA => Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ hA
  let N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) :=
    { carrier := {f | f ∈ M.Pol ψ τ ∧ ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ Alg}
      add_mem' := fun {f g} hf hg => ⟨(M.Pol ψ τ).add_mem hf.1 hg.1, fun φ h1 h2 => by
        rw [pure_add, map_add]; exact Alg.add_mem (hf.2 φ h1 h2) (hg.2 φ h1 h2)⟩
      zero_mem' := ⟨(M.Pol ψ τ).zero_mem, fun φ _ _ => by rw [pure_zero, map_zero]; exact Alg.zero_mem⟩
      smul_mem' := fun c f hf => ⟨(M.Pol ψ τ).smul_mem c hf.1, fun φ h1 h2 => by
        rw [pure_smul, map_smul]; exact Alg.smul_mem c (hf.2 φ h1 h2)⟩ }
  have hPN : M.Pol ψ τ ≤ N := sInf_le ⟨fun f₀ h => ⟨hG f₀ h, fun φ h1 h2 => by
      rw [hmem f₀ (hG f₀ h) φ h1 h2]; exact hvac f₀ φ h h1 h2⟩,
    fun u hu f hf f₁ hA => ⟨hC u hu f hf.1 f₁ hA, fun φ h1 h2 => by
      rw [hmem f₁ (hC u hu f hf.1 f₁ hA) φ h1 h2]
      exact hder f φ u f₁ hf.1 hu hA h1 h2 (by rw [← hmem f hf.1 φ h1 h2]; exact hf.2 φ h1 h2)⟩⟩
  rw [Submodule.map_le_iff_le_comap]
  unfold GlobalTheory.TripleAssembly.darbAlg
  rw [Submodule.span_le]
  rintro Φ ⟨f, φ, hf, h1, h2, rfl⟩
  exact (hPN hf).2 φ h1 h2

end Generic

end GlobalTheory.DarbImage

namespace GlobalTheory.DarbImage

theorem thetaImage : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ T : ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) →ₗ[ℂ] (WO W X → ℂ),
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
            T Φ = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Φ) →
          (GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb).map T = algF ψ θ true A B) ∧
        ∀ T : ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) →ₗ[ℂ] (WO W₁ X → ℂ),
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)),
            T Φ = GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Φ) →
          (GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb).map T = algF ψ θ false A₁ B := by
  intro hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have hG : Γ.M.IsGood Bs.ψ := hM.triple.geo.hM
  have hG' : Γ.M'.IsGood Bs.ψ := hM.triple.geo.hM'
  have hs := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb hG
  have hs' := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb hG'
  refine ⟨fun T hT => ?_, fun T hT => ?_⟩
  · refine map_eq Γ.M Bs.ψ Bs.emb _ T _ hs hT
      (GlobalTheory.T.seesaw_weil_doubling_factor hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM)
      (fun f φ u f₁ hf hu hA h1 h2 hin => ?_) ?_
    · obtain ⟨L, hLc, hLf, hL⟩ := GlobalTheory.T.seesaw_weil_zeta_unramified hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM f φ u f₁ hf hu hA h1 h2
      rw [hL]
      exact GlobalTheory.T.fockAlgebraicThetaVectors_stable_lineDerivative D ψ θ hψ hθ true W X A B _ hin L hLc hLf
    · rw [algF, Submodule.span_le]
      rintro q ⟨g, P, hg, rfl⟩
      obtain ⟨Φ, hΦ, hΦe⟩ := GlobalTheory.T.seesaw_weil_zeta_global hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM g P hg
      exact ⟨Φ, hΦ, by rw [hT Φ (hs hΦ), hΦe]⟩
  · refine map_eq Γ.M' Bs.ψ Bs.emb _ T _ hs' hT
      (GlobalTheory.T.seesaw_weil_zeta_nonvanishing hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM)
      (fun f φ u f₁ hf hu hA h1 h2 hin => ?_) ?_
    · obtain ⟨L, hLc, hLf, hL⟩ := GlobalTheory.T.seesaw_weil_zeta_continuation hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM f φ u f₁ hf hu hA h1 h2
      rw [hL]
      exact GlobalTheory.T.fockAlgebraicThetaVectors_stable_lineDerivative D ψ θ hψ hθ false W₁ X A₁ B _ hin L hLc hLf
    · rw [algF, Submodule.span_le]
      rintro q ⟨g, P, hg, rfl⟩
      obtain ⟨Φ, hΦ, hΦe⟩ := GlobalTheory.T.exists_darbAlg_thO_eq_fockF' hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM g P hg
      exact ⟨Φ, hΦ, by rw [hT Φ (hs' hΦ), hΦe]⟩

end GlobalTheory.DarbImage

end
