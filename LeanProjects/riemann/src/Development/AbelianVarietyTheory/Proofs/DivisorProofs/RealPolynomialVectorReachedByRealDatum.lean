import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaTripleProportionalToNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzDatumStableHeisenbergDerivatiStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigNZ.DatReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

section Tens

variable (W : G.Weil) {X Y : Node} {p : Path T X Y}

theorem tensT_zero (τ : TotT G p) : tensT W (0 : PolT G p →₀ ℂ) τ = 0 := Finsupp.sum_zero_index

theorem tensT_add (a b : PolT G p →₀ ℂ) (τ : TotT G p) : tensT W (a + b) τ = tensT W a τ + tensT W b τ := by
  unfold tensT
  refine Finsupp.sum_add_index' (fun P => by simp) (fun P c₁ c₂ => ?_)
  simp only [add_mul, Finsupp.single_add, Finsupp.sum_add]

theorem tensT_smul (c : ℂ) (a : PolT G p →₀ ℂ) (τ : TotT G p) : tensT W (c • a) τ = c • tensT W a τ := by
  unfold tensT
  rw [Finsupp.sum_smul_index' (fun P => by simp), Finsupp.smul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  dsimp only
  rw [Finsupp.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  dsimp only
  rw [Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem fock_one (q : Pair T) (f : WO (G.pS q) (G.pT q) → ℂ) : W.fock q f 1 = f := by
  unfold GridData.Weil.fock pureTensorO pureTensorL
  rw [show (1 : MvPolynomial (FVar D (G.pT q).rank (G.pS q).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 by
    rw [MvPolynomial.coe_basisMonomials]; rfl, Module.Basis.constr_basis]
  simp [opPow]

end Tens

section Datum

variable {t : T} {i j : ℕ} (W : G.Weil) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)

noncomputable def onePol : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) := (((), 1), 1)

theorem tensT_one (τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) : tensT W (Finsupp.single onePol 1) τ = τ := by
  unfold tensT
  rw [Finsupp.sum_single_index (by simp)]
  have hz : ∀ d : PureT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j), Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d onePol = d := by
    rintro ⟨⟨⟨⟩, d₁⟩, d₂⟩
    show (((), W.fock _ d₁ 1), W.fock _ d₂ 1) = (((), d₁), d₂)
    rw [fock_one, fock_one]
  simp only [hz, one_mul]
  exact Finsupp.sum_single τ

theorem isDatumA_zero : IsDatumA W e Γ (0 : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) 0 := by
  refine ⟨Submodule.zero_mem _, fun u => ?_⟩
  have : Γ.M.co.rho W.ψ u 0 = 0 := by
    funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  rw [this, Finsupp.sum_zero_index]
  simp [GlobalTheory.WeilM.thetaSum]

theorem datumA_add (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ) {τ τ' : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)} {Φ Φ'} (h : IsDatumA W e Γ τ Φ)
    (h' : IsDatumA W e Γ τ' Φ') : IsDatumA W e Γ (τ + τ') (Φ + Φ') := by
  refine ⟨add_mem h.1 h'.1, fun u => ?_⟩
  have e1 : Γ.M.co.rho W.ψ u (Φ + Φ') = Γ.M.co.rho W.ψ u Φ + Γ.M.co.rho W.ψ u Φ' := by
    funext x; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply]; ring
  rw [e1, GlobalTheory.WeilM.thetaSum_add _ (GlobalTheory.HeisSchA.rho_mem_schA _ _ hψ _ _ h.1) (GlobalTheory.HeisSchA.rho_mem_schA _ _ hψ _ _ h'.1),
    h.2, h'.2, Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

theorem datumA_smul (c : ℂ) {τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)} {Φ} (h : IsDatumA W e Γ τ Φ) :
    IsDatumA W e Γ (c • τ) (c • Φ) := by
  refine ⟨Submodule.smul_mem _ c h.1, fun u => ?_⟩
  have e1 : Γ.M.co.rho W.ψ u (c • Φ) = c • Γ.M.co.rho W.ψ u Φ := by
    funext x; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, GlobalTheory.WeilM.thetaSum_smul, h.2, Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  simp only [smul_eq_mul, mul_assoc]

end Datum

section Pure

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)

theorem pure_zero : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : SInf F κ) φ = 0 := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]

theorem pure_add (f f' : SInf F κ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + f') φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul (c : ℂ) (f : SInf F κ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end Pure

theorem datum_real : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ → ∀ f₀, f₀ ≠ 0 → Γ.M.IsGauss Bs.ψ Bs.emb f₀ → IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∃ a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f₀ hf₀ hG hD
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  change TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) at τ
  let N : Submodule ℂ (SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank))) :=
    { carrier := {f | ∃ a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)}
      zero_mem' := ⟨0, by rw [tensT_zero, pure_zero]; exact isDatumA_zero W e Γ⟩
      add_mem' := by
        rintro f f' ⟨a, ha⟩ ⟨a', ha'⟩
        exact ⟨a + a', by rw [tensT_add, pure_add]; exact datumA_add W e Γ hψ ha ha'⟩
      smul_mem' := by
        rintro c f ⟨a, ha⟩
        exact ⟨c • a, by rw [tensT_smul, pure_smul]; exact datumA_smul W e Γ c ha⟩ }
  have h0 : f₀ ∈ N := ⟨Finsupp.single onePol 1, by rw [tensT_one]; exact hD⟩
  have hle : Γ.M.Pol Bs.ψ Bs.emb ≤ N := sInf_le ⟨fun g hg => by
      obtain ⟨c, rfl⟩ := GlobalTheory.T.fockVacua_triple_proportional_to_nonzero Bs Γ X om om' hT f₀ hf₀ hG g hg
      exact N.smul_mem c h0,
    fun u hu f ⟨a, ha⟩ f₁ h1 => GlobalTheory.T.archimedeanSchwartzDatum_stable_heisenbergDerivative hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f a ha u hu f₁ h1⟩
  exact fun f hf => hle hf

end GlobalTheory.BigNZ.DatReal
