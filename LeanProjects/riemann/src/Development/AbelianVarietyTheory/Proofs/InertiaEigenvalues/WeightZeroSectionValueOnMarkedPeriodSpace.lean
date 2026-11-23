import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDictionaryFrameMemOpenFramesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FamilyUniformisationPointsEqMarkedIsometryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterEqOfMarkedLatticeIsometryStatement

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MarkVal

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in

theorem val_at_mark {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n r : ℕ} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) (d : DeltaDat Xo c n)
    (U₂ : Unf d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (C : GlobalTheory.Member.Ctx d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) V r) (hC : C.OK) (hι : C.ι = ι)
    (hx : C.x₀ = x₀) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ) (hf : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (d.l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (hv : GlobalTheory.OneMapAll.CXiAt V hr σ0 d U₂ dict₂ ι x₀ xi c0)
    (y : FrPt d.Xo₂ d.c₂ (CAt (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)))) (k : Fin C.F.n) (P : (C.F.Di k).La →+ (Fin C.g → ℂ))
    (hP : IsPeriod (C.F.Di k) (fun j => relab d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (C.e j).1) P)
    (hy : y.x = C.F.u k P) (h γ : GA D V) (hM : C.Mark h k γ) :
    toC (evR d.Xo₂ d.c₂ d.cδ y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ) := by
  classical
  subst hr hι hx
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  have hσ : GoodEmb d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) := hC.good
  have hor : ∀ j, IsOrthogonalFrame (U₂.X j) C.x₀ := by
    intro j τ hτ
    have h1 := hC.orth k
    have hG : (U₂.X j).Gm = (C.M.X k).Gm := by rw [(hW j).1, (hC.modelW k).1]
    have hp : (U₂.X j).p0 = (C.M.X k).p0 := ((hU.2.1 j).1).trans (hC.base.type k).1.symm
    have hΨ : τ ∈ (C.M.X k).Ψ := ((hC.base.type k).2 τ).2 (((hU.2.1 j).2 τ).1 hτ)
    rw [hG, hp]
    exact h1 τ hΨ

  have hdom := GlobalTheory.T.latticeDictionary_frame_mem_open_frames V U₂ dict₂ C.ι e₀ F ik φ th C.x₀ hσ hC.lA hU hW hD hth hor
  obtain ⟨h', hh'⟩ := GlobalTheory.TwistTie.exists_dict_over V U₂ dict₂ C.ι e₀ F ik φ th C.x₀ hσ hC.lA hC.pos hU hW hD hC.iota
    hth hor hdom y
  obtain ⟨P', -, hP', hy', -⟩ := hD.1.2 (dict₂ h').1 ⟨_, hdom h'⟩
  have hpt : C.F.u k P = F.u (ik (dict₂ h').1) P' := hy.symm.trans (hh'.trans hy')
  have hg : (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ) = H.rt0 := hC.good
  obtain ⟨gam, hgE, hgm⟩ := GlobalTheory.T.familyUniformisation_points_eq_marked_isometry C.F F hC.pos hg
    ((GlobalTheory.Relab.relab_good _ H d.l₂ d.c₂ _ hσ).2.2.2 Dw C.g C.e)
    ((GlobalTheory.Relab.relab_good _ H d.l₂ d.c₂ _ hσ).2.2.2 Dw g₀ e₀) (C.e.trans e₀.symm)
    (fun j => by simp) k (ik (dict₂ h').1) P P' hP hP' hpt
  obtain ⟨γ', hγ', hΛ', hm', -⟩ := hD.2 h'
  have hxe := GlobalTheory.T.detCharacter_eq_of_marked_lattice_isometry d.l₂ V C.ι hC.iota.emb.2 (C.F.Di k) (F.Di (ik (dict₂ h').1)) (C.F.t k) (F.t (ik (dict₂ h').1))
    (C.M.X k) (U₂.X (dict₂ h').1) (C.M.φ k) (φ (dict₂ h').1) (γ * h) (γ' * h') (hC.modelW k) (hW _)
    (hC.base.ef k) (hD.1.1 _) hM.2.1 hΛ' hM.2.2 hm' gam hgE hgm xi hxi1 hxi2
  have hv := hval h' γ' ⟨hγ', hΛ', hm'⟩
  rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hf hh', ← hxe, ← hv]
  show _ = (if h'' : (dict₂ h').2 ∈ (U₂.X (dict₂ h').1).dom then toC (evR d.Xo₂ d.c₂ d.cδ (U₂.un _ ⟨_, h''⟩)) else 0)
  rw [dif_pos (hdom h')]

end GlobalTheory.MarkVal

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.MarkVal

set_option maxHeartbeats 4000000 in

theorem val_on_marked_space : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (C : GlobalTheory.Member.Ctx (M.dδ a).Xo₂ (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (Wc D i) D.R.r), C.OK → C.ι = iotaW T i → C.x₀ = T.x₀ ((i : ℕ) + 1) M.s0 → ∀ (f : Rul (M.dδ a).Xo₂ (M.dδ a).c₂) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ), f ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 → (∀ u : GA D (Wc D i), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ a).l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1) → (∀ γ ∈ GQ (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1) → GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) xi c0 → ∀ (y : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ (CAt ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)))) (k : Fin C.F.n) P, IsPeriod (C.F.Di k) (fun j => relab (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (C.e j).1) P → y.x = C.F.u k P → ∀ h γ : GA D (Wc D i), C.Mark h k γ → toC (evR (M.dδ a).Xo₂ (M.dδ a).c₂ f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hcore hfw i Tp tup M hM a C hOK hι hx f xi c0 hf hxi1 hxi2 hCX y k P hPer hy h γ hmk
  exact val_at_mark (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i)
    (T.x₀ ((i : ℕ) + 1) M.s0) C hOK hι hx xi c0 hf hxi1 hxi2 hCX y k P hPer hy h γ hmk

end GlobalTheory.MarkVal
