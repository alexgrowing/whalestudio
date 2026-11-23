import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDifferentiableAtOfForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfConjEqOne
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh

theorem exists_comb_of_exp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {σ : c.F →+* ℂ} {x x' : Sp ℂ ⟶ Z.X} (hxx : x' = x) {g : ℕ} (ex : (Fin g → ℂ) → (Over.mk x' ⟶ Z.t.G))
    (hex : IsExpAt Z.t x' ex) (f : EigFrame Z σ x) (τ : E →+* ℂ) (δ : Fin (Dw.mult τ) → Fin g → ℂ)
    (hδ : ∀ b, IsDerivAt0 (fun z => (ex z).left) (δ b) (f.v τ b)) (v' : Sp (DualNumber ℂ) ⟶ Z.t.G.left)
    (hv' : IsTanAtG Z.t x v') (heig : ∀ a, v' ≫ (Z.t.act.act a).left = spMap (epsMul (σ (embK c τ a))) ≫ v')
    (w : Fin g → ℂ) (hw : IsDerivAt0 (fun z => (ex z).left) w v') :
    ∃ a : Fin (Dw.mult τ) → ℂ, IsCombAtG Z.t x (f.v τ) a v' ∧ w = ∑ b, a b • δ b := by
  subst hxx
  obtain ⟨a, ha, -⟩ := f.basis τ v' hv' heig
  have e1 : ex 0 = 1 := by
    have h := hex.1 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hd := GlobalTheory.ShFam.Hor.ExpDirs.isDerivAt0_of_comb (congrArg (·.left) e1) (f.tan τ) hδ hv' ha
  obtain ⟨w', -, hu⟩ := hex.2.2 v' hv'
  exact ⟨a, ha, (hu w hw).trans (hu _ hd).symm⟩

end GlobalTheory.HolCoordEv

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom)

theorem coords_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (d : ℕ) (u₀ : V d) (R : Type) [CommRing R] (φR : c.F →+* R) (xR : Sp R ⟶ Z.X) (fR : EigFrame Z φR xR) (ev : V d → (R →+* ℂ)) (k : U.Comp) (G : V d → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) (τ : E →+* ℂ), (∀ t, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ev u t) u) → (∀ τ' a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → (∀ᶠ u in 𝓝 u₀, (ev u).comp φR = σ) → (∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, (cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z = spMap (ev u) ≫ xR) → ∃ M : V d → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => M u a b) u) ∧ ∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, ∀ i, IsCombAtG Z.t ((cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z) ((cxFrame Z (U.un k ⟨G u, h⟩)).v τ) (fun b => M u b i) (spMap (dualMap (ev u)) ≫ fR.v τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ U _hg hU d u₀ R _ φR xR fR ev k G τ hev hG hφ hpt
  classical
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hP⟩ := hU
  choose Pm h1 h2 h3 h4 _ using hP
  obtain ⟨h₀, -⟩ := hpt.self_of_nhds
  let L := EuclideanSpace.equiv (Fin d) ℂ
  let x : (Fin d → ℂ) → (U.X k).dom := fun b =>
    if h : G (L.symm b) ∈ (U.X k).dom then ⟨G (L.symm b), h⟩ else ⟨G u₀, h₀⟩
  have hxb : ∀ b (h : G (L.symm b) ∈ (U.X k).dom), x b = ⟨G (L.symm b), h⟩ := fun b h => dif_pos h
  let P : (Fin d → ℂ) → ((F.Di (ik k)).La →+ (Fin g → ℂ)) := fun b => Pm k (x b)
  let p : (Fin d → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b => GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x b))
  have hu : ∀ b, F.u (ik k) (P b) =
      p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    fun b => (h3 k (x b)).symm.trans (ptF_fst (U.un k (x b))).symm
  have hs : ∀ b, p b ≫ pullback.snd _ _ = spMap σ := fun b => ptF_snd (U.un k (x b))
  have hgood : ∀ᶠ u in 𝓝 u₀, G u ∈ (U.X k).dom ∧
      ∀ τ' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u :=
    (hpt.mono fun u hu => hu.1).and
      (eventually_all.2 fun τ' => eventually_all.2 fun a => eventually_all.2 fun b => hG τ' a b)
  obtain ⟨B₀, hB₀, hB₀o, hu₀⟩ := eventually_nhds_iff.1 hgood
  let B : Set (Fin d → ℂ) := L.symm ⁻¹' B₀
  have hBo : IsOpen B := hB₀o.preimage L.symm.continuous
  have hb₀ : L u₀ ∈ B := by
    show L.symm (L u₀) ∈ B₀
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hu₀
  have hPd : ∀ a, DifferentiableOn ℂ (fun b => P b a) B := fun a => differentiableOn_pi.2 fun j =>
    (TrueCx.TorHolo.differentiableOn_perFr (U.X k) (x := fun b => G (L.symm b)) (fun b hb => (hB₀ _ hb).1)
      (fun τ' a' c' b hb => (((hB₀ _ hb).2 τ' a' c').comp b L.symm.differentiableAt).differentiableWithinAt)
      _ _ _).congr fun b hb => by
        show Pm k (x b) a j = _
        rw [h1, hxb b (hB₀ _ hb).1]
  let ev' : (Fin d → ℂ) → (R →+* ℂ) := fun b => ev (L.symm b)
  let Ex : (Fin d → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left) := fun b z =>
    liftEx Z F (p b) (ik k) (P b) (hu b) z ≫ Z.m.φ
  let Wd : Fin (Dw.mult τ) → (Fin d → ℂ) → Fin g → ℂ := fun i b =>
    if h : ∃ w, IsDerivAt0 (Ex b) w (spMap (dualMap (ev' b)) ≫ fR.v τ i) then h.choose else 0
  have core : ∀ b (h : G (L.symm b) ∈ (U.X k).dom),
      (cxPt Z (U.un k ⟨G (L.symm b), h⟩)).1 ≫ genι Z = spMap (ev (L.symm b)) ≫ xR →
      (ev (L.symm b)).comp φR = σ → ∀ i,
      IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) ∧
      IsCombAtG Z.t ((cxPt Z (U.un k ⟨G (L.symm b), h⟩)).1 ≫ genι Z)
        ((cxFrame Z (U.un k ⟨G (L.symm b), h⟩)).v τ) (fun a => Wd i b (e.symm ⟨τ, a⟩))
        (spMap (dualMap (ev (L.symm b))) ≫ fR.v τ i) := by
    intro b h hx hφb i
    rw [← hxb b h] at hx ⊢
    obtain ⟨gF, hgF⟩ := HolFrames.exists_bc fR (ev (L.symm b)) (φ' := σ) hφb.symm hx
    have hxp : p b ≫ Z.jQ ≫ genι Z = (cxPt Z (U.un k (x b))).1 ≫ genι Z := (Category.assoc _ _ _).symm
    have hExp := isExpAt_pushEx E H Dw l Xo c O β Z g _ _ F (p b) (ik k) (P b) _ (hu b) rfl (h2 k (x b))
    have hδ : ∀ a, IsDerivAt0 (fun z => (pushEx Z F (p b) (ik k) (P b) _ (hu b) rfl z).left)
        (Pi.single (e.symm ⟨τ, a⟩) 1) ((cxFrame Z (U.un k (x b))).v τ a) := by
      intro a
      obtain ⟨w, hwt, hw0, hwm⟩ := EigFrame.ofFrPt_v Z (U.un k (x b))
        (x := (cxPt Z (U.un k (x b))).1 ≫ genι Z) (Category.assoc _ _ _).symm τ a
      have hw0' : (w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left) ≫ Z.m0.toSABMap.φ = (U.un k (x b)).u τ a := hw0
      have hwm' : (w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left) ≫ Z.m.φ = (cxFrame Z (U.un k (x b))).v τ a := hwm
      have hd : IsDerivAt0 (fun z => (F.ex (ik k) (P b) z).left) (Pi.single (e.symm ⟨τ, a⟩) 1)
          (w ≫ Z.m0.toSABMap.φ) := by
        exact (congrArg (IsDerivAt0 _ _) hw0').mpr (h4 k (x b) τ a)
      have := isDerivAt0_comp_hom (isDerivAt0_liftEx Z F (p b) (ik k) (P b) (h2 k (x b)) (hu b) hwt.1 hd) Z.m.φ
      exact (congrArg (IsDerivAt0 _ _) hwm').mp this
    have ht : IsTanAtG Z.t (p b ≫ Z.jQ ≫ genι Z) (gF.v τ i) := by
      rw [hxp]; exact gF.tan τ i
    have hex : ∃ w, IsDerivAt0 (Ex b) w (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      obtain ⟨w, hw, -⟩ := hExp.2.2 _ ht
      exact ⟨w, (hgF τ i) ▸ hw⟩
    have hW : IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      have e0 : Wd i b = hex.choose := dif_pos hex
      rw [e0]
      exact hex.choose_spec
    refine ⟨hW, ?_⟩
    obtain ⟨a, ha, hwa⟩ := exists_comb_of_exp hxp _ hExp (cxFrame Z (U.un k (x b))) τ _ hδ (gF.v τ i)
      (gF.tan τ i) (gF.eig τ i) (Wd i b) ((hgF τ i).symm ▸ hW)
    have hfa : (fun a' => Wd i b (e.symm ⟨τ, a'⟩)) = a := by
      funext a'
      rw [hwa]
      have hi : ∀ j j' : Fin (Dw.mult τ), e.symm ⟨τ, j⟩ = e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
      simp [Finset.sum_apply, Pi.single_apply, hi]
    rw [hfa, ← hgF τ i]
    exact ha
  have ht : Tendsto L.symm (𝓝 (L u₀)) (𝓝 u₀) := by
    simpa using L.symm.continuous.tendsto (L u₀)
  refine ⟨fun u a i => Wd i (L u) (e.symm ⟨τ, a⟩), fun a i => ?_, ?_⟩
  · have hev'' : ∀ t, ∀ᶠ b in 𝓝 (L u₀), DifferentiableAt ℂ (fun b => ev' b t) b := fun t => by
      filter_upwards [ht.eventually (hev t)] with b hb
      exact hb.comp b L.symm.differentiableAt
    have hW : ∀ᶠ b in 𝓝 (L u₀), IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      filter_upwards [ht.eventually hpt, ht.eventually hφ] with b ⟨h, hx⟩ hφb
      exact (core b h hx hφb i).1
    have hd := eventually_differentiableAt_dir Z σ F (ik k) hBo hu (fun b => h2 k (x b)) hPd hs (fR.v τ i) ev' hb₀
      hev'' (Wd i) hW
    filter_upwards [(L.continuous.tendsto u₀).eventually hd] with u hu
    exact (differentiableAt_pi.1 hu (e.symm ⟨τ, a⟩)).comp u L.differentiableAt
  · filter_upwards [hpt, hφ] with u ⟨h, hx⟩ hφu
    refine ⟨h, fun i => ?_⟩
    have c := core (L u)
    rw [ContinuousLinearEquiv.symm_apply_apply] at c
    exact (c h hx hφu i).2

end GlobalTheory.HolCoordEv
