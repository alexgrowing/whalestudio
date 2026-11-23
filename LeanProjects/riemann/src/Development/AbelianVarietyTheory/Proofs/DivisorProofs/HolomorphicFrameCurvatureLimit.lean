import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualEigOfHasDual
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EigGramChart

open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.DRBaseEx (pairMat pairMat_mulVec_crd)

theorem form_blockDiagonal' {ι : Type} [Fintype ι] [DecidableEq ι] {m : ι → Type} [∀ τ, Fintype (m τ)]
    [∀ τ, DecidableEq (m τ)] (A : ∀ τ, Matrix (m τ) (m τ) ℂ) (v w : (Σ τ, m τ) → ℂ) :
    form (blockDiagonal' A) v w = ∑ τ, form (A τ) (fun j => v ⟨τ, j⟩) fun j => w ⟨τ, j⟩ := by
  rw [form_eq_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [form_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_sigma, Finset.sum_eq_single τ]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [blockDiagonal'_apply_eq]
  · intro τ' _ h
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [blockDiagonal'_apply_ne A j k (Ne.symm h)]
    ring
  · simp

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {σ : c.F →+* ℂ} {x : Sp ℂ ⟶ Z.X} {n : ℕ}

def pairAll (u : EigFrame Z σ x) {U : Z.X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (m : Fin n → Γ(omega Z.t.G, U)) :
    Matrix (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (Fin n) ℂ :=
  Matrix.of fun j a => pairMat u h m j.1 j.2 a

theorem pairAll_mul_tr {σ₀ : Oz →+* ℂ} {z : CxPts Z.s σ₀} (e : z.1 = x) (u : EigFrame Z σ x)
    (c₁ c₂ : Chart (omega Z.t.G) n) (h₁ : ⊤ ≤ x ⁻¹ᵁ c₁.U) (h₂ : ⊤ ≤ x ⁻¹ᵁ c₂.U) :
    pairAll u h₁ c₁.e * c₁.tr Z.s σ₀ c₂ z = pairAll u h₂ c₂.e := by
  ext j a
  have := congrFun (pairMat_mulVec_crd e u c₁ h₁ h₂ (c₂.e a) j.1) j.2
  rw [mul_apply]
  exact this

theorem G_eq_chg_pairAll {G : ∀ σ', EigMet Z σ'} {g : ℕ} {h : VMetric Z.s (omega Z.t.G) g} (hd : IsDualEig G h)
    (yc : CxPts (genStr Z) σ) (z : CxPts Z.s (σ.comp β)) (e : z.1 = yc.1 ≫ genι Z) (u : EigFrame Z σ (yc.1 ≫ genι Z))
    (c₁ : Chart (omega Z.t.G) g) {W : Z.t.G.left.Opens} (hW : c₁.U ≤ unitSec Z.t.G ⁻¹ᵁ W)
    (f : Fin g → Γ(Z.t.G.left, W)) (hf : ∀ k, dUnit Z.t.G hW (f k) = c₁.e k) (hz : z ∈ ptsIn Z.s (σ.comp β) c₁.U)
    (hx : ⊤ ≤ (yc.1 ≫ genι Z) ⁻¹ᵁ c₁.U) :
    (h.met (σ.comp β)).G c₁ z = chg (pairAll u hx c₁.e) (blockDiagonal' fun τ => ((G σ).gram yc u τ)⁻¹) := by
  ext a b
  rw [← (h.met _).form_frame c₁ hz, ← hf a, ← hf b, hd σ yc z e u c₁.U W hW (f a) (f b) hz, chg_apply,
    form_blockDiagonal']
  refine Finset.sum_congr rfl fun τ _ => ?_
  have key : ∀ k, (fun i => (valR (u.v τ i) W (f k)).snd) = fun i => pairAll u hx c₁.e ⟨τ, i⟩ k := fun k => by
    funext i
    change _ = GlobalTheory.LocM.tanEv Z.t (u.tan τ i) hx (c₁.e k)
    rw [← hf k]
    exact (GlobalTheory.LocM.tanEv_dUnit_eq (u.tan τ i) hx hW (f k)).2.symm
  rw [key a, key b]

end Model

end GlobalTheory.EigGramChart

open GlobalTheory.LieVB (omega unitSec dUnit)

open GlobalTheory.EigGramChart in

theorem GlobalTheory.EigGramChart.gram_eq_chg : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (Y : Scheme.{0}) (i : Y ⟶ M.B) (hi : (i ≫ M.b) ≫ O.s.T.Z.s = i ≫ M.q) (σ : O.κ.c.F →+* ℂ) (e : ℕ) (ch : AlgChart (i ≫ M.q) (σ.comp _) (e + 2)) (cE : Chart ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback M.b).obj (GlobalTheory.LieVB.omega O.s.T.Z.t.G))) (D.R.f * O.N)) (U : Set (V (e + 2))) (a : V (e + 2) → CxFr O.s.T.Z σ), IsOpen U → U ⊆ ch.e.target → HolFam U a → ContinuousOn (fun u => (a u).1) U → (∀ u ∈ U, (a u).1 = up (i ≫ M.b) hi σ (ch.e.symm u)) → ∃ T : V (e + 2) → Matrix (Σ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ)) (Fin (D.R.f * O.N)) ℂ, (∀ j b, DifferentiableOn ℂ (fun u => T u j b) (U ∩ ch.e.symm ⁻¹' ptsIn _ _ cE.U)) ∧ (∀ u ∈ U ∩ ch.e.symm ⁻¹' ptsIn _ _ cE.U, Function.Bijective (T u).mulVec) ∧ ∀ R : ℝ, ∀ u ∈ U ∩ ch.e.symm ⁻¹' ptsIn _ _ cE.U, ((((M.h R).pull M.b rfl).pull i rfl).met (σ.comp _)).G cE (ch.e.symm u) = chg (T u) (Matrix.blockDiagonal' fun τ => dualGram (eigGram (M.x.eigMetAt σ (some R)) a τ u)) := by
  intro D O c M Y i hi σ e ch cE U a hU hUt hhol hcont hup
  classical
  have hV : IsVB (omega O.s.T.Z.t.G) (D.R.f * O.N) := (M.h 0).isVB
  let zu : V (e + 2) → CxPts O.s.T.Z.s (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F)) := fun u =>
    PtsOver.map (i ≫ M.b) hi _ (ch.e.symm u)
  let pb : Chart (omega O.s.T.Z.t.G) (D.R.f * O.N) →
      Chart ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback M.b).obj (omega O.s.T.Z.t.G))) (D.R.f * O.N) :=
    fun c₀ => (c₀.pull hV M.b).pull (hV.pullback M.b) i
  let Tc : ∀ (u : V (e + 2)) (c₀ : Chart (omega O.s.T.Z.t.G) (D.R.f * O.N)),
      ⊤ ≤ ((a u).1.1 ≫ genι O.s.T.Z) ⁻¹ᵁ c₀.U → Matrix (Σ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ)) (Fin (D.R.f * O.N)) ℂ :=
    fun u c₀ h => pairAll (a u).2 h c₀.e * (pb c₀).tr (i ≫ M.q) _ cE (ch.e.symm u)
  let T : V (e + 2) → Matrix (Σ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ)) (Fin (D.R.f * O.N)) ℂ := fun u =>
    if h : ⊤ ≤ ((a u).1.1 ≫ genι O.s.T.Z) ⁻¹ᵁ (hV.pick (zu u)).U then Tc u _ h else 0
  have hz : ∀ u ∈ U, (zu u).1 = (a u).1.1 ≫ genι O.s.T.Z := fun u hu => by
    rw [hup u hu, up_ι]
    rfl
  have hmem : ∀ u (c₀ : Chart (omega O.s.T.Z.t.G) (D.R.f * O.N)), zu u ∈ ptsIn _ _ c₀.U →
      ch.e.symm u ∈ ptsIn (i ≫ M.q) _ (pb c₀).U := fun u c₀ h => h
  have hK : ∀ u ∈ U, ∀ (c₀ : Chart (omega O.s.T.Z.t.G) (D.R.f * O.N)) (hc : ⊤ ≤ ((a u).1.1 ≫ genι O.s.T.Z) ⁻¹ᵁ c₀.U),
      T u = Tc u c₀ hc := by
    intro u hu c₀ hc
    have h0 : ⊤ ≤ ((a u).1.1 ≫ genι O.s.T.Z) ⁻¹ᵁ (hV.pick (zu u)).U := hz u hu ▸ hV.mem_pick (zu u)
    have hzc : zu u ∈ ptsIn _ _ c₀.U := by
      change ⊤ ≤ (zu u).1 ⁻¹ᵁ c₀.U
      rw [hz u hu]
      exact hc
    change dite _ _ _ = _
    rw [dif_pos h0]
    change pairAll (a u).2 h0 _ * _ = pairAll (a u).2 hc _ * _
    rw [← Chart.tr_mul' (pb (hV.pick (zu u))) (pb c₀) cE (hmem u c₀ hzc), ← Matrix.mul_assoc]
    congr 1
    have e1 := Chart.tr_pull ((hV.pick (zu u)).pull hV M.b) (c₀.pull hV M.b) (hV.pullback M.b) i
      (rfl : i ≫ M.b ≫ O.s.T.Z.s = i ≫ M.q) (z := ch.e.symm u) (hV.mem_pick (zu u)) hzc
    have e2 := Chart.tr_pull (hV.pick (zu u)) c₀ hV M.b (rfl : M.b ≫ O.s.T.Z.s = M.b ≫ O.s.T.Z.s)
      (z := PtsOver.map i rfl _ (ch.e.symm u)) (hV.mem_pick (zu u)) hzc
    rw [PtsOver.map_map] at e2
    rw [e1, e2]
    exact pairAll_mul_tr (z := zu u) (hz u hu) (a u).2 _ _ h0 hc
  have hloc : ∀ u, ∃ (c₁ : Chart (omega O.s.T.Z.t.G) (D.R.f * O.N)) (W : O.s.T.Z.t.G.left.Opens)
      (hW : c₁.U ≤ unitSec O.s.T.Z.t.G ⁻¹ᵁ W) (f : Fin (D.R.f * O.N) → Γ(O.s.T.Z.t.G.left, W)),
      (∀ k, dUnit O.s.T.Z.t.G hW (f k) = c₁.e k) ∧ zu u ∈ ptsIn _ _ c₁.U := by
    intro u
    have := O.s.T.Z.t.semi
    have hs := LieVB.sec_hom (MonObj.one (X := O.s.T.Z.t.G))
    obtain ⟨U₁, W, hx, hle, chc⟩ := GlobalTheory.Conormal.exists_isChart hs (mem_ptsIn.1 (hV.mem_pick (zu u)))
    let c₁ : Chart (omega O.s.T.Z.t.G) (D.R.f * O.N) := ⟨U₁, _, (hV.pick (zu u)).isFrame.res hle⟩
    choose f hf using fun k => chc.d_surjective hs (c₁.e k)
    exact ⟨c₁, W, chc.le, f, hf, mem_ptsIn.2 hx⟩
  have hxz : ∀ u ∈ U, ∀ (c₀ : Chart (omega O.s.T.Z.t.G) (D.R.f * O.N)), zu u ∈ ptsIn _ _ c₀.U →
      ⊤ ≤ ((a u).1.1 ≫ genι O.s.T.Z) ⁻¹ᵁ c₀.U := fun u hu c₀ h => by
    have h' : ⊤ ≤ (zu u).1 ⁻¹ᵁ c₀.U := h
    rwa [hz u hu] at h'
  have hG : ∀ R : ℝ, ∀ u ∈ U, ch.e.symm u ∈ ptsIn (i ≫ M.q) _ cE.U →
      ((((M.h R).pull M.b rfl).pull i rfl).met (σ.comp _)).G cE (ch.e.symm u) =
        chg (T u) (Matrix.blockDiagonal' fun τ => dualGram (eigGram (M.x.eigMetAt σ (some R)) a τ u)) := by
    intro R u hu hyE
    obtain ⟨c₁, W, hW, f, hf, hz1⟩ := hloc u
    have hx1 := hxz u hu c₁ hz1
    rw [hK u hu c₁ hx1]
    change ((((M.h R).met _).pull M.b rfl).pull i rfl).G cE (ch.e.symm u) = _
    rw [Met.trans _ (pb c₁) cE _ (hmem u c₁ hz1)]
    have e1 := Met.pull_G (((M.h R).met (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).pull M.b rfl) i rfl
      (c₁.pull hV M.b) (z := ch.e.symm u) hz1
    have e2 := Met.pull_G ((M.h R).met (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))) M.b rfl c₁
      (z := PtsOver.map i rfl _ (ch.e.symm u)) hz1
    rw [PtsOver.map_map] at e2
    rw [e1, e2, G_eq_chg_pairAll (M.dual R) (a u).1 (zu u) (hz u hu) (a u).2 c₁ hW f hf hz1 hx1, chg_chg]
    congr 2
    funext τ
    rw [dualGram, eigGram, transpose_nonsing_inv, transpose_transpose]
  refine ⟨T, ?_, ?_, fun R u hu => hG R u hu.1 hu.2⟩
  · intro j b u₀ hu₀
    obtain ⟨c₁, W, hW, f, hf, hz1⟩ := hloc u₀
    let N := U ∩ (ch.e.target ∩ ch.e.symm ⁻¹' (ptsIn (i ≫ M.q) (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F)) cE.U ∩
      ptsIn (i ≫ M.q) (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F)) (pb c₁).U))
    have hN : IsOpen N := hU.inter (ch.e.isOpen_inter_preimage_symm ((isOpen_ptsIn _).inter (isOpen_ptsIn _)))
    have hu₀N : u₀ ∈ N := ⟨hu₀.1, hUt hu₀.1, hu₀.2, hmem u₀ c₁ hz1⟩
    have hxN : ∀ u ∈ N, ⊤ ≤ ((a u).1.1 ≫ genι O.s.T.Z) ⁻¹ᵁ c₁.U := fun u hu => hxz u hu.1 c₁ hu.2.2.2
    let g : Fin (D.R.f * O.N) → Γ(Y, cE.U ⊓ (pb c₁).U) := fun l =>
      ((pb c₁).isFrame.basis inf_le_right).repr (GlobalTheory.Twist.resM _ inf_le_left (cE.e b)) l
    let L : V (e + 2) → ℂ := fun u => ∑ l, (valR ((a u).2.v j.1 j.2) W (f l)).snd *
      ev (i ≫ M.q) (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F)) (cE.U ⊓ (pb c₁).U) (g l) (ch.e.symm u)
    have hL : DifferentiableOn ℂ L N := by
      refine DifferentiableOn.fun_sum fun l _ => DifferentiableOn.mul ?_ ?_
      · exact (hhol.2 j.1 j.2 W (f l)).mono fun u hu =>
          ⟨hu.1, (GlobalTheory.LocM.tanEv_dUnit_eq ((a u).2.tan j.1 j.2) (hxN u hu) hW (f l)).1⟩
      · exact (ch.holo _ (g l)).mono fun u hu => ⟨hu.2.1, mem_ptsIn_inf.2 hu.2.2⟩
    have hTL : ∀ u ∈ N, T u j b = L u := fun u hu => by
      rw [hK u hu.1 c₁ (hxN u hu)]
      show (pairAll (a u).2 (hxN u hu) c₁.e * (pb c₁).tr (i ≫ M.q) _ cE (ch.e.symm u)) j b = _
      rw [mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      change GlobalTheory.LocM.tanEv _ _ _ (c₁.e l) = _
      rw [← hf l]
      exact (GlobalTheory.LocM.tanEv_dUnit_eq ((a u).2.tan j.1 j.2) (hxN u hu) hW (f l)).2
    exact ((hL.differentiableAt (hN.mem_nhds hu₀N)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hN.mem_nhds hu₀N) hTL)).differentiableWithinAt
  · intro u hu
    have hpd := ((((M.h 0).pull M.b rfl).pull i rfl).met (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).posDef cE
      (ch.e.symm u) hu.2
    rw [hG 0 u hu.1 hu.2] at hpd
    have hinj : Function.Injective (T u).mulVec := by
      intro v w hvw
      by_contra hne
      have := (posDef_iff.1 hpd).2 (v - w) (sub_ne_zero.2 hne)
      rw [form_chg, mulVec_sub, hvw, sub_self] at this
      simp [form] at this
    refine ⟨hinj, ?_⟩
    have hfin : Module.finrank ℂ (Fin (D.R.f * O.N) → ℂ) =
        Module.finrank ℂ ((Σ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ)) → ℂ) := by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_sigma]
      simp only [Fintype.card_fin]
      exact (GlobalTheory.DRBaseEx.sum_mult O).symm
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Matrix.mulVecLin (T u)) hfin).1 hinj
