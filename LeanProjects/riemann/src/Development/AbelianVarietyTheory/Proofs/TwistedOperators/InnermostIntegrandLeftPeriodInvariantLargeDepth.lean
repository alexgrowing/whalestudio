import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QEqColPer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatBFSource

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLeftInv

section Steps

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem rowGrp_odd (j σ : ℕ) (hj : j + 2 * σ + 1 = D.R.m) :
    rowGrp G j = jacGrp (rowJac G j (by omega) σ (by omega)) := by
  obtain rfl : σ = (D.R.m - 1 - j) / 2 := by omega
  exact dif_pos hj

theorem rowGrp_even (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) :
    rowGrp G j = besGrp (besDecAt G j σ hj) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  obtain rfl : σ = (D.R.m - 2 - j) / 2 := by omega
  unfold rowGrp
  rw [dif_neg (by omega), dif_pos hj]

variable (W : G.Weil) {t : T} {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t)

abbrev handAt (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (Φ : SchDown G t) (φ : GA D (G.V (.top j)) → ℂ)
    (g : GA D (G.V (.grid D.R.m j))) (h₁ : GA D (G.V (.grid D.R.m (j + 1)))) (h₂ : GA D (G.V (.grid D.R.m (j + 1 + 1)))) :
    GA D (G.V (.top (j + 1 + 1))) → ℂ :=
  GlobalTheory.Unf.Chain.hand (stepAt G W t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
    (stepAt G W t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega)))
    (linkAt hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
    ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
    (B := besAt G hM j (σ + 1) hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
    (B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
    (Φ ⟨j, by omega⟩) (Φ ⟨j + 1, by omega⟩) φ g h₁ h₂

theorem biL_conAt (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j))
    (φ : GA D (G.V (.top j)) → ℂ) (hφ : GlobalTheory.Unf.IsContAut _ φ) (h : Pts G) :
    biL W M t j φ (conAt W hM Φ h j) = handAt W hM j σ hj Φ φ (h j) (h (j + 1)) (h (j + 1 + 1)) := by
  obtain rfl : σ = (D.R.m - 4 - j) / 2 := by omega
  refine Eq.trans ?_ (dbl_hand_eq_biLift G W t hM _ j hj _ _ _ φ (hΦ ⟨j, by omega⟩) (hΦ ⟨j + 1, by omega⟩) hφ _ _ _).symm
  have e : conAt W hM Φ h j = _ := (dif_neg (by omega)).trans (dif_pos hj)
  rw [e]
  rfl

theorem handAt_contAut (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j))
    (φ : GA D (G.V (.top j)) → ℂ) (hφ : GlobalTheory.Unf.IsContAut _ φ) (g h₁ h₂) :
    GlobalTheory.Unf.IsContAut _ (handAt W hM j σ hj Φ φ g h₁ h₂) := by
  let B := besAt G hM j (σ + 1) hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some
  let J := jacAt G hM (j + 1) (σ + 1) (by omega)
  let B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ (by omega))).some
  let s₁ : GlobalTheory.Unf.StepBF W.ψ B J :=
    stepAt G W t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
  let s₂ : GlobalTheory.Unf.StepFB W.ψ J B' :=
    stepAt G W t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
  have t₁ : IsThetaFunO W.ψ B.V₀ J.W₀ (GlobalTheory.Unf.flatBF s₁ (s₁.om (g, h₁) (Φ ⟨j, by omega⟩))) :=
    (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) W.ψ).1 _ B J s₁ _ (s₁.weil.om_pres (g, h₁) _ (hΦ ⟨j, by omega⟩))
  have t₂ : IsThetaFunO W.ψ J.W₀ B'.V₀ (GlobalTheory.Unf.flatFB s₂ (s₂.om (h₁, h₂) (Φ ⟨j + 1, by omega⟩))) :=
    (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) W.ψ).2 _ J B' s₂ _
      (s₂.weil.om_pres (h₁, h₂) _ (hΦ ⟨j + 1, by omega⟩))
  exact GlobalTheory.FinPl.ValDbl.contAut_hand0 s₁ s₂ (linkAt hM j σ hj _ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
    ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) hφ t₁ t₂

theorem biL_contAut (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (i : ℕ) (hi : Even i) (hm : i + 2 < D.R.m)
    (ψ : GA D (G.V (.top i)) → ℂ) (hψ : GlobalTheory.Unf.IsContAut _ ψ) : GlobalTheory.Unf.IsContAut _ (biL W M t i ψ (conAt W hM Φ h i)) := by
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨b, hb⟩ := hi
  rw [biL_conAt W hM i (a - b - 2) (by omega) Φ hΦ ψ hψ]
  exact handAt_contAut W hM _ _ _ Φ hΦ ψ hψ _ _ _

theorem odd_step (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (i σ : ℕ)
    (hi : i + 2 * (σ + 1) + 2 = D.R.m) (r) (hr : r ∈ rowGrp G (i + 1)) (ψ : GA D (G.V (.top i)) → ℂ)
    (hψ : GlobalTheory.Unf.IsContAut _ ψ) :
    biL W M t i ψ (conAt W hM Φ (Function.update h (i + 1) (r * h (i + 1))) i) = biL W M t i ψ (conAt W hM Φ h i) := by
  rw [biL_conAt W hM i σ hi Φ hΦ ψ hψ, biL_conAt W hM i σ hi Φ hΦ ψ hψ, Function.update_self,
    Function.update_of_ne (show i ≠ i + 1 by omega), Function.update_of_ne (show i + 1 + 1 ≠ i + 1 by omega)]
  rw [rowGrp_odd (i + 1) (σ + 1) (by omega)] at hr
  exact (GlobalTheory.FinPl.HandInvPf.handInv D W.ψ σ (besAt G hM i (σ + 1) hi (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
    (jacAt G hM (i + 1) (σ + 1) (by omega)) (besAt G hM (i + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
    _ _ _ _ _ _ (hΦ ⟨i, by omega⟩) (hΦ ⟨i + 1, by omega⟩) ψ hψ _ _ _).1 r hr

theorem even_first (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (i σ : ℕ)
    (hi : i + 2 * (σ + 1) + 2 = D.R.m) (hi' : i + 1 + 1 + 2 * σ + 2 = D.R.m) (n) (hn : n ∈ flagN (besDecAt G (i + 1 + 1) σ hi')) (a)
    (ψ : GA D (G.V (.top i)) → ℂ) (hψ : GlobalTheory.Unf.IsContAut _ ψ) :
    biL W M t i ψ (conAt W hM Φ (Function.update h (i + 1 + 1)
        (n * embA (besDecAt G (i + 1 + 1) σ hi') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) a * h (i + 1 + 1))) i) =
      star (psiBes W.ψ (besDecAt G (i + 1 + 1) σ hi') 1
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D _ _) fun _ => D.host.xi0 ^ σ) n) • rTrans a (biL W M t i ψ (conAt W hM Φ h i)) := by
  rw [biL_conAt W hM i σ hi Φ hΦ ψ hψ, biL_conAt W hM i σ hi Φ hΦ ψ hψ, Function.update_self,
    Function.update_of_ne (show i ≠ i + 1 + 1 by omega), Function.update_of_ne (show i + 1 ≠ i + 1 + 1 by omega)]
  exact GlobalTheory.BesMove.hand_right (B := besAt G hM i (σ + 1) hi (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
    (J := jacAt G hM (i + 1) (σ + 1) (by omega)) (B' := besAt G hM (i + 1 + 1) σ hi' (GlobalTheory.Unf.Inhab.nonempty_volN _).some) _ _ _ _ _
    (hΦ ⟨i + 1, by omega⟩) ψ _ _ _ hn a

theorem even_second (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (j σ : ℕ)
    (hj : j + 2 * σ + 2 = D.R.m) (n) (hn : n ∈ flagN (besDecAt G j σ hj)) (a)
    (φ : GA D (G.V (.top j)) → ℂ) (hφ : GlobalTheory.Unf.IsContAut _ φ) :
    biL W M t j (star (psiBes W.ψ (besDecAt G j σ hj) 1
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D _ _) fun _ => D.host.xi0 ^ σ) n) • rTrans a φ)
      (conAt W hM Φ (Function.update h j (n * embA (besDecAt G j σ hj) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) a * h j)) j) =
      biL W M t j φ (conAt W hM Φ h j) := by
  rcases σ with _ | σ
  · have e : ∀ h' : Pts G, conAt W hM Φ h' j = lastDat W hM j hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some (h' j) (Φ ⟨j, by omega⟩)
        (castSch G (show j + 1 + 1 = D.R.m by omega) (Φ ⟨j + 1, by omega⟩)) := fun h' => dif_pos hj
    rw [e, e, Function.update_self]
    obtain ⟨χz, hzH, hzE, -, -, hodd⟩ := GlobalTheory.T.thetaGrid_lastRow_column_characters_differ G W t
    obtain ⟨hS0, hT0⟩ := hodd j (by omega) (by omega)
    let B := besAt G hM j 0 hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    let s := (lastAt G W t hM j hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).s
    have homa : IsWeilDatumO W.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.chrS (.top t j)) (G.chrT (.top t j))
        (W.om (.top t j)) := W.om_is (.top t j) (by show j + 1 ≤ D.R.m; omega)
    have hom₁ : IsWeilDatumO W.ψ B.V₀ (G.V (.top (j + 1))) (G.chrS (.top t j) * χz) (G.chrT (.top t j)) s.om₀ := by
      rw [← hS0, ← hT0]; exact s.weil₀
    obtain ⟨omz, homz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (GlobalTheory.SeeSaw.Model.nLine D) (G.V (.top (j + 1))) W.ψ χz
      (G.chrT (.top t j)) W.ψ_std hzH homa.hecT hzE homa.resT
    have hΞ := (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) W.ψ).1 _ B _ s _
      (s.weil.om_pres (h j, 1) _ (hΦ ⟨j, by omega⟩))
    have k := GlobalTheory.BesMove.flatBF_bes (B := B) s (hΦ ⟨j, by omega⟩) hn a (h j) 1
    have k' := GlobalTheory.BesMove.biLift_last B.o (topOrthAt G (show D.R.m = j + 1 + 1 by omega)) lastTau hom₁ homa homz
      (W.om (.top t (j + 1))) (volAt hM (.top j) (by show j ≤ D.R.m; omega))
      (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) hφ.1 hΞ
      (fun w => castSch G (show j + 1 + 1 = D.R.m by omega) (Φ ⟨j + 1, by omega⟩)
        ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w))
      (psiBes W.ψ B.d 1 (vecB B.o B.ζ) n) (GlobalTheory.FinPl.HandInvPf.mul_star_psi W.ψ_std _) a
    erw [← k] at k'
    exact k'
  · obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top j))
    have hφ' : GlobalTheory.Unf.IsContAut _ (star (psiBes W.ψ (besDecAt G j (σ + 1) hj) 1
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D _ _) fun _ => D.host.xi0 ^ (σ + 1)) n) • rTrans a φ) :=
      ⟨fun γ hγ x => by simp only [Pi.smul_apply, rTrans, mul_assoc, hφ.1 γ hγ],
        (hφ.2.comp (continuous_mul_const a)).const_smul _⟩
    rw [biL_conAt W hM j σ hj Φ hΦ _ hφ', biL_conAt W hM j σ hj Φ hΦ φ hφ, Function.update_self,
      Function.update_of_ne (show j + 1 ≠ j by omega), Function.update_of_ne (show j + 1 + 1 ≠ j by omega)]
    exact GlobalTheory.BesMove.hand_left (B := besAt G hM j (σ + 1) hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (J := jacAt G hM (j + 1) (σ + 1) (by omega))
      (B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) _ _ _ _ _
      (hΦ ⟨j, by omega⟩) hφ.1 _ _ _ hn a

theorem even_step (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (i σ : ℕ)
    (hi : i + 2 * (σ + 1) + 2 = D.R.m) (r) (hr : r ∈ rowGrp G (i + 1 + 1)) (ψ : GA D (G.V (.top i)) → ℂ)
    (hψ : GlobalTheory.Unf.IsContAut _ ψ) :
    biL W M t (i + 1 + 1) (biL W M t i ψ (conAt W hM Φ (Function.update h (i + 1 + 1) (r * h (i + 1 + 1))) i))
        (conAt W hM Φ (Function.update h (i + 1 + 1) (r * h (i + 1 + 1))) (i + 1 + 1)) =
      biL W M t (i + 1 + 1) (biL W M t i ψ (conAt W hM Φ h i)) (conAt W hM Φ h (i + 1 + 1)) := by
  have hi' : i + 1 + 1 + 2 * σ + 2 = D.R.m := by omega
  rw [rowGrp_even (i + 1 + 1) σ hi'] at hr
  obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp _ _ r).1 hr
  rw [even_first W hM Φ hΦ h i σ hi hi' n hn a ψ hψ]
  refine even_second W hM Φ hΦ h (i + 1 + 1) σ hi' n hn a _ ?_
  rw [biL_conAt W hM i σ hi Φ hΦ ψ hψ]
  exact handAt_contAut W hM _ _ _ Φ hΦ ψ hψ _ _ _

omit hM in
theorem jPer_congr_above (M : GlobalTheory.FunObj.Vol G) (t : T) (C C' : BiFam G) (F : Fn G (.grid D.R.m D.R.m)) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (φ : Fn G (.top j)), Even j → (∀ i, Even i → j ≤ i → C i = C' i) →
      jPer W M t C F σ j hj φ = jPer W M t C' F σ j hj φ
  | 0, j, hj, φ, he, hC => by
    simp only [jPer]
    rw [hC j he le_rfl]
  | σ + 1, j, hj, φ, he, hC => by
    simp only [jPer]
    rw [hC j he le_rfl]
    exact jPer_congr_above M t C C' F σ (j + 1 + 1) _ _ (by obtain ⟨a, ha⟩ := he; exact ⟨a + 1, by omega⟩)
      fun i hi hji => hC i hi (by omega)

omit hM in

theorem jPer_congr_window (M : GlobalTheory.FunObj.Vol G) (t : T) (C C' : BiFam G) (F : Fn G (.grid D.R.m D.R.m)) (k : ℕ)
    (hk4 : k + 1 + 1 + 2 ≤ D.R.m) (hC : ∀ i, Even i → i ≠ k → i ≠ k + 1 + 1 → C i = C' i)
    (hpres : ∀ i, Even i → i < k → ∀ ψ : GA D (G.V (.top i)) → ℂ, GlobalTheory.Unf.IsContAut _ ψ →
      GlobalTheory.Unf.IsContAut _ (biL W M t i ψ (C i)))
    (hwin : ∀ ψ : GA D (G.V (.top k)) → ℂ, GlobalTheory.Unf.IsContAut _ ψ →
      biL W M t (k + 1 + 1) (biL W M t k ψ (C k)) (C (k + 1 + 1)) =
        biL W M t (k + 1 + 1) (biL W M t k ψ (C' k)) (C' (k + 1 + 1))) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (φ : Fn G (.top j)), Even j → Even k → j ≤ k → GlobalTheory.Unf.IsContAut _ φ →
      jPer W M t C F σ j hj φ = jPer W M t C' F σ j hj φ
  | 0, j, hj, φ, he, hk, hjk, hφ => by
    have h1 : j + 2 = D.R.m := by simpa using hj
    have h2 : j ≤ k := hjk
    omega
  | σ + 1, j, hj, φ, he, hk, hjk, hφ => by
    rcases Nat.lt_or_ge j k with hlt | hge
    · have hCj : C j = C' j := hC j he (by omega) (by omega)
      simp only [jPer]
      rw [← hCj]
      refine jPer_congr_window M t C C' F k hk4 hC hpres hwin σ (j + 1 + 1) _ _ ?_ hk ?_ (hpres j he hlt φ hφ)
      · obtain ⟨a, ha⟩ := he; exact ⟨a + 1, by omega⟩
      · obtain ⟨a, ha⟩ := he; obtain ⟨b, hb⟩ := hk; omega
    · have hj2 : j + 2 * (σ + 1) + 2 = D.R.m := by simpa using hj
      obtain rfl : j = k := by omega
      rcases σ with _ | σ'
      · simp only [jPer]
        rw [hwin φ hφ]
      simp only [jPer]
      rw [hwin φ hφ]
      exact jPer_congr_above W M t C C' F σ' (j + 1 + 1 + 1 + 1) _ _
        (by obtain ⟨a, ha⟩ := he; exact ⟨a + 2, by omega⟩) fun i hi hji => hC i hi (by omega) (by omega)

theorem conAt_update (Φ : SchDown G t) (h : Pts G) (j : ℕ) (x : GA D (G.V (.grid D.R.m j))) (i : ℕ) (h0 : i ≠ j)
    (h1 : i + 1 ≠ j) (h2 : i + 1 + 1 ≠ j) : conAt W hM Φ (Function.update h j x) i = conAt W hM Φ h i := by
  unfold conAt
  simp only [Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2]

end Steps

theorem rinv_all {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) : RInv ch := by
  intro t M hM Φ f hΦ hf P φ F hφ hF j hj r hr h
  obtain ⟨c, hc⟩ := D.R.m_even
  have hm2 := D.R.two_le_m
  have hj' : 1 ≤ j ∧ j + 2 ≤ D.R.m := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  unfold per
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 + 1 := ⟨j - 2, by obtain ⟨a, ha⟩ := he; omega⟩
    obtain ⟨b, hb⟩ : Even i := by
      obtain ⟨a, ha⟩ := he
      exact ⟨a - 1, by omega⟩
    refine jPer_congr_window ch.W M t _ _ _ i (by omega) ?_ ?_ ?_ _ 0 top_idx _ ⟨0, rfl⟩ ⟨b, hb⟩ (Nat.zero_le _) hφ
    · intro i' hi' h1 h2
      refine conAt_update ch.W hM Φ h _ _ i' h2 ?_ ?_
      · intro e; obtain ⟨a, ha⟩ := hi'; omega
      · intro e; exact h1 (by omega)
    · intro i' hi' hlt ψ hψ
      exact biL_contAut ch.W hM Φ hΦ _ i' hi' (by omega) ψ hψ
    · intro ψ hψ
      exact even_step ch.W hM Φ hΦ h i (c - b - 2) (by omega) r hr ψ hψ
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    obtain ⟨b, hb⟩ : Even i := by
      obtain ⟨a, ha⟩ := ho
      exact ⟨a, by omega⟩
    refine jPer_congr_window ch.W M t _ _ _ i (by omega) ?_ ?_ ?_ _ 0 top_idx _ ⟨0, rfl⟩ ⟨b, hb⟩ (Nat.zero_le _) hφ
    · intro i' hi' h1 h2
      refine conAt_update ch.W hM Φ h _ _ i' ?_ ?_ ?_
      · intro e; obtain ⟨a, ha⟩ := hi'; omega
      · intro e; exact h1 (by omega)
      · intro e; obtain ⟨a, ha⟩ := hi'; omega
    · intro i' hi' hlt ψ hψ
      exact biL_contAut ch.W hM Φ hΦ _ i' hi' (by omega) ψ hψ
    · intro ψ hψ
      rw [odd_step ch.W hM Φ hΦ h i (c - b - 2) (by omega) r hr ψ hψ,
        conAt_update ch.W hM Φ h (i + 1) _ (i + 1 + 1) (by omega) (by omega) (by omega)]

theorem rinv : Big fun ch => RInv ch :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => rinv_all ch⟩⟩

end GlobalTheory.RowLeftInv

end
