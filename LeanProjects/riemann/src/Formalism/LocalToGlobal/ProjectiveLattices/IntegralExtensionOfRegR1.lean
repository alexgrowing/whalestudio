import Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def RegularityR1 (X : PJ D B P j) (E : PtExt X) : Prop :=
  ∀ w (F : B.Cusp j w), (∀ la (y : X.Pt la), 0 ≤ X.vAt la y (X.inc w F)) →
    ∀ la (y' : E.Pt' la), 0 ≤ E.vAt' la y' (X.inc w F)

def RegularityR2 (X : PJ D B P j) (E : PtExt X)
    (NoZero : ∀ {wL : WeightFamilies.Wt D j} {n : ℕ}, (Fin n → B.Cusp j wL) → Prop) : Prop :=
  (∀ (wL wE : WeightFamilies.Wt D j) (n : ℕ) (gens : Fin n → B.Cusp j wL) (et : B.Cusp j wE)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (c : ℝ), 0 ≤ c → NoZero gens →
    (∀ la (y : X.Pt la), 0 ≤ X.vAt la y (X.inc wE et) ∧ (X.vAt la y (X.inc wE et) ≠ ⊤ →
      (⨅ k, X.vAt la y (X.inc wL (gens k))) ≤
        (((nus la : ℝ) + c * (X.vAt la y (X.inc wE et)).toReal : ℝ) : EReal))) →
    ∀ la (y' : E.Pt' la), 0 ≤ E.vAt' la y' (X.inc wE et) ∧ (E.vAt' la y' (X.inc wE et) ≠ ⊤ →
      (⨅ k, E.vAt' la y' (X.inc wL (gens k))) ≤
        (((nus la : ℝ) + c * (E.vAt' la y' (X.inc wE et)).toReal : ℝ) : EReal))) ∧
  (∀ (wL : WeightFamilies.Wt D j) (n : ℕ) (gens : Fin n → B.Cusp j wL) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    NoZero gens →
    (∀ la (y : X.Pt la), (⨅ k, X.vAt la y (X.inc wL (gens k))) ≤ ((nus la : ℝ) : EReal)) →
    ∀ la (y' : E.Pt' la), (⨅ k, E.vAt' la y' (X.inc wL (gens k))) ≤ ((nus la : ℝ) : EReal))

theorem iInf_span_eq {X : PJ D B P j} {wL : WeightFamilies.Wt D j} {n : ℕ} (g : Fin n → B.Cusp j wL)
    (la : HeightOneSpectrum (𝓞 B.KO)) (v : X.Forms → EReal) (hv0 : v 0 = ⊤)
    (hadd : ∀ F G, min (v F) (v G) ≤ v (F + G))
    (hsmul : ∀ (a : B.KO) F, a ≠ 0 → v (a • F) = (((vAdd la a : ℤ) : ℝ) : EReal) + v F)
    (hint : ∀ a : 𝓞 B.KO, (a : B.KO) ≠ 0 → 0 ≤ vAdd la (a : B.KO)) :
    (⨅ F ∈ Submodule.span (𝓞 B.KO) (Set.range g), v (X.inc wL F)) = ⨅ k, v (X.inc wL (g k)) := by
  apply le_antisymm
  · exact le_iInf fun k => iInf₂_le (g k) (Submodule.subset_span (Set.mem_range_self k))
  · refine le_iInf₂ fun F hF => ?_
    induction hF using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact iInf_le _ k
    | zero => simp [hv0]
    | add x y _ _ hx hy =>
      rw [map_add]; exact le_trans (le_min hx hy) (hadd _ _)
    | smul a x _ hx =>
      by_cases ha : (a : B.KO) = 0
      · have : a = 0 := by exact_mod_cast ha
        subst this; simp [hv0]
      · have hsm : X.inc wL (a • x) = (a : B.KO) • X.inc wL x := by
          rw [← map_smul]; congr 1; exact (algebraMap_smul B.KO a x).symm
        rw [hsm, hsmul _ _ ha]
        have h0 : (0 : EReal) ≤ (((vAdd la (a : B.KO) : ℤ) : ℝ) : EReal) := by
          exact_mod_cast hint a ha
        calc (⨅ k, v (X.inc wL (g k))) = 0 + ⨅ k, v (X.inc wL (g k)) := (zero_add _).symm
          _ ≤ _ := add_le_add h0 hx

def RegTrivK (X : PJ D B P j) (Q : Type) (ord : Q → X.Forms → EReal) : Prop :=
  (∀ w (F : B.Cusp j w), (∀ la (y : X.Pt la), 0 ≤ X.vAt la y (X.inc w F)) →
    ∀ q, 0 ≤ ord q (X.inc w F)) ∧
  (∀ (wL wE : WeightFamilies.Wt D j) (M : Submodule (𝓞 B.KO) (B.Cusp j wL)) (et : B.Cusp j wE)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (c : ℝ), 0 ≤ c →
    (∀ la (y : X.Pt la), 0 ≤ X.vAt la y (X.inc wE et) ∧ (X.vAt la y (X.inc wE et) ≠ ⊤ →
      (⨅ F ∈ M, X.vAt la y (X.inc wL F)) ≤
        (((nus la : ℝ) + c * (X.vAt la y (X.inc wE et)).toReal : ℝ) : EReal))) →
    ∀ q, 0 ≤ ord q (X.inc wE et) ∧ (ord q (X.inc wE et) ≠ ⊤ →
      (⨅ F ∈ M, ord q (X.inc wL F)) ≤ ((c * (ord q (X.inc wE et)).toReal : ℝ) : EReal)))

def gd2Xplus {ka wL wF : WeightFamilies.Wt D j} {X : PJ D B P j} (G : GlobalFamilyData X ka wL wF) (E : PtExt X)
    (hM : IntAtExt X E) : GlobalFamilyData (xplus X E hM) ka wL wF :=
  ⟨G.N, G.w, G.del, G.th', G.rz, G.alz, G.th0, G.zc, G.rq, G.th, G.iet, G.et, G.mx⟩

theorem combBound_xplus {ka wL wF : WeightFamilies.Wt D j} (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E)
    (NoZero : ∀ {wL : WeightFamilies.Wt D j} {n : ℕ}, (Fin n → B.Cusp j wL) → Prop)
    (G : GlobalFamilyData X ka wL wF) (S : Scal B) (c : ℝ) (hc : 0 ≤ c) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hspan : Submodule.span (𝓞 B.KO) (Set.range G.w) = X.WWc S.sW wL) (hNZ : NoZero G.w)
    (hint : ∀ (la : HeightOneSpectrum (𝓞 B.KO)) (a : 𝓞 B.KO), (a : B.KO) ≠ 0 → 0 ≤ vAdd la (a : B.KO))
    (hX : CombBound G S c nus) (hR2 : RegularityR2 X E NoZero) :
    CombBound (gd2Xplus G E hM) S c nus := by
  have dX : ∀ la (y : X.Pt la), X.depth S.sW wL la y = ⨅ k, X.vAt la y (X.inc wL (G.w k)) := by
    intro la y
    unfold PJ.depth
    rw [← hspan]
    exact iInf_span_eq G.w la (X.vAt la y) (X.vAt_zero la y) (X.vAt_add la y) (X.vAt_smul la y) (hint la)
  have dE : ∀ la (y : E.Pt' la), (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y (X.inc wL F)) =
      ⨅ k, E.vAt' la y (X.inc wL (G.w k)) := by
    intro la y
    rw [← hspan]
    exact iInf_span_eq G.w la (E.vAt' la y) (E.vAt'_zero la y) (E.vAt'_add la y) (E.vAt'_smul la y) (hint la)
  intro la y
  cases y with
  | inl y0 => exact hX la y0
  | inr y1 =>
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · have hc' : 0 ≤ c / (2 * (G.iet : ℝ)) := by positivity
      have := hR2.1 wL _ G.N G.w G.et nus _ hc' hNZ
        (fun la' y => by have h := (hX la' y).1 hj; rw [dX] at h; exact h) la y1
      show 0 ≤ E.vAt' la y1 (X.inc _ G.et) ∧ (E.vAt' la y1 (X.inc _ G.et) ≠ ⊤ →
        (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y1 (X.inc wL F)) ≤ _)
      rw [dE]; exact this
    · have := hR2.2 wL G.N G.w nus hNZ (fun la' y => by have h := (hX la' y).2 hj; rw [dX] at h; exact h) la y1
      show (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y1 (X.inc wL F)) ≤ _
      rw [dE]; exact this

section l2NormAlt

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

def gd2XplusN {ka wL wF : WeightFamilies.Wt D j} {X : PJ D B P j} (G : GlobalFamilyData X ka wL wF) (E : PtExt X)
    (hM : IntAtExt X E) : GlobalFamilyData (xplusN N h0 h1 h2 h3 h4 X E hM) ka wL wF :=
  ⟨G.N, G.w, G.del, G.th', G.rz, G.alz, G.th0, G.zc, G.rq, G.th, G.iet, G.et, G.mx⟩

end l2NormAlt

end Formalism.L2.Pj
