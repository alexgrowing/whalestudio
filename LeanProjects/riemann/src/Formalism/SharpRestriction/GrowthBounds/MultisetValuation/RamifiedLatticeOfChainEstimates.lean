import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RelativePresentationOfD7
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def EntCondition : Prop :=
  ∀ j < X.mm, ∀ (i0 : X.Pl → ℕ) (gP : X.Pl → ℚ), (∀ v, PlaceB X Y j v (i0 v) (gP v)) →
    EntB X Y j i0 (∑ v, (gP v : ℝ))

def RatCondition : Prop := ∀ v j, ∃ q : ℚ, X.g0v v j = q

def HeckeIntegralLevel : Prop :=
  ∀ v, ∀ j < X.mm, ∀ i ∈ Icc 1 X.G.P.r, ∀ F ∈ X.Int (j + 1), X.Tt v i (j + 1) F ∈ X.Int (j + 1)

theorem sum_ite_single {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι) (a : ℝ) (f : ι → ℝ) :
    ∑ v', (if v' = v then a else f v') = a + ∑ v' ∈ univ.erase v, f v' := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), if_pos rfl]
  congr 1
  refine Finset.sum_congr rfl fun v' hv' => ?_
  rw [if_neg (Finset.ne_of_mem_erase hv')]

variable {X Y}

theorem PlaceB.mono {j : ℕ} {v : X.Pl} {i : ℕ} {g g' : ℝ} (h : g' ≤ g) (hP : PlaceB X Y j v i g) :
    PlaceB X Y j v i g' := by
  unfold PlaceB at *
  rcases hP with ⟨hi, hL | hL⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨hi, Or.inl (Pend.LowAt.mono Y h hL)⟩
  · exact Or.inl ⟨hi, Or.inr (h.trans hL)⟩
  · exact Or.inr ⟨h1, h2, h.trans h3⟩

theorem EntB.mono {j : ℕ} {i0 : X.Pl → ℕ} {g g' : ℝ} (h : g' ≤ g) (hB : EntB X Y j i0 g) : EntB X Y j i0 g' := by
  unfold EntB at *
  intro La La' h1 h2 φ I n
  exact Pend.geC_mono Y h (hB La La' h1 h2 φ I n)

theorem ent_strict (hE : EntCondition X Y) (j : ℕ) (hj : j < X.mm) (i0 : X.Pl → ℕ) (gP : X.Pl → ℝ)
    (hP : ∀ v, PlaceB X Y j v (i0 v) (gP v)) (g' : ℝ) (hg : g' < ∑ v, gP v) : EntB X Y j i0 g' := by
  classical
  have hD : 0 < ∑ v, gP v - g' := sub_pos.mpr hg
  have hc : (0 : ℝ) < Fintype.card X.Pl + 1 := by positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (∑ v, gP v - g') / (Fintype.card X.Pl + 1) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact div_pos hD hc
  have hεc : (Fintype.card X.Pl : ℝ) * ε < ∑ v, gP v - g' := by
    have h1 : ε * (Fintype.card X.Pl + 1) = ∑ v, gP v - g' := by
      rw [hε]; exact div_mul_cancel₀ _ hc.ne'
    nlinarith
  have hq : ∀ v, ∃ q : ℚ, gP v - ε < q ∧ (q : ℝ) < gP v := fun v => exists_rat_btwn (by linarith)
  choose q hq1 hq2 using hq
  have hsum : g' ≤ ∑ v, (q v : ℝ) := by
    have h1 : ∑ v, (gP v - ε) ≤ ∑ v, (q v : ℝ) := Finset.sum_le_sum fun v _ => (hq1 v).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    linarith
  exact EntB.mono hsum (hE j hj i0 q fun v => PlaceB.mono (hq2 v).le (hP v))

theorem formB_lim (hF : FormB X Y) (j : ℕ) (hj : j < X.mm) (i0 : X.Pl → ℕ) (vs : List X.Pl) (g : ℝ) (hnd : vs.Nodup)
    (hr : ∀ v, i0 v ≤ X.G.P.r) (h0 : ∀ v, v ∉ vs → i0 v = 0) (hB : ∀ g' < g, EntB X Y j i0 g')
    (G : X.Fm j) (hG : G ∈ X.Int j) : X.vGe (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G)) (g - X.dG j) := by
  have he0 : (0 : ℝ) ≤ (X.eO : ℝ) := Nat.cast_nonneg _
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (g - X.dG j) * (X.eO : ℝ) := ⟨_, rfl⟩
  have hc1 : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
  have hc2 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (x - ⌈x⌉ + 1) / ((X.eO : ℝ) + 1) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (by linarith) (by linarith)
  have hδe : δ * (X.eO : ℝ) < x - ⌈x⌉ + 1 := by
    have h1 : δ * ((X.eO : ℝ) + 1) = x - ⌈x⌉ + 1 := by
      rw [hδ]; exact div_mul_cancel₀ _ (by linarith)
    nlinarith
  have hlin : (g - δ - X.dG j) * (X.eO : ℝ) = x - δ * (X.eO : ℝ) := by rw [hx]; ring
  have hceil : ⌈(g - δ - X.dG j) * (X.eO : ℝ)⌉ = ⌈(g - X.dG j) * (X.eO : ℝ)⌉ := by
    rw [← hx, Int.ceil_eq_iff, hlin]
    constructor
    · linarith
    · nlinarith
  have h := hF j hj i0 vs (g - δ) hnd hr h0 (hB _ (by linarith)) G hG
  have hv : X.vsc (g - δ - X.dG j) = X.vsc (g - X.dG j) := by rw [vsc_def, vsc_def, hceil]
  unfold Sys.vGe at h ⊢
  rw [hv] at h
  exact h

theorem form_of_place (hF : FormB X Y) (hE : EntCondition X Y) (j : ℕ) (hj : j < X.mm) (i0 : X.Pl → ℕ) (vs : List X.Pl)
    (gP : X.Pl → ℝ) (hnd : vs.Nodup) (hr : ∀ v, i0 v ≤ X.G.P.r) (h0 : ∀ v, v ∉ vs → i0 v = 0)
    (hP : ∀ v, PlaceB X Y j v (i0 v) (gP v)) (G : X.Fm j) (hG : G ∈ X.Int j) :
    X.vGe (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G)) (∑ v, gP v - X.dG j) :=
  formB_lim hF j hj i0 vs (∑ v, gP v) hnd hr h0 (fun g' hg' => ent_strict hE j hj i0 gP hP g' hg') G hG

theorem form_valuation_of_bound (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (h3 : adm3 D X Y) : Conclusion0 D X := by
  unfold Conclusion0
  intro j hj G hG
  have h := hF j hj (fun _ => 0) [] 0 List.nodup_nil (fun _ => Nat.zero_le _) (fun _ _ => rfl)
    (fun La La' h1 h2 φ I n => h3 j hj La La' h1 h2 φ I n) G hG
  rw [zero_sub] at h
  exact h

theorem theorem_A_entries_of_corollary (D : Formalism.BasicNotions.D7) (hE : EntCondition X Y) (hQ : RatCondition X) (h2U : VolumeRatio₂ D X Y) : projection_lemma_base_level D X Y := by
  unfold projection_lemma_base_level
  intro j hj La La' h1 h2 φ I n
  choose q hq using hQ
  have hP : ∀ v, PlaceB X Y j v 0 (q v (j + 1)) := fun v =>
    Or.inl ⟨rfl, Or.inl (by rw [← hq v (j + 1)]; exact h2U v j hj)⟩
  have h := hE j hj (fun _ => 0) (fun v => q v (j + 1)) hP La La' h1 h2 φ I n
  have hs : ∑ v, X.g0v v (j + 1) = ∑ v, ((q v (j + 1) : ℚ) : ℝ) :=
    Finset.sum_congr rfl fun v _ => hq v (j + 1)
  rw [hs]
  exact h

theorem slopeEstimate_of_lemmaB_slopeLine (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) : Conclusion2 D X := by
  unfold Conclusion2
  intro j hj G hG
  exact form_of_place hF hE j hj (fun _ => 0) [] (fun v => X.g0v v (j + 1)) List.nodup_nil
    (fun _ => Nat.zero_le _) (fun _ _ => rfl) (fun v => Or.inl ⟨rfl, Or.inl (h2U v j hj)⟩) G hG

theorem hecke_integral_of_forms (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) : MassRatio₂ D X := by
  classical
  unfold MassRatio₂
  intro v j hj G hG
  have hP : ∀ v', PlaceB X Y j v' 0
      (if v' = v then X.gv v (j + 1) - X.alEven v else X.g0v v' (j + 1)) := by
    intro v'
    by_cases hv : v' = v
    · subst hv
      rw [if_pos rfl]
      exact Or.inl ⟨rfl, Or.inr le_rfl⟩
    · rw [if_neg hv]
      exact Or.inl ⟨rfl, Or.inl (h2U v' j hj)⟩
  have h := form_of_place hF hE j hj (fun _ => 0) []
    (fun v' => if v' = v then X.gv v (j + 1) - X.alEven v else X.g0v v' (j + 1)) List.nodup_nil
    (fun _ => Nat.zero_le _) (fun _ _ => rfl) hP G hG
  beta_reduce at h
  rw [sum_ite_single] at h
  exact h

theorem hecke_valuation_of_entries (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) (v : X.Pl) (j : ℕ)
    (hj : j < X.mm) (i : ℕ) (hi : i ∈ Icc 1 X.G.P.r) (G : X.Fm j) (hG : G ∈ X.Int j) :
    X.vGe (j + 1) (X.Tt v i (j + 1) (X.Kz j G))
      (X.gv v (j + 1) + ∑ v' ∈ univ.erase v, X.g0v v' (j + 1) - X.dG j) := by
  classical
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  have hP : ∀ v', PlaceB X Y j v' (if v' = v then i else 0)
      (if v' = v then X.gv v (j + 1) else X.g0v v' (j + 1)) := by
    intro v'
    by_cases hv : v' = v
    · subst hv
      rw [if_pos rfl, if_pos rfl]
      exact Or.inr ⟨hi1, hi2, le_rfl⟩
    · rw [if_neg hv, if_neg hv]
      exact Or.inl ⟨rfl, Or.inl (h2U v' j hj)⟩
  have h := form_of_place hF hE j hj (fun v' => if v' = v then i else 0) [v]
    (fun v' => if v' = v then X.gv v (j + 1) else X.g0v v' (j + 1)) (List.nodup_singleton v)
    (fun v' => by split_ifs <;> omega)
    (fun v' hv' => if_neg (by simpa using hv')) hP G hG
  beta_reduce at h
  rw [sum_ite_single] at h
  simpa only [TtL, List.foldr_cons, List.foldr_nil, eq_self_iff_true, if_true, ↓reduceIte] using h

theorem latticeChain_succ_of_partial (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) (hB1 : HeckeIntegralLevel X) :
    PointsLemma D X := fun v j hj =>
  ⟨fun i hi F hF' => hB1 v j hj i hi F hF', fun i hi G hG => hecke_valuation_of_entries D hF hE h2U v j hj i hi G hG⟩

theorem ramifiedLattice_of_chain_estimates (D : Formalism.BasicNotions.D7) (h2U : VolumeRatio₂ D X Y) (h5D : LowTermBound D X Y) : Conclusion5 D X := by
  unfold Conclusion5
  refine ⟨fun v => relative_presentation_of_d7 D _ _ _ _ _ _ _ _ _ _ _ _ (X.std v), fun VV F hF => ?_⟩
  exact h5D X.gv X.g0v X.Conclusion₂ X.Svv VV (fun _ _ _ _ => le_rfl) h2U (fun _ _ _ _ => le_rfl)
    (fun _ _ => le_rfl) F hF

end Formalism.MainNotions.FormalGroupSystem.Pf
