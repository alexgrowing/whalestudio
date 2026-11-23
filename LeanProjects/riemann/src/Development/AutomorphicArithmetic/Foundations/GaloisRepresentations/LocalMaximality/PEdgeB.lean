import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma lft_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) :
    lft s ⊆ lft t := by
  intro a ha
  simp only [lft, Finset.mem_toLeft, Finset.mem_map] at ha ⊢
  obtain ⟨u, hu, e⟩ := ha
  exact ⟨u, h hu, e⟩

private lemma rgt_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) :
    rgt s ⊆ rgt t := by
  intro a ha
  simp only [rgt, Finset.mem_toRight, Finset.mem_map] at ha ⊢
  obtain ⟨u, hu, e⟩ := ha
  exact ⟨u, h hu, e⟩

private lemma omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q := by
  refine Submodule.span_mono ?_
  rintro y ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

private lemma wd_empty' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (w : ι → Module.End ℂ E)
    (c : Finset ι → E) : wd w c ∅ = 0 := by
  simp [wd]

private lemma acx_C' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] {A : Finset ι → Submodule ℂ E}
    {w : ι → Module.End ℂ E} {n : ℤ} {c : Finset ι → E} :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule ℂ E) :=
  ⟨fun h s => h s trivial, fun h s _ => h s⟩

private lemma cech_C' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] {A : Finset ι → Submodule ℂ E}
    {n : ℤ} {c : Finset ι → E} :
    c ∈ (cech A).C n ↔ ∀ s, c s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥ : Submodule ℂ E) :=
  ⟨fun h s => h s trivial, fun h s _ => h s⟩

theorem UpperTheory.Gal.productCup_of_system.edgeB_of :
    EdgeInj → RowEx → L1 → RYBasic → WdUni → WdBasic → EdgeB := by
  intro hEI hRow hL1 hRY hU hW
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h0 y hy hB
  obtain ⟨hRI, hGood, hRmono, -, -⟩ := hRY F K K' d x j2 h0
  have lu : ∀ I J : Finset (Fin (d + 1)), lft (uni I J) = I := fun I J =>
    (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) I J).2.1
  have ru : ∀ I J : Finset (Fin (d + 1)), rgt (uni I J) = J := fun I J =>
    (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) I J).2.2.1
  have cu : ∀ I J : Finset (Fin (d + 1)), (uni I J).card = I.card + J.card := fun I J =>
    (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) I J).2.2.2.1
  let G : Finset (Two d) → Submodule ℂ (DR ℂ K') := fun s => omB ℂ K' (RY (xv x) j2 (lft s) (rgt s)) d
  have hGm : ∀ I J, G (uni I J) = omB ℂ K' (RY (xv x) j2 I J) d := by
    intro I J
    simp only [G, lu, ru]
  have hG0 : ∀ I, G (uni I ∅) = omB ℂ K' (rB ℂ K' (xv x) I) d := by
    intro I
    rw [hGm, hRI]
  have hcech : (fun I => G (uni I ∅)) = fun I => omB ℂ K' (rB ℂ K' (xv x) I) d := funext hG0
  have hmix : (fun I J => G (uni I J)) = fun I J => omB ℂ K' (RY (xv x) j2 I J) d :=
    funext fun I => funext fun J => hGm I J
  obtain ⟨γ, hγ, hγ0, hγI⟩ := hEI (Fin (d + 1)) (DR ℂ K') G d y
    (by rw [hcech]; exact hy) (by rw [hmix]; exact hB)
  let A : Finset (Two d) → Submodule ℂ (DR ℂ K') := fun s => if (lft s).Nonempty then G s else ⊥
  have hAn : ∀ s, (lft s).Nonempty → A s = G s := fun s hs => if_pos hs
  have hAe : ∀ s, ¬ (lft s).Nonempty → A s = ⊥ := fun s hs => if_neg hs
  have hWOk : WOk A (fun _ => 1) := by
    refine ⟨fun _ _ => Commute.one_left _, ?_⟩
    intro s i _ m hm
    by_cases hs : (lft s).Nonempty
    · have hsub : s ⊆ insert i s := Finset.subset_insert _ _
      have hs' : (lft (insert i s)).Nonempty := hs.mono (lft_mono' hsub)
      rw [hAn _ hs] at hm
      show m ∈ A (insert i s)
      rw [hAn _ hs']
      exact omB_mono' (hRmono _ _ _ _ (lft_mono' hsub) (rgt_mono' hsub)) d hm
    · rw [hAe _ hs, Submodule.mem_bot] at hm
      show m ∈ A (insert i s)
      rw [hm]
      exact Submodule.zero_mem _
  have hKE : ∀ b, KE (colA A (fun _ => 1) b) ((d : ℤ) + 2) := by
    intro b m _
    by_cases hb : b.Nonempty
    · have e : (fun L => A (uni b L)) = fun J => omB ℂ K' (RY (xv x) j2 b J) d := by
        funext L
        rw [hAn _ (by rw [lu]; exact hb), hGm]
      show (acx (fun L => A (uni b L)) fun _ => 1).Z m ≤ (acx (fun L => A (uni b L)) fun _ => 1).B m
      rw [e]
      exact hRow F K K' d x j2 h0 d b hb m
    · intro c hc
      have hc0 : c = 0 := by
        funext L
        have h1 := acx_C'.1 hc.1 L
        have hA : A (uni b L) = ⊥ := hAe _ (by rw [lu]; exact hb)
        have h2 : c L ∈ (⊥ : Submodule ℂ (DR ℂ K')) := by
          simp only [hA, ite_self] at h1
          exact h1
        exact (Submodule.mem_bot ℂ).1 h2
      rw [hc0]
      exact Submodule.zero_mem _
  have hdelta : ∀ c : Finset (Two d) → DR ℂ K', wd (fun _ => (1 : Module.End ℂ (DR ℂ K'))) c = deltaL ℂ _ _ c :=
    (hW (Two d) (DR ℂ K') A (fun _ => 1)).2.2.2.2.1
  have hdelta' : ∀ c : Finset (Fin (d + 1)) → DR ℂ K', wd (fun _ => (1 : Module.End ℂ (DR ℂ K'))) c = deltaL ℂ _ _ c :=
    (hW (Fin (d + 1)) (DR ℂ K') (fun _ => ⊥) (fun _ => 1)).2.2.2.2.1
  have hγZ : γ ∈ (acx A fun _ => 1).Z ((d : ℤ) + 1) := by
    refine ⟨?_, ?_⟩
    · refine acx_C'.2 fun s => ?_
      have h1 := cech_C'.1 hγ.1 s
      by_cases hc : (s.card : ℤ) = (d : ℤ) + 1
      · rw [if_pos hc]
        by_cases hs : (lft s).Nonempty
        · rw [hAn _ hs]
          have hne : s.Nonempty := by
            rw [← Finset.card_pos]
            omega
          rw [if_pos ⟨hne, hc⟩] at h1
          exact h1
        · rw [hAe _ hs, Submodule.mem_bot]
          have hl : lft s = ∅ := Finset.not_nonempty_iff_eq_empty.1 hs
          have := hγ0 (rgt s)
          rwa [← hl, (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) ∅ ∅).2.2.2.2 s] at this
      · rw [if_neg hc]
        rw [if_neg (fun h => hc h.2)] at h1
        exact h1
    · show wd _ γ = 0
      rw [hdelta]
      exact hγ.2
  have hBγ : γ ∈ (acx A fun _ => 1).B ((d : ℤ) + 1) := by
    refine hL1 (Fin (d + 1)) (Fin (d + 1)) (DR ℂ K') A (fun _ => 1) ((d : ℤ) + 2) ((d : ℤ) + 1) hWOk hKE γ hγZ ?_ ?_
    · intro b L hL
      exfalso
      have : L.card ≤ d + 1 := by simpa using Finset.card_le_univ L
      omega
    · intro b hb
      exfalso
      have : (0 : ℤ) ≤ b.card := by positivity
      omega
  obtain ⟨η, hη, he⟩ := hBγ
  refine Submodule.mem_map.2 ⟨fun b => η (uni b ∅), ?_, ?_⟩
  · refine cech_C'.2 fun b => ?_
    have h1 := acx_C'.1 hη (uni b ∅)
    rw [cu] at h1
    simp only [Finset.card_empty, add_zero] at h1
    by_cases hb : b.Nonempty ∧ (b.card : ℤ) = (d : ℤ) - 1 + 1
    · rw [if_pos hb]
      have hc : (b.card : ℤ) = (d : ℤ) + 1 - 1 := by omega
      rw [if_pos hc, hAn _ (by rw [lu]; exact hb.1), hG0] at h1
      exact h1
    · rw [if_neg hb]
      by_cases hc : (b.card : ℤ) = (d : ℤ) + 1 - 1
      · have hne : ¬ b.Nonempty := fun h => hb ⟨h, by omega⟩
        rw [if_pos hc, hAe _ (by rw [lu]; exact hne)] at h1
        exact h1
      · rw [if_neg hc] at h1
        exact h1
  · funext I
    have e1 := (hU _ _ (DR ℂ K') (fun _ => 1) η I ∅).1
    rw [wd_empty', smul_zero, add_zero] at e1
    have e2 : wd (fun _ => (1 : Module.End ℂ (DR ℂ K'))) η = γ := he
    rw [e2, hγI] at e1
    rw [e1]
    exact (congrFun (hdelta' _) I).symm
