import Mathlib
import Formalism.PieriBlockIdeals.MultiplicityZeroThickEmbedding
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent.WorkedExample

open Formalism.CohomologicalDescent

theorem reflection_identity_holds : ReflIdentity := by
  intro n i μ
  constructor <;> push_cast <;> ring

theorem image_Icc_neg_shift (h x y : ℤ) :
    (Finset.Icc x y).image (fun u => h - u) = Finset.Icc (h - y) (h - x) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨h - z, ⟨by omega, by omega⟩, by omega⟩

theorem sub_modEq_sub_iff (l : ℕ) (h x u : ℤ) :
    h - x ≡ h - u [ZMOD (l : ℤ)] ↔ x ≡ u [ZMOD (l : ℤ)] := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, show h - u - (h - x) = -(u - x) by ring, dvd_neg]

theorem flip_sets_holds : FlipSets := by
  intro l b h t κ
  refine ⟨?_, ?_, fun x u => sub_modEq_sub_iff l h x u⟩
  · rw [image_Icc_neg_shift]
    congr 1 <;> ring
  · rw [image_Icc_neg_shift]
    congr 1 <;> ring

theorem weight_reflection_holds : MwFlip := by
  intro l b h t κ U
  unfold mwCount
  apply Finset.card_bij' (fun u _ => h - u) (fun u _ => h - u)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc] at hu ⊢
    obtain ⟨⟨⟨w, hw, rfl⟩, hB⟩, x, hx, hxu⟩ := hu
    refine ⟨⟨by simpa using hw, fun hc => hB ⟨by omega, by omega⟩⟩, h - x, ⟨by omega, by omega⟩, ?_⟩
    exact (Int.ModEq.refl h).sub hxu
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc] at hu ⊢
    obtain ⟨⟨hw, hB⟩, x, hx, hxu⟩ := hu
    refine ⟨⟨⟨u, hw, rfl⟩, fun hc => hB ⟨by omega, by omega⟩⟩, h - x, ⟨by omega, by omega⟩, ?_⟩
    exact (Int.ModEq.refl h).sub hxu
  · intro u _; ring
  · intro u _; ring

theorem prod_comp_eq_prod_comp {K : Type} [CommRing K] {N : ℕ} (f : Fin N → Polynomial K) (g : Polynomial K) :
    (∏ a, f a).comp g = ∏ a, (f a).comp g :=
  map_prod (Polynomial.compRingHom g) f Finset.univ

theorem linkage_reflection_holds : LinkageFlip := by
  intro K _ N U U' c c' h H
  have H2 := congrArg (fun p => p.comp (-Polynomial.X + Polynomial.C (((-h - c' - c : ℤ)) : K))) H
  simp only [prod_comp_eq_prod_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp] at H2
  have e : ∀ W : Fin N → ℤ, ∀ a : Fin N, -Polynomial.X + Polynomial.C (((-h - c' - c : ℤ)) : K) +
      Polynomial.C (((W a + c : ℤ)) : K) = -(Polynomial.X + Polynomial.C (((h - W a + c' : ℤ)) : K)) := by
    intro W a
    rw [neg_add, add_assoc, ← Polynomial.C_add, ← Polynomial.C_neg]
    congr 2
    push_cast
    ring
  simp only [e, Finset.prod_neg] at H2
  exact ((isUnit_neg_one).pow _).mul_left_cancel H2

theorem prod_X_add_C_shift_eq {K : Type} [CommRing K] {N : ℕ} (U U' : Fin N → ℤ) (c c' : ℤ)
    (H : (∏ a, (Polynomial.X + Polynomial.C (((U a + c : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' a + c : ℤ)) : K))) :
    (∏ a, (Polynomial.X + Polynomial.C (((U a + c' : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' a + c' : ℤ)) : K)) := by
  have H2 := congrArg (fun p => p.comp (Polynomial.X + Polynomial.C (((c' - c : ℤ)) : K))) H
  simp only [prod_comp_eq_prod_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp] at H2
  have e : ∀ W : Fin N → ℤ, ∀ a : Fin N, Polynomial.X + Polynomial.C (((c' - c : ℤ)) : K) +
      Polynomial.C (((W a + c : ℤ)) : K) = Polynomial.X + Polynomial.C (((W a + c' : ℤ)) : K) := by
    intro W a
    rw [add_assoc, ← Polynomial.C_add]
    congr 2
    push_cast
    ring
  simpa only [e] using H2

theorem residue_reflection_holds : ResidueFlip := by
  intro l N U U' h H
  have H2 := congrArg (Multiset.map (fun z : ZMod l => (h : ZMod l) - z)) H
  simpa [Multiset.map_map, Function.comp_def, Int.cast_sub] using H2

theorem weight_letters_holds : MwLetters := by
  intro ι N D σ h t hR l κ i
  obtain ⟨_, _, _, hU, _, hbot⟩ := hR
  unfold Labels.mw
  have himg : Finset.univ.image (D.U (D.cc i)) =
      (Finset.univ.image (D.U i)).image (fun u => (h : ℤ) - u) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨D.U i (Fin.rev a), ⟨_, rfl⟩, (hU i a).symm⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨Fin.rev a, by rw [hU, Fin.rev_rev]⟩
  rw [himg, hbot]
  exact weight_reflection_holds l (D.bot i) h t κ _

theorem linked_all_holds : LinkedAll := by
  intro ι N D σ h t F _ cst hR hL
  obtain ⟨hinv, _, hΦ, hU, hU', hbot⟩ := hR
  have hc : ∀ i ∈ D.Φ, StrictAnti (D.U (D.cc i)) ∧ StrictAnti (D.U' (D.cc i)) ∧
      (∀ s : Fin t, ∃ a, D.U (D.cc i) a = D.bot (D.cc i) + ((s : ℕ) : ℤ)) ∧
      (∏ a, (Polynomial.X + Polynomial.C (((D.U (D.cc i) a + 0 : ℤ)) : F))) =
        ∏ a, (Polynomial.X + Polynomial.C (((D.U' (D.cc i) a + 0 : ℤ)) : F)) := by
    intro i hi
    obtain ⟨h1, h2, h3, h4⟩ := hL i hi
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      rw [hU, hU]
      have := h1 (Fin.rev_lt_rev.mpr hab)
      omega
    · intro a b hab
      rw [hU', hU']
      have := h2 (Fin.rev_lt_rev.mpr hab)
      omega
    · intro s
      obtain ⟨a, ha⟩ := h3 (Fin.rev s)
      refine ⟨Fin.rev a, ?_⟩
      rw [hU, Fin.rev_rev, ha, hbot]
      have e1 : ((Fin.rev s : Fin t) : ℕ) = t - (s + 1) := Fin.val_rev s
      have e2 := s.isLt
      omega
    · have e := linkage_reflection_holds F N (D.U i) (D.U' i) (cst i) 0 h h4
      have r1 := Equiv.prod_comp Fin.revPerm
        (fun a => (Polynomial.X + Polynomial.C ((((h : ℤ) - D.U i a + 0 : ℤ)) : F)))
      have r2 := Equiv.prod_comp Fin.revPerm
        (fun a => (Polynomial.X + Polynomial.C ((((h : ℤ) - D.U' i a + 0 : ℤ)) : F)))
      simp only [Fin.revPerm_apply] at r1 r2
      simp only [hU, hU']
      rw [r1, r2, e]
  intro i
  rcases hΦ i with hi | hi
  · obtain ⟨h1, h2, h3, h4⟩ := hL i hi
    exact ⟨h1, h2, h3, prod_X_add_C_shift_eq _ _ _ _ h4⟩
  · have := hc (D.cc i) hi
    rwa [hinv i] at this

theorem reflection_carried_facts {ι : Type} {N : ℕ} (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) (ep : ι → ι)
    (J : ι → Fin N → ℤ) (botJ : ι → ℤ) (hR : D.Refl σ h t) (hC : D.Carried ep J botJ) :
    (∀ i, ep (ep i) = i) ∧ (∀ i, σ (ep i) = ep (σ i)) ∧ (∀ i, J i = D.U' (ep i)) ∧
      (∀ i, botJ i = D.bot (ep i)) := by
  obtain ⟨hinv, hcom, _⟩ := hR
  obtain ⟨hep, hJ, hb⟩ := hC
  have h1 : ∀ i, ep (ep i) = i := by
    rcases hep with rfl | rfl
    · intro i; rfl
    · exact hinv
  have h2 : ∀ i, σ (ep i) = ep (σ i) := by
    rcases hep with rfl | rfl
    · intro i; rfl
    · exact hcom
  refine ⟨h1, h2, fun i => ?_, fun i => ?_⟩
  · rw [← hJ (ep i), h1]
  · rw [← hb (ep i), h1]

theorem orientation_holds : WEOrient := by
  intro ι _ σ k j t q l h F _ _ W D cst ep J botJ kap c τ hl hsmall hR hL hC hW hs hk hS hU'h hc
  obtain ⟨hinv, hcom, hJ, hb⟩ := reflection_carried_facts D σ h t ep J botJ hR hC
  have all := linked_all_holds ι _ D σ h t F cst hR hL
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have e1 : D.U (ep (ep τ)) = D.U τ := by rw [hinv]
  have e2 : J (ep τ) = D.U' τ := hC.2.1 τ
  have e3 : botJ (ep τ) = D.bot τ := hC.2.2 τ
  have e4 : σ (ep τ) = ep (σ τ) := hcom τ
  have e5 : botJ (ep (σ τ)) = D.bot (σ τ) := hC.2.2 _
  have e6 : D.U (ep (ep (σ τ))) = D.U (σ τ) := by rw [hinv]
  have key := weightExchangeFull_holds ι σ k j t q l h F W (fun i => D.U (ep i)) J botJ (fun _ => 0) kap c (ep τ)
    hl hsmall hW hs hk (fun i => (all (ep i)).1) (fun i => by rw [hJ]; exact (all (ep i)).2.1)
    (fun i s => by rw [hb]; exact (all (ep i)).2.2.1 s)
    (fun i => by rw [hJ]; exact (all (ep i)).2.2.2)
    (by intro a; show 0 ≤ D.U (ep (ep τ)) a; rw [e1]; exact hS1 a)
    (by intro a; rw [e2]; exact hU'h a)
    (by show ∑ a, D.U (ep (ep τ)) a = _; rw [e1, e2]; exact hS2)
    (by intro a h1 h2; show D.U (ep (ep τ)) a = _; rw [e1, e3]; exact hS3 a h1 h2)
    (by rw [e2]; exact hc)
  simp only [e4, e1, e2, e3, e5, e6] at key
  exact key

theorem orientation_inputs_holds : WEOrientInputs := by
  intro ι _ σ k j t q l h _ O F _ _ _ _ _ W u c D cst ep J botJ kap τ hl hsmall hR hL hC hW hS
  obtain ⟨hinv, hcom, hJ, hb⟩ := reflection_carried_facts D σ h t ep J botJ hR hC
  have all := linked_all_holds ι _ D σ h t F cst hR hL
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have e1 : D.U (ep (ep τ)) = D.U τ := by rw [hinv]
  have e2 : J (ep τ) = D.U' τ := hC.2.1 τ
  have e3 : botJ (ep τ) = D.bot τ := hC.2.2 τ
  have e4 : σ (ep τ) = ep (σ τ) := hcom τ
  have e5 : botJ (ep (σ τ)) = D.bot (σ τ) := hC.2.2 _
  have e6 : D.U (ep (ep (σ τ))) = D.U (σ τ) := by rw [hinv]
  have key := FrobeniusPeriodChange.weight_exponents_from_inputs ι σ k j t q l h O F W u c (fun i => D.U (ep i)) J botJ
    (fun _ => 0) kap (ep τ)
    hl hsmall hW (fun i => (all (ep i)).1) (fun i => by rw [hJ]; exact (all (ep i)).2.1)
    (fun i s => by rw [hb]; exact (all (ep i)).2.2.1 s)
    (fun i => by rw [hJ]; exact (all (ep i)).2.2.2)
    (by intro a; show 0 ≤ D.U (ep (ep τ)) a; rw [e1]; exact hS1 a)
    (by show ∑ a, D.U (ep (ep τ)) a = _; rw [e1, e2]; exact hS2)
    (by intro a h1 h2; show D.U (ep (ep τ)) a = _; rw [e1, e3]; exact hS3 a h1 h2)
  simp only [e4, e1, e2, e3, e5, e6] at key
  exact key

theorem orientation_lattice_holds : WEOrientLattice := by
  intro ι _ σ k j t q l h _ O F L _ _ _ _ _ _ I _ W u c D cst ep J botJ kap τ ζ em jj hl hsmall hR hL
    hC hW hS
  obtain ⟨hinv, hcom, hJ, hb⟩ := reflection_carried_facts D σ h t ep J botJ hR hC
  have all := linked_all_holds ι _ D σ h t F cst hR hL
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have e1 : D.U (ep (ep τ)) = D.U τ := by rw [hinv]
  have e2 : J (ep τ) = D.U' τ := hC.2.1 τ
  have e3 : botJ (ep τ) = D.bot τ := hC.2.2 τ
  have e4 : σ (ep τ) = ep (σ τ) := hcom τ
  have e5 : botJ (ep (σ τ)) = D.bot (σ τ) := hC.2.2 _
  have e6 : D.U (ep (ep (σ τ))) = D.U (σ τ) := by rw [hinv]
  have key := FrobeniusPeriodChange.weight_exponents_from_lattice ι σ k j t q l h O F L I W u c (fun i => D.U (ep i)) J botJ
    (fun _ => 0) kap (ep τ) ζ em jj
    hl hsmall hW (fun i => (all (ep i)).1) (fun i => by rw [hJ]; exact (all (ep i)).2.1)
    (fun i s => by rw [hb]; exact (all (ep i)).2.2.1 s)
    (fun i => by rw [hJ]; exact (all (ep i)).2.2.2)
    (by intro a; show 0 ≤ D.U (ep (ep τ)) a; rw [e1]; exact hS1 a)
    (by show ∑ a, D.U (ep (ep τ)) a = _; rw [e1, e2]; exact hS2)
    (by intro a h1 h2; show D.U (ep (ep τ)) a = _; rw [e1, e3]; exact hS3 a h1 h2)
  simp only [e4, e1, e2, e3, e5, e6] at key
  exact key

theorem card_filter_Ico_eq_sub (N x y : ℕ) (hy : y ≤ N) :
    (Finset.univ.filter (fun a : Fin N => x ≤ (a : ℕ) ∧ (a : ℕ) < y)).card = y - x := by
  have e : (Finset.univ.filter (fun a : Fin N => x ≤ (a : ℕ) ∧ (a : ℕ) < y)).map Fin.valEmbedding =
      Finset.Ico x y := by
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hm
      exact ⟨⟨m, by omega⟩, hm, rfl⟩
  rw [← Finset.card_map, e, Nat.card_Ico]

theorem sum_split_three_intervals {N : ℕ} (f : Fin N → ℤ) (x y : ℕ) (hxy : x ≤ y) :
    ∑ a, f a = ∑ a ∈ Finset.univ.filter (fun a : Fin N => (a : ℕ) < x), f a +
      ∑ a ∈ Finset.univ.filter (fun a : Fin N => x ≤ (a : ℕ) ∧ (a : ℕ) < y), f a +
      ∑ a ∈ Finset.univ.filter (fun a : Fin N => y ≤ (a : ℕ)), f a := by
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs <;> first | (exfalso; omega) | simp

theorem arithmetic_reflected_holds : WEArithReflected := by
  intro k j t q l h κ mw mwp U U' kc kp _ _ hU hU' hsum hminor hkc hkp
  have sU := sum_split_three_intervals U (k + j) (k + j + t) (by omega)
  have sU' := sum_split_three_intervals U' t (k + j + t) (by omega)
  have c1 : (univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < t)).card = t := by
    have := card_filter_Ico_eq_sub (k + j + t + q) 0 t (by omega)
    simpa using this
  have c2 : (univ.filter
      (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t)).card = t := by
    have := card_filter_Ico_eq_sub (k + j + t + q) (k + j) (k + j + t) (by omega)
    omega
  have c3 : (univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j)).card = k + j := by
    have := card_filter_Ico_eq_sub (k + j + t + q) 0 (k + j) (by omega)
    simpa using this
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, c1, c2]
    at hminor
  have hmid : 0 ≤ ∑ a ∈ univ.filter
      (fun a : Fin (k + j + t + q) => t ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U' a :=
    Finset.sum_nonneg (fun a _ => hU' a)
  have htop : ∑ a ∈ univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), U a ≤
      ((k : ℤ) + j) * h := by
    calc _ ≤ (univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j)).card • (h : ℤ) :=
          Finset.sum_le_card_nsmul _ _ _ (fun a _ => hU a)
      _ = ((k : ℤ) + j) * h := by rw [c3, nsmul_eq_mul]; push_cast; ring
  have hkp' : (l : ℤ) * kp ≤ (l : ℤ) * ((mwp : ℤ) * ((t : ℤ) + 2 * κ)) :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self kp) hkp) (Int.natCast_nonneg l)
  have hkc' : -kc ≤ (mw : ℤ) * ((t : ℤ) + 2 * κ) := le_trans (neg_le_abs kc) hkc
  have e : ((l : ℤ) * mwp + mw) * ((t : ℤ) + 2 * κ) =
      (l : ℤ) * ((mwp : ℤ) * ((t : ℤ) + 2 * κ)) + (mw : ℤ) * ((t : ℤ) + 2 * κ) := by ring
  rw [Finset.sum_sub_distrib, e]
  linarith

theorem example_parameters_holds : WeightAddRhoEqParameter := by
  intro p q' t v β e i
  unfold twistedSequenceWeight exampleParameterVector rho
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      simp only [Fin.append_left, aPlus, Fin.val_castAdd]
      push_cast
      ring
    | right a =>
      simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
      push_cast
      ring
  | right c =>
    simp only [Fin.append_right, aMinus, Fin.rev_rev, Fin.val_natAdd]
    push_cast
    ring

theorem example_run_entry_eq (p q' t : ℕ) (v : Fin p → ℝ) (β : Fin q' → ℝ) (e : ℝ) (a : Fin t) :
    exampleParameterVector p q' t v β e (Fin.castAdd q' (Fin.natAdd p a)) =
      -e + ((t : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) := by
  simp only [exampleParameterVector, Fin.append_left, Fin.append_right]
  ring

theorem example_run_holds : ParameterSequenceCentred := by
  intro p q' t v β e a
  refine ⟨example_run_entry_eq p q' t v β e a, ?_⟩
  rw [example_run_entry_eq, example_run_entry_eq, Fin.val_rev]
  have ha : (a : ℕ) + 1 ≤ t := a.isLt
  rw [Nat.cast_sub ha]
  push_cast
  ring

theorem append_strictAnti {m n : ℕ} (f : Fin m → ℝ) (g : Fin n → ℝ) (hf : StrictAnti f)
    (hg : StrictAnti g) (hfg : ∀ i j, g j < f i) : StrictAnti (Fin.append f g) := by
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.append_left]
      rw [Fin.lt_def] at hij
      exact hf (by rw [Fin.lt_def]; simpa only [Fin.coe_castAdd] using hij)
    | right j =>
      simp only [Fin.append_left, Fin.append_right]
      exact hfg i j
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      exfalso
      rw [Fin.lt_def] at hij
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hij
      have := j.isLt
      omega
    | right j =>
      simp only [Fin.append_right]
      rw [Fin.lt_def] at hij
      exact hg (by rw [Fin.lt_def]; simpa only [Fin.coe_natAdd, Nat.add_lt_add_iff_left] using hij)

theorem example_order_holds : ParameterStrictOrder := by
  intro p q' t v β e hv hβ h1 h2 h3
  unfold exampleParameterVector
  refine append_strictAnti _ _ ?_ (fun a b hab => neg_lt_neg (hβ hab)) ?_
  · refine append_strictAnti _ _ hv ?_ ?_
    · intro a b hab
      have h' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := Nat.cast_lt.mpr hab
      try dsimp only
      linarith
    · intro i a
      have h0 : (0 : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg _
      have := h1 i
      try dsimp only
      linarith
  · intro i c
    induction i using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      exact h3 i c
    | right a =>
      simp only [Fin.append_right]
      have ha : ((a : ℕ) : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast Nat.succ_le_of_lt a.isLt
      have := h2 c
      linarith

theorem example_shape_holds : ParameterShapeBounds := by
  intro P kc j q' cloud bu bd e c σ z bot hσ hcl hbu hbd hz hbot
  have hσ2 : (σ : ℝ) * (σ : ℝ) = 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hv : ∀ a, (σ : ℝ) * ((z a : ℝ) - c) =
      exampleParameterVector (kc + j) q' P.t (Fin.append cloud fun i => -bu i) bd e a := by
    intro a
    rw [hz a, example_parameters_holds]
    linear_combination
      (exampleParameterVector (kc + j) q' P.t (Fin.append cloud fun i => -bu i) bd e a) * hσ2
  have hblk : ∀ s : Fin P.t, (σ : ℝ) * ((z (Fin.castAdd q' (Fin.natAdd (kc + j) s)) : ℝ) - c) =
      -e + ((P.t : ℝ) - 1) / 2 - ((s : ℕ) : ℝ) := by
    intro s; rw [hv, example_run_entry_eq]
  obtain ⟨⟨s0, hs0⟩, hmin⟩ := hbot
  have hmin' : ∀ s : Fin P.t, (bot : ℝ) ≤ (z (Fin.castAdd q' (Fin.natAdd (kc + j) s)) : ℝ) := by
    intro s
    have : bot ≤ z (Fin.castAdd q' (Fin.natAdd (kc + j) s)) := hmin ⟨s, rfl⟩
    exact_mod_cast this
  have hs0' : (z (Fin.castAdd q' (Fin.natAdd (kc + j) s0)) : ℝ) = (bot : ℝ) := by
    have : z (Fin.castAdd q' (Fin.natAdd (kc + j) s0)) = bot := hs0
    exact_mod_cast this
  have ht : 0 < P.t := lt_of_le_of_lt (Nat.zero_le _) s0.isLt
  have hle : ∀ s : Fin P.t, ((s : ℕ) : ℝ) + 1 ≤ (P.t : ℝ) := fun s => by exact_mod_cast s.isLt
  have hge : ∀ s : Fin P.t, (0 : ℝ) ≤ ((s : ℕ) : ℝ) := fun s => Nat.cast_nonneg _

  have main : (σ : ℝ) * ((bot : ℝ) + ((P.t : ℝ) - 1) / 2 - c) = -e ∧
      ∀ s : Fin P.t, (z (Fin.castAdd q' (Fin.natAdd (kc + j) s)) : ℝ) ≤ (bot : ℝ) + (P.t : ℝ) - 1 := by
    rcases hσ with rfl | rfl
    · let sl : Fin P.t := ⟨P.t - 1, by omega⟩
      have hsl : ((sl : ℕ) : ℝ) = (P.t : ℝ) - 1 := by
        show ((P.t - 1 : ℕ) : ℝ) = _
        rw [Nat.cast_sub (by omega)]; simp
      have a1 := hblk s0
      have a2 := hblk sl
      have a3 := hmin' sl
      have a4 := hle s0
      rw [hs0'] at a1
      rw [hsl] at a2
      push_cast at a1 a2 ⊢
      have hs : ((s0 : ℕ) : ℝ) = (P.t : ℝ) - 1 := by linarith
      refine ⟨by linarith, fun s => ?_⟩
      have a5 := hblk s
      have a6 := hge s
      push_cast at a5
      linarith
    · let sf : Fin P.t := ⟨0, ht⟩
      have hsf : ((sf : ℕ) : ℝ) = 0 := by simp [sf]
      have a1 := hblk s0
      have a2 := hblk sf
      have a3 := hmin' sf
      have a4 := hge s0
      rw [hs0'] at a1
      rw [hsf] at a2
      push_cast at a1 a2 ⊢
      have hs : ((s0 : ℕ) : ℝ) = 0 := by linarith
      refine ⟨by linarith, fun s => ?_⟩
      have a5 := hblk s
      have a6 := hle s
      push_cast at a5
      linarith
  refine ⟨hσ, main.1, ?_⟩
  intro u hu hnot
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
  rw [hv a]
  induction a using Fin.addCases with
  | left a =>
    induction a using Fin.addCases with
    | left a =>
      induction a using Fin.addCases with
      | left i =>
        left
        simp only [exampleParameterVector, Fin.append_left]
        exact hcl i
      | right i =>
        right
        simp only [exampleParameterVector, Fin.append_left, Fin.append_right]
        have : -bu i + e = -(bu i - e) := by ring
        rw [this, abs_neg]
        exact hbu i
    | right s =>
      exfalso
      apply hnot
      rw [Finset.mem_Icc]
      constructor
      · exact hmin ⟨s, rfl⟩
      · have := main.2 s
        have h2 : (z (Fin.castAdd q' (Fin.natAdd (kc + j) s)) : ℝ) ≤
            ((bot + (P.t : ℤ) - 1 : ℤ) : ℝ) := by push_cast; exact this
        exact_mod_cast h2
  | right i =>
    right
    simp only [exampleParameterVector, Fin.append_right]
    have : -bd i + e = -(bd i - e) := by ring
    rw [this, abs_neg]
    exact hbd i

theorem example_weight_zero_holds : MultiplicityZeroThickEmbedding := by
  intro P H G l hl hlJ kc j q' cloud bu bd e c σ z bot hσ hcl hbu hbd hz hbot hcase
  exact LogSmallConstantBounds.noWindowResidue_holds P H G l hl hlJ _ bot c e σ
    (example_shape_holds P kc j q' cloud bu bd e c σ z bot hσ hcl hbu hbd hz hbot) hcase

theorem slack_size_holds : SlackSize := by
  intro P H G
  have N := LogSmallConstantBounds.natBounds H
  have hD := LogSmallConstantBounds.le_lstarDenom H G
  have hDp := LogSmallConstantBounds.lstarDenom_pos H G
  have hb := LogSmallConstantBounds.b_pos' P
  have hL := G.L_ge
  have hls := LogSmallConstantBounds.lstar_pos H G
  have t6 := N.t6; have m1 := N.m1; have mt := N.mt
  have hr : P.b / P.lstar = LogSmallConstantBounds.lstarDenom P / (P.m : ℝ) := by
    rw [LogSmallConstantBounds.lstar_eq_div]; field_simp
  constructor
  · rw [hr, le_div_iff₀ (by linarith)]
    have hL2 : (16 : ℝ) ≤ P.L ^ 2 := by nlinarith
    have h1 : (P.t : ℝ) ^ 3 * 16 ≤ (P.t : ℝ) ^ 3 * P.L ^ 2 := by gcongr
    have h2 : 48 * (P.t : ℝ) ^ 2 * (P.m : ℝ) ≤ (P.t : ℝ) ^ 3 * 16 := by
      have : 0 ≤ (P.t : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  · intro l hl
    have hbE := LogSmallConstantBounds.paramsLStar_holds P H G
    have h0 := LogSmallConstantBounds.paramsBasic_holds P H G
    have h7 := LogSmallConstantBounds.seven_lt_lstar H G
    have hl1 : 3 * P.lstar ≤ (l : ℝ) - 1 := by nlinarith [hbE.1]
    have hl1p : 0 < (l : ℝ) - 1 := by linarith
    have hh : 0 ≤ P.h := by have := LogSmallConstantBounds.b_add_seven_le_h H; linarith
    have k1 : (P.kap l : ℝ) ≤ P.h / ((l : ℝ) - 1) := Nat.floor_le (by positivity)
    have k2 : P.h / ((l : ℝ) - 1) ≤ 2 * P.b / (3 * P.lstar) := by
      apply div_le_div₀ (by positivity) h0.2.2 (by positivity) hl1
    have k3 : 2 * P.b / (3 * P.lstar) = 2 / 3 * (P.b / P.lstar) := by field_simp
    linarith

theorem no_residue_displaced_holds : NoResDisplaced := by
  intro P H G l hlp hl U bot c e δ σ hδ hS hk
  obtain ⟨hσ, hc, hU⟩ := hS
  have N := LogSmallConstantBounds.natBounds H
  have d := LogSmallConstantBounds.paramsLargePrime_holds P H G l hl
  have fE := LogSmallConstantBounds.paramsTop_holds P H G
  have fF := LogSmallConstantBounds.paramsThin_holds P H G
  have sl := slack_size_holds P H G
  have r2 : 2 * P.b / P.lstar = 2 * (P.b / P.lstar) := by ring
  have r8 : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := by ring
  have t6 := N.t6
  have hr48 : 48 * (P.t : ℝ) ^ 2 ≤ P.b / P.lstar := sl.1
  have hr3 : (3 : ℝ) ≤ P.b / P.lstar := by nlinarith
  have hκ0 := sl.2 l hl

  have hκ : (P.kap l : ℝ) + |δ| ≤ 2 * (P.b / P.lstar) - 1 := by linarith
  have hκm : (P.kap l : ℝ) + |δ| ≤ (P.kmax : ℝ) := by
    have : 2 * P.b / P.lstar < (P.kmax : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [r2] at this
    linarith
  have hδ' := abs_le.mp (le_refl |δ|)
  apply windowResidueCountEqZero_holds
  intro u hu hub x hx
  rw [Finset.mem_Icc] at hx
  have x1 : (bot : ℝ) - (P.kap l : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx.1
  have x2 : (x : ℝ) ≤ (bot : ℝ) + (P.t : ℝ) - 1 + (P.kap l : ℝ) := by exact_mod_cast hx.2
  have hs2 : (σ : ℝ) = 1 ∨ (σ : ℝ) = -1 := by rcases hσ with h | h <;> simp [h]
  have hcast : ((|u - x| : ℤ) : ℝ) = |(u : ℝ) - (x : ℝ)| := by push_cast; rfl
  have hzc : ((σ * (u - x) : ℤ) : ℝ) =
      ((σ : ℝ) * ((u : ℝ) - c) + e) - ((σ : ℝ) * ((x : ℝ) - c) + e) := by push_cast; ring
  have hB : |(σ : ℝ) * ((x : ℝ) - c) + e| ≤ ((P.t : ℝ) - 1) / 2 + ((P.kap l : ℝ) + |δ|) := by
    have e1 : (σ : ℝ) * ((x : ℝ) - c) + e =
        (σ : ℝ) * ((x : ℝ) - (bot : ℝ) - ((P.t : ℝ) - 1) / 2) + δ := by
      linear_combination hc
    have e2 : |(σ : ℝ) * ((x : ℝ) - (bot : ℝ) - ((P.t : ℝ) - 1) / 2)| ≤
        ((P.t : ℝ) - 1) / 2 + (P.kap l : ℝ) := by
      rw [abs_mul]
      have : |(σ : ℝ)| = 1 := by rcases hs2 with h | h <;> simp [h]
      rw [this, one_mul, abs_le]; constructor <;> linarith
    rw [e1]
    have := abs_add_le ((σ : ℝ) * ((x : ℝ) - (bot : ℝ) - ((P.t : ℝ) - 1) / 2)) δ
    linarith
  have hAB : |((σ : ℝ) * ((u : ℝ) - c) + e) - ((σ : ℝ) * ((x : ℝ) - c) + e)| = |(u : ℝ) - (x : ℝ)| := by
    have : ((σ : ℝ) * ((u : ℝ) - c) + e) - ((σ : ℝ) * ((x : ℝ) - c) + e)
        = (σ : ℝ) * ((u : ℝ) - (x : ℝ)) := by ring
    rw [this, abs_mul]
    have : |(σ : ℝ)| = 1 := by rcases hs2 with h | h <;> simp [h]
    rw [this, one_mul]
  generalize hAdef : (σ : ℝ) * ((u : ℝ) - c) + e = A at *
  generalize hBdef : (σ : ℝ) * ((x : ℝ) - c) + e = B at *
  have hBB := abs_le.mp hB
  have crit : 0 < |A - B| → |A - B| < (l : ℝ) → (0 < |u - x| ∧ |u - x| < (l : ℤ)) := by
    intro a1 a2
    rw [hAB, ← hcast] at a1 a2
    exact ⟨by exact_mod_cast a1, by exact_mod_cast a2⟩
  rcases hU u hu hub with hcl | hlow
  ·
    have hv : (σ : ℝ) * ((u : ℝ) - c) = A - e := by linarith
    rw [hv] at hcl
    rcases hk with ⟨hth, hex⟩ | htop | hthin
    · right
      intro hdvd
      apply hex
      refine ⟨σ * (u - x), ?_, ?_, Dvd.dvd.mul_left hdvd σ⟩
      · rw [hzc]; have := hth.1; linarith [hBB.2]
      · rw [hzc]; have := hth.2; linarith [hBB.1]
    · left
      obtain ⟨bt, b1, b2, b3, b4⟩ := htop
      have bp := H.b'_pos
      have hx := H.x_ge
      have q1 : 0 ≤ P.b' / P.x := by positivity
      have tl := G.top_le
      have e1 : P.b' * (1 + 1 / P.x + 1 / P.x ^ 2) = P.b' * (1 + 1 / P.x ^ 2) + P.b' / P.x := by ring
      rw [e1] at tl
      have pos : 0 < A - B := by linarith [hBB.2, fF.1, fF.2]
      apply crit
      · rw [abs_of_pos pos]; exact pos
      · rw [abs_of_pos pos]; linarith [hBB.1, fF.1, fF.2]
    · left
      have bp := H.b'_pos
      have hx := H.x_ge
      have q1 : 0 ≤ P.b' / P.x := by positivity
      have q2 : 0 ≤ P.b' * (1 / P.x ^ 2) := by positivity
      have tl := G.top_le
      have e1 : P.b' * (1 + 1 / P.x + 1 / P.x ^ 2) = P.b' + P.b' * (1 / P.x ^ 2) + P.b' / P.x := by ring
      rw [e1] at tl
      have pos : 0 < A - B := by linarith [hBB.2, fF.1, fF.2, hthin.1]
      apply crit
      · rw [abs_of_pos pos]; exact pos
      · rw [abs_of_pos pos]; linarith [hBB.1, fF.1, fF.2, hthin.2]
  ·
    left
    rw [r2, hAdef] at hlow
    have g1 : |A| - |B| ≤ |A - B| := abs_sub_abs_le_abs_sub A B
    have g2 : |A - B| ≤ |A| + |B| := abs_sub A B
    have w := H.win_lt
    rw [r8] at w
    have te := H.t_le
    have dl := d.1
    apply crit
    · linarith [hlow.1]
    · linarith [hlow.2]

theorem line_c_identity_holds : LstarGapInequalities := by
  intro P H G
  have h1 := H.sum_lt
  have h2 := H.win_lt
  have h3 := H.b'_pos
  have h4 := LogSmallConstantBounds.b_div_lstar_pos H G
  have h5 := LogSmallConstantBounds.eta_nonneg' H
  have h6 := LogSmallConstantBounds.two_mul_lstar_le_b H G
  have e8 : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := mul_div_assoc _ _ _
  have e2 : 2 * P.b / P.lstar = 2 * (P.b / P.lstar) := mul_div_assoc _ _ _
  rw [e8] at h2
  rw [e2]
  refine ⟨by linarith, by linarith, by linarith, h6, by linarith⟩

theorem tail_line_c_holds : ParameterQuotientBoundOfTwoLeF := by
  intro P H hf hL
  have ht := H.t_ge
  have hm := H.m_pos
  have hmk := H.m_le
  have hN := H.Nr_eq
  have ht6 : 6 ≤ P.t := by omega
  have hk : 1 ≤ P.k := by omega
  have hk3 : 1 ≤ P.k ^ 3 := Nat.one_le_pow _ _ hk
  have h12 : 12 ≤ P.t * P.f * P.k ^ 3 * P.m := by
    calc 12 = 6 * 2 * 1 * 1 := by norm_num
      _ ≤ P.t * P.f * P.k ^ 3 * P.m :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ht6 hf) hk3) hm
  refine ⟨ht6, h12, ?_⟩
  intro η' h0 h3
  have hb : 0 < P.b := LogSmallConstantBounds.b_pos' P
  have htR : (0 : ℝ) < (P.t : ℝ) := by exact_mod_cast (by omega : 0 < P.t)
  have hfR : (0 : ℝ) < (P.f : ℝ) := by exact_mod_cast (by omega : 0 < P.f)
  have hkR : (0 : ℝ) < (P.k : ℝ) := by exact_mod_cast (by omega : 0 < P.k)
  have hNr : (P.Nr : ℝ) ≤ 2 * (P.t : ℝ) := by exact_mod_cast (by omega : P.Nr ≤ 2 * P.t)
  have hNr0 : (0 : ℝ) ≤ (P.Nr : ℝ) := Nat.cast_nonneg _
  have hD : 0 < (P.t : ℝ) * (P.f : ℝ) * (P.k : ℝ) ^ 3 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_right _ hL
    have hsq : (P.Nr : ℝ) ^ 2 ≤ 4 * (P.t : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul h3 hsq (by positivity) (by linarith)
  · have hη := H.η_le
    have e : 12 * P.L * P.b / ((P.t : ℝ) * (P.f : ℝ) * (P.k : ℝ) ^ 3) =
        3 * (P.b / ((P.t : ℝ) ^ 3 * (P.f : ℝ) * (P.k : ℝ) ^ 3)) * (4 * (P.t : ℝ) ^ 2) * P.L := by
      field_simp
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hL
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  · rw [div_le_iff₀ hD]
    have h12R : (12 : ℝ) ≤ (P.t : ℝ) * (P.f : ℝ) * (P.k : ℝ) ^ 3 * (P.m : ℝ) := by
      exact_mod_cast h12
    have hLb : 0 ≤ P.L * P.b := mul_nonneg hL hb.le
    nlinarith [mul_le_mul_of_nonneg_left h12R hLb]

def exampleParamsAlt : LogSmallConstantBounds.Par :=
  {k := 1, m := 1, t := 6, f := 1, n := 1, Nr := 7, L := 60, x := 4, b' := 40000000, η := 6, S := 4}

theorem two_pow_sixty_le_example_b : (2 : ℝ) ^ 60 ≤ exampleParamsAlt.b := by
  show (2 : ℝ) ^ 60 ≤ Real.exp 60
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc (2 : ℝ) ^ 60 ≤ (Real.exp 1) ^ 60 := by gcongr
    _ = Real.exp 60 := by rw [← Real.exp_nat_mul]; norm_num

theorem example_lstar_eq_b_div : exampleParamsAlt.lstar = exampleParamsAlt.b / 1814470 := by
  simp only [LogSmallConstantBounds.Par.lstar, LogSmallConstantBounds.Par.N, exampleParamsAlt]; norm_num

theorem example_b_div_lstar_eq : exampleParamsAlt.b / exampleParamsAlt.lstar = 1814470 := by
  have := two_pow_sixty_le_example_b
  have hp : 0 < exampleParamsAlt.b := by linarith [show (0 : ℝ) < 2 ^ 60 by norm_num]
  rw [example_lstar_eq_b_div]; field_simp

theorem example_params_satisfy_hyp : exampleParamsAlt.Hyp := by
  have hb := two_pow_sixty_le_example_b
  have e := example_b_div_lstar_eq
  have e8 : 8 * exampleParamsAlt.b / exampleParamsAlt.lstar = 8 * 1814470 := by rw [mul_div_assoc, e]
  have hl : (2 : ℝ) ^ 60 / 1814470 ≤ exampleParamsAlt.lstar := by rw [example_lstar_eq_b_div]; gcongr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (simp [exampleParamsAlt]; done)
  · show (6 : ℝ) ≤ exampleParamsAlt.b / _
    simp only [exampleParamsAlt] at *
    rw [le_div_iff₀ (by norm_num)]; norm_num at hb ⊢; linarith
  · rw [e]; simp only [exampleParamsAlt] at *; norm_num at hl ⊢; linarith
  · rw [e8]; simp only [exampleParamsAlt] at *; norm_num at hl ⊢; linarith

theorem example_params_large : exampleParamsAlt.Large := by
  have hb := two_pow_sixty_le_example_b
  have e := example_b_div_lstar_eq
  have e2 : 2 * exampleParamsAlt.b / exampleParamsAlt.lstar = 2 * 1814470 := by rw [mul_div_assoc, e]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [exampleParamsAlt]
  · norm_num [exampleParamsAlt] at hb ⊢; linarith
  · norm_num [exampleParamsAlt] at hb ⊢; linarith
  · rw [e2]; norm_num [exampleParamsAlt, LogSmallConstantBounds.Par.w'']
  · norm_num [exampleParamsAlt]

theorem tail_line_needs_f_holds : ParameterQuotientBoundFailsAtFEqOne := by
  refine ⟨exampleParamsAlt, example_params_satisfy_hyp, example_params_large, rfl, by norm_num [exampleParamsAlt], ?_⟩
  have hp : 0 < exampleParamsAlt.b := LogSmallConstantBounds.b_pos' _
  show ((1 : ℕ) : ℝ) * exampleParamsAlt.b * 60 < 12 * 60 * exampleParamsAlt.b / (((6 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) ^ 3)
  rw [lt_div_iff₀ (by norm_num)]
  push_cast
  linarith

theorem term_c_small_holds : TermCSmall := by
  intro P H G hf ι D hA τ hτ l hl hlt
  have hL : 0 ≤ P.L := by have := G.L_ge; linarith
  have lp : (0 : ℝ) < l := by have := LogSmallConstantBounds.two_le_prime_cast hl; linarith
  have a1 := LogSmallConstantBounds.ex_mul_log_le_of_thickA H G hA hτ hl
  have te := H.t_le
  obtain ⟨c1, c2, c3⟩ := (tail_line_c_holds P H hf hL).2.2 (l : ℝ) lp.le (by linarith)
  rw [le_div_iff₀ lp]
  calc (D.ex τ l : ℝ) * Real.log (l : ℝ) * (l : ℝ) ≤ ((P.Nr : ℝ) ^ 2 * P.L) * (l : ℝ) := by gcongr
    _ = (l : ℝ) * (P.Nr : ℝ) ^ 2 * P.L := by ring
    _ ≤ _ := le_trans c1 (le_trans c2 c3)

end Formalism.CohomologicalDescent.WorkedExample
