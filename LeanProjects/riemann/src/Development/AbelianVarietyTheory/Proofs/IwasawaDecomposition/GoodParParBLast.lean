import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParDualPar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodParameterFirstSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainModels

open Finset GlobalTheory.SignedHC GlobalTheory.ContragredientPar

theorem goodPar_image {ι : Type} [Fintype ι] {n p q : ℕ} (f : ι → ℚ × Bool) (hf : Function.Injective fun a => (f a).1)
    (hn : Fintype.card ι = n) (hc : ∀ a, ∃ z : ℤ, (f a).1 = ((n : ℚ) - 1) / 2 + z)
    (hq : (univ.filter fun a => (f a).2 = false).card = q) (hpq : p + q = n) : GoodPar n p q (univ.image f) := by
  have hinj : Function.Injective f := fun a c h => hf (congrArg Prod.fst h)
  have hcard : (univ.image f).card = n := by rw [card_image_of_injective _ hinj, card_univ, hn]
  have hminus : SignedHC.nMinus (univ.image f) = q := by
    rw [SignedHC.nMinus, filter_image, card_image_of_injective _ hinj, hq]
  have hsum := nPlus_add_nMinus (univ.image f)
  refine goodPar_iff.2 ⟨⟨?_, hcard, ?_⟩, ?_⟩
  · intro x hx y hy e
    obtain ⟨a, -, rfl⟩ := mem_image.1 hx
    obtain ⟨c, -, rfl⟩ := mem_image.1 hy
    rw [hf e]
  · intro x hx
    obtain ⟨s, hs⟩ := mem_entries.1 hx
    obtain ⟨a, -, e⟩ := mem_image.1 hs
    have e1 : (f a).1 = x := congrArg Prod.fst e
    rw [← e1]
    exact hc a
  · simp only [signature, Prod.mk.injEq]
    omega

variable {R : Ranks} (P : HCParam R)

theorem b_le_e {a c : Fin R.m} (h : a ≤ c) : P.b a + ((R.t : ℚ) + 3) / 2 ≤ P.e c := by
  have h1 := P.gap_be c
  have h2 := (b_strictMono P).monotone h
  linarith

theorem e_le_b {a c : Fin R.m} (h : c < a) : P.e c + ((R.t : ℚ) + 3) / 2 ≤ P.b a := by
  have hc : c.1 + 1 < R.m := lt_of_le_of_lt (Nat.succ_le_of_lt h) a.2
  have h1 := P.gap_eb c hc
  have h2 : P.b ⟨c.1 + 1, hc⟩ ≤ P.b a := (b_strictMono P).monotone (show c.1 + 1 ≤ a.1 from h)
  linarith

def entAt (j : ℕ) (hj : j ≤ R.m) (s : ℚ) : Fin (R.k - 1) ⊕ Fin R.m ⊕ Fin j × Fin R.t → ℚ × Bool
  | .inl i => (P.v i + s, true)
  | .inr (.inl i) => (-P.b i + s, decide (i.1 ≤ j ∨ Even (i.1 - j)))
  | .inr (.inr x) => (-P.e (Fin.castLE hj x.1) + ((R.t : ℚ) - 1) / 2 - (x.2 : ℕ) + s, true)

theorem entAt_inj (j : ℕ) (hj : j ≤ R.m) (s : ℚ) : Function.Injective fun a => (entAt P j hj s a).1 := by
  have hb : ∀ a : Fin R.t, (0 : ℚ) ≤ (a : ℕ) ∧ ((a : ℕ) : ℚ) + 1 ≤ R.t := fun a =>
    ⟨Nat.cast_nonneg _, by exact_mod_cast a.2⟩
  have hvb : ∀ i (c : Fin R.m) (a : Fin R.t), P.v i ≠ -P.e c + ((R.t : ℚ) - 1) / 2 - (a : ℕ) := fun i c a h => by
    have := neg_v_lt_b P i c
    have := b_le_e P (le_refl c)
    have := hb a
    linarith [this.1]
  have hbb : ∀ (i c : Fin R.m) (a : Fin R.t), -P.b i ≠ -P.e c + ((R.t : ℚ) - 1) / 2 - (a : ℕ) := fun i c a h => by
    have := hb a
    rcases le_or_gt i c with h' | h'
    · linarith [b_le_e P h', this.1]
    · linarith [e_le_b P h', this.2]
  have hee : ∀ (c c' : Fin R.m) (a a' : Fin R.t), c < c' →
      -P.e c + ((R.t : ℚ) - 1) / 2 - (a : ℕ) ≠ -P.e c' + ((R.t : ℚ) - 1) / 2 - (a' : ℕ) := fun c c' a a' h' h => by
    linarith [e_le_b P h', b_le_e P (le_refl c'), (hb a).2, (hb a').1]
  rintro (a | a | ⟨a, x⟩) (c | c | ⟨c, y⟩) h <;> simp only [entAt, add_left_inj] at h
  · rw [(v_strictAnti P).injective h]
  · exact absurd (by linarith) (neg_v_lt_b P a c).ne
  · exact absurd h (hvb _ _ _)
  · exact absurd (by linarith) (neg_v_lt_b P c a).ne
  · rw [(b_strictMono P).injective (neg_injective h)]
  · exact absurd h (hbb _ _ _)
  · exact absurd h.symm (hvb _ _ _)
  · exact absurd h.symm (hbb _ _ _)
  · rcases lt_trichotomy a c with h' | rfl | h'
    · exact absurd h (hee _ _ _ _ h')
    · have : ((x : ℕ) : ℚ) = (y : ℕ) := by linarith
      rw [Fin.ext (Nat.cast_injective this : (x : ℕ) = y)]
    · exact absurd h.symm (hee _ _ _ _ h')

theorem card_minus (j m : ℕ) : ((range m).filter fun i => ¬ (i ≤ j ∨ Even (i - j))).card = (m - j) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [ih]
      rw [Nat.even_iff] at h
      omega
    · rw [card_insert_of_notMem (by simp), ih]
      rw [Nat.even_iff] at h
      omega

theorem card_entAt_false (j : ℕ) (hj : j ≤ R.m) (s : ℚ) :
    (univ.filter fun a => (entAt P j hj s a).2 = false).card = (R.m - j) / 2 := by
  rw [← card_minus j R.m]
  symm
  refine card_bij (fun i hi => .inr (.inl ⟨i, mem_range.1 (mem_filter.1 hi).1⟩)) ?_ ?_ ?_
  · intro i hi
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    simpa [entAt] using (mem_filter.1 hi).2
  · intro a _ c _ h
    simpa using h
  · rintro (a | a | a) hx
    · simp [entAt] at hx
    · exact ⟨a.1, mem_filter.2 ⟨mem_range.2 a.2, by simpa [entAt] using hx⟩, rfl⟩
    · simp [entAt] at hx

theorem goodPar_entAt (j : ℕ) (hj : j ≤ R.m) :
    GoodPar (R.rankY j) (sigYD R j).1 (sigYD R j).2 (univ.image (entAt P j hj (if Odd j then -(1 / 2) else 0))) := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  obtain ⟨k', hk'⟩ := R.k_even
  obtain ⟨m', hm'⟩ := R.m_even
  obtain ⟨t', ht'⟩ := R.t_odd
  refine goodPar_image _ (entAt_inj P j hj _) ?_ ?_ (card_entAt_false P j hj _) ?_
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Ranks.rankY, Ranks.r]
    omega
  · have hs : ∃ w : ℤ, (if Odd j then -(1 / 2) else 0 : ℚ) = ((R.rankY j : ℚ) - 1) / 2 + w := by
      have hr : R.r = 2 * (k' + m' - 1) + 1 := by unfold Ranks.r; omega
      unfold Ranks.rankY
      rw [hr, ht']
      generalize k' + m' - 1 = n
      rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
      · rw [if_neg (by simp)]
        exact ⟨-(n + i * (2 * t' + 1)), by push_cast; ring⟩
      · rw [if_pos (by simp)]
        exact ⟨-(n + i * (2 * t' + 1) + t' + 1), by push_cast; ring⟩
    obtain ⟨w, hw⟩ := hs
    rw [hw]
    rintro (a | a | ⟨a, x⟩)
    · obtain ⟨z, hz⟩ := P.v_int a
      exact ⟨z + w, by simp only [entAt, hz]; push_cast; ring⟩
    · obtain ⟨z, hz⟩ := P.b_int a
      exact ⟨-z + w, by simp only [entAt, hz]; push_cast; ring⟩
    · obtain ⟨z, hz⟩ := P.e_int (Fin.castLE hj a)
      refine ⟨-z + t' - (x : ℕ) + w, ?_⟩
      have ht : (R.t : ℚ) = 2 * t' + 1 := by exact_mod_cast ht'
      simp only [entAt, hz, ht]; push_cast; ring
  · simp only [sigYD, Ranks.rankY, Ranks.r]
    omega

theorem Dpar_eq (D : D7) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) :
    (Ptw D).Dpar j τ = univ.image (entAt (D.hc τ) j hj (if Odd j then -(1 / 2) else 0)) := by
  ext x
  simp only [TPar.Dpar, TPar.block, mem_image, mem_union, mem_biUnion, mem_filter, mem_univ, true_and, mem_range,
    Sum.exists, Prod.exists, entAt]
  constructor
  · rintro ⟨_, _, (⟨i, e⟩ | ⟨i, e⟩) | ⟨i, hi, _, ⟨a, ha, rfl⟩, e⟩, rfl⟩ <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr ⟨⟨i.1, hi⟩, ⟨a, ha⟩, rfl⟩)
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, a, rfl⟩)
    · exact ⟨_, _, Or.inl (Or.inl ⟨i, rfl⟩), rfl⟩
    · exact ⟨_, _, Or.inl (Or.inr ⟨i, rfl⟩), rfl⟩
    · exact ⟨_, _, Or.inr ⟨Fin.castLE hj i, i.2, _, ⟨a.1, a.2, rfl⟩, rfl⟩, rfl⟩

theorem goodPar_parB (D : D7) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) :
    GoodPar (D.sp.Y j).rank ((D.sp.Y j).sig (tauE D τ)).1 ((D.sp.Y j).sig (tauE D τ)).2 (parB (Ptw D) j τ) := by
  rw [D.sp.Y_rank j hj, D.Y_sigval j hj, parB, Dpar_eq D j hj]
  exact GlobalTheory.RealGeo.FrameModels.goodPar_dualPar (goodPar_entAt (D.hc τ) j hj)

theorem goodPar_parB_last (D : D7) (τ : D.what₂.Tau) :
    GoodPar D.sp.X'.rank (D.sp.X'.sig (tauE D τ)).1 (D.sp.X'.sig (tauE D τ)).2 (parB (Ptw D) D.R.m τ) := by
  have h := goodPar_parB D D.R.m le_rfl τ
  rw [D.sp.Y_rank _ le_rfl] at h
  rw [GlobalTheory.ChiGrid.sig_X'_eq_sig_Y, D.sp.X'_rank]
  exact h

theorem nonempty_modelY (h : GlobalTheory.Published.DiscreteSeriesExists) (D : D7) (j : ℕ) :
    Nonempty (DSModel (Yc D j) (parB (Ptw D) (min j D.R.m))) :=
  GlobalTheory.Published.dsExists_of_discreteSeriesExists h D _ _ (D.sp.Y_sig _) (goodPar_parB D _ (min_le_right _ _))

theorem nonempty_modelX (h : GlobalTheory.Published.DiscreteSeriesExists) (D : D7) :
    Nonempty (DSModel D.sp.X' (parB (Ptw D) D.R.m)) :=
  GlobalTheory.Published.dsExists_of_discreteSeriesExists h D _ _ D.sp.X'_sig (goodPar_parB_last D)

theorem labE_embLL (D : D7) (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem labE_lab_embLL (D : D7) (ρ : D.what₂.Tau) : labE D.what₂.embLL (lab D.what₂.embLL ρ) = tauE D ρ := by
  have h : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (labE_embLL D ρ)⟩
  unfold lab
  rw [dif_pos h]
  have hs := h.choose_spec
  generalize h.choose = τ at hs
  rcases hs with hs | hs
  · exact hs
  · exfalso
    rw [labE_embLL] at hs
    have a := xi_zero_im_pos D τ
    have b := xi_zero_im_pos D ρ
    rw [hs] at a
    simp at a
    linarith

theorem exists_models : GlobalTheory.Published.DiscreteSeriesExists → ∀ D : D7,
    ((∀ j, Nonempty (DSModel (Yc D j) (parB (Ptw D) (min j D.R.m)))) ∧ Nonempty (DSModel D.sp.X' (parB (Ptw D) D.R.m))) ∧
    ∀ (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL], (∀ x : D.host.E, ∃ y : Ks, algebraMap Ks D.what₂.LL y = D.embE x) →
      ∃ MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ),
        (∀ i τ a, (MW i D.what₂.embLL).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) ∧
          GlobalTheory.RealGeo.FrameKs Ks MW := by
  intro h D
  refine ⟨⟨nonempty_modelY h D, nonempty_modelX h D⟩, fun Ks _ _ hK => ?_⟩
  obtain ⟨MW, hMW⟩ := GlobalTheory.RealGeo.FrameModels.exists_frameKs h D Ks hK
  exact ⟨MW, fun i => hMW.2 i _ (labE_lab_embLL D), hMW⟩

theorem order_embLL (D : D7) (i : Fin D.R.m) (M : DSModel (Wc D i) (parAt (Wc D i) D.what₂.embLL)) (τ : D.what₂.Tau)
    (a : Fin (Wc D i).rank) : M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1) := by
  have he := M.enum τ
  have e : parAt (Wc D i) D.what₂.embLL τ = Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) D.what₂.embLL τ) :=
    if_pos (labE_lab_embLL D τ)
  rw [e] at he
  exact (GlobalTheory.HolDict.isEnum_holPar_kapW _ (Formalism.IndefR.FWT.rank_Wc i) (GlobalTheory.RealGeo.FrameModels.sig_add i τ) he a).2

end GlobalTheory.ChainModels
