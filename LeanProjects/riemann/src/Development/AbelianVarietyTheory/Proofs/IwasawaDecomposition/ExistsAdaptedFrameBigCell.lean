import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagMatLower
open Module TopologicalSpace GlobalTheory.FlagPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPts.SphericalEisensteinCover

variable {k W : Type} [Field k] [AddCommGroup W] [Module k W]

theorem two_avoid (S H₁ H₂ : Submodule k W) (h₁ : ¬ S ≤ H₁) (h₂ : ¬ S ≤ H₂) :
    ∃ v ∈ S, v ∉ H₁ ∧ v ∉ H₂ := by
  obtain ⟨x, hxS, hx1⟩ := SetLike.not_le_iff_exists.1 h₁
  obtain ⟨y, hyS, hy2⟩ := SetLike.not_le_iff_exists.1 h₂
  by_cases hx2 : x ∈ H₂
  · by_cases hy1 : y ∈ H₁
    · refine ⟨x + y, S.add_mem hxS hyS, fun h => hx1 ?_, fun h => hy2 ?_⟩
      · simpa using H₁.sub_mem h hy1
      · simpa using H₂.sub_mem h hx2
    · exact ⟨y, hyS, hy1, hy2⟩
  · exact ⟨x, hxS, hx1, hx2⟩

theorem disj_sup (P G : Submodule k W) (v : W) (hPG : Disjoint P G) (hv : v ∉ P ⊔ G) :
    Disjoint P (G ⊔ k ∙ v) := by
  rw [Submodule.disjoint_def]
  intro x hxP hx
  obtain ⟨g, hg, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul, add_zero] at hxP ⊢
    exact Submodule.disjoint_def.1 hPG _ hxP hg
  · exfalso
    apply hv
    have h1 : g + c • v ∈ P ⊔ G := Submodule.mem_sup_left hxP
    have h2 : g ∈ P ⊔ G := Submodule.mem_sup_right hg
    have h3 : v = c⁻¹ • ((g + c • v) - g) := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h1 h2)

theorem finrank_sup_span [FiniteDimensional k W] (G : Submodule k W) (v : W) (hv : v ∉ G) :
    finrank k (G ⊔ k ∙ v : Submodule k W) = finrank k G + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ G.zero_mem)
  have h := Submodule.finrank_sup_add_finrank_inf_eq G (k ∙ v)
  rw [((Submodule.disjoint_span_singleton' hv0).2 hv).eq_bot, finrank_bot, add_zero,
    finrank_span_singleton hv0] at h
  exact h

theorem not_le_of_finrank [FiniteDimensional k W] (B H G : Submodule k W) (hGB : ¬ G ≤ B) (hGH : G ≤ H)
    (hd : finrank k H ≤ finrank k B) : ¬ B ≤ H := fun hBH => hGB
  (hGH.trans (Submodule.eq_of_le_of_finrank_le hBH hd).symm.le)

variable (k) in

def spanFrom (f : ℕ → W) (N m : ℕ) : Submodule k W := Submodule.span k (f '' {a | m ≤ a ∧ a < N})

theorem spanFrom_update_of_lt (f : ℕ → W) (N m m' : ℕ) (v : W) (h : m < m') :
    spanFrom k (Function.update f m v) N m' = spanFrom k f N m' := by
  unfold spanFrom
  congr 1
  refine Set.image_congr fun a ha => ?_
  rw [Function.update_of_ne]
  exact (lt_of_lt_of_le h ha.1).ne'

theorem spanFrom_update_self (f : ℕ → W) (N m : ℕ) (v : W) (h : m < N) :
    spanFrom k (Function.update f m v) N m = spanFrom k f N (m + 1) ⊔ k ∙ v := by
  rw [← spanFrom_update_of_lt (k := k) f N m (m + 1) v (Nat.lt_succ_self m)]
  unfold spanFrom
  have : {a | m ≤ a ∧ a < N} = insert m {a | m + 1 ≤ a ∧ a < N} := by
    ext a; simp only [Set.mem_setOf_eq, Set.mem_insert_iff]; omega
  rw [this, Set.image_insert_eq, Submodule.span_insert, Function.update_self, sup_comm]

theorem spanFrom_ge (f : ℕ → W) (N m : ℕ) (h : N ≤ m) : spanFrom k f N m = ⊥ := by
  unfold spanFrom
  have : {a | m ≤ a ∧ a < N} = ∅ := by ext a; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]; omega
  rw [this, Set.image_empty, Submodule.span_empty]

end GlobalTheory.FlagPts.SphericalEisensteinCover

namespace GlobalTheory.FlagPts.SphericalEisensteinCover

variable {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]

theorem mem_spanFrom_update (f : ℕ → W) (N m : ℕ) (v : W) (h : m < N) :
    v ∈ spanFrom k (Function.update f m v) N m := by
  rw [spanFrom_update_self f N m v h]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)

theorem image_fin (f : ℕ → W) (N m : ℕ) :
    (fun i : Fin N => f i) '' {a : Fin N | m ≤ (a : ℕ)} = f '' {a | m ≤ a ∧ a < N} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ⟨ha, a.2⟩, rfl⟩
  · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨a, h2⟩, h1, rfl⟩

def Inv (Fs : ℕ → Submodule k W) (A : Submodule k W) (f : ℕ → W) (m : ℕ) : Prop :=
  ∀ m', m ≤ m' → Disjoint (Fs m') (spanFrom k f (finrank k W) m') ∧
    Disjoint A (spanFrom k f (finrank k W) m') ∧
    finrank k (spanFrom k f (finrank k W) m') = finrank k W - m'

theorem step_core (Fs : ℕ → Submodule k W) (hmono : ∀ m, Fs m ≤ Fs (m + 1)) (A : Submodule k W)
    (f : ℕ → W) (m : ℕ) (hmN : m < finrank k W) (v : W)
    (hv1 : v ∉ Fs m ⊔ spanFrom k f (finrank k W) (m + 1))
    (hv2 : v ∉ A ⊔ spanFrom k f (finrank k W) (m + 1)) (hinv : Inv Fs A f (m + 1)) :
    Inv Fs A (Function.update f m v) m := by
  intro m' hm'
  rcases hm'.eq_or_lt with rfl | hlt
  · rw [spanFrom_update_self f _ _ v hmN]
    obtain ⟨h1, h2, h3⟩ := hinv (_ + 1) le_rfl
    refine ⟨disj_sup _ _ _ (Disjoint.mono_left (hmono _) h1) hv1, disj_sup _ _ _ h2 hv2, ?_⟩
    rw [finrank_sup_span _ _ (fun h => hv2 (Submodule.mem_sup_right h)), h3]
    omega
  · rw [spanFrom_update_of_lt f _ _ _ v hlt]
    exact hinv m' hlt

theorem exists_basis (Fs : ℕ → Submodule k W) (hmono : ∀ m, Fs m ≤ Fs (m + 1))
    (hdim : ∀ m, finrank k (Fs m) = min m (finrank k W)) (A B : Submodule k W) (hN : 2 ≤ finrank k W)
    (hAB : A ≤ B) (hA : finrank k A = 1) (hB : finrank k B + 1 = finrank k W) :
    ∃ b : Basis (Fin (finrank k W)) k W, (∀ a : Fin (finrank k W), (a : ℕ) = 0 → b a ∈ A) ∧
      (∀ a : Fin (finrank k W), (a : ℕ) + 1 < finrank k W → b a ∈ B) ∧
      ∀ m, Disjoint (Fs m) (Submodule.span k (b '' {a : Fin (finrank k W) | m ≤ (a : ℕ)})) := by
  set N := finrank k W with hNdef
  let Q : ℕ → Prop := fun m => ∃ f : ℕ → W, ¬ spanFrom k f N m ≤ B ∧
    (∀ a, m ≤ a → a + 1 < N → f a ∈ B) ∧ Inv Fs A f m
  have base : Q (N - 1) := by
    have hF : ¬ (⊤ : Submodule k W) ≤ Fs (N - 1) := fun h => by
      have := Submodule.finrank_mono h
      rw [finrank_top, hdim] at this
      omega
    have hBt : ¬ (⊤ : Submodule k W) ≤ B := fun h => by
      have := Submodule.finrank_mono h
      rw [finrank_top] at this
      omega
    obtain ⟨v, -, hv1, hvB⟩ := two_avoid ⊤ _ _ hF hBt
    let f0 : ℕ → W := fun _ => 0
    have hG : spanFrom k f0 N (N - 1 + 1) = ⊥ := spanFrom_ge f0 N _ (by omega)
    refine ⟨Function.update f0 (N - 1) v, fun h => hvB (h (mem_spanFrom_update f0 N _ v (by omega))),
      fun a h1 h2 => by omega, step_core Fs hmono A f0 (N - 1) (by omega) v ?_ ?_ ?_⟩
    · rw [hG, sup_bot_eq]; exact hv1
    · rw [hG, sup_bot_eq]; exact fun h => hvB (hAB h)
    · intro m' hm'
      rw [spanFrom_ge f0 N m' (by omega)]
      refine ⟨disjoint_bot_right, disjoint_bot_right, ?_⟩
      rw [finrank_bot]
      omega
  have step : ∀ m, 1 ≤ m → m + 1 < N → Q (m + 1) → Q m := by
    rintro m hm1 hmN ⟨f, hfB, hmem, hinv⟩
    set G := spanFrom k f N (m + 1) with hGdef
    obtain ⟨-, -, hGd⟩ := hinv (m + 1) le_rfl
    have h1 : ¬ B ≤ Fs m ⊔ G := by
      refine not_le_of_finrank B _ G hfB le_sup_right ?_
      have := Submodule.finrank_add_le_finrank_add_finrank (Fs m) G
      rw [hdim, hGd] at this
      have : min m N = m := min_eq_left (by omega)
      omega
    have h2 : ¬ B ≤ A ⊔ G := by
      refine not_le_of_finrank B _ G hfB le_sup_right ?_
      have := Submodule.finrank_add_le_finrank_add_finrank A G
      rw [hA, hGd] at this
      omega
    obtain ⟨v, hvB, hv1, hv2⟩ := two_avoid B _ _ h1 h2
    refine ⟨Function.update f m v, fun h => hfB ?_, fun a ha1 ha2 => ?_,
      step_core Fs hmono A f m (by omega) v hv1 hv2 hinv⟩
    · rw [spanFrom_update_self f N m v (by omega)] at h
      exact le_sup_left.trans h
    · rcases ha1.eq_or_lt with rfl | hlt
      · rw [Function.update_self]; exact hvB
      · rw [Function.update_of_ne hlt.ne']; exact hmem a hlt ha2
  have all : ∀ t, t + 2 ≤ N → Q (N - 1 - t) := by
    intro t
    induction t with
    | zero => intro _; simpa using base
    | succ t ih =>
      intro ht
      have := step (N - 1 - (t + 1)) (by omega) (by omega)
      rw [show N - 1 - (t + 1) + 1 = N - 1 - t by omega] at this
      exact this (ih (by omega))
  obtain ⟨f, -, hmem, hinv⟩ : Q 1 := by
    have := all (N - 2) (by omega)
    rwa [show N - 1 - (N - 2) = 1 by omega] at this
  have hAne : A ≠ ⊥ := fun h => by rw [h, finrank_bot] at hA; omega
  obtain ⟨a, haA, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hAne
  obtain ⟨-, hA1, hd1⟩ := hinv 1 le_rfl
  have haG : a ∉ spanFrom k f N 1 := fun h => ha0 (Submodule.disjoint_def.1 hA1 a haA h)
  have hF0 : Fs 0 = ⊥ := Submodule.finrank_eq_zero.1 (by rw [hdim]; simp)
  set f' := Function.update f 0 a with hf'
  have htop : spanFrom k f' N 0 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hf', spanFrom_update_self f N 0 a (by omega), finrank_sup_span _ _ haG]
    change finrank k (spanFrom k f (finrank k W) 1) + 1 = _
    omega
  have hdisj : ∀ m, Disjoint (Fs m) (spanFrom k f' N m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [hF0]; exact disjoint_bot_left
    · rw [hf', spanFrom_update_of_lt f N 0 m a hm]
      exact (hinv m hm).1
  have hspan : ⊤ ≤ Submodule.span k (Set.range (fun i : Fin N => f' i)) := by
    rw [← Set.image_univ, show (Set.univ : Set (Fin N)) = {a : Fin N | 0 ≤ (a : ℕ)} by ext; simp, image_fin]
    exact htop.ge
  refine ⟨basisOfTopLeSpanOfCardEqFinrank (fun i : Fin N => f' i) hspan (Fintype.card_fin _), fun i hi => ?_,
    fun i hi => ?_, fun m => ?_⟩
  · rw [coe_basisOfTopLeSpanOfCardEqFinrank]
    simp only [hi, hf', Function.update_self]
    exact haA
  · rw [coe_basisOfTopLeSpanOfCardEqFinrank]
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · simp only [h0, hf', Function.update_self]
      exact hAB haA
    · simp only [hf']
      rw [Function.update_of_ne hpos.ne']
      exact hmem i hpos hi
  · rw [coe_basisOfTopLeSpanOfCardEqFinrank, image_fin]
    exact hdisj m

end GlobalTheory.FlagPts.SphericalEisensteinCover

namespace GlobalTheory.FlagPts

end GlobalTheory.FlagPts
