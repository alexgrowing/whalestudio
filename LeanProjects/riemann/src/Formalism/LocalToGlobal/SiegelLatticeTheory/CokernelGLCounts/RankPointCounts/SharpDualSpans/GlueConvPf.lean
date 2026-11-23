import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueConvA

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Matrix

namespace PI.LocCntLat.GC

open PI.LocCntLat.GE

section Quot

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem ddMk_add (H : HermSp M V) {r : ℕ} (t : Term V M r) (a b : ↥(MMsharp H t)) :
    ddMk H t (a + b) = ddMk H t a + ddMk H t b := Submodule.Quotient.mk_add _
theorem ddMk_smul (H : HermSp M V) {r : ℕ} (t : Term V M r) (c : M.L.O) (a : ↥(MMsharp H t)) :
    ddMk H t (c • a) = c • ddMk H t a := Submodule.Quotient.mk_smul _ _ _
theorem ddMk_zero (H : HermSp M V) {r : ℕ} (t : Term V M r) : ddMk H t 0 = 0 := Submodule.Quotient.mk_zero _
theorem dwMk_add (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) (a b : ↥(ThSharp H t N)) :
    dwMk H t N (a + b) = dwMk H t N a + dwMk H t N b := Submodule.Quotient.mk_add _
theorem dwMk_smul (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) (c : M.L.O)
    (a : ↥(ThSharp H t N)) : dwMk H t N (c • a) = c • dwMk H t N a := Submodule.Quotient.mk_smul _ _ _
theorem dwMk_zero (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) :
    dwMk H t N 0 = 0 := Submodule.Quotient.mk_zero _

theorem ddMk_eq_zero (H : HermSp M V) {r : ℕ} (t : Term V M r) (a : ↥(MMsharp H t)) :
    ddMk H t a = 0 ↔ (a : V) ∈ MMo H t := by
  unfold ddMk
  exact Submodule.Quotient.mk_eq_zero _

theorem dwMk_eq_zero (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) (a : ↥(ThSharp H t N)) :
    dwMk H t N a = 0 ↔ (a : V) ∈ N := by
  unfold dwMk
  exact Submodule.Quotient.mk_eq_zero _

theorem exists_rep (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) (d : DDW H t N) :
    ∃ w : ↥(ThSharp H t N), dwMk H t N w = d := Submodule.Quotient.mk_surjective _ d

theorem exists_rep' (H : HermSp M V) {r : ℕ} (t : Term V M r) (d : DDt H t) :
    ∃ m : ↥(MMsharp H t), ddMk H t m = d := Submodule.Quotient.mk_surjective _ d

end Quot

section Conv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem glueConv_holds (M : Model F E) (r : ℕ) : GlueConv M r := by
  intro hOK V _ _ H t hG hMI N hNW hNfg hNspan hNint η hη
  set U := Submodule.span E (Set.range (H.MMfam t)) with hUdef
  have hU : IsCompl U (H.perp U) := isCompl_span_perp H (H.MMfam t) hG
  have hW : H.W0 t.f t.f' = H.perp U := hermSp_W0_eq_perp_span_range_MMfam H t
  have hdis : ∀ x, x ∈ U → x ∈ H.W0 t.f t.f' → x = 0 := by
    intro x h1 h2; rw [hW] at h2; exact (Submodule.disjoint_def.1 hU.disjoint) x h1 h2
  have hdec : ∀ x : V, ∃ m ∈ U, ∃ w ∈ H.W0 t.f t.f', m + w = x := by
    intro x
    have hx : x ∈ U ⊔ H.perp U := by rw [hU.sup_eq_top]; trivial
    rw [← hW] at hx
    exact Submodule.mem_sup.1 hx
  have huniq : ∀ {m m' w w' : V}, m ∈ U → m' ∈ U → w ∈ H.W0 t.f t.f' → w' ∈ H.W0 t.f t.f' →
      m + w = m' + w' → m = m' ∧ w = w' := by
    intro m m' w w' hm hm' hw hw' he
    have e1 : m - m' = w' - w := by rw [sub_eq_sub_iff_add_eq_add, he, add_comm]
    have h0 : m - m' = 0 := hdis _ (Submodule.sub_mem _ hm hm') (by rw [e1]; exact Submodule.sub_mem _ hw' hw)
    have hmm : m = m' := sub_eq_zero.1 h0
    refine ⟨hmm, ?_⟩
    rw [hmm] at he; exact add_left_cancel he
  have hMMs : ∀ m ∈ MMo H t, m ∈ MMsharp H t := fun m hm =>
    ⟨mem_spanE_of_mem_MMo H t hm, fun m' hm' => hMI m hm m' hm'⟩
  have hNs : ∀ n ∈ N, n ∈ ThSharp H t N := fun n hn => ⟨hNW hn, fun n' hn' => hNint n hn n' hn'⟩

  let Λ : Submodule M.L.O V :=
    { carrier := {x | ∃ (m : ↥(MMsharp H t)) (w : ↥(ThSharp H t N)),
        η (ddMk H t m) = dwMk H t N w ∧ (m : V) + w = x}
      add_mem' := by
        rintro _ _ ⟨m, w, h, rfl⟩ ⟨m', w', h', rfl⟩
        refine ⟨m + m', w + w', ?_, ?_⟩
        · rw [ddMk_add, map_add, h, h', dwMk_add]
        · simp only [Submodule.coe_add]; abel
      zero_mem' := ⟨0, 0, by rw [ddMk_zero, map_zero, dwMk_zero], by simp⟩
      smul_mem' := by
        rintro c _ ⟨m, w, h, rfl⟩
        refine ⟨c • m, c • w, ?_, ?_⟩
        · rw [ddMk_smul, map_smul, h, dwMk_smul]
        · simp only [Submodule.coe_smul]; rw [smul_add] }
  have GI : ∀ (m : ↥(MMsharp H t)) (w : ↥(ThSharp H t N)),
      η (ddMk H t m) = dwMk H t N w ↔ (m : V) + w ∈ Λ := by
    intro m w
    constructor
    · intro h; exact ⟨m, w, h, rfl⟩
    · rintro ⟨m₀, w₀, h₀, e⟩
      obtain ⟨e1, e2⟩ := huniq m₀.2.1 m.2.1 w₀.2.1 w.2.1 e
      have : m₀ = m := Subtype.ext e1
      have : w₀ = w := Subtype.ext e2
      subst_vars
      exact h₀
  have hNΛ : N ≤ Λ := by
    intro n hn
    refine ⟨0, ⟨n, hNs n hn⟩, ?_, by simp⟩
    rw [ddMk_zero, map_zero, eq_comm, dwMk_eq_zero]
    exact hn
  have hgΛ : ∀ a, H.MMfam t a ∈ Λ := by
    intro a
    have ha : H.MMfam t a ∈ MMo H t := Submodule.subset_span ⟨a, rfl⟩
    refine ⟨⟨_, hMMs _ ha⟩, 0, ?_, by simp⟩
    rw [dwMk_zero, (ddMk_eq_zero H t _).2 ha, map_zero]
  have hMMΛ : MMo H t ≤ Λ := Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hgΛ a)

  have hInf : Λ ⊓ (H.W0 t.f t.f').restrictScalars M.L.O = N := by
    apply le_antisymm
    · rintro x ⟨⟨m, w, h, rfl⟩, hx⟩
      have hxW : (m : V) + w ∈ H.W0 t.f t.f' := hx
      have hm0 : (m : V) = 0 := hdis _ m.2.1 (by
        have := Submodule.sub_mem _ hxW w.2.1
        rwa [add_sub_cancel_right] at this)
      have hm : m = 0 := Subtype.ext hm0
      subst hm
      rw [ddMk_zero, map_zero, eq_comm, dwMk_eq_zero] at h
      simpa using h
    · intro n hn
      exact ⟨hNΛ hn, hNW hn⟩

  have hPrim : H.Prim Λ (H.MMfam t) := by
    refine ⟨hgΛ, linIndep_of_gram H (H.MMfam t) hG, ?_⟩
    rintro x ⟨m, w, h, rfl⟩ hxU
    have hw0 : (w : V) = 0 := hdis _ (by
      have := Submodule.sub_mem _ hxU m.2.1
      rwa [add_sub_cancel_left] at this) w.2.1
    have hw : w = 0 := Subtype.ext hw0
    subst hw
    rw [dwMk_zero, ← map_zero η, η.injective.eq_iff, ddMk_eq_zero] at h
    simpa [MMo] using h

  have hfwd : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O := by
    rintro _ ⟨m, w, h, rfl⟩ _ ⟨m', w', h', rfl⟩
    have := hη m m' w w' h h'
    rw [h_expand, hermitian_span_orthogonal_W0 H t m.2.1 w'.2.1, hermitian_W0_orthogonal_span H t m'.2.1 w.2.1, add_zero, add_zero]
    exact this
  have hdual : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, H.h x y ∈ M.L.O := by
    intro x
    refine ⟨hfwd x, fun hx => ?_⟩
    obtain ⟨m, hm, w, hw, rfl⟩ := hdec x
    have hms : m ∈ MMsharp H t := ⟨hm, fun m' hm' => by
      have := hx m' (hMMΛ hm')
      rwa [H.h_add_left, hermitian_W0_orthogonal_span H t (mem_spanE_of_mem_MMo H t hm') hw, add_zero] at this⟩
    have hws : w ∈ ThSharp H t N := ⟨hw, fun n hn => by
      have := hx n (hNΛ hn)
      rwa [H.h_add_left, hermitian_span_orthogonal_W0 H t hm (hNW hn), zero_add] at this⟩
    obtain ⟨w₀, hw₀⟩ := exists_rep H t N (η (ddMk H t ⟨m, hms⟩))
    have hin₀ : m + (w₀ : V) ∈ Λ := (GI ⟨m, hms⟩ w₀).1 hw₀.symm
    set v : ↥(ThSharp H t N) := ⟨w, hws⟩ - w₀ with hv
    have hvV : (v : V) = w - w₀ := rfl
    obtain ⟨mv, hmv⟩ := exists_rep' H t (η.symm (dwMk H t N v))
    have hmv' : η (ddMk H t mv) = dwMk H t N v := by rw [hmv, LinearEquiv.apply_symm_apply]
    have hint : ∀ u ∈ MMsharp H t, H.h mv u ∈ M.L.O := by
      intro u hu
      obtain ⟨w', hw'⟩ := exists_rep H t N (η (ddMk H t ⟨u, hu⟩))
      have h1 : H.h mv u + H.h v w' ∈ M.L.O := hη mv ⟨u, hu⟩ v w' hmv' hw'.symm
      have hin : u + (w' : V) ∈ Λ := (GI ⟨u, hu⟩ w').1 hw'.symm
      have h2 := hx _ hin
      rw [h_expand, hermitian_span_orthogonal_W0 H t hm w'.2.1, hermitian_W0_orthogonal_span H t hu.1 hw, add_zero, add_zero] at h2
      have h4 := hfwd _ hin₀ _ hin
      rw [h_expand, hermitian_span_orthogonal_W0 H t hm w'.2.1, hermitian_W0_orthogonal_span H t hu.1 w₀.2.1, add_zero, add_zero] at h4
      have h5 : H.h v w' ∈ M.L.O := by
        have e : H.h (v : V) w' = (H.h m u + H.h w w') - (H.h m u + H.h w₀ w') := by
          rw [hvV, h_sub_left]; ring
        rw [e]; exact M.L.O.sub_mem h2 h4
      have := M.L.O.sub_mem h1 h5
      rwa [add_sub_cancel_right] at this
    have hmvM : (mv : V) ∈ MMo H t := mem_MMo_of_dual H t hG mv.2.1 hint
    have hvN : (v : V) ∈ N := by
      rw [← dwMk_eq_zero, ← hmv', (ddMk_eq_zero H t mv).2 hmvM, map_zero]
    have e : m + w = (m + (w₀ : V)) + (v : V) := by rw [hvV]; abel
    rw [e]
    exact Λ.add_mem hin₀ (hNΛ hvN)

  have hspan : Submodule.span E (Λ : Set V) = ⊤ := by
    apply eq_top_iff.2
    rw [← hU.sup_eq_top, ← hW]
    apply sup_le
    · exact Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact Submodule.subset_span (hgΛ a))
    · rw [← hNspan]; exact Submodule.span_mono (fun x hx => hNΛ hx)

  have hdualfam : ∀ j, ∃ u ∈ U, ∀ i, H.h u (H.MMfam t i) = if i = j then 1 else 0 :=
    fun j => exists_dual H _ hG j
  choose u hu hu' using hdualfam
  have husharp : ∀ j, u j ∈ MMsharp H t := fun j => dual_mem_sharp H t (hu j) j (hu' j)
  have spanU_le : Submodule.span M.L.O (Set.range u) ≤ MMsharp H t :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact husharp j)
  choose wj hwj using fun j => exists_rep H t N (η (ddMk H t ⟨u j, husharp j⟩))
  set S := N ⊔ Submodule.span M.L.O (Set.range fun j => u j + (wj j : V)) with hS
  have key : ∀ y ∈ Submodule.span M.L.O (Set.range u), ∀ (hy : y ∈ MMsharp H t) (w : ↥(ThSharp H t N)),
      η (ddMk H t ⟨y, hy⟩) = dwMk H t N w → y + (w : V) ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨j, rfl⟩ := hy'
      intro hy w hw
      have e0 : (⟨u j, hy⟩ : ↥(MMsharp H t)) = ⟨u j, husharp j⟩ := rfl
      rw [e0, ← hwj j, dwMk_eq_iff] at hw
      have e : u j + (w : V) = (u j + wj j) + ((w : V) - wj j) := by abel
      rw [e]
      refine S.add_mem (Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)) (Submodule.mem_sup_left ?_)
      have := N.neg_mem hw
      rwa [neg_sub] at this
    | zero =>
      intro hy w hw
      have e0 : (⟨0, hy⟩ : ↥(MMsharp H t)) = 0 := rfl
      rw [e0, ddMk_zero, map_zero, eq_comm, dwMk_eq_zero] at hw
      rw [zero_add]; exact Submodule.mem_sup_left hw
    | add a b ha hb iha ihb =>
      intro hy w hw
      have has : a ∈ MMsharp H t := spanU_le ha
      have hbs : b ∈ MMsharp H t := spanU_le hb
      obtain ⟨wa, hwa⟩ := exists_rep H t N (η (ddMk H t ⟨a, has⟩))
      obtain ⟨wb, hwb⟩ := exists_rep H t N (η (ddMk H t ⟨b, hbs⟩))
      have hA := iha has wa hwa.symm
      have hB := ihb hbs wb hwb.symm
      have e0 : (⟨a + b, hy⟩ : ↥(MMsharp H t)) = ⟨a, has⟩ + ⟨b, hbs⟩ := rfl
      rw [e0, ddMk_add, map_add, ← hwa, ← hwb, ← dwMk_add, dwMk_eq_iff] at hw
      have e : a + b + (w : V) = (a + wa) + (b + wb) + ((w : V) - ↑(wa + wb)) := by
        simp only [Submodule.coe_add]; abel
      rw [e]
      refine S.add_mem (S.add_mem hA hB) (Submodule.mem_sup_left ?_)
      have := N.neg_mem hw
      rwa [neg_sub] at this
    | smul c a ha iha =>
      intro hy w hw
      have has : a ∈ MMsharp H t := spanU_le ha
      obtain ⟨wa, hwa⟩ := exists_rep H t N (η (ddMk H t ⟨a, has⟩))
      have hA := iha has wa hwa.symm
      have e0 : (⟨c • a, hy⟩ : ↥(MMsharp H t)) = c • ⟨a, has⟩ := rfl
      rw [e0, ddMk_smul, map_smul, ← hwa, ← dwMk_smul, dwMk_eq_iff] at hw
      have e : c • a + (w : V) = c • (a + wa) + ((w : V) - ↑(c • wa)) := by
        simp only [Submodule.coe_smul, smul_add]; abel
      rw [e]
      refine S.add_mem (S.smul_mem c hA) (Submodule.mem_sup_left ?_)
      have := N.neg_mem hw
      rwa [neg_sub] at this
  have hΛS : Λ = S := by
    apply le_antisymm
    · rintro x ⟨m, w, h, rfl⟩
      exact key m (sharp_le_span_dual H t hG u hu hu' m.2) m.2 w h
    · apply sup_le hNΛ
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (GI ⟨u j, husharp j⟩ (wj j)).1 (hwj j).symm
  have hFG : Λ.FG := by
    rw [hΛS]; exact hNfg.sup (Submodule.fg_span (Set.finite_range _))
  refine ⟨Λ, ⟨⟨hFG, hspan, hdual⟩, hPrim, hInf, GI⟩, ?_⟩
  rintro Λ' ⟨hSD', hPrim', hInf', GI'⟩
  ext x
  constructor
  · intro hx
    obtain ⟨m, hm, w, hw, rfl⟩ := hdec x
    have hmΛ' : MMo H t ≤ Λ' := Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hPrim'.1 a)
    have hNΛ' : N ≤ Λ' := by rw [← hInf']; exact inf_le_left
    have hms : m ∈ MMsharp H t := ⟨hm, fun m' hm' => by
      have := (hSD'.2.2 _).1 hx m' (hmΛ' hm')
      rwa [H.h_add_left, hermitian_W0_orthogonal_span H t (mem_spanE_of_mem_MMo H t hm') hw, add_zero] at this⟩
    have hws : w ∈ ThSharp H t N := ⟨hw, fun n hn => by
      have := (hSD'.2.2 _).1 hx n (hNΛ' hn)
      rwa [H.h_add_left, hermitian_span_orthogonal_W0 H t hm (hNW hn), zero_add] at this⟩
    exact (GI ⟨m, hms⟩ ⟨w, hws⟩).1 ((GI' ⟨m, hms⟩ ⟨w, hws⟩).2 hx)
  · rintro ⟨m, w, h, rfl⟩
    exact (GI' m w).1 h

end Conv

end PI.LocCntLat.GC
