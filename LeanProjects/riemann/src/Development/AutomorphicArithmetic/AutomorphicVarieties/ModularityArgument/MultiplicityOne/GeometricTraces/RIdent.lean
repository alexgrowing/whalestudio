import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfGalStep

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula UpperTheory.V.Z.Mult

theorem UpperTheory.V.Z.Mult.rIdent :
    RIdent := by
  intro hND hCA hGT hG hM1 hM3 hE hS E _ _ _ hunr n hn hn4 lam
  have hF : MatchUnit → MatchSplit → FamMatch := fun h1 h3 => rFamMatch h1 h3 places exAct exHecke2 ctEx muConj
  have hEn := ends
  have hTw := twDataT cdAddG muInf mwAt dualWt
  have hRO := regOf mwAt dualWt
  have hUS := unStable
  have hMI := muInf
  have hCI := csdInert UpperTheory.V.Z.Tf.GOne.csdSat
  have hSep := rSep places
  have hReg := regCt
  have hTr := trAvg
  have hP := places
  obtain ⟨l₀⟩ : Nonempty (InfinitePlace E → DomWeight 0) := ⟨fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  obtain ⟨c₀, hc₀, hst⟩ := hS E hunr n hn lam l₀
  refine ⟨2 * c₀, by positivity, fun π hreg hd hinf μ e hμ S hS' Z hZ B τ f hB hf ⟨w₀, hw₀, hr₀⟩ K' hK hK1 hK2 ι' _ σ hdec => ?_⟩
  obtain ⟨ι, _, BU, hBU, hUv⟩ := hCA E hunr n hn hn4 π hreg hd S hS' lam Z hZ B τ (fun w hw => (hB w hw).1) (fun w hw => (hf w hw).1)
    K' hK hK1 ι' σ hdec
  obtain ⟨hdim, hgt⟩ := hGT E hunr n hn S hS' lam K' hK
  have hFM := hF hM1 hM3 E hunr n μ e hμ S hS' Z hZ (fun w hw => (hB w hw).2) f fun w hw => (hf w hw).2.1
  have hLc := fun a b h => (hFM a b h).1
  choose t ht using fun a b h => (hFM a b h).2
  have hRg : ∀ a b (h : a + b = n), ∃ w ∈ Z, RegAt2 a b w (ct0 μ h f w) := fun a b h =>
    ⟨w₀, hw₀, hReg E w₀ (hZ w₀ hw₀).2 μ n a b h f hr₀⟩
  obtain ⟨κ, _, a, l₁, l₂, sg, hw, ⟨i₁, ha₁, hs₁, hu₁⟩, ⟨i₀, ha₀, hs₀, hu₀⟩, hid⟩ := hG E hunr n hn μ e hμ lam
  have hab : ∀ i, a i + (n - a i) = n := fun i => Nat.add_sub_cancel' (hw i).1
  obtain ⟨c, hc, hst⟩ := hst π hreg hd hinf S hS' Z hZ B τ (fun w hw => (hB w hw).1) fun w hw => (hf w hw).1
  obtain ⟨Js, _, Ds, Bs, hDs, hDsI, hDsS, hst⟩ := hst (ct0 μ (Nat.add_zero n) f) (hLc n 0 _) (hRg n 0 _)
  choose J hJ D₁ D₂ B₁ B₂ hD hDI hDS hEb using fun i => hE E hunr (a i) (n - a i) (by rw [hab i]; exact hn) S hS' (l₁ i) (l₂ i) Z hZ
    (ct0 μ (hab i) f) (hLc _ _ _) (hRg _ _ _)
  have hoff := off_cofinite hP Z
  have hBst : ∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → inv (B w) = B w :=
    ((hCI E n hn π hd).and hoff).mono fun w h hns => h.1 hns _ (hB w h.2).1
  let I : Type := ι ⊕ Js ⊕ (Σ i : {i : κ // 1 ≤ a i ∧ 1 ≤ n - a i}, J i.1)
  let C : I → Pl E → Multiset ℂˣ := Sum.elim BU (Sum.elim Bs fun p w => un μ (a p.1.1) (n - a p.1.1) w (B₁ p.1.1 p.2 w) (B₂ p.1.1 p.2 w))
  have hdat : ∀ (D : CD E n) (X : Pl E → Multiset ℂˣ), ¬ D.Has π → D.Reg →
      (∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → inv (X w) = X w) → (∀ w, Off Z w → D.Sat w (X w)) →
      ∃ w, Off Z w ∧ IsSplitAt w ∧ (B w).card = n ∧ (X w).card = n ∧ X w ≠ B w := fun D X h1 hr hs h2 => by
    by_contra h
    refine hND E hunr n hn hn4 π hreg hd D h1 hr ((hoff.and hs).mono fun w hx hns => ⟨X w, h2 w hx.1, hx.2 hns⟩)
      (hoff.mono fun w ho hs => ⟨B w, ?_, (hB w ho).1⟩)
    have : X w = B w := by_contra fun h' => h ⟨w, ho, hs, (hB w ho).1.card, sat_card (h2 w ho), h'⟩
    exact this ▸ h2 w ho
  obtain ⟨T, e₁, e₂, hT, hTZ, hv1, hv0⟩ := hSep E n S hS' Z I B C (by
    rintro (i | j | ⟨i, j⟩)
    · exact hBU i
    · exact hdat (Ds j) (Bs j) (hDs j).1 (hRO E n lam (Ds j) (hDsI j))
        (hBst.mono fun w h hns => hDsS j w hns (h hns)) (hDs j).2
    · obtain ⟨D, h1, hr, h2⟩ := hTw E n _ _ (hab i.1) i.2.1 i.2.2 μ e hμ (l₁ i.1) (l₂ i.1) lam (hw i.1).2
        (D₁ i.1 j) (D₂ i.1 j) (hDI i.1 j).1 (hDI i.1 j).2
      exact hdat D _ (h1 π) hr
        (Filter.Eventually.of_forall fun w hns => hUS E μ _ _ w _ _ ((hMI E μ e hμ).1 w hns)
          (hDS i.1 j w hns).1 (hDS i.1 j w hns).2)
        fun w ho => h2 w _ _ (hB w ho).2 (hD i.1 j w ho).1 (hD i.1 j w ho).2)
  have un0 : ∀ X : Pl E → Multiset ℂˣ, (fun w => un μ n 0 w (X w) ((0 : Pl E → Multiset ℂˣ) w)) = X := fun X => by
    funext w; simp [un]
  let Φ := fun (a b : ℕ) (h : a + b = n) (k : ℕ) =>
    fam Z T (ct0 μ h f) (fun w => (e₁ w).bind (t a b h w)) (fun w => (e₂ w).bind (t a b h w)) k
  set P : ℂ := c * ∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => ct0 μ (Nat.add_zero n) f w (g, 1) with hPdef
  set Q : ℂ := ∏ w ∈ Z, trc (τ w).ρ (KGL w n) (f w) with hQdef
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun w hw => (hf w hw).2.2
  have hPQ : P = c * Q := congrArg (c * ·) (Finset.prod_congr rfl fun w hw => hTr E n w (hZ w hw).2 μ (τ w) f (hf w hw).2.1)
  have hU := hUv f hK2 T hT hTZ e₁ e₂ hv1 fun j => hv0 (.inl j)
  have hSt : Tendsto (fun k => geomSt2 S lam l₀ (Φ n 0 (Nat.add_zero n) k)) atTop (𝓝 P) := by
    have h1 := small_tendsto (hst T hT hTZ _ _ (1 / 2) (by norm_num) fun j => by
      rw [(ht n 0 (Nat.add_zero n) T hT hTZ e₁ e₂).1 _ _ fun w ho => ⟨sat_card ((hDs j).2 w ho), rfl⟩, un0]
      have := hv0 (.inr (.inl j))
      simp only [C, Sum.elim_inr, Sum.elim_inl] at this
      rw [this]; norm_num)
    rw [(ht n 0 (Nat.add_zero n) T hT hTZ e₁ e₂).1 _ _ fun w ho => ⟨(hB w ho).1.card, rfl⟩, un0, hv1] at h1
    have h2 := h1.add_const P
    simpa [hPdef, Φ] using h2
  have hterm : ∀ i, Tendsto (fun k => ((sg i : ℤ) : ℂ) * geomSt2 S (l₁ i) (l₂ i) (Φ _ _ (hab i) k)) atTop
      (𝓝 (if 1 ≤ a i ∧ 1 ≤ n - a i then 0 else P)) := fun i => by
    split_ifs with hm
    · have h1 := small_tendsto (hEb i T hT hTZ _ _ (1 / 2) (by norm_num) fun j => by
        rw [(ht _ _ (hab i) T hT hTZ e₁ e₂).1 _ _ fun w ho => ⟨sat_card (hD i j w ho).1, sat_card (hD i j w ho).2⟩]
        have := hv0 (.inr (.inr ⟨⟨i, hm⟩, j⟩))
        simp only [C, Sum.elim_inr] at this
        rw [this]; norm_num)
      simpa using h1.const_mul ((sg i : ℤ) : ℂ)
    · have h0 : a i = 0 ∨ n - a i = 0 := by omega
      have hs : sg i = 1 := by
        rcases h0 with h | h
        · rw [hu₀ i h]; exact hs₀
        · rw [hu₁ i (by have := hab i; omega)]; exact hs₁
      refine hSt.congr fun k => ?_
      rw [hs, hEn E n _ _ (hab i) h0 μ e S (l₁ i) (l₂ i) lam l₀ (famU Z T f e₁ e₂ k) _ _ (hw i).2
        (fun w hw => (((ht _ _ (hab i) T hT hTZ e₁ e₂).2 k).2 w hw).2)
        (fun w hw => (((ht _ _ (Nat.add_zero n) T hT hTZ e₁ e₂).2 k).2 w hw).2)]
      simp [Φ]
  have hsum := tendsto_finset_sum Finset.univ fun i _ => hterm i
  have hzero : ∀ k, 1 ≤ k → ∑ i, ((sg i : ℤ) : ℂ) * geomSt2 S (l₁ i) (l₂ i) (Φ _ _ (hab i) k) =
      (Nat.card {i // At π (σ i)} : ℂ) * Q := fun k hk => by
    have h1 := hid S hS' K' (famU Z T f e₁ e₂ k) (fun a' => if h : a' + (n - a') = n then Φ a' (n - a') h k else 0) hK
      (hU k).1 fun a' ha' => by
        have h := Nat.add_sub_cancel' ha'
        simp only [dif_pos h]
        exact ⟨((ht _ _ h T hT hTZ e₁ e₂).2 k).1, fun w hw => (((ht _ _ h T hT hTZ e₁ e₂).2 k).2 w hw).1⟩
    simp only [dif_pos (hab _)] at h1
    rw [← h1]
    refine mul_left_cancel₀ hdim ?_
    rw [← (hU k).2 hk, hgt _ (hU k).1 ⟨w₀, (hZ w₀ hw₀).1, fun y hy => hr₀ _ (by simpa only [famU, if_pos hw₀] using hy)⟩]
  have hlim := tendsto_nhds_unique hsum (tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun k hk => (hzero k hk).symm))
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul] at hlim
  haveI := Classical.decEq κ
  have hne : i₀ ≠ i₁ := fun h => by rw [h, ha₁] at ha₀; omega
  have hfil : (Finset.univ.filter fun i => ¬ (1 ≤ a i ∧ 1 ≤ n - a i)) = {i₀, i₁} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have := (hw i).1
      by_cases h0 : a i = 0
      · exact Or.inl (hu₀ i h0)
      · exact Or.inr (hu₁ i (by omega))
    · rintro (rfl | rfl) <;> omega
  rw [hfil, Finset.card_pair hne, hPQ, ← mul_assoc] at hlim
  have h2 := congrArg norm (mul_right_cancel₀ hQ0 hlim)
  rw [norm_mul, hc, Complex.norm_natCast, Complex.norm_natCast] at h2
  exact_mod_cast h2.symm
