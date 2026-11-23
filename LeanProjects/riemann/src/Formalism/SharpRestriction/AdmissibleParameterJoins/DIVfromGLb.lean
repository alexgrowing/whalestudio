import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def NumsL (D : D7) (L : SizeData₂ D) (Cn cL : ℝ) : Prop :=
  ∀ u, flipTwoThree.Nums D (flipTwoThree.Tu D u) (D.host.g 0) (D.host.g 1) Cn L.sc.x L.sc.b (cL * L.sc.L) L.sc.b' L.Sc
    L.etaSz

def WtsL (D : D7) (L : SizeData₂ D) (Cn : ℝ) : Prop :=
  ∀ u, flipTwoThree.Wts D u Cn L.sc.x L.sc.b L.sc.b' L.Sc L.etaSz

theorem tau1_mem_Psi (φ : Formalism.HC.Frame) (t : φ.A) : φ.tau1 t ∈ φ.Psi := by
  show φ.tau1 t ∈ φ.chD.ker
  rw [MonoidHom.mem_ker]
  rfl

theorem tau1_injective_alt (φ : Formalism.HC.Frame) : Function.Injective φ.tau1 := by
  intro a b h
  simpa [Formalism.HC.Frame.tau1, Formalism.HC.Frame.iota] using h

theorem sum_tops (D : D7) (g : D.what₂.Tau → ℝ) (h : D.host.TT → ℝ)
    (hg : ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t → g τ = h t) :
    ∑ τ ∈ topsOf D.host D.eTau, g τ = ∑ t : D.host.TT, h t := by
  symm
  refine Finset.sum_bij
    (fun (t : D.host.TT) _ => D.eTau.symm ⟨D.R.tau1 (t : D.R.A), tau1_mem_Psi D.R.toFrame (t : D.R.A)⟩)
    ?_ ?_ ?_ ?_
  · intro t _
    simp only [topsOf, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply,
      Subtype.coe_mk, Host.topPlaces, Finset.mem_image]
    exact ⟨(t : D.R.A), t.2, rfl⟩
  · intro a _ b _ hab
    have h1 := congrArg (fun x => ((D.eTau x : D.R.Psi) : D.R.GG)) hab
    simp only [Equiv.apply_symm_apply, Subtype.coe_mk] at h1
    exact Subtype.ext (tau1_injective_alt D.R.toFrame h1)
  · intro τ hτ
    simp only [topsOf, Finset.mem_filter, Finset.mem_univ, true_and, Host.topPlaces,
      Finset.mem_image] at hτ
    obtain ⟨a, ha, hat⟩ := hτ
    refine ⟨⟨a, ha⟩, Finset.mem_univ _, ?_⟩
    apply D.eTau.injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply, Subtype.coe_mk]
    exact hat
  · intro t _
    symm
    apply hg
    simp only [Equiv.apply_symm_apply, Subtype.coe_mk]

theorem lamCol_top (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (τ : D.what₂.Tau) (t : D.host.TT)
    (h : (D.eTau τ : D.R.GG) = D.R.tau1 t) : flipTwoThree.aT D u τ = (L.aT t : ℝ) := by
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨h1, -⟩ := L.top_u τ t hk h
  have e1 := D.hcW_first u τ hk
  have e2 : flipTwoThree.aT D u τ = (((D.hcW u τ).u ⟨0, hk⟩ : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2) := by
    simp only [flipTwoThree.aT, flipTwoThree.lamCol, dif_pos hk, hcToWeightQ, rhoVec, Fin.val_mk, Nat.cast_zero,
      sub_zero] <;> push_cast <;> ring
  rw [e2, e1, h1]
  ring

theorem scale_pos (s : Scale) : 0 < s.x ∧ 0 < s.L ∧ 0 < s.b ∧ 0 < s.a ∧ 0 < s.b' := by
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have hL : 0 < s.L := Real.rpow_pos_of_pos hx _
  have hb : 0 < s.b := Real.exp_pos _
  have ha : 0 < s.a := mul_pos hx hb
  exact ⟨hx, hL, hb, ha, div_pos ha (Real.exp_pos _)⟩

theorem orderBound_of_fifth_sixth (D : D7) (L : SizeData₂ D) (Cn C5 C6 cL : ℝ)
    (h5 : flipTwoThree.Conclusion5 D Cn C5 L.sc.x) (h6 : flipTwoThree.Conclusion6 D Cn C6 L.sc.x)
    (hcL : 1 ≤ cL) (hrd : 1 ≤ D.host.rdE)
    (hN : NumsL D L Cn cL) (hW : WtsL D L Cn) (CV : ∀ u, flipTwoThree.ColVal D u) :
    LocalQuadraticParts.FrobeniusExpansionCongruence L (max (max C5 C6) 0 * cL) := by
  intro u
  have hM5 : C5 ≤ max (max C5 C6) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM6 : C6 ≤ max (max C5 C6) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM0 : 0 ≤ max (max C5 C6) 0 := le_max_right _ _
  have hcL0 : 0 ≤ cL := by linarith
  have hMc := mul_le_mul_of_nonneg_left hcL hM0
  have hC5 : C5 ≤ max (max C5 C6) 0 * cL := by linarith
  have hC6 : C6 ≤ max (max C5 C6) 0 * cL := by linarith
  have h5' := h5 u _ _ _ _ _ (hN u) (hW u) (CV u)
  have h6' := h6 u _ _ _ _ _ (hN u) (hW u) (CV u)
  have hNu := hN u
  unfold flipTwoThree.Nums at hNu
  obtain ⟨-, -, -, -, -, -, hSc, heta, hmt, -, -, -, -, -, hv1, -⟩ := hNu
  have eT : flipTwoThree.Tu D u = (D.mem u).A.T := rfl
  rw [eT] at h5' h6'
  have hS : ∑ t ∈ flipTwoThree.tops D, flipTwoThree.aT D u t / (D.R.k : ℝ) * Real.log ((D.mem u).A.T : ℝ) =
      ∑ t : D.host.TT, ((L.aT t : ℝ) / D.R.k) * Real.log ((D.mem u).A.T : ℝ) :=
    sum_tops D _ _ (fun τ t h => by rw [lamCol_top D L u τ t h])
  rw [hS] at h5'
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hlk : 0 ≤ Real.log (D.R.k : ℝ) := Real.log_nonneg hk1
  have hlT : 0 ≤ Real.log ((D.mem u).A.T : ℝ) := Real.log_natCast_nonneg _
  have hlkv : 0 ≤ Real.log ((D.R.k : ℝ) * D.host.v) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hk1 hv1)
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have hsc := scale_pos L.sc
  have hx0 : 0 < L.sc.x := hsc.1
  have hxb : 0 ≤ L.sc.x * L.sc.b := (mul_pos hsc.1 hsc.2.2.1).le
  have hmt0 : (0 : ℝ) ≤ (D.R.m : ℝ) * D.R.t := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hb'x : 0 < L.sc.b' / L.sc.x := by linarith
  have hb' : 0 ≤ L.sc.b' := by
    by_contra hneg
    push_neg at hneg
    have := div_neg_of_neg_of_pos hneg hx0
    linarith
  have hbS : 0 ≤ L.sc.b' + L.Sc := by linarith
  have hk0 : (0 : ℝ) ≤ D.R.k := by linarith
  have hfk2L : 0 ≤ (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * L.sc.L :=
    mul_nonneg (mul_nonneg hf (sq_nonneg _)) hsc.2.1.le
  rw [show LocalQuadraticParts.nTT D = (D.host.TT.card : ℝ) from rfl, show L.sc.a = L.sc.x * L.sc.b from rfl]
  constructor
  · have p1 := mul_nonneg (sub_nonneg.mpr hC5) (mul_nonneg (mul_nonneg hn hxb) hlk)
    have p2 := mul_nonneg (sub_nonneg.mpr hC5) (mul_nonneg (mul_nonneg (mul_nonneg hf hk0) hbS) hlk)
    have p3 := mul_nonneg (sub_nonneg.mpr hC5) (mul_nonneg (mul_nonneg hf (by linarith : (0 : ℝ) ≤ L.Sc)) hlT)
    have p4 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hM5) hcL0) hfk2L
    linarith
  · have q1 := mul_nonneg (sub_nonneg.mpr hC6) (mul_nonneg (mul_nonneg hn hxb) hlkv)
    have q2 := mul_nonneg (sub_nonneg.mpr hC6)
      (mul_nonneg (mul_nonneg hf hbS) (add_nonneg (mul_nonneg hk0 hlkv) hlT))
    have q3 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hM6) hcL0) hfk2L
    linarith

theorem family_orderBound_of_fifth_sixth {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (Cn cL : ℝ) (h5 : flipTwoThree.ConclusionF5 Fm) (h6 : flipTwoThree.ConclusionF6 Fm) (hcL : 1 ≤ cL)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      1 ≤ (Fm.D x i).host.rdE ∧ NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧ WtsL (Fm.D x i) (Fm.L x i) Cn ∧
        ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) :
    LocalQuadraticParts.SlopesFamily Fm := by
  obtain ⟨C5, xa, hC5⟩ := h5 Cn
  obtain ⟨C6, xb, hC6⟩ := h6 Cn
  obtain ⟨x0, hx0⟩ := hE
  unfold LocalQuadraticParts.SlopesFamily
  refine ⟨max (max C5 C6) 0 * cL, max (max x0 xa) (max xb (Fm.x1 + 1)), ?_⟩
  intro x hx i
  have hxa : xa ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx0' : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : Fm.x1 < x := by
    have : Fm.x1 + 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    linarith
  obtain ⟨hrd, hN, hW, hCV⟩ := hx0 x hx0' i
  have hxx := Fm.L_x x i hx1
  have p5 : flipTwoThree.Conclusion5 (Fm.D x i) Cn C5 (Fm.L x i).sc.x := by rw [hxx]; exact hC5 x hxa hx1 i
  have p6 : flipTwoThree.Conclusion6 (Fm.D x i) Cn C6 (Fm.L x i).sc.x := by rw [hxx]; exact hC6 x hxb hx1 i
  exact orderBound_of_fifth_sixth (Fm.D x i) (Fm.L x i) Cn C5 C6 cL p5 p6 hcL hrd hN hW (fun u => (hCV u).some)

def SupTie (D : D7) (X : DivX D) (Lc : placeRankTwoOne.Loc D X) : Prop :=
  ∀ u i L L', i + 1 ≤ D.R.m →
    ∃ (T : ∀ s : D.what₂.LL →+* ℂ, flipTwoThree.Torus D i s) (Th : ∀ _ : D.what₂.LL →+* ℂ, (flipTwoThree.Gx D i → ℂ) → ℂ),
      (∀ s, (T s).Admis (Th s) ∧ (T s).l2Sq (Th s) = 1) ∧
      Lc.thSup u i L L' = DV.meanE D (fun s => Real.log (⨆ z, flipTwoThree.dens D i s (Th s) z))

def SupSize (D : D7) (large₂ : SizeData₂ D) (Cs : ℝ) : Prop :=
  ∀ i, i + 1 ≤ D.R.m →
    Real.log 4 + Real.log (2 + 8 * ((D.R.f * D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) * D.host.v) ≤ Cs * large₂.sc.L

private theorem meanE_le_lemma (D : D7) (g : (D.what₂.LL →+* ℂ) → ℝ) (c : ℝ) (h : ∀ s, g s ≤ c) :
    DV.meanE D g ≤ c := by
  have hcard : (Finset.univ : Finset (D.what₂.LL →+* ℂ)).card = Module.finrank ℚ D.what₂.LL := by
    rw [Finset.card_univ]
    convert NumberField.Embeddings.card D.what₂.LL ℂ
  have hpos : (0 : ℝ) < (Module.finrank ℚ D.what₂.LL : ℝ) := by
    exact_mod_cast Module.finrank_pos
  unfold DV.meanE
  rw [div_le_iff₀ hpos]
  calc ∑ σ, g σ ≤ ∑ _σ : D.what₂.LL →+* ℂ, c := Finset.sum_le_sum (fun σ _ => h σ)
    _ = (Module.finrank ℚ D.what₂.LL : ℝ) * c := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = c * (Module.finrank ℚ D.what₂.LL : ℝ) := mul_comm _ _

theorem supBound_of_size_packet (D : D7) (large₂ : SizeData₂ D) (X : DivX D) (Lc : placeRankTwoOne.Loc D X) (Cs : ℝ)
    (h : flipTwoThree.ThetaSupremumBound D) (hT : SupTie D X Lc) (hS : SupSize D large₂ Cs) (hv : 0 ≤ D.host.v) (hCs : 0 ≤ Cs) :
    placeRankTwoOne.ThetaSupBound D large₂ X Lc Cs := by
  intro u i L L' hi
  obtain ⟨T, Th, hTh, heq⟩ := hT u i L L' hi
  rw [heq]
  have hL : 0 < large₂.sc.L := (scale_pos large₂.sc).2.1
  have hS' := hS i hi
  have hNle : ((D.R.f * D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) ≤ (D.R.f : ℝ) * placeRankTwoOne.NN D ^ 2 := by
    have h1 : D.R.N i ≤ D.R.N D.R.m := by
      unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    have h2 : D.R.N (i + 1) ≤ D.R.N D.R.m := by
      unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
    have h3 : D.R.f * D.R.N i * D.R.N (i + 1) ≤ D.R.f * D.R.N D.R.m ^ 2 := by
      rw [sq, ← mul_assoc]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
    rw [show placeRankTwoOne.NN D = (D.R.N D.R.m : ℝ) from rfl]
    exact_mod_cast h3
  have hBs : ∀ s, Real.log (⨆ z, flipTwoThree.dens D i s (Th s) z) ≤
      ((D.R.f * D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) * (Cs * large₂.sc.L) := by
    intro s
    have hy0 : (0 : ℝ) ≤ 8 * ((D.R.f * D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) * D.host.v :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hv
    have hy : (0 : ℝ) < 2 + 8 * ((D.R.f * D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) * D.host.v := by linarith
    have hb : ∀ z, flipTwoThree.dens D i s (Th s) z ≤ (4 : ℝ) ^ (D.R.f * D.R.N i * D.R.N (i + 1)) *
        (2 + 8 * ((D.R.f * D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) * D.host.v) ^ (D.R.f * D.R.N i * D.R.N (i + 1)) := by
      intro z
      have := h i s (T s) (Th s) (hTh s).1 z
      rwa [(hTh s).2, mul_one] at this
    have h0 : ∀ z, 0 ≤ flipTwoThree.dens D i s (Th s) z := fun z => by unfold flipTwoThree.dens; positivity
    have hlogB : Real.log ((4 : ℝ) ^ (D.R.f * D.R.N i * D.R.N (i + 1)) *
        (2 + 8 * ((D.R.f * D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) * D.host.v) ^ (D.R.f * D.R.N i * D.R.N (i + 1))) ≤
        ((D.R.f * D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) * (Cs * large₂.sc.L) := by
      rw [Real.log_mul (pow_pos (by norm_num) _).ne' (pow_pos hy _).ne', Real.log_pow, Real.log_pow, ← mul_add]
      exact mul_le_mul_of_nonneg_left hS' (Nat.cast_nonneg _)
    have hsup := ciSup_le hb
    have hsup0 : 0 ≤ ⨆ z, flipTwoThree.dens D i s (Th s) z := Real.iSup_nonneg h0
    rcases hsup0.eq_or_lt with h00 | hpos
    · rw [← h00, Real.log_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hCs hL.le)
    · exact (Real.log_le_log hpos hsup).trans hlogB
  refine (meanE_le_lemma D _ _ hBs).trans ?_
  have := mul_le_mul_of_nonneg_right hNle (mul_nonneg hCs hL.le)
  linarith

theorem thirdAdmissible_of_sup (D : D7) (large₂ : SizeData₂ D) (X : DivX D) (Lc : placeRankTwoOne.Loc D X) (Cn C1 cL CG C : ℝ)
    (h1 : flipTwoThree.Conclusion1 D Cn C1 large₂.sc.x) (hN : NumsL D large₂ Cn cL) (hCl : ∀ u, flipTwoThree.ClsTie D u)
    (hG : FactDGam D CG) (hsup : placeRankTwoOne.ThetaSupBound D large₂ X Lc C)
    (hcL : 1 ≤ cL) (hCG : 0 ≤ CG) (hC : max C1 0 * cL ≤ C) (hC' : 2 * CG ≤ C) :
    placeRankTwoOne.adm3 D large₂ X Lc C := by
  have hsc := scale_pos large₂.sc
  have hL0 : 0 < large₂.sc.L := hsc.2.1
  have hL1 : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hcL0 : 0 ≤ cL := by linarith
  have hf2 : 2 ≤ 2 * D.R.ord := le_trans D.R.two_le_m D.R.m_le_f
  have hf : (2 : ℝ) ≤ D.R.f := by
    show (2 : ℝ) ≤ ((2 * D.R.ord : ℕ) : ℝ)
    exact_mod_cast hf2
  have hfN : (D.R.f : ℝ) ≤ D.R.N D.R.m := by
    have : 2 * D.R.ord ≤ D.R.k + D.R.m * (D.R.t + 1) := le_trans D.R.f_le_k (Nat.le_add_right _ _)
    show ((2 * D.R.ord : ℕ) : ℝ) ≤ ((D.R.k + D.R.m * (D.R.t + 1) : ℕ) : ℝ)
    exact_mod_cast this
  have hF0 : (0 : ℝ) < D.R.f := by linarith
  have hN0 : (0 : ℝ) < D.R.N D.R.m := by linarith
  unfold placeRankTwoOne.adm3
  refine ⟨hsup, ?_, ?_⟩
  · intro u i hi
    have h1' := (h1 u _ _ _ _ _ (hN u) (hCl u)).1 i hi
    have eT : flipTwoThree.Tu D u = (D.mem u).A.T := rfl
    rw [eT] at h1'
    have hlT : 0 ≤ Real.log ((D.mem u).A.T : ℝ) := Real.log_natCast_nonneg _
    have hlg : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
      have := Real.log_natCast_nonneg (D.host.g 0 * D.host.g 1)
      push_cast at this
      exact this
    have hM1 : C1 ≤ max C1 0 := le_max_left _ _
    have hM0 : 0 ≤ max C1 0 := le_max_right _ _
    have q1 : C1 * cL ≤ C := le_trans (mul_le_mul_of_nonneg_right hM1 hcL0) hC
    have q2 : C1 ≤ C := by have := mul_le_mul_of_nonneg_left hcL hM0; linarith
    have hN2 : (0 : ℝ) ≤ (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 := mul_nonneg hF0.le (sq_nonneg _)
    have e1 := mul_nonneg (sub_nonneg.mpr q1) (mul_nonneg hN2 hL0.le)
    have e2 := mul_nonneg (sub_nonneg.mpr q2) (mul_nonneg hN2 (add_nonneg hlT hlg))
    have hX : Real.log (Fintype.card ((D.mem u).C.cls i) : ℝ) ≤
        C * D.R.f * placeRankTwoOne.NN D ^ 2 * (large₂.sc.L + Real.log ((D.mem u).A.T : ℝ) +
          Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) := by
      rw [show placeRankTwoOne.NN D = (D.R.N D.R.m : ℝ) from rfl]
      linarith
    rcases Nat.eq_zero_or_pos (Fintype.card ((D.mem u).C.cls i)) with h0 | hpos
    · rw [h0, Nat.cast_zero]
      exact (Real.exp_pos _).le
    · calc (Fintype.card ((D.mem u).C.cls i) : ℝ)
          = Real.exp (Real.log (Fintype.card ((D.mem u).C.cls i) : ℝ)) :=
            (Real.exp_log (by exact_mod_cast hpos)).symm
        _ ≤ _ := Real.exp_le_exp.mpr hX
  · intro u i c hi
    have hdpos := (D.mem u).C.DGam_pos
    have hle : Nat.card ((D.mem u).C.stab i c) ≤ (D.mem u).C.DGam :=
      Nat.le_of_dvd hdpos ((D.mem u).C.dvd_DGam i hi c)
    have hGu := hG u
    have hlog : Real.log ((D.R.f : ℝ) * D.R.N D.R.m) ≤ 2 * (D.R.N D.R.m : ℝ) * large₂.sc.L := by
      rw [Real.log_mul hF0.ne' hN0.ne']
      have a1 := Real.log_le_sub_one_of_pos hF0
      have a2 := Real.log_le_sub_one_of_pos hN0
      have a3 := mul_le_mul_of_nonneg_left hL1 hN0.le
      linarith
    have hY : Real.log ((D.mem u).C.DGam : ℝ) ≤ C * D.R.f * placeRankTwoOne.NN D ^ 2 * large₂.sc.L := by
      rw [show placeRankTwoOne.NN D = (D.R.N D.R.m : ℝ) from rfl]
      have b1 := mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg hCG hF0.le) hN0.le)
      have b2 := mul_nonneg (sub_nonneg.mpr hC') (mul_nonneg (mul_nonneg hF0.le (sq_nonneg (D.R.N D.R.m : ℝ))) hL0.le)
      linarith
    calc (Nat.card ((D.mem u).C.stab i c) : ℝ) ≤ ((D.mem u).C.DGam : ℝ) := by exact_mod_cast hle
      _ = Real.exp (Real.log ((D.mem u).C.DGam : ℝ)) := (Real.exp_log (by exact_mod_cast hdpos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hY

theorem supBound_mono {D : D7} {large₂ : SizeData₂ D} {X : DivX D} {Lc : placeRankTwoOne.Loc D X} {C C' : ℝ}
    (h : placeRankTwoOne.ThetaSupBound D large₂ X Lc C) (hC : C ≤ C') : placeRankTwoOne.ThetaSupBound D large₂ X Lc C' := by
  intro u i L L' hi
  have hL := (scale_pos large₂.sc).2.1
  have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) * placeRankTwoOne.NN D ^ 2 * large₂.sc.L :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hL.le
  have h1 := mul_le_mul_of_nonneg_right hC h0
  have h2 := h u i L L' hi
  linarith

theorem thirdAdmissible_of_sizes (D : D7) (large₂ : SizeData₂ D) (X : DivX D) (Lc : placeRankTwoOne.Loc D X) (Cn C1 cL CG Cs : ℝ)
    (hs : flipTwoThree.ThetaSupremumBound D) (h1 : flipTwoThree.Conclusion1 D Cn C1 large₂.sc.x) (hT : SupTie D X Lc) (hS : SupSize D large₂ Cs)
    (hN : NumsL D large₂ Cn cL) (hCl : ∀ u, flipTwoThree.ClsTie D u) (hG : FactDGam D CG)
    (hv : 0 ≤ D.host.v) (hCs : 0 ≤ Cs) (hcL : 1 ≤ cL) (hCG : 0 ≤ CG) :
    placeRankTwoOne.adm3 D large₂ X Lc (max Cs (max (max C1 0 * cL) (2 * CG))) := by
  have hsup := supBound_of_size_packet D large₂ X Lc Cs hs hT hS hv hCs
  exact thirdAdmissible_of_sup D large₂ X Lc Cn C1 cL CG _ h1 hN hCl hG (supBound_mono hsup (le_max_left _ _)) hcL hCG
    (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) (le_max_right _ _))

theorem family_thirdAdmissible_of_sizes {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (XF : placeRankTwoOne.LocF Fm) (Cn cL CG Cs : ℝ)
    (hs : flipTwoThree.FamilySupremumBound Fm) (h1 : flipTwoThree.ConclusionF1 Fm) (hCs : 0 ≤ Cs) (hcL : 1 ≤ cL) (hCG : 0 ≤ CG)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), 0 ≤ (Fm.D x i).host.v ∧ NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧
      (∀ u, flipTwoThree.ClsTie (Fm.D x i) u) ∧ FactDGam (Fm.D x i) CG ∧ SupTie (Fm.D x i) (Fm.X x i) (XF x hx i) ∧
      SupSize (Fm.D x i) (Fm.L x i) Cs) :
    placeRankTwoOne.admF3 Fm XF := by
  obtain ⟨C1, xa, hC1⟩ := h1 Cn
  obtain ⟨x0, hx0⟩ := hE
  unfold placeRankTwoOne.admF3
  refine ⟨max Cs (max (max C1 0 * cL) (2 * CG)), max x0 xa, ?_⟩
  intro x hx hxle i
  obtain ⟨hv, hN, hCl, hG, hT, hS⟩ := hx0 x (le_trans (le_max_left _ _) hxle) hx i
  have hp1 : flipTwoThree.Conclusion1 (Fm.D x i) Cn C1 (Fm.L x i).sc.x := by
    rw [Fm.L_x x i hx]; exact hC1 x (le_trans (le_max_right _ _) hxle) hx i
  exact thirdAdmissible_of_sizes (Fm.D x i) (Fm.L x i) (Fm.X x i) (XF x hx i) Cn C1 cL CG Cs (hs x i) hp1 hT hS hN hCl hG
    hv hCs hcL hCG

theorem genusOne_theta_norm_bound (D : D7) (large₂ : SizeData₂ D) (Cn C cL : ℝ) (h : flipTwoThree.adm2 D Cn C large₂.sc.x)
    (hN : NumsL D large₂ Cn cL) : placeRankTwoOne.GenusOneThetaNorm D large₂ (C * cL) := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h2 := (h D.u₀ _ _ _ _ _ (hN D.u₀) 0 hm).2
  have key : ∀ s, Real.log (flipTwoThree.thetaLocalFactorAtIndex D D.u₀ 0 s ^ 2) =
      ((D.R.f : ℝ) * D.R.N 0 * D.R.N 1) * Real.log (D.gx.thOne s ^ 2) := by
    intro s
    unfold flipTwoThree.thetaLocalFactorAtIndex
    rw [← pow_mul, mul_comm _ 2, pow_mul, Real.log_pow, Nat.cast_mul, Nat.cast_mul, zero_add]
  simp only [key, zero_add] at h2
  rw [← Finset.mul_sum] at h2
  have hcard : (Fintype.card (D.what₂.LL →+* ℂ) : ℝ) = (Module.finrank ℚ D.what₂.LL : ℝ) := by
    norm_cast
    convert NumberField.Embeddings.card D.what₂.LL ℂ
  rw [hcard] at h2
  have hf2 : 2 ≤ 2 * D.R.ord := le_trans D.R.two_le_m D.R.m_le_f
  have hf : (0 : ℝ) < D.R.f := by
    show (0 : ℝ) < ((2 * D.R.ord : ℕ) : ℝ)
    exact_mod_cast (by omega : 0 < 2 * D.R.ord)
  have hk := D.R.m_add_three_le_k
  have hN0 : (0 : ℝ) < D.R.N 0 := by
    show (0 : ℝ) < ((D.R.k + 0 * (D.R.t + 1) : ℕ) : ℝ)
    exact_mod_cast (by omega : 0 < D.R.k + 0 * (D.R.t + 1))
  have hN1 : (0 : ℝ) < D.R.N 1 := by
    show (0 : ℝ) < ((D.R.k + 1 * (D.R.t + 1) : ℕ) : ℝ)
    exact_mod_cast (by omega : 0 < D.R.k + 1 * (D.R.t + 1))
  have hn : (0 : ℝ) < (D.R.f : ℝ) * D.R.N 0 * D.R.N 1 := mul_pos (mul_pos hf hN0) hN1
  unfold placeRankTwoOne.GenusOneThetaNorm placeRankTwoOne.thMean DV.meanE
  have e : (D.R.f : ℝ) * D.R.N 0 * D.R.N 1 *
      ((∑ s, Real.log (D.gx.thOne s ^ 2)) / (Module.finrank ℚ D.what₂.LL : ℝ)) ≤
      (D.R.f : ℝ) * D.R.N 0 * D.R.N 1 * (C * cL * large₂.sc.L) := by
    rw [← mul_div_assoc]
    linarith
  exact le_of_mul_le_mul_left e hn

theorem family_theta_norm_bound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cn cL : ℝ) (h : flipTwoThree.admF2 Fm)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, NumsL (Fm.D x i) (Fm.L x i) Cn cL) :
    placeRankTwoOne.ThetaNormFamily Fm := by
  obtain ⟨C, xa, hC⟩ := h Cn
  obtain ⟨x0, hx0⟩ := hE
  unfold placeRankTwoOne.ThetaNormFamily
  refine ⟨C * cL, max (max x0 xa) (Fm.x1 + 1), ?_⟩
  intro x hx i
  have hxa : xa ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx0' : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1 : Fm.x1 < x := by
    have : Fm.x1 + 1 ≤ x := le_trans (le_max_right _ _) hx
    linarith
  have p2 : flipTwoThree.adm2 (Fm.D x i) Cn C (Fm.L x i).sc.x := by rw [Fm.L_x x i hx1]; exact hC x hxa hx1 i
  exact genusOne_theta_norm_bound (Fm.D x i) (Fm.L x i) Cn C cL p2 (hx0 x hx0' i)

end Formalism.MainNotions.J
