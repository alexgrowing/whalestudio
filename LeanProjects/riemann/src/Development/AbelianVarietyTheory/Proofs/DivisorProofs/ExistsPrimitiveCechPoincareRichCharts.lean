import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPrimitiveBoxSegment

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

set_option autoImplicit false in
open CategoryTheory TopologicalSpace in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} in
private theorem exists_global_cechPrimitive_of_zero_section_lemma
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {g : ℕ} {K : Type}
    (W : K → Set (P × (Fin g → ℂ))) (c : K → K → P × (Fin g → ℂ) → ℂ)
    (ω : K → Fin g → P × (Fin g → ℂ) → ℂ) (V : Set P) (hV : IsOpen V) (hW : ∀ k, IsOpen (W k))
    (hcov : ∀ p : P × (Fin g → ℂ), p.1 ∈ V → ∃ k, p ∈ W k)
    (hc : ∀ k l, AnalyticOnNhd ℂ (c k l) (W k ∩ W l))
    (hcoc : ∀ k l m, ∀ p ∈ W k, p ∈ W l → p ∈ W m → c k m p = c k l p + c l m p)
    (hω : ∀ k a, AnalyticOnNhd ℂ (ω k a) (W k))
    (hcl : ∀ k a b, ∀ p ∈ W k,
      fderiv ℂ (ω k b) p (0, Pi.single a 1) = fderiv ℂ (ω k a) p (0, Pi.single b 1))
    (hd : ∀ k l a, ∀ p ∈ W k, p ∈ W l →
      ω k a p - ω l a p = fderiv ℂ (c k l) p (0, Pi.single a 1))
    (k₀ : K) (h₀ : ∀ z ∈ V, (z, (0 : Fin g → ℂ)) ∈ W k₀) :
    ∃ G : K → P × (Fin g → ℂ) → ℂ,
      (∀ k, ∀ p ∈ W k, p.1 ∈ V → AnalyticAt ℂ (G k) p) ∧
      (∀ k a, ∀ p ∈ W k, p.1 ∈ V → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧
      (∀ k l, ∀ p ∈ W k, p ∈ W l → p.1 ∈ V → G k p - G l p = c k l p) := by
  have box := _root_.GlobalTheory.exists_cechPrimitive_box_segment W c ω V hV hW hcov hc hcoc hω hcl hd
  have box' : ∀ q : P × (Fin g → ℂ), ∃ Z : Set P, ∃ C : Set (Fin g → ℂ),
      ∃ G : K → P × (Fin g → ℂ) → ℂ, q.1 ∈ V →
        (IsOpen Z ∧ q.1 ∈ Z ∧ Z ⊆ V ∧ IsOpen C ∧ Convex ℝ C ∧ (0 : Fin g → ℂ) ∈ C ∧ q.2 ∈ C ∧
        (∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ Z ×ˢ C)) ∧
        (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧
        ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G l p = c k l p) := by
    intro q
    by_cases hq : q.1 ∈ V
    · obtain ⟨Z, C, G, h⟩ := box q.1 hq q.2
      exact ⟨Z, C, G, fun _ => h⟩
    · exact ⟨∅, ∅, fun _ _ => 0, fun h => absurd h hq⟩
  choose Z C G hG using box'
  choose κ hκ using hcov

  have hfib : ∀ q, q.1 ∈ V → ∀ k, ∀ y ∈ W k, y ∈ Z q ×ˢ C q → ∀ v : Fin g → ℂ,
      fderiv ℂ (G q k) y ((0 : P), v) = ∑ a, v a * ω k a y := by
    intro q hq k y hy hyB v
    have hv : ((0 : P), v) = ∑ a, v a • ((0 : P), (Pi.single a (1 : ℂ) : Fin g → ℂ)) := by
      ext j
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, smul_eq_mul, (hG q hq).2.2.2.2.2.2.2.2.1 k a y hy hyB]
  set H : P × (Fin g → ℂ) → K → P × (Fin g → ℂ) → ℂ :=
    fun q k x => G q k x - G q k₀ (x.1, 0) with hH
  have huniq : ∀ q q' k x, q.1 ∈ V → q'.1 ∈ V → x ∈ W k → x.1 ∈ Z q → x.1 ∈ Z q' →
      x.2 ∈ C q → x.2 ∈ C q' → H q k x = H q' k x := by
    intro q q' k x hq hq' hxk hz hz' hw hw'
    obtain ⟨-, -, hZV, hCo, hCc, h0C, -, hGa, -, hGc⟩ := hG q hq
    obtain ⟨-, -, -, hCo', hCc', h0C', -, hGa', -, hGc'⟩ := hG q' hq'
    have hzV : x.1 ∈ V := hZV hz
    have hind : ∀ k k' (y : P × (Fin g → ℂ)), y ∈ W k → y ∈ W k' → y.1 ∈ Z q → y.1 ∈ Z q' →
        y.2 ∈ C q → y.2 ∈ C q' → G q k y - G q' k y = G q k' y - G q' k' y := by
      intro k k' y hk hk' h1 h2 h3 h4
      have e1 := hGc k k' y hk hk' ⟨h1, h3⟩
      have e2 := hGc' k k' y hk hk' ⟨h2, h4⟩
      linear_combination e1 - e2
    set φ : (Fin g → ℂ) → ℂ := fun w =>
      G q (κ (x.1, w) hzV) (x.1, w) - G q' (κ (x.1, w) hzV) (x.1, w) with hφ
    have hS : IsOpen (C q ∩ C q') := hCo.inter hCo'
    have hderiv : ∀ w ∈ C q ∩ C q', HasFDerivAt φ (0 : (Fin g → ℂ) →L[ℂ] ℂ) w := by
      intro w hw
      set k := κ (x.1, w) hzV
      have hk : (x.1, w) ∈ W k := hκ (x.1, w) hzV
      have hU : IsOpen ({w' | (x.1, w') ∈ W k} ∩ (C q ∩ C q')) :=
        ((hW k).preimage (continuous_const.prodMk continuous_id)).inter hS
      have heq : (fun w' => G q k (x.1, w') - G q' k (x.1, w')) =ᶠ[nhds w] φ := by
        filter_upwards [hU.mem_nhds ⟨hk, hw⟩] with w' hw'
        exact hind k _ (x.1, w') hw'.1 (hκ (x.1, w') hzV) hz hz' hw'.2.1 hw'.2.2
      have hA : HasFDerivAt (G q k) (fderiv ℂ (G q k) (x.1, w)) (x.1, w) :=
        ((hGa k (x.1, w) ⟨hk, hz, hw.1⟩).differentiableAt).hasFDerivAt
      have hA' : HasFDerivAt (G q' k) (fderiv ℂ (G q' k) (x.1, w)) (x.1, w) :=
        ((hGa' k (x.1, w) ⟨hk, hz', hw.2⟩).differentiableAt).hasFDerivAt
      have hin : HasFDerivAt (fun w' : Fin g → ℂ => (x.1, w'))
          ((0 : (Fin g → ℂ) →L[ℂ] P).prod (ContinuousLinearMap.id ℂ (Fin g → ℂ))) w :=
        (hasFDerivAt_const x.1 w).prodMk (hasFDerivAt_id w)
      have hsum := (hA.comp w hin).sub (hA'.comp w hin)
      refine (hsum.congr_of_eventuallyEq heq.symm).congr_fderiv ?_
      ext v
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
        ContinuousLinearMap.id_apply]
      rw [hfib q hq k _ hk ⟨hz, hw.1⟩, hfib q' hq' k _ hk ⟨hz', hw.2⟩, sub_self]
    have hconst : φ x.2 = φ 0 := by
      refine Convex.is_const_of_fderivWithin_eq_zero (hCc.inter hCc')
        (fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => ?_) ⟨hw, hw'⟩ ⟨h0C, h0C'⟩
      rw [fderivWithin_of_isOpen hS hw, (hderiv w hw).fderiv]
    have e1 : φ x.2 = G q k x - G q' k x :=
      hind _ k (x.1, x.2) (hκ (x.1, x.2) hzV) hxk hz hz' hw hw'
    have e2 : φ 0 = G q k₀ (x.1, 0) - G q' k₀ (x.1, 0) :=
      hind _ k₀ (x.1, 0) (hκ (x.1, 0) hzV) (h₀ _ hzV) hz hz' h0C h0C'
    simp only [hH]
    linear_combination e1.symm.trans (hconst.trans e2)
  have hloc : ∀ k x, x ∈ W k → x.1 ∈ V →
      (fun y => H y k y) =ᶠ[nhds x] H x k := by
    intro k x hxk hxV
    obtain ⟨hZo, hxZ, hZV, hCo, -, -, hxC, -⟩ := hG x hxV
    filter_upwards [((hW k).inter (hZo.prod hCo)).mem_nhds ⟨hxk, hxZ, hxC⟩] with y hy
    have hyV : y.1 ∈ V := hZV hy.2.1
    obtain ⟨-, hyZ, -, -, -, -, hyC, -⟩ := hG y hyV
    exact huniq y x k y hyV hxV hy.1 hyZ hy.2.1 hyC hy.2.2
  set L : P × (Fin g → ℂ) →L[ℂ] P × (Fin g → ℂ) :=
    (ContinuousLinearMap.fst ℂ P (Fin g → ℂ)).prod 0 with hL
  have hfun : ∀ x k, H x k = G x k - G x k₀ ∘ L := by
    intro x k
    funext y
    simp [hH, hL]
  refine ⟨fun k y => H y k y, ?_, ?_, ?_⟩
  · intro k x hxk hxV
    obtain ⟨-, hxZ, -, -, -, h0C, hxC, hGa, -⟩ := hG x hxV
    have h1 : AnalyticAt ℂ (G x k) x := hGa k x ⟨hxk, hxZ, hxC⟩
    have h2 : AnalyticAt ℂ (G x k₀) (L x) := hGa k₀ (x.1, 0) ⟨h₀ _ hxV, hxZ, h0C⟩
    have h3 := (h1.sub (h2.comp (L.analyticAt x)))
    rw [← hfun] at h3
    exact h3.congr (hloc k x hxk hxV).symm
  · intro k a x hxk hxV
    obtain ⟨-, hxZ, -, -, -, h0C, hxC, hGa, hGd, -⟩ := hG x hxV
    have h1 : HasFDerivAt (G x k) (fderiv ℂ (G x k) x) x :=
      (hGa k x ⟨hxk, hxZ, hxC⟩).differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (G x k₀) (fderiv ℂ (G x k₀) (L x)) (L x) :=
      (hGa k₀ (x.1, 0) ⟨h₀ _ hxV, hxZ, h0C⟩).differentiableAt.hasFDerivAt
    have h3 := h1.sub (h2.comp x L.hasFDerivAt)
    rw [← hfun] at h3
    rw [(hloc k x hxk hxV).fderiv_eq, h3.fderiv]
    have hL0 : L ((0 : P), (Pi.single a (1 : ℂ) : Fin g → ℂ)) = 0 := by simp [hL]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, hL0, map_zero, sub_zero,
      hGd k a x hxk ⟨hxZ, hxC⟩]
  · intro k l x hxk hxl hxV
    obtain ⟨-, hxZ, -, -, -, -, hxC, -, -, hGc⟩ := hG x hxV
    simp only [hH]
    linear_combination hGc k l x hxk hxl ⟨hxZ, hxC⟩

set_option autoImplicit false in
open CategoryTheory TopologicalSpace in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} in
private theorem hol_sub_fn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {W : TopologicalSpace.Opens E} (f h : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (f - h).fn p = f.fn p - h.fn p := by
  rw [← _root_.GlobalTheory.AnPer.Hol.ev_apply p hp, map_sub,
    _root_.GlobalTheory.AnPer.Hol.ev_apply, _root_.GlobalTheory.AnPer.Hol.ev_apply]

set_option autoImplicit false in
open CategoryTheory TopologicalSpace in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} in

theorem _root_.GlobalTheory.AnPer.Charts.exists_primitive_of_rich {I : Type} [Fintype I] {g : ℕ} {Λ : Type}
    [AddCommGroup Λ] {F : _root_.GlobalTheory.AnPer.Fam I g Λ}
    (K : _root_.GlobalTheory.AnPer.Charts F) (hR : K.Rich)
    (hB : K.Based)
    (a : ∀ k k', K.le 0 k' k → _root_.GlobalTheory.AnPer.Hol (K.W k'))
    (ω : ∀ k, Fin g → _root_.GlobalTheory.AnPer.Hol (K.W k))
    (hcoc : ∀ k k' k'' (e : K.le 0 k' k)
      (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k),
      a k k'' e'' = _root_.GlobalTheory.AnPer.Charts.sh e' (a k k' e) + a k' k'' e')
    (hcl : ∀ k i j, _root_.GlobalTheory.AnPer.dw i (ω k j) =
      _root_.GlobalTheory.AnPer.dw j (ω k i))
    (hd : ∀ k k' (e : K.le 0 k' k) i,
      ω k' i - _root_.GlobalTheory.AnPer.Charts.sh e (ω k i) =
        _root_.GlobalTheory.AnPer.dw i (a k k' e)) :
    ∃ G : ∀ k, _root_.GlobalTheory.AnPer.Hol (K.W k),
      (∀ k i, _root_.GlobalTheory.AnPer.dw i (G k) = ω k i) ∧
      ∀ k k' (e : K.le 0 k' k),
        a k k' e = G k' - _root_.GlobalTheory.AnPer.Charts.sh e (G k) := by
  classical
  obtain ⟨hcov, hmeet⟩ := hR
  obtain ⟨k₀, hk₀⟩ := hB
  have hsub : ∀ {k k' : K.K}, K.le 0 k' k → ∀ p ∈ K.W k', p ∈ K.W k := by
    intro k k' e p hp
    have := K.maps e p hp
    rwa [_root_.GlobalTheory.AnPer.Fam.shift_zero] at this
  have htrans : ∀ {k k' k'' : K.K}, K.le 0 k' k → K.le 0 k'' k' → K.le 0 k'' k := by
    intro k k' k'' e e'
    simpa using K.le_trans e e'
  have hsh : ∀ {k k' : K.K} (e : K.le 0 k' k) (f : _root_.GlobalTheory.AnPer.Hol (K.W k)),
      ∀ p ∈ K.W k', (_root_.GlobalTheory.AnPer.Charts.sh e f).fn p = f.fn p := by
    intro k k' e f p hp
    rw [_root_.GlobalTheory.AnPer.Charts.fn_sh e f hp, _root_.GlobalTheory.AnPer.Fam.shift_zero]
  have hdw : ∀ {k : K.K} (i : Fin g) (f : _root_.GlobalTheory.AnPer.Hol (K.W k)), ∀ p ∈ K.W k,
      (_root_.GlobalTheory.AnPer.dw i f).fn p = fderiv ℂ f.fn p (0, Pi.single i 1) := by
    intro k i f p hp
    exact _root_.GlobalTheory.AnPer.Hol.fn_der _ f hp

  have hpc : ∀ k k' k'' (e : K.le 0 k' k) (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k),
      ∀ p ∈ K.W k'', (a k k'' e'').fn p = (a k k' e).fn p + (a k' k'' e').fn p := by
    intro k k' k'' e e' e'' p hp
    rw [hcoc k k' k'' e e' e'', _root_.GlobalTheory.AnPer.Hol.fn_add _ _ hp, hsh e' _ p hp]
  have hmeet0 : ∀ (k₁ k₂ : K.K) (p : _root_.GlobalTheory.AnPer.Tot I g), p ∈ K.W k₁ →
      p ∈ K.W k₂ → ∃ k, p ∈ K.W k ∧ K.le 0 k k₁ ∧ K.le 0 k k₂ := by
    intro k₁ k₂ p h₁ h₂
    exact hmeet 0 k₁ k₂ p h₁ (by rwa [_root_.GlobalTheory.AnPer.Fam.shift_zero])
  choose! μ hμ using hmeet0

  let c : K.K → K.K → _root_.GlobalTheory.AnPer.Tot I g → ℂ := fun k₁ k₂ p =>
    if h : p ∈ K.W k₁ ∧ p ∈ K.W k₂ then
      (a k₂ (μ k₁ k₂ p) (hμ k₁ k₂ p h.1 h.2).2.2).fn p -
        (a k₁ (μ k₁ k₂ p) (hμ k₁ k₂ p h.1 h.2).2.1).fn p
    else 0
  have hind : ∀ (k₁ k₂ k : K.K) (e₁ : K.le 0 k k₁) (e₂ : K.le 0 k k₂), ∀ p ∈ K.W k,
      c k₁ k₂ p = (a k₂ k e₂).fn p - (a k₁ k e₁).fn p := by
    intro k₁ k₂ k e₁ e₂ p hp
    have h₁ := hsub e₁ p hp
    have h₂ := hsub e₂ p hp
    simp only [c, dif_pos (And.intro h₁ h₂)]
    obtain ⟨hpm, em₁, em₂⟩ := hμ k₁ k₂ p h₁ h₂
    set k' := μ k (μ k₁ k₂ p) p with hk'
    obtain ⟨hpk', f₁, f₂⟩ := hμ k (μ k₁ k₂ p) p hp hpm
    have r1 := hpc k₁ k k' e₁ f₁ (htrans e₁ f₁) p hpk'
    have r2 := hpc k₂ k k' e₂ f₁ (htrans e₂ f₁) p hpk'
    have r3 := hpc k₁ _ k' em₁ f₂ (htrans e₁ f₁) p hpk'
    have r4 := hpc k₂ _ k' em₂ f₂ (htrans e₂ f₁) p hpk'
    linear_combination r3 - r4 - r1 + r2
  obtain ⟨Gf, hGa, hGd, hGc⟩ := exists_global_cechPrimitive_of_zero_section_lemma
    (P := I → ℂ) (g := g) (fun k => (K.W k : Set (_root_.GlobalTheory.AnPer.Tot I g))) c
    (fun k i => (ω k i).fn) (F.V : Set (I → ℂ)) F.V.isOpen (fun k => (K.W k).isOpen) hcov
    (by
      intro k₁ k₂ p hp
      obtain ⟨hpk, e₁, e₂⟩ := hμ k₁ k₂ p hp.1 hp.2
      have hev : (fun q => (a k₂ _ e₂).fn q - (a k₁ _ e₁).fn q) =ᶠ[nhds p] c k₁ k₂ := by
        filter_upwards [(K.W _).isOpen.mem_nhds hpk] with q hq
        exact (hind k₁ k₂ _ e₁ e₂ q hq).symm
      exact (((a k₂ _ e₂).analytic p hpk).sub
        ((a k₁ _ e₁).analytic p hpk)).congr hev)
    (by
      intro k l m p hk hl hm
      obtain ⟨hp', e₁, e₂⟩ := hμ k l p hk hl
      obtain ⟨hp'', f₁, f₂⟩ := hμ _ m p hp' hm
      rw [hind k m _ (htrans e₁ f₁) f₂ p hp'', hind k l _ (htrans e₁ f₁) (htrans e₂ f₁) p hp'',
        hind l m _ (htrans e₂ f₁) f₂ p hp'']
      ring)
    (fun k i => (ω k i).analytic)
    (by
      intro k i j p hp
      rw [← hdw i _ p hp, ← hdw j _ p hp, hcl])
    (by
      intro k₁ k₂ i p h₁ h₂
      obtain ⟨hpk, e₁, e₂⟩ := hμ k₁ k₂ p h₁ h₂
      have hev : ((a k₂ _ e₂).fn - (a k₁ _ e₁).fn) =ᶠ[nhds p] c k₁ k₂ := by
        filter_upwards [(K.W _).isOpen.mem_nhds hpk] with q hq
        exact (hind k₁ k₂ _ e₁ e₂ q hq).symm
      have d₁ := ((a k₁ _ e₁).analytic p hpk).differentiableAt
      have d₂ := ((a k₂ _ e₂).analytic p hpk).differentiableAt
      have hfd := (d₂.hasFDerivAt.sub d₁.hasFDerivAt).fderiv
      rw [← hev.fderiv_eq]
      rw [hfd, ContinuousLinearMap.sub_apply, ← hdw i _ p hpk,
        ← hdw i _ p hpk, ← hd k₂ _ e₂ i, ← hd k₁ _ e₁ i, hol_sub_fn _ _ hpk,
        hol_sub_fn _ _ hpk, hsh e₂ _ p hpk, hsh e₁ _ p hpk]
      ring)
    k₀ hk₀
  set Gh : ∀ k, _root_.GlobalTheory.AnPer.Hol (K.W k) := fun k =>
    _root_.GlobalTheory.AnPer.Hol.mk (Gf k)
      (fun p hp => hGa k p hp (K.base k p hp)) with hGh
  have hfn : ∀ k, ∀ q ∈ K.W k, (Gh k).fn q = Gf k q := fun k q hq =>
    _root_.GlobalTheory.AnPer.Hol.fn_mk _ _ hq
  refine ⟨Gh, ?_, ?_⟩
  · intro k i
    apply _root_.GlobalTheory.AnPer.Hol.ext_fn
    intro p hp
    rw [hdw i (Gh k) p hp, _root_.GlobalTheory.AnPer.Hol.fderiv_fn_congr (Gh k) (hfn k) hp]
    exact hGd k i p hp (K.base k p hp)
  · intro k k' e
    apply _root_.GlobalTheory.AnPer.Hol.ext_fn
    intro p hp
    rw [hol_sub_fn _ _ hp, hsh e _ p hp]
    rw [hfn k' p hp, hfn k p (hsub e p hp)]
    have h1 := hGc k k' p (hsub e p hp) hp (K.base k' p hp)
    have h2 := hind k k' k' e (K.le_refl k') p hp
    have h3 := hpc k' k' k' (K.le_refl k') (K.le_refl k') (K.le_refl k') p hp
    linear_combination h1 + h2 - h3

end GlobalTheory.AnPer.Charts
