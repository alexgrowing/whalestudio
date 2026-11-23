import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import Formalism.LFunctionBounds.LFunctionBoundsProofs.RectResidue

open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma neg_log_deriv_differentiableAt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {w : ℂ}
    (hL : DirichletCharacter.LFunction χ w ≠ 0) : DifferentiableAt ℂ (negLD χ) w := by
  have hLd := DirichletCharacter.differentiable_LFunction hχ
  have hd' : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) w :=
    ((hLd.analyticAt w).deriv).differentiableAt
  show DifferentiableAt ℂ (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
    DirichletCharacter.LFunction χ s)) w
  exact (hd'.div (hLd w) hL).neg

lemma perron_integrand_differentiableAt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y : ℝ}
    (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) (hL : DirichletCharacter.LFunction χ w ≠ 0) :
    DifferentiableAt ℂ (Fchi χ y) w := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  show DifferentiableAt ℂ (fun w => negLD χ w * (y : ℂ) ^ w / (w * (w - 1))) w
  refine ((neg_log_deriv_differentiableAt hχ hL).mul ?_).div (by fun_prop) (mul_ne_zero h0 (sub_ne_zero.2 h1))
  exact DifferentiableAt.const_cpow (f := fun w => w) differentiableAt_id (Or.inl hy')

lemma perron_integrand_residue_at_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y : ℝ}
    (hy : 0 < y) :
    ∃ A : ℂ → ℂ, DifferentiableAt ℂ A 1 ∧
      ∀ᶠ z in 𝓝[≠] (1 : ℂ), Fchi χ y z - negLD χ 1 * (y : ℂ) / (z - 1) = A z := by
  have hLd := DirichletCharacter.differentiable_LFunction hχ
  have hL1 : DirichletCharacter.LFunction χ 1 ≠ 0 := DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  set h : ℂ → ℂ := fun z => negLD χ z * (y : ℂ) ^ z / z with hh
  have hs : IsOpen {z : ℂ | DirichletCharacter.LFunction χ z ≠ 0 ∧ z ≠ 0} :=
    (isOpen_ne.preimage hLd.continuous).inter isOpen_ne
  have h1s : (1 : ℂ) ∈ {z : ℂ | DirichletCharacter.LFunction χ z ≠ 0 ∧ z ≠ 0} := ⟨hL1, one_ne_zero⟩
  have hdiff : DifferentiableOn ℂ h {z : ℂ | DirichletCharacter.LFunction χ z ≠ 0 ∧ z ≠ 0} := by
    intro z hz
    exact (((neg_log_deriv_differentiableAt hχ hz.1).mul
      (DifferentiableAt.const_cpow (f := fun w => w) differentiableAt_id (Or.inl hy'))).div
        differentiableAt_id hz.2).differentiableWithinAt
  refine ⟨dslope h 1,
    ((Complex.differentiableOn_dslope (hs.mem_nhds h1s)).2 hdiff).differentiableAt (hs.mem_nhds h1s), ?_⟩
  have hev : ∀ᶠ z in 𝓝[≠] (1 : ℂ), z ≠ 1 ∧ z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds (one_ne_zero : (1 : ℂ) ≠ 0))] with z hz1 hz0
    exact ⟨hz1, hz0⟩
  filter_upwards [hev] with z hz
  obtain ⟨hz1, hz0⟩ := hz
  rw [dslope_of_ne _ hz1, slope_def_field]
  simp only [hh, Fchi, cpow_one, div_one]
  field_simp [sub_ne_zero.2 hz1]

lemma perron_integrand_residue_real_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y : ℝ}
    (hy : 0 < y) {β : ℂ} (h0 : 0 < β.re) (h1 : β ≠ 1)
    (hLβ : DirichletCharacter.LFunction χ β = 0)
    (hd : deriv (DirichletCharacter.LFunction χ) β ≠ 0) :
    ∃ A : ℂ → ℂ, DifferentiableAt ℂ A β ∧
      ∀ᶠ z in 𝓝[≠] β, DirichletCharacter.LFunction χ z ≠ 0 ∧
        Fchi χ y z - (-((y : ℂ) ^ β / (β * (β - 1)))) / (z - β) = A z := by
  have hLd := DirichletCharacter.differentiable_LFunction hχ
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hβ0 : β ≠ 0 := fun h => by rw [h] at h0; simp at h0
  set L := DirichletCharacter.LFunction χ with hLdef
  set g := dslope L β with hg
  have hgd : Differentiable ℂ g := fun z =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).2 hLd.differentiableOn).differentiableAt
      Filter.univ_mem
  have hgβ : g β ≠ 0 := by rw [hg, dslope_same]; exact hd
  have hLz : ∀ z, L z = (z - β) * g z := by
    intro z
    have := sub_smul_dslope L β z
    rw [hLβ, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hderiv : ∀ z, deriv L z = g z + (z - β) * deriv g z := by
    intro z
    have hfun : L = fun z => (z - β) * g z := funext hLz
    have h1 : HasDerivAt (fun z => (z - β) * g z) (1 * g z + (z - β) * deriv g z) z :=
      ((hasDerivAt_id' z).sub_const β).mul (hgd z).hasDerivAt
    rw [hfun, h1.deriv]
    ring
  have hev : ∀ᶠ z in 𝓝[≠] β, z ≠ β ∧ g z ≠ 0 ∧ z ≠ 0 ∧ z ≠ 1 := by
    have h2 : ∀ᶠ z in 𝓝 β, g z ≠ 0 ∧ z ≠ 0 ∧ z ≠ 1 :=
      ((hgd β).continuousAt.eventually_ne hgβ).and
        ((show ∀ᶠ z in 𝓝 β, z ≠ 0 from isOpen_ne.mem_nhds hβ0).and
          (show ∀ᶠ z in 𝓝 β, z ≠ 1 from isOpen_ne.mem_nhds h1))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h2] with z hz hz'
    exact ⟨hz, hz'⟩
  set k : ℂ → ℂ := fun z => (y : ℂ) ^ z / (z * (z - 1)) with hk
  have hs : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 1} := isOpen_ne.inter isOpen_ne
  have hβs : β ∈ {z : ℂ | z ≠ 0 ∧ z ≠ 1} := ⟨hβ0, h1⟩
  have hkd : DifferentiableOn ℂ k {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
    intro z hz
    have hz' : DifferentiableAt ℂ (fun w : ℂ => (y : ℂ) ^ w / (w * (w - 1))) z :=
      (DifferentiableAt.const_cpow (f := fun w => w) differentiableAt_id (Or.inl hy')).div
        (by fun_prop) (mul_ne_zero hz.1 (sub_ne_zero.2 hz.2))
    exact hz'.differentiableWithinAt
  have hdk : DifferentiableAt ℂ (dslope k β) β :=
    ((Complex.differentiableOn_dslope (hs.mem_nhds hβs)).2 hkd).differentiableAt (hs.mem_nhds hβs)
  have hdg' : DifferentiableAt ℂ (deriv g) β := ((hgd.analyticAt β).deriv).differentiableAt
  refine ⟨fun z => -(dslope k β z) - deriv g z / g z * k z,
    hdk.neg.sub ((hdg'.div (hgd β) hgβ).mul ((hkd β hβs).differentiableAt (hs.mem_nhds hβs))), ?_⟩
  filter_upwards [hev] with z hz
  obtain ⟨hzβ, hgz, hz0, hz1⟩ := hz
  refine ⟨by rw [hLz]; exact mul_ne_zero (sub_ne_zero.2 hzβ) hgz, ?_⟩
  rw [dslope_of_ne _ hzβ, slope_def_field]
  have hLz' : ∀ z, DirichletCharacter.LFunction χ z = (z - β) * g z := hLz
  have hderiv' : ∀ z, deriv (DirichletCharacter.LFunction χ) z = g z + (z - β) * deriv g z := hderiv
  simp only [Fchi, negLD, hk, hderiv', hLz']
  field_simp [sub_ne_zero.2 hzβ, hgz, hz0, sub_ne_zero.2 hz1, hβ0, sub_ne_zero.2 h1]
  ring

theorem rectangle_contour_shift_character : RectShiftChi := by
  intro q _ χ hχ y hy σ₁ σ₀ T B hσ₁ hσ₁1 hσ₀ hT hB hZ hBz
  have hLd := DirichletCharacter.differentiable_LFunction hχ
  have hL1 : DirichletCharacter.LFunction χ 1 ≠ 0 := DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hBre : ∀ β ∈ B, 0 < ((β : ℂ)).re := fun β hβ => by simp; linarith [(hB β hβ).1]
  have hB1 : ∀ β ∈ B, (β : ℂ) ≠ 1 := fun β hβ h => hL1 (h ▸ hBz β hβ)
  set P : Finset ℂ := insert 1 (B.image (fun β : ℝ => (β : ℂ))) with hP
  set b : ℂ → ℂ := fun p => if p = 1 then negLD χ 1 * y else -((y : ℂ) ^ p / (p * (p - 1))) with hb
  have h1P : (1 : ℂ) ∉ B.image (fun β : ℝ => (β : ℂ)) := by
    intro h
    obtain ⟨β, hβ, hβ1⟩ := Finset.mem_image.1 h
    exact hB1 β hβ hβ1
  have hloc : ∀ p ∈ P, ∃ A : ℂ → ℂ, DifferentiableAt ℂ A p ∧
      ∀ᶠ z in 𝓝[≠] p, Fchi χ y z - b p / (z - p) = A z := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · obtain ⟨A, hA, hev⟩ := perron_integrand_residue_at_one hχ hy
      refine ⟨A, hA, ?_⟩
      filter_upwards [hev] with z hz
      simpa [hb] using hz
    · obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨A, hA, hev⟩ :=
        perron_integrand_residue_real_zero hχ hy (hBre β hβ) (hB1 β hβ) (hBz β hβ) (hB β hβ).2.2
      refine ⟨A, hA, ?_⟩
      filter_upwards [hev] with z hz
      simpa [hb, hB1 β hβ] using hz.2
  have hnhds : ∀ β ∈ B,
      {z : ℂ | z ≠ (β : ℂ) → DirichletCharacter.LFunction χ z ≠ 0} ∈ 𝓝 (β : ℂ) := by
    intro β hβ
    obtain ⟨A, -, hev⟩ :=
      perron_integrand_residue_real_zero hχ hy (hBre β hβ) (hB1 β hβ) (hBz β hβ) (hB β hβ).2.2
    exact eventually_nhdsWithin_iff.1 (hev.mono fun z hz => hz.1)
  set U : Set ℂ := {w | 0 < w.re} ∩ ({w | DirichletCharacter.LFunction χ w ≠ 0} ∪
      ⋃ p ∈ P, interior {z | z ≠ p → DirichletCharacter.LFunction χ z ≠ 0}) with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_ne.preimage hLd.continuous).union (isOpen_biUnion fun p _ => isOpen_interior))
  have hUgood : ∀ w ∈ U, w ∉ P →
      DirichletCharacter.LFunction χ w ≠ 0 ∧ w ≠ 0 ∧ w ≠ 1 := by
    intro w hw hwP
    refine ⟨?_, fun h => ?_, fun h => hwP (by rw [h, hP]; exact Finset.mem_insert_self _ _)⟩
    · rcases hw.2 with h | h
      · exact h
      · obtain ⟨p, hp, hwp⟩ := Set.mem_iUnion₂.1 h
        exact interior_subset hwp (fun h' => hwP (h' ▸ hp))
    · have h' := hw.1
      simp [h] at h'
  have hrect : (Set.uIcc σ₁ σ₀ ×ℂ Set.uIcc (-T) T) ⊆ U := by
    intro w hw
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hw
    refine ⟨show 0 < w.re by linarith [hw.1.1], ?_⟩
    by_cases hLw : DirichletCharacter.LFunction χ w = 0
    · right
      obtain ⟨β, hβ, rfl⟩ := hZ w hw.1.1 hw.1.2 (abs_le.2 hw.2) hLw
      exact Set.mem_iUnion₂.2 ⟨(β : ℂ), Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hβ),
        mem_interior_iff_mem_nhds.2 (hnhds β hβ)⟩
    · exact Or.inl hLw
  set G0 : ℂ → ℂ := fun w => Fchi χ y w - ∑ p ∈ P, b p / (w - p) with hG0
  set G : ℂ → ℂ := fun w => if w ∈ P then limUnder (𝓝[≠] w) G0 else G0 w with hG
  have hPc : IsClosed (P : Set ℂ) := P.finite_toSet.isClosed
  have hsumd : ∀ (S : Finset ℂ) (w : ℂ), w ∉ S →
      DifferentiableAt ℂ (fun z => ∑ p ∈ S, b p / (z - p)) w := by
    intro S w hw
    apply DifferentiableAt.fun_sum
    intro p hp
    exact (differentiableAt_const _).div (differentiableAt_id.sub_const p)
      (sub_ne_zero.2 fun h => hw (h ▸ hp))
  have hGd : DifferentiableOn ℂ G U := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    by_cases hwP : w ∈ P
    · obtain ⟨A, hA, hev⟩ := hloc w hwP
      set R : ℂ → ℂ := fun z => A z - ∑ p ∈ P.erase w, b p / (z - p) with hR
      have hRd : DifferentiableAt ℂ R w := hA.sub (hsumd _ w (Finset.notMem_erase w P))
      have hev2 : ∀ᶠ z in 𝓝[≠] w, z ∉ P ∧ G0 z = R z := by
        have hfar : ∀ᶠ z in 𝓝[≠] w, z ∉ (P.erase w : Set ℂ) :=
          nhdsWithin_le_nhds ((P.erase w).finite_toSet.isClosed.isOpen_compl.mem_nhds
            (Finset.notMem_erase w P))
        filter_upwards [hev, hfar, self_mem_nhdsWithin] with z hz hzf hzw
        refine ⟨fun hzP => hzf (Finset.mem_erase.2 ⟨hzw, hzP⟩), ?_⟩
        simp only [hG0, hR]
        rw [← hz, ← Finset.add_sum_erase P _ hwP]
        ring
      have hlim : limUnder (𝓝[≠] w) G0 = R w :=
        ((hRd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
          (hev2.mono fun z hz => hz.2.symm)).limUnder_eq
      have hEq : G =ᶠ[𝓝 w] R := by
        filter_upwards [eventually_nhdsWithin_iff.1 hev2] with z hz
        by_cases hzw : z = w
        · rw [hzw]
          simp only [hG, if_pos hwP, hlim]
        · obtain ⟨hzP, hzG⟩ := hz hzw
          simp only [hG, if_neg hzP]
          exact hzG
      exact hRd.congr_of_eventuallyEq hEq
    · obtain ⟨hLw, hw0, hw1⟩ := hUgood w hw hwP
      have hG0d : DifferentiableAt ℂ G0 w :=
        (perron_integrand_differentiableAt hχ hy hw0 hw1 hLw).sub (hsumd P w hwP)
      have hEq : G =ᶠ[𝓝 w] G0 := by
        filter_upwards [hPc.isOpen_compl.mem_nhds hwP] with z hz
        simp only [hG, if_neg (show z ∉ P from hz)]
      exact hG0d.congr_of_eventuallyEq hEq
  have hPin : ∀ p ∈ P, σ₁ < p.re ∧ p.re < σ₀ ∧ -T < p.im ∧ p.im < T := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
    · obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hp
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith [(hB β hβ).1, (hB β hβ).2.1]
  have hdec : ∀ w : ℂ, w ∉ P → Fchi χ y w = G w + ∑ p ∈ P, b p / (w - p) := by
    intro w hw
    simp only [hG, if_neg hw, hG0]
    ring
  have hres := Formalism.FX.rectangle_residue (Fchi χ y) G P b σ₁ σ₀ (-T) T (by linarith) (by linarith)
    hPin ⟨U, hUo, hrect, hGd⟩ hdec
  have hsum : ∑ p ∈ P, b p =
      negLD χ 1 * y - ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) := by
    rw [hP, Finset.sum_insert h1P,
      Finset.sum_image (fun x _ z _ h => Complex.ofReal_injective h)]
    simp only [hb, ↓reduceIte]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro β hβ
    rw [if_neg (hB1 β hβ)]
  unfold Formalism.ZF.rectInt
  unfold Formalism.FX.rectInt at hres
  rw [hres, hsum]

end Formalism.ZeroFreeDirichlet
