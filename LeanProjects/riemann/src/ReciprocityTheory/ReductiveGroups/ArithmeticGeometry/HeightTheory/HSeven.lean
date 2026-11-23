import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CardEmbPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HFour
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntNsg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FsumLeOf

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem h_seven (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (hF1d : d.TrivialPlaceHyp) (hSup : d.HtSup)
    (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K) (hx : ∀ c, d.wx x c ≠ 0) (ta' : ∀ c, A c)
    (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    let lr := Real.log (d.N + 1 : ℕ) + 1 / 2
    let HL := d.Hgt h d.wL (d.wx x)
    let Hde := d.Hgt h (d.n1 • d.wde) d.et / d.n1
    let ade := (d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1
    let aG1 := (d.aG h ((2 : ℕ) • d.G1) d.ta1 : ℝ) / 2
    let X8 := d.HgtMM h (d.wx x) + d.del * ((∑ᶠ la, d.nu la * logNorm la) /
      (Module.finrank ℚ K : ℝ) + d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo) + d.D * d.cc * d.g0 * ade * lr
    let Y := d.del * d.PI4 * d.D * d.wsize d.wL + d.D * aG1 * lr
    HL ≤ X8 + d.cc * d.g0 * Hde ∧ Hde ≤ HL + Y ∧
      d.Hgt h d.wF ta' ≤ (d.D + 4) * HL + d.del * d.PI4 * d.D * d.wsize d.wL +
        d.D * d.aG h d.G2 d.ta2 * lr := by
  dsimp only
  have hf : ∀ c, d.wx x c ∈ 𝒜 c d.wL ∧ d.wx x c ≠ 0 := fun c => ⟨d.wx_mem hd x c, hx c⟩
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hi : (0 : ℝ) < d.i := by exact_mod_cast hd.i_ge
  have hg : (0 : ℝ) < d.g0 := by exact_mod_cast hd.g_zero_ge_ask_sum
  have hn1 : ((d.n1 : ℕ) : ℝ) = (d.i : ℝ) * d.g0 := by simp [Data.n1]
  have hn1pos : (0 : ℝ) < d.n1 := by rw [hn1]; positivity
  have hdel : (0 : ℝ) ≤ d.del := Nat.cast_nonneg _
  have hla := d.la_part hd h hH1 (d.wx x) hf
  have hsg := d.sg_part hd h hI2be (d.wx x) hf
  have h0 := d.logHeight_section_bound hd h hF1d (d.wx x) hf
  obtain ⟨-, -, hind3, hind4⟩ := d.h_ind hd h hI2be
  have hta1 : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1) ∧ d.ta1 c ≠ 0 :=
    fun c => ⟨hd.firstSectionMem c, hd.firstSectionNeZero c⟩
  have hta2 : ∀ c, d.ta2 c ∈ 𝒜 c d.G2 ∧ d.ta2 c ≠ 0 := fun c => ⟨hd.secondSectionMem c, hd.secondSectionNeZero c⟩
  have hbdd1 := fun sg => hd.bdd sg _ d.ta1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  have hbdd2 := fun sg => hd.bdd sg _ d.ta2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  have hint1 := fun c sg => (d.int_Nsg hd h hI2be c sg).1 ((2 : ℕ) • d.G1) (d.ta1 c) (by simp)
    (hd.firstSectionMem c) (hd.firstSectionNeZero c)
  have hint2 := fun c sg => (d.int_Nsg hd h hI2be c sg).1 d.G2 (d.ta2 c) (by simp)
    (hd.secondSectionMem c) (hd.secondSectionNeZero c)
  have h41 := (d.h_four hd h _ d.ta1 hta1 hd.ordDoubleFirstSection_nonneg hbdd1 hint1).1
  have h42 := (d.h_four hd h _ d.ta2 hta2 hd.ordSecondSectionNonneg hbdd2 hint2).1
  obtain ⟨-, -, hsup1, hsup2⟩ := hSup
  have m1 := mul_le_mul_of_nonneg_left hsup1 hdel
  have m2 := mul_le_mul_of_nonneg_left hsup2 hdel
  refine ⟨?_, ?_, ?_⟩
  · have e1 : d.Hgt h d.wL (d.wx x) = (∑ᶠ la, d.NlaG h d.wL (d.wx x) la * logNorm la) /
        (Module.finrank ℚ K : ℝ) + meanK (d.Nsg d.wL (d.wx x)) + d.h0f h d.wL (d.wx x) := rfl
    have e2 : d.HgtMM h (d.wx x) = (∑ᶠ la, d.NlaMM h (d.wx x) la * logNorm la) /
        (Module.finrank ℚ K : ℝ) + meanK (d.NsgMM (d.wx x)) + d.mahlerMeasureHeight h (d.wx x) := rfl
    have e3 : d.Hgt h (d.n1 • d.wde) d.et = (∑ᶠ la, d.NlaG h (d.n1 • d.wde) d.et la * logNorm la) /
        (Module.finrank ℚ K : ℝ) + meanK (d.Nsg (d.n1 • d.wde) d.et) + d.h0f h (d.n1 • d.wde) d.et := rfl
    have hla' := div_le_div_of_nonneg_right hla hK.le
    rw [add_div, add_div, mul_div_assoc, mul_div_assoc] at hla'
    have eH : d.cc * d.g0 * (d.Hgt h (d.n1 • d.wde) d.et / d.n1) =
        d.cc / d.i * d.Hgt h (d.n1 • d.wde) d.et := by
      rw [hn1]; field_simp
    have eA : d.D * d.cc * d.g0 * ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1) *
        (Real.log (d.N + 1 : ℕ) + 1 / 2) =
        d.D * (Real.log (d.N + 1 : ℕ) + 1 / 2) * (d.cc / d.i) * (d.aG h (d.n1 • d.wde) d.et : ℝ) := by
      rw [hn1]; field_simp
    rw [e1, e2, eH, eA, e3]
    nlinarith [hla', hsg, h0]
  · have hd3 := hind3 x hx
    have eq : d.Hgt h (d.n1 • d.wde) d.et / d.n1 =
        d.Hgt h d.wL (d.wx x) - d.Hgt h ((2 : ℕ) • d.G1) d.ta1 / 2 := by
      rw [div_eq_iff hn1pos.ne']
      linarith
    rw [eq]
    linarith [h41, m1]
  · have hd4 := hind4 x ta' hx hta'
    linarith [h42, m2]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
