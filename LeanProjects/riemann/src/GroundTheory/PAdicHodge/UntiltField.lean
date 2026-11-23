import Mathlib
import GroundTheory.PAdicHodge.TiltAlgebra
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p

variable (K C p) in

def integerTilt (N : IntermediateField K♭ C♭) : Subring 𝒪C♭ :=
  N.toSubfield.toSubring.comap (algebraMap 𝒪C♭ C♭)

theorem mem_integerTilt (N : IntermediateField K♭ C♭) {a : 𝒪C♭} : a ∈ integerTilt K C p N ↔ algebraMap 𝒪C♭ C♭ a ∈ N :=
  Iff.rfl

variable (K C p) in

def untiltInteger (N : IntermediateField K♭ C♭) : Subring (normInteger C) :=
  (RingHom.comp θ (WittVector.map (integerTilt K C p N).subtype)).range

variable (K C p) in

def untiltField (N : IntermediateField K♭ C♭) : IntermediateField K C :=
  IntermediateField.adjoin K ((↑) '' (untiltInteger K C p N : Set (normInteger C)))

theorem untilt_mem_untiltInteger {N : IntermediateField K♭ C♭} {a : 𝒪C♭} (ha : a ∈ integerTilt K C p N) :
    PreTilt.untilt a ∈ untiltInteger K C p N :=
  ⟨WittVector.teichmuller p ⟨a, ha⟩, by
    rw [RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]
    rfl⟩

theorem coe_mem_untiltField {N : IntermediateField K♭ C♭} {z : normInteger C} (hz : z ∈ untiltInteger K C p N) :
    (z : C) ∈ untiltField K C p N :=
  IntermediateField.subset_adjoin _ _ ⟨z, hz, rfl⟩

theorem tiltSharp_mem_untiltField {N : IntermediateField K♭ C♭} {z : C♭} (hz : z ∈ N) : tiltSharp C p z ∈ untiltField K C p N := by
  have key : ∀ y : C♭, y ∈ N → ‖y‖ ≤ 1 → tiltSharp C p y ∈ untiltField K C p N := by
    intro y hy hy1
    obtain ⟨a, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hy1
    rw [tiltSharp_algebraMap]
    exact coe_mem_untiltField (untilt_mem_untiltInteger ((mem_integerTilt N).2 hy))
  rcases le_or_gt ‖z‖ 1 with h | h
  · exact key z hz h
  · have h0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at h; linarith
    have := key z⁻¹ (inv_mem hz) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h.le)
    rw [map_inv₀] at this
    simpa using inv_mem this

section Perfect

theorem frobeniusEquiv_symm_mem_integerTilt {N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N]
    {a : 𝒪C♭} (ha : a ∈ integerTilt K C p N) :
    (frobeniusEquiv 𝒪C♭ p).symm a ∈ integerTilt K C p N := by
  have : PerfectField K♭ := PerfectRing.toPerfectField K♭ p
  have : PerfectField N := Algebra.IsAlgebraic.perfectField (K := K♭)
  have : CharP N p := charP_of_injective_algebraMap (algebraMap K♭ N).injective p
  have : PerfectRing N p := PerfectField.toPerfectRing p
  set y : N := (frobeniusEquiv N p).symm ⟨algebraMap 𝒪C♭ C♭ a, ha⟩
  have hy : (y : C♭) ^ p = algebraMap 𝒪C♭ C♭ a := by
    have := frobeniusEquiv_symm_pow_p (R := N) p ⟨algebraMap 𝒪C♭ C♭ a, ha⟩
    exact congrArg Subtype.val this
  have ha' : (algebraMap 𝒪C♭ C♭ ((frobeniusEquiv 𝒪C♭ p).symm a)) ^ p = algebraMap 𝒪C♭ C♭ a := by
    rw [← map_pow, frobeniusEquiv_symm_pow_p]
  have : algebraMap 𝒪C♭ C♭ ((frobeniusEquiv 𝒪C♭ p).symm a) = y :=
    frobenius_inj C♭ p (by simp only [frobenius_def]; rw [ha', hy])
  rw [mem_integerTilt, this]
  exact y.2

instance perfectRing_integerTilt (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    PerfectRing (integerTilt K C p N) p :=
  PerfectRing.ofSurjective (integerTilt K C p N) p fun a =>
    ⟨⟨(frobeniusEquiv 𝒪C♭ p).symm a, frobeniusEquiv_symm_mem_integerTilt a.2⟩,
      Subtype.ext (by
        change ((frobeniusEquiv 𝒪C♭ p).symm (a : 𝒪C♭)) ^ p = a
        exact frobeniusEquiv_symm_pow_p (R := 𝒪C♭) p _)⟩

theorem exists_eq_untilt_add_p_mul {N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N]
    {z : normInteger C} (hz : z ∈ untiltInteger K C p N) :
    ∃ a ∈ integerTilt K C p N, ∃ z' ∈ untiltInteger K C p N,
      z = PreTilt.untilt a + (p : normInteger C) * z' := by
  obtain ⟨u, rfl⟩ := hz
  set a0 : integerTilt K C p N := u.coeff 0
  have hmem : u - WittVector.teichmuller p a0 ∈ Ideal.span {(p : WittVector p (integerTilt K C p N))} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    have h := map_sub (WittVector.constantCoeff (p := p) (R := integerTilt K C p N)) u
      (WittVector.teichmuller p a0)
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h
    rw [h, sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨a0, a0.2, _, ⟨v, rfl⟩, ?_⟩
  have hu : u = WittVector.teichmuller p a0 + v * p := by rw [hv]; ring
  conv_lhs => rw [hu]
  rw [RingHom.comp_apply, map_add, map_mul, map_natCast, map_add, map_mul, map_natCast,
    WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller, RingHom.comp_apply, mul_comm]
  rfl

theorem exists_untilt_sum_eq {N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N] {ι : Type*}
    (s : Finset ι) (a : ι → integerTilt K C p N) :
    ∃ z ∈ untiltInteger K C p N, PreTilt.untilt (∑ i ∈ s, (a i : 𝒪C♭)) =
      ∑ i ∈ s, PreTilt.untilt (a i : 𝒪C♭) + (p : normInteger C) * z := by
  set x : WittVector p (integerTilt K C p N) :=
    WittVector.teichmuller p (∑ i ∈ s, a i) - ∑ i ∈ s, WittVector.teichmuller p (a i)
  have hmem : x ∈ Ideal.span {(p : WittVector p (integerTilt K C p N))} := by
    have hs : (∑ i ∈ s, WittVector.teichmuller p (a i)).coeff 0 = ∑ i ∈ s, a i := by
      have := map_sum (WittVector.constantCoeff (p := p) (R := integerTilt K C p N))
        (fun i => WittVector.teichmuller p (a i)) s
      simpa only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] using this
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    show (WittVector.teichmuller p (∑ i ∈ s, a i) -
      ∑ i ∈ s, WittVector.teichmuller p (a i)).coeff 0 = 0
    have h := map_sub (WittVector.constantCoeff (p := p) (R := integerTilt K C p N))
      (WittVector.teichmuller p (∑ i ∈ s, a i)) (∑ i ∈ s, WittVector.teichmuller p (a i))
    simp only [WittVector.constantCoeff_apply] at h
    rw [h, hs, WittVector.teichmuller_coeff_zero, sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨_, ⟨v, rfl⟩, ?_⟩
  have hx : WittVector.teichmuller p (∑ i ∈ s, a i) =
      ∑ i ∈ s, WittVector.teichmuller p (a i) + v * p := by rw [hv]; ring
  have := congrArg (RingHom.comp θ (WittVector.map (integerTilt K C p N).subtype)) hx
  simp only [RingHom.comp_apply, map_add, map_sum, map_mul, map_natCast,
    WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller, map_sum] at this
  rw [mul_comm] at this
  convert this using 2 <;> rfl

end Perfect

theorem integerTilt_mono {N N' : IntermediateField K♭ C♭} (h : N ≤ N') :
    integerTilt K C p N ≤ integerTilt K C p N' :=
  fun _ ha => h ha

theorem untiltInteger_mono {N N' : IntermediateField K♭ C♭} (h : N ≤ N') :
    untiltInteger K C p N ≤ untiltInteger K C p N' := by
  rintro _ ⟨u, rfl⟩
  refine ⟨WittVector.map (Subring.inclusion (integerTilt_mono h)) u, ?_⟩
  simp only [RingHom.comp_apply]
  congr 1

theorem untiltField_mono {N N' : IntermediateField K♭ C♭} (h : N ≤ N') :
    untiltField K C p N ≤ untiltField K C p N' :=
  IntermediateField.adjoin.mono _ _ _ (Set.image_mono (untiltInteger_mono h))

end GroundTheory.PAdicHodge
