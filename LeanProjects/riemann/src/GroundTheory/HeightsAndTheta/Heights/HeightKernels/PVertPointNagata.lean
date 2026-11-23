import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointNagata
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointMultChart
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace VerticalPointNagata

variable {T : Type} [Fintype T]

abbrev comp (n : ℕ) (f : MRing (fun _ : Unit => T)) : MRing (fun _ : Unit => T) :=
  weightedHomogeneousComponent (Inter.LocRingPow.multiDegWeight (fun _ : Unit => T)) (fun _ => n) f

theorem isMultiHomog_comp (n : ℕ) (f : MRing (fun _ : Unit => T)) :
    IsMultiHomog (comp n f) (fun _ => n) :=
  Inter.LocRingPow.isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

omit [Fintype T] in

theorem exists_comp_not_mem {J : Ideal (MRing (fun _ : Unit => T))} {f : MRing (fun _ : Unit => T)}
    (hf : f ∉ J) : ∃ n, comp n f ∉ J := by
  obtain ⟨D, hD⟩ := Inter.LocRingPow.exists_component_not_mem hf
  exact ⟨D (), hD⟩

theorem comp_mem {J : Ideal (MRing (fun _ : Unit => T))} (hJ : IsMultiHomogIdeal J)
    {f : MRing (fun _ : Unit => T)} (hf : f ∈ J) (n : ℕ) : comp n f ∈ J :=
  Inter.LocRingPow.component_mem hJ hf _

omit [Fintype T] in

theorem aeval_eq_eval₂ {S : Type*} [CommRing S] [Algebra ℤ S] (v : (Σ _ : Unit, T) → S)
    (f : MRing (fun _ : Unit => T)) : aeval v f = eval₂ (Int.castRingHom S) v f := by
  rw [aeval_def, show algebraMap ℤ S = Int.castRingHom S from RingHom.ext_int _ _]

theorem aeval_C_mul_X' {S : Type*} [CommRing S] [Algebra ℤ S] [Algebra ℤ (Polynomial S)] (r : (Σ _ : Unit, T) → S)
    (f : MRing (fun _ : Unit => T)) (d : ℕ) (hf : IsMultiHomog f (fun _ => d)) :
    (aeval (fun p => Polynomial.C (r p) * Polynomial.X) f : Polynomial S) =
      Polynomial.C (aeval r f) * Polynomial.X ^ d := by
  rw [aeval_eq_eval₂, aeval_eq_eval₂, VerticalPointMultiplicityChart.aeval_C_mul_X r f d hf]

theorem coeff_aeval {S : Type*} [CommRing S] [Algebra ℤ S] [Algebra ℤ (Polynomial S)] (r : (Σ _ : Unit, T) → S) (f : MRing (fun _ : Unit => T))
    (n : ℕ) :
    (aeval (fun p => Polynomial.C (r p) * Polynomial.X) f : Polynomial S).coeff n = aeval r (comp n f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    have hu : IsMultiHomog (monomial u c : MRing (fun _ : Unit => T)) (fun _ => ∑ i, u ⟨(), i⟩) := by
      intro m hm k
      have := Finset.mem_singleton.mp (support_monomial_subset hm)
      subst this
      rfl
    rw [aeval_C_mul_X' r _ _ hu, Polynomial.coeff_C_mul_X_pow]
    have hw := Inter.LocRingPow.isMultiHomog_iff.mp hu
    by_cases h : n = ∑ i, u ⟨(), i⟩
    · rw [if_pos h, comp, h, hw.weightedHomogeneousComponent_same]
    · rw [if_neg h, comp, hw.weightedHomogeneousComponent_ne _ (fun e => h (congrFun e ())), map_zero]
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq, comp, comp, comp, map_add, map_add]

end VerticalPointNagata

open VerticalPointNagata in

theorem VertPointNagata.proof (hCh : VertPointChart.Statement) : VertPointNagata.Statement := by
  intro T _ K' _ _ y s hP hs hsP W hW t ht _ _ a b hb hab
  classical

  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hPh : IsMultiHomogIdeal (mCoordIdeal y) := hP.2.1.2.1
  have hWh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hW.1
  have hformP : ∀ (g : MRing (fun _ : Unit => T)) (d : ℕ), IsMultiHomog g (fun _ => d) →
      g ∈ mCoordIdeal y → aeval y g = 0 := by
    intro g d hg hgP
    have h0 : mConeMap y g = 0 := hgP
    rw [LowerBoundFree.mConeMap_of_isMultiHomog y hg] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact MvPolynomial.C_eq_zero.mp h
    · exact absurd h (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero _))

  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    apply ht
    apply hPW
    refine LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y
      ((VerticalPointResidue.isMultiHomog_iff (n := 1)).mpr (VerticalPointResidue.isWH_X t)) ?_
    simp [h0]

  set m := curvePtIdeal y W with hm
  let Bm := Localization.AtPrime m
  let r : (Σ _ : Unit, T) → Bm := fun p =>
    IsLocalization.mk' Bm (a p.2) (⟨b p.2, hb p.2⟩ : m.primeCompl)
  obtain ⟨ι, hι, hιalg, hιmk, hιaeval⟩ : ∃ ι : Bm →+* K', Function.Injective ι ∧
      (∀ β : curveRing y, ι (algebraMap _ Bm β) = β) ∧
      (∀ (α : curveRing y) (β : m.primeCompl), (α : K') = (β : K') * ι (IsLocalization.mk' Bm α β)) ∧
      ∀ g : MRing (fun _ : Unit => T), ι (aeval r g) = aeval (fun p => y p / y ⟨(), t⟩) g := by
    have hu : ∀ u : m.primeCompl, IsUnit ((curveRing y).subtype u) := by
      intro u
      refine isUnit_iff_ne_zero.mpr fun h => u.2 ?_
      have : (u : curveRing y) = 0 := Subtype.ext h
      rw [this]
      exact zero_mem _
    refine ⟨IsLocalization.lift hu, (IsLocalization.lift_injective_iff (hg := hu)).mpr fun x z =>
      ⟨fun h => by rw [IsLocalization.injective Bm (Ideal.primeCompl_le_nonZeroDivisors m) h],
        fun h => by rw [Subtype.ext h]⟩, fun β => IsLocalization.lift_eq hu β,
      fun α β => by
        have := (IsLocalization.lift_mk'_spec (S := Bm) hu α
          (IsLocalization.lift hu (IsLocalization.mk' Bm α β)) β).mp rfl
        exact this, fun g => ?_⟩
    rw [aeval_eq_eval₂, aeval_eq_eval₂, MvPolynomial.eval₂_comp_left,
      show (IsLocalization.lift hu).comp (Int.castRingHom Bm) = Int.castRingHom K' from RingHom.ext_int _ _]
    congr 1
    funext p
    show IsLocalization.lift hu (IsLocalization.mk' Bm (a p.2) (⟨b p.2, hb p.2⟩ : m.primeCompl)) = _
    rw [IsLocalization.lift_mk'_spec]
    exact (hab p.2).symm
  have hιev : ∀ (g : MRing (fun _ : Unit => T)) (d : ℕ), IsMultiHomog g (fun _ => d) →
      ι (aeval r g) = aeval y g * (y ⟨(), t⟩ ^ d)⁻¹ := fun g d hg => by
    rw [hιaeval, VerticalPointResidue.aeval_div y t g d hg]

  have hcrit : ∀ (g : MRing (fun _ : Unit => T)) (d : ℕ), IsMultiHomog g (fun _ => d) →
      (g ∈ W ↔ aeval r g ∈ IsLocalRing.maximalIdeal Bm) := by
    intro g d hg
    have h3 := (hCh T K' y s hP hs hsP W hW t ht).2.2 d g hg
    have hytd : y ⟨(), t⟩ ^ d ≠ 0 := pow_ne_zero _ hyt
    constructor
    · intro hgW
      obtain ⟨α, β, hα, hβ, he⟩ := h3.mp hgW
      have : aeval r g = IsLocalization.mk' Bm α (⟨β, hβ⟩ : m.primeCompl) := by
        apply hι
        have h1 := hιmk α ⟨β, hβ⟩
        have hβ0 : (β : K') ≠ 0 := fun h => hβ (by rw [show β = 0 from Subtype.ext h]; exact zero_mem _)
        rw [hιev g d hg]
        apply mul_left_cancel₀ hβ0
        rw [← h1, ← mul_assoc, he, mul_assoc, mul_inv_cancel₀ hytd, mul_one]
      rw [this]
      exact (IsLocalization.AtPrime.mk'_mem_maximal_iff Bm m α _).mpr hα
    · intro hg'
      obtain ⟨⟨α, β⟩, hαβ⟩ := IsLocalization.mk'_surjective m.primeCompl (aeval r g)
      have hα : α ∈ m := by
        rw [← hαβ] at hg'
        exact (IsLocalization.AtPrime.mk'_mem_maximal_iff Bm m α β).mp hg'
      refine h3.mpr ⟨α, β, hα, β.2, ?_⟩
      have h1 := hιmk α β
      change IsLocalization.mk' Bm α β = aeval r g at hαβ
      rw [hαβ, hιev g d hg] at h1
      rw [h1, mul_assoc, inv_mul_cancel_right₀ hytd]

  let ψ : MRing (fun _ : Unit => T) →ₐ[ℤ] Polynomial Bm :=
    aeval (fun p : (Σ _ : Unit, T) => Polynomial.C (r p) * Polynomial.X)
  let M := (IsLocalRing.maximalIdeal Bm).map (Polynomial.C : Bm →+* Polynomial Bm)
  let N := nagataRing Bm
  have hψcoeff : ∀ f n, (ψ f).coeff n = aeval r (comp n f) := fun f n => coeff_aeval r f n
  have hψform : ∀ (G : MRing (fun _ : Unit => T)) (d : ℕ), IsMultiHomog G (fun _ => d) →
      ψ G = Polynomial.C (aeval r G) * Polynomial.X ^ d := fun G d hG => aeval_C_mul_X' r G d hG
  have hrt : r ⟨(), t⟩ = 1 := by
    apply hι
    have h1 := hιaeval (X ⟨(), t⟩)
    rw [aeval_X, aeval_X] at h1
    rw [h1, map_one, div_self hyt]
  have hψX : ψ (X ⟨(), t⟩) = Polynomial.X := by
    rw [hψform _ 1 ((VerticalPointResidue.isMultiHomog_iff (n := 1)).mpr (VerticalPointResidue.isWH_X t)),
      aeval_X, hrt, map_one, one_mul, pow_one]
  have hψW : ∀ h ∈ W, ψ h ∈ M := by
    intro h hh
    rw [Ideal.mem_map_C_iff]
    intro n
    rw [hψcoeff]
    exact (hcrit _ _ (isMultiHomog_comp n h)).mp (comp_mem hWh hh n)
  have hψnot : ∀ g ∉ W, ψ g ∉ M := by
    intro g hg hM
    obtain ⟨n, hn⟩ := exists_comp_not_mem hg
    rw [Ideal.mem_map_C_iff] at hM
    have := hM n
    rw [hψcoeff] at this
    exact hn ((hcrit _ _ (isMultiHomog_comp n g)).mpr this)
  have hψP : ∀ f, ψ f = 0 ↔ f ∈ mCoordIdeal y := by
    intro f
    constructor
    · intro h0
      by_contra hf
      obtain ⟨n, hn⟩ := exists_comp_not_mem hf
      have h1 := congrArg (fun q => Polynomial.coeff q n) h0
      simp only [Polynomial.coeff_zero] at h1
      rw [hψcoeff] at h1
      have h2 := congrArg ι h1
      rw [hιev _ _ (isMultiHomog_comp n f), map_zero] at h2
      refine hn (LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_comp n f) ?_)
      exact (mul_eq_zero.mp h2).resolve_right (inv_ne_zero (pow_ne_zero _ hyt))
    · intro hf
      ext n
      rw [hψcoeff, Polynomial.coeff_zero]
      apply hι
      rw [hιev _ _ (isMultiHomog_comp n f), hformP _ _ (isMultiHomog_comp n f) (comp_mem hPh hf n),
        zero_mul, map_zero]

  have hunit : ∀ g : W.primeCompl,
      IsUnit ((algebraMap (Polynomial Bm) N).comp ψ.toRingHom g) := fun g =>
    IsLocalization.map_units N (⟨ψ g, hψnot g g.2⟩ : M.primeCompl)
  let Φ : Localization.AtPrime W →+* N := IsLocalization.lift hunit
  have hΦ : ∀ f, Φ (algebraMap _ _ f) = algebraMap (Polynomial Bm) N (ψ f) := fun f =>
    IsLocalization.lift_eq hunit f
  have hΦmk : ∀ (f : MRing (fun _ : Unit => T)) (g : W.primeCompl) (v : N),
      Φ (IsLocalization.mk' _ f g) = v ↔ algebraMap (Polynomial Bm) N (ψ f) =
        algebraMap (Polynomial Bm) N (ψ g) * v := fun f g v =>
    IsLocalization.lift_mk'_spec hunit f v g
  have hinjN : Function.Injective (algebraMap (Polynomial Bm) N) :=
    IsLocalization.injective (R := Polynomial Bm) (M := M.primeCompl) N (Ideal.primeCompl_le_nonZeroDivisors M)
  refine ⟨Φ, ?_, ?_, hΦ⟩
  ·
    have hB : ∀ β : curveRing y, ∃ (d : ℕ) (G : MRing (fun _ : Unit => T)), IsMultiHomog G (fun _ => d) ∧
        aeval r G = algebraMap _ Bm β := by
      intro β
      have hβ := mem_curveRing.mp β.2 (fun _ => t) (fun _ => hyt)
      rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at hβ
      obtain ⟨f, hf⟩ := hβ
      obtain ⟨d, G, hG, hGf⟩ := VerticalPointResidue.exists_homog
        (aeval (fun p : (Σ _ : Unit, T) => y p / y ⟨(), t⟩)).toRingHom t
        (by rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]; exact div_self hyt) f
      refine ⟨d, G, hG, hι ?_⟩
      rw [hιaeval, hιalg]
      exact hGf.trans hf
    have hC : ∀ c : Bm, ∃ x, Φ x = algebraMap (Polynomial Bm) N (Polynomial.C c) := by
      intro c
      obtain ⟨⟨β, γ⟩, hc⟩ := IsLocalization.mk'_surjective m.primeCompl c
      change IsLocalization.mk' Bm β γ = c at hc
      subst hc
      obtain ⟨d1, G1, hG1, e1⟩ := hB β
      obtain ⟨d2, G2, hG2, e2⟩ := hB γ
      have hG2W : G2 ∉ W := by
        rw [hcrit _ _ hG2, e2, IsLocalization.AtPrime.to_map_mem_maximal_iff Bm m]
        exact γ.2
      have hden : G2 * X ⟨(), t⟩ ^ d1 ∈ W.primeCompl := fun h =>
        (Ideal.IsPrime.mem_or_mem ‹_› h).elim hG2W fun h' => ht (Ideal.IsPrime.mem_of_pow_mem ‹_› _ h')
      have hψeq : ψ (G1 * X ⟨(), t⟩ ^ d2) =
          ψ (G2 * X ⟨(), t⟩ ^ d1) * Polynomial.C (IsLocalization.mk' Bm β γ) := by
        rw [map_mul, map_mul, map_pow, map_pow, hψform G1 d1 hG1, hψform G2 d2 hG2, hψX, e1, e2,
          ← IsLocalization.mk'_spec' Bm β γ, map_mul]
        ring
      exact ⟨IsLocalization.mk' (Localization.AtPrime W) (G1 * X ⟨(), t⟩ ^ d2) ⟨_, hden⟩,
        (hΦmk _ _ _).mpr (by rw [hψeq, map_mul])⟩
    have hXim : ∃ x, Φ x = algebraMap (Polynomial Bm) N Polynomial.X :=
      ⟨algebraMap (MRing (fun _ : Unit => T)) (Localization.AtPrime W) (X ⟨(), t⟩),
        (hΦ (X ⟨(), t⟩)).trans (congrArg _ hψX)⟩
    have hIm : ∀ q : Polynomial Bm, ∃ x, Φ x = algebraMap (Polynomial Bm) N q := by
      intro q
      refine Polynomial.induction_on (motive := fun q => ∃ x, Φ x = algebraMap (Polynomial Bm) N q) q hC
        (fun p q hp hq => ?_) (fun n c ih => ?_)
      · obtain ⟨x, hx⟩ := hp
        obtain ⟨x', hx'⟩ := hq
        exact ⟨x + x', by rw [map_add, hx, hx', map_add]⟩
      · obtain ⟨x, hx⟩ := ih
        obtain ⟨x', hx'⟩ := hXim
        exact ⟨x * x', by rw [map_mul, hx, hx', ← map_mul, pow_succ, mul_assoc]⟩
    have hΦmax : ∀ x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime W),
        Φ x ∈ M.map (algebraMap (Polynomial Bm) N) := by
      intro x hx
      rw [← Localization.AtPrime.map_eq_maximalIdeal] at hx
      have hle : (W.map (algebraMap _ (Localization.AtPrime W))).map Φ ≤
          M.map (algebraMap (Polynomial Bm) N) := by
        rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
        intro h hh
        rw [Ideal.mem_comap, RingHom.comp_apply, hΦ]
        exact Ideal.mem_map_of_mem _ (hψW h hh)
      exact hle (Ideal.mem_map_of_mem Φ hx)
    intro z
    obtain ⟨⟨q, q'⟩, hz⟩ := IsLocalization.mk'_surjective M.primeCompl z
    change IsLocalization.mk' N q q' = z at hz
    subst hz
    obtain ⟨x1, h1⟩ := hIm q
    obtain ⟨x2, h2⟩ := hIm q'
    have hx2 : IsUnit x2 := by
      by_contra hu
      have hmem := hΦmax x2 ((IsLocalRing.mem_maximalIdeal _).mpr hu)
      rw [h2, Localization.AtPrime.map_eq_maximalIdeal,
        IsLocalization.AtPrime.to_map_mem_maximal_iff N M] at hmem
      exact q'.2 hmem
    obtain ⟨u, rfl⟩ := hx2
    refine ⟨x1 * ↑u⁻¹, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq, ← h1, ← h2, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
  ·
    ext x
    rw [RingHom.mem_ker]
    constructor
    · intro hx
      obtain ⟨⟨f, g⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
      have h1 := (hΦmk f g 0).mp hx
      rw [mul_zero, ← map_zero (algebraMap (Polynomial Bm) N)] at h1
      have hf : f ∈ mCoordIdeal y := (hψP f).mp (hinjN h1)
      change IsLocalization.mk' (Localization.AtPrime W) f g ∈ _
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hf)
    · intro hx
      have hle : (mCoordIdeal y).map (algebraMap _ (Localization.AtPrime W)) ≤ RingHom.ker Φ := by
        rw [Ideal.map_le_iff_le_comap]
        intro f hf
        rw [Ideal.mem_comap, RingHom.mem_ker, hΦ, (hψP f).mpr hf, map_zero]
      exact hle hx

end

end GroundTheory.Heights₂.Heights
