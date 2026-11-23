import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsClosedOfChartIdeal
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RingKrullDimLocRingEqOfMinimalPrime

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory IsLocalRing

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem ne_zero_of_span_eq_maximalIdeal {R : Type*} [CommRing R] [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) (v : Fin d → R) (hv : Ideal.span (Set.range v) = maximalIdeal R)
    (l : Fin d) : v l ≠ 0 := by
  intro h0
  have hfin : (Set.range v \ {0}).Finite := (Set.finite_range v).sdiff
  have hncard : (Set.range v \ {0}).ncard < d := by
    have h1 : (Set.range v \ {0}).ncard < (Set.range v).ncard :=
      Set.ncard_sdiff_singleton_lt_of_mem ⟨l, h0⟩ (Set.finite_range v)
    have h2 : (Set.range v).ncard ≤ d := by
      calc (Set.range v).ncard ≤ (Set.univ : Set (Fin d)).ncard := by
            rw [← Set.image_univ]; exact Set.ncard_image_le (Set.finite_univ)
        _ = d := by simp
    omega
  have hspan : Ideal.span (Set.range v \ {0}) = maximalIdeal R := by
    rw [Ideal.span_sdiff_singleton_zero, hv]
  have hle : (maximalIdeal R).spanFinrank ≤ (Set.range v \ {0}).ncard := by
    rw [← hspan]; exact Submodule.spanFinrank_span_le_ncard_of_finite hfin
  have hdim := ringKrullDim_le_spanFinrank_maximalIdeal R
  rw [hd] at hdim
  have : (d : WithBot ℕ∞) ≤ ((Set.range v \ {0}).ncard : WithBot ℕ∞) :=
    hdim.trans (by exact_mod_cast hle)
  have := (Nat.cast_le (α := WithBot ℕ∞)).mp this
  omega

theorem WData.exists_closed_off (w : WData P D hP) (Q : AffPres (w.π ≫ toSpecC hP)) (x : w.M) (hxV : x.1 ∈ Q.V)
    (𝔮 : Ideal (MvPolynomial (Fin Q.n) ℂ)) (h𝔮min : 𝔮 ∈ Q.K.minimalPrimes)
    (h𝔮x : 𝔮 ≤ ptIdeal (Q.coord x.1 hxV)) (G : MvPolynomial (Fin Q.n) ℂ)
    (hG : eval (Q.coord x.1 hxV) G ≠ 0) :
    ∃ x' : w.M, ∃ hx' : x'.1 ∈ Q.V,
      𝔮 ≤ ptIdeal (Q.coord x'.1 hx') ∧
        w.π.base x'.1 ∉ (projB P D hP : Set (projX P hP)) ∧ eval (Q.coord x'.1 hx') G ≠ 0 := by
  generalize hp : Q.coord x.1 hxV = p at h𝔮x hG
  have := w.regular x.1
  haveI hregL : IsRegularLocalRing (locRing Q.K p) := by
    rw [← hp]; exact (Q.isRegularLocalRing_stalk_iff x.1 hxV x.2).mp (w.regular x.1)
  haveI : IsDomain (locRing Q.K p) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  set d := (maximalIdeal (w.W.presheaf.stalk x.1)).spanFinrank with hdd
  have hd : ringKrullDim (w.W.presheaf.stalk x.1) = d :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal).symm
  obtain ⟨S, -, -⟩ := exists_sncData w.snc_Zb Q w.compEquiv d x.1 hxV x.2 hd
  rw [hp] at S
  have hdL : ringKrullDim (locRing Q.K p) = d := by
    rw [← hp, ← Q.ringKrullDim_stalk x.1 hxV x.2]; exact hd
  have hmax : Ideal.map (algebraMap _ (locRing Q.K p)) (ptIdeal p) = maximalIdeal (locRing Q.K p) := by
    subst hp
    rw [← Q.map_maximalIdeal_stalk x.1 hxV x.2]; exact map_ringEquiv_maximalIdeal _

  set 𝔮' := RingHom.ker (algebraMap (MvPolynomial (Fin Q.n) ℂ) (locRing Q.K p)) with h𝔮'
  have h𝔮'prime : 𝔮'.IsPrime := RingHom.ker_isPrime _
  have hK𝔮' : Q.K ≤ 𝔮' := by
    intro f hf
    rw [h𝔮', RingHom.mem_ker, IsScalarTower.algebraMap_apply (MvPolynomial (Fin Q.n) ℂ) (locPt p),
      Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hf)
  have h𝔮'p : 𝔮' ≤ ptIdeal p := by
    intro f hf
    by_contra hfp
    rw [h𝔮', RingHom.mem_ker, IsScalarTower.algebraMap_apply (MvPolynomial (Fin Q.n) ℂ) (locPt p),
      Ideal.Quotient.algebraMap_eq] at hf
    have hu : IsUnit (algebraMap (MvPolynomial (Fin Q.n) ℂ) (locPt p) f) :=
      IsLocalization.map_units (locPt p) (⟨f, hfp⟩ : (ptIdeal p).primeCompl)
    have := (hu.map (Ideal.Quotient.mk (Ideal.map (algebraMap _ (locPt p)) Q.K))).ne_zero
    exact this hf
  have h𝔮𝔮' : 𝔮 ≤ 𝔮' := by
    obtain ⟨Q', hQ'min, hQ'le⟩ := Ideal.exists_minimalPrimes_le hK𝔮'
    obtain ⟨q0, -, -, hu, -⟩ := regular_point_unique_minimalPrime Q.K p
    rw [hu 𝔮 h𝔮min h𝔮x, ← hu Q' hQ'min (hQ'le.trans h𝔮'p)]
    exact hQ'le
  have h𝔮prime : 𝔮.IsPrime := h𝔮min.1.1
  set F := S.h * ∏ l ∈ S.J, S.r l with hF
  have hFbd : F ∈ Q.bdIdeal w.Zb := S.mem_bd
  have hFq : F ∉ 𝔮 := by
    intro hmem
    rcases h𝔮prime.mem_or_mem hmem with hh | hprod
    · exact S.eval_h (by simpa [ptIdeal, RingHom.mem_ker] using h𝔮x hh)
    · haveI := h𝔮prime
      obtain ⟨l, -, hl⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
      have h0 : algebraMap _ (locRing Q.K p) (S.r l) = 0 := h𝔮𝔮' hl
      exact ne_zero_of_span_eq_maximalIdeal hdL (fun l => algebraMap _ (locRing Q.K p) (S.r l))
        (S.span_eq.trans hmax) l h0

  have hGq : G ∉ 𝔮 := fun hG𝔮 => hG (by simpa [ptIdeal, RingHom.mem_ker] using h𝔮x hG𝔮)
  have hFGq : F * G ∉ 𝔮 := fun hm => (h𝔮prime.mem_or_mem hm).elim hFq hGq
  obtain ⟨y, hy𝔮, hyFG⟩ : ∃ y : Fin Q.n → ℂ, (∀ f ∈ 𝔮, eval y f = 0) ∧ eval y (F * G) ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hFGq
    have : F * G ∈ vanishingIdeal ℂ (zeroLocus ℂ 𝔮) := by
      rw [mem_vanishingIdeal_iff]
      intro y hy
      exact hno y (fun f hf => by simpa using hy f hf)
    rwa [vanishingIdeal_zeroLocus_eq_radical, h𝔮prime.radical] at this
  obtain ⟨x'', ⟨hx''V, hcl, hco⟩, -⟩ :=
    Q.existsUnique_closed_coord y (fun f hf => hy𝔮 f (h𝔮min.1.2 hf))
  have hyF : eval y F ≠ 0 := fun h0 => hyFG (by rw [eval_mul, h0, zero_mul])
  have hyG : eval y G ≠ 0 := fun h0 => hyFG (by rw [eval_mul, h0, mul_zero])
  refine ⟨⟨x'', hcl⟩, hx''V, ?_, ?_, by rw [hco]; exact hyG⟩
  · intro f hf
    show f ∈ ptIdeal (Q.coord x'' hx''V)
    rw [hco, ptIdeal, RingHom.mem_ker]
    exact hy𝔮 f hf
  · intro hB
    have hsupp : x'' ∈ (w.Zb.support : Set w.W) := by
      rw [w.support_Zb]; exact hB
    have := (Q.zero_bdIdeal_iff w.Zb x'' hx''V hcl).mpr hsupp F hFbd
    rw [hco] at this
    exact hyF this

set_option backward.isDefEq.respectTransparency.types false in

theorem WData.ringKrullDim_stalk_off (w : WData P D hP) (e : ℕ)
    (hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval z h = 0) →
      ringKrullDim (chartLocRing P p z) = e)
    (y : w.M) (hy : w.π.base y.1 ∉ (projB P D hP : Set (projX P hP))) :
    ringKrullDim (w.W.presheaf.stalk y.1) = e := by
  have := w.lft
  have := w.isIso_off
  have hU : y.1 ∈ w.π ⁻¹ᵁ projBCompl P D hP := hy
  have hiso : IsIso (w.π.stalkMap y.1) := by
    have h := (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap w.π (projBCompl P D hP) ⟨y.1, hU⟩)
    haveI hoi : IsOpenImmersion (w.π ∣_ projBCompl P D hP) := IsOpenImmersion.of_isIso _
    have h2 : IsIso ((w.π ∣_ projBCompl P D hP).stalkMap ⟨y.1, hU⟩) := inferInstance
    exact h.mp h2
  rw [← ringKrullDim_eq_of_ringEquiv (asIso (w.π.stalkMap y.1)).commRingCatIsoToRingEquiv]
  have hcl : IsClosed ({w.π.base y.1} : Set (projX P hP)) :=
    (val_comp (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl (U := ⊤) (V := ⊤) (by simp) 0 y.1 trivial
      y.2).1
  obtain ⟨p, hp⟩ := chartOpen_cover hP (w.π.base y.1)
  obtain ⟨z, hz, -, ⟨ψ⟩⟩ := exists_closedPoint_stalk hP p _ hp hcl
  rw [ringKrullDim_eq_of_ringEquiv ψ]
  exact hdim p z hz

theorem WData.ringKrullDim_stalk (w : WData P D hP) (e : ℕ) (hD : IsMultiHomogIdeal D)
    (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q)
    (hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval z h = 0) →
      ringKrullDim (chartLocRing P p z) = e) :
    ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e := by

  have offB : ∀ y : w.M, w.π.base y.1 ∉ (projB P D hP : Set (projX P hP)) →
      ringKrullDim (w.W.presheaf.stalk y.1) = e :=
    w.ringKrullDim_stalk_off e hdim
  intro x
  obtain ⟨c, hc⟩ := w.cover x
  have hxV : x.1 ∈ (w.pres c.1 c.2).V := hc
  rw [(w.pres c.1 c.2).ringKrullDim_stalk x.1 hxV x.2]
  have := ((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x.1 hxV x.2).mp (w.regular x.1)
  obtain ⟨𝔮, h𝔮min, h𝔮x, -, -⟩ :=
    regular_point_unique_minimalPrime (w.pres c.1 c.2).K ((w.pres c.1 c.2).coord x.1 hxV)

  obtain ⟨x', hx'V, h𝔮x', hx'B, -⟩ :=
    w.exists_closed_off (w.pres c.1 c.2) x hxV 𝔮 h𝔮min h𝔮x 1 (by simp)
  have := ((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x'.1 hx'V x'.2).mp (w.regular x'.1)
  rw [ringKrullDim_locRing_eq_of_minimalPrime (w.pres c.1 c.2).K _ _ 𝔮 h𝔮min h𝔮x h𝔮x',
    ← (w.pres c.1 c.2).ringKrullDim_stalk x'.1 hx'V x'.2]
  exact offB x' hx'B

theorem WData.dim_coord (w : WData P D hP) {e : ℕ}
    (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e) (c : w.Idx) (x : w.M)
    (hx : x ∈ w.src c) : ringKrullDim (locRing (w.pres c.1 c.2).K (w.coord c x)) = e := by
  have h1 : w.coord c x = (w.pres c.1 c.2).coord x.1 hx := by
    unfold WData.coord
    exact dif_pos hx
  rw [h1, ← (w.pres c.1 c.2).ringKrullDim_stalk x.1 hx x.2]
  exact he x

end ReciprocityTheory.AnForm.R
