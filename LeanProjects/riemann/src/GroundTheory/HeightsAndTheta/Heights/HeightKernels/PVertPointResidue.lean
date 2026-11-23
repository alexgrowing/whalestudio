import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace VerticalPointResidue

variable {T : Type} [Fintype T]

theorem isMultiHomog_iff {g : MRing (fun _ : Unit => T)} {n : ℕ} :
    IsMultiHomog g (fun _ => n) ↔
      IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) g n := by
  constructor
  · intro h
    exact isWeightedHomogeneous_of_isMultiHomog h ()
  · intro h m hm k
    cases k
    exact (weight_blockWeight (ι := fun _ : Unit => T) () m).symm.trans (h (mem_support_iff.mp hm))

omit [Fintype T] in
theorem isWH_X' (i : Σ _ : Unit, T) :
    IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ())
      (X i : MRing (fun _ : Unit => T)) 1 := by
  have h := isWeightedHomogeneous_X ℤ (blockWeight (ι := fun _ : Unit => T) ()) i
  have e : blockWeight (ι := fun _ : Unit => T) () i = 1 := by simp [blockWeight]
  rwa [e] at h

omit [Fintype T] in
theorem isWH_X (c : T) :
    IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ())
      (X ⟨(), c⟩ : MRing (fun _ : Unit => T)) 1 :=
  isWH_X' ⟨(), c⟩

omit [Fintype T] in
theorem isWH_X_pow (c : T) (n : ℕ) :
    IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ())
      (X ⟨(), c⟩ ^ n : MRing (fun _ : Unit => T)) n := by
  have h := (isWH_X c).pow n
  simpa using h

omit [Fintype T] in
theorem isWH_sub {f g : MRing (fun _ : Unit => T)} {n : ℕ}
    (hf : IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) f n)
    (hg : IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) g n) :
    IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) (f - g) n := by
  have h := sub_mem ((mem_weightedHomogeneousSubmodule ℤ _ n f).mpr hf)
    ((mem_weightedHomogeneousSubmodule ℤ _ n g).mpr hg)
  exact (mem_weightedHomogeneousSubmodule ℤ _ n _).mp h

theorem exists_homog {S : Type*} [CommRing S] (χ : MRing (fun _ : Unit => T) →+* S) (c : T)
    (hχ : χ (X ⟨(), c⟩) = 1) (f : MRing (fun _ : Unit => T)) :
    ∃ (n : ℕ) (G : MRing (fun _ : Unit => T)), IsMultiHomog G (fun _ => n) ∧ χ G = χ f := by
  simp_rw [isMultiHomog_iff]
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, isWeightedHomogeneous_C _ _, rfl⟩
  | add p q hp hq =>
    obtain ⟨n₁, G₁, h₁, e₁⟩ := hp
    obtain ⟨n₂, G₂, h₂, e₂⟩ := hq
    refine ⟨n₁ + n₂, G₁ * X ⟨(), c⟩ ^ n₂ + G₂ * X ⟨(), c⟩ ^ n₁, ?_, ?_⟩
    · refine (h₁.mul (isWH_X_pow c n₂)).add ?_
      rw [add_comm n₁]
      exact h₂.mul (isWH_X_pow c n₁)
    · simp only [map_add, map_mul, map_pow, hχ, one_pow, mul_one, e₁, e₂]
  | mul_X p i hp =>
    obtain ⟨n, G, h, e⟩ := hp
    refine ⟨n + 1, G * X i, h.mul (isWH_X' i), ?_⟩
    rw [map_mul, map_mul, e]

theorem exists_homog_mem {S : Type*} [CommRing S] (χ : MRing (fun _ : Unit => T) →+* S) (c : T)
    (hχ : χ (X ⟨(), c⟩) = 1) {W : Ideal (MRing (fun _ : Unit => T))} (hW : IsMultiHomogIdeal W)
    {f : MRing (fun _ : Unit => T)} (hf : f ∈ W) :
    ∃ (n : ℕ) (G : MRing (fun _ : Unit => T)), G ∈ W ∧ IsMultiHomog G (fun _ => n) ∧ χ G = χ f := by
  obtain ⟨Sg, hSg, rfl⟩ := hW
  simp_rw [isMultiHomog_iff]
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hSg x hx
    exact ⟨a (), x, Ideal.subset_span hx, isWeightedHomogeneous_of_isMultiHomog ha (), rfl⟩
  | zero => exact ⟨0, 0, zero_mem _, fun d hd => absurd rfl hd, rfl⟩
  | add x z _ _ hx hz =>
    obtain ⟨n₁, G₁, hG₁, h₁, e₁⟩ := hx
    obtain ⟨n₂, G₂, hG₂, h₂, e₂⟩ := hz
    refine ⟨n₁ + n₂, G₁ * X ⟨(), c⟩ ^ n₂ + G₂ * X ⟨(), c⟩ ^ n₁,
      add_mem (Ideal.mul_mem_right _ _ hG₁) (Ideal.mul_mem_right _ _ hG₂), ?_, ?_⟩
    · refine (h₁.mul (isWH_X_pow c n₂)).add ?_
      rw [add_comm n₁]
      exact h₂.mul (isWH_X_pow c n₁)
    · simp only [map_add, map_mul, map_pow, hχ, one_pow, mul_one, e₁, e₂]
  | smul a x _ hx =>
    obtain ⟨n, G, hG, h, e⟩ := hx
    obtain ⟨m, A, hA, eA⟩ := exists_homog χ c hχ a
    refine ⟨m + n, A * G, Ideal.mul_mem_left _ _ hG, (isMultiHomog_iff.mp hA).mul h, ?_⟩
    rw [smul_eq_mul, map_mul, map_mul, eA, e]

theorem aeval_div {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K') (c : T)
    (G : MRing (fun _ : Unit => T)) (n : ℕ) (hG : IsMultiHomog G (fun _ => n)) :
    aeval (fun p => y p / y ⟨(), c⟩) G = aeval y G * (y ⟨(), c⟩ ^ n)⁻¹ := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : ∑ i, m ⟨(), i⟩ = n := hG m hm ()
  rw [mul_assoc]
  congr 1
  rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]),
    Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
  have hden : ∏ p : (Σ _ : Unit, T), y ⟨(), c⟩ ^ m p = y ⟨(), c⟩ ^ n := by
    rw [Finset.prod_pow_eq_pow_sum, Fintype.sum_sigma, Fintype.sum_unique]
    rw [← hmd]
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, hden, div_eq_mul_inv]

end VerticalPointResidue

open VerticalPointResidue in

theorem VertPointResidue.proof (hC : CurveCharts.Statement) : VertPointResidue.Statement := by
  intro T _ K' _ _ y s hP hs hsP W hW
  classical
  have hP' := hP
  obtain ⟨-, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP'
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have := hWp
  have := hPp
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hWmin.1.2
  have hWmh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hWmin
  have hdim : ringKrullDim (MRing (fun _ : Unit => T) ⧸ W) =
      ((0 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
    have h1 := dim_quot_minimal_add_one (mCoordIdeal y) W s hsP hWmin
    rw [hPdim] at h1
    exact withBot_eq_of_add_one
      (by rw [h1, show 1 + Fintype.card Unit = 0 + Fintype.card Unit + 1 by omega])
  have hvert : ¬ IsHorizontal W :=
    IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full Unit (fun _ => T) _ s _ hP hs hsP W ⟨hWmin, hWrel⟩
  have : Fact (charOf W).Prime := ⟨charOf_prime hWp hvert⟩
  have hp : (C ((charOf W : ℕ) : ℤ) : MRing (fun _ : Unit => T)) ∈ W := by
    have hgen := Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing (fun _ : Unit => T)))
    have : ((charOf W : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MRing (fun _ : Unit => T)) := by
      unfold charOf
      rw [Int.natCast_natAbs]
      rcases abs_choice (Submodule.IsPrincipal.generator
        (W.comap (C : ℤ →+* MRing (fun _ : Unit => T)))) with h | h <;> rw [h]
      · exact hgen
      · exact neg_mem hgen
    exact Ideal.mem_comap.mp this
  have hcW : ∀ k, (X ⟨k, (hWrel k).choose⟩ : MRing (fun _ : Unit => T)) ∉ W :=
    fun k => (hWrel k).choose_spec
  set J := W ⊔ Ideal.span (Set.range fun k => (X ⟨k, (hWrel k).choose⟩ : MRing (fun _ : Unit => T)) - 1)
    with hJ
  have hgeo : ∀ b, geoNum 0 W b = ((Module.length ℤ (MRing (fun _ : Unit => T) ⧸ J)).toNat : ℤ) := by
    intro b
    rw [geoNum, dif_pos hWrel]
  obtain ⟨hF, hFin, hcard⟩ := Inter.regularityLocalResidue_holds.chart_field_card hWmh hcW hdim (charOf W) hp
  letI : Field (MRing (fun _ : Unit => T) ⧸ J) := hF.toField
  set c : T := (hWrel ()).choose with hc
  have hXc : (X ⟨(), c⟩ : MRing (fun _ : Unit => T)) ∉ W := hcW ()
  have hXc1 : (X ⟨(), c⟩ : MRing (fun _ : Unit => T)) - 1 ∈ J :=
    Ideal.mem_sup_right (Ideal.subset_span ⟨(), rfl⟩)
  have hyc : y ⟨(), c⟩ ≠ 0 := by
    intro h0
    refine hXc (hPW (LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_iff.mpr (isWH_X c)) ?_))
    rw [aeval_X, h0]

  let φ : MRing (fun _ : Unit => T) →+* K' := (aeval fun p => y p / y ⟨(), c⟩).toRingHom
  have hφX : ∀ p, φ (X p) = y p / y ⟨(), c⟩ := fun p => aeval_X _ _
  have hφc : φ (X ⟨(), c⟩) = 1 := by rw [hφX, div_self hyc]
  have hφform : ∀ G n, IsMultiHomog G (fun _ => n) → φ G = aeval y G * (y ⟨(), c⟩ ^ n)⁻¹ :=
    fun G n hG => aeval_div y c G n hG
  have hspan : ∀ z ∈ Ideal.span (Set.range fun k =>
      (X ⟨k, (hWrel k).choose⟩ : MRing (fun _ : Unit => T)) - 1), φ z = 0 := by
    intro z hz
    refine (Ideal.span_le (I := RingHom.ker φ)).mpr ?_ hz
    rintro _ ⟨⟨⟩, rfl⟩
    show (X ⟨(), c⟩ : MRing (fun _ : Unit => T)) - 1 ∈ RingHom.ker φ
    rw [RingHom.mem_ker, map_sub, map_one, hφc, sub_self]
  have hker : RingHom.ker φ ≤ J := by
    intro f hf
    rw [RingHom.mem_ker] at hf
    have hχ : Ideal.Quotient.mk (Ideal.span {(X ⟨(), c⟩ : MRing (fun _ : Unit => T)) - 1})
        (X ⟨(), c⟩) = 1 := by
      rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact Ideal.mem_span_singleton_self _
    obtain ⟨n, G, hG, hGf⟩ := exists_homog _ c hχ f
    have hd : G - f ∈ Ideal.span {(X ⟨(), c⟩ : MRing (fun _ : Unit => T)) - 1} :=
      Ideal.Quotient.eq.mp hGf
    have hd' : G - f ∈ J := (Ideal.span_singleton_le_iff_mem _).mpr hXc1 hd
    have hφd : G - f ∈ RingHom.ker φ := (Ideal.span_singleton_le_iff_mem _).mpr
      (by rw [RingHom.mem_ker, map_sub, map_one, hφc, sub_self]) hd
    have hG0 : aeval y G = 0 := by
      rw [RingHom.mem_ker, map_sub, hf, sub_zero, hφform G n hG] at hφd
      exact (mul_eq_zero.mp hφd).resolve_right (inv_ne_zero (pow_ne_zero _ hyc))
    have hGJ : G ∈ J := Ideal.mem_sup_left (hPW (LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y hG hG0))
    simpa using sub_mem hGJ hd'

  have hB : ∀ b : curveRing y, ∃ f, φ f = b := by
    intro b
    have hb := mem_curveRing.mp b.2 (fun _ => c) (fun _ => hyc)
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at hb
    obtain ⟨f, hf⟩ := (AlgHom.mem_range _).mp hb
    exact ⟨f, hf⟩
  have hBr : ∀ b : curveRing y, (curveRing y).subtype b ∈ φ.range := fun b => hB b
  let e := RingHom.quotientKerEquivRange φ
  let ψ : φ.range →+* (MRing (fun _ : Unit => T) ⧸ J) :=
    (Ideal.Quotient.factor hker).comp e.symm.toRingHom
  have hψ : ∀ f (h : φ f ∈ φ.range), ψ ⟨φ f, h⟩ = Ideal.Quotient.mk J f := by
    intro f h
    have h' : e.symm ⟨φ f, h⟩ = Ideal.Quotient.mk (RingHom.ker φ) f := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.factor hker (e.symm ⟨φ f, h⟩) = _
    rw [h', Ideal.Quotient.factor_mk]
  let incl : curveRing y →+* φ.range := (curveRing y).subtype.codRestrict φ.range hBr
  let Θ : curveRing y →+* (MRing (fun _ : Unit => T) ⧸ J) := ψ.comp incl
  have hΘ : ∀ (b : curveRing y) f, φ f = b → Θ b = Ideal.Quotient.mk J f := by
    intro b f hf
    have h' : incl b = ⟨φ f, RingHom.mem_range_self φ f⟩ := Subtype.ext hf.symm
    show ψ (incl b) = _
    rw [h']
    exact hψ f _
  have hΘmul : ∀ (b₁ b₂ : curveRing y) g, (b₁ : K') * φ g = b₂ →
      Θ b₁ * Ideal.Quotient.mk J g = Θ b₂ := by
    intro b₁ b₂ g h
    obtain ⟨f, hf⟩ := hB b₁
    rw [hΘ b₁ f hf, hΘ b₂ (f * g) (by rw [map_mul, hf, h]), map_mul]

  have : Finite (MRing (fun _ : Unit => T) ⧸ J) := hFin
  have hFF : IsField Θ.range := Finite.isDomain_to_isField _
  have hmax : (RingHom.ker Θ).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField hFF (RingHom.quotientKerEquivRange Θ).toMulEquiv)

  obtain ⟨-, -, hchart⟩ := hC T K' y hP
  obtain ⟨t, hyt, hrat⟩ := hchart (RingHom.ker Θ) hmax
  have hgen : ∀ u : T, Ideal.Quotient.mk J (X ⟨(), u⟩) ∈ Θ.range := by
    intro u
    obtain ⟨ac, bc, hbc, hc'⟩ := hrat c
    obtain ⟨au, bu, hbu, hu'⟩ := hrat u
    have hac : Θ ac ≠ 0 := by
      intro h0
      apply hbc
      rw [RingHom.mem_ker, ← hΘmul ac bc (X ⟨(), t⟩) ?_, h0, zero_mul]
      rw [hφX, ← hc']
      field_simp
    have hbu' : Θ bu ≠ 0 := fun h0 => hbu (RingHom.mem_ker.mpr h0)
    have key : Θ (bu * ac) * Ideal.Quotient.mk J (X ⟨(), u⟩) = Θ (au * bc) := by
      refine hΘmul _ _ _ ?_
      push_cast
      rw [hφX, ← hu', ← hc']
      field_simp
    have hx : Θ (bu * ac) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero hbu' hac
    obtain ⟨w, hw⟩ := hFF.mul_inv_cancel (a := ⟨Θ (bu * ac), bu * ac, rfl⟩)
      (fun h => hx (congrArg Subtype.val h))
    have hw' : Θ (bu * ac) * (w : MRing (fun _ : Unit => T) ⧸ J) = 1 := congrArg Subtype.val hw
    have h2 : Ideal.Quotient.mk J (X ⟨(), u⟩) = Θ (au * bc) * w := by
      rw [← key, mul_comm (Θ (bu * ac)), mul_assoc, hw', mul_one]
    rw [h2]
    exact mul_mem ⟨au * bc, rfl⟩ w.2
  have hsurj : Function.Surjective Θ := by
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    suffices h : Ideal.Quotient.mk J f ∈ Θ.range from h
    induction f using MvPolynomial.induction_on with
    | C a =>
      rw [show Ideal.Quotient.mk J (C a) = (a : MRing (fun _ : Unit => T) ⧸ J) from
        eq_intCast ((Ideal.Quotient.mk J).comp C) a]
      exact intCast_mem _ a
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p i hp =>
      obtain ⟨⟨⟩, u⟩ := i
      rw [map_mul]
      exact mul_mem hp (hgen u)

  have hkerΘ : RingHom.ker Θ = curvePtIdeal y W := by
    apply le_antisymm
    · intro b hb
      rw [RingHom.mem_ker] at hb
      obtain ⟨f, hf⟩ := hB b
      rw [hΘ b f hf, Ideal.Quotient.eq_zero_iff_mem] at hb
      obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨n, G, hGW, hG, hφG⟩ := exists_homog_mem φ c hφc hWmh hw
      have h1 : (b : K') = aeval y G * (y ⟨(), c⟩ ^ n)⁻¹ := by
        rw [← hφform G n hG, hφG, ← hf, map_add, hspan z hz, add_zero]
      have hXn : IsMultiHomog (X ⟨(), c⟩ ^ n : MRing (fun _ : Unit => T)) (fun _ => n) :=
        isMultiHomog_iff.mpr (isWH_X_pow c n)
      have hXnW : (X ⟨(), c⟩ ^ n : MRing (fun _ : Unit => T)) ∉ W :=
        fun h => hXc (hWp.mem_of_pow_mem n h)
      have hval : (b : K') * aeval y (X ⟨(), c⟩ ^ n : MRing (fun _ : Unit => T)) = aeval y G := by
        rw [h1, map_pow, aeval_X, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hyc), mul_one]
      have hmemS : ∃ (d : Unit → ℕ) (g h : MRing (fun _ : Unit => T)), IsMultiHomog g d ∧
          IsMultiHomog h d ∧ g ∈ W ∧ h ∉ W ∧ (b : K') * aeval y h = aeval y g :=
by
        refine ⟨fun _ => n, G, X ⟨(), c⟩ ^ n, ?_, ?_, ?_, ?_, ?_⟩
        · exact hG
        · exact hXn
        · exact hGW
        · exact hXnW
        · exact hval
      exact Ideal.subset_span hmemS
    · refine Ideal.span_le.mpr ?_
      rintro b ⟨d, g, h, hg, hh, hgW, hhW, hbgh⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have hd : d = fun _ => d () := funext fun k => by cases k; rfl
      rw [hd] at hg hh
      obtain ⟨f, hf⟩ := hB b
      have hid : (b : K') * φ h = φ g := by
        rw [hφform h _ hh, hφform g _ hg, ← mul_assoc, hbgh]
      rw [hΘ b f hf]
      have h1 : Ideal.Quotient.mk J f * Ideal.Quotient.mk J h = 0 := by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        have h3 : f * h - g ∈ J := hker (by rw [RingHom.mem_ker, map_sub, map_mul, hf, hid, sub_self])
        simpa using add_mem h3 (Ideal.mem_sup_left hgW : g ∈ J)
      have h2 : Ideal.Quotient.mk J h ≠ 0 := by
        rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
        intro hJh
        obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp hJh
        obtain ⟨n', G, hGW, hG, hφG⟩ := exists_homog_mem φ c hφc hWmh hw
        have e1 : φ G = φ h := by rw [hφG, ← hwz, map_add, hspan z hz, add_zero]
        have hmem : G * X ⟨(), c⟩ ^ d () - h * X ⟨(), c⟩ ^ n' ∈ mCoordIdeal y := by
          refine LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (d := fun _ => n' + d ()) ?_ ?_
          · refine isMultiHomog_iff.mpr (isWH_sub ((isMultiHomog_iff.mp hG).mul (isWH_X_pow c _)) ?_)
            rw [add_comm n']
            exact (isMultiHomog_iff.mp hh).mul (isWH_X_pow c _)
          · rw [hφform G n' hG, hφform h _ hh] at e1
            rw [map_sub, map_mul, map_mul, map_pow, map_pow, aeval_X, sub_eq_zero]
            field_simp at e1
            linear_combination e1
        have h4 : h * X ⟨(), c⟩ ^ n' ∈ W := by
          have h5 := sub_mem (Ideal.mul_mem_right (X ⟨(), c⟩ ^ d ()) W hGW) (hPW hmem)
          simpa using h5
        rcases hWp.mem_or_mem h4 with h3 | h3
        · exact hhW h3
        · exact hXc (hWp.mem_of_pow_mem _ h3)
      exact (mul_eq_zero.mp h1).resolve_right h2

  let eq : (curveRing y ⧸ curvePtIdeal y W) ≃+* (MRing (fun _ : Unit => T) ⧸ J) :=
    (Ideal.quotEquivOfEq hkerΘ.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  rw [Nat.card_congr eq.toEquiv, hcard, hgeo]
  push_cast
  rw [Real.log_pow]

end

end GroundTheory.Heights₂.Heights
