import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsHomLocRingLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultiHomogPrimeCriterion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HomLocRingDimLe

variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}

def frac (P : Ideal (MRing ι R)) [P.IsPrime] (h : MRing ι R) : FractionRing (MRing ι R ⧸ P) :=
  algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P h)

theorem frac_zero (P : Ideal (MRing ι R)) [P.IsPrime] : frac P 0 = 0 := by
  simp [frac]

theorem frac_one (P : Ideal (MRing ι R)) [P.IsPrime] : frac P 1 = 1 := by
  simp [frac]

theorem frac_add (P : Ideal (MRing ι R)) [P.IsPrime] (x y : MRing ι R) :
    frac P (x + y) = frac P x + frac P y := by
  simp [frac]

theorem frac_mul (P : Ideal (MRing ι R)) [P.IsPrime] (x y : MRing ι R) :
    frac P (x * y) = frac P x * frac P y := by
  simp [frac]

variable (P W : Ideal (MRing ι R)) [P.IsPrime]

def ValIn (q : Ideal (homLocRing P W)) (z : FractionRing (MRing ι R ⧸ P)) : Prop :=
  ∃ a ∈ q, (a : FractionRing (MRing ι R ⧸ P)) = z

def primeSet (q : Ideal (homLocRing P W)) : Set (MRing ι R) :=
  {h | ∀ (b : K → ℕ) (g : MRing ι R), IsMultiHomog g b → g ∉ W →
    ValIn P W q (frac P (weightedHomogeneousComponent (blockWeight ι) b h) / frac P g)}

variable {P W}

theorem frac_ne_zero (hPW : P ≤ W) {g : MRing ι R} (hg : g ∉ W) : frac P g ≠ 0 := by
  simp only [frac, ne_eq, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  exact fun h => hg (hPW h)

theorem div_mem {b : K → ℕ} {f g : MRing ι R} (hf : IsMultiHomog f b) (hg : IsMultiHomog g b)
    (hgW : g ∉ W) : frac P f / frac P g ∈ homLocRing P W :=
  Subring.subset_closure ⟨b, f, g, hf, hg, hgW, rfl⟩

theorem valIn_zero (q : Ideal (homLocRing P W)) : ValIn P W q 0 := ⟨0, q.zero_mem, rfl⟩

theorem valIn_add {q : Ideal (homLocRing P W)} {z w : FractionRing (MRing ι R ⧸ P)}
    (hz : ValIn P W q z) (hw : ValIn P W q w) : ValIn P W q (z + w) := by
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨c, hc, rfl⟩ := hw
  exact ⟨a + c, q.add_mem ha hc, rfl⟩

theorem valIn_mul {q : Ideal (homLocRing P W)} {z w : FractionRing (MRing ι R ⧸ P)}
    (hz : ValIn P W q z) (hw : w ∈ homLocRing P W) : ValIn P W q (z * w) := by
  obtain ⟨a, ha, rfl⟩ := hz
  exact ⟨a * ⟨w, hw⟩, q.mul_mem_right _ ha, rfl⟩

theorem valIn_change (hPW : P ≤ W) {q : Ideal (homLocRing P W)} {b : K → ℕ} {f g g' : MRing ι R}
    (hg : IsMultiHomog g b) (hg' : IsMultiHomog g' b) (hgW : g ∉ W) (hg'W : g' ∉ W)
    (h : ValIn P W q (frac P f / frac P g)) : ValIn P W q (frac P f / frac P g') := by
  have e : frac P f / frac P g' = frac P f / frac P g * (frac P g / frac P g') := by
    rw [div_mul_div_cancel₀ (frac_ne_zero hPW hgW)]
  rw [e]
  exact valIn_mul h (div_mem hg hg' hg'W)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem comp_mul_add [Fintype K] {c d : K → ℕ} {s : MRing ι R} (hs : IsMultiHomog s c) (h : MRing ι R) :
    weightedHomogeneousComponent (blockWeight ι) (c + d) (s * h) =
      s * weightedHomogeneousComponent (blockWeight ι) d h := by
  have key := DirectSum.coe_decompose_mul_add_of_left_mem
    (𝒜 := weightedHomogeneousSubmodule R (blockWeight ι)) (j := d) (b := h)
    ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hs)
  rw [MultiHomogPrimeCriterion.coe_decompose, MultiHomogPrimeCriterion.coe_decompose] at key
  exact key

theorem comp_mul_of_ne [Fintype K] {c b : K → ℕ} {s : MRing ι R} (hs : IsMultiHomog s c) (h : MRing ι R)
    (hb : ∀ d, b ≠ c + d) : weightedHomogeneousComponent (blockWeight ι) b (s * h) = 0 := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) h,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp h), Finset.mul_sum, map_sum]
  exact Finset.sum_eq_zero fun d _ => IsWeightedHomogeneous.weightedHomogeneousComponent_ne b
    (IsWeightedHomogeneous.mul hs (weightedHomogeneousComponent_isWeightedHomogeneous d h)) (hb d)

theorem zero_mem_primeSet (q : Ideal (homLocRing P W)) : (0 : MRing ι R) ∈ primeSet P W q := by
  intro b g _ _
  rw [map_zero, frac_zero, zero_div]
  exact valIn_zero q

theorem add_mem_primeSet {q : Ideal (homLocRing P W)} {x y : MRing ι R} (hx : x ∈ primeSet P W q)
    (hy : y ∈ primeSet P W q) : x + y ∈ primeSet P W q := by
  intro b g hg hgW
  rw [map_add, frac_add, add_div]
  exact valIn_add (hx b g hg hgW) (hy b g hg hgW)

theorem form_mul_mem_primeSet [Fintype K] (hPW : P ≤ W) (hW : W.IsPrime) (hrel : IsRelevant W)
    {q : Ideal (homLocRing P W)} {c : K → ℕ} {s h : MRing ι R} (hs : IsMultiHomog s c)
    (hh : h ∈ primeSet P W q) : s * h ∈ primeSet P W q := by
  intro b g hg hgW
  by_cases hcb : ∃ d, b = c + d
  · obtain ⟨d, rfl⟩ := hcb
    rw [comp_mul_add hs h]
    obtain ⟨g', hg', hg'W⟩ := homLocRing_form_not_mem hW hrel d
    have hsg : IsMultiHomog (s * g') (c + d) := IsWeightedHomogeneous.mul hs hg'
    have e : frac P (s * weightedHomogeneousComponent (blockWeight ι) d h) / frac P g =
        frac P (weightedHomogeneousComponent (blockWeight ι) d h) / frac P g' *
          (frac P (s * g') / frac P g) := by
      have h1 := frac_ne_zero hPW hg'W
      have h2 := frac_ne_zero hPW hgW
      rw [frac_mul, frac_mul]
      field_simp
    rw [e]
    exact valIn_mul (hh d g' hg' hg'W) (div_mem hsg hg hgW)
  · rw [comp_mul_of_ne hs h (fun d hd => hcb ⟨d, hd⟩), frac_zero, zero_div]
    exact valIn_zero q

theorem mul_mem_primeSet [Fintype K] (hPW : P ≤ W) (hW : W.IsPrime) (hrel : IsRelevant W)
    {q : Ideal (homLocRing P W)} (s : MRing ι R) {h : MRing ι R} (hh : h ∈ primeSet P W q) :
    s * h ∈ primeSet P W q := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) s,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp s), Finset.sum_mul]
  exact Finset.sum_induction _ (· ∈ primeSet P W q) (fun _ _ => add_mem_primeSet)
    (zero_mem_primeSet q) fun c _ =>
      form_mul_mem_primeSet hPW hW hrel (weightedHomogeneousComponent_isWeightedHomogeneous c s) hh

def primeAbove [Fintype K] (hPW : P ≤ W) (hW : W.IsPrime) (hrel : IsRelevant W) (q : Ideal (homLocRing P W)) :
    Ideal (MRing ι R) where
  carrier := primeSet P W q
  zero_mem' := zero_mem_primeSet q
  add_mem' := add_mem_primeSet
  smul_mem' s _ hh := mul_mem_primeSet hPW hW hrel s hh

theorem form_mem_primeSet (hPW : P ≤ W) {q : Ideal (homLocRing P W)} {s : K → ℕ} {f g : MRing ι R}
    (hf : IsMultiHomog f s) (hg : IsMultiHomog g s) (hgW : g ∉ W)
    (h : ValIn P W q (frac P f / frac P g)) : f ∈ primeSet P W q := by
  intro b g' hg' hg'W
  by_cases hsb : b = s
  · subst hsb
    rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hf]
    exact valIn_change hPW hg hg' hgW hg'W h
  · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b hf hsb, frac_zero, zero_div]
    exact valIn_zero q

theorem valIn_of_form_mem {q : Ideal (homLocRing P W)} {s : K → ℕ} {f g : MRing ι R}
    (hf : IsMultiHomog f s) (hg : IsMultiHomog g s) (hgW : g ∉ W) (h : f ∈ primeSet P W q) :
    ValIn P W q (frac P f / frac P g) := by
  have := h s g hg hgW
  rwa [IsWeightedHomogeneous.weightedHomogeneousComponent_same hf] at this

theorem mem_primeAbove [Fintype K] (hPW : P ≤ W) (hW : W.IsPrime) (hrel : IsRelevant W)
    (q : Ideal (homLocRing P W)) (h : MRing ι R) :
    h ∈ primeAbove hPW hW hrel q ↔ h ∈ primeSet P W q := Iff.rfl

theorem primeAbove_multiHomog [Fintype K] (hPW : P ≤ W) (hW : W.IsPrime) (hrel : IsRelevant W)
    (q : Ideal (homLocRing P W)) : IsMultiHomogIdeal (primeAbove hPW hW hrel q) := by
  intro h hh c
  rw [mem_primeAbove] at hh ⊢
  intro b g hg hgW
  rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2
    (weightedHomogeneousComponent_isWeightedHomogeneous c h))]
  split_ifs with hbc
  · subst hbc
    exact hh b g hg hgW
  · rw [frac_zero, zero_div]
    exact valIn_zero q

theorem primeAbove_isPrime [Fintype K] (hPW : P ≤ W) (hW : W.IsPrime) (hrel : IsRelevant W)
    (q : Ideal (homLocRing P W)) [hq : q.IsPrime] : (primeAbove hPW hW hrel q).IsPrime := by
  refine MultiHomogPrimeCriterion.proof R K ι _ (primeAbove_multiHomog hPW hW hrel q) ?_ ?_
  · intro htop
    have h1 : (1 : MRing ι R) ∈ primeSet P W q := by
      rw [← mem_primeAbove hPW hW hrel, htop]
      exact Submodule.mem_top
    have hW1 : (1 : MRing ι R) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one W).2 h)
    obtain ⟨a, ha, hav⟩ := valIn_of_form_mem (isWeightedHomogeneous_one R (blockWeight ι))
      (isWeightedHomogeneous_one R (blockWeight ι)) hW1 h1
    rw [frac_one, div_one] at hav
    have : a = 1 := Subtype.ext hav
    exact hq.ne_top ((Ideal.eq_top_iff_one q).2 (this ▸ ha))
  · intro a b sa sb ha hb hab
    obtain ⟨ga, hga, hgaW⟩ := homLocRing_form_not_mem hW hrel sa
    obtain ⟨gb, hgb, hgbW⟩ := homLocRing_form_not_mem hW hrel sb
    have hg : IsMultiHomog (ga * gb) (sa + sb) := IsWeightedHomogeneous.mul hga hgb
    have hgW : ga * gb ∉ W := fun h => (hW.mem_or_mem h).elim hgaW hgbW
    obtain ⟨x, hx, hxv⟩ := valIn_of_form_mem (IsWeightedHomogeneous.mul ha hb) hg hgW hab
    have hxe : x = ⟨_, div_mem ha hga hgaW⟩ * ⟨_, div_mem hb hgb hgbW⟩ := by
      apply Subtype.ext
      rw [hxv, Subring.coe_mul, frac_mul, frac_mul, mul_div_mul_comm]
    rw [hxe] at hx
    rcases hq.mem_or_mem hx with h | h
    · exact Or.inl (form_mem_primeSet hPW ha hga hgaW ⟨_, h, rfl⟩)
    · exact Or.inr (form_mem_primeSet hPW hb hgb hgbW ⟨_, h, rfl⟩)

theorem le_primeAbove [Fintype K] (hP : IsMultiHomogIdeal P) (hPW : P ≤ W) (hW : W.IsPrime)
    (hrel : IsRelevant W) (q : Ideal (homLocRing P W)) : P ≤ primeAbove hPW hW hrel q := by
  intro p hp
  rw [mem_primeAbove]
  intro b g _ _
  have : frac P (weightedHomogeneousComponent (blockWeight ι) b p) = 0 := by
    rw [frac, Ideal.Quotient.eq_zero_iff_mem.mpr (hP p hp b), map_zero]
  rw [this, zero_div]
  exact valIn_zero q

theorem primeAbove_le [Fintype K] (hloc : HomLocRingIsLocal.Statement.{u}) (hPW : P ≤ W)
    (hW : W.IsPrime) (hrel : IsRelevant W) (q : Ideal (homLocRing P W)) [hq : q.IsPrime] :
    primeAbove hPW hW hrel q ≤ W := by
  intro h hh
  rw [mem_primeAbove] at hh
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) h,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp h)]
  refine W.sum_mem fun b _ => ?_
  by_contra hf
  obtain ⟨g, hg, hgW⟩ := homLocRing_form_not_mem hW hrel b
  have hfb : IsMultiHomog (weightedHomogeneousComponent (blockWeight ι) b h) b :=
    weightedHomogeneousComponent_isWeightedHomogeneous b h
  obtain ⟨a, ha, hav⟩ := hh b g hg hgW
  have hu := ((hloc R K ι P W hW hPW).2 b _ g hfb hg hgW (div_mem hfb hg hgW)).2 hf
  have : a = ⟨_, div_mem hfb hg hgW⟩ := Subtype.ext hav
  rw [this] at ha
  exact hq.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)

theorem primeAbove_strictMono [Fintype K] (hmem : HomLocRingMem.Statement.{u}) (hPW : P ≤ W)
    (hW : W.IsPrime) (hrel : IsRelevant W) {q q' : Ideal (homLocRing P W)} (hlt : q < q') :
    primeAbove hPW hW hrel q < primeAbove hPW hW hrel q' := by
  refine lt_of_le_of_ne (fun h hh => ?_) (fun heq => ?_)
  · rw [mem_primeAbove] at hh ⊢
    intro b g hg hgW
    obtain ⟨a, ha, hav⟩ := hh b g hg hgW
    exact ⟨a, hlt.le ha, hav⟩
  · obtain ⟨x, hx', hx⟩ := SetLike.exists_of_lt hlt
    obtain ⟨b, f, g, hf, hg, hgW, hxv⟩ := (hmem R K ι P W hW hPW x.1).1 x.2
    have h1 : f ∈ primeAbove hPW hW hrel q' := form_mem_primeSet hPW hf hg hgW ⟨x, hx', hxv⟩
    rw [← heq] at h1
    obtain ⟨a, ha, hav⟩ := valIn_of_form_mem hf hg hgW h1
    have hax : a = x := Subtype.ext (hav.trans hxv.symm)
    exact hx (hax ▸ ha)

end HomLocRingDimLe

open HomLocRingDimLe in

theorem HomLocRingDimLe.proof (h₁ : HomLocRingMem.Statement.{u})
    (h₂ : HomLocRingIsLocal.Statement.{u}) : HomLocRingDimLe.Statement.{u} := by
  intro R _ K _ _ ι _ P W _ hP hW hrel hPW
  haveI := hW
  let Φ : PrimeSpectrum (homLocRing P W) → PrimeSpectrum (MRing ι R ⧸ P) := fun q =>
    haveI := primeAbove_isPrime hPW hW hrel q.asIdeal
    ⟨(primeAbove hPW hW hrel q.asIdeal).map (Ideal.Quotient.mk P),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact le_primeAbove hP hPW hW hrel q.asIdeal)⟩
  have hΦ : StrictMono Φ := by
    intro q q' hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hlt ⊢
    have hlt' := primeAbove_strictMono h₁ hPW hW hrel hlt
    have hPq := le_primeAbove hP hPW hW hrel q.asIdeal
    have hPq' := le_primeAbove hP hPW hW hrel q'.asIdeal
    change (primeAbove hPW hW hrel q.asIdeal).map (Ideal.Quotient.mk P) <
      (primeAbove hPW hW hrel q'.asIdeal).map (Ideal.Quotient.mk P)
    refine lt_of_le_of_ne (Ideal.map_mono hlt'.le) fun heq => hlt'.ne ?_
    have := congrArg (Ideal.comap (Ideal.Quotient.mk P)) heq
    rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hPq, sup_eq_left.mpr hPq'] at this
  haveI hWq : (W.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPW)
  let w : PrimeSpectrum (MRing ι R ⧸ P) := ⟨W.map (Ideal.Quotient.mk P), hWq⟩
  have hΦw : ∀ q, Φ q ≤ w := fun q => by
    rw [← PrimeSpectrum.asIdeal_le_asIdeal]
    exact Ideal.map_mono (primeAbove_le h₂ hPW hW hrel q.asIdeal)
  rw [show (W.map (Ideal.Quotient.mk P)).height = Order.height w from
    PrimeSpectrum.height_eq_orderHeight w]
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l => ?_
  have h1 : ((l.map Φ hΦ).length : ℕ∞) ≤ Order.height ((l.map Φ hΦ).last) :=
    Order.length_le_height_last
  rw [LTSeries.last_map] at h1
  have h2 := h1.trans (Order.height_mono (hΦw l.last))
  have h3 : (l.map Φ hΦ).length = l.length := rfl
  rw [h3] at h2
  exact_mod_cast h2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
