import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
open CategoryTheory AlgebraicGeometry Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjSpace
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjHol

variable {N : ℕ}

abbrev InChart (x : Sp ℂ ⟶ PSpace ℂ N) (i : Fin (N + 1)) : Prop := ⊤ ≤ x ⁻¹ᵁ chart ℂ N i

def rv (x : Sp ℂ ⟶ PSpace ℂ N) (i j : Fin (N + 1)) : ℂ := valAt' x (chart ℂ N i) (ratio ℂ N i j)

theorem rv_eq {x : Sp ℂ ⟶ PSpace ℂ N} {i : Fin (N + 1)} (h : InChart x i) (j : Fin (N + 1)) :
    rv x i j = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (pullRatio x ⊤ i h j) := by
  rw [rv, valAt', dif_pos h]
  rfl

theorem rv_self {x : Sp ℂ ⟶ PSpace ℂ N} {i : Fin (N + 1)} (h : InChart x i) : rv x i i = 1 := by
  rw [rv_eq h, pullRatio_self, map_one]

theorem rv_mul {x : Sp ℂ ⟶ PSpace ℂ N} {i j : Fin (N + 1)} (hi : InChart x i) (hj : InChart x j)
    (k : Fin (N + 1)) : rv x i j * rv x j k = rv x i k := by
  rw [rv_eq hi, rv_eq hj, rv_eq hi, ← map_mul, pullRatio_mul_pullRatio]

theorem inChart_iff {x : Sp ℂ ⟶ PSpace ℂ N} {i : Fin (N + 1)} (hi : InChart x i) (j : Fin (N + 1)) :
    InChart x j ↔ rv x i j ≠ 0 := by
  rw [rv, ← GlobalTheory.HolHom.le_basicOpen_iff x hi, ratio, basicOpen_ratioOn, Scheme.Hom.preimage_inf, le_inf_iff]
  exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩

theorem exists_inChart (x : Sp ℂ ⟶ PSpace ℂ N) : ∃ i, InChart x i :=
  (exists_mem_chart ℂ N (x (default : PrimeSpectrum ℂ))).imp fun _ h => (GlobalTheory.HolHom.le_preimage_iff x _).2 h

theorem eq_of_rv_eq {x y : Sp ℂ ⟶ PSpace ℂ N} (h : x ≫ PSpace.str ℂ N = y ≫ PSpace.str ℂ N) {i : Fin (N + 1)}
    (hx : InChart x i) (hy : InChart y i) (H : ∀ j, rv x i j = rv y i j) : x = y := by
  refine hom_ext h fun p => ⟨⊤, trivial, i, hx, hy, fun j => ?_⟩
  have := H j
  rw [rv_eq hx, rv_eq hy] at this
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 this

theorem inChart_pt (c : ℂ →+* ℂ) (v : Fin (N + 1) → ℂ) (hv : Ideal.span (Set.range v) = ⊤) {i : Fin (N + 1)}
    (hi : v i ≠ 0) : InChart (pt c v hv) i := by
  rw [InChart, pt_preimage_chart]
  intro p _
  rw [mem_spOpen]
  exact fun h => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsUnit.mk0 _ hi))

theorem rv_pt (c : ℂ →+* ℂ) (v : Fin (N + 1) → ℂ) (hv : Ideal.span (Set.range v) = ⊤) {i : Fin (N + 1)}
    (hi : v i ≠ 0) (j : Fin (N + 1)) : rv (pt c v hv) i j = v j / v i := by
  have h := inChart_pt c v hv hi
  have e : ∀ a : ℂ, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (fnOn ⊤ a) = a := fun a => by
    have : fnOn (A := ℂ) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a :=
      GlobalTheory.Cartier.resG_self (X := Sp ℂ) le_top _
    rw [this]
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply a
  rw [rv_eq h, eq_div_iff hi, ← e (v i), ← e (v j), ← map_mul, pullRatio_pt_mul]

section Hol

variable {φ ψ : ℂ → (Sp ℂ ⟶ PSpace ℂ N)}

theorem eventually_inChart (hφ : IsHolTo (Set.univ : Set ℂ) φ) {z : ℂ} {i : Fin (N + 1)} (h : InChart (φ z) i) :
    ∀ᶠ w in 𝓝 z, InChart (φ w) i :=
  (GlobalTheory.HolHom.holAt_of_isHolTo hφ (Set.mem_univ z) _ h).1

theorem analyticAt_rv (hφ : IsHolTo (Set.univ : Set ℂ) φ) {z : ℂ} {i : Fin (N + 1)} (h : InChart (φ z) i)
    (j : Fin (N + 1)) : AnalyticAt ℂ (fun w => rv (φ w) i j) z :=
  (hφ (chart ℂ N i) (ratio ℂ N i j)).2.analyticAt ((hφ _ (ratio ℂ N i j)).1.mem_nhds ⟨trivial, h⟩)

theorem eq_of_eventuallyEq (hφ : IsHolTo (Set.univ : Set ℂ) φ) (hψ : IsHolTo (Set.univ : Set ℂ) ψ) {z : ℂ}
    (hs : φ z ≫ PSpace.str ℂ N = ψ z ≫ PSpace.str ℂ N) (h : ∀ᶠ w in 𝓝[≠] z, φ w = ψ w) : φ z = ψ z := by
  obtain ⟨k, hk⟩ := exists_inChart (φ z)
  obtain ⟨l, hl⟩ := exists_inChart (ψ z)
  have key : ∀ j, rv (ψ z) l k * rv (φ z) k j = rv (ψ z) l j := fun j => by
    have h1 := ((analyticAt_rv hψ hl k).continuousAt.mul (analyticAt_rv hφ hk j).continuousAt).tendsto
    have h2 := (analyticAt_rv hψ hl j).continuousAt.tendsto
    refine tendsto_nhds_unique_of_eventuallyEq (h1.mono_left nhdsWithin_le_nhds)
      (h2.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))) ?_
    filter_upwards [h, nhdsWithin_le_nhds (eventually_inChart hφ hk), nhdsWithin_le_nhds (eventually_inChart hψ hl)]
      with w e a b
    rw [e] at a
    simp only [Pi.mul_apply, e]
    exact rv_mul b a j
  have h0 : rv (ψ z) l k ≠ 0 := left_ne_zero_of_mul_eq_one ((key l).trans (rv_self hl))
  have hk' : InChart (ψ z) k := (inChart_iff hl k).2 h0
  exact eq_of_rv_eq hs hk hk' fun j => mul_left_cancel₀ h0 ((key j).trans (rv_mul hl hk' j).symm)

theorem eventually_nhdsNE_inChart (hφ : IsHolTo (Set.univ : Set ℂ) φ) {z₀ : ℂ} {k : Fin (N + 1)}
    (h₀ : InChart (φ z₀) k) (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, InChart (φ w) k := by
  let A : Set ℂ := {z | ∀ᶠ w in 𝓝[≠] z, InChart (φ w) k}
  have dich : ∀ z, z ∈ A ∨ ∀ᶠ w in 𝓝 z, ¬ InChart (φ w) k := fun z => by
    obtain ⟨i, hi⟩ := exists_inChart (φ z)
    rcases (analyticAt_rv hφ hi k).eventually_eq_zero_or_eventually_ne_zero with h | h
    · right
      filter_upwards [h, eventually_inChart hφ hi] with w a b c using (inChart_iff b k).1 c a
    · left
      filter_upwards [h, nhdsWithin_le_nhds (eventually_inChart hφ hi)] with w a b using (inChart_iff b k).2 a
  have ho : IsOpen A := isOpen_iff_mem_nhds.2 fun z hz => by
    have hz' : ∀ᶠ w in 𝓝 z, w ≠ z → InChart (φ w) k := eventually_nhdsWithin_iff.1 hz
    filter_upwards [hz'] with w hw
    by_cases e : w = z
    · exact e ▸ hz
    · exact nhdsWithin_le_nhds (eventually_inChart hφ (hw e))
  have hc : IsOpen Aᶜ := isOpen_iff_mem_nhds.2 fun z hz => by
    filter_upwards [((dich z).resolve_left hz).eventually_nhds] with w hw
    intro (hA : ∀ᶠ u in 𝓝[≠] w, InChart (φ u) k)
    obtain ⟨u, a, b⟩ := (hA.and (nhdsWithin_le_nhds hw)).exists
    exact b a
  have hA : A = Set.univ := IsClopen.eq_univ ⟨isOpen_compl_iff.1 hc, ho⟩
    ⟨z₀, nhdsWithin_le_nhds (eventually_inChart hφ h₀)⟩
  exact hA.ge (Set.mem_univ z)

theorem meromorphic_rv (hφ : IsHolTo (Set.univ : Set ℂ) φ) {z₀ : ℂ} {k : Fin (N + 1)}
    (h₀ : InChart (φ z₀) k) (j : Fin (N + 1)) : Meromorphic fun w => rv (φ w) k j := fun z => by
  obtain ⟨i, hi⟩ := exists_inChart (φ z)
  refine ((analyticAt_rv hφ hi j).meromorphicAt.div (analyticAt_rv hφ hi k).meromorphicAt).congr ?_
  filter_upwards [eventually_nhdsNE_inChart hφ h₀ z, nhdsWithin_le_nhds (eventually_inChart hφ hi)] with w a b
  rw [Pi.div_apply, div_eq_iff ((inChart_iff b k).1 a), mul_comm, rv_mul b a]

end Hol

end GlobalTheory.ProjHol
