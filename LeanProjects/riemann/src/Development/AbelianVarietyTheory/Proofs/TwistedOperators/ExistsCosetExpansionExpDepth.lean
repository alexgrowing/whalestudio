import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri FieldCond)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem isLattice_pairs {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀)
    (t : T) (j : ℕ) (hj : j < D.R.m) :
      (Submodule.IsLattice D.host.E (G.latS (.top t j)) ∧ Submodule.IsLattice D.host.E (G.latT (.top t j))) ∧
      (Submodule.IsLattice D.host.E (G.latS (.chi j D.R.m)) ∧ Submodule.IsLattice D.host.E (G.latT (.chi j D.R.m))) := by
  have hV : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → Submodule.IsLattice D.host.E (G.Λ X) :=
    fun X h h0 => (G.isV h h0).sd.1
  refine ⟨⟨hV (.top j) (show j ≤ D.R.m by omega) (by simp), hV (.top (j + 1)) (show j + 1 ≤ D.R.m by omega) (by simp)⟩,
    hV (.grid (j + 1) D.R.m) ⟨by omega, le_rfl⟩ (by simp), ?_⟩
  rcases j with _ | i
  · show Submodule.IsLattice D.host.E (columnBlock L D.R.m).lat
    rw [colY_m]
    obtain ⟨c, hF, -⟩ := hL.βX
    exact GlobalTheory.DiagLiftFix.isLattice_of_isFrame hF
  · exact hV (.grid (i + 1) D.R.m) ⟨by omega, le_rfl⟩ (by simp)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

section Coset

variable {m n : ℕ}

theorem isHalf_nsmul_of {e : AE D} {u : Mx D m n} (c : ℕ) (h : IsHalf e u) : IsHalf e (c • u) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, h i j]

theorem isHalf_of_mem_halfCoset {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {x₀ x : Mx D m n} (h0 : IsHalf e x₀)
    (h : x ∈ halfCoset e Λ K x₀) : IsHalf e x := by
  obtain ⟨u, -, hu, rfl⟩ := h
  intro i j
  rw [Matrix.add_apply, mul_add, h0 i j, isHalf_nsmul_of K hu i j]

theorem add_nsmul_mem_halfCoset_iff {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {x₀ x u : Mx D m n} (hu : u ∈ Λ)
    (hu' : IsHalf e u) : x + K • u ∈ halfCoset e Λ K x₀ ↔ x ∈ halfCoset e Λ K x₀ := by
  constructor
  · rintro ⟨v, hv, hv', hx⟩
    refine ⟨v - u, sub_mem hv hu, fun i j => by rw [Matrix.sub_apply, mul_sub, hv' i j, hu' i j], ?_⟩
    rw [nsmul_sub, ← add_sub_assoc, ← hx, add_sub_cancel_right]
  · rintro ⟨v, hv, hv', rfl⟩
    exact ⟨v + u, add_mem hv hu, fun i j => by rw [Matrix.add_apply, mul_add, hv' i j, hu' i j],
      by rw [nsmul_add, add_assoc]⟩

theorem isSBHalf_halfCoset_indicator {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} (hK : 0 < K) {x₀ : Mx D m n}
    (h0 : IsHalf e x₀) (h1 : K • x₀ ∈ Λ) : IsSBHalf e Λ ((halfCoset e Λ K x₀).indicator 1) := by
  refine ⟨fun x hx => isHalf_of_mem_halfCoset h0 (Set.mem_of_indicator_ne_zero hx), K, hK, fun u hu hu' x => ?_,
    fun x hx => ?_⟩
  · by_cases hx : x ∈ halfCoset e Λ K x₀
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((add_nsmul_mem_halfCoset_iff hu hu').2 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (add_nsmul_mem_halfCoset_iff hu hu').1 hx)]
  · obtain ⟨u, hu, -, rfl⟩ := Set.mem_of_indicator_ne_zero hx
    rw [nsmul_add]
    exact add_mem h1 (nsmul_mem (nsmul_mem hu K) K)

theorem isSBHalf_of_dvd {e : AE D} {Λ : AddSubgroup (Mx D m n)} {f : Mx D m n → ℂ} (h : IsSBHalf e Λ f) {K : ℕ}
    (hK : h.2.choose ∣ K) :
    (∀ x, f x ≠ 0 → IsHalf e x ∧ K • x ∈ Λ) ∧ ∀ u ∈ Λ, IsHalf e u → ∀ x, f (x + K • u) = f x := by
  obtain ⟨c, rfl⟩ := hK
  obtain ⟨-, h2, h3⟩ := h.2.choose_spec
  refine ⟨fun x hx => ⟨h.1 x hx, ?_⟩, fun u hu hu' x => ?_⟩
  · rw [show h.2.choose * c = c * h.2.choose from mul_comm _ _, mul_smul]
    exact nsmul_mem (h3 x hx) c
  · rw [mul_smul]
    exact h2 _ (nsmul_mem hu c) (isHalf_nsmul_of c hu') x

theorem eq_sum_halfCoset_indicator {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {f : Mx D m n → ℂ}
    {R : Finset (Mx D m n)} (hf1 : ∀ x, f x ≠ 0 → IsHalf e x ∧ K • x ∈ Λ)
    (hf2 : ∀ u ∈ Λ, IsHalf e u → ∀ x, f (x + K • u) = f x)
    (hR2 : ∀ x, IsHalf e x → K • x ∈ Λ → ∃ r ∈ R, x ∈ halfCoset e Λ K r)
    (hR3 : ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e Λ K r → r = r') (x : Mx D m n) :
    f x = ∑ r ∈ R, f r * (halfCoset e Λ K r).indicator (1 : Mx D m n → ℂ) x := by
  have key : ∀ r, x ∈ halfCoset e Λ K r → f r = f x := by
    rintro r ⟨u, hu, hu', rfl⟩
    exact (hf2 u hu hu' r).symm
  by_cases hx : f x = 0
  · rw [hx, eq_comm]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hm : x ∈ halfCoset e Λ K r
    · rw [key r hm, hx, zero_mul]
    · rw [Set.indicator_of_notMem hm, mul_zero]
  · obtain ⟨r₀, hr₀, hm⟩ := hR2 x (hf1 x hx).1 (hf1 x hx).2
    rw [Finset.sum_eq_single_of_mem r₀ hr₀, Set.indicator_of_mem hm, key r₀ hm, Pi.one_apply, mul_one]
    intro r hr hne
    rw [Set.indicator_of_notMem, mul_zero]
    intro hm'
    refine hne (hR3 r hr r₀ hr₀ ?_)
    rw [(halfCoset_eq hm').symm.trans (halfCoset_eq hm)]
    exact mem_halfCoset_self _ _ _ _

end Coset

open Classical in

def cosetDatum {t : T} {p : Pair T} (d : FinDatum G t p) (K : ℕ) (r : WO (G.pS p) (G.pT p)) : FinDatum G t p :=
  if h : 0 < K ∧ IsHalf d.e r ∧ K • r ∈ pairLat G p then
    { d with fn := (halfCoset d.e (pairLat G p) K r).indicator 1, sb := isSBHalf_halfCoset_indicator h.1 h.2.1 h.2.2 }
  else d

theorem cosetDatum_P {t : T} {p : Pair T} (d : FinDatum G t p) (K : ℕ) (r) : (cosetDatum d K r).P = d.P := by
  unfold cosetDatum; split_ifs <;> rfl

theorem cosetDatum_e {t : T} {p : Pair T} (d : FinDatum G t p) (K : ℕ) (r) : (cosetDatum d K r).e = d.e := by
  unfold cosetDatum; split_ifs <;> rfl

theorem cosetIndicatorFinDatum_point {t : T} {p : Pair T} (d : FinDatum G t p) (K : ℕ) (r) : (cosetDatum d K r).z = d.z := by
  unfold cosetDatum; split_ifs <;> rfl

theorem cosetDatum_fn {t : T} {p : Pair T} (d : FinDatum G t p) {K : ℕ} {r} {e : AE D} (he : d.e = e) (hK : 0 < K)
    (h1 : IsHalf e r) (h2 : K • r ∈ pairLat G p) :
    (cosetDatum d K r).fn = (halfCoset e (pairLat G p) K r).indicator 1 := by
  subst he
  unfold cosetDatum
  rw [dif_pos ⟨hK, h1, h2⟩]

theorem isCosetDatum_cosetDatum {t : T} {p : Pair T} (d : FinDatum G t p) {K : ℕ} {r} (hK : 0 < K) (h1 : IsHalf d.e r)
    (h2 : K • r ∈ pairLat G p) : IsCosetDatum K (cosetDatum d K r) :=
  ⟨r, (cosetDatum_e d K r).symm ▸ h1, h2, by rw [cosetDatum_fn d rfl hK h1 h2, cosetDatum_e]⟩

section Reps

variable {D : D7} {m n : ℕ}

theorem nsmul_cancel_ae {K : ℕ} (hK : 0 < K) {a b : AE D} (h : K • a = K • b) : a = b := by
  have hu : IsUnit (K : AE D) := by
    rw [← map_natCast (algebraMap D.host.F (AE D))]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hK.ne')).map _
  rw [nsmul_eq_mul, nsmul_eq_mul] at h
  exact hu.mul_left_cancel h

theorem nsmul_cancel_mx {K : ℕ} (hK : 0 < K) {x y : Mx D m n} (h : K • x = K • y) : x = y := by
  ext i j
  exact nsmul_cancel_ae hK (by simpa only [Matrix.smul_apply] using congrFun (congrFun h i) j)

theorem exists_halfCoset_reps {Λ : AddSubgroup (Mx D m n)} (e : AE D) {K : ℕ} (hK : 0 < K)
    (hF : ∃ F : Set (Mx D m n), F.Finite ∧ ∀ u ∈ Λ, ∃ f ∈ F, ∃ v ∈ Λ, u = f + (K * K) • v) :
    ∃ R : Finset (Mx D m n), (∀ r ∈ R, IsHalf e r ∧ K • r ∈ Λ) ∧
      (∀ x, IsHalf e x → K • x ∈ Λ → ∃ r ∈ R, x ∈ halfCoset e Λ K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e Λ K r → r = r' := by
  classical
  obtain ⟨F₀, hF₀, hF2⟩ := hF
  let F := hF₀.toFinset
  let C : Mx D m n → Set (Mx D m n) := fun f => {x | IsHalf e x ∧ K • x ∈ Λ ∧ ∃ v ∈ Λ, K • x = f + (K * K) • v}
  let rep : Mx D m n → Mx D m n := fun f => if h : (C f).Nonempty then h.some else 0
  have hrep : ∀ f, (C f).Nonempty → rep f ∈ C f := fun f h => by
    simp only [rep, dif_pos h]
    exact h.some_mem
  have hhalf : ∀ {x r w : Mx D m n}, IsHalf e x → IsHalf e r → K • x = K • r + (K * K) • w → IsHalf e w := by
    intro x r w hx hr h i j
    have hw : (K * K) • w = K • x - K • r := by rw [h]; abel
    have hs : IsHalf e (K • x - K • r) := fun i j => by
      rw [Matrix.sub_apply, mul_sub, isHalf_nsmul_of K hx i j, isHalf_nsmul_of K hr i j]
    rw [← hw] at hs
    refine nsmul_cancel_ae (Nat.mul_pos hK hK) ?_
    have := hs i j
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm] at this
    rw [nsmul_eq_mul, nsmul_eq_mul]
    exact this
  have hCeq : ∀ f f' : Mx D m n, (∃ w ∈ Λ, f' = f + (K * K) • w) → C f = C f' := by
    rintro f f' ⟨w, hw, rfl⟩
    ext x
    constructor
    · rintro ⟨hx, hKx, v, hv, h⟩
      exact ⟨hx, hKx, v - w, sub_mem hv hw, by rw [h, nsmul_sub]; abel⟩
    · rintro ⟨hx, hKx, v, hv, h⟩
      exact ⟨hx, hKx, w + v, add_mem hw hv, by rw [h, nsmul_add]; abel⟩
  refine ⟨(F.filter fun f => (C f).Nonempty).image rep, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨h1, h2, -⟩ := hrep f (Finset.mem_filter.1 hf).2
    exact ⟨h1, h2⟩
  · intro x hx hKx
    obtain ⟨f, hf, v, hv, hfv⟩ := hF2 _ hKx
    have hxC : x ∈ C f := ⟨hx, hKx, v, hv, hfv⟩
    refine ⟨rep f, Finset.mem_image.2 ⟨f, Finset.mem_filter.2 ⟨hF₀.mem_toFinset.2 hf, x, hxC⟩, rfl⟩, ?_⟩
    obtain ⟨h1, -, w, hw, h2⟩ := hrep f ⟨x, hxC⟩
    have h3 : K • x = K • rep f + (K * K) • (v - w) := by rw [hfv, h2, nsmul_sub]; abel
    refine ⟨v - w, sub_mem hv hw, hhalf hx h1 h3, nsmul_cancel_mx hK ?_⟩
    rw [h3, nsmul_add, mul_smul]
  · intro r hr r' hr' hm
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hr'
    obtain ⟨-, -, w, hw, h1⟩ := hrep f (Finset.mem_filter.1 hf).2
    obtain ⟨-, -, w', hw', h2⟩ := hrep f' (Finset.mem_filter.1 hf').2
    obtain ⟨u, hu, -, h3⟩ := hm
    have h4 : f' = f + (K * K) • (w + u - w') := by
      have h5 : K • rep f' = K • rep f + (K * K) • u := by rw [h3, nsmul_add, mul_smul]
      rw [h2, h1] at h5
      rw [nsmul_sub, nsmul_add, eq_sub_of_add_eq h5]
      abel
    have := hCeq f f' ⟨_, sub_mem (add_mem hw hu) hw', h4⟩
    simp only [rep, this]

end Reps

section Main

variable {U : Set T}

theorem exists_cosetExpansion {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) :
    (∃ τ, S.IsExpansion t Φ β τ) → ∃ k τ', IsCosetExpansion S t Φ β k τ' := by
  classical
  rintro ⟨τ, e, he, hP, hsum⟩
  set K : ℕ := ∏ d ∈ τ.support, ((∏ j, (d.1 j).sb.2.choose) * ∏ i, (d.2 i).sb.2.choose) with hKdef
  have hKpos : 0 < K := Finset.prod_pos fun d _ => Nat.mul_pos (Finset.prod_pos fun j _ => (d.1 j).sb.2.choose_spec.1)
    (Finset.prod_pos fun i _ => (d.2 i).sb.2.choose_spec.1)
  have hdvd1 : ∀ d ∈ τ.support, ∀ j, (d.1 j).sb.2.choose ∣ K := fun d hd j =>
    (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (fun j => (d.1 j).sb.2.choose) (Finset.mem_univ j)) _).trans
      (Finset.dvd_prod_of_mem (fun d : PureDat G t => (∏ j, (d.1 j).sb.2.choose) * ∏ i, (d.2 i).sb.2.choose) hd)
  have hdvd2 : ∀ d ∈ τ.support, ∀ i, (d.2 i).sb.2.choose ∣ K := fun d hd i =>
    (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun i => (d.2 i).sb.2.choose) (Finset.mem_univ i)) _).trans
      (Finset.dvd_prod_of_mem (fun d : PureDat G t => (∏ j, (d.1 j).sb.2.choose) * ∏ i, (d.2 i).sb.2.choose) hd)
  have hR1 : ∀ j : Fin D.R.m, ∃ R : Finset (WO (G.pS (.top t j)) (G.pT (.top t j))),
      (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.top t j)) ∧
      (∀ x, IsHalf e x → K • x ∈ pairLat G (.top t j) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.top t j)) K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairLat G (.top t j)) K r → r = r' := fun j =>
    exists_halfCoset_reps e hKpos (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t j j.2).1.1.fg
      (isLattice_pairs G hL t j j.2).1.2.fg _ (K * K) (Nat.mul_pos hKpos hKpos))
  have hR2 : ∀ i : Fin D.R.m, ∃ R : Finset (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.chi i D.R.m)) ∧
      (∀ x, IsHalf e x → K • x ∈ pairLat G (.chi i D.R.m) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r → r = r' := fun i =>
    exists_halfCoset_reps e hKpos (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t i i.2).2.1.fg
      (isLattice_pairs G hL t i i.2).2.2.fg _ (K * K) (Nat.mul_pos hKpos hKpos))
  choose R1 hR1 using hR1
  choose R2 hR2 using hR2
  set τ' : PureDat G t →₀ ℂ := (∑ d ∈ τ.support, ∑ ρ ∈ Fintype.piFinset R1, ∑ ρ' ∈ Fintype.piFinset R2,
      Finsupp.single (((fun j => cosetDatum (d.1 j) K (ρ j)), fun i => cosetDatum (d.2 i) K (ρ' i)) : PureDat G t)
        (τ d * (∏ j, (d.1 j).fn (ρ j)) * ∏ i, (d.2 i).fn (ρ' i))) with hτ'
  have hsupp : ∀ d' ∈ τ'.support,
      ∃ d ∈ τ.support, ∃ ρ ∈ Fintype.piFinset R1, ∃ ρ' ∈ Fintype.piFinset R2,
        d' = ((fun j => cosetDatum (d.1 j) K (ρ j)), fun i => cosetDatum (d.2 i) K (ρ' i)) := by
    intro d' hd'
    rw [hτ'] at hd'
    obtain ⟨d, hd, h1⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hd')
    obtain ⟨ρ, hρ, h2⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum h1)
    obtain ⟨ρ', hρ', h3⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum h2)
    exact ⟨d, hd, ρ, hρ, ρ', hρ', Finset.mem_singleton.1 (Finsupp.support_single_subset h3)⟩
  refine ⟨K, τ', hKpos, ⟨e, he, fun d' hd' => ?_, fun x y hx hy => ?_⟩, fun d' hd' => ?_⟩
  · obtain ⟨d, hd, ρ, -, ρ', -, rfl⟩ := hsupp d' hd'
    refine ⟨fun j => ?_, fun i => ?_⟩
    · obtain ⟨a, b, c⟩ := (hP d hd).1 j
      exact ⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩
    · obtain ⟨a, b, c⟩ := (hP d hd).2 i
      exact ⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩
  · let g : PureDat G t → ℂ → ℂ := fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)
    have h0 : ∀ d, g d 0 = 0 := fun d => by simp [g]
    have hadd : ∀ d b₁ b₂, g d (b₁ + b₂) = g d b₁ + g d b₂ := fun d b₁ b₂ => by simp only [g]; ring
    rw [← hsum x y hx hy]
    change Finsupp.sum τ' g = τ.sum g
    rw [hτ', ← Finsupp.sum_finsetSum_index h0 hadd, Finsupp.sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← Finsupp.sum_finsetSum_index h0 hadd]
    simp_rw [← Finsupp.sum_finsetSum_index h0 hadd, Finsupp.sum_single_index (h0 _)]
    have hA : ∀ j, (d.1 j).fn (x j) =
        ∑ r ∈ R1 j, (d.1 j).fn r * (halfCoset e (pairLat G (.top t j)) K r).indicator 1 (x j) := fun j => by
      have h := isSBHalf_of_dvd (d.1 j).sb (hdvd1 d hd j)
      rw [((hP d hd).1 j).2.1] at h
      exact eq_sum_halfCoset_indicator h.1 h.2 (hR1 j).2.1 (hR1 j).2.2 (x j)
    have hB : ∀ i, (d.2 i).fn (y i) =
        ∑ r ∈ R2 i, (d.2 i).fn r * (halfCoset e (pairLat G (.chi i D.R.m)) K r).indicator 1 (y i) := fun i => by
      have h := isSBHalf_of_dvd (d.2 i).sb (hdvd2 d hd i)
      rw [((hP d hd).2 i).2.1] at h
      exact eq_sum_halfCoset_indicator h.1 h.2 (hR2 i).2.1 (hR2 i).2.2 (y i)
    simp only [g]
    rw [Finset.prod_congr rfl fun j _ => hA j, Finset.prod_congr rfl fun i _ => hB i, Finset.prod_univ_sum,
      Finset.prod_univ_sum]
    conv_rhs => rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ' hρ' => ?_
    rw [Fintype.mem_piFinset] at hρ hρ'
    rw [Finset.prod_congr rfl fun j _ => congrFun (cosetDatum_fn (d.1 j) ((hP d hd).1 j).2.1 hKpos ((hR1 j).1 _ (hρ j)).1
        ((hR1 j).1 _ (hρ j)).2) (x j),
      Finset.prod_congr rfl fun i _ => congrFun (cosetDatum_fn (d.2 i) ((hP d hd).2 i).2.1 hKpos ((hR2 i).1 _ (hρ' i)).1
        ((hR2 i).1 _ (hρ' i)).2) (y i),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  · obtain ⟨d, hd, ρ, hρ, ρ', hρ', rfl⟩ := hsupp d' hd'
    rw [Fintype.mem_piFinset] at hρ hρ'
    refine ⟨fun j => ?_, fun i => ?_⟩
    · have h := (hR1 j).1 _ (hρ j)
      exact isCosetDatum_cosetDatum _ hKpos (((hP d hd).1 j).2.1 ▸ h.1) h.2
    · have h := (hR2 i).1 _ (hρ' i)
      exact isCosetDatum_cosetDatum _ hKpos (((hP d hd).2 i).2.1 ▸ h.1) h.2

end Main

theorem exists_cosetExpansion_expDepth {U : Set T} {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (β : CosFam G t) (h : ∃ τ, S.IsExpansion t Φ β τ) : ∃ τ', IsCosetExpansion S t Φ β (expDepth S t Φ β) τ' := by
  obtain ⟨k, τ', h'⟩ := exists_cosetExpansion hL S t Φ β h
  exact h'.exists_expDepth

end GlobalTheory.RowTest

end
