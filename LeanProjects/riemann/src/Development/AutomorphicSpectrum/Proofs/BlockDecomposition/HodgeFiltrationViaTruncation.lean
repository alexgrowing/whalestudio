import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClassStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationPropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.KIso

section Abstract
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem restrict_bij (F : C ⥤ ModuleCat.{0} R) (Q : ObjectProperty C) (hQ : ∀ T, Q T) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict F Q.ι).pull j) := by
  refine CrystallineSemistableComparison.P.mapH_bij (CH.Mor.restrict F Q.ι).hom (fun n => ⟨fun f f' h => ?_, fun g => ?_⟩) j
  · funext s
    exact congrFun h (s ⋙ Q.lift (𝟭 C) hQ)
  · exact ⟨fun s => g (s ⋙ Q.lift (𝟭 C) hQ), rfl⟩

variable {A : C ⥤ CommAlgCat.{0} R}

noncomputable def incB (a : IdF A) : CH.Mor (sq a (IdF.bot A)) (CH.modF A) (RingHom.id R) where
  G := 𝟭 C
  τ T := (AlgEquiv.quotientBot R (A.obj T)).toLinearMap ∘ₗ (sqM a (IdF.bot A) T).subtype
  nat φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

theorem incB_mem (a : IdF A) {T : C} (x : (sq a (IdF.bot A)).obj T) : (incB a).τ T x ∈ a.S T := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact hy

theorem ses (a₀ a : IdF A) (h0 : ∀ T, a₀.S T = ⊤) :
    (∀ n, Function.Injective ((incB a).hom.f n)) ∧
    (∀ n, Function.Exact ((incB a).hom.f n) ((toSq a₀ a h0).hom.f n)) ∧
    ∀ n, Function.Surjective ((toSq a₀ a h0).hom.f n) := by
  refine ⟨fun n x y hxy => ?_, fun n y => ⟨fun hy => ?_, ?_⟩, fun n y => ?_⟩
  · funext s
    have h : (incB a).τ _ (x (s ⋙ 𝟭 C)) = (incB a).τ _ (y (s ⋙ 𝟭 C)) := congrFun hxy s
    exact Subtype.ext ((AlgEquiv.quotientBot R _).injective h)
  · have hm : ∀ s : ComposableArrows C n, (show A.obj (s.obj (Fin.last n)) from y s) ∈ a.S (s.obj (Fin.last n)) := fun s => by
      have h := congrArg Subtype.val (congrFun hy s)
      exact Ideal.Quotient.eq_zero_iff_mem.1 h
    exact ⟨fun s => sqMk a (IdF.bot A) _ (hm s), rfl⟩
  · rintro ⟨x, rfl⟩
    funext s
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (incB_mem a (x (s ⋙ 𝟭 C))))
  · have hm : ∀ s : ComposableArrows C n, ∃ t : A.obj (s.obj (Fin.last n)), Ideal.Quotient.mk _ t = (show sqM a₀ a _ from y s).1 :=
      fun s => Ideal.Quotient.mk_surjective _
    choose t ht using hm
    exact ⟨t, funext fun s => Subtype.ext (ht s)⟩

theorem pull_eq_zero_iff (a₀ a : IdF A) (h0 : ∀ T, a₀.S T = ⊤) (j : ℕ) (x : CH.H (CH.modF A) j) :
    (toSq a₀ a h0).pull j x = 0 ↔ ∃ (z : CH.Cn (CH.modF A) j) (hz : CH.d (CH.modF A) j z = 0),
      x = (CH.cx (CH.modF A)).cls z hz ∧ ∀ s : ComposableArrows C j, (show A.obj (s.obj (Fin.last j)) from z s) ∈ a.S (s.obj (Fin.last j)) := by
  obtain ⟨hf, hfg, hg⟩ := ses a₀ a h0
  obtain ⟨δ, -, -, hex, -, -⟩ := CrystallineSemistableComparison.P.les _ _ hf hfg hg
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := (hex j x).1 h
    obtain ⟨y, hy, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 y
    exact ⟨(incB a).hom.f j y, CrystallineSemistableComparison.CechClassBoundaries.cyc (incB a).hom y hy, rfl, fun s => incB_mem a (y (s ⋙ 𝟭 C))⟩
  · rintro ⟨z, hz, rfl, hs⟩
    have e : (toSq a₀ a h0).hom.f j z = 0 := funext fun s => Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (hs s))
    change (CH.cx _).cls ((toSq a₀ a h0).hom.f j z) _ = 0
    simp only [e]
    rfl

theorem toSq_bij (a₀ a : IdF A) (h0 : ∀ T, a₀.S T = ⊤) (hv : ∀ j, Subsingleton (CH.H (sq a (IdF.bot A)) j)) (j : ℕ) :
    Function.Bijective ((toSq a₀ a h0).pull j) := by
  obtain ⟨hf, hfg, hg⟩ := ses a₀ a h0
  obtain ⟨δ, -, -, hex, hex2, -⟩ := CrystallineSemistableComparison.P.les _ _ hf hfg hg
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hex j x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    obtain ⟨x, hx⟩ := (hex2 j y).1 ((hv (j + 1)).elim _ _)
    exact ⟨x, hx⟩

theorem toSq_bij_bot (a₀ b : IdF A) (h0 : ∀ T, a₀.S T = ⊤) (hb : ∀ T, b.S T = ⊥) (j : ℕ) :
    Function.Bijective ((toSq a₀ b h0).pull j) := by
  refine CrystallineSemistableComparison.P.mapH_bij (toSq a₀ b h0).hom (fun n => ⟨fun f f' h => ?_, (ses a₀ b h0).2.2 n⟩) j
  funext s
  have h1 := congrArg Subtype.val (congrFun h s)
  have h2 := Ideal.Quotient.eq.1 h1
  rw [hb] at h2
  exact sub_eq_zero.1 h2

end Abstract

section Concrete
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem dividedPowerFiltration_bot {r : ℕ} (hr : 1 ≤ r) : pdP (dividedPowersBot K) r = ⊥ := by
  refine Ideal.span_eq_bot.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have h : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra h
    push Not at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by simpa using h)
    omega
  obtain ⟨p, hp, h0⟩ := h
  refine List.prod_eq_zero (List.mem_map.2 ⟨p, hp, ?_⟩)
  have e : p.2 = 0 := hl p hp
  rw [e]
  exact (dividedPowersBot K).dpow_eval_zero h0

theorem tfBase [CharZero K] {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot K) 1 s where
  nil := dividedPowerFiltration_bot hs
  tf r x h := by simpa using h
  dv n hn := ⟨0, (n : K)⁻¹, by
    have : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
    simp [this]⟩

theorem dpow_mem_pow {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B))
    (n : ℕ) {x : B} (hx : x ∈ J) : δ.dpow n x ∈ J ^ n := by
  obtain ⟨u, hu⟩ := hu n.factorial (Nat.factorial_ne_zero n)
  have h := δ.factorial_mul_dpow_eq_pow (n := n) hx
  have e : δ.dpow n x = (↑u⁻¹ : B) * x ^ n := by
    rw [← h, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hx n)

theorem dividedPowerFiltration_le_pow {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B))
    (r : ℕ) : pdP δ r ≤ J ^ r := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have key : ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ J) →
      (l.map fun p => δ.dpow p.1 p.2).prod ∈ J ^ (l.map Prod.fst).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih =>
      intro h
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [pow_add]
      exact Ideal.mul_mem_mul (dpow_mem_pow δ hu _ (h a (by simp))) (ih fun p hp => h p (by simp [hp]))
  exact Ideal.pow_le_pow_right hs (key l hl)

theorem pdPow_nil [CharZero K] (T : Thick (nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥))) : ∃ N, T.pdPow N = ⊥ := by
  obtain ⟨N, hN⟩ := T.adm.2 rfl
  refine ⟨N, le_bot_iff.1 ?_⟩
  have hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : T.B) := fun n hn => by
    have h : IsUnit (n : K) := (Nat.cast_ne_zero.2 hn : (n : K) ≠ 0).isUnit
    simpa using h.map T.i
  have := dividedPowerFiltration_le_pow T.δ hu N
  rw [hN] at this
  exact this

omit [Field K] in
theorem inU_top {X : Scheme.{0}} {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (T : Thick (nlFun γ p X q κ)) : InU ⊤ T := le_of_eq rfl

end Concrete

section Loc
variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

local notation "LL" => nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)
local notation "TFs" => (TF 1 : ℕ → ObjectProperty (Thick (nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥))))

theorem loc_vanish (hG : KH.LocGr) (hP : KH.PolyTf) {V : X.Opens} {d : ℕ} (c : Coord q V d) (r s' : ℕ) (hd : d < r)
    (hs : r + 1 ≤ s') (j : ℕ) : Subsingleton (CH.H (gr (sFil (St (TFs s') {V})) (r : ℤ)) j) := by
  have hb : TFBase (dividedPowersBot K) 1 s' := tfBase (by omega)
  obtain ⟨c', e, hTF, -, -, -⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := K) (R := K) (dividedPowersBot K) 1 s' hb q (Ideal.Quotient.mk ⊥)
    (fun a => rfl) c
  have hgood := GlobalTheory.T.chart_is_good c'
  have hQ : ∀ T, St (TFs s') {V} T → InU V T := by
    rintro T ⟨-, W, hW, h⟩
    rw [Set.mem_singleton_iff.1 hW] at h
    exact h
  have hD : St (TFs s') {V} c'.D := ⟨hTF, V, rfl, c'.inV⟩
  obtain ⟨hpow, hc⟩ := GlobalTheory.T.chart_divided_powers_graded_constant c' hgood _ hQ hD
  obtain ⟨PQ, hPQ⟩ := hP (dividedPowersBot K) q (Ideal.Quotient.mk ⊥) 1 s' {V}
  have hF := GlobalTheory.T.sheaf_filtration_property (St (TFs s') {V})
  have key := hG PQ hF (c'.frame hgood _ hQ hD) (fun T => ((c'.frame hgood _ hQ hD).ne T).some) hc (r : ℤ)
    (fun r' hr' => (hPQ r' (by omega)).1) j
  rcases lt_or_ge (r : ℤ) (j : ℤ) with hlt | hge
  · exact key.1 hlt
  obtain ⟨qq, hq⟩ : ∃ qq : ℕ, (r : ℤ) = j + qq := ⟨r - j, by omega⟩
  have hrep := (key.2 qq hq).1
  have hz : ∀ cl : CH.H (gr (sFil (St (TFs s') {V})) (r : ℤ)) j, cl = 0 := by
    intro cl
    obtain ⟨x, hx, f, hf, rfl, hv⟩ := hrep cl
    have hx0 : ∀ I, x I = 0 := by
      intro I
      have hjd : j ≤ d := by simpa using Fintype.card_le_of_injective _ I.2.injective
      have hq1 : 1 ≤ qq := by omega
      have h2 : (show c'.D.B from x I) ∈ c'.D.pdPow ((qq : ℤ).toNat) := hx I
      rw [Int.toNat_natCast, hpow, dividedPowerFiltration_bot hq1, Ideal.map_bot] at h2
      exact Ideal.mem_bot.1 h2
    have hf0 : f = 0 := by
      funext s
      refine Subtype.ext ((hv s).trans ?_)
      beta_reduce
      rw [Finset.sum_eq_zero fun I _ => ?_, map_zero]
      · rfl
      · rw [hx0 I]
        simp [Frame.form]
    subst hf0
    rfl
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem glob_vanish (hG : KH.LocGr) (hP : KH.PolyTf) (hV : KH.GlobVanSt) (U : Cov q) (r s' : ℕ) (hd : ∀ α, U.d α < r)
    (hs : r + 1 ≤ s') (j : ℕ) :
    Subsingleton (HU (sq (thFil LL (r : ℤ)) (thFil LL ((r : ℤ) + 1))) (St (TFs s') (Set.range U.U)) j) := by
  refine (hV (sq (thFil LL (r : ℤ)) (thFil LL ((r : ℤ) + 1))) (TFs s') U.U 0).2.1 (fun S hS j => ?_) j
  obtain ⟨α, hα⟩ := id hS
  obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα) (U.inter S hS)
  exact loc_vanish q hG hP c' r s' (hd α) hs j

omit [CharZero K] in
theorem all_top (T : Thick LL) : St (⊤ : ObjectProperty (Thick LL)) {⊤} T := ⟨trivial, ⊤, rfl, inU_top T⟩

theorem thick_vanish (hG : KH.LocGr) (hP : KH.PolyTf) (hV : KH.GlobVanSt) (U : Cov q) (r : ℕ) (hd : ∀ α, U.d α < r)
    (j : ℕ) : Subsingleton (CH.H (sq (thFil LL (r : ℤ)) (thFil LL ((r : ℤ) + 1))) j) := by
  have h1 : St (TFs (r + 1)) {⊤} ≤ St (⊤ : ObjectProperty (Thick LL)) {⊤} := fun T h => ⟨trivial, h.2⟩
  have h2 : St (TFs (r + 1)) (Set.range U.U) ≤ St (TFs (r + 1)) {⊤} := fun T h => ⟨h.1, ⊤, rfl, inU_top T⟩
  have hc : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup (Set.range U.U) := by
    intro W hW
    rw [Set.mem_singleton_iff.1 hW, sSup_range, U.cover]
  have b1 := GlobalTheory.T.filtered_cohomology_restriction_bijective (⊤ : ObjectProperty (Thick LL)) 1 (r + 1) (Or.inl ⟨rfl, rfl⟩) {⊤} h1 (r : ℤ) ((r : ℤ) + 1)
    (by push_cast; omega) j
  have b2 := (GlobalTheory.T.cech_refinement_cohomology_bijective (TFs (r + 1)) (Or.inl ⟨rfl, 1, r + 1, rfl⟩) (Set.range U.U) {⊤} h2 hc j).1 (r : ℤ) ((r : ℤ) + 1)
  have b0 := restrict_bij (sq (thFil LL (r : ℤ)) (thFil LL ((r : ℤ) + 1))) (St (⊤ : ObjectProperty (Thick LL)) {⊤})
    (all_top q) j
  have : Subsingleton (CH.H (sq (sFil (St (TFs (r + 1)) (Set.range U.U)) (r : ℤ))
      (sFil (St (TFs (r + 1)) (Set.range U.U)) ((r : ℤ) + 1))) j) :=
    glob_vanish q hG hP hV U r (r + 1) hd le_rfl j
  exact (b2.1.comp (b1.1.comp b0.1)).subsingleton

theorem tower_vanish (hG : KH.LocGr) (hP : KH.PolyTf) (hV : KH.GlobVanSt) (U : Cov q) (s : ℕ) (hd : ∀ α, U.d α < s)
    (j : ℕ) : Subsingleton (CH.H (sq (thFil LL (s : ℤ)) (IdF.bot (thA LL))) j) := by
  refine GlobalTheory.T.cohomology_vanishing_along_ideal_filtration (fun k => thFil LL ((s + k : ℕ) : ℤ)) (fun k T => ?_) (fun T => ?_) (fun k j => ?_) j
  · exact T.pdPow_anti (by simp)
  · obtain ⟨N, hN⟩ := pdPow_nil q T
    refine ⟨N, le_bot_iff.1 ?_⟩
    rw [← hN]
    exact T.pdPow_anti (by omega)
  · have e : (((s + (k + 1) : ℕ)) : ℤ) = ((s + k : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [e]
    exact thick_vanish q hG hP hV U (s + k) (fun α => (hd α).trans_le (by omega)) j

omit [CharZero K] in
theorem top_ge (s : ℕ) : St (TFs s) {⊤} ≤ St (⊤ : ObjectProperty (Thick LL)) {⊤} := fun _ h => ⟨trivial, h.2⟩

omit [CharZero K] in
theorem st_le (s : ℕ) (𝒱 : Set X.Opens) : St (TFs s) 𝒱 ≤ St (TFs s) {⊤} := fun T h => ⟨h.1, ⊤, rfl, inU_top T⟩

noncomputable def chain (s : ℕ) (𝒱 : Set X.Opens) (r r' : ℤ) (j : ℕ) (y : CH.H (sq (thFil LL r) (thFil LL r')) j) :
    CH.H (sq (sFil (St (TFs s) 𝒱) r) (sFil (St (TFs s) 𝒱) r')) j :=
  ((incl (st_le q s 𝒱)).sq (incl_fil _ r) (incl_fil _ r')).pull j
    (((incl (top_ge q s)).sq (incl_fil _ r) (incl_fil _ r')).pull j
      ((CH.Mor.restrict (sq (thFil LL r) (thFil LL r')) (St (⊤ : ObjectProperty (Thick LL)) {⊤}).ι).pull j y))

omit [CharZero K] in
theorem chain_zero (s : ℕ) (𝒱 : Set X.Opens) (r r' : ℤ) (j : ℕ) : chain q s 𝒱 r r' j 0 = 0 := by
  simp only [chain, map_zero]

omit [CharZero K] in
theorem chain_bij (s : ℕ) (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (r r' : ℤ) (hr : r' ≤ s) (j : ℕ) :
    Function.Bijective (chain q s 𝒱 r r' j) := by
  have hc : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup 𝒱 := by
    intro W hW
    rw [Set.mem_singleton_iff.1 hW, h𝒱]
  have b1 := GlobalTheory.T.filtered_cohomology_restriction_bijective (⊤ : ObjectProperty (Thick LL)) 1 s (Or.inl ⟨rfl, rfl⟩) {⊤} (top_ge q s) r r' hr j
  have b2 := (GlobalTheory.T.cech_refinement_cohomology_bijective (TFs s) (Or.inl ⟨rfl, 1, s, rfl⟩) 𝒱 {⊤} (st_le q s 𝒱) hc j).1 r r'
  have b0 := restrict_bij (sq (thFil LL r) (thFil LL r')) (St (⊤ : ObjectProperty (Thick LL)) {⊤}) (all_top q) j
  exact b2.comp (b1.comp b0)

omit [CharZero K] in
theorem chain_comm (s : ℕ) (𝒱 : Set X.Opens) (r : ℤ) (j : ℕ) (x : CH.H (CH.modF (thA LL)) j) :
    chain q s 𝒱 0 r j ((toSq (thFil LL 0) (thFil LL r) fun T => T.pdPow_zero).pull j x) =
      (toSq (sFil (St (TFs s) 𝒱) 0) (sFil (St (TFs s) 𝒱) r) fun T => T.obj.pdPow_zero).pull j
        ((CH.Mor.restrict (CH.modF (thA LL)) (St (TFs s) 𝒱).ι).pull j x) := by
  obtain ⟨z, hz, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 x
  rfl

omit [CharZero K] in
theorem fil_iff (j r : ℕ) (y : CH.H (CH.modF (thA LL)) j) :
    (show HdR q j from y) ∈ FilR q j r ↔ (toSq (thFil LL 0) (thFil LL (r : ℤ)) fun T => T.pdPow_zero).pull j y = 0 := by
  rw [pull_eq_zero_iff]
  constructor
  · rintro ⟨z, hz, hs⟩
    exact ⟨z.1, z.2, hz.symm, fun s => by
      change _ ∈ (s.obj (Fin.last j)).pdPow ((r : ℤ).toNat)
      rw [Int.toNat_natCast]
      exact hs s⟩
  · rintro ⟨z, hz, rfl, hs⟩
    refine ⟨⟨z, hz⟩, rfl, fun s => ?_⟩
    have h := hs s
    change _ ∈ (s.obj (Fin.last j)).pdPow ((r : ℤ).toNat) at h
    rw [Int.toNat_natCast] at h
    exact h

end Loc

theorem k_iso : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.GrAff → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (s : ℕ)
    (hs : ∀ α, U.d α < s) (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (j : ℕ), Function.Bijective (resK q (KS q s 𝒱) j) ∧
      ∀ r ≤ s, ∀ x : HdR q j, x ∈ FilR q j r ↔ quoK q (KS q s 𝒱) r j x = 0 := by
  intro hG _ hP _ hV _ K _ _ X q U s hs 𝒱 h𝒱 j
  refine ⟨?_, fun r hr x => ?_⟩
  · have hA := (chain_bij q s 𝒱 h𝒱 0 (s : ℤ) le_rfl j).comp
      (toSq_bij _ _ (fun T => T.pdPow_zero) (tower_vanish q hG hP hV U s hs) j)
    have hB := toSq_bij_bot (sFil (KS q s 𝒱) 0) (sFil (KS q s 𝒱) (s : ℤ)) (fun T => T.obj.pdPow_zero)
      (fun T => by
        have h := T.property.1.1
        change T.obj.pdPow ((s : ℤ).toNat) = ⊥
        rw [Int.toNat_natCast]
        exact h) j
    refine (Function.Bijective.of_comp_iff' hB _).1 ?_
    have e : ∀ x : HdR q j, (toSq (sFil (KS q s 𝒱) 0) (sFil (KS q s 𝒱) (s : ℤ)) fun T => T.obj.pdPow_zero).pull j
        (resK q (KS q s 𝒱) j x) = chain q s 𝒱 0 (s : ℤ) j
        ((toSq (thFil _ 0) (thFil _ (s : ℤ)) fun T => T.pdPow_zero).pull j x) :=
      fun x => (chain_comm q s 𝒱 (s : ℤ) j x).symm
    refine ⟨fun a b hab => hA.1 ?_, fun y => ?_⟩
    · exact (e a).symm.trans (hab.trans (e b))
    · obtain ⟨x, hx⟩ := hA.2 y
      exact ⟨x, (e x).trans hx⟩
  · have e : quoK q (KS q s 𝒱) r j x = chain q s 𝒱 0 (r : ℤ) j
        ((toSq (thFil _ 0) (thFil _ (r : ℤ)) fun T => T.pdPow_zero).pull j x) := (chain_comm q s 𝒱 (r : ℤ) j x).symm
    rw [e, ← chain_zero q s 𝒱 0 (r : ℤ) j, (chain_bij q s 𝒱 h𝒱 0 (r : ℤ) (by exact_mod_cast hr) j).1.eq_iff]
    exact fil_iff q j r x

end GlobalTheory.CompanionTheory.KIso
