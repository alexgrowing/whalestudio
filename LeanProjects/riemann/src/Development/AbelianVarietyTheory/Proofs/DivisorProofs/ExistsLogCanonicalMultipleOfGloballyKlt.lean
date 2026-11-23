import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetOfFormOrdNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteType
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KltGlobal

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {n : ℕ}
  {Δ : X → ℚ} {η : RatForms p n} {x y : X} {m : ℕ} {g h : X.functionFieldˣ}

theorem compactSpace_of_isProjOver' {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Sp R}
    (hf : IsProjOver f) : CompactSpace Y := by
  obtain ⟨N, i, hi, rfl⟩ := hf
  have := isProper_str R N
  have : IsProper (i ≫ PSpace.str R N) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R N)

theorem unitAt_of_specializes' {z : X} {f : X.functionField} (hz : z ⤳ y) (hf : UnitAt y f) :
    UnitAt z f :=
  (unitAt_iff hf.ne_zero).2 ⟨regAt_of_specializes hz hf.regAt, regAt_of_specializes hz hf.inv.regAt⟩

theorem ord_eq_zero_of_unitAt' {E : DivOver p} {z : X} (hE : E.IsAt z) {u : X.functionFieldˣ}
    (hu : UnitAt z (u : X.functionField)) : E.ord u = 0 := by
  have h1 := (E.ord_nonneg_iff u).2 ((hE _).2 hu.regAt)
  have h2 := (E.ord_nonneg_iff u⁻¹).2 ((hE _).2 (by rw [Units.val_inv_eq_inv_val]; exact hu.inv.regAt))
  rw [E.ord_inv] at h2
  omega

theorem isLogEqn_pow' (hg : IsLogEqn p Δ η x m g) (r : ℕ) : IsLogEqn p Δ η x (m * r) (g ^ r) := by
  intro z hz E hE
  rw [E.ord_pow]
  push_cast
  rw [← hg z hz E hE]
  ring

theorem isLogEqn_of_unitAt' (hg : IsLogEqn p Δ η y m g)
    (hu : UnitAt y ((h : X.functionField) / g)) : IsLogEqn p Δ η y m h := by
  intro z hz E hE
  have h0 : E.ord (h * g⁻¹) = 0 := ord_eq_zero_of_unitAt' hE (by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
    exact unitAt_of_specializes' hz hu)
  have e : E.ord h = E.ord g := by
    have := E.ord_mul (h * g⁻¹) g
    rwa [inv_mul_cancel_right, h0, zero_add] at this
  rw [hg z hz E hE, e]

theorem unitAt_of_isLogEqn' [LocallyOfFiniteType p] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (hg : IsLogEqn p Δ η y m g) (hh : IsLogEqn p Δ η y m h) :
    UnitAt y ((h : X.functionField) / g) := by
  have h0 : ∀ z, z ⤳ y → ∀ F : DivOver p, F.IsAt z → F.ord (h * g⁻¹) = 0 := by
    intro z hz F hF
    have a := hg z hz F hF
    have b := hh z hz F hF
    rw [F.ord_mul, F.ord_inv]
    have : (F.ord g : ℚ) = F.ord h := a.symm.trans b
    have : F.ord g = F.ord h := by exact_mod_cast this
    omega
  have reg : ∀ v : X.functionFieldˣ, (∀ z, z ⤳ y → ∀ F : DivOver p, F.IsAt z → F.ord v = 0) →
      RegAt y (v : X.functionField) := fun v hv =>
    regAt_of_forall_coheight_eq_one fun z hz h1 =>
      have ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) h1
      (hF _).1 ((F.ord_nonneg_iff v).1 (hv z hz F hF).ge)
  have hne : (h : X.functionField) / g ≠ 0 := div_ne_zero h.ne_zero g.ne_zero
  have e1 : ((h * g⁻¹ : X.functionFieldˣ) : X.functionField) = h / g := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  have e2 : (((h * g⁻¹)⁻¹ : X.functionFieldˣ) : X.functionField) = ((h : X.functionField) / g)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, e1]
  refine (unitAt_iff hne).2 ⟨e1 ▸ reg _ h0, e2 ▸ reg _ fun z hz F hF => ?_⟩
  rw [F.ord_inv, h0 z hz F hF, neg_zero]

theorem exists_isLogEqn_of_form' [PerfectField k] [LocallyOfFiniteType p]
    (hn : topologicalKrullDim X = n) {η₀ : RatForms p n} (hη₀ : η₀ ≠ 0) (hη : η ≠ 0)
    (hg : IsLogEqn p Δ η x m g) : ∃ g' : X.functionFieldˣ, IsLogEqn p Δ η₀ x m g' := by
  by_cases hE : Nonempty (DivOver p)
  · obtain ⟨E⟩ := hE
    obtain ⟨ω, hω, f₀, e₀, -⟩ := E.isFormOrd_formOrd hn hη₀
    obtain ⟨f, e⟩ := (E.isFreeGen_toRat hω).2 η
    have hf : f ≠ 0 := fun h0 => hη (by rw [← e, h0]; exact zero_smul _ _)
    obtain ⟨c, hc⟩ : ∃ c : X.functionFieldˣ, η = (c : X.functionField) • η₀ :=
      ⟨Units.mk0 f hf * f₀⁻¹, by rw [e₀, smul_smul, ← e]; simp⟩
    refine ⟨g * (c ^ m)⁻¹, fun z hz F hF => ?_⟩
    have a := hg z hz F hF
    rw [hc, F.formOrd_smul hn hη₀] at a
    rw [F.ord_mul, F.ord_inv, F.ord_pow]
    push_cast at a ⊢
    linear_combination a
  · exact ⟨1, fun z _ F _ => (hE ⟨F⟩).elim⟩

theorem exists_nhds_isLogEqn' [IsLocallyNoetherian X] [CompactSpace X]
    (hfin : {z : X | ∃ E : DivOver p, E.IsAt z ∧ E.formOrd η ≠ 0}.Finite)
    (hΔ : (Function.support Δ).Finite) (hg : IsLogEqn p Δ η x m g) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, IsLogEqn p Δ η y m g := by
  set B : Set X := {z | ∃ E : DivOver p, E.IsAt z ∧ (m : ℚ) * (E.formOrd η + Δ z) ≠ E.ord g}
    with hB
  have hBf : B.Finite := by
    refine ((hfin.union hΔ).union (CartierDiv.principal g).finite_support_mult).subset ?_
    rintro z ⟨E, hE, hne⟩
    by_cases h1 : E.formOrd η = 0
    · by_cases h2 : Δ z = 0
      · right
        show (CartierDiv.principal g).mult z ≠ 0
        rw [(CartierDiv.isEqn_principal g z).mult_eq, ← hE.ord_eq]
        intro h3
        apply hne
        rw [h1, h2, h3]
        simp
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl ⟨E, hE, h1⟩)
  have key : ∀ y, y ∈ closure B → ∃ z ∈ B, z ⤳ y := by
    intro y hy
    have hc : closure B = ⋃ z ∈ B, closure {z} := by
      conv_lhs => rw [← Set.biUnion_of_singleton B]
      exact hBf.closure_biUnion _
    rw [hc] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨z, hz, hy⟩ := hy
    exact ⟨z, hz, specializes_iff_mem_closure.2 hy⟩
  refine ⟨⟨(closure B)ᶜ, isClosed_closure.isOpen_compl⟩, show x ∉ closure B from fun hx => ?_,
    fun y hy z hz E hE => ?_⟩
  · obtain ⟨z, ⟨E, hE, hne⟩, hzx⟩ := key x hx
    exact hne (hg z hzx E hE)
  · have hy' : y ∉ closure B := hy
    by_contra hne
    exact hy' (closure_mono (Set.singleton_subset_iff.2 (show z ∈ B from ⟨E, hE, hne⟩))
      (specializes_iff_mem_closure.1 hz))

end GlobalTheory.KltGlobal

namespace GlobalTheory.Discrepancy

open GlobalTheory.KltGlobal

theorem exists_isLogCanonicalMultiple_of_kltAt :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
      (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p →
      topologicalKrullDim X = n → ∀ Δ : X → ℚ, IsEffQDiv Δ → (∀ y, KltAt p n Δ y) →
      ∃ (m : ℕ) (G : CartierDiv X), 0 < m ∧ IsLogCanonicalMultiple p n Δ m G := by
  intro X _ _ _ p n hP hn Δ hΔ hklt
  classical
  haveI : CompactSpace X := compactSpace_of_isProjOver' hP
  haveI : LocallyOfFiniteType p := isProjOver_locallyOfFiniteType ℂ X p hP
  obtain ⟨η₀, -, -, hη₀, -, -, -⟩ := hklt (genericPoint X)
  have hfin := GlobalTheory.FormOrdFinite.finite_setOf_formOrd_ne_zero ℂ X p n hP hn η₀ hη₀
  have h1 : ∀ x, ∃ (m : ℕ) (g : X.functionFieldˣ) (U : X.Opens), 0 < m ∧ x ∈ U ∧
      ∀ y ∈ U, IsLogEqn p Δ η₀ y m g := by
    intro x
    obtain ⟨η, m, g, hη, hm, hg, -⟩ := hklt x
    obtain ⟨g', hg'⟩ := exists_isLogEqn_of_form' hn hη₀ hη hg
    obtain ⟨U, hU, hy⟩ := exists_nhds_isLogEqn' hfin hΔ.finite hg'
    exact ⟨m, g', U, hm, hU, hy⟩
  choose mm gg UU hm hU hy using h1
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (UU x : Set X))
    (fun x => (UU x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hU x⟩)
  set M := ∏ i ∈ t, mm i with hM
  have hM0 : 0 < M := Finset.prod_pos fun i _ => hm i
  have hMd : ∀ i ∈ t, mm i * (M / mm i) = M := fun i hi =>
    Nat.mul_div_cancel' (Finset.dvd_prod_of_mem _ hi)
  have sel : ∀ y : X, ∃ i ∈ t, y ∈ UU i := fun y => by
    have := ht (Set.mem_univ y)
    simpa using this
  choose s hs hsy using sel
  let e : X → X.functionFieldˣ := fun y => gg (s y) ^ (M / mm (s y))
  have he : ∀ y, ∀ w ∈ UU (s y), IsLogEqn p Δ η₀ w M (e y) := fun y w hw => by
    have := isLogEqn_pow' (hy (s y) w hw) (M / mm (s y))
    rwa [hMd _ (hs y)] at this
  let G : CartierDiv X := show cartierGroup X from
    ⟨fun y => germOf y (e y), fun x => ⟨UU (s x), hsy x, e x, fun y hy' =>
      germOf_eq_iff.2 (unitAt_of_isLogEqn' (he y y (hsy y)) (he x y hy'))⟩⟩
  refine ⟨M, G, hM0, η₀, hη₀, fun x g hg => ?_⟩
  have h0 : G.IsEqn x (e x) := rfl
  exact isLogEqn_of_unitAt' (he x x (hsy x)) (h0.iff_unitAt.1 hg)

end GlobalTheory.Discrepancy

example : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p →
  topologicalKrullDim X = n → ∀ Δ : X → ℚ, IsEffQDiv Δ → (∀ y, KltAt p n Δ y) →
  ∃ (m : ℕ) (G : CartierDiv X), 0 < m ∧ IsLogCanonicalMultiple p n Δ m G :=
  GlobalTheory.Discrepancy.exists_isLogCanonicalMultiple_of_kltAt
