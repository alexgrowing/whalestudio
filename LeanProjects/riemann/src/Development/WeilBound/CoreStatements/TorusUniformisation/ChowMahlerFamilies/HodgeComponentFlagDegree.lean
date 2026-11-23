import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCechNerveDiagonalIsoZeroOverBase
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.ComponentDegreeAlt

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {W : Type} [AddCommGroup W] [Module Ω W]

theorem wedge_ne_zero {r : ℕ} {b : Fin r → W} (hb : LinearIndependent Ω b) :
    exteriorPower.ιMulti Ω r b ≠ 0 := by
  have h := (exteriorPower.ιMulti_family_linearIndependent_field (n := r) hb).ne_zero
    (Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin r)).toOrderEmbedding)
  intro h0
  apply h
  simpa [exteriorPower.ιMulti_family] using h0

theorem unit_zpow {p : Cpt ξ} {u : Ω} (hu : unitAt ξ p u) (n : ℤ) : unitAt ξ p (u ^ n) := by
  cases n with
  | ofNat n => simpa using ZUnit.pow hu n
  | negSucc n => rw [zpow_negSucc]; exact ZUnit.inv (ZUnit.pow hu _)

theorem unit_prod {p : Cpt ξ} {I : Type} (s : Finset I) (u : I → Ω) (hu : ∀ i, unitAt ξ p (u i)) :
    unitAt ξ p (∏ i ∈ s, u i) :=
  Finset.prod_induction u (unitAt ξ p) (fun _ _ => ZUnit.mul) ZUnit.one (fun i _ => hu i)

theorem mul_mem_span {p : Cpt ξ} {u : Ω} (hu : u ∈ regAt ξ p) (t : Ω) :
    u * t ∈ Submodule.span (regAt ξ p) {t} :=
  Submodule.mem_span_singleton.2 ⟨⟨u, hu⟩, rfl⟩

theorem span_unit_mul {p : Cpt ξ} {u : Ω} (hu : unitAt ξ p u) (t : Ω) :
    Submodule.span (regAt ξ p) {u * t} = Submodule.span (regAt ξ p) {t} := by
  apply le_antisymm
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 (mul_mem_span hu.2.1 t)
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 ?_
    have := mul_mem_span hu.2.2 (u * t)
    rwa [inv_mul_cancel_left₀ hu.1] at this

theorem exists_gen_wedge {L : Lat ξ W} {r : ℕ} {b₀ : Fin r → W} (hb₀ : LinearIndependent Ω b₀)
    (hFl : L.IsFlagVBOn Set.univ b₀) (p : Cpt ξ) :
    ∃ t : Fin r → Ω, (∀ i, (L.gr b₀ i).IsGenAt p (t i)) ∧
      L.wedge r p = Submodule.span (regAt ξ p) {(∏ i, t i) • exteriorPower.ιMulti Ω r b₀} := by
  obtain ⟨U, hU, b, hbF, hbL⟩ := hFl p trivial
  have hfr : L.IsFrameAt b p := hbL p trivial hU
  choose c hc using FlagDet.exists_diag hbF
  refine ⟨c, fun i => FlagGrGen.gr_isGenAt X Ω ξ W L r b₀ b p i (c i) hb₀ hbF hfr (hc i), ?_⟩
  rw [Lat.wedge_eq_span_of_isFrameAt X Ω ξ W _ r _ p hfr,
    FlagDet.alt_triangular (exteriorPower.ιMulti Ω r (M := W)) b b₀ c hc]

theorem lineLat_eq {A B : Lat ξ W} {p q : ℕ} {a : ⋀[Ω]^p W} {b : ⋀[Ω]^q W} (ha : a ≠ 0) (hb : b ≠ 0)
    {x : Cpt ξ} {α β : Ω} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hA : A.wedge p x = Submodule.span (regAt ξ x) {α • a})
    (hB : B.wedge q x = Submodule.span (regAt ξ x) {β • b}) :
    lineLat A B p q a b x = Submodule.span (regAt ξ x) {α / β} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, ⟨α', β', hα', hβ', hA', hB', hf⟩, rfl⟩
    obtain ⟨u, hu, eu⟩ := ZUnit.exists_of_span_eq (smul_ne_zero hα' ha) (hA'.symm.trans hA)
    obtain ⟨v, hv, ev⟩ := ZUnit.exists_of_span_eq (smul_ne_zero hβ' hb) (hB'.symm.trans hB)
    rw [smul_smul] at eu ev
    have e1 : α' = u * α := smul_left_injective Ω ha eu
    have e2 : β' = v * β := smul_left_injective Ω hb ev
    have e3 : f = β' / α' := by rw [← hf]; field_simp
    have e4 : f⁻¹ = (u * v⁻¹) * (α / β) := by
      have := hu.1
      have := hv.1
      rw [e3, e1, e2]; field_simp
    rw [e4]
    exact mul_mem_span (mul_mem hu.2.1 hv.2.2) _
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span ?_)
    exact ⟨β / α, ⟨α, β, hα, hβ, hA, hB, div_mul_cancel₀ _ hα⟩, (inv_div _ _).symm⟩

theorem tens_unit_eq {Λ : Lat ξ Ω} {p : Cpt ξ} {t : Ω} (ht : Λ.IsGenAt p t) (n : ℤ) :
    Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = Submodule.span (regAt ξ p) {t ^ n} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨u, hu, eu⟩ := ZUnit.exists_of_span_eq (hs ()).1 ((hs ()).2.symm.trans ht.2)
    have e : ∏ i : Unit, s i ^ n = u ^ n * t ^ n := by
      rw [Fintype.prod_unique, ← mul_zpow]
      exact congrArg (· ^ n) eu
    rw [e]
    exact mul_mem_span (unit_zpow hu n).2.1 _
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span ?_)
    exact ⟨fun _ => t, fun _ => ht, by rw [Fintype.prod_unique]⟩

theorem zpow_finsum {a : Ω} (ha : a ≠ 0) {I : Type} (s : Finset I) (n : I → ℤ) :
    a ^ (∑ i ∈ s, n i) = ∏ i ∈ s, a ^ n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

end General

theorem prod_root {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {Ω : Type} [Field Ω] (t : ∀ s, Fin (labelRk D s) → Ω) (τ : CMType H) :
    ∏ i : Fin (D.p + D.q), t (HodgeCpt.rootIdx D (τ, i)).1 (HodgeCpt.rootIdx D (τ, i)).2 ^
      HodgeCpt.rootSgn D (τ, i) = (∏ i, t (.inl τ) i) / ∏ j, t (.inr τ) j := by
  rw [Fin.prod_univ_add, div_eq_mul_inv]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have h : ((Fin.castAdd D.q i : Fin (D.p + D.q)) : ℕ) < D.p := i.2
    have e : HodgeCpt.rootIdx D (τ, Fin.castAdd D.q i) = ⟨.inl τ, i⟩ := dif_pos h
    have e' : HodgeCpt.rootSgn D (τ, Fin.castAdd D.q i) = 1 := if_pos h
    rw [e, e', zpow_one]
  · rw [← Finset.prod_inv_distrib]
    refine Fintype.prod_equiv (Fin.revPerm (n := D.q)) _ _ fun j => ?_
    have h : ¬ ((Fin.natAdd D.p j : Fin (D.p + D.q)) : ℕ) < D.p := by simp
    have e : HodgeCpt.rootIdx D (τ, Fin.natAdd D.p j) = ⟨.inr τ, Fin.rev j⟩ := by
      refine (dif_neg h).trans ?_
      congr 1
      apply Fin.ext
      have hj : (j : ℕ) < D.q := j.2
      show D.p + D.q - 1 - (D.p + (j : ℕ)) = D.q - ((j : ℕ) + 1)
      omega
    have e' : HodgeCpt.rootSgn D (τ, Fin.natAdd D.p j) = -1 := if_neg h
    rw [e, e', zpow_neg_one]
    rfl

end PositivityTheory.Xgn.ComponentDegreeAlt

open PositivityTheory.Xgn.ComponentDegreeAlt in
theorem PositivityTheory.Xgn.hodge_component_flag_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H), Fl.RootLines xdeg e → (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsDegOn Set.univ y (∑ i, xdeg (τ, i)) (∏ i, e (τ, i)) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl xdeg e τ hR
  have hli : ∀ s, LinearIndependent Ω (Fl.b s) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => (hR (τ, i)).1, fun p _ cc hcc => ?_⟩
  choose t ht hw using fun s => exists_gen_wedge (hli s) (Fl.sub s) p
  have hy : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcc.1 k (Finset.mem_univ k)
  rw [lineLat_eq (wedge_ne_zero (hli _)) (wedge_ne_zero (hli _))
    (Finset.prod_ne_zero_iff.2 fun i _ => (ht _ i).1) (Finset.prod_ne_zero_iff.2 fun i _ => (ht _ i).1)
    (hw (.inl τ)) (hw (.inr τ)), ← prod_root D t τ]
  have hu : ∀ i : Fin (D.p + D.q), ∃ u : Ω, unitAt 𝔐.ξ p u ∧
      t (HodgeCpt.rootIdx D (τ, i)).1 (HodgeCpt.rootIdx D (τ, i)).2 ^ HodgeCpt.rootSgn D (τ, i) =
        u • (∏ k, y ⟨k, cc k⟩ ^ xdeg (τ, i) k) • e (τ, i) := fun i =>
    ZUnit.exists_of_span_eq (zpow_ne_zero _ (ht _ _).1)
      ((tens_unit_eq (ht _ _) _).symm.trans ((hR (τ, i)).2 p trivial cc hcc))
  choose u hu eu using hu
  have key : ∏ i : Fin (D.p + D.q), t (HodgeCpt.rootIdx D (τ, i)).1 (HodgeCpt.rootIdx D (τ, i)).2 ^
      HodgeCpt.rootSgn D (τ, i) =
      (∏ i, u i) * ((∏ k, y ⟨k, cc k⟩ ^ (∑ i, xdeg (τ, i)) k) • ∏ i, e (τ, i)) := by
    simp only [eu, smul_eq_mul, Finset.prod_mul_distrib, Finset.sum_apply, zpow_finsum (hy _)]
    rw [Finset.prod_comm]
  rw [key]
  exact span_unit_mul (unit_prod _ u hu) _
