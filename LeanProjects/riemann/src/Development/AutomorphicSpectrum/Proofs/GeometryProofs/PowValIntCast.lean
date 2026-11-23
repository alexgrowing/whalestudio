import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsHTAtIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualBC
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatPar
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverZpOfInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartIntegralStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct

noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open GlobalTheory.CompanionTheory.Ar.HTTie

theorem pow_val_intCast {G : Type} [Group G] (g : G) (N : ℕ) [NeZero N] (hg : g ^ N = 1) (j : ℤ) :
    g ^ (j : ZMod N).val = g ^ j := by
  have h : (((j : ZMod N).val : ℕ) : ℤ) = j % N := ZMod.val_intCast j
  rw [← zpow_natCast, h, ← zpow_eq_zpow_emod' j hg]

theorem cp_descend {A Ω : Type} [CommRing A] [Field Ω] [Algebra A Ω] (hinj : Function.Injective (algebraMap A Ω))
    (p : ℕ) (κ : A) (h : IsCp p (algebraMap A Ω κ)) :
    if p = 2 then κ = 4 else ∃ ζ : A, IsPrimitiveRoot ζ p ∧ κ = ζ - 1 := by
  unfold IsCp at h
  split_ifs at h ⊢
  · exact hinj (by rw [h, map_ofNat])
  · obtain ⟨ζ, h1, h2⟩ := h
    refine ⟨κ + 1, IsPrimitiveRoot.of_map_of_injective (f := algebraMap A Ω) ?_ hinj, by ring⟩
    rwa [map_add, map_one, h2, sub_add_cancel]

theorem exists_chart (h876 : type_of% @GlobalTheory.T.section_eq_zero_of_values) (h450 : type_of% @GlobalTheory.T.torsion_embedding_geometric_points)
    (h758 : type_of% @GlobalTheory.T.HTChartExists_holds) (h576 : type_of% @GlobalTheory.T.hodge_tate_chart_integral)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Scheme.{0}}
    [IsLocallyNoetherian X] (t : SAB H X) {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (hξ : IsCptGen ξ)
    (hall : ∀ q : X, genPt ξ ⤳ q)
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li)
    (hρ : M.IsActOf t.act.act ρ) (p m : ℕ) [Fact p.Prime] {ev : D.La → (Over.mk ξ ⟶ t.G)} {ζ₀ : Ωˣ}
    (hev : IsParam D t ξ (p ^ m) ev ζ₀) (hprop : IsProper (pullback.snd t.G.hom ξ))
    (hfull : FullTorsion t.G ξ (p ^ m)) (hrk : 2 * Module.finrank Ω Li = Module.finrank ℤ D.La)
    (u : Fin (D.p + D.q) → D.La) (hu : IsPolLattice (cmConj E) p D.EF u)
    (π : Multiplicative (Fin (D.p + D.q) → 𝓞 E) →* LevGrp D.La p m)
    (e : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ m))
    (hπ : ∀ z, π (Multiplicative.ofAdd z) = lev p m (∑ k, z k • u k))
    (he : ∀ z z', e z z' = ((D.EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ m)))
    (hsurj : Function.Surjective π)
    (hker : ∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = (p ^ m) • y')
    (halt : ∀ y, e y y = 0)
    (hadj : ∀ (a : 𝓞 E) (y z : Fin (D.p + D.q) → 𝓞 E),
      e (a • y) z = e y (RingOfIntegers.mapRingEquiv (cmConj E) a • z))
    (hes : ∀ φ : (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ m), ∃ y, e y = φ)
    (hei : ∀ y, e y = 0 → ∃ y', y = (p ^ m) • y')
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra A Ω]
    [IsFractionRing A Ω] (x : Sp A ⟶ X) (hx : spMap (algebraMap A Ω) ≫ x = ξ)
    (hsub : ∀ q : Cpt ξ, q.1 ∈ Set.range x → ∀ a, algebraMap A Ω a ∈ regAt ξ q) :
    ∃ Dc : HTChart A Ω (cmConj E) p m (D.p + D.q) (Module.Dual Ω Li), Dc.e = e ∧
      (∀ a w, Dc.ρΩ a w = w ∘ₗ ρ (H.bar a)) ∧
      (∀ w, w ∈ Dc.om ↔ ∀ q : Cpt ξ, q.1 ∈ Set.range x → w ∈ M.omLat q) ∧
      (∀ q : Cpt ξ, q.1 ∈ Set.range x →
        M.omLat q = Submodule.span (regAt ξ q) (Dc.om : Set (Module.Dual Ω Li))) ∧
      (∀ q : Cpt ξ, q.1 ∈ Set.range x → ∀ z w', M.IsHTAt t.PP.L (p ^ m) (ev (∑ k, z k • u k)) q w' ↔
        ∃ v ∈ M.omLat q, w' = Dc.h z + (p ^ m) • v) ∧
      ∀ κ : A, PointHT → IsCp p (algebraMap A Ω κ) → Dc.HasTestPoints κ := by
  have hinj := IsFractionRing.injective A Ω
  have : CharZero A := (algebraMap A Ω).charZero
  have hp := (Fact.out : p.Prime)
  have hn : p ^ m ≠ 0 := pow_ne_zero _ hp.ne_zero
  have : NeZero (p ^ m) := ⟨hn⟩
  have := t.semi.smooth
  have := t.semi.separated
  let κ : FractionRing A ≃+* Ω := (FractionRing.algEquiv A Ω).toRingEquiv
  have hκ : ∀ a, κ (algebraMap A _ a) = algebraMap A Ω a := (FractionRing.algEquiv A Ω).commutes
  have hκ' : κ.toRingHom.comp (algebraMap A (FractionRing A)) = algebraMap A Ω := RingHom.ext hκ
  have hx' : spMap (κ.toRingHom.comp (algebraMap A (FractionRing A))) ≫ x = ξ := by rw [hκ', hx]
  obtain ⟨Γ, i, htor, hpt, hact, hprop', htate⟩ := exists_chartGroup D t ξ h450 p m hev hprop hfull A x κ hx'
  have : Finite (LevGrp D.La p m) := by
    have := hu.finite
    have : Finite (D.La ⧸ LinearMap.range ((p ^ m) • (LinearMap.id : D.La →ₗ[ℤ] D.La))) := by
      refine Module.finite_of_fg_torsion _ fun a => ?_
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      refine ⟨⟨((p ^ m : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.2 hn)⟩, ?_⟩
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨a, (natCast_zsmul a (p ^ m)).symm⟩
    infer_instance
  obtain ⟨L₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X t.G A x
  obtain ⟨ρ₀, hρ₀, -⟩ := lieModel_exists_unique_act X t.G A x L₀ M₀ (𝓞 E) t.act.act t.act.hom t.act.one t.act.mul
    t.act.add
  have hfin : Module.Finite A L₀ := (lie_proj X t.G A x L₀ M₀).1
  obtain ⟨j₀, j, hj, hjj, hj₀, hspan, hrk₀⟩ : ∃ (j₀ : L₀ →+ Li) (j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li),
      IsBaseChange Ω j ∧ (∀ w b, j w (j₀ b) = algebraMap A Ω (w b)) ∧
      (∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left) ∧
      ((∀ w w' : Module.Dual Ω Li, (∀ b, w (j₀ b) = w' (j₀ b)) → w = w') ∧
        ∀ w : Module.Dual Ω Li, ∃ w' : L₀ →ₗ[A] Ω, ∀ b, w' b = w (j₀ b)) ∧
      Module.finrank Ω Li = Module.finrank A L₀ := by
    letI : Module A Li := Module.compHom Li (algebraMap A Ω)
    haveI : IsScalarTower A Ω Li := ⟨fun r a l => by rw [Algebra.smul_def, mul_smul]; rfl⟩
    obtain ⟨j₀, h1, h2⟩ := exists_lieBC M M₀ hx
    obtain ⟨j, h3, h4⟩ := exists_dualBC j₀ h1
    exact ⟨j₀.toAddMonoidHom, j, h3, h4, h2,
      ⟨fun w w' h => h1.algHom_ext _ _ h, fun w => ⟨w.restrictScalars A ∘ₗ j₀, fun _ => rfl⟩⟩, h1.finrank_eq⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Aˣ, algebraMap A Ω ζ = ζ₀ := by
    have h0 : (ζ₀ : Ω) ^ (p ^ m) = 1 := by rw [← Units.val_pow_eq_pow_val, hev.prim.pow_eq_one, Units.val_one]
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) (K := Ω)
      (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by rw [h0]; exact isIntegral_one))
    exact ⟨Units.ofPowEqOne a (p ^ m) (hinj (by rw [map_pow, ha, h0, map_one])) hn, ha⟩
  have hζ1 : ζ ^ (p ^ m) = 1 := Units.ext (hinj (by
    rw [Units.val_pow_eq_pow_val, map_pow, hζ, ← Units.val_pow_eq_pow_val, hev.prim.pow_eq_one]; simp))
  obtain ⟨Dc, hDe, hDc⟩ := h758 A Ω E (cmConj E) p m (D.p + D.q) _ Γ X t.G x i htor inferInstance t.act.act
    t.act.hom L₀ M₀ ρ₀ hρ₀ _ j hj π hsurj hker (fun a y => by
      rw [hπ, hπ, ← hact, Finset.smul_sum]
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul]) ζ hζ1 e halt hadj hes hei
  have hom := fun q hq w => mem_omLat_iff M M₀ hξ hinj hx j₀ hj₀ q hq (hsub q hq) w
  have hsm : ∀ (a : A) (w : Module.Dual Ω Li), a • w = algebraMap A Ω a • w := fun a w =>
    (algebraMap_smul Ω a w).symm
  refine ⟨Dc, hDe, fun a w => ?_, fun w => ⟨?_, fun h => ?_⟩, fun q hq => le_antisymm (fun w hw => ?_) ?_,
    fun q hq z w' => ?_, fun c hPt hc => ?_⟩
  · induction w using hj.inductionOn with
    | zero => simp
    | tmul w =>
      rw [hDc.2.1, ModelTest.bar_eq H]
      refine hspan.1 _ _ fun b => ?_
      have : ρ (H.bar a) (j₀ b) = j₀ (ρ₀ (H.bar a) b) := M.inj (Over.OverMorphism.ext (by
        rw [hρ, hj₀, hρ₀, Over.comp_left, Over.comp_left, hj₀, Category.assoc]))
      rw [LinearMap.comp_apply, this, hjj, hjj]; rfl
    | smul s w ih => rw [map_smul, ih, LinearMap.smul_comp]
    | add w w' ih ih' => rw [map_add, ih, ih', LinearMap.add_comp]
  · rw [hDc.1]
    rintro ⟨w₀, rfl⟩ q hq
    exact (hom q hq _).2 fun b => by rw [hjj]; exact hsub q hq _
  · obtain ⟨w₁, hw₁⟩ := hspan.2 w
    obtain ⟨v, w₀, h1, h2, h3⟩ := clear_denom hinj (algebraMap A Ω).range
      (by rintro _ ⟨a, rfl⟩; exact ⟨1, a, by simp, by simp, by simp⟩) w₁ (fun b => by
        let I : Ideal A := (Submodule.span A {(1 : Ω)}).comap (LinearMap.toSpanSingleton A Ω (w₁ b))
        by_cases hI : I = ⊤
        · have h1 : (1 : A) ∈ I := hI ▸ Submodule.mem_top
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
          exact ⟨a, by simpa [Algebra.smul_def] using ha⟩
        · obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal I hI
          let P' : PrimeSpectrum A := ⟨P, hP.isPrime⟩
          obtain ⟨s, a, hs, hsa⟩ := (regAt_frac hξ hinj hx P' ⟨x P', hall _⟩ rfl (hsub _ ⟨P', rfl⟩)).2 (w₁ b)
            (by rw [hw₁]; exact (hom _ ⟨P', rfl⟩ w).1 (h _ ⟨P', rfl⟩) b)
          exact absurd (hle (Submodule.mem_span_singleton.2 ⟨a, by simp [Algebra.smul_def, hsa]⟩)) hs)
    obtain ⟨v', hv'⟩ := h2
    rw [hDc.1]
    refine ⟨v' • w₀, hspan.1 _ _ fun b => ?_⟩
    rw [hjj, LinearMap.smul_apply, smul_eq_mul, map_mul, h3, hv', ← _root_.mul_assoc, inv_mul_cancel₀ h1,
      _root_.one_mul, hw₁]
  · obtain ⟨w₁, hw₁⟩ := hspan.2 w
    obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum A, x P = q.1 := hq
    have hf := regAt_frac hξ hinj hx P q hP (hsub q ⟨P, hP⟩)
    obtain ⟨v, w₀, h1, h2, h3⟩ := clear_denom hinj (regAt ξ q) (fun b hb => by
      obtain ⟨s, a, hs, hsa⟩ := hf.2 b hb
      exact ⟨s, a, (hf.1 s hs).1, (hf.1 s hs).2, hsa⟩) w₁ (fun b => by rw [hw₁]; exact (hom q ⟨P, hP⟩ w).1 hw b)
    have : w = (⟨_, h2⟩ : regAt ξ q) • j w₀ := hspan.1 _ _ fun b => by
      show _ = (algebraMap A Ω v)⁻¹ * j w₀ (j₀ b)
      rw [hjj, h3, ← _root_.mul_assoc, inv_mul_cancel₀ h1, _root_.one_mul, hw₁]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by rw [hDc.1]; exact ⟨w₀, rfl⟩))
  · rw [Submodule.span_le, hDc.1]
    rintro _ ⟨w₀, rfl⟩
    exact (hom q hq _).2 fun b => by rw [hjj]; exact hsub q hq _
  · obtain ⟨χ, w₀, hχ, hh, hHT⟩ := hDc.2.2 z
    refine isHTAt_iff lie_proj h876 hξ t.PP.L hn hfull M x κ hx' Γ i htor M₀ j₀ (by rw [hκ']; exact hj₀) _ χ w₀ _
      (fun s k _ _ a xk gk c h1 h2 => ?_) hHT (fun b => by rw [hh, hjj, hκ]) q hq
      (fun a => by rw [hκ]; exact hsub q hq a) w'
    obtain ⟨z', rfl⟩ := hsurj s
    have hz' : z' = Multiplicative.ofAdd (Multiplicative.toAdd z') := rfl
    rw [hz'] at h2 ⊢
    rw [hπ] at h2
    rw [hev.weil _ _ k a xk gk c h1 (h2.trans (congrArg (spMap a ≫ ·) (hpt _))), hχ, hDe, he, hκ,
      ← pow_val_intCast ζ₀ (p ^ m) hev.prim.pow_eq_one, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
      map_pow, map_pow, hζ]
  · refine h576 hPt E H D p A Ω m _ Dc u hu X t x Γ i htor L₀ M₀ ρ₀ hρ₀ j hj π ζ c hDc hπ (by rw [hDe]; exact he)
      (by rw [← hrk₀, hrk]) hprop' (fun k _ _ f => ?_) (cp_descend hinj p c hc)
    obtain ⟨I, h1, h2⟩ := htate k f
    exact ⟨I, by rw [h1, ← hζ, ← hκ, RingEquiv.symm_apply_apply], h2⟩

end GlobalTheory.CompanionTheory.HtLink
