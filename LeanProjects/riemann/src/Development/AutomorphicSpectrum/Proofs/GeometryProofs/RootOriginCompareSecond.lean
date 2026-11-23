import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProjectStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagCompareStatement
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplierLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BadExists

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.JoinPts

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_zero_of_mem (y : (Σ k, ι k) → Ω) {g : MRing ι} (h : g ∈ mCoordIdeal y) : aeval y g = 0 := by
  have h0 : mConeMap y g = 0 := (RingHom.mem_ker).1 h
  have e : ((aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ).comp (mConeMap y) =
      aeval y := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap]
  rw [← e, AlgHom.comp_apply, h0, map_zero]

theorem aeval_map_hom {Ω' : Type} [Field Ω'] (i : Ω →+* Ω') (y : (Σ k, ι k) → Ω) (g : MRing ι) :
    aeval (fun p => i (y p)) g = i (aeval y g) := by
  have e : (aeval (fun p => i (y p)) : MRing ι →ₐ[ℤ] Ω') = (i.toIntAlgHom).comp (aeval y) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp
  rw [e]
  rfl

theorem cross_mem (y : (Σ k, ι k) → Ω) (p q p' q' : Σ k, ι k) (hp : p'.1 = p.1) (hq : q'.1 = q.1)
    (h : y p * y q' = y p' * y q) :
    (X p * X q' - X p' * X q : MRing ι) ∈ mCoordIdeal y := by
  refine (RingHom.mem_ker).2 ?_
  have e : (C (y p) * C (y q') : MvPolynomial K Ω) = C (y p') * C (y q) := by
    rw [← C_mul, ← C_mul, h]
  have hx : mConeMap y (X p * X q' - X p' * X q : MRing ι) =
      C (y p) * X p.1 * (C (y q') * X q'.1) - C (y p') * X p'.1 * (C (y q) * X q.1) := by
    simp [mConeMap]
  rw [hx, hp, hq]
  linear_combination (X p.1 * X q.1) * e

theorem exists_smul_of_cross {κ : Type} {u v : κ → ℂ} (hv : v ≠ 0) (h : ∀ a b, u a * v b = u b * v a) :
    ∃ t : ℂ, u = t • v := by
  obtain ⟨b, hb⟩ := Function.ne_iff.1 hv
  have hb' : v b ≠ 0 := hb
  refine ⟨u b / v b, funext fun a => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  exact h a b

end Forms

theorem coordsAt_smul {X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X'} {K : Type}
    {ι : K → Type} {y : (Σ k, ι k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X'} {w : (Σ k, ι k) → ℂ}
    (h : CoordsAt ξ y z w) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : CoordsAt ξ y z (fun p => c p.1 * w p) := by
  refine ⟨fun k => ?_, fun k a ha => ?_⟩
  · obtain ⟨a, ha⟩ := h.1 k
    exact ⟨a, (isUnit_iff_ne_zero.2 (hc k)).mul ha⟩
  · have ha' : IsUnit (w ⟨k, a⟩) := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul ha.ne_zero)
    obtain ⟨hy, hr⟩ := h.2 k a ha'
    refine ⟨hy, fun i => ?_⟩
    obtain ⟨r, h1, h2⟩ := hr i
    refine ⟨r, h1, ?_⟩
    show c k * w ⟨k, i⟩ = r * (c k * w ⟨k, a⟩)
    rw [h2]
    ring

section Origin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {M : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}

theorem mono_coeff (c : Coeff l) : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { }
  have := IsPreimmersion.of_isLocalization (S := c.F) (nonZeroDivisors (𝓞 c.F))
  exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F))))

theorem exists_form (o : RootOrigin Y S M Fx) :
    ∃ b : MRing M.ι, aeval M.y b ≠ 0 ∧ ∀ w ∈ mcPts M.P, aeval w b ≠ 0 →
      ∃ z : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X, CoordsAt o.𝔐.ξ M.y z w ∧ o.𝔐.Interior z := by
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨-, ⟨x, hx⟩, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c (𝓞 c.F) _ Y S M.Ω M.K M.ι M.y o.𝔐 hinj
  obtain ⟨b, d, hd, hb, hw⟩ := GlobalTheory.T.hodge_cpt_multihomog_form E H D l Xo c (𝓞 c.F) _ Y S M.Ω M.K M.ι M.y o.𝔐 x hx (mono_coeff c)
  refine ⟨b, fun h => hb (Small.LineModel.mem_of_aeval M.y hd h), fun w hw' hne => hw w hw' ?_⟩
  rw [Cmp.evC, Small.LineModel.eval_map_eq]
  exact hne

theorem exists_lift (o : RootOrigin Y S M Fx) (hJ : o.Re.J = ⊤) {w : (Σ k, M.ι k) → ℂ} (hw : w ∈ mcPts M.P)
    {z : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X} (hz : CoordsAt o.𝔐.ξ M.y z w) (hI : o.𝔐.Interior z) :
    ∃ x : o.Re.R.X, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) w ∧ o.Re.π x ∈ Sys.open' ∧
      ∃ t : ℂ, Fx.pt (o.Re.π x) = t • fun a => w ⟨o.k₀, o.ix a⟩ := by
  have hnot : w ∉ mcPts o.Re.J := by
    rw [hJ]
    intro h
    have := h.2 1 Submodule.mem_top
    simp at this
  obtain ⟨x, hx⟩ := o.Re.R.surj w hw hnot
  obtain ⟨k, hk, hxw⟩ := id hx
  refine ⟨x, hx, ?_, ?_⟩
  · have hC : CoordsAt o.𝔐.ξ M.y z (o.Re.R.lift x x) := by
      rw [hxw]
      exact coordsAt_smul hz hk
    exact (o.interior x z hC).1 hI
  · obtain ⟨α, hα, h⟩ := TowerOriginModel.pi_pt_ne o x
    refine ⟨α⁻¹ * k o.k₀, funext fun a => ?_⟩
    have h1 := congrFun h a
    rw [hxw] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_assoc, h1, inv_mul_cancel_left₀ hα]

end Origin

theorem join_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → o.Re.J = ⊤ → o₀.Re.J = ⊤ → ∃ f : MRing (Cmp.joinIdx M.ι R.ι), f ∉ mCoordIdeal (Ht.joinOf M R i) ∧ ∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), Cmp.evC w f ≠ 0 → ∃ (x : o.Re.R.X) (x' : o₀.Re.R.X) (z₁ : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ o₀.𝔐.X), ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) (fun p => w (Cmp.joinInl M.ι R.ι p)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o₀.Re.R.lift x' x') (fun p => w (Cmp.joinInr M.ι R.ι p)) ∧ o.Re.π x = o₀.Re.π x' ∧ o.Re.π x ∈ Sys.open' ∧ CoordsAt o.𝔐.ξ M.y z₁ (fun p => w (Cmp.joinInl M.ι R.ι p)) ∧ CoordsAt o₀.𝔐.ξ R.y z₂ (fun p => w (Cmp.joinInr M.ι R.ι p)) ∧ o.𝔐.Interior z₁ ∧ o₀.𝔐.Interior z₂ := by
  intro E _ _ _ H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi hJ hJ₀
  classical
  obtain ⟨b, hb, hbw⟩ := exists_form o
  obtain ⟨b₀, hb₀, hbw₀⟩ := exists_form o₀
  have eL : (Ht.joinOf M R i) ∘ Cmp.joinInl M.ι R.ι = M.y := rfl
  have eR : (Ht.joinOf M R i) ∘ Cmp.joinInr M.ι R.ι = fun p => i (R.y p) := rfl
  refine ⟨rename (Cmp.joinInl M.ι R.ι) b * rename (Cmp.joinInr M.ι R.ι) b₀, fun h => ?_, fun w hw hf => ?_⟩
  · have h0 := aeval_eq_zero_of_mem _ h
    rw [map_mul, aeval_rename, aeval_rename, eL, eR, aeval_map_hom] at h0
    exact (mul_ne_zero hb ((map_ne_zero i).2 hb₀)) h0
  · obtain ⟨hw₁, hw₂⟩ := (GlobalTheory.T.join_model_points_project (CMType H) (D.p + D.q) M R i).2.2.1 ℂ w hw
    rw [Small.LineModel.ptsOver_complex] at hw₁ hw₂
    rw [Cmp.evC, Small.LineModel.eval_map_eq, map_mul, aeval_rename, aeval_rename] at hf
    obtain ⟨z₁, hz₁, hI₁⟩ := hbw _ hw₁ (left_ne_zero_of_mul hf)
    obtain ⟨z₂, hz₂, hI₂⟩ := hbw₀ _ hw₂ (right_ne_zero_of_mul hf)
    obtain ⟨x, hx, hxo, t, ht⟩ := exists_lift o hJ hw₁ hz₁ hI₁
    obtain ⟨x', hx', -, t', ht'⟩ := exists_lift o₀ hJ₀ hw₂ hz₂ hI₂
    refine ⟨x, x', z₁, z₂, hx, hx', ?_, hxo, hz₁, hz₂, hI₁, hI₂⟩
    have hcross : ∀ a b', w (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) * w (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b'⟩) =
        w (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b'⟩) * w (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) := by
      intro a b'
      have hm := cross_mem (Ht.joinOf M R i) (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩)
        (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b'⟩)
        (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b'⟩) rfl rfl (by
          show M.y _ * i (R.y _) = M.y _ * i (R.y _)
          have hg : ∀ u, i (o₀.g u) = o.g u := fun u => congrArg (fun φ : Fx.Ωf →+* M.Ω => φ u) hi
          rw [o.y_eq, o.y_eq, o₀.y_eq, o₀.y_eq, hg, hg]
          ring)
      have h0 := hw.2 _ hm
      simp only [map_sub, map_mul, aeval_X] at h0
      exact sub_eq_zero.1 h0
    obtain ⟨s, hs⟩ := exists_smul_of_cross (u := Fx.pt (o.Re.π x)) (v := Fx.pt (o₀.Re.π x')) (Fx.pt_ne _)
      (fun a b' => by
        rw [ht, ht']
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (t * t') * hcross a b')
    exact Fx.pt_inj _ _ s hs

end GlobalTheory.CompanionTheory.Ar.JoinPts
