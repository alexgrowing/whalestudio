import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibrePowerFreePullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelFibresPowerFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowFnsOfAbelianGenericStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocalization
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackStalkIsDomainEtale

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GlobalFib

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem natCast_residueField_iff {Y Z : Scheme.{0}} (f : Y ⟶ Z) (y : Y) (n : ℕ) :
    (n : Z.residueField (f y)) = 0 ↔ (n : Y.residueField y) = 0 := by
  rw [← map_natCast (f.residueFieldMap y).hom n, map_eq_zero]

theorem natCast_mem_of_residueField {Z : Scheme.{0}} {A : Type} [CommRing A] (f : Z ⟶ Sp A) (z : Z) (n : ℕ)
    (h : (n : Z.residueField z) = 0) : (n : A) ∈ (f z).asIdeal := by
  have := (f z).isPrime
  have h₁ : (n : (Sp A).residueField (f z)) = 0 := by
    rw [← map_natCast (f.residueFieldMap z).hom n, map_eq_zero] at h
    exact h
  rw [← Ideal.algebraMap_residueField_eq_zero, map_natCast,
    ← map_natCast (Scheme.Spec.residueFieldIso (CommRingCat.of A) (f z)).hom.hom n, map_eq_zero]
  exact h₁

theorem isNoetherianRing_V (c : Coeff l) (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) : IsNoetherianRing (c.V W) := by
  obtain ⟨b, hb, -⟩ := GlobalTheory.GlobalModelGuards.exists_incl c W
  obtain ⟨M, hM⟩ := GlobalTheory.ShFam.Pad.BCEx.exists_isLocalization hp hW b hb
  letI := b.toAlgebra
  exact IsLocalization.isNoetherianRing M (c.V W) inferInstance

theorem not_isUnit_V (c : Coeff l) (W : ValuationSubring ℂ) (x : c.V W) (hx : ((x : c.F) : ℂ) ∈ W.nonunits) :
    ¬ IsUnit x := by
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvW : ((v : c.F) : ℂ) ∈ W := v.2
  have h1 : ((x : c.F) : ℂ) * ((v : c.F) : ℂ) = 1 := by
    have := congrArg (fun z : c.V W => ((z : c.F) : ℂ)) hv
    simpa using this
  rw [ValuationSubring.mem_nonunits_iff] at hx
  have h2 := (W.valuation_le_one_iff _).2 hvW
  have h3 := congrArg W.valuation h1
  rw [map_mul, map_one] at h3
  exact (mul_lt_one_of_lt_of_le hx h2).ne h3

theorem exists_place_over (c : Coeff l) (q : PrimeSpectrum (𝓞 c.F)) {p : ℕ} (hp : p.Prime)
    (hq : (p : 𝓞 c.F) ∈ q.asIdeal) :
    ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ ∀ b : 𝓞 c.F →+* c.V W,
      (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → (IsLocalRing.maximalIdeal (c.V W)).comap b = q.asIdeal := by
  have := c.fin
  have : NumberField c.F := {}
  let φ : 𝓞 c.F →+* ℂ := c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)
  have hφ : Function.Injective φ := fun a b h => RingOfIntegers.coe_injective (Subtype.ext h)
  let e : 𝓞 c.F ≃+* φ.range :=
    RingEquiv.ofBijective φ.rangeRestrict ⟨fun a b h => hφ (by have h' := congrArg (fun x : φ.range => (x : ℂ)) h; exact h'), φ.rangeRestrict_surjective⟩
  let I : Ideal φ.range := q.asIdeal.comap (e.symm : φ.range →+* 𝓞 c.F)
  have hI : I ≠ ⊤ := fun h => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have : (1 : φ.range) ∈ I := h ▸ Submodule.mem_top
    simpa [I] using this))
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hmem : ∀ x ∈ q.asIdeal, φ x ∈ W.nonunits := fun x hx =>
    hW ⟨e x, by simpa [I] using hx, rfl⟩
  refine ⟨W, ?_, fun b hb => ?_⟩
  · simpa [φ] using hmem _ hq
  have hne : q.asIdeal ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hq
    exact hp.ne_zero (by exact_mod_cast hq)
  have hmax : q.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal q.isPrime hne
  refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) fun x hx => ?_).symm
  refine not_isUnit_V c W (b x) ?_
  have := hmem x hx
  rw [show φ x = (((b x : c.V W) : c.F) : ℂ) by simp [φ, hb]] at this
  exact this

variable {Xo : Moduli D l} {c : Coeff l}

theorem isLocallyNoetherian_X (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : IsLocallyNoetherian Y.X := by
  have := c.fin
  have : NumberField c.F := {}
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  exact LocallyOfFiniteType.isLocallyNoetherian Y.s

theorem isReduced_X (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : IsReduced Y.X := by
  have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
    have := (Y.normal x).1
    infer_instance
  exact isReduced_of_isReduced_stalk Y.X

theorem generic_mem_abLocus (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (ξ : Y.X)
    (hξ : ∀ y : Y.X, y ⤳ ξ → y = ξ) : ξ ∈ abLocus Y.t.G := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  have := Y.jQ_open
  have := Y.flat
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  let o : Sp c.F := IsLocalRing.closedPoint c.F
  have ho : spMap (algebraMap (𝓞 c.F) c.F) o ⤳ Y.s ξ := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
    have h1 : algebraMap (𝓞 c.F) c.F a ∈ IsLocalRing.maximalIdeal c.F := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h1
    obtain rfl : a = 0 := RingOfIntegers.coe_injective (by simpa using h1)
    exact zero_mem _
  obtain ⟨ξ', h₁, h₂⟩ := Flat.generalizingMap Y.s ho
  obtain rfl := hξ ξ' h₁
  obtain ⟨ζ, hζ⟩ : ξ' ∈ Set.range (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨o, h₂.symm⟩
  have : IsLocallyNoetherian (pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : CompactSpace (pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : IsNoetherian (pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := {}
  have hr : ζ ∈ Set.range Y.jQ := by
    refine GlobalTheory.TraitGeneric.mem_of_dense_of_maximal (fun y hy => ?_) Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense
    have : y = ζ := by
      refine (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective ?_
      rw [hζ]
      exact hξ _ (hζ ▸ hy.map (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous)
    rw [this]
  rw [← Y.ab_gen] at hr
  rw [← hζ]
  exact hr

theorem global_fibPF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Y p W hp hW i).SplitFibres ∧ (Y p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Ygl : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Dominates Ygl (Y p W hp hW ⟨l, c, hg p hp⟩) b) → PowFns Ygl.t ∧ ∀ (p : ℕ), p.Prime → ∀ z : Ygl.X, (p : Ygl.X.residueField z) = 0 → FibPF Ygl.t z := by
  intro E _ _ _ H D Xo Y hY l c hg Ygl hdom
  refine ⟨GlobalTheory.T.powFns_of_abelian_generic E H Ygl.X Ygl.t (isReduced_X Ygl) (isLocallyNoetherian_X Ygl)
    (fun z hz => generic_mem_abLocus Ygl z hz), ?_⟩
  intro p hp z hz
  have hq : (p : 𝓞 c.F) ∈ (Ygl.s z).asIdeal := natCast_mem_of_residueField Ygl.s z p hz
  obtain ⟨W, hW, hc⟩ := exists_place_over c (Ygl.s z) hp hq
  obtain ⟨b, hb, -⟩ := GlobalTheory.GlobalModelGuards.exists_incl c W
  have hpt : Ygl.s z = spMap b (IsLocalRing.closedPoint (c.V W)) :=
    PrimeSpectrum.ext (hc b hb).symm
  obtain ⟨z', rfl, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Ygl.s) (g := spMap b) z _ hpt
  obtain ⟨f, t, m₁, m₂, -, -, -⟩ := hdom p W hp hW b hb
  have hN := isNoetherianRing_V c W hp hW
  have hinj : Function.Injective (c.V W).subtype := Subtype.val_injective
  have hz' : (p : ((Y p W hp hW ⟨l, c, hg p hp⟩).X).residueField (f z')) = 0 := by
    exact (natCast_residueField_iff f z' p).2 ((natCast_residueField_iff _ z' p).1 hz)
  have h₁ := GlobalTheory.T.model_fibres_power_free E H D l (Xo l) c (c.V W) (c.V W).subtype (Y p W hp hW ⟨l, c, hg p hp⟩)
    (GlobalTheory.LocM.BaseMdl.dense_j hinj _) (hY p W hp hW _).1 (hY p W hp hW _).2 p hp (f z') hz'
  exact (GlobalTheory.T.fibre_power_free_pullback E H _ _ _ t _ m₁ z').1 ((GlobalTheory.T.fibre_power_free_pullback E H _ _ _ t f m₂ z').2 h₁)

end GlobalTheory.CompanionTheory.Ar.GlobalFib
