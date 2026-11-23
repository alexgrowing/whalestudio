import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.EmbUniq

variable {l : ℕ} [Fact l.Prime]

theorem norm_coe_algHom {K L : FinExt l} (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (x : ↥K.1) :
    ‖((τ x : ↥L.1) : Om l)‖ = ‖(x : Om l)‖ := by
  have a := minpoly.algHom_eq (L.1.val.comp τ) (RingHom.injective (L.1.val.comp τ : ↥K.1 →+* Om l)) x
  have b := minpoly.algHom_eq K.1.val (RingHom.injective (K.1.val : ↥K.1 →+* Om l)) x
  have c : minpoly ℚ_[l] ((τ x : ↥L.1) : Om l) = minpoly ℚ_[l] (x : Om l) := a.trans b.symm
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, c]

theorem norm_le_one_of_isIntegral {x : Om l} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := Om l)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := Om l))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

variable {E : Type} [Field E] [NumberField E]

theorem continuous_withVal (w : HeightOneSpectrum (𝓞 E)) (f : E →+* Om l)
    (h1 : ∀ x, w.valuation E x ≤ 1 → ‖f x‖ ≤ 1) (y : E) (hy0 : y ≠ 0) (hy : ‖f y‖ < 1) :
    Continuous (f.comp (WithVal.equiv (w.valuation E)).toRingHom) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hy
  let x0 : WithVal (w.valuation E) := WithVal.toVal _ (y ^ n)
  have hx0' : x0 ≠ 0 := by
    intro h
    exact pow_ne_zero n hy0 ((WithVal.equiv (w.valuation E)).symm.map_eq_zero_iff.1 h)
  have h0 : Valued.v.restrict x0 ≠ 0 := by simp [hx0']
  filter_upwards [Valued.mem_nhds_zero.2 ⟨Units.mk0 _ h0, subset_rfl⟩] with z hz
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
  have hz' : w.valuation E (WithVal.equiv (w.valuation E) z) < w.valuation E (y ^ n) := hz
  have hv : 0 < w.valuation E (y ^ n) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (pow_ne_zero n hy0))
  have hu : w.valuation E (WithVal.equiv (w.valuation E) z / y ^ n) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hv).2 hz'.le
  have h2 := h1 _ hu
  have hp : 0 < ‖f y‖ ^ n := pow_pos (norm_pos_iff.2 ((map_ne_zero f).2 hy0)) n
  rw [map_div₀, map_pow, norm_div, norm_pow, div_le_one₀ hp] at h2
  rw [dist_zero_right]
  exact lt_of_le_of_lt h2 hn

def toKw {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) : E →+* ↥Bw.Kw.1 :=
  (Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E

theorem existsUnique_continuous_induced : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
      ∃! j : {j : w.adicCompletion E →+* Qbar l // Continuous j},
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hj LL' τ'
  let g : E →+* ↥LL'.1 := (τ' : ↥Bw.Kw.1 →+* ↥LL'.1).comp (toKw Bw)
  let f : E →+* Om l := (algebraMap ↥LL'.1 (Om l)).comp g
  have hfn : ∀ x, ‖f x‖ = ‖Bw.j (algebraMap E Ω x)‖ := fun x => norm_coe_algHom τ' (toKw Bw x)
  have hlt : ∀ y : 𝓞 E, ‖f (y : E)‖ < 1 ↔ y ∈ w.asIdeal := fun y => by
    rw [hfn, ← hj.valuation_lt_one_iff]
    exact hA y
  have hint : ∀ y : 𝓞 E, ‖f (y : E)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral (by
      convert map_isIntegral_int f (RingOfIntegers.isIntegral_coe y)
      exact Subsingleton.elim _ _)
  have h1 : ∀ x, w.valuation E x ≤ 1 → ‖f x‖ ≤ 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    have hd : 1 ≤ ‖f ((d : 𝓞 E) : E)‖ := not_lt.1 fun hl => d.2 ((hlt _).1 hl)
    have h2 : ‖f x‖ * ‖f ((d : 𝓞 E) : E)‖ = ‖f (n : E)‖ := by
      rw [← norm_mul, ← map_mul]
      exact congrArg (fun z => ‖f z‖) h
    have h3 := hint n
    nlinarith [norm_nonneg (f x)]
  obtain ⟨y, hyw, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have hc := continuous_withVal w f h1 (y : E) (by simpa using hy0) ((hlt y).2 hyw)
  have hcg : Continuous (g.comp (WithVal.equiv (w.valuation E)).toRingHom) :=
    Topology.IsInducing.subtypeVal.continuous_iff.2 hc
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : CompleteSpace ↥LL'.1 := FiniteDimensional.complete ℚ_[l] ↥LL'.1
  let ext : w.adicCompletion E →+* ↥LL'.1 :=
    (UniformSpace.Completion.extensionHom _ hcg).comp (HeightOneSpectrum.adicCompletion.equiv E w).toRingHom
  have hextc : Continuous ext := UniformSpace.Completion.continuous_extension.comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w)
  have hext : ∀ x : E, ext (algebraMap E _ x) = g x := fun k =>
    UniformSpace.Completion.extensionHom_coe _ hcg (WithVal.toVal _ k)
  have hval : ∀ x : E, ((ext (algebraMap E _ x) : ↥LL'.1) : Om l) = f x := fun x =>
    congrArg (Subtype.val) (hext x)
  refine ⟨⟨(algebraMap ↥LL'.1 (Om l)).comp ext, continuous_subtype_val.comp hextc⟩, fun x => (hval x), ?_⟩
  rintro ⟨j', hj'c⟩ hj'
  refine Subtype.ext (DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer hj'c
    (continuous_subtype_val.comp hextc) (funext fun x => ?_)))
  exact (hj' x).trans (hval x).symm

end GlobalTheory.CompanionTheory.EmbUniq
