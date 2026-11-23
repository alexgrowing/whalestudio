import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NormInj
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ConjDesc
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OrbProper
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.QuotDesc
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.TwOrbConj
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootEx
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootConj
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RigidNear
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OpenNear
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ValuationNatCastLeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Unimod

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc.NearIdentityDescent

open UpperTheory.ConvolutionTheory.Loc.BallG

private theorem sb_of_push {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {U : Set X} (hU : IsCompact U)
    {p : X → Y} (hp : Continuous p) (ho : IsOpen (p '' U)) {a : X → ℂ} (ha : IsLocallyConstant a) {f : Y → ℂ}
    (h1 : ∀ u ∈ U, f (p u) = a u) (h2 : ∀ y, y ∉ p '' U → f y = 0) : f ∈ SB Y := by
  refine ⟨fun s => ?_, HasCompactSupport.intro (hU.image hp) h2⟩
  rw [← isClosed_compl_iff, ← Set.preimage_compl]
  generalize sᶜ = t
  have hc : IsClosed (a ⁻¹' t) := by
    rw [← isOpen_compl_iff, ← Set.preimage_compl]
    exact ha _
  have e : f ⁻¹' t = p '' (U ∩ a ⁻¹' t) ∪ ((p '' U)ᶜ ∩ {_y | (0 : ℂ) ∈ t}) := by
    ext y
    by_cases hy : y ∈ p '' U
    · obtain ⟨u, hu, rfl⟩ := hy
      constructor
      · intro h
        exact Or.inl ⟨u, ⟨hu, by rwa [Set.mem_preimage, h1 u hu] at h⟩, rfl⟩
      · rintro (⟨u', ⟨hu', h⟩, e⟩ | ⟨h, -⟩)
        · rw [Set.mem_preimage, ← e, h1 u' hu']
          exact h
        · exact absurd ⟨u, hu, rfl⟩ h
    · rw [Set.mem_preimage, h2 y hy]
      constructor
      · exact fun h => Or.inr ⟨hy, h⟩
      · rintro (⟨u', ⟨hu', -⟩, e⟩ | ⟨-, h⟩)
        · exact absurd ⟨u', hu', e⟩ hy
        · exact h
  rw [e]
  exact ((hU.inter_right hc).image hp).isClosed.union (ho.isClosed_compl.inter isClosed_const)

private theorem avg_locConst {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    (μ : Measure G) {θ : G → G} (hθ : Continuous θ) {K : Set G} (hK : IsCompact K) (hm : MeasurableSet K) {φ : G → ℂ}
    (hφ : IsLocallyConstant φ) : IsLocallyConstant fun u => ∫ κ in K, φ (κ⁻¹ * u * θ κ) ∂μ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u₀
  have h : ∀ᶠ u in nhds u₀, ∀ κ ∈ K, φ (κ⁻¹ * u * θ κ) = φ (κ⁻¹ * u₀ * θ κ) := by
    refine hK.eventually_forall_of_forall_eventually fun κ _ => ?_
    have h1 := (hφ.comp_continuous (f := fun z : G × G => z.2⁻¹ * z.1 * θ z.2) (by fun_prop)).eventually_eq (u₀, κ)
    have h2 := (hφ.comp_continuous (f := fun z : G × G => z.2⁻¹ * u₀ * θ z.2) (by fun_prop)).eventually_eq (u₀, κ)
    filter_upwards [h1, h2] with z hz1 hz2
    exact hz1.trans hz2.symm
  filter_upwards [h] with u hu
  exact setIntegral_congr_fun hm hu

private theorem quot_zero {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H) {F : G → ℂ}
    (h : ∀ g, F g = 0) : quotIntegral μ H ν F = 0 := by
  simp [quotIntegral, h]

private theorem quot_const_mul {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H) (c : ℂ)
    (F : G → ℂ) : quotIntegral μ H ν (fun g => c * F g) = c * quotIntegral μ H ν F := by
  unfold quotIntegral
  split_ifs
  · rw [← integral_const_mul]
    simp only [mul_assoc]
  · simp

section Alg

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ}

private theorem incl_inj : Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := fun x y h => by
  ext i j
  exact (algebraMap k E).injective (congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) h)

private theorem sigma_incl (σ : E ≃ₐ[k] E) (y : GL (Fin n) k) : sigmaGL σ (incl y : GL (Fin n) E) = incl y := by
  ext i j
  exact σ.commutes _

private theorem norm_incl (σ : E ≃ₐ[k] E) (y : GL (Fin n) k) :
    normGL σ (incl y : GL (Fin n) E) = incl (y ^ Module.finrank k E) := by
  unfold normGL
  induction Module.finrank k E with
  | zero => simp
  | succ m ih =>
    rw [twNorm_succ, ih, pow_succ y, map_mul]
    congr 1
    clear ih
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ_apply, sigma_incl, ih]

private theorem sep_incl (γ : GL (Fin n) k) :
    ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable ↔ IsRegSemisimple γ := by
  have e : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) k).map (algebraMap k E) := rfl
  rw [e, Matrix.charpoly_map, Polynomial.separable_map]
  rfl

private theorem sep_conj (x h : GL (Fin n) E) : ((h * x * h⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
    (x : Matrix (Fin n) (Fin n) E).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

private theorem comm_of_sep {a x y : GL (Fin n) E} (ha : (a : Matrix (Fin n) (Fin n) E).charpoly.Separable)
    (hx : x * a = a * x) (hy : y * a = a * y) : x * y = y * x :=
  Units.ext (UpperTheory.V.Z.Tf.Orb.centComm E n a x y ha (congrArg Units.val hx) (congrArg Units.val hy))

private theorem theta_pow [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E) :
    (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
  rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]

private theorem mem_twCent_conj {G : Type} [Group G] (θ : Monoid.End G) (δ g x : G) :
    x ∈ twCent θ δ ↔ g⁻¹ * x * g ∈ twCent θ (twConj θ g δ) := by
  rw [mem_twCent, mem_twCent, twConj, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc _ = g⁻¹ * (x⁻¹ * δ * θ x) * θ g := by group
      _ = _ := by rw [h]
  · intro h
    calc _ = g * ((g⁻¹ * x * g)⁻¹ * (g⁻¹ * δ * θ g) * ((θ g)⁻¹ * θ x * θ g)) * (θ g)⁻¹ := by group
      _ = _ := by rw [h]; group

end Alg

section Loc

variable {k E : Type} [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] {σ : E ≃ₐ[k] E}
  (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) {n : ℕ} {r : ValueGroupWithZero E}
  (hr : r < valuation E (Module.finrank k E : E))

include hr in
private theorem root_conj {u u' y : GL (Fin n) k} (hu : (incl u : GL (Fin n) E) ∈ ball n r) (hu' : (incl u' : GL (Fin n) E) ∈ ball n r)
    (h : y⁻¹ * u ^ Module.finrank k E * y = u' ^ Module.finrank k E) : y⁻¹ * u * y = u' := by
  apply incl_inj (E := E)
  rw [map_mul, map_mul, map_inv]
  refine rootConj E n _ r hr _ hu _ hu' _ ?_
  rw [← map_pow, ← map_pow, ← h, map_mul, map_mul, map_inv]

include hgen hr in
private theorem rigid {u u' y y' : GL (Fin n) k} (hu : (incl u : GL (Fin n) E) ∈ ball n r) (hu' : (incl u' : GL (Fin n) E) ∈ ball n r)
    {g : GL (Fin n) E} (h : g⁻¹ * incl (y * u * y⁻¹) * sigmaGL σ g = incl (y' * u' * y'⁻¹)) : ∃ x : GL (Fin n) k, incl x = g := by
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  obtain ⟨x, hx⟩ := ((hb n).2.2.1 hgen ((incl y)⁻¹ * g * incl y')).mp
    (rigidNear E n σ _ hc r hr _ hu _ hu' (sigma_incl σ u) (sigma_incl σ u') _ (by
      show _ * _ * sigmaGL σ _ = _
      simp only [map_mul, map_inv, sigma_incl] at h ⊢
      calc _ = (incl y')⁻¹ * (g⁻¹ * (incl y * incl u * (incl y)⁻¹) * sigmaGL σ g) * incl y' := by group
        _ = _ := by rw [h]; group))
  exact ⟨y * x * y'⁻¹, by rw [map_mul, map_mul, map_inv, hx]; group⟩

include hgen hr in
private theorem near {g : GL (Fin n) E} (hg : g ∈ ball n (r * valuation E (Module.finrank k E : E))) :
    ∃ κ ∈ ball n r, ∃ u : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r ∧ g = κ⁻¹ * incl u * sigmaGL σ κ := by
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  obtain ⟨κ, hκ, u, hu, hf, e⟩ := openNear E n σ _ hc r r hr le_rfl 1 (fun i j => by simp) (map_one _) g hg
  obtain ⟨u, rfl⟩ := ((hb n).2.2.1 hgen u).mp hf
  rw [one_mul, one_mul] at e
  exact ⟨κ, hκ, u, hu, e⟩

include hgen hr in
private theorem cent_eq {u : GL (Fin n) k} (hu : (incl u : GL (Fin n) E) ∈ ball n r) (y : GL (Fin n) k) :
    twCent (sigmaGL σ) (incl (y * u * y⁻¹) : GL (Fin n) E) =
      (Subgroup.centralizer {y * u ^ Module.finrank k E * y⁻¹}).map incl := by
  ext x
  rw [mem_twCent, Subgroup.mem_map]
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := rigid hgen hr hu hu h
    refine ⟨x, ?_, rfl⟩
    rw [sigma_incl, ← map_inv, ← map_mul, ← map_mul] at h
    have h1 := incl_inj h
    rw [Subgroup.mem_centralizer_singleton_iff, ← conj_pow]
    refine (Commute.pow_right ?_ _).eq
    calc x * (y * u * y⁻¹) = x * (x⁻¹ * (y * u * y⁻¹) * x) := by rw [h1]
      _ = _ := by group
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have h1 := root_conj hr hu hu (y := y⁻¹ * x * y) (by
      calc _ = y⁻¹ * x⁻¹ * (y * u ^ Module.finrank k E * y⁻¹ * x) * y := by group
        _ = _ := by rw [← hx]; group)
    rw [sigma_incl, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    calc _ = y * ((y⁻¹ * x * y)⁻¹ * u * (y⁻¹ * x * y)) * y⁻¹ := by group
      _ = _ := by rw [h1]

include hgen hr in
private theorem exists_push (hr0 : 0 < r) {a : GL (Fin n) k → ℂ} (ha : IsLocallyConstant a) :
    ∃ f ∈ SB (GL (Fin n) k), (∀ u : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r → f (u ^ Module.finrank k E) = a u) ∧
      ∀ γ, (¬ ∃ u : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r ∧ u ^ Module.finrank k E = γ) → f γ = 0 := by
  classical
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  have hj := (hb n).2.2.2.1
  haveI := (UpperTheory.V.Z.Tf.Orb.gLTop k n).2.2.1
  have hr1 : r < 1 := hr.trans_le (valuation_natCast_le_one _)
  let f : GL (Fin n) k → ℂ := fun γ =>
    if h : ∃ u : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r ∧ u ^ Module.finrank k E = γ then a h.choose else 0
  have h1 : ∀ u : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r → f (u ^ Module.finrank k E) = a u := by
    intro u hu
    have h : ∃ u' : GL (Fin n) k, (incl u' : GL (Fin n) E) ∈ ball n r ∧ u' ^ Module.finrank k E = u ^ Module.finrank k E :=
      ⟨u, hu, rfl⟩
    have := root_conj hr (y := 1) h.choose_spec.1 hu (by simpa using h.choose_spec.2)
    simp only [f, dif_pos h]
    rw [inv_one, one_mul, mul_one] at this
    exact congrArg a this
  have h2 : ∀ γ, (¬ ∃ u : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r ∧ u ^ Module.finrank k E = γ) → f γ = 0 :=
    fun γ h => dif_neg h
  refine ⟨f, sb_of_push (U := incl ⁻¹' ball (E := E) n r) (hj.isCompact_preimage (isCompact_ball hr1))
    (p := fun u => u ^ Module.finrank k E) (continuous_pow _) ?_ ha h1 h2, h1, h2⟩
  have e : (fun u : GL (Fin n) k => u ^ Module.finrank k E) '' (incl ⁻¹' ball (E := E) n r) =
      incl ⁻¹' ball (E := E) n (r * valuation E (Module.finrank k E : E)) := by
    ext γ
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Set.mem_preimage, map_pow]
      exact pow_mem_ball hr hu
    · intro hγ
      obtain ⟨u, hu, hf, huq⟩ := exists_fixed_root hc.isom hr hγ (sigma_incl σ γ)
      obtain ⟨u, rfl⟩ := ((hb n).2.2.1 hgen u).mp hf
      exact ⟨u, hu, incl_inj (by rw [map_pow, huq])⟩
  rw [e]
  exact (isOpen_ball (mul_pos hr0 (hr0.trans hr)).ne').preimage hj.continuous

end Loc

end UpperTheory.ConvolutionTheory.Loc.NearIdentityDescent

open UpperTheory.ConvolutionTheory.Loc.NearIdentityDescent UpperTheory.ConvolutionTheory.Loc.BallG UpperTheory.V.Z.Tf.Orb in
theorem UpperTheory.ConvolutionTheory.Loc.nearDown :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)), μE.IsHaarMeasure → μk.IsHaarMeasure → ∃ ρ : ValueGroupWithZero E, 0 < ρ ∧ ∀ φ ∈ SB (GL (Fin n) E), Function.support φ ⊆ ball n ρ →
        ∃ f ∈ SB (GL (Fin n) k), Match σ μE μk φ f := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ _ _ μE μk hμE hμk
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  have hj := (hb n).2.2.2.1
  obtain ⟨_, _, _, -⟩ := gLTop E n
  obtain ⟨_, _, _, -⟩ := gLTop k n
  have hθ : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) := ((extCont k E).2.2 n).2 σ
  obtain ⟨r, hr0, hr⟩ := exists_radius (w := valuation E (Module.finrank k E : E))
    ((Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hc.pos.ne'))
  have hq1 := valuation_natCast_le_one (E := E) (Module.finrank k E)
  have hr1 : r < 1 := hr.trans_le hq1
  refine ⟨r * valuation E (Module.finrank k E : E), mul_pos hr0 (hr0.trans hr), fun φ hφ hs => ?_⟩
  set K := ballSub n r hr1 with hK
  have hKo : IsOpen (K : Set (GL (Fin n) E)) := isOpen_ball hr0.ne'
  have hKc : IsCompact (K : Set (GL (Fin n) E)) := isCompact_ball hr1
  set c : ℂ := (((μk (K.comap (incl : GL (Fin n) k →* GL (Fin n) E))).toReal⁻¹ : ℝ) : ℂ) with hcdef
  set A : GL (Fin n) E → ℂ := fun u => ∫ κ in (K : Set (GL (Fin n) E)), φ (κ⁻¹ * u * sigmaGL σ κ) ∂μE with hA
  have hAl : IsLocallyConstant A := avg_locConst μE hθ hKc hKo.measurableSet hφ.1
  obtain ⟨f, hf, h1, h2⟩ := exists_push hgen hr hr0 (a := fun u => c * A (incl u))
    ((hAl.comp_continuous hj.continuous).comp fun z => c * z)
  have hA0 : ∀ w, w ∉ ball n r → A w = 0 := by
    intro w hw
    refine setIntegral_eq_zero_of_forall_eq_zero fun κ hκ => ?_
    by_contra h
    have h3 : κ⁻¹ * w * sigmaGL σ κ ∈ K := ball_mono (mul_le_of_le_one_right' hq1) (hs h)
    have h4 : sigmaGL σ κ ∈ K := (sg_mem_ball_iff hc.isom).mpr hκ
    have h5 := K.mul_mem (K.mul_mem hκ h3) (K.inv_mem h4)
    rw [show κ * (κ⁻¹ * w * sigmaGL σ κ) * (sigmaGL σ κ)⁻¹ = w by group] at h5
    exact hw h5
  refine ⟨f, hf, fun δ γ h μδ μγ hδ hN hμδ hμγ hmap => ?_, fun γ μγ _ hno _ => ?_⟩
  swap
  · refine quot_zero _ _ _ fun y => h2 _ ?_
    rintro ⟨u, -, hu⟩
    exact hno ⟨incl u, (incl y)⁻¹, by rw [norm_incl, hu, map_mul, map_mul, map_inv, inv_inv]⟩
  have hγE : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    rw [← sep_conj _ h, ← hN]
    exact hδ
  have hγ : IsRegSemisimple γ := (sep_incl γ).mp hγE
  by_cases hex : ∃ u y : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r ∧ γ = y * u ^ Module.finrank k E * y⁻¹
  swap
  · rw [twOrbIntegralC, orbIntegralC, quot_zero, quot_zero]
    · refine fun y => h2 _ ?_
      rintro ⟨u, hu, e⟩
      exact hex ⟨u, y, hu, by rw [e]; group⟩
    · intro g
      by_contra h0
      obtain ⟨κ, -, u, hu, e⟩ := near hgen hr (hs h0)
      have e1 := congrArg (twNorm (sigmaGL σ) (Module.finrank k E)) e
      rw [← twConj, twNorm_twConj_of_pow_eq_one _ (theta_pow σ), twNorm_twConj_of_pow_eq_one _ (theta_pow σ),
        ← normGL, ← normGL, hN, norm_incl] at e1
      obtain ⟨y, hy⟩ := conjDesc k E n γ (u ^ Module.finrank k E) hγ ⟨κ * g⁻¹ * h, by
        calc _ = κ * (κ⁻¹ * incl (u ^ Module.finrank k E) * κ) * κ⁻¹ := by group
          _ = _ := by rw [← e1]; group⟩
      exact hex ⟨u, y⁻¹, hu, by rw [hy]; group⟩
  obtain ⟨u, y, hu, hγu⟩ := hex
  have hN1 : normGL σ (incl (y * u * y⁻¹) : GL (Fin n) E) = incl γ := by rw [norm_incl, conj_pow, hγu]
  obtain ⟨g, hg⟩ := normInj k E σ hgen n γ hγ δ (incl (y * u * y⁻¹)) ⟨h, hN⟩ ⟨1, by simpa using hN1⟩
  obtain ⟨μ', hμ', hmap'⟩ := haarConj (GL (Fin n) E) _ _ g (mem_twCent_conj (sigmaGL σ) δ g) μδ hμδ
  rw [← twOrbConj k E σ n μE hμE δ g μδ μ' hδ hμδ hμ' hmap' φ hφ]
  have hz : h⁻¹ * g * incl γ = incl γ * (h⁻¹ * g) := by
    have e := hN1
    rw [hg, normGL, twNorm_twConj_of_pow_eq_one _ (theta_pow σ), ← normGL, hN] at e
    calc _ = h⁻¹ * g * (g⁻¹ * (h * incl γ * h⁻¹) * g) := by rw [e]
      _ = _ := by group
  have hpt : (fun x : twCent (sigmaGL σ) δ => g⁻¹ * (x : GL (Fin n) E) * g) =
      fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h := by
    funext x
    have e := comm_of_sep hγE (Subgroup.mem_centralizer_singleton_iff.mp
      (conj_twCent_mem_centralizer _ (theta_pow σ) hN x.2)) hz
    calc _ = (h⁻¹ * g)⁻¹ * (h⁻¹ * (x : GL (Fin n) E) * h * (h⁻¹ * g)) := by group
      _ = _ := by rw [e]; group
  rw [hpt, hmap] at hmap'
  clear hμ' hpt
  revert μ'
  rw [← hg]
  intro μ' hmap'
  have hT : IsClosed (Subgroup.centralizer ({γ} : Set (GL (Fin n) k)) : Set (GL (Fin n) k)) := by
    have e : (Subgroup.centralizer ({γ} : Set (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x} :=
      Set.ext fun x => Subgroup.mem_centralizer_singleton_iff
    rw [e]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hinv := (haarComm (GL (Fin n) k) _ hT (fun a ha b hb => comm_of_sep hγ
    (Subgroup.mem_centralizer_singleton_iff.mp ha) (Subgroup.mem_centralizer_singleton_iff.mp hb)) μγ hμγ).2.1
  have hreg : IsTwRegSemisimple σ (incl (y * u * y⁻¹) : GL (Fin n) E) := by
    rw [IsTwRegSemisimple, hN1]
    exact hγE
  obtain ⟨D, hD, hDs⟩ := orbProper k E σ hgen n _ hreg _ hφ.2
  rw [twOrbIntegralC, quotDesc _ _ incl hj μE μk hμE (unimod gLTop E n μE hμE).1 hμk (unimod gLTop k n μk hμk).1 K hKo hKc
    _ _ μ' μγ hT (by rw [cent_eq hgen hr hu y, ← hγu]) hμγ hinv hmap'.symm (fun g => φ (twConj (sigmaGL σ) g (incl (y * u * y⁻¹))))
    (hφ.1.continuous.comp (by unfold twConj; fun_prop))
    (fun s hs g => by rw [twConj_mul_left _ _ hs]) ?_ ⟨D, hD, fun x hx => hDs x (subset_tsupport _ hx)⟩,
    ← quot_const_mul, orbIntegralC]
  · congr 1
    funext x
    have e : (∫ κ in (K : Set (GL (Fin n) E)), φ (twConj (sigmaGL σ) (incl x * κ) (incl (y * u * y⁻¹))) ∂μE) =
        A (incl ((y⁻¹ * x)⁻¹ * u * (y⁻¹ * x))) := by
      simp only [hA, twConj, map_mul, map_inv, sigma_incl, mul_inv_rev, inv_inv, mul_assoc]
    have e' : x⁻¹ * γ * x = ((y⁻¹ * x)⁻¹ * u * (y⁻¹ * x)) ^ Module.finrank k E := by
      have := conj_pow (a := (y⁻¹ * x)⁻¹) (b := u) (i := Module.finrank k E)
      rw [inv_inv] at this
      rw [this, hγu]
      group
    rw [e]
    by_cases hw : (incl ((y⁻¹ * x)⁻¹ * u * (y⁻¹ * x)) : GL (Fin n) E) ∈ ball n r
    · rw [e', h1 _ hw]
    · rw [hA0 _ hw, mul_zero, h2]
      rintro ⟨u', hu', e2⟩
      rw [root_conj hr hu hu' (y := y⁻¹ * x) (by rw [e2, hγu]; group)] at hw
      exact hw hu'
  · intro x hx
    obtain ⟨κ, hκ, u', hu', e⟩ := near hgen hr (hs hx)
    obtain ⟨z, hz⟩ := rigid hgen hr hu hu' (y := y) (y' := 1) (g := x * κ⁻¹) (by
      rw [one_mul, inv_one, mul_one, map_mul (sigmaGL σ), map_inv]
      calc _ = κ * twConj (sigmaGL σ) x (incl (y * u * y⁻¹)) * (sigmaGL σ κ)⁻¹ := by unfold twConj; group
        _ = _ := by rw [e]; group)
    exact ⟨z, κ, hκ, by rw [hz]; group⟩
