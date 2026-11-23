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
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NearCore

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc.NearIdentityAscent

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

private theorem set_left {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (hm : MeasurableSet (K : Set G)) (F : G → ℂ) {z : G} (hz : z ∈ K) :
    ∫ κ in (K : Set G), F (z * κ) ∂μ = ∫ κ in (K : Set G), F κ ∂μ := by
  rw [← integral_indicator hm, ← integral_indicator hm, ← integral_mul_left_eq_self ((K : Set G).indicator F) z]
  congr 1
  funext κ
  by_cases h : κ ∈ K
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (K.mul_mem hz h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h ((K.mul_mem_cancel_left hz).1 h')]

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ}

private theorem incl_inj : Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := fun x y h => by
  ext i j
  exact (algebraMap k E).injective (congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) h)

private theorem sigma_incl (σ : E ≃ₐ[k] E) (y : GL (Fin n) k) : sigmaGL σ (incl y : GL (Fin n) E) = incl y := by
  ext i j
  exact σ.commutes _

private theorem small [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension k E] {s : ValueGroupWithZero E} (hs : s ≠ 0) :
    ∃ ρ : ValueGroupWithZero k, 0 < ρ ∧ ∀ g ∈ ball n ρ, (incl g : GL (Fin n) E) ∈ ball n s := by
  have key : ∀ a b : k, valuation E (algebraMap k E a) ≤ valuation E (algebraMap k E b) ↔ valuation k a ≤ valuation k b := fun a b => by
    rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le, ValuativeExtension.vle_iff_vle]
  obtain ⟨x, hx⟩ := valuation_surjective (K := k) (uniformizer k)
  have h1 : valuation k x < 1 := hx ▸ uniformizer_lt_one
  have h0 : x ≠ 0 := fun h => by
    rw [h, map_zero] at hx
    exact uniformizer_ne_zero hx.symm
  have h2 : valuation E (algebraMap k E x) < 1 := by
    have := key 1 x
    rw [map_one, map_one, map_one] at this
    exact lt_of_not_ge fun h => (not_le.2 h1) (this.1 h)
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h2 (Units.mk0 s hs)
  refine ⟨valuation k (x ^ m), zero_lt_iff.2 (by simpa using fun h => absurd h h0), fun g hg i j => ?_⟩
  have e : ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
      algebraMap k E ((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) := by
    rw [map_sub]
    congr 1
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [e]
  refine ((key _ _).2 (hg i j)).trans ?_
  rw [map_pow, map_pow]
  exact hm.le

end UpperTheory.ConvolutionTheory.Loc.NearIdentityAscent

open UpperTheory.ConvolutionTheory.Loc.NearIdentityAscent UpperTheory.ConvolutionTheory.Loc.BallG UpperTheory.V.Z.Tf.Orb in
theorem UpperTheory.ConvolutionTheory.Loc.nearUp :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)), μE.IsHaarMeasure → μk.IsHaarMeasure → ∃ ρ : ValueGroupWithZero k, 0 < ρ ∧ ∀ f ∈ SB (GL (Fin n) k), Function.support f ⊆ ball n ρ →
        ∃ φ ∈ SB (GL (Fin n) E), Match σ μE μk φ f := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ _ _ μE μk hμE hμk
  classical
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  have hj := (hb n).2.2.2.1
  obtain ⟨_, _, _, -⟩ := gLTop E n
  obtain ⟨_, _, _, -⟩ := gLTop k n
  have hθ : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) := ((extCont k E).2.2 n).2 σ
  obtain ⟨r, hr0, hr⟩ := exists_radius (w := valuation E (Module.finrank k E : E))
    ((Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hc.pos.ne'))
  have hr1 : r < 1 := hr.trans_le (valuation_natCast_le_one (E := E) (Module.finrank k E))
  have hs0 : r * valuation E (Module.finrank k E : E) ≠ 0 := (mul_pos hr0 (hr0.trans hr)).ne'
  obtain ⟨ρ, hρ, hρb⟩ := small (k := k) (n := n) hs0
  refine ⟨ρ, hρ, fun f hf hs => ?_⟩
  set K := ballSub n r hr1 with hK
  have hKo : IsOpen (K : Set (GL (Fin n) E)) := isOpen_ball hr0.ne'
  have hKc : IsCompact (K : Set (GL (Fin n) E)) := isCompact_ball hr1
  set K' : Subgroup (GL (Fin n) k) := K.comap (incl : GL (Fin n) k →* GL (Fin n) E) with hK'
  have hKo' : IsOpen (K' : Set (GL (Fin n) k)) := hKo.preimage hj.continuous
  have hKc' : IsCompact (K' : Set (GL (Fin n) k)) := hj.isCompact_preimage hKc
  set A : GL (Fin n) k → ℂ := fun u => ∫ κ in (K' : Set (GL (Fin n) k)), f (κ⁻¹ * u * id κ) ∂μk with hA
  have hAl : IsLocallyConstant A := avg_locConst μk continuous_id hKc' hKo'.measurableSet hf.1
  set c : ℂ := ((μE.real (K : Set (GL (Fin n) E)) : ℝ) : ℂ) with hcd
  have hc0 : c ≠ 0 := Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hKo.measure_ne_zero μE ⟨1, one_mem _⟩, hKc.measure_ne_top⟩)
  let p : GL (Fin n) E × GL (Fin n) k → GL (Fin n) E := fun z => z.1⁻¹ * incl z.2 * sigmaGL σ z.1
  let U : Set (GL (Fin n) E × GL (Fin n) k) := (K : Set _) ×ˢ (K' : Set _)
  let a : GL (Fin n) E × GL (Fin n) k → ℂ := fun z => c⁻¹ * A (z.2 ^ Module.finrank k E)
  let φ : GL (Fin n) E → ℂ := fun g => if h : ∃ z ∈ U, p z = g then a h.choose else 0
  have wd : ∀ z ∈ U, ∀ z' ∈ U, p z = p z' → a z = a z' := by
    rintro ⟨κ, u⟩ ⟨hκ, hu⟩ ⟨κ', u'⟩ ⟨hκ', hu'⟩ e
    have e1 : (κ * κ'⁻¹)⁻¹ * incl u * sigmaGL σ (κ * κ'⁻¹) = incl u' := by
      rw [map_mul, map_inv]
      calc _ = κ' * (κ⁻¹ * incl u * sigmaGL σ κ) * (sigmaGL σ κ')⁻¹ := by group
        _ = κ' * (κ'⁻¹ * incl u' * sigmaGL σ κ') * (sigmaGL σ κ')⁻¹ := congrArg (fun t => κ' * t * (sigmaGL σ κ')⁻¹) e
        _ = _ := by group
    obtain ⟨x, hx⟩ := ((hb n).2.2.1 hgen (κ * κ'⁻¹)).mp
      (rigidNear E n σ _ hc r hr _ hu _ hu' (sigma_incl σ u) (sigma_incl σ u') _ e1)
    have hxK : x ∈ K' := by
      show incl x ∈ K
      rw [hx]
      exact K.mul_mem hκ (K.inv_mem hκ')
    rw [← hx, sigma_incl, ← map_inv, ← map_mul, ← map_mul] at e1
    have e2 := incl_inj e1
    show c⁻¹ * A (u ^ _) = c⁻¹ * A (u' ^ _)
    congr 1
    have e3 : u' ^ Module.finrank k E = x⁻¹ * u ^ Module.finrank k E * x := by
      have := conj_pow (a := x⁻¹) (b := u) (i := Module.finrank k E)
      rw [inv_inv] at this
      rw [← e2, this]
    rw [hA, e3]
    refine (set_left μk K' hKo'.measurableSet (fun κ => f (κ⁻¹ * u ^ Module.finrank k E * id κ)) hxK).symm.trans ?_
    simp only [id, mul_inv_rev, mul_assoc]
  have h1 : ∀ z ∈ U, φ (p z) = a z := fun z hz => by
    have h : ∃ z' ∈ U, p z' = p z := ⟨z, hz, rfl⟩
    simp only [φ, dif_pos h]
    exact wd _ h.choose_spec.1 _ hz h.choose_spec.2
  have h2 : ∀ g, g ∉ p '' U → φ g = 0 := fun g h => dif_neg h
  have ho : IsOpen (p '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨⟨κ, u⟩, ⟨hκ, hu⟩, rfl⟩
    have hO : IsOpen ((fun g => (incl u)⁻¹ * κ * g * (sigmaGL σ κ)⁻¹) ⁻¹' ball n (r * valuation E (Module.finrank k E : E))) :=
      (isOpen_ball hs0).preimage (by fun_prop)
    refine Filter.mem_of_superset (hO.mem_nhds ?_) fun g hg => ?_
    · have : (incl u)⁻¹ * κ * p (κ, u) * (sigmaGL σ κ)⁻¹ = 1 := by simp only [p]; group
      rw [Set.mem_preimage, this]
      exact fun i j => by simp
    · obtain ⟨κ', hκ', u', hu', hf', e⟩ := openNear E n σ _ hc r r hr le_rfl (incl u) hu (sigma_incl σ u) _ hg
      obtain ⟨u', rfl⟩ := ((hb n).2.2.1 hgen u').mp hf'
      refine ⟨(κ' * κ, u * u'), ⟨K.mul_mem hκ' hκ, K'.mul_mem hu hu'⟩, ?_⟩
      change _ = κ'⁻¹ * _ * sigmaGL σ κ' at e
      simp only [p, map_mul]
      calc _ = κ⁻¹ * (κ'⁻¹ * (incl u * incl u') * sigmaGL σ κ') * sigmaGL σ κ := by group
        _ = _ := by rw [← e]; group
  have hφ : φ ∈ SB (GL (Fin n) E) := sb_of_push (hKc.prod hKc') (p := p) (by have := hj.continuous; fun_prop) ho (a := a)
    ((hAl.comp_continuous (f := fun z : GL (Fin n) E × GL (Fin n) k => z.2 ^ Module.finrank k E) (by fun_prop)).comp fun z => c⁻¹ * z) h1 h2
  refine ⟨φ, hφ, nearCore k E σ hgen n μE μk hμE hμk r hr K rfl hKo hKc φ hφ f hf (fun g hg => ?_) (fun g hg => ?_) fun u hu => ?_⟩
  · by_contra h
    refine hg (h2 g ?_)
    rintro ⟨⟨κ, u⟩, ⟨hκ, hu⟩, rfl⟩
    exact h ⟨κ, hκ, u, hu, rfl⟩
  · obtain ⟨u, hu, hf', huq⟩ := exists_fixed_root hc.isom hr (hρb g (hs hg)) (sigma_incl σ g)
    obtain ⟨u, rfl⟩ := ((hb n).2.2.1 hgen u).mp hf'
    exact ⟨u, hu, incl_inj (by rw [map_pow, huq])⟩
  · rw [setIntegral_congr_fun (μ := μE) hKo.measurableSet (g := fun _ => c⁻¹ * A (u ^ Module.finrank k E))
      (fun κ hκ => h1 (κ, u) ⟨hκ, hu⟩), setIntegral_const, Complex.real_smul, ← hcd, mul_inv_cancel_left₀ hc0]
    rfl
