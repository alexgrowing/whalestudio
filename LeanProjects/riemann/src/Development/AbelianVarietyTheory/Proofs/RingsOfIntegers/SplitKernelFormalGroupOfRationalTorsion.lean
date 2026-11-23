import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FiniteHeightFormalGroupUniformisedModel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupPointsOfIntegralChartSpec
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalModuleMatrixApplyPointsActionLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupLawCompMulNZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesMemMapCOfCoeffMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SplitKernel

section Completion

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev comp1)
attribute [local instance] Over.cartesianMonoidalCategory

variable {V : Type} [CommRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] {d : ℕ}

theorem exists_jet_pt {x : Fam G (Fin d)} (hu : IsUnivChart G d x) (C : Chart G) (m : ℕ) :
    ∃ h : Γ(G.left, C.U) →ₐ[V] JetR V (Fin d) m, x m = pt C h := by
  refine exists_pt C (x m) (le_preimage_of_nil C (jetAug V (Fin d) m)
    (fun c => ⟨algebraMap V _ c, (jetAug V (Fin d) m).commutes c⟩) (fun a ha => ⟨m + 1, ?_⟩) (x m) _
    ((spMap_jetAug_alt hu m).trans (pt_eps C V).symm))
  have := Ideal.pow_mem_pow ha (m + 1)
  rwa [ker_jetAug_pow, Ideal.mem_bot] at this

theorem jet_surjective {x : Fam G (Fin d)} (hu : IsUnivChart G d x) (C : Chart G) (m : ℕ)
    (h : Γ(G.left, C.U) →ₐ[V] JetR V (Fin d) m) (hx : x m = pt C h) : Function.Surjective h := by
  have hk : RingHom.ker ((jetAug V (Fin d) m).comp h.range.val) ^ (m + 1) = ⊥ := by
    have h1 : RingHom.ker ((jetAug V (Fin d) m).comp h.range.val) =
        (RingHom.ker (jetAug V (Fin d) m)).comap h.range.val := rfl
    rw [h1, eq_bot_iff]
    refine (Ideal.le_comap_pow _ _).trans' le_rfl |>.trans ?_
    rw [ker_jetAug_pow]
    intro a ha
    exact Subtype.ext ha
  have hv : h.range.val.comp h.rangeRestrict = h := rfl
  obtain ⟨ψ, ⟨h1, h2⟩, -⟩ := hu.2.2 h.range _ m hk (pt C h.rangeRestrict) (by
    rw [spMap_pt, AlgHom.comp_assoc, hv, ← spMap_pt, ← hx, spMap_jetAug_alt hu])
  obtain ⟨ψ₀, -, hψ₀⟩ := hu.2.2 (JetR V (Fin d) m) (jetAug V (Fin d) m) m (ker_jetAug_pow _ m) (x m)
    (spMap_jetAug_alt hu m)
  have e1 := hψ₀ (AlgHom.id V _) ⟨rfl, by
    have : spMap (R₀ := V) (AlgHom.id V (JetR V (Fin d) m)) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      rw [spMap_left]
      exact Spec.map_id _
    rw [this, Category.id_comp]⟩
  have e2 := hψ₀ (h.range.val.comp ψ) ⟨by rw [← AlgHom.comp_assoc, h1], by
    rw [← spMap_comp, Category.assoc, ← h2, spMap_pt, hv, hx]⟩
  intro z
  have : h.range.val (ψ z) = z := DFunLike.congr_fun (e2.trans e1.symm) z
  obtain ⟨s, hs⟩ := (ψ z).2
  exact ⟨s, hs.trans this⟩

theorem exists_expansion {x : Fam G (Fin d)} (hu : IsUnivChart G d x) (C : Chart G) :
    ∃ τ : Γ(G.left, C.U) →ₐ[V] MvPowerSeries (Fin d) V, ∀ m,
      ∃ h : Γ(G.left, C.U) →ₐ[V] JetR V (Fin d) m, x m = pt C h ∧ ∀ s, toJet m (τ s) = h s := by
  obtain ⟨J1, -, J3, J4, -⟩ := jetAlg V (Fin d)
  choose h hh using exists_jet_pt hu C
  choose T hT hT' using J1
  have hc : ∀ m, (jetTruncR V (Fin d) m).comp (h (m + 1)) = h m := fun m =>
    pt_injective C (by rw [← spMap_pt, ← hh, ← hh, hu.1 m])
  choose τ hτ using fun s => J4 (fun m => h m s) fun m => DFunLike.congr_fun (hc m) s
  have hτ' : ∀ s m, T m (τ s) = h m s := fun s m => (hT m _).trans (hτ s m)
  have ext : ∀ g g', (∀ m, T m g = T m g') → g = g' := fun g g' H =>
    J3 g g' fun m => by rw [← hT, ← hT, H]
  refine ⟨⟨⟨⟨⟨τ, ext _ _ fun m => ?_⟩, fun a b => ext _ _ fun m => ?_⟩, ext _ _ fun m => ?_,
    fun a b => ext _ _ fun m => ?_⟩, fun c => ext _ _ fun m => ?_⟩, fun m => ⟨h m, hh m, fun s => hτ s m⟩⟩
  · simp only [hτ', map_one]
  · simp only [hτ', map_mul]
  · simp only [hτ', map_zero]
  · simp only [hτ', map_add]
  · simp only [hτ', AlgHom.commutes]

theorem le_preimage_of_local (C : Chart G) {P P₀ : Type} [CommRing P] [IsLocalRing P] [Algebra V P] [CommRing P₀]
    [Nontrivial P₀] [Algebra V P₀] (q : P →ₐ[V] P₀) (hq : Function.Surjective q) (y : sp P ⟶ G)
    (h₀ : Γ(G.left, C.U) →ₐ[V] P₀) (hy : spMap q ≫ y = pt C h₀) : ⊤ ≤ y.left ⁻¹ᵁ C.U := by
  intro p _
  obtain ⟨M, hM⟩ := Ideal.exists_maximal P₀
  let p₀ : ↥(Spec (CommRingCat.of P₀)) := (⟨M, hM.isPrime⟩ : PrimeSpectrum P₀)
  have hp : (Spec.map (CommRingCat.ofHom q.toRingHom)).base p₀ = closedPoint P := by
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective q.toRingHom hq)
  have e := congrArg (fun y : sp P₀ ⟶ G => y.left.base p₀) hy
  simp only [Over.comp_left, spMap_left, pt_left, Scheme.Hom.comp_apply] at e
  have hc : y.left (closedPoint P) ∈ C.U := by
    rw [← hp, e]
    exact C.hU.range_fromSpec.subset (Set.mem_range_self _)
  have hsp : (p : PrimeSpectrum P) ⤳ closedPoint P :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum P).isPrime.ne_top)
  exact hsp.mem_open (y.left ⁻¹ᵁ C.U).isOpen hc

def subA {κ : Type} [Finite κ] (a : Fin d → MvPowerSeries κ V) (ha : ∀ j, constantCoeff (a j) = 0) :
    MvPowerSeries (Fin d) V →ₐ[V] MvPowerSeries κ V :=
  substAlgHom (hasSubst_of_constantCoeff_zero ha)

theorem subA_apply {κ : Type} [Finite κ] (a : Fin d → MvPowerSeries κ V) (ha : ∀ j, constantCoeff (a j) = 0)
    (g : MvPowerSeries (Fin d) V) : subA a ha g = subst a g := substAlgHom_apply _ g

theorem subA_X {κ : Type} [Finite κ] (a : Fin d → MvPowerSeries κ V) (ha : ∀ j, constantCoeff (a j) = 0)
    (j : Fin d) : subA a ha (X j) = a j := substAlgHom_X _ j

theorem sub_mem_of_toJet_eq {S : Type} [CommRing S] [Algebra V S] (φ : MvPowerSeries (Fin d) V →ₐ[V] S) {J : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ J) (m : ℕ) {g g' : MvPowerSeries (Fin d) V} (h : toJet m g = toJet m g') :
    φ g - φ g' ∈ J ^ (m + 1) := by
  have h1 := GlobalTheory.algHom_sub_aeval_truncTotal_mem φ hφ (m + 1) g
  have h2 := GlobalTheory.algHom_sub_aeval_truncTotal_mem φ hφ (m + 1) g'
  have h3 : Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) V)) ≤
      J.comap (MvPolynomial.aeval (R := V) fun i => φ (X i)) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simpa using hφ j
  have h4 := Ideal.le_comap_pow _ (m + 1) (Ideal.pow_right_mono h3 (m + 1) (Ideal.Quotient.eq.1 h))
  rw [Ideal.mem_comap, map_sub] at h4
  have := Ideal.sub_mem _ (Ideal.add_mem _ h1 h4) h2
  convert this using 1
  ring

theorem exists_completion [IsLocalRing V] {x : Fam G (Fin d)} (hu : IsUnivChart G d x) :
    ∃ (C : Chart G) (σ : Γ(G.left, C.U) →ₐ[V] PS V 1 d),
      (∀ (m : ℕ) (g : PS V 1 d), ∃ s, g - σ s ∈ Ideal.span (Set.range (X : Fin 1 × Fin d → PS V 1 d)) ^ (m + 1)) ∧
      ∀ (f : G ⟶ G) (φ : Pt V 1 d), IsMapOf x x f φ → ∀ (Ω : Type) [CommRing Ω] [Algebra V Ω]
        (χ : PS V 1 d →ₐ[V] Ω), (∀ j, χ (φ j) = 0) → pt C (χ.comp σ) ≫ f = 1 := by
  obtain ⟨C⟩ := exists_chart G
  obtain ⟨τ, hτ⟩ := exists_expansion hu C
  choose h hh hτ using hτ
  have hp : ∀ j, constantCoeff (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt V (n := 1) d 0 j) = 0 :=
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0
  obtain ⟨J1, J2, J3, -, J5⟩ := jetAlg V (Fin 1 × Fin d)
  choose T hT hT' using J1
  have key : ∀ (a : Pt V 1 d) (ha : ∀ j, constantCoeff (a j) = 0) (m : ℕ)
      (ψ : JetR V (Fin d) m →ₐ[V] JetR V (Fin 1 × Fin d) m), (∀ j, ψ (zR m j) = toJet m (a j)) →
      spMap ψ ≫ x m = pt C ((T m).comp ((subA a ha).comp τ)) := fun a ha m ψ hψ => by
    rw [hh, spMap_pt]
    congr 1
    ext s
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, hT, subA_apply, ← hτ,
      (J5 (Fin d) a ha m).2 ψ hψ]
  refine ⟨C, (subA _ hp).comp τ, fun m g => ?_, fun f φ hφ Ω _ _ χ hχ => ?_⟩
  · have hq : HasSubst (fun p : Fin 1 × Fin d => (X p.2 : MvPowerSeries (Fin d) V)) :=
      hasSubst_of_constantCoeff_zero fun p => by simp
    obtain ⟨s, hs⟩ := jet_surjective hu C m (h m) (hh m) (toJet m (subst (fun p : Fin 1 × Fin d => (X p.2 : MvPowerSeries (Fin d) V)) g))
    have e : subA _ hp (subst (fun p : Fin 1 × Fin d => (X p.2 : MvPowerSeries (Fin d) V)) g) = g := by
      rw [subA_apply, subst_comp_subst_apply hq (hasSubst_of_constantCoeff_zero hp)]
      have : (fun p : Fin 1 × Fin d => subst (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt V (n := 1) d 0)
          (X p.2 : MvPowerSeries (Fin d) V)) = X := by
        funext ⟨i, j⟩
        rw [subst_X (hasSubst_of_constantCoeff_zero hp), Subsingleton.elim i 0]
        rfl
      rw [this]
      exact congrFun subst_self g
    refine ⟨s, ?_⟩
    have := sub_mem_of_toJet_eq (subA _ hp) (J := Ideal.span (Set.range (X : Fin 1 × Fin d → PS V 1 d)))
      (fun i => by rw [subA_X]; exact Ideal.subset_span ⟨(0, i), rfl⟩) m (hs.symm.trans (hτ m s).symm)
    rwa [e] at this
  · have hrep : Rep x (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt V (n := 1) d 0)
        (fun m => pt C ((T m).comp ((subA _ hp).comp τ))) := ⟨hp, fun m => by
      obtain ⟨ψ, hψ⟩ := (J5 (Fin d) _ hp m).1
      exact ⟨ψ, hψ, (key _ hp m ψ hψ).symm⟩⟩
    have h2 := hφ.2 1 _ _ hrep
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_comp1_pt_right] at h2
    have h3 : ∀ m, spMap (T m) ≫ (pt C ((subA _ hp).comp τ) ≫ f) = pt C ((T m).comp ((subA φ hφ.1).comp τ)) :=
      fun m => by
        obtain ⟨ψ, hψ, e⟩ := h2.2 m
        rw [← Category.assoc, spMap_pt, ← key φ hφ.1 m ψ hψ]
        exact e
    have hs : Function.Surjective ((jetAug V (Fin 1 × Fin d) 0).comp (T 0)) := fun c =>
      ⟨algebraMap V _ c, AlgHom.commutes _ c⟩
    obtain ⟨h', hh'⟩ := exists_pt C (pt C ((subA _ hp).comp τ) ≫ f) (le_preimage_of_local C _ hs _ _ (by
      rw [← spMap_comp, Category.assoc, h3, spMap_pt]))
    have h4 : h' = (subA φ hφ.1).comp τ := by
      ext1 s
      refine J3 _ _ fun m => ?_
      have := h3 m
      rw [hh', spMap_pt] at this
      rw [← hT, ← hT]
      exact DFunLike.congr_fun (pt_injective C this) s
    have h5 : (jetAug V (Fin d) 0).comp (h 0) = (Algebra.ofId V V).comp (eps C) :=
      pt_injective C (by rw [← spMap_pt, ← hh, spMap_jetAug_alt hu, pt_eps])
    rw [← spMap_pt, Category.assoc, hh', h4, spMap_pt, ← pt_eps C Ω]
    congr 1
    ext s
    have h6 := GlobalTheory.algHom_sub_constantCoeff_mem (χ.comp (subA φ hφ.1)) (K := ⊥)
      (fun i => by rw [AlgHom.comp_apply, subA_X, hχ]; exact zero_mem _) (τ s)
    rw [Ideal.mem_bot, sub_eq_zero] at h6
    have h7 : constantCoeff (τ s) = eps C s := by
      rw [← ((jetAlg V (Fin d)).2.1 0 (τ s)).2, hτ]
      exact DFunLike.congr_fun h5 s
    rw [h7] at h6
    exact h6

theorem range_le_of_descends (C : Chart G) {Ω K : Type} [Field Ω] [Algebra V Ω] [Field K] (ψ : K →+* Ω)
    (h : Γ(G.left, C.U) →ₐ[V] Ω) (a : Spec (CommRingCat.of K) ⟶ G.left)
    (ha : (pt C h).left = Spec.map (CommRingCat.ofHom ψ) ≫ a) (s : Γ(G.left, C.U)) : h s ∈ ψ.range := by
  have hU : ⊤ ≤ a ⁻¹ᵁ C.U := by
    intro p _
    let p₀ : ↥(Spec (CommRingCat.of Ω)) := closedPoint Ω
    have hp : (Spec.map (CommRingCat.ofHom ψ)).base p₀ = p :=
      Subsingleton.elim (α := PrimeSpectrum K) _ _
    have e := congrArg (fun y => y.base p₀) ha
    simp only [pt_left, Scheme.Hom.comp_apply] at e
    show a p ∈ C.U
    rw [← hp, ← e]
    exact C.hU.range_fromSpec.subset (Set.mem_range_self _)
  rw [← chart_eq C a hU, pt_left, ← Category.assoc, cancel_mono, ← Spec.map_comp] at ha
  have := congrArg (fun q => q.hom s) (Spec.map_injective ha)
  exact ⟨_, this.symm⟩

end Completion

section Algebra

open IsLocalRing MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.TB (dLin)

variable {V : Type} [CommRing V] {d : ℕ}

theorem mem_range_of_dense [IsLocalRing V] [IsNoetherianRing V] [IsAdicComplete (maximalIdeal V) V]
    {σ ι : Type} [Finite σ] (f : ι → MvPowerSeries σ V)
    (hf : ∃ M : ℕ, Ideal.span (Set.range (X : σ → MvPowerSeries σ (ResidueField V))) ^ M ≤
      Ideal.span (Set.range fun j => MvPowerSeries.map (residue V) (f j)))
    {Ω : Type} [CommRing Ω] [Algebra V Ω] (χ : MvPowerSeries σ V →ₐ[V] Ω) (hχ : ∀ j, χ (f j) = 0) :
    (∀ g, IsIntegral V (χ g)) ∧
      ((∀ (m : ℕ) (g : MvPowerSeries σ V), ∃ g', χ g' ∈ (algebraMap V Ω).range ∧
        g - g' ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ V)) ^ (m + 1)) →
        ∀ g, χ g ∈ (algebraMap V Ω).range) := by
  have hfin : Module.Finite V (MvPowerSeries σ V ⧸ Ideal.span (Set.range f)) :=
    (GlobalTheory.FormalIsogeny.finiteReduction_iff.2 hf).finite_quotient
  have hker : Ideal.span (Set.range f) ≤ RingHom.ker χ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hχ j
  let χ' := Ideal.Quotient.liftₐ (Ideal.span (Set.range f)) χ fun a ha => hker ha
  have hχ' : ∀ g, χ' (Ideal.Quotient.mk _ g) = χ g := fun g => rfl
  refine ⟨fun g => hχ' g ▸ (Algebra.IsIntegral.isIntegral (R := V) (Ideal.Quotient.mk _ g)).map χ', fun H => ?_⟩
  obtain ⟨M, hM⟩ := hf
  have hlift := GlobalTheory.span_X_pow_le_sup_of_residue V σ ι f M hM
  let N : Submodule V Ω := LinearMap.range χ'.toLinearMap
  have hN : ∀ g, χ g ∈ N := fun g => ⟨Ideal.Quotient.mk _ g, rfl⟩
  have hfg : N.FG := by
    rw [show N = Submodule.map χ'.toLinearMap ⊤ from (Submodule.map_top _).symm]
    exact Module.Finite.fg_top.map _
  have hm : ∀ v ∈ Ideal.map (C : V →+* MvPowerSeries σ V) (maximalIdeal V), ∀ r, χ (r * v) ∈ maximalIdeal V • N := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨c, hc, rfl⟩ := hv
      intro r
      have : χ (r * C c) = c • χ r := by
        rw [map_mul, mul_comm, Algebra.smul_def, ← χ.commutes]; rfl
      rw [this]
      exact Submodule.smul_mem_smul hc (hN r)
    | zero => intro r; simp
    | add u v _ _ hu hv => intro r; rw [mul_add, map_add]; exact add_mem (hu r) (hv r)
    | smul a v _ hv => intro r; rw [smul_eq_mul, ← mul_assoc]; exact hv _
  have hle : N ≤ LinearMap.range (Algebra.linearMap V Ω) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal V) hfg (maximalIdeal_le_jacobson _) ?_
    rintro _ ⟨q, rfl⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨g', ⟨c, hc⟩, hg⟩ := H M g
    obtain ⟨u, hu, v, hv, e⟩ := Submodule.mem_sup.1 (hlift (Ideal.pow_le_pow_right (Nat.le_succ M) hg))
    have : χ g = χ g' + χ (1 * v) := by
      rw [one_mul, show g = g' + (u + v) by rw [e]; ring, map_add, map_add, show χ u = 0 from hker hu, zero_add]
    change χ g ∈ _
    rw [this]
    exact Submodule.add_mem_sup ⟨c, hc⟩ (hm v hv 1)
  exact fun g => hle (hN g)

variable {O : Type} [CommRing O] [StarRing O]

theorem dLin_act_natCast (B : FB V d O) (N : ℕ) : dLin (B.A.act (N : O)) = (N : V) • 1 := by
  have hadd : ∀ a b, dLin (B.A.act (a + b)) = dLin (B.A.act a) + dLin (B.A.act b) := fun a b => by
    rw [B.A.add_act, GlobalTheory.FormalMulN.dLin_add B.G (B.A.const a) (B.A.const b)]
  induction N with
  | zero =>
    have := hadd 0 0
    rw [add_zero, left_eq_add] at this
    rw [Nat.cast_zero, this, Nat.cast_zero, zero_smul]
  | succ n ih =>
    rw [Nat.cast_succ, hadd, ih, B.A.one_act, GlobalTheory.FormalMulN.dLin_pt, Nat.cast_succ, add_smul, one_smul]

theorem span_X_le_span_act [IsLocalRing V] (B : FB V d O) (N : ℕ) (hN : IsUnit (N : V)) :
    Ideal.span (Set.range (X : Fin 1 × Fin d → PS V 1 d)) ≤ Ideal.span (Set.range (B.A.act (N : O))) := by
  classical
  set I := Ideal.span (Set.range (X : Fin 1 × Fin d → PS V 1 d)) with hI
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := I) (Submodule.fg_span (Set.finite_range _)) ?_ ?_
  · refine le_trans ?_ (maximalIdeal_le_jacobson _)
    rw [hI, Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    exact GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp)
  · rw [hI, Ideal.span_le, ← hI]
    rintro _ ⟨⟨z, i⟩, rfl⟩
    obtain rfl : z = 0 := Subsingleton.elim _ _
    have h2 : (C (N : V) * X (0, i) - B.A.act (N : O) i : PS V 1 d) ∈ I ^ 2 := by
      refine GlobalTheory.algHom_mem_pow_of_le_order (AlgHom.id V _) (K := I)
        (g := C (N : V) * X (0, i) - B.A.act (N : O) i)
        (fun p => Ideal.subset_span (Set.mem_range_self p)) (nat_le_order fun e he => ?_)
      rcases Nat.lt_succ_iff_lt_or_eq.1 he with h | h
      · obtain rfl : e = 0 := (Finsupp.degree_eq_zero_iff e).1 (by omega)
        simp [B.A.const]
      · obtain ⟨⟨z, j⟩, rfl⟩ : ∃ p, e = Finsupp.single p 1 := by
          obtain ⟨p, hp⟩ := (Finsupp.sum_eq_one_iff e).1 (by simpa [Finsupp.degree_apply, Finsupp.sum] using h)
          exact ⟨p, hp⟩
        obtain rfl : z = 0 := Subsingleton.elim _ _
        have := congrFun (congrFun (dLin_act_natCast B N) i) j
        change coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act (N : O) i) = _ at this
        rw [map_sub, this, coeff_C_mul, coeff_X]
        by_cases hij : i = j
        · subst hij; simp
        · have : Finsupp.single ((0 : Fin 1), j) 1 ≠ Finsupp.single ((0 : Fin 1), i) 1 := fun h =>
            hij (Prod.ext_iff.1 (Finsupp.single_left_injective one_ne_zero h)).2.symm
          simp [this, Matrix.one_apply_ne hij]
    obtain ⟨u, hu⟩ := hN
    have e : (X (0, i) : PS V 1 d) = C (↑u⁻¹ : V) * (B.A.act (N : O) i + (C (N : V) * X (0, i) - B.A.act (N : O) i)) := by
      rw [add_sub_cancel, ← mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, one_mul]
    rw [SetLike.mem_coe, e]
    refine Ideal.mul_mem_left _ _ (Submodule.add_mem_sup (Ideal.subset_span ⟨i, rfl⟩) ?_)
    rwa [smul_eq_mul, ← sq]

theorem kills_of_unit_mul [IsLocalRing V] (B : FB V d O) (N M : ℕ) (hN : IsUnit (N : V)) {S : Type} [CommRing S]
    [Algebra V S] (χ : PS V 1 d →ₐ[V] S) (h : ∀ i, χ (B.A.act ((N * M : ℕ) : O) i) = 0) (i : Fin d) :
    χ (B.A.act (M : O) i) = 0 := by
  have hs : HasSubst (fun p : Fin 1 × Fin d => (![B.A.act (M : O)] : Fin 1 → Pt V 1 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by simp [B.A.const]
  have hk : Ideal.span (Set.range (B.A.act (N : O))) ≤ RingHom.ker (χ.comp (substAlgHom hs)) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have := h j
    rw [Nat.cast_mul, B.A.mul_act] at this
    rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.comp_apply, substAlgHom_apply]
    exact this
  have := hk (span_X_le_span_act B N hN (Ideal.subset_span ⟨(0, i), rfl⟩))
  rwa [RingHom.mem_ker, AlgHom.comp_apply, substAlgHom_X] at this

theorem kills_of_matV [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
    (B : FB V d O) {n : ℕ} (mu mu' : Matrix (Fin n) (Fin n) O) (N M : ℕ) (hN : IsUnit (N : V))
    (hmu : mu' * mu = ((N * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O)) {S : Type} [CommRing S] [Algebra V S]
    (χ : PS V n d →ₐ[V] S) (h : ∀ b i, χ (matV B mu (fun j => pt V d j) b i) = 0) (b : Fin n) :
    ∃ ψ : PS V 1 d →ₐ[V] PS V n d, (∀ i, ψ (X (0, i)) = X (b, i)) ∧ (∀ f, evV ![pt V d b] f = ψ f) ∧
      ∀ i, χ (ψ (B.A.act (M : O) i)) = 0 := by
  have hp : ∀ (b : Fin n) i, constantCoeff (pt V (n := n) d b i) ∈ maximalIdeal V := fun b i => by simp [pt]
  obtain ⟨ψ, h1, h2⟩ := (evC_spec V (Fin 1 × Fin d) (Fin n × Fin d) Unit
    (fun p => (![pt V d b] : Fin 1 → Pt V n d) p.1 p.2) (fun p => by simpa using hp b p.2)).1
  refine ⟨ψ, fun i => h1 (0, i), h2, kills_of_unit_mul B N M hN (χ.comp ψ) fun i => ?_⟩
  obtain ⟨l1, l2, -, l4, -, -⟩ := MatAct.matV_laws V d O B n n mu' mu _ _ hp hp
  have l0 := (MatAct.matV_laws V d O B n n mu mu _ _ hp hp).1
  obtain ⟨-, -, -, -, l5, l6, -⟩ := MatAct.matV_laws V d O B n n mu' mu _ _ l0 l0
  obtain ⟨ρ, r1, r2⟩ := (evC_spec V (Fin n × Fin d) (Fin n × Fin d) Unit
    (fun p => matV B mu (fun j => pt V d j) p.1 p.2) (fun p => l0 p.1 p.2)).1
  have e := GlobalTheory.algHom_sub_constantCoeff_mem (χ.comp ρ) (K := ⊥)
    (fun p => by rw [AlgHom.comp_apply, r1, h]; exact zero_mem _) (matV B mu' (fun j => pt V d j) b i)
  rw [l6, map_zero, sub_zero, Ideal.mem_bot, AlgHom.comp_apply, ← r2] at e
  have e2 := l5 b i
  rw [← l2, hmu, l4] at e2
  rw [AlgHom.comp_apply, ← h2]
  exact (congrArg χ e2).symm.trans e

end Algebra

section Main

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem pow_eq_one_iff_of_push {S S' W : Scheme.{0}} {g : S' ⟶ S} {t : W ⟶ S} {t' : W ⟶ S'} {A : Over S}
    {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left} (ht : t' ≫ g = t) (hp : IsGrpPullback A' A g Φ)
    {x : Over.mk t ⟶ A} {x' : Over.mk t' ⟶ A'} (hx : x'.left ≫ Φ = x.left) (k : ℕ) : x' ^ k = 1 ↔ x ^ k = 1 := by
  subst ht
  have e : pushHom hp (Over.mk t') x' = x := Over.OverMorphism.ext hx
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg (pushHom hp (Over.mk t')) h
    rw [map_pow, map_one, e] at this
    exact this
  · have e₂ : pushHom hp (Over.mk t') (x' ^ k) = pushHom hp (Over.mk t') 1 := by
      rw [map_pow, map_one, e]; exact h
    exact Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun q => q.left) e₂) (by rw [Over.w, Over.w]))

theorem descends_of_allRat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {V K : Type} [CommRing V] [Field K] [Algebra V K] {x : Sp K ⟶ Xo.X}
    {G : SAB H (Sp V)} {t' : SAB H (Sp K)} (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap V K)))
    {M : ℕ} (hM : AllRat Xo x M) {Ω : Type} [Field Ω] [Algebra V Ω] (ψ : K →+* Ω)
    (hψ : ψ.comp (algebraMap V K) = algebraMap V Ω) (w : Over.mk (spMap (algebraMap V Ω)) ⟶ G.G) (hw : w ^ M = 1) :
    ∃ a : Sp K ⟶ G.G.left, w.left = spMap ψ ≫ a := by
  have ht : spMap ψ ≫ spMap (algebraMap V K) = spMap (algebraMap V Ω) := by
    rw [← hψ, ← Spec.map_comp]; rfl
  have e : w.left ≫ G.G.hom = spMap ψ ≫ spMap (algebraMap V K) := (Over.w w).trans ht.symm
  let w' : Over.mk (spMap ψ) ⟶ t'.G := Over.homMk (m2.cart.1.lift _ _ e) (m2.cart.1.lift_snd _ _ _)
  have h2 : w'.left ≫ m2.φ = w.left := m2.cart.1.lift_fst _ _ _
  have hw' := (pow_eq_one_iff_of_push ht m2.cart h2 M).2 hw
  let w₁ : ptO Xo (spMap ψ ≫ x) ⟶ Xo.univ.t.G := Over.homMk (w'.left ≫ m1.φ) (by
    rw [Category.assoc, m1.cart.1.w, ← Category.assoc, Over.w w']; rfl)
  obtain ⟨a, ha⟩ := hM Ω ψ w₁ ((pow_eq_one_iff_of_push (x := w₁) rfl m1.cart rfl M).1 hw')
  have e₁ : a.left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ x := (Over.w a).trans (Category.id_comp _).symm
  refine ⟨m1.cart.1.lift _ _ e₁ ≫ m2.φ, ?_⟩
  rw [← h2, ← Category.assoc]
  congr 1
  refine m1.cart.1.hom_ext ?_ ?_
  · rw [Category.assoc, IsPullback.lift_fst]; exact ha
  · rw [Category.assoc, IsPullback.lift_snd, Category.comp_id]; exact Over.w w'

theorem isUnit_natCast_of_coprime {V : Type} [CommRing V] [IsLocalRing V] {k ℓ : ℕ} (h : Nat.Coprime k ℓ)
    (hℓ : ¬ IsUnit (ℓ : V)) : IsUnit (k : V) := by
  obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom V)
  simp only [eq_intCast, Int.cast_natCast] at e
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one e with h1 | h1
  · exact isUnit_of_mul_isUnit_right h1
  · exact absurd (isUnit_of_mul_isUnit_right h1) hℓ

theorem splitKer_of_allRat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (n : ℕ) (mu mu' : Matrix (Fin n) (Fin n) (𝓞 E)) (k M : ℕ), Nat.Coprime k ℓ → 0 < M → mu' * mu = ((k * M : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) → AllRat Xo (xOf y) M → SplitKer B mu ∧ ∀ α ∈ kerM B mu, ∀ a : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G), (∀ b, FormPt C (a b) (α b)) → ∀ b, (∃ j : ℕ, a b ^ (ℓ ^ j) = 1) := by
  intro E _ _ _ H Dw l Xo c inst hstar T io y C hC B hB ℓ hℓ hu n mu mu' k M hk hM hmu hrat
  have hfh := GlobalTheory.PlaceFinHt.finHt_of_good E H Dw l Xo c hstar T io y C hC B hB
  obtain ⟨p1, p2, -, p4, -⟩ := GlobalTheory.PlaceFormPt.formPt_spec E H Dw l Xo c hstar T io y C B hB
  refine ⟨fun Ω _ _ hinj χ hχ p => ?_, fun α hα a ha b => ?_⟩
  · obtain rfl := GlobalTheory.PowGerm.starSt E H inst hstar
    letI := H.starRing
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hB
    obtain ⟨x, hx, hm⟩ := GlobalTheory.PowGerm.univConv T.V C.I.G.G _ C.xT
      (GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C) _ (GlobalTheory.PowGerm.oneCol _)
    have hc := C.chartT
    have hf := C.frameT
    rw [← h1, ← h2] at hc
    rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6] at hf
    have hl := (GlobalTheory.LinkLaw.linkLaw E H T.V C.I.G _ B C.tgT C.xT C.eT C.wPT hc hf C.primT x hx hm).2 (M : 𝓞 E)
    obtain ⟨ψ, hψ, -, hkill⟩ := kills_of_matV B mu mu' k M (isUnit_natCast_of_coprime hk hu) hmu χ hχ p.1
    obtain ⟨U, σ, hd, hσ⟩ := exists_completion hx
    have hw := hσ _ _ hl Ω (χ.comp ψ) hkill
    rw [GlobalTheory.PlaceFinHt.oact_natCast, MonObj.comp_pow, Category.comp_id] at hw
    let j0 : T.Fr →+* Ω := IsFractionRing.lift hinj
    have hj0 : ∀ v, j0 (algebraMap T.V T.Fr v) = algebraMap T.V Ω v := fun v => IsFractionRing.lift_algebraMap hinj v
    obtain ⟨a, ha⟩ := descends_of_allRat C.I.m1 C.I.m2 hrat j0 (RingHom.ext hj0) _ hw
    obtain ⟨hint, hall⟩ := mem_range_of_dense (B.A.act (M : 𝓞 E)) (hfh M hM) (χ.comp ψ) hkill
    have := hall (fun m g => ?_) (MvPowerSeries.X (0, p.2))
    · rwa [AlgHom.comp_apply, hψ] at this
    · obtain ⟨s, hs⟩ := hd m g
      refine ⟨σ s, ?_, hs⟩
      obtain ⟨z, hz⟩ := range_le_of_descends U j0 _ a ha s
      have hz' : IsIntegral T.V z := by
        have := hint (σ s)
        rw [show (χ.comp ψ) (σ s) = j0 z from hz.symm] at this
        exact (isIntegral_algHom_iff (⟨j0, hj0⟩ : T.Fr →ₐ[T.V] Ω) j0.injective).1 this
      obtain ⟨v, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hz'
      exact ⟨v, (hj0 v).symm.trans hz⟩
  · obtain ⟨j, M', hM', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' ℓ hℓ.ne_one
    have hN : IsUnit ((k * M' : ℕ) : T.V) := isUnit_natCast_of_coprime
      (Nat.Coprime.mul_left hk ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hM').symm) hu
    have hx : ∀ b i, MvPowerSeries.constantCoeff ((fun j => cpt (n := 0) (α j)) b i) ∈ maximalIdeal T.V :=
      fun b i => by simpa [cpt] using hα.1 b i
    obtain ⟨⟨χ, c1, c2⟩, -⟩ := evC_spec T.V (Fin n × Fin (chD C.ch)) (Fin 0 × Fin (chD C.ch)) Unit
      (fun s => cpt (n := 0) (α s.1) s.2) (fun s => hx s.1 s.2)
    obtain ⟨ψ, hψ, hψ', hkill⟩ := kills_of_matV B mu mu' (k * M') (ℓ ^ j) hN
      (by rw [hmu]; congr 2; ring) χ (fun b i => by
        rw [← c2]
        exact ((MatAct.matV_laws T.V _ _ B n 0 mu mu _ _ hx hx).2.2.2.2.1 b i).trans
          (congrFun (congrFun hα.2 b) i)) b
    have hz : (cpt 0 : Pt T.V 0 (chD C.ch)) = compV (B.A.act ((ℓ ^ j : ℕ) : 𝓞 E)) (cpt (α b)) := by
      funext i
      have e := (evC_spec T.V (Fin 1 × Fin (chD C.ch)) (Fin n × Fin (chD C.ch)) (Fin 0 × Fin (chD C.ch))
        (fun p => (![pt T.V (chD C.ch) b] : Fin 1 → Pt T.V n (chD C.ch)) p.1 p.2)
        (fun p => by simp [pt])).2.2.2 (fun s => cpt (n := 0) (α s.1) s.2) (fun s => hx s.1 s.2)
        (B.A.act ((ℓ ^ j : ℕ) : 𝓞 E) i)
      have e' := hkill i
      rw [← hψ', ← c2] at e'
      have e'' := e'.symm.trans e
      refine ((map_zero _).trans e'').trans ?_
      unfold compV evV
      congr 1
      funext p
      rw [c2]
      obtain ⟨z, q⟩ := p
      obtain rfl : z = 0 := Subsingleton.elim _ _
      exact c1 (b, q)
    refine ⟨j, ?_⟩
    have := (p2 _ _ _ _ (p4 _ _ _ _ (ha b) hz) p1).2 rfl
    rwa [GlobalTheory.PlaceFinHt.oact_natCast, MonObj.comp_pow, Category.comp_id] at this

end Main

end GlobalTheory.SplitKernel
