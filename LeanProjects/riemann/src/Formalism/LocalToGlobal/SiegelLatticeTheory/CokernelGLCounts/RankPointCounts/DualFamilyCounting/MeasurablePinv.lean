import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EmbVHomInjective
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BoxFundT

noncomputable section

open MeasureTheory NumberField NumberField.mixedEmbedding Formalism.BasicNotions
open scoped ENNReal Classical

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fib

variable {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] (μ : Measure V) [SigmaFinite μ]
  [μ.IsAddRightInvariant]

theorem fib2 (Γ : AddSubgroup (V × V)) [Countable Γ] (A₁ A₂ : AddSubgroup V)
    (hA₁ : ∀ x, x ∈ A₁ ↔ ∃ y, (x, y) ∈ Γ) (hA₂ : ∀ y, y ∈ A₂ ↔ ((0 : V), y) ∈ Γ)
    (F₁ F₂ : Set V) (hF₁ : MeasurableSet F₁) (hF₂ : MeasurableSet F₂)
    (hd₁ : ∀ v, ∃! a : A₁, (a : V) + v ∈ F₁) (hd₂ : ∀ v, ∃! a : A₂, (a : V) + v ∈ F₂)
    (K : Set (V × V)) (hK : MeasurableSet K) (hKd : ∀ g, ∃! γ : Γ, (γ : V × V) + g ∈ K) :
    (μ.prod μ) K = μ F₁ * μ F₂ := by
  classical
  haveI : μ.IsAddLeftInvariant := ⟨fun g => by
    have h : (fun x : V => g + x) = fun x => x + g := funext fun x => add_comm g x
    rw [h]
    exact Measure.IsAddRightInvariant.map_add_right_eq_self g⟩
  haveI : MeasurableAdd (V × V) :=
    ⟨fun c => by
      first
        | exact ((measurable_const_add c.1).comp measurable_fst).prodMk ((measurable_const_add c.2).comp measurable_snd)
        | exact ((measurable_const_add c.1).comp measurable_fst).prod_mk ((measurable_const_add c.2).comp measurable_snd),
     fun c => by
      first
        | exact ((measurable_add_const c.1).comp measurable_fst).prodMk ((measurable_add_const c.2).comp measurable_snd)
        | exact ((measurable_add_const c.1).comp measurable_fst).prod_mk ((measurable_add_const c.2).comp measurable_snd)⟩
  haveI : MeasurableConstVAdd Γ (V × V) := ⟨fun c => measurable_const_add (c : V × V)⟩
  haveI : VAddInvariantMeasure Γ (V × V) (μ.prod μ) :=
    ⟨fun c s _ => measure_preimage_add (μ.prod μ) (c : V × V) s⟩
  have hK' : ∀ g : V × V, ∃! γ : Γ, (γ : V × V) + g ∈ F₁ ×ˢ F₂ := by
    rintro ⟨x, y⟩
    obtain ⟨a₁, ha₁, hu₁⟩ := hd₁ x
    obtain ⟨s, hs⟩ := (hA₁ (a₁ : V)).1 a₁.2
    obtain ⟨a₂, ha₂, hu₂⟩ := hd₂ (s + y)
    have hmem : ((a₁ : V), s + (a₂ : V)) ∈ Γ := by
      have h2 : ((0 : V), (a₂ : V)) ∈ Γ := (hA₂ _).1 a₂.2
      have h3 := Γ.add_mem hs h2
      simpa using h3
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · show (a₁ : V) + x ∈ F₁ ∧ s + (a₂ : V) + y ∈ F₂
      refine ⟨ha₁, ?_⟩
      have e : s + (a₂ : V) + y = (a₂ : V) + (s + y) := by abel
      rw [e]
      exact ha₂
    · rintro ⟨⟨g₁, g₂⟩, hg⟩ hgK
      change g₁ + x ∈ F₁ ∧ g₂ + y ∈ F₂ at hgK
      have hg₁ : g₁ ∈ A₁ := (hA₁ g₁).2 ⟨g₂, hg⟩
      have e₁ : g₁ = (a₁ : V) := congrArg Subtype.val (hu₁ ⟨g₁, hg₁⟩ hgK.1)
      have hd : ((0 : V), g₂ - s) ∈ Γ := by
        have h3 := Γ.sub_mem hg hs
        simpa [e₁] using h3
      have hg₂ : g₂ - s ∈ A₂ := (hA₂ _).2 hd
      have e₂ : g₂ - s = (a₂ : V) := by
        refine congrArg Subtype.val (hu₂ ⟨g₂ - s, hg₂⟩ ?_)
        have e : g₂ - s + (s + y) = g₂ + y := by abel
        show g₂ - s + (s + y) ∈ F₂
        rw [e]
        exact hgK.2
      apply Subtype.ext
      show (g₁, g₂) = ((a₁ : V), s + (a₂ : V))
      rw [e₁, ← e₂]
      congr 1
      abel
  have hFK : IsAddFundamentalDomain Γ K (μ.prod μ) :=
    IsAddFundamentalDomain.mk' hK.nullMeasurableSet hKd
  have hFK' : IsAddFundamentalDomain Γ (F₁ ×ˢ F₂) (μ.prod μ) :=
    IsAddFundamentalDomain.mk' (hF₁.prod hF₂).nullMeasurableSet hK'
  rw [hFK.measure_eq hFK', Measure.prod_prod]

end Fib

variable {D : D7} (X : HidaSetting D)

theorem embS_conj (τ : D.what₂.Tau) (x : D.host.E) : embS D τ (D.host.conj x) = starRingEnd ℂ (embS D τ x) :=
  D.host.toHostAx.conjE_apply (embS D τ) x

theorem mem_F_iff (x : D.host.E) : x ∈ D.host.F ↔ D.host.conj x = x := by
  rw [NumberField.mem_maximalRealSubfield_iff]
  constructor
  · intro h
    apply D.host.φ₀.injective
    rw [D.host.toHostAx.conjE_apply]
    exact h _
  · intro h φ
    have e := D.host.toHostAx.conjE_apply φ x
    rw [h] at e
    exact e.symm

instance : IsEmpty {w : InfinitePlace D.host.F // w.IsComplex} :=
  ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩

def psiP : InfinitePlace X.B.I.F ≃ InfinitePlace D.host.F where
  toFun v := v.comap ((fIso X).symm : D.host.F →+* X.B.I.F)
  invFun w := w.comap ((fIso X) : X.B.I.F →+* D.host.F)
  left_inv v := by
    show (v.comap _).comap _ = v
    rw [← InfinitePlace.comap_comp]
    have : ((fIso X).symm : D.host.F →+* X.B.I.F).comp ((fIso X) : X.B.I.F →+* D.host.F) = RingHom.id _ := by
      ext a; simp
    rw [this]; rfl
  right_inv w := by
    show (w.comap _).comap _ = w
    rw [← InfinitePlace.comap_comp]
    have : ((fIso X) : X.B.I.F →+* D.host.F).comp ((fIso X).symm : D.host.F →+* X.B.I.F) = RingHom.id _ := by
      ext a; simp
    rw [this]; rfl

theorem fIso_coe (a : X.B.I.F) : ((fIso X a : D.host.F) : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E a) := rfl

theorem emb_symm (v : InfinitePlace X.B.I.F) (y : D.host.F) :
    v.embedding ((fIso X).symm y) = embS D (X.pl v) (y : D.host.E) := by
  have hy : (y : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E ((fIso X).symm y)) := by
    rw [← fIso_coe, RingEquiv.apply_symm_apply]
  rw [hy, ← X.φ_eq, X.B.I.φ_over]

theorem psiP_embedding (v : InfinitePlace X.B.I.F) (y : D.host.F) :
    (psiP X v).embedding y = embS D (X.pl v) (y : D.host.E) := by
  have hr : (psiP X v).IsReal := IsTotallyReal.isReal _
  show (v.comap ((fIso X).symm : D.host.F →+* X.B.I.F)).embedding y = _
  rw [InfinitePlace.comap_embedding_of_isReal _ hr, RingHom.comp_apply]
  exact emb_symm X v y

def reVHom : D.host.F →+ (InfinitePlace X.B.I.F → ℝ) where
  toFun y := fun v => (embS D (X.pl v) (y : D.host.E)).re
  map_zero' := by funext v; simp
  map_add' a b := by funext v; simp

theorem mixed_re (y : D.host.F) (v : InfinitePlace X.B.I.F) :
    (mixedEmbedding D.host.F y).1 ⟨psiP X v, IsTotallyReal.isReal _⟩ = reVHom X y v := by
  rw [mixedEmbedding_apply_isReal]
  show _ = (embS D (X.pl v) (y : D.host.E)).re
  rw [← psiP_embedding X v y, ← InfinitePlace.embedding_of_isReal_apply, Complex.ofReal_re]

def Pmap (x : mixedSpace D.host.F) : InfinitePlace X.B.I.F → ℝ := fun v => x.1 ⟨psiP X v, IsTotallyReal.isReal _⟩

def Pinv (z : InfinitePlace X.B.I.F → ℝ) : mixedSpace D.host.F :=
  (fun w => z ((psiP X).symm w.1), fun w => isEmptyElim w)

theorem Pmap_Pinv (z : InfinitePlace X.B.I.F → ℝ) : Pmap X (Pinv X z) = z := by
  funext v
  simp [Pmap, Pinv]

theorem Pinv_Pmap (x : mixedSpace D.host.F) : Pinv X (Pmap X x) = x := by
  refine Prod.ext ?_ ?_
  · funext w
    simp [Pmap, Pinv]
  · funext w
    exact isEmptyElim w

theorem Pmap_add (x y : mixedSpace D.host.F) : Pmap X (x + y) = Pmap X x + Pmap X y := rfl

theorem Pmap_mp : MeasurePreserving (Pmap X) volume volume := by
  let e : {w : InfinitePlace D.host.F // w.IsReal} ≃ InfinitePlace X.B.I.F :=
    { toFun := fun w => (psiP X).symm w.1
      invFun := fun v => ⟨psiP X v, IsTotallyReal.isReal _⟩
      left_inv := fun w => Subtype.ext ((psiP X).apply_symm_apply w.1)
      right_inv := fun v => (psiP X).symm_apply_apply v }
  haveI : IsProbabilityMeasure (volume : Measure ({w : InfinitePlace D.host.F // w.IsComplex} → ℂ)) := by
    rw [volume_pi, Measure.pi_of_empty]
    infer_instance
  have h1 : MeasurePreserving (Prod.fst : mixedSpace D.host.F → ({w : InfinitePlace D.host.F // w.IsReal} → ℝ))
      volume volume := measurePreserving_fst
  have h2 := volume_preserving_arrowCongr' e (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)
  convert h2.comp h1 using 1
  all_goals first
    | rfl
    | (funext x; rfl)

theorem measurable_Pinv : Measurable (Pinv X) := by
  unfold Pinv
  fun_prop

def reLat (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) : AddSubgroup (InfinitePlace X.B.I.F → ℝ) :=
  ((𝔞 : Submodule (𝓞 D.host.F) D.host.F).toAddSubgroup).map (reVHom X)

theorem Pmap_emb (y : D.host.F) : Pmap X (mixedEmbedding D.host.F y) = reVHom X y := by
  funext v
  exact mixed_re X y v

theorem realIdealBlock (𝔞 : (FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)ˣ) :
    (∃ F : Set (InfinitePlace X.B.I.F → ℝ), MeasurableSet F ∧ ∀ v, ∃! a : reLat X 𝔞, (a : InfinitePlace X.B.I.F → ℝ) + v ∈ F) ∧
    ∀ F : Set (InfinitePlace X.B.I.F → ℝ), MeasurableSet F →
      (∀ v, ∃! a : reLat X 𝔞, (a : InfinitePlace X.B.I.F → ℝ) + v ∈ F) →
        volume F = ENNReal.ofReal ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) : ℝ) *
          √|(discr D.host.F : ℝ)|) := by
  classical
  let b := fractionalIdealLatticeBasis D.host.F 𝔞
  have hmem : ∀ z : mixedSpace D.host.F, z ∈ Submodule.span ℤ (Set.range b) ↔ Pmap X z ∈ reLat X 𝔞 := by
    intro z
    rw [mem_span_fractionalIdealLatticeBasis]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Pmap_emb]
      exact AddSubgroup.mem_map_of_mem _ hy
    · rintro ⟨y, hy, hyz⟩
      refine ⟨y, hy, ?_⟩
      have e : Pmap X (mixedEmbedding D.host.F y) = Pmap X z := by
        rw [Pmap_emb]
        exact hyz
      have e2 := congrArg (Pinv X) e
      rwa [Pinv_Pmap, Pinv_Pmap] at e2
  have hPinv_add : ∀ u w, Pinv X (u + w) = Pinv X u + Pinv X w := by
    intro u w
    have e : u + w = Pmap X (Pinv X u + Pinv X w) := by
      rw [Pmap_add, Pmap_Pinv, Pmap_Pinv]
    rw [e, Pinv_Pmap]
  have htr : ∀ S : Set (InfinitePlace X.B.I.F → ℝ),
      (∀ v, ∃! a : reLat X 𝔞, (a : InfinitePlace X.B.I.F → ℝ) + v ∈ S) →
      ∀ z, ∃! l : Submodule.span ℤ (Set.range b), l +ᵥ z ∈ Pmap X ⁻¹' S := by
    intro S hS z
    obtain ⟨a, ha, hu⟩ := hS (Pmap X z)
    have hl : Pinv X a ∈ Submodule.span ℤ (Set.range b) := by
      rw [hmem, Pmap_Pinv]
      exact a.2
    refine ⟨⟨Pinv X a, hl⟩, ?_, ?_⟩
    · show Pmap X (Pinv X a + z) ∈ S
      rw [Pmap_add, Pmap_Pinv]
      exact ha
    · rintro ⟨l, hl'⟩ hlS
      change Pmap X (l + z) ∈ S at hlS
      rw [Pmap_add] at hlS
      have e := hu ⟨Pmap X l, (hmem l).1 hl'⟩ hlS
      apply Subtype.ext
      show l = Pinv X a
      rw [← e]
      exact (Pinv_Pmap X l).symm
  have hrev : ∀ T : Set (mixedSpace D.host.F),
      (∀ z, ∃! l : Submodule.span ℤ (Set.range b), l +ᵥ z ∈ T) →
      ∀ v, ∃! a : reLat X 𝔞, (a : InfinitePlace X.B.I.F → ℝ) + v ∈ Pinv X ⁻¹' T := by
    intro T hT v
    obtain ⟨l, hl, hu⟩ := hT (Pinv X v)
    have ha : Pmap X l ∈ reLat X 𝔞 := (hmem l).1 l.2
    refine ⟨⟨Pmap X l, ha⟩, ?_, ?_⟩
    · show Pinv X (Pmap X l + v) ∈ T
      rw [hPinv_add, Pinv_Pmap]
      exact hl
    · rintro ⟨a, ha'⟩ haT
      change Pinv X (a + v) ∈ T at haT
      rw [hPinv_add] at haT
      have hl2 : Pinv X a ∈ Submodule.span ℤ (Set.range b) := by
        rw [hmem, Pmap_Pinv]
        exact ha'
      have e := hu ⟨Pinv X a, hl2⟩ haT
      apply Subtype.ext
      show a = Pmap X l
      rw [← e]
      exact (Pmap_Pinv X a).symm
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range b)) (mixedSpace D.host.F) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : mixedSpace D.host.F) s⟩
  have hFD : IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)) (ZSpan.fundamentalDomain b) volume :=
    ZSpan.isAddFundamentalDomain b volume
  have hvol : volume (ZSpan.fundamentalDomain b) =
      ENNReal.ofReal ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) : ℝ) *
        √|(discr D.host.F : ℝ)|) := by
    rw [volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_latticeBasis,
      IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, one_mul,
      ENNReal.ofReal_mul (by exact_mod_cast FractionalIdeal.absNorm_nonneg _), ← ENNReal.ofReal_coe_nnreal]
    congr 2
    first
      | simp [Int.norm_eq_abs]
      | simp [Real.coe_sqrt, Int.norm_eq_abs]
      | (rw [NNReal.coe_sqrt]; simp [Int.norm_eq_abs])
  refine ⟨⟨Pinv X ⁻¹' ZSpan.fundamentalDomain b,
    measurable_Pinv X (ZSpan.fundamentalDomain_measurableSet b),
    hrev _ (fun z => ZSpan.exist_unique_vadd_mem_fundamentalDomain b z)⟩, ?_⟩
  intro F hF hd
  have hF' : IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)) (Pmap X ⁻¹' F) volume :=
    IsAddFundamentalDomain.mk' ((Pmap_mp X).measurable hF).nullMeasurableSet (htr F hd)
  rw [← (Pmap_mp X).measure_preimage hF.nullMeasurableSet, hF'.measure_eq hFD, hvol]

end Formalism.L2.SG.Pf.NcReal.JX.CovB
