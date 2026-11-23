import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.FJE.TransportInt

theorem isAddFundamentalDomain_prod {X : Type*} [AddCommGroup X] [MeasurableSpace X]
    (Γ : AddSubgroup X) {μ : Measure X} [SFinite μ] {F : Set X}
    (h : IsAddFundamentalDomain Γ F μ) :
    IsAddFundamentalDomain (Γ.prod Γ) (F ×ˢ F) (μ.prod μ) := by
  refine ⟨h.nullMeasurableSet.prod h.nullMeasurableSet, ?_, ?_⟩
  · have h1 : ∀ᵐ z ∂(μ.prod μ), ∃ g : Γ, g +ᵥ z.1 ∈ F :=
      Measure.quasiMeasurePreserving_fst.ae h.ae_covers
    have h2 : ∀ᵐ z ∂(μ.prod μ), ∃ g : Γ, g +ᵥ z.2 ∈ F :=
      Measure.quasiMeasurePreserving_snd.ae h.ae_covers
    filter_upwards [h1, h2] with z a b
    obtain ⟨g, hg⟩ := a
    obtain ⟨g', hg'⟩ := b
    exact ⟨⟨(g.1, g'.1), g.2, g'.2⟩, hg, hg'⟩
  · intro g g' hne
    have key : ∀ k : Γ.prod Γ, (k +ᵥ (F ×ˢ F)) =
        (((⟨k.1.1, k.2.1⟩ : Γ)) +ᵥ F) ×ˢ (((⟨k.1.2, k.2.2⟩ : Γ)) +ᵥ F) := by
      intro k
      ext z
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod]
      rfl
    show μ.prod μ ((g +ᵥ (F ×ˢ F)) ∩ (g' +ᵥ (F ×ˢ F))) = 0
    rw [key, key, Set.prod_inter_prod, Measure.prod_prod]
    by_cases h1 : g.1.1 = g'.1.1
    · have h2 : g.1.2 ≠ g'.1.2 := fun h2 => hne (Subtype.ext (Prod.ext h1 h2))
      have : ((⟨g.1.2, g.2.2⟩ : Γ)) ≠ ⟨g'.1.2, g'.2.2⟩ := fun h3 => h2 (congrArg Subtype.val h3)
      have h4 := h.aedisjoint this
      simp only [Function.onFun] at h4
      rw [show μ _ = 0 from h4, mul_zero]
    · have : ((⟨g.1.1, g.2.1⟩ : Γ)) ≠ ⟨g'.1.1, g'.2.1⟩ := fun h3 => h1 (congrArg Subtype.val h3)
      have h4 := h.aedisjoint this
      simp only [Function.onFun] at h4
      rw [show μ _ = 0 from h4, zero_mul]

section Generic

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem map_eq_of_fundamentalDomain (L : AddSubgroup G) [Countable L] (ν : Measure G)
    [ν.IsAddHaarMeasure] {F : Set G} (hF : IsAddFundamentalDomain L F ν) (h0 : ν F ≠ 0)
    (hT0 : ν F ≠ ∞) (T : G ≃ₜ+ G) (hr : ∀ x, T x ∈ L ↔ x ∈ L) :
    ν.map T = ν ∧ IsAddFundamentalDomain L (T '' F) ν := by
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  haveI hH : (ν.map T).IsAddHaarMeasure :=
    T.toAddEquiv.isAddHaarMeasure_map ν T.continuous T.symm.continuous
  have e := Measure.isAddLeftInvariant_eq_smul (ν.map T) ν
  have hF2 : IsAddFundamentalDomain L F (ν.map T) :=
    hF.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have hF3 : IsAddFundamentalDomain L (T '' F) (ν.map T) := by
    let g : L ≃ L :=
      { toFun := fun γ => ⟨T.symm γ, (hr _).1 (by rw [T.apply_symm_apply]; exact γ.2)⟩
        invFun := fun γ => ⟨T γ, (hr _).2 γ.2⟩
        left_inv := fun γ => Subtype.ext (T.apply_symm_apply _)
        right_inv := fun γ => Subtype.ext (T.symm_apply_apply _) }
    refine hF.image_of_equiv T.toEquiv ?_ g fun γ x => ?_
    · refine ⟨(T.symm.continuous.measurable : Measurable (T.symm : G → G)), ?_⟩
      have : (ν.map T).map T.symm = ν := by
        have hs : Measurable (T.symm : G → G) := T.symm.continuous.measurable
        have ht : Measurable (T : G → G) := T.continuous.measurable
        rw [Measure.map_map hs ht]
        have : (T.symm ∘ T : G → G) = id := funext T.symm_apply_apply
        rw [this, Measure.map_id]
      exact this.absolutelyContinuous
    · change T (T.symm γ + x) = γ + T x
      rw [map_add, T.apply_symm_apply]
  have h3 : ν.map T F = ν.map T (T '' F) := hF2.measure_eq hF3
  have h4 : ν.map T (T '' F) = ν F := by
    rw [hemb.map_apply, Set.preimage_image_eq _ T.injective]
  have hc : Measure.addHaarScalarFactor (ν.map T) ν = 1 := by
    have h5 : ν.map T F = ν F := h3.trans h4
    rw [e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h5
    have h6 := (ENNReal.mul_eq_right h0 hT0).1 h5
    simpa using h6
  have hm : ν.map T = ν := by rw [e, hc, one_smul]
  refine ⟨hm, ?_⟩
  rwa [hm] at hF3

theorem setIntegral_comp_eq (L : AddSubgroup G) [Countable L] (ν : Measure G)
    [ν.IsAddHaarMeasure] {F : Set G} (hF : IsAddFundamentalDomain L F ν) (h0 : ν F ≠ 0)
    (hT0 : ν F ≠ ∞) (T : G ≃ₜ+ G) (hr : ∀ x, T x ∈ L ↔ x ∈ L) (A : G → ℂ)
    (hA : ∀ γ ∈ L, ∀ v, A (γ + v) = A v) :
    ∫ v in F, A (T v) ∂ν = ∫ v in F, A v ∂ν := by
  obtain ⟨hm, hF3⟩ := map_eq_of_fundamentalDomain L ν hF h0 hT0 T hr
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have h1 : ∫ v in T '' F, A v ∂(ν.map T) = ∫ v in F, A (T v) ∂ν := by
    rw [hemb.setIntegral_map, Set.preimage_image_eq _ T.injective]
  rw [← h1, hm]
  exact hF3.setIntegral_eq hF fun γ a => hA γ γ.2 a

end Generic

end GlobalTheory.CompanionTheory.FJE.TransportInt

namespace GlobalTheory.CompanionTheory.FJE.TransportInt

theorem transport_int : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (T : (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p)), (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) → (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T.symm (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) → ∀ A : Mx D ρ p × Mx D ρ p → ℂ, (∀ (ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E) v, A (v + (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂)) = A v) → ∫ v in m.𝓕 ×ˢ m.𝓕, A (T v) ∂(m.μ.prod m.μ) = ∫ v in m.𝓕 ×ˢ m.𝓕, A v ∂(m.μ.prod m.μ) := by
  intro D ρ p m T h1 h2 A hA
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D ρ p
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : Countable (ratMx D ρ p) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, hF, hone⟩ := m.hμ
  haveI : Countable ((ratMx D ρ p).prod (ratMx D ρ p)) :=
    (Function.Injective.countable (f := fun g : (ratMx D ρ p).prod (ratMx D ρ p) =>
      ((⟨g.1.1, g.2.1⟩ : ratMx D ρ p), (⟨g.1.2, g.2.2⟩ : ratMx D ρ p))) fun a b h =>
        Subtype.ext (Prod.ext (congrArg (fun z => z.1.1) h) (congrArg (fun z => z.2.1) h)))
  have hv : m.μ.prod m.μ (m.𝓕 ×ˢ m.𝓕) = 1 := by rw [Measure.prod_prod, hone, one_mul]
  have mem : ∀ z : Mx D ρ p × Mx D ρ p, z ∈ (ratMx D ρ p).prod (ratMx D ρ p) ↔
      ∃ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, z = (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) := by
    rintro ⟨a, b⟩
    constructor
    · rintro ⟨⟨ξ₁, h₁⟩, ⟨ξ₂, h₂⟩⟩
      exact ⟨ξ₁, ξ₂, Prod.ext h₁.symm h₂.symm⟩
    · rintro ⟨ξ₁, ξ₂, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨⟨ξ₁, rfl⟩, ⟨ξ₂, rfl⟩⟩
  have hr : ∀ x, T x ∈ (ratMx D ρ p).prod (ratMx D ρ p) ↔ x ∈ (ratMx D ρ p).prod (ratMx D ρ p) := by
    intro x
    constructor
    · intro h
      obtain ⟨ξ₁, ξ₂, e⟩ := (mem _).1 h
      obtain ⟨ξ₁', ξ₂', e'⟩ := h2 ξ₁ ξ₂
      refine (mem _).2 ⟨ξ₁', ξ₂', ?_⟩
      rw [← e', ← e, T.symm_apply_apply]
    · intro h
      obtain ⟨ξ₁, ξ₂, e⟩ := (mem _).1 h
      obtain ⟨ξ₁', ξ₂', e'⟩ := h1 ξ₁ ξ₂
      exact (mem _).2 ⟨ξ₁', ξ₂', by rw [e, e']⟩
  refine setIntegral_comp_eq _ (m.μ.prod m.μ) (isAddFundamentalDomain_prod _ hF)
    (by rw [hv]; exact one_ne_zero) (by rw [hv]; exact ENNReal.one_ne_top) T hr A ?_
  intro γ hγ v
  obtain ⟨ξ₁, ξ₂, e⟩ := (mem _).1 hγ
  rw [e, add_comm]
  exact hA ξ₁ ξ₂ v

end GlobalTheory.CompanionTheory.FJE.TransportInt
