import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp.PtTest

theorem hasCompactSupport_of_loc {X : Type} [TopologicalSpace X] (g : X → ℂ) (hg : IsLocallyConstant g)
    (C : Set X) (hC : IsCompact C) (hz : ∀ x ∉ C, g x = 0) : HasCompactSupport g := by
  have hcl : IsClosed (Function.support g) := by
    have := (hg.isOpen_fiber 0).isClosed_compl
    convert this using 1
    ext; simp [Function.mem_support]
  show IsCompact (closure (Function.support g))
  rw [hcl.closure_eq]
  exact hC.of_isClosed_subset hcl fun x hx => by
    by_contra h
    exact hx (hz x h)

theorem slice_eventually {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Φ : X × Y → ℂ) (hΦ : IsTest Φ)
    (a : X) : ∀ᶠ a' in 𝓝 a, (fun b => Φ (a', b)) = fun b => Φ (a, b) := by
  have hC : IsCompact (Prod.snd '' tsupport Φ) := hΦ.2.isCompact.image continuous_snd
  have h := hC.eventually_forall_of_forall_eventually (x₀ := a) (P := fun a' b => Φ (a', b) = Φ (a, b))
    fun y _ => by
      have h1 : ∀ᶠ z in 𝓝 (a, y), Φ z = Φ (a, y) := (IsLocallyConstant.iff_eventually_eq Φ).1 hΦ.1 (a, y)
      have hc : Continuous fun z : X × Y => (a, z.2) := continuous_const.prodMk continuous_snd
      have h2 : ∀ᶠ z in 𝓝 (a, y), Φ (a, z.2) = Φ (a, y) :=
        (hc.tendsto (a, y)).eventually ((IsLocallyConstant.iff_eventually_eq Φ).1 hΦ.1 (a, y))
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hz2]
  filter_upwards [h] with a' ha'
  funext b
  by_cases hb : b ∈ Prod.snd '' tsupport Φ
  · exact ha' b hb
  · have h0 : ∀ c, Φ (c, b) = 0 := fun c => by
      by_contra hne
      exact hb ⟨(c, b), subset_tsupport _ hne, rfl⟩
    rw [h0, h0]

theorem slice_isTest {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Φ : X × Y → ℂ) (hΦ : IsTest Φ)
    (a : X) : IsTest fun b => Φ (a, b) := by
  have hl : IsLocallyConstant fun b => Φ (a, b) :=
    hΦ.1.comp_continuous (continuous_const.prodMk continuous_id)
  refine ⟨hl, hasCompactSupport_of_loc _ hl _ (hΦ.2.isCompact.image continuous_snd) fun b hb => ?_⟩
  by_contra hne
  exact hb ⟨(a, b), subset_tsupport _ hne, rfl⟩

end GlobalTheory.JR.Hyp.PtTest

open GlobalTheory.JR.Hyp.PtTest in

theorem GlobalTheory.JR.Hyp.pt_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ) := by
  intro F E _ _ _ _ _ A ψ hψ x ν hν Φ hΦ

  let β : LinearMap.BilinForm F A.K := LinearMap.comp (Algebra.traceForm F A.K) (LinearMap.mulLeft F (x : A.K))
  have hβapp : ∀ u b, β u b = Algebra.trace F A.K ((x : A.K) * u * b) := fun u b => by simp [β, Algebra.traceForm_apply, mul_assoc]
  have hsymm : β.IsSymm := by
    refine ⟨fun u b => ?_⟩
    simp only [RingHom.id_apply, hβapp]
    ring_nf
  have htr := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  have hsepL : ∀ u : A.K, (∀ b, β u b = 0) → u = 0 := fun u hu => by
    have h1 : (x : A.K) * u = 0 := htr.1 _ fun b => by simpa [hβapp] using hu b
    simpa using congrArg (fun t => ((x⁻¹ : A.Kˣ) : A.K) * t) h1
  have hnd : β.Nondegenerate := ⟨hsepL, fun b hb => hsepL b fun u => by
    have := hb u
    rw [hβapp] at this
    rw [hβapp, mul_right_comm]; exact this⟩
  have hF : ∀ f : A.K → ℂ, IsTest f → IsTest (fourB ν (kx A ψ (x : A.K)) f) := fun f hf =>
    (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K β hsymm hnd).2 ν hν f hf
  have hG : ∀ p, Hyp.pt A ν ψ x Φ p = fourB ν (kx A ψ (x : A.K)) (fun b => Φ (p.1, b)) p.2 := fun p => rfl
  have hloc : IsLocallyConstant (Hyp.pt A ν ψ x Φ) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨a, u⟩
    have h1 := slice_eventually Φ hΦ a
    have h2 := (IsLocallyConstant.iff_eventually_eq _).1 (hF _ (slice_isTest Φ hΦ a)).1 u
    rw [nhds_prod_eq]
    filter_upwards [h1.prod_mk h2] with q hq
    rw [hG, hG, hq.1]
    exact hq.2
  refine ⟨hloc, ?_⟩
  have hC1 : IsCompact (Prod.fst '' tsupport Φ) := hΦ.2.isCompact.image continuous_fst
  obtain ⟨t, -, ht⟩ := hC1.elim_nhds_subcover (fun a => {a' | (fun b => Φ (a', b)) = fun b => Φ (a, b)})
    fun a _ => slice_eventually Φ hΦ a
  refine hasCompactSupport_of_loc _ hloc
    ((Prod.fst '' tsupport Φ) ×ˢ ⋃ i ∈ t, tsupport (fourB ν (kx A ψ (x : A.K)) fun b => Φ (i, b)))
    (hC1.prod (t.isCompact_biUnion fun i _ => (hF _ (slice_isTest Φ hΦ i)).2.isCompact)) ?_
  rintro ⟨a, u⟩ hq
  by_contra hne
  apply hq
  have ha : a ∈ Prod.fst '' tsupport Φ := by
    by_contra ha
    apply hne
    have h0 : ∀ b, Φ (a, b) = 0 := fun b => by
      by_contra hb
      exact ha ⟨(a, b), subset_tsupport _ hb, rfl⟩
    simp [hG, fourB, h0]
  refine ⟨ha, ?_⟩
  obtain ⟨i, hi, hai⟩ := Set.mem_iUnion₂.1 (ht ha)
  refine Set.mem_iUnion₂.2 ⟨i, hi, subset_tsupport _ ?_⟩
  rw [hG] at hne
  simp only [Set.mem_setOf_eq] at hai
  rw [Function.mem_support]
  rwa [hai] at hne
