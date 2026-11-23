import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.CoordMeas

theorem map_comp_comap {H Y Z : Type} [MeasurableSpace H] [MeasurableSpace Y] [MeasurableSpace Z]
    (e : H ≃ᵐ Y) (ν : Measure Y) {c : Y → Z} (hc : Measurable c) :
    (Measure.comap e ν).map (c ∘ e) = ν.map c := by
  rw [← MeasurableEquiv.map_symm, ← Measure.map_map hc e.measurable,
    Measure.map_map e.measurable e.symm.measurable]
  have : (⇑e ∘ ⇑e.symm) = id := funext e.apply_symm_apply
  rw [this, Measure.map_id]

theorem map_prod_box {R K P : Type} [MeasurableSpace R] [MeasurableSpace K] [Fintype P] {n d : ℕ}
    (lam : Measure R) [SigmaFinite lam] (κ : Measure K) [SigmaFinite κ] (r : K → Fin d → R)
    (hr : Measurable r) (hκ : κ.map r = Measure.pi fun _ => lam) :
    ((Measure.pi fun _ : Fin n => lam).prod (Measure.pi fun _ : P => κ)).map
        (fun x : (Fin n → R) × (P → K) =>
          (Sum.elim x.1 (fun q : Fin d × P => r (x.2 q.2) q.1) : Fin n ⊕ (Fin d × P) → R)) =
      Measure.pi fun _ : Fin n ⊕ (Fin d × P) => lam := by
  have hc : Measurable (fun x : (Fin n → R) × (P → K) =>
      (Sum.elim x.1 (fun q : Fin d × P => r (x.2 q.2) q.1) : Fin n ⊕ (Fin d × P) → R)) := by
    refine measurable_pi_iff.2 fun i => ?_
    rcases i with i | q
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply q.1).comp
        (hr.comp ((measurable_pi_apply q.2).comp measurable_snd))
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hc (MeasurableSet.univ_pi hs)]
  have hset : (fun x : (Fin n → R) × (P → K) =>
      (Sum.elim x.1 (fun q : Fin d × P => r (x.2 q.2) q.1) : Fin n ⊕ (Fin d × P) → R)) ⁻¹'
        Set.pi Set.univ s =
      (Set.pi Set.univ fun i : Fin n => s (Sum.inl i)) ×ˢ
        (Set.pi Set.univ fun p : P => r ⁻¹' Set.pi Set.univ fun k : Fin d => s (Sum.inr (k, p))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod,
      Sum.forall, Sum.elim_inl, Sum.elim_inr, Prod.forall]
    exact and_congr Iff.rfl ⟨fun h p k => h k p, fun h k p => h p k⟩
  have hκs : ∀ p : P, κ (r ⁻¹' Set.pi Set.univ fun k : Fin d => s (Sum.inr (k, p))) =
      ∏ k : Fin d, lam (s (Sum.inr (k, p))) := fun p => by
    rw [← Measure.map_apply hr (MeasurableSet.univ_pi fun k => hs _), hκ, Measure.pi_pi]
  rw [hset, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fintype.prod_sum_type,
    Fintype.prod_prod_type]
  simp only [hκs]
  rw [Finset.prod_comm]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.CoordMeas

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.CoordMeas

theorem coordHerm_map_hCo : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ n : ℕ, (GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n).map (hCo R σ b) = Measure.pi fun _ : Idx n d => lam := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ d b lam hlam n
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hcm
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hcm R d b lam hlam
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.SW.coordK R b lam) := inferInstance

  let r : R ⊗[F] E → Fin d → R := fun y k => (Algebra.TensorProduct.basis R b).repr y k
  let Tr : (R ⊗[F] E) ≃ₜ (Fin d → R) := (t7 d b).homeomorph r
  have hr : Measurable r := Tr.toMeasurableEquiv.measurable
  have hκ : (GlobalTheory.CompanionTheory.SW.coordK R b lam).map r = Measure.pi fun _ => lam := by
    have := map_comp_comap Tr.toMeasurableEquiv (Measure.pi fun _ => lam) (c := id) measurable_id
    rw [Measure.map_id] at this
    exact this

  let T := (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6).homeomorph
    (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord R σ n)
  have hbox := map_prod_box (n := n) (P := {p : Fin n × Fin n // p.1 < p.2}) lam
    (GlobalTheory.CompanionTheory.SW.coordK R b lam) r hr hκ
  have hc : Measurable (fun x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) =>
      (Sum.elim x.1 (fun q : Fin d × {p : Fin n × Fin n // p.1 < p.2} => r (x.2 q.2) q.1) : Idx n d → R)) := by
    refine measurable_pi_iff.2 fun i => ?_
    rcases i with i | q
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply q.1).comp
        (hr.comp ((measurable_pi_apply q.2).comp measurable_snd))
  have hm := map_comp_comap T.toMeasurableEquiv
    ((Measure.pi fun _ : Fin n => lam).prod
      (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => GlobalTheory.CompanionTheory.SW.coordK R b lam)) hc
  rw [hbox] at hm
  have hfun : hCo R σ b = (fun x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) =>
      (Sum.elim x.1 (fun q : Fin d × {p : Fin n × Fin n // p.1 < p.2} => r (x.2 q.2) q.1) : Idx n d → R)) ∘
      T.toMeasurableEquiv := by
    funext S i
    rcases i with i | q <;> rfl
  rw [hfun]
  exact hm

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
