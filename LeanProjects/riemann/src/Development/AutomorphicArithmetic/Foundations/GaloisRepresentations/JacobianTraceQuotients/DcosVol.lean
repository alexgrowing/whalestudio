import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem mem_dcos_iff {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {t : Fin n → kˣ} (ht : Dom t)
    (g : GL (Fin n) k) :
    g ∈ dcos K t ↔ ∃ u ∈ unipB k (Fin n), u ∈ K ∧ ∃ i ∈ K, g = u * diagT k (Fin n) t * i := by
  refine ⟨?_, fun ⟨u, _, hu, i, hi, e⟩ => ⟨u, hu, i, hi, e⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := hK.fact a ha
  refine ⟨u, hu.2, hu.1, _, mul_mem (mul_mem hd (hK.low t ht c hc)) hb, ?_⟩
  have e : diagT k (Fin n) t * diagT k (Fin n) d = diagT k (Fin n) d * diagT k (Fin n) t := by
    rw [← map_mul, mul_comm, map_mul]
  calc u * diagT k (Fin n) d * c * diagT k (Fin n) t * b
      = u * (diagT k (Fin n) d * diagT k (Fin n) t) * ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) * b := by
        group
    _ = _ := by rw [← e]; group

private theorem dcos_eq_image (K : Subgroup (GL (Fin n) k)) (t : Fin n → kˣ) :
    dcos K t = (fun x : GL (Fin n) k × GL (Fin n) k => x.1 * diagT k (Fin n) t * x.2) ''
      ((K : Set (GL (Fin n) k)) ×ˢ (K : Set (GL (Fin n) k))) := by
  ext g
  exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨(a, b), ⟨ha, hb⟩, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x.1, hx.1, x.2, hx.2, e.symm⟩⟩

private theorem isCompact_dcos {K : Subgroup (GL (Fin n) k)} (hK : CO K) (t : Fin n → kˣ) :
    IsCompact (dcos K t) := by
  rw [dcos_eq_image]
  exact (hK.1.prod hK.1).image (by fun_prop)

private theorem isOpen_dcos {K : Subgroup (GL (Fin n) k)} (hK : CO K) (t : Fin n → kˣ) :
    IsOpen (dcos K t) := by
  have e : dcos K t = ⋃ a ∈ (K : Set (GL (Fin n) k)),
      (fun g => (a * diagT k (Fin n) t) * g) '' (K : Set (GL (Fin n) k)) := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, e.symm⟩, fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, e.symm⟩⟩
  rw [e]
  exact isOpen_biUnion fun a _ => (Homeomorph.mulLeft (a * diagT k (Fin n) t)).isOpenMap _ hK.2

open GlobalTheory.SplitWeil GlobalTheory.IwahoriTraceProof in
private theorem isClosed_unipB : IsClosed (unipB k (Fin n) : Set (GL (Fin n) k)) := by
  have e : (unipB k (Fin n) : Set (GL (Fin n) k)) = (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin n) k | g.val i j = 0}) ∩
      ⋂ i, {g : GL (Fin n) k | g.val i i = 1} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    exact mem_unipB k
  rw [e]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun i => isClosed_eq (Units.continuous_val.matrix_elem i i) continuous_const)

open GlobalTheory.SplitWeil GlobalTheory.IwahoriTraceProof in

private theorem measure_dcos [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {t : Fin n → kˣ} (ht : Dom t) :
    μ.real (dcos K t) = μ.real (K : Set (GL (Fin n) k)) * (deltaB t)⁻¹ := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  letI : MeasurableSpace (unipRad k (points (Fin n))) := _root_.borel _
  haveI : BorelSpace (unipRad k (points (Fin n))) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unipRad k (points (Fin n))) :=
    (UnipHaar.unipHomeo (points (Fin n))).isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (unipRad k (points (Fin n))) :=
    (UnipHaar.unipHomeo (points (Fin n))).secondCountableTopology
  let ν : Measure (unipRad k (points (Fin n))) := Measure.haar
  have ho : IsOpen {s : unipRad k (points (Fin n)) | (s : GL (Fin n) k) ∈ K} :=
    hK.co.2.preimage continuous_subtype_val
  have hcl : IsClosed (unipRad k (points (Fin n)) : Set (GL (Fin n) k)) := isClosed_unipB
  have hc : IsCompact {s : unipRad k (points (Fin n)) | (s : GL (Fin n) k) ∈ K} :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK.co.1
  have h1 := measure_mul_eq μ ν hK.co.2 (t := diagT k (Fin n) t)
    (fun u hu => by simpa [unipB] using conj_mem_unipB t⁻¹ hu)
    (fun u hu hI => hK.up t ht u ⟨hI, hu⟩)
    (isCompact_dcos hK.co t).measurableSet (mem_dcos_iff hK ht)
  have h2 := UnipHaar.haar_conj_eq_modulus_mul k (Fin n) (Fin n) (fun _ => Unit) (points (Fin n)) ν
    (leviTorus k (Fin n) t) _ ho.measurableSet
  rw [← deltaB_eq_modulus] at h2
  have h3 := (congrArg (· * μ (dcos K t)) h2).symm.trans h1
  rw [mul_right_comm, ENNReal.mul_left_inj (ho.measure_pos ν ⟨1, one_mem K⟩).ne' hc.measure_lt_top.ne] at h3
  rw [measureReal_def, measureReal_def, ← h3, ENNReal.toReal_mul, ENNReal.toReal_ofReal (deltaB_pos t).le,
    mul_right_comm, mul_inv_cancel₀ (deltaB_pos t).ne', one_mul]

end

end UpperTheory.Gal.Join

theorem UpperTheory.Gal.Join.dcosVol :
    UpperTheory.Gal.Join.DcosVol := by
  intro k _ _ _ _ n _ _ μ _ K hK t ht
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc := isCompact_dcos hK.co t
  refine ⟨⟨(LocallyConstant.indicator (1 : LocallyConstant (GL (Fin n) k) ℂ) ⟨hc.isClosed, isOpen_dcos hK.co t⟩).2,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩, measure_dcos μ hK ht⟩
