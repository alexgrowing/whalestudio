import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.IsEulerProdConstIff
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentTarget

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Scale
open scoped TensorProduct ENNReal NNReal Matrix

theorem scaleC : ScaleC := by
  intro F E _ _ _ _ _ σ hcm M J hJ n T hT _ g T' hT' hrel hSW d b laminf lam hinf hv μ 𝓕 hH hF minf m
    hminf hm
  have hinv := (HaarCoord.conj_facts hcm).1
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin n) (Fin n) E, G = (g : Matrix (Fin n) (Fin n) E) := ⟨_, rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H : Matrix (Fin n) (Fin n) E, H = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) :=
    ⟨_, rfl⟩
  have hGH : G * H = 1 := by rw [hG, hHd]; exact Units.mul_inv g
  have hHG : H * G = 1 := by rw [hG, hHd]; exact Units.inv_mul g
  rw [← hG] at hrel
  have hdetH : H.det ≠ 0 := by
    intro h0
    have : H.det * G.det = 1 := by rw [← Matrix.det_mul, hHG, Matrix.det_one]
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hrel' : cT (σ : E →+* E) H * T' * H = T := by
    rw [hrel]
    calc cT (σ : E →+* E) H * (cT (σ : E →+* E) G * T * G) * H
        = (cT (σ : E →+* E) H * cT (σ : E →+* E) G) * T * (G * H) := by
          simp only [Matrix.mul_assoc]
      _ = T := by rw [← cT_mul, hGH, cT_one, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨ai, a, hau, hai, hav⟩ := GlobalTheory.T.right_multiplication_euler_product F E σ hcm n M H hdetH
  obtain ⟨ci, c, hcu, hci, hcv⟩ := GlobalTheory.T.hermitian_matrix_euler_product F E σ hcm n H hdetH
  obtain ⟨-, -, -, -, hq, -⟩ := GlobalTheory.T.unit_product_closure_properties F ai ci a c hau hcu
  obtain ⟨hci0, hc0, -⟩ := GlobalTheory.T.unit_product_closure_properties F ci ai c a hcu hau
  have hrI : IsLocR (Ainf F) := isLocR_Ainf F hcm.1
  have hrV : ∀ v, IsLocR (Fv F v) := fun v => LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have sInf := unitary_conjugate_local σ hcm hinv J hJ (Ainf F) hrI b laminf hinf.1 minf hminf H T T' hdetH hT hT'
    hrel' ai ci hci0 hai hci
  have sV := fun v => unitary_conjugate_local σ hcm hinv J hJ (Fv F v) (hrV v) b (lam v) (hv v).1 (m v) (hm v) H T T'
    hdetH hT hT' hrel' (a v) (c v) (hc0 v) (hav v) (hcv v)
  obtain ⟨⟨t1, t2, t3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have me := measurable_rmul σ hcm (AF F) n M (H.map (inclR (F := F) (AF F)))
  have mi : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E =>
      rmul (Ainf F) X (H.map (inclR (F := F) (Ainf F))) := by
    obtain ⟨r1, r2, r3, r4, -⟩ := hrI
    exact measurable_rmul σ hcm (Ainf F) n M _
  have mv : ∀ v, Measurable fun X : Fin n → Fin M → Fv F v ⊗[F] E =>
      rmul (Fv F v) X (H.map (inclR (F := F) (Fv F v))) := by
    intro v
    obtain ⟨r1, r2, r3, r4, -⟩ := hrV v
    exact measurable_rmul σ hcm (Fv F v) n M _
  obtain ⟨κ, hE, hκ⟩ := hSW d b laminf lam hinf hv μ 𝓕 hH hF minf m hminf hm
  refine ⟨κ, ?_, hκ⟩
  have hth := theta_map σ hcm J hJ μ 𝓕 hH hF G H T T' hGH hHG hrel' hrel.symm me
  have hlat := (GlobalTheory.T.adelic_tuple_projections F E σ hcm d b n M).2.2.2
  have hfin : ∀ v, (cfac E v • m v (hermOf (Fv F v) σ T hT)) (latV b v) < ⊤ := by
    intro v
    obtain ⟨r1, r2, r3, r4, -⟩ := id (hrV v)
    obtain ⟨-, hW, hHm⟩ := coord_measures_haar F E σ hcm (Fv F v) d b (lam v) (hv v).1
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm M J hJ (Fv F v) (hrV v) n _ _ (m v) (hW n M) (hHm n) (hm v)
      (hermOf (Fv F v) σ T hT)).1
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hlat.1 v).1.measure_lt_top
  rw [isEulerProd_const_iff, ← hth]
  exact GlobalTheory.T.euler_product_measure_transport F E σ hcm d b n M _ (κ • minf (hermOf (Ainf F) σ T' hT')) (κ • minf (hermOf (Ainf F) σ T hT))
    (fun v => cfac E v • m v (hermOf (Fv F v) σ T' hT')) (fun v => cfac E v • m v (hermOf (Fv F v) σ T hT))
    (fun X => rmul (AF F) X (H.map (inclR (F := F) (AF F))))
    (fun X => rmul (Ainf F) X (H.map (inclR (F := F) (Ainf F))))
    (fun v X => rmul (Fv F v) X (H.map (inclR (F := F) (Fv F v)))) me mi mv
    (fun X => ⟨projInf_rmul X H, fun v => projV_rmul v X H⟩)
    ((LatRat.latV_rational F E σ hcm d b n M).1 H hdetH)
    (ai / ci) (fun v => a v / c v) hq (by rw [Measure.map_smul, sInf, smul_comm])
    (fun v => by rw [Measure.map_smul, sV v, smul_comm]) hfin
    ((isEulerProd_const_iff b _ κ _ _).1 hE)

end PositivityTheory.SiegelWeilFormula.Densx

end
