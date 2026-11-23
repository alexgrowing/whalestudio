import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightStabilizerMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasMOfCont

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.ME

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem measurePreserving_prod_rearrange {L M P N : Type*} [MeasurableSpace L] [MeasurableSpace M] [MeasurableSpace P] [MeasurableSpace N]
    (μL : Measure L) (μM : Measure M) (μP : Measure P) (μN : Measure N) [SigmaFinite μL] [SigmaFinite μM]
    [SigmaFinite μP] [SigmaFinite μN] :
    MeasurePreserving (fun p : L × (M × (P × N)) => (p.2.1, ((p.1, p.2.2.1), p.2.2.2)))
      (μL.prod (μM.prod (μP.prod μN))) (μM.prod ((μL.prod μP).prod μN)) := by
  have h1 := (measurePreserving_prodAssoc μL μM (μP.prod μN)).symm
  have h2 := (Measure.measurePreserving_swap (μ := μL) (ν := μM)).prod (MeasurePreserving.id (μP.prod μN))
  have h3 := measurePreserving_prodAssoc μM μL (μP.prod μN)
  have h4 := (MeasurePreserving.id μM).prod (measurePreserving_prodAssoc μL μP μN).symm
  have := h4.comp (h3.comp (h2.comp h1))
  convert this using 1
  funext ⟨l, m, p, n⟩
  rfl

theorem muSS_eq (S : B.RealPlaceData k r Wp Wq) (w : Equiv.Perm (Fin (r + 1)))
    (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ)) (he : MeasurePreserving e volume volume)
    (μ0 μ0' : Measure (Mt k r)) (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
    (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0') (c1 c2 : NNReal)
    (hN1 : S.μN = c1 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0).map
      (fun p => Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
    (hN2 : S.μN = c2 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0').map
      (fun p => Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2))) :
    S.μSS = (c1 * c2) • ((volume : Measure (C2.Lstidx w → ℂ)).prod (OD.nuR S w μ0 μ0')).map
      (fun p => OD.Xi S w e p.1 p.2) := by
  have sf : ∀ {V : Set (B.Mat k r)} {μ : Measure (Mt k r)}, B.IsHaarOn V μ → SigmaFinite μ := by
    intro V μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    infer_instance
  haveI := sf S.haarW
  haveI := sf S.haarW'
  haveI := sf hμ0
  haveI := sf hμ0'
  have m1 : Measurable (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
      Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)) := (HC.cont_Phi S.z).measurable
  have m2 : Measurable (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
      Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)) := (HC.cont_Phi S.z').measurable

  have hA : MeasurePreserving
      (fun p : (C2.Lstidx w → ℂ) × OD.RR k r w => ((p.2.1.1, (e (p.1, p.2.1.2.1), p.2.1.2.2)), p.2.2))
      ((volume : Measure (C2.Lstidx w → ℂ)).prod (OD.nuR S w μ0 μ0'))
      ((S.μW.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0)).prod
        (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'))) := by
    have h1 := (measurePreserving_prodAssoc (volume : Measure (C2.Lstidx w → ℂ))
      (S.μW.prod ((volume : Measure (C2.LPidx w → ℂ)).prod μ0))
      (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'))).symm
    have h2 := (measurePreserving_prod_rearrange (volume : Measure (C2.Lstidx w → ℂ)) S.μW (volume : Measure (C2.LPidx w → ℂ)) μ0).prod
      (MeasurePreserving.id (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0')))
    have h3 := ((MeasurePreserving.id S.μW).prod (he.prod (MeasurePreserving.id μ0))).prod
      (MeasurePreserving.id (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0')))
    have := h3.comp (h2.comp h1)
    simp only [OD.nuR]
    convert this using 1
    all_goals first | rfl | (funext p; rfl)
  have hB : Measurable (Prod.map
      (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
      (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)))) :=
    (measurable_id.prodMap m1).prodMap (measurable_id.prodMap m2)
  have hXi : (fun p : (C2.Lstidx w → ℂ) × OD.RR k r w => OD.Xi S w e p.1 p.2) =
      (Prod.map
        (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
          Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
        (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
          Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)))) ∘
      (fun p : (C2.Lstidx w → ℂ) × OD.RR k r w => ((p.2.1.1, (e (p.1, p.2.1.2.1), p.2.1.2.2)), p.2.2)) := by
    funext p; rfl
  rw [hXi, ← Measure.map_map hB hA.measurable, hA.map_eq,
    ← Measure.map_prod_map _ _ (measurable_id.prodMap m1) (measurable_id.prodMap m2),
    ← Measure.map_prod_map _ _ measurable_id m1, ← Measure.map_prod_map _ _ measurable_id m2,
    Measure.map_id, Measure.map_id]
  show (S.μW.prod S.μN).prod (S.μW'.prod S.μN) = _
  have e2 : S.μW'.prod S.μN = S.μW'.prod (c2 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0').map
      (fun p => Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2))) := by rw [← hN2]
  rw [e2, hN1]
  rw [ENNReal.smul_def c1, ENNReal.smul_def c2, ENNReal.smul_def (c1 * c2), Measure.prod_smul_right,
    Measure.prod_smul_right, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ENNReal.coe_mul]

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.ME
