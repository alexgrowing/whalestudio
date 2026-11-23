import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbPol
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushSupp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem gramR_Y0_eq_TI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) :
    gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (Y0 X u') = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
  rw [show Y0 X u' = orbM X u' 1 from (one_smul _ _).symm, orbM, gramR_smul, gramR_ratTup]
  rfl

theorem indI_of_gram {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) (Y : TupI X)
    (hY : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _)) :
    Y ∈ IndI X := by
  have e1 := orbM_mem X u' hT hd 1
  have e0 : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y =
      gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (orbM X u' 1) := by rw [hY, e1.1]
  apply linIndep_of_isUnit_det (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  rw [e0, e1.1]
  have e2 := RingHom.map_det (inclR (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F))
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))
  rw [RingHom.mapMatrix_apply] at e2
  show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))).det
  rw [← e2]
  exact (isUnit_iff_ne_zero.2 hd).map _

theorem fib_near (hR : RmulFacts) (hF : FibAllT) (hC : MassDataMassesW.HinfCompact) {D : D7} (X : HidaSetting D)
    (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf
    (hP : PushHyp X u' ψ hT μinf νinf fibInf) (T : HmI X) (a : MfI X) (hunit : IsUnit a)
    (hgT : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X a (Y0 X u')) = (T : Matrix _ _ _))
    (hind : ∀ Y : TupI X, gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = (T : Matrix _ _ _) → Y ∈ IndI X) :
    ∃ c : ENNReal, fibInf T = c • X.measG.μGinf.map (fun g => g • rmulT X a (Y0 X u')) := by
  obtain ⟨hmr, hcomp, hsmul, hgram, hcTmul, hcT1, hKm, hrc⟩ := hR X
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hfib := hP.2.2.2.2.2.2
  obtain ⟨hinvT, hlfT⟩ := hF X u' ψ hT μinf νinf fibInf hP T
  set b : MfI X := ↑hunit.unit⁻¹ with hb
  have hab : a * b = 1 := hunit.mul_val_inv
  have hba : b * a = 1 := hunit.val_inv_mul
  have hab' : ∀ Y, rmulT X a (rmulT X b Y) = Y := fun Y => by rw [hcomp, hba, rmulT_one]
  have hba' : ∀ Y, rmulT X b (rmulT X a Y) = Y := fun Y => by rw [hcomp, hab, rmulT_one]
  set ν := (fibInf T).map (rmulT X b) with hν
  have i1 : InvI X ν := by
    intro g
    rw [hν, Measure.map_map (measurable_smul_tupI X g) (hmr b)]
    have : ((fun y => g • y) ∘ rmulT X b) = rmulT X b ∘ (fun y => g • y) := funext fun y => hsmul g b y
    rw [this, ← Measure.map_map (hmr b) (measurable_smul_tupI X g), hinvT g]
  have hS : fibInf T (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1} ∩ IndI X)ᶜ = 0 :=
    hfib.1 T
  have s1 : ν (FbI X u' hT)ᶜ = 0 := by
    rw [hν, Measure.map_apply (hmr b) (measurableSet_FbI X u' hT).compl]
    refine measure_mono_null ?_ hS
    intro y hy hy2
    apply hy
    have hg : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X b y) = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
      rw [hgram, hy2.1, ← hgT, hgram, gramR_Y0_eq_TI X u' hT, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hcTmul,
        Matrix.mul_assoc, hab, hcT1, Matrix.one_mul, Matrix.mul_one]
    exact ⟨hg, indI_of_gram X u' hT hd _ hg⟩
  have l1 : LFI X ν := by
    intro K hK hKI
    rw [hν, Measure.map_apply (hmr b) (hKm K hK)]
    have hpre : rmulT X b ⁻¹' K = rmulT X a '' K := by
      ext y
      constructor
      · intro hy; exact ⟨rmulT X b y, hy, hab' y⟩
      · rintro ⟨k, hk, rfl⟩; show rmulT X b (rmulT X a k) ∈ K; rw [hba']; exact hk
    rw [hpre]
    have hcl : IsClosed (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) := by
      haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
      exact isClosed_singleton.preimage (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    have hK2 : IsCompact (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) :=
      (hK.image (hrc a)).inter_right hcl
    calc fibInf T (rmulT X a '' K)
        ≤ fibInf T (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) +
          fibInf T (rmulT X a '' K \ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) :=
          measure_le_inter_add_sdiff _ _ _
      _ = fibInf T (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) := by
          have h0 : fibInf T (rmulT X a '' K \ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) = 0 := by
            refine measure_mono_null ?_ hS
            intro y hy hy2
            exact hy.2 hy2.1
          rw [h0, add_zero]
      _ < ⊤ := hlfT _ hK2 (fun y hy => hind y hy.2)
  obtain ⟨c, -, hc⟩ := orbRep_of_witt wittInf_holds hC X u' ψ hT μinf νinf fibInf hP ν i1 s1 l1
  refine ⟨c, ?_⟩
  have e1 : fibInf T = ν.map (rmulT X a) := by
    rw [hν, Measure.map_map (hmr a) (hmr b)]
    have : rmulT X a ∘ rmulT X b = id := funext hab'
    rw [this, Measure.map_id]
  have e2 : (fun g => g • rmulT X a (Y0 X u')) = rmulT X a ∘ orbM X u' :=
    funext fun g => hsmul g a (Y0 X u')
  rw [e1, hc, Measure.map_smul, e2, Measure.map_map (hmr a) (measurable_orbM X u')]

end PI.AprimeInfW
