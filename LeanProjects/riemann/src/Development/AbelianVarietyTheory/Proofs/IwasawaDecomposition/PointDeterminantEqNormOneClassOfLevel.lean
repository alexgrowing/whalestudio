import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

theorem adAt_eq_one_of_prV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) {z : AfE F E}
    (hz : Formalism.UG.prV (E := E) (P.under (𝓞 F)) z = 1) : adAt F P z = 1 := by
  set v := P.under (𝓞 F)
  have h1 : Formalism.UG.P.afsplitEps E v * z = Formalism.UG.P.afsplitEps E v := by
    rw [← Formalism.UG.P.afsplit_decomp, hz]
    rfl
  have h2 : Formalism.UG.P.afsplitEps E v = (1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (1 : v.adicCompletion F) := by
    rw [Formalism.UG.P.afsplitEps, Algebra.TensorProduct.one_def, Formalism.UG.P.afsplitIE_tmul]
  have h3 : adAt F P (Formalism.UG.P.afsplitEps E v) = 1 := by
    rw [h2, adAt_apply, GlobalTheory.Mem.ReadTwist.afIso_one_tmul (k := 1)]
    · simp
    · rw [Formalism.UG.P.afsplitI_self]; simp
  have h4 := congrArg (adAt F P) h1
  rwa [map_mul, h3, one_mul] at h4

theorem detPt_eq_u1Dt_of_level : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q) (y k : GL (Fin n) (AfE H.F H.E)) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), LevOk H SG SQ → IsPtOf (host_cmData R H) (y * k) (extTo SQ p) → k ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → Formalism.L2.Herm.Carries k (stdLat H.E n) (stdLat H.E n) → (∀ P ∈ uSG SG SQ, Formalism.UG.bc (Formalism.UG.prV (E := H.E) (P.under (𝓞 H.F))) k = 1) → Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det y → detPt H SQ p = u1Dt H SQ x := by
  intro R H n ST SG Q SQ p y k x hl hp hk hc hbc hx
  obtain ⟨a, ha⟩ := exists_lift H x
  obtain ⟨b, hb⟩ := DetLift.exists_isDetLift R H n k hk
  have hab : IsDetLift (host_cmData R H) (y * k) (a * b) := by
    unfold IsDetLift at ha hb ⊢
    rw [map_mul, map_mul, ha, hb, hx, map_mul]
  have hK : b ∈ KDq H SQ := by
    refine mem_KDq_of_conj hl b (fun w => ?_) fun P hP => ?_
    · rw [DetSpec.val_compAt_eq hb ⟨stdLat_lattice, stdLat_unimodular⟩ hc (fr := fun _ => LinearEquiv.refl _ _)
        (fun _ _ => Iff.rfl) w]
      simp
    · have hdet : adAt H.F P (k : Matrix (Fin n) (Fin n) (AfE H.F H.E)).det = 1 := by
        refine adAt_eq_one_of_prV P ?_
        have h := congrArg (fun g => Matrix.det (Units.val g)) (hbc P hP)
        simp only [Formalism.UG.bc, Units.coe_map, Units.val_one, Matrix.det_one] at h
        rw [RingHom.map_det]
        exact h
      have hs0 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E b : AfE H.F H.E)) ≠ 0 :=
        (((Units.isUnit (finAf H.F H.E b)).map (Formalism.UG.sigR (host_cmData R H).sig _)).map (adAt H.F P)).ne_zero
      rw [DetSpec.compAt_eq hb P, hdet, one_mul, div_self hs0, sub_self, map_zero]
      exact zero_lt_one
  rw [normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha, ← DetSpec.mk_eq_detPt R H n ST SG Q SQ p (y * k) (a * b) hl hp hab,
    QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b).2 hK, mul_one]

end GlobalTheory.Mem.Col2.FullDt
