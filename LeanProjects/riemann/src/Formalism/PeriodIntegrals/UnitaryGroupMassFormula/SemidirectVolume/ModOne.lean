import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.StabilizerFixesFrameVector

noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_hermitian_form_left [IsTopologicalRing (R ⊗[F] E)] (u : Fin M → R ⊗[F] E) :
    Continuous fun w : Fin M → R ⊗[F] E => hR R σ J u w := by
  unfold hR Formalism.UG.hform
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_apply j)

theorem isClosed_Wsub [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {r : ℕ}
    (P : Frame E M r) : IsClosed (Wsub R σ J P : Set (Fin M → R ⊗[F] E)) := by
  have : (Wsub R σ J P : Set (Fin M → R ⊗[F] E)) =
      ((⋂ a, {w | hR R σ J (ratV (F := F) R (P.e a)) w = 0}) ∩
        (⋂ a, {w | hR R σ J (ratV (F := F) R (P.f a)) w = 0})) ∩
        {w | hR R σ J (ratV (F := F) R P.z) w = 0} := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [this]
  exact ((isClosed_iInter fun a => isClosed_eq (continuous_hermitian_form_left σ J _) continuous_const).inter
    (isClosed_iInter fun a => isClosed_eq (continuous_hermitian_form_left σ J _) continuous_const)).inter
    (isClosed_eq (continuous_hermitian_form_left σ J _) continuous_const)

theorem continuous_tensor_conj [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous (sigR R σ) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (Lc.sigL R σ)

theorem isClosed_Sk [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)]
    (r : ℕ) : IsClosed (Sk R σ r : Set (Fin r → Fin r → R ⊗[F] E)) := by
  have : (Sk R σ r : Set (Fin r → Fin r → R ⊗[F] E)) =
      ⋂ a, ⋂ b, {c | c a b + sigR R σ (c b a) = 0} := by
    ext c
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    rfl
  rw [this]
  refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
  have hc : Continuous fun c : Fin r → Fin r → R ⊗[F] E => c a b + sigR R σ (c b a) :=
    (continuous_apply_apply a b).add ((continuous_tensor_conj σ).comp (continuous_apply_apply b a))
  exact isClosed_eq hc continuous_const

end Gen

theorem modOne_of (hC : HeisenbergCoordinates) (hW : WMod) : Cj.ModOne := by
  intro F E _ _ _ _ _ σ hCM M J hJ r P T hr hP h hh
  obtain ⟨Φ, hmul, hconj⟩ := hC F E σ hCM M J hJ r P T hr hP
  obtain ⟨htr, ht2, hlc, hsc⟩ := Lc.tensor_adele_topology_holds F E
  obtain ⟨hXlc, hXsc, hXt2, hXtg⟩ := Lc.locally_compact_adelic_unitary F E σ hCM M J hJ
  have : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have hAFtr : IsTopologicalRing (AF F) := inferInstance
  have : LocallyCompactSpace (Wsub (AF F) σ J P) :=
    (isClosed_Wsub σ J P).locallyCompactSpace
  have : LocallyCompactSpace (Sk (AF F) σ r) := (isClosed_Sk σ r).locallyCompactSpace
  have scV : SecondCountableTopology (Fin M → AF F ⊗[F] E) := inferInstance
  have scW : SecondCountableTopology (Wsub (AF F) σ J P) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have scK : SecondCountableTopology (Fin r → Fin r → AF F ⊗[F] E) := inferInstance
  have scS : SecondCountableTopology (Sk (AF F) σ r) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have scP : SecondCountableTopology (Fin r → Wsub (AF F) σ J P) := inferInstance
  have scE : SecondCountableTopologyEither (Fin r → Wsub (AF F) σ J P) (Sk (AF F) σ r) :=
    inferInstance
  have bV : BorelSpace (Fin M → AF F ⊗[F] E) := Pi.borelSpace
  have bW : BorelSpace (Wsub (AF F) σ J P) := Subtype.borelSpace _
  have bK : BorelSpace (Fin r → Fin r → AF F ⊗[F] E) := Pi.borelSpace
  have bS : BorelSpace (Sk (AF F) σ r) := Subtype.borelSpace _
  have bP : BorelSpace (Fin r → Wsub (AF F) σ J P) := Pi.borelSpace
  have bX : BorelSpace ((Fin r → Wsub (AF F) σ J P) × Sk (AF F) σ r) := Prod.borelSpace
  have bN : BorelSpace (FrameUnipotentSubgroup (AF F) σ J P) := Subtype.borelSpace _
  obtain ⟨νW, hνW⟩ : ∃ ν : Measure (Wsub (AF F) σ J P), ν.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨νS, hνS⟩ : ∃ ν : Measure (Sk (AF F) σ r), ν.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  have cW : SigmaCompactSpace (Wsub (AF F) σ J P) := inferInstance
  have cS : SigmaCompactSpace (Sk (AF F) σ r) := inferInstance
  have sW : SigmaFinite νW := inferInstance
  have sS : SigmaFinite νS := inferInstance
  let νP : Measure (Fin r → Wsub (AF F) σ J P) := Measure.pi fun _ => νW
  have hνP : νP.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have sP : SigmaFinite νP := Measure.pi.sigmaFinite _
  let ν : Measure ((Fin r → Wsub (AF F) σ J P) × Sk (AF F) σ r) := νP.prod νS
  have hν : ν.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hΦm : Measurable Φ := Φ.continuous.measurable
  have hΦsm : Measurable Φ.symm := Φ.symm.continuous.measurable

  have key : ∀ g : FrameUnipotentSubgroup (AF F) σ J P, MeasurePreserving (fun x => Φ (g * Φ.symm x)) ν ν := by
    intro g
    have hcont : Continuous fun p : (Fin r → Wsub (AF F) σ J P) × Sk (AF F) σ r =>
        (Φ (g * Φ.symm (p.1, 0))).2 + p.2 :=
      (continuous_snd.comp (Φ.continuous.comp (continuous_const.mul
        (Φ.symm.continuous.comp (continuous_fst.prodMk continuous_const))))).add continuous_snd
    have hsk := MeasurePreserving.skew_product (μa := νP) (μb := νP) (μc := νS) (μd := νS)
      (f := fun w => (Φ g).1 + w) (g := fun w c => (Φ (g * Φ.symm (w, 0))).2 + c)
      (measurePreserving_add_left νP (Φ g).1) hcont.measurable
      (ae_of_all _ fun w => map_add_left_eq_self νS _)
    convert hsk using 1
    funext p
    obtain ⟨w, c⟩ := p
    have h1 := (hmul g (Φ.symm (w, c))).1
    have h2 := (hmul g (Φ.symm (w, c))).2
    have h3 := (hmul g (Φ.symm (w, 0))).2
    simp only [Homeomorph.apply_symm_apply] at h1 h2 h3
    refine Prod.ext (funext fun a => Subtype.ext ?_) (Subtype.ext ?_)
    · have := congrFun h1 a
      simpa using this
    · show ((Φ (g * Φ.symm (w, c))).2 : Fin r → Fin r → AF F ⊗[F] E) =
        (((Φ (g * Φ.symm (w, 0))).2 + c : Sk (AF F) σ r) : Fin r → Fin r → AF F ⊗[F] E)
      rw [h2, AddSubgroup.coe_add, h3]
      simp only [AddSubgroup.coe_zero, add_zero]
      abel
  let μ : Measure (FrameUnipotentSubgroup (AF F) σ J P) := ν.map Φ.symm
  have hinvN : ∀ g : FrameUnipotentSubgroup (AF F) σ J P, μ.map (g * ·) = μ := by
    intro g
    have hcomp : (fun n => g * n) ∘ Φ.symm = Φ.symm ∘ (fun x => Φ (g * Φ.symm x)) := by
      funext x; simp
    rw [Measure.map_map (continuous_const_mul g).measurable hΦsm, hcomp,
      ← Measure.map_map hΦsm (key g).measurable, (key g).map_eq]
  have i1 : μ.IsMulLeftInvariant := ⟨hinvN⟩
  have i2 : IsFiniteMeasureOnCompacts μ := Measure.IsFiniteMeasureOnCompacts.map ν Φ.symm
  have i3 : μ.IsOpenPosMeasure := Φ.symm.continuous.isOpenPosMeasure_map Φ.symm.surjective
  have hμ : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := i2, toIsMulLeftInvariant := i1, toIsOpenPosMeasure := i3 }
  refine ⟨μ, hμ, fun f hf => ?_⟩

  let c : FrameUnipotentSubgroup (AF F) σ J P → FrameUnipotentSubgroup (AF F) σ J P := fun n =>
    ⟨h * (n : HA (AF F) σ J) * h⁻¹, norm_gen (AF F) σ J P h hh n n.2⟩
  have hc : Continuous c :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hA : MeasurePreserving (fun x => Φ (c (Φ.symm x))) ν ν := by
    have hact : MeasurePreserving (actW hh) νW νW :=
      ⟨(((lin (AF F) σ J h).continuous_on_pi.comp continuous_subtype_val).subtype_mk _).measurable,
        hW F E σ hCM M J hJ r P T hr hP h hh νW inferInstance⟩
    have hpi : MeasurePreserving (fun (w : Fin r → Wsub (AF F) σ J P) a => actW hh (w a)) νP νP :=
      measurePreserving_pi _ _ fun _ => hact
    have hsk := hpi.prod (MeasurePreserving.id νS)
    convert hsk using 1
    funext x
    obtain ⟨h1, h2⟩ := hconj h hh (Φ.symm x) (c (Φ.symm x)) rfl
    simp only [Homeomorph.apply_symm_apply] at h1 h2
    exact Prod.ext (funext fun a => Subtype.ext (h1 a)) h2
  have hmapc : μ.map c = μ := by
    have hcomp : c ∘ Φ.symm = Φ.symm ∘ (fun x => Φ (c (Φ.symm x))) := by
      funext x; simp
    rw [Measure.map_map hc.measurable hΦsm, hcomp, ← Measure.map_map hΦsm hA.measurable,
      hA.map_eq]
  have hfm : Measurable fun n : FrameUnipotentSubgroup (AF F) σ J P => f (n : HA (AF F) σ J) :=
    hf.comp measurable_subtype_coe
  calc ∫⁻ n, f (h * (n : HA (AF F) σ J) * h⁻¹) ∂μ
      = ∫⁻ n, (fun m : FrameUnipotentSubgroup (AF F) σ J P => f (m : HA (AF F) σ J)) (c n) ∂μ := rfl
    _ = ∫⁻ m, f (m : HA (AF F) σ J) ∂(μ.map c) := (lintegral_map hfm hc.measurable).symm
    _ = ∫⁻ m, f (m : HA (AF F) σ J) ∂μ := by rw [hmapc]

end PI.VolSemiDirect.W.Md
