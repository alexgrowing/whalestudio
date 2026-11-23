import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExSk

noncomputable section

namespace HcInf

open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.StandardLattice HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes HcS.L2.Fam.SG.Tau
  HcS.L2.Fam.SG.Tau.InfCmpCut Matrix MeasureTheory Filter Topology
open scoped TensorProduct ENNReal NNReal

section Upq

variable (P Q : ℕ)

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem cT_eq (X : Mat) : HcS.UG.cT (starRingEnd ℂ) X = Xᴴ := by
  ext i j
  simp [HcS.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]

theorem Jpq_mul_self : HcS.UG.Jpq P Q * HcS.UG.Jpq P Q = 1 := by
  simp [HcS.UG.Jpq, Matrix.fromBlocks_multiply]

theorem Jpq_conjTranspose : (HcS.UG.Jpq P Q)ᴴ = HcS.UG.Jpq P Q := by
  simp [HcS.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem mem_Upq_iff (g : GL (Fin P ⊕ Fin Q) ℂ) :
    g ∈ HcS.UG.Upq P Q ↔ (g : Mat)ᴴ * HcS.UG.Jpq P Q * (g : Mat) = HcS.UG.Jpq P Q := by
  unfold HcS.UG.Upq
  rw [← cT_eq]
  rfl

def toS (g : UpqT P Q) : HcS.UG.Upq P Q := g

theorem mat_eq (g : UpqT P Q) : UpqT.mat g = ((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ) : Mat) := rfl

theorem mat_inv (g : UpqT P Q) :
    (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat) =
      HcS.UG.Jpq P Q * (UpqT.mat g)ᴴ * HcS.UG.Jpq P Q := by
  have hmem : (UpqT.mat g)ᴴ * HcS.UG.Jpq P Q * UpqT.mat g = HcS.UG.Jpq P Q := by
    rw [mat_eq]
    exact (mem_Upq_iff P Q _).mp (toS P Q g).2
  have hAB : UpqT.mat g * (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat) = 1 := by
    rw [mat_eq, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat)
      = (HcS.UG.Jpq P Q * ((UpqT.mat g)ᴴ * HcS.UG.Jpq P Q * UpqT.mat g)) *
          (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat) := by
        rw [hmem, Jpq_mul_self, Matrix.one_mul]
    _ = HcS.UG.Jpq P Q * (UpqT.mat g)ᴴ * HcS.UG.Jpq P Q *
          (UpqT.mat g * (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hAB, Matrix.mul_one]

theorem isInducing_mat : IsInducing (UpqT.mat (P := P) (Q := Q)) := by
  have hv : IsInducing (fun g : UpqT P Q => ((toS P Q g : HcS.UG.Upq P Q) : GL (Fin P ⊕ Fin Q) ℂ)) := by
    rw [isInducing_iff]
    ext s
    rw [isOpen_induced_iff]
    show HcS.BasicNotions.instTopologicalSpaceUpqT._aux_1 P Q s ↔ _
    unfold HcS.BasicNotions.instTopologicalSpaceUpqT._aux_1
    rfl
  have he : IsInducing ((Units.embedProduct Mat) ∘
      (fun g : UpqT P Q => ((toS P Q g : HcS.UG.Upq P Q) : GL (Fin P ⊕ Fin Q) ℂ))) :=
    Units.isEmbedding_embedProduct.isInducing.comp hv
  have hcomp : (Units.embedProduct Mat) ∘
      (fun g : UpqT P Q => ((toS P Q g : HcS.UG.Upq P Q) : GL (Fin P ⊕ Fin Q) ℂ)) =
      (fun X : Mat => (X, MulOpposite.op (HcS.UG.Jpq P Q * Xᴴ * HcS.UG.Jpq P Q))) ∘ UpqT.mat := by
    funext x
    exact Prod.ext rfl (congrArg MulOpposite.op (mat_inv P Q x))
  rw [hcomp] at he
  refine IsInducing.of_comp ?_ ?_ he
  · exact Units.continuous_val.comp hv.continuous
  · exact continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))

theorem range_mat : Set.range (UpqT.mat (P := P) (Q := Q)) =
    {X : Mat | Xᴴ * HcS.UG.Jpq P Q * X = HcS.UG.Jpq P Q} := by
  ext X
  constructor
  · rintro ⟨g, rfl⟩
    show (UpqT.mat g)ᴴ * HcS.UG.Jpq P Q * UpqT.mat g = HcS.UG.Jpq P Q
    rw [mat_eq]
    exact (mem_Upq_iff P Q _).mp (toS P Q g).2
  · intro hX
    have hX' : Xᴴ * HcS.UG.Jpq P Q * X = HcS.UG.Jpq P Q := hX
    have hl : (HcS.UG.Jpq P Q * Xᴴ * HcS.UG.Jpq P Q) * X = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ, hX', Jpq_mul_self]
    have hr : X * (HcS.UG.Jpq P Q * Xᴴ * HcS.UG.Jpq P Q) = 1 := mul_eq_one_comm.mp hl
    let u : GL (Fin P ⊕ Fin Q) ℂ := ⟨X, _, hr, hl⟩
    have hu : u ∈ HcS.UG.Upq P Q := (mem_Upq_iff P Q u).mpr hX'
    exact ⟨(⟨u, hu⟩ : HcS.UG.Upq P Q), rfl⟩

theorem isClosedEmbedding_mat : IsClosedEmbedding (UpqT.mat (P := P) (Q := Q)) := by
  refine ⟨⟨isInducing_mat P Q, fun a b h => ?_⟩, ?_⟩
  · exact Subtype.ext (Units.ext h)
  · rw [range_mat]
    exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const

instance : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (HcS.UG.Upq P Q))

instance : BorelSpace (UpqT P Q) := ⟨rfl⟩

instance : LocallyCompactSpace (UpqT P Q) := by
  haveI : LocallyCompactSpace Mat :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact (isClosedEmbedding_mat P Q).locallyCompactSpace

instance : SecondCountableTopology (UpqT P Q) := by
  haveI : SecondCountableTopology Mat :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact (isInducing_mat P Q).secondCountableTopology

instance : SigmaCompactSpace (UpqT P Q) := inferInstance

end Upq

theorem cd_haar_finite (cd : CDHaar) : CdFin cd := by
  intro P Q
  haveI := cd.haar P Q
  infer_instance

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (T : Type) [Fintype T] (cd : CDHaar)

theorem haar_unique' : HaarUnique F E hc T cd := by
  intro W P Q Φ hmul hΦ hΦs μ hμ
  haveI : SigmaFinite (cd.cd P Q) := cd_haar_finite cd P Q
  haveI : (cd.cd P Q).IsHaarMeasure := cd.haar P Q
  haveI : (μ.map Φ).IsMulLeftInvariant := by
    constructor
    intro h
    have hLg : (fun x => Φ.symm h * x) = Φ.symm ∘ (fun y => h * y) ∘ Φ := by
      funext x
      apply Φ.injective
      simp [hmul]
    have hLgm : Measurable (fun x => Φ.symm h * x) := by
      rw [hLg]
      exact Φ.symm.measurable.comp ((measurable_const_mul h).comp Φ.measurable)
    have hc : (fun x => h * x) ∘ Φ = Φ ∘ (fun x => Φ.symm h * x) := by
      funext x
      simp [hmul]
    rw [Measure.map_map (measurable_const_mul h) Φ.measurable, hc,
      ← Measure.map_map Φ.measurable hLgm, map_mul_left_eq_self]
  haveI : IsFiniteMeasureOnCompacts (μ.map Φ) := by
    constructor
    intro K hK
    rw [MeasurableEquiv.map_apply]
    have hpre : Φ ⁻¹' K = Φ.symm '' K := by
      ext x
      constructor
      · intro hx
        exact ⟨Φ x, hx, Φ.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [hpre]
    exact (hK.image hΦs).measure_lt_top
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul (μ.map Φ) (Measure.pi fun _ : T => cd.cd P Q)⟩

end HcInf
