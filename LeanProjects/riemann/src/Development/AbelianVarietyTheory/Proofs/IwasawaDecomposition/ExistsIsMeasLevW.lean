import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupRealPointsEquivPiIndefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelMeasure

theorem isMinf_unique {p q : ℕ} {m m' : Measure (UpqT p q)} (h : Lev.IsMinf m) (h' : Lev.IsMinf m') : m' = m := by
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).1
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.1
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.2.1
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.2.2.1
  haveI := h.1
  haveI := h'.1
  have e : m' = ((Measure.haarScalarFactor m' m : NNReal) : ENNReal) • m := Measure.isMulLeftInvariant_eq_smul m' m
  have h1 := GlobalTheory.OmegaDensityScale.omegaDensity_smul h.2 (Measure.haarScalarFactor m' m)
  rw [← e] at h1
  have h2 := GlobalTheory.OmegaDensityScale.omegaDensity_unique h'.2 h1
  have h0 : minfDensity (p + q) ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have ht : minfDensity (p + q) ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)
  have hc : ((Measure.haarScalarFactor m' m : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 (h2.trans (one_mul _).symm)
  rw [e, hc, one_smul]

theorem exists_isMeasLevW (D : D7) (V : HSp D) (hV : V.SigOK) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hKo : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)))
    (hKc : IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V)))
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (m : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))
    (hm : ∀ ρ, (m ρ).IsHaarMeasure) (hg : ∀ ρ, good ρ (m ρ)) (hu : ∀ ρ m', good ρ m' → m' = m ρ) :
    ∃ μ, Lev.IsMeasLevW V K good μ := by
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hθ := GlobalTheory.Mem.VolEmb.existsUnique_infEmb D.host.F D.host.E D.sp.cm.sig hcm
  choose θ hθ1 hθ2 using fun i => hθ (tauE D i)
  have hA := fun i => GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hV (tauE D i))
  choose A hA1 using fun i => (hA i).2.1
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig V.rank V.gram D.what₂.Tau (tauE D) θ
    (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) A hcm hτ hθ1 (fun i => hV (tauE D i)) hA1
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  obtain ⟨-, hsc, ht2⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hinj := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective
  let j : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* GA D V :=
    (e0.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : Continuous j := e0.symm.continuous.comp (Continuous.prodMk_right 1)
  have hj0 : ∀ k, e0 (j k) = (1, k) := fun k => e0.apply_symm_apply _
  have hfin : ∀ h : GA D V, Lev.finE V (j (e0 h).2) = Lev.finE V h := by
    intro h
    have h1 : finHom V (j (e0 h).2) = finHom V h := by
      refine Units.ext ?_
      have a1 := (he0 (j (e0 h).2)).1
      have a2 := (he0 h).1
      rw [hj0] at a1
      exact a1.symm.trans a2
    rw [Lev.finE_eq, Lev.finE_eq, h1]
  have hinf : ∀ k, j k ∈ GfC V := by
    intro k
    have a1 := (he0 (j k)).2
    rw [hj0] at a1
    exact Units.ext a1.symm
  let K' := (K.comap (Lev.finE V)).comap j
  have hK : ∀ h : GA D V, (e0 h).2 ∈ K' ↔ Lev.finE V h ∈ K := fun h => by
    rw [← hfin h]; rfl
  have hK'o : IsOpen (K' : Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := hKo.preimage hj
  have hK'c : IsCompact (K' : Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := by
    have h1 := hKc.image (continuous_snd.comp e0.continuous)
    convert h1 using 1
    ext k
    constructor
    · intro hk
      exact ⟨j k, ⟨hinf k, hk⟩, congrArg Prod.snd (hj0 k)⟩
    · rintro ⟨h, hh, rfl⟩
      exact (hK h).2 hh.2
  let e : GA D V ≃ₜ* (∀ i, UpqT (V.sig (tauE D i)).1 (V.sig (tauE D i)).2) ×
      HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram :=
    e0.trans
      { e1.toMulEquiv.prodCongr (MulEquiv.refl _) with
        continuous_toFun := e1.continuous_toFun.prodMap continuous_id
        continuous_invFun := e1.continuous_invFun.prodMap continuous_id }
  have hee : ∀ h, e h = (e1 (e0 h).1, (e0 h).2) := fun h => rfl
  obtain ⟨μ, hμ, hμB⟩ := GlobalTheory.Mem.VolExists.exists_haar_prod m e K' hK'o hK'c
  refine ⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ' = θ := funext fun i => hθ2 i _ (hθ' i)
  refine ⟨⟨A, hA1⟩, fun A' hA' => ⟨⟨m, hg⟩, fun m' hm' B hB => ?_⟩⟩
  obtain rfl : m' = m := funext fun i => hu i _ (hm' i)
  have hv : ∀ i, ∃ u : UpqT (V.sig (tauE D i)).1 (V.sig (tauE D i)).2, UpqT.mat u * A i = A' i := by
    intro i
    obtain ⟨C, h1, h2⟩ := (hA i).2.2 _ (hA1 i)
    obtain ⟨C', h3, h4⟩ := (hA i).2.2 _ (hA' i)
    exact GlobalTheory.Mem.VolExists.exists_upq_mul _ _ C C' h1 h2 h3 h4 ((hA1 i).trans (hA' i).symm)
  choose u hv using hv
  have key := hμB (fun i => (fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i))
    (fun i => measurable_const_mul _ (measurable_mul_const _ (hB i)))
  have hcj : ∀ i, m' i ((fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) = m' i (B i) := by
    intro i
    haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant _ _ _ (hm i)
    rw [measure_preimage_mul, measure_preimage_mul_right]
  rw [Finset.prod_congr rfl (fun i _ => hcj i)] at key
  rw [← key]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, hee, Set.mem_preimage]
  rw [hK]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  have h1 : UpqT.mat (e1 (e0 h).1 i) * A i = A i * infMat D.sp.cm.sig V.gram (θ' i) h := by
    rw [he1, (he0 h).2]; rfl
  have h2 : UpqT.mat (u i * e1 (e0 h).1 i * (u i)⁻¹) * A' i = A' i * infMat D.sp.cm.sig V.gram (θ' i) h := by
    have h3 : UpqT.mat (u i)⁻¹ * A' i = A i := by
      rw [← hv i, ← Matrix.mul_assoc, ← GlobalTheory.Mem.VolExists.mat_mul, inv_mul_cancel, GlobalTheory.Mem.VolExists.mat_one,
        Matrix.one_mul]
    rw [GlobalTheory.Mem.VolExists.mat_mul, GlobalTheory.Mem.VolExists.mat_mul, Matrix.mul_assoc, h3, Matrix.mul_assoc, h1,
      ← Matrix.mul_assoc, hv i]
  constructor
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨C', h3, -⟩ := (hA i).2.2 _ (hA' i)
    have : b = u i * e1 (e0 h).1 i * (u i)⁻¹ := by
      apply hinj
      have h5 := congrArg (· * C') (hbe.trans h2.symm)
      simpa only [Matrix.mul_assoc, h3, Matrix.mul_one] using h5
    exact this ▸ hb
  · intro hb
    exact ⟨_, hb, h2⟩

theorem exists_isMeasLev (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hV : V.SigOK) :
    ∃ μ, Lev.IsMeasLev V (lev D.sp.cm V.gram β L) μ := by
  choose m hm using GlobalTheory.MinfMeasure.exists_isMinf
  exact exists_isMeasLevW D V hV _ (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L)
    (GlobalTheory.ParahoricCompact.isCompact_levG V β L) _ (fun _ => m _ _) (fun _ => (hm _ _).1) (fun _ => hm _ _)
    (fun _ _ h => isMinf_unique (hm _ _) h)

theorem exists_isMeasFD : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), IsFrame β Λ → V.SigOK → ∃ μ 𝓕, Lev.IsMeasFD V (lev D.sp.cm V.gram β L) μ 𝓕 := by
  intro D V β _ L _ hV
  obtain ⟨μ, hμ⟩ := exists_isMeasLev D V β L hV
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

end GlobalTheory.LevelMeasure
