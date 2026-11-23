import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupRealPointsEquivPiIndefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqDefiniteCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.DefiniteMeasure

open Formalism.IndefR.Lev GlobalTheory.Mem.VolExists

theorem exists_level (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (e0 : GA D V ≃ₜ* HA (Ainf D.host.F) D.sp.cm.sig V.gram × HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
    (hf : ∀ h, HA.mat (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (e0 h).2 = finHom V h)
    (hi : ∀ h, HA.mat (Ainf D.host.F) D.sp.cm.sig V.gram (e0 h).1 = infHom V h) :
    ∃ K : Subgroup (HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram),
      (∀ h : GA D V, (e0 h).2 ∈ K ↔ finE V h ∈ lev D.sp.cm V.gram β L) ∧
      IsOpen (K : Set (HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) ∧
      IsCompact (K : Set (HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := by
  let K : Subgroup (HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram) :=
    (lev D.sp.cm V.gram β L).comap
      ((Formalism.UG.bc (swapAE D)).comp (HR (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).subtype)
  have hK : ∀ h : GA D V, (e0 h).2 ∈ K ↔ finE V h ∈ lev D.sp.cm V.gram β L := fun h => by
    have e : HA.mat (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (e0 h).2 = finHom V h := hf h
    change Formalism.UG.bc (swapAE D) (HA.mat (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (e0 h).2) ∈
      lev D.sp.cm V.gram β L ↔ _
    rw [e]
    rfl
  have hKo : IsOpen (K : Set (HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := by
    have hc : Continuous fun b : HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram => e0.symm (1, b) :=
      e0.symm.continuous.comp (continuous_const.prodMk continuous_id)
    have h := (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L).preimage hc
    convert h using 1
    ext b
    have := hK (e0.symm (1, b))
    rw [e0.apply_symm_apply] at this
    exact this
  have hKc : IsCompact (K : Set (HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := by
    have hc : Continuous fun h : GA D V => (e0 h).2 := continuous_snd.comp e0.continuous
    have h := (GlobalTheory.ParahoricCompact.isCompact_levG V β L).image hc
    convert h using 1
    ext b
    constructor
    · intro hb
      have h1 := hK (e0.symm (1, b))
      have h2 := hi (e0.symm (1, b))
      rw [e0.apply_symm_apply] at h1 h2
      refine ⟨e0.symm (1, b), ⟨?_, h1.1 hb⟩, congrArg Prod.snd (e0.apply_symm_apply _)⟩
      exact h2.symm
    · rintro ⟨h, hh, rfl⟩
      exact (hK h).2 hh.2
  exact ⟨K, hK, hKo, hKc⟩

theorem exists_isMeasLevW (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hW : V.SigOK)
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (ν : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))
    (hν : ∀ ρ, (ν ρ).IsHaarMeasure) (hg : ∀ ρ m, good ρ m ↔ m = ν ρ) :
    ∃ μ, IsMeasLevW V (lev D.sp.cm V.gram β L) good μ := by
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host D.R D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hθ := GlobalTheory.Mem.VolEmb.existsUnique_infEmb D.host.F D.host.E D.sp.cm.sig hcm
  choose θ hθ1 hθ2 using fun i => hθ (tauE D i)
  have hA := fun i => GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (tauE D i))
  choose A hA1 using fun i => (hA i).2.1
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig V.rank V.gram _ (tauE D) θ
    (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) A hcm hτ hθ1 (fun i => hW (tauE D i)) hA1
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  obtain ⟨-, hsc, ht2⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  obtain ⟨K, hK, hKo, hKc⟩ := exists_level D V β L e0 (fun h => Units.ext (he0 h).1) fun h => Units.ext (he0 h).2
  haveI : IsTopologicalGroup (HA (AF D.host.F) D.sp.cm.sig V.gram) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (HA (AF D.host.F) D.sp.cm.sig V.gram) := ⟨rfl⟩
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hinj := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective
  haveI := hν
  let e : HA (AF D.host.F) D.sp.cm.sig V.gram ≃ₜ*
      (∀ i, UpqT (V.sig (tauE D i)).1 (V.sig (tauE D i)).2) × HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram :=
    e0.trans
      { e1.toMulEquiv.prodCongr (MulEquiv.refl _) with
        continuous_toFun := e1.continuous_toFun.prodMap continuous_id
        continuous_invFun := e1.continuous_invFun.prodMap continuous_id }
  have hee : ∀ h, e h = (e1 (e0 h).1, (e0 h).2) := fun h => rfl
  obtain ⟨μ, hμ, hμB⟩ := exists_haar_prod ν e K hKo hKc
  refine ⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ' = θ := funext fun i => hθ2 i _ (hθ' i)
  refine ⟨⟨A, hA1⟩, fun A' hA' => ⟨⟨ν, fun ρ => (hg ρ _).2 rfl⟩, fun m hm B hB => ?_⟩⟩
  obtain rfl : m = ν := funext fun ρ => (hg ρ _).1 (hm ρ)
  have hu : ∀ i, ∃ u : UpqT (V.sig (tauE D i)).1 (V.sig (tauE D i)).2, UpqT.mat u * A i = A' i := by
    intro i
    obtain ⟨C, h1, h2⟩ := (hA i).2.2 _ (hA1 i)
    obtain ⟨C', h3, h4⟩ := (hA i).2.2 _ (hA' i)
    exact exists_upq_mul _ _ C C' h1 h2 h3 h4 ((hA1 i).trans (hA' i).symm)
  choose u hu using hu
  have key := hμB (fun i => (fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i))
    (fun i => measurable_const_mul _ (measurable_mul_const _ (hB i)))
  have hcj : ∀ i, m i ((fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) = m i (B i) := by
    intro i
    haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant _ _ _ (hν i)
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
      rw [← hu i, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
    rw [mat_mul, mat_mul, Matrix.mul_assoc, h3, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hu i]
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

theorem exists_probHaar (P Q : ℕ) (h : P = 0 ∨ Q = 0) : ∃ ν : Measure (UpqT P Q), ν.IsHaarMeasure ∧
    ∀ m : Measure (UpqT P Q), (m.IsHaarMeasure ∧ IsProbabilityMeasure m) ↔ m = ν := by
  haveI : CompactSpace (UpqT P Q) := by
    rcases h with rfl | rfl
    exacts [(GlobalTheory.compactSpace_UpqT_definite Q).2, (GlobalTheory.compactSpace_UpqT_definite P).1]
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  let ν : Measure (UpqT P Q) := Measure.haarMeasure ⊤
  haveI hν : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure ⊤
  haveI hp : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self (K₀ := ⊤)⟩
  refine ⟨ν, hν, fun m => ⟨fun ⟨h1, h2⟩ => ?_, fun e => e ▸ ⟨hν, hp⟩⟩⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure m ν

theorem exists_isMeasDef : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), IsFrame β Λ → V.SigOK → (∀ τ, (V.sig (tauE D τ)).1 = 0 ∨ (V.sig (tauE D τ)).2 = 0) → ∃ μ 𝓕, IsMeasDef V (lev D.sp.cm V.gram β L) μ 𝓕 := by
  intro D V β _ L _ hW hd
  choose ν hν hg using fun ρ => exists_probHaar _ _ (hd ρ)
  obtain ⟨μ, hμ⟩ := exists_isMeasLevW D V β L hW (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) ν hν hg
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

end GlobalTheory.Mem.DefiniteMeasure
