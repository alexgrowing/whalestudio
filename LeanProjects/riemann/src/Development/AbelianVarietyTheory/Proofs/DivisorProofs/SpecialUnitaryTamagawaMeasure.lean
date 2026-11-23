import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryAdelicRealizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfAdjointLevelMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSpecialUnitaryMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalSpecialUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerLatticeIffHatStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal Pointwise
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published

namespace GlobalTheory.TamUnf
open scoped GlobalTheory.GaugeEx

theorem stab_open_compact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ →
    IsOpen {k : finSU (IsCMField.complexConj E).toAlgHom Gᵀ | GlobalTheory.Mem.Vol.StabHat (maximalRealSubfield E) (Λ : Set (Fin r → E))
      ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ k.1 :
        GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
        Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E))} ∧
    IsCompact {k : finSU (IsCMField.complexConj E).toAlgHom Gᵀ | GlobalTheory.Mem.Vol.StabHat (maximalRealSubfield E) (Λ : Set (Fin r → E))
      ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ k.1 :
        GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
        Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E))} := by
  intro E _ _ _ r G Λ hfg hsp
  obtain ⟨K, hK, hKo, hKc⟩ := GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab (maximalRealSubfield E) E
    (IsCMField.complexConj E).toAlgHom r Gᵀ Λ hfg hsp
  have hset : {k : finSU (IsCMField.complexConj E).toAlgHom Gᵀ | GlobalTheory.Mem.Vol.StabHat (maximalRealSubfield E)
      (Λ : Set (Fin r → E))
      ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ k.1 :
        GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
        Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E))} =
      Subtype.val ⁻¹' (K : Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ)) := by
    ext k; exact (hK k.1).symm
  rw [hset]
  refine ⟨hKo.preimage continuous_subtype_val, ?_⟩
  have hcl : IsClosed ((finSU (IsCMField.complexConj E).toAlgHom Gᵀ : Subgroup _) :
      Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ)) := by
    have : ((finSU (IsCMField.complexConj E).toAlgHom Gᵀ : Subgroup _) :
        Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ)) =
        (fun g => ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ g :
          GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
          Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)).det) ⁻¹' {1} := by
      ext g; exact mem_finSU
    rw [this]
    exact isClosed_singleton.preimage (GlobalTheory.GaugeEx.continuous_mat _ _ _).matrix_det
  exact hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKc

set_option maxHeartbeats 1000000 in

theorem tam_unfold : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) [MeasurableSpace (realSU Ψ G)] [BorelSpace (realSU Ψ G)] (θ : Ψ → (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* ℂ)) (ν : Measure (Ψ → Fin r → Fin r → ℂ)) (μ₀ : Measure (realSU Ψ G)) (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (c : ℝ≥0∞), SelfDualLat G Λ → (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ ρ : Ψ, IsInfEmb ρ.1 (θ ρ)) → μ₀.IsHaarMeasure → HasDensityOne (realSU Ψ G) μ₀ ν → IsSReps G (Λ : Set (Fin r → E)) 1 s → c ≠ 0 → c ≠ ⊤ → ∃ (μ : Measure (SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ)) (𝓕 : Set (SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ)), μ.IsHaarMeasure ∧ Tendsto (fun ε : ℝ => μ {h | h ∈ stabSet (IsCMField.complexConj E).toAlgHom Gᵀ Λ ∧ ∀ ρ a b, ‖infMat (IsCMField.complexConj E).toAlgHom Gᵀ (θ ρ) h.1 a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε} / ν (tanBall Ψ r ε)) (𝓝[>] 0) (𝓝 c) ∧ IsFundamentalDomain ((SURat (IsCMField.complexConj E).toAlgHom Gᵀ).subgroupOf (SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ)) 𝓕 μ ∧ μ 𝓕 = (∑' j, covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G) μ₀) * c := by
  intro E _ _ _ r G Λ Ψ _ _ θ ν μ₀ J s c hL hΨ hθ hμ₀ hdens hs hc0 hct
  classical
  obtain ⟨e, he⟩ := GlobalTheory.T.special_unitary_adelic_realization E r G Ψ θ (fun a b => hL.1 a b) hL.2.1 hΨ hθ
  obtain ⟨hKo, hKc⟩ := stab_open_compact E r G Λ hL.2.2.1 hL.2.2.2.1
  obtain ⟨hSA, hSA'⟩ := GlobalTheory.T.self_adjoint_level_matrix E r G
  let mat : finSU (IsCMField.complexConj E).toAlgHom Gᵀ → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E) :=
    fun k => ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ k.1 :
      GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
      Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E))
  have mat_mul : ∀ a b, mat (a * b) = mat a * mat b := fun a b => rfl
  have mat_one : mat 1 = 1 := rfl
  have mat_inj : Function.Injective mat := fun a b h => Subtype.ext (Subtype.ext (Units.ext h))
  let Ks : Subgroup (finSU (IsCMField.complexConj E).toAlgHom Gᵀ) :=
    { carrier := {k | GlobalTheory.Mem.Vol.StabHat (maximalRealSubfield E) (Λ : Set (Fin r → E)) (mat k)}
      one_mem' := fun y => by rw [mat_one, Matrix.one_mulVec]
      mul_mem' := fun {a b} ha hb y => by
        rw [mat_mul, ← Matrix.mulVec_mulVec]
        exact (hb y).trans (ha _)
      inv_mem' := fun {a} ha y => by
        refine Iff.trans ?_ (ha _).symm
        rw [Matrix.mulVec_mulVec, ← mat_mul, mul_inv_cancel, mat_one, Matrix.one_mulVec] }
  have hKs : ∀ k, k ∈ Ks ↔ IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 (mat k) :=
    fun k => (GlobalTheory.T.stabilizer_lattice_iff_hat E r G Λ (mat k) (hSA k)).symm

  choose t ht using fun j => hSA' (s j) (hs.1 j)

  have hdisc : ∀ j, DiscreteTopology (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) := by
    intro j
    obtain ⟨L', hL', -, hsd⟩ := GlobalTheory.UCls.selfDual_latOf_translate E r G Λ (s j) hL (hs.1 j).1
    exact GlobalTheory.SUCount.discrete_inReal hΨ G _ L' hsd.2.2.1 hsd.2.2.2.1 fun γ hγ y hy => by
      rw [← SetLike.mem_coe, hL'] at hy ⊢
      have := (hγ.2.2 _).2 hy
      rw [GlobalTheory.LocGlob.ratM_mulVec_fv] at this
      exact this
  have hD : ∀ j, ∃ D : Set (realSU Ψ G), MeasurableSet D ∧
      (∀ x, ∃! g : inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j)), g • x ∈ D) ∧
      ∀ μ : Measure (realSU Ψ G), IsFundamentalDomain (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) D μ :=
    fun j => by
      haveI := hdisc j
      exact GlobalTheory.exists_isFundamentalDomain_subgroup _
  choose D hDm hDu hDf using hD

  have hsame : ∀ i j (a b : finSU (IsCMField.complexConj E).toAlgHom Gᵀ) (δ : Matrix (Fin r) (Fin r) E),
      (t i)⁻¹ * a ∈ Ks → (t j)⁻¹ * b ∈ Ks → IsSA G (GlobalTheory.UCls.ratM (maximalRealSubfield E) δ) →
      mat b = GlobalTheory.UCls.ratM (maximalRealSubfield E) δ * mat a → i = j := by
    intro i j a b δ ha hb hδ hab
    set k0 := ((t i)⁻¹ * a) * ((t j)⁻¹ * b)⁻¹ with hk0
    have hk0K : k0 ∈ Ks := mul_mem ha (inv_mem hb)
    refine hs.2.1 i j ⟨δ, hδ, mat k0, (hKs k0).1 hk0K, (hSA k0).2, ?_⟩
    have hti : mat (t i) = s i := ht i
    have htj : mat (t j) = s j := ht j
    have e1 : t j = b * ((t j)⁻¹ * b)⁻¹ := by group
    have e2 : mat a = mat (t i) * mat ((t i)⁻¹ * a) := by rw [← mat_mul]; congr 1; group
    calc s j = mat (t j) := htj.symm
      _ = mat (b * ((t j)⁻¹ * b)⁻¹) := congrArg mat e1
      _ = mat b * mat ((t j)⁻¹ * b)⁻¹ := mat_mul _ _
      _ = GlobalTheory.UCls.ratM (maximalRealSubfield E) δ * mat (t i) * (mat ((t i)⁻¹ * a) * mat ((t j)⁻¹ * b)⁻¹) := by
        rw [hab, e2]; simp only [Matrix.mul_assoc]
      _ = GlobalTheory.UCls.ratM (maximalRealSubfield E) δ * s i * mat k0 := by rw [hti, hk0, mat_mul ((t i)⁻¹ * a)]
  haveI : SecondCountableTopology (finSU (IsCMField.complexConj E).toAlgHom Gᵀ) :=
    TopologicalSpace.Subtype.secondCountableTopology _

  have hJc : Countable J := by
    have hdis : (Set.univ : Set J).PairwiseDisjoint fun j => t j • (Ks : Set (finSU (IsCMField.complexConj E).toAlgHom Gᵀ)) := by
      intro i _ j _ hij
      refine Set.disjoint_left.2 fun k hki hkj => hij ?_
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hki hkj
      exact hsame i j k k 1 hki hkj (by rw [GlobalTheory.SUVol.ratM_one]; exact ⟨(isKM_one _ G (Λ : Set (Fin r → E)) 1).1, det_one⟩) (by rw [GlobalTheory.SUVol.ratM_one, Matrix.one_mul])
    have := hdis.countable_of_isOpen (fun j _ => hKo.smul (t j)) (fun j _ => ⟨t j * 1, Set.smul_mem_smul_set (Ks.one_mem)⟩)
    exact Set.countable_univ_iff.1 this

  have ht' : ∀ j, mat (t j) = s j := ht
  haveI : LocallyCompactSpace (finSU (IsCMField.complexConj E).toAlgHom Gᵀ) :=
    hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds Ks.one_mem)
  obtain ⟨μ, hμH, hμ⟩ := exists_haar_prod (K := (Ks : Set (finSU (IsCMField.complexConj E).toAlgHom Gᵀ)))
    μ₀ e hKo hKc Ks.one_mem hc0 hct

  have hinf : ∀ (γ : SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ) (δ : GL (Fin r) E),
      (∀ ρ : Ψ, infMat (IsCMField.complexConj E).toAlgHom Gᵀ (θ ρ) γ.1 = (δ : Matrix (Fin r) (Fin r) E).map ρ.1) →
      ((e γ).1 : Ψ → GL (Fin r) ℂ) = embGL Ψ r δ :=
    fun γ δ h => funext fun ρ => Units.ext (((he γ).1 ρ).trans (h ρ))
  have hfin : ∀ (γ : SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ) (δ : Matrix (Fin r) (Fin r) E),
      finMat (IsCMField.complexConj E).toAlgHom Gᵀ γ.1 = GlobalTheory.UCls.ratM (maximalRealSubfield E) δ →
      mat (e γ).2 = GlobalTheory.UCls.ratM (maximalRealSubfield E) δ :=
    fun γ δ h => ((he γ).2).trans h

  let P : J → Set (SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ) :=
    fun j => e ⁻¹' (D j ×ˢ (t j • (Ks : Set (finSU (IsCMField.complexConj E).toAlgHom Gᵀ))))
  have hPm : ∀ j, MeasurableSet (P j) := fun j =>
    e.continuous.measurable ((hDm j).prod (hKo.smul (t j)).measurableSet)
  have hPd : Pairwise (Function.onFun Disjoint P) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hi hj => hij ?_
    have h1 := hi.2
    have h2 := hj.2
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at h1 h2
    exact hsame i j (e x).2 (e x).2 1 h1 h2
      (by rw [GlobalTheory.SUVol.ratM_one]; exact ⟨(isKM_one _ G (Λ : Set (Fin r → E)) 1).1, det_one⟩)
      (by rw [GlobalTheory.SUVol.ratM_one, Matrix.one_mul])

  have hex : ∀ x : SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ,
      ∃ g : (SURat (IsCMField.complexConj E).toAlgHom Gᵀ).subgroupOf (SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ),
        g • x ∈ ⋃ j, P j := by
    intro x
    obtain ⟨j, δ, hδ, k, hk, hkd, hg⟩ := hs.2.2 _ (hSA (e x).2)
    obtain ⟨hδ1, hδ2⟩ := GlobalTheory.SUCount.rat_of_isSA hδ
    obtain ⟨δg, rfl⟩ : IsUnit δ := (Matrix.isUnit_iff_isUnit_det δ).2 (hδ1 ▸ isUnit_one)
    have hδs : δg ∈ GlobalTheory.SUCount.ratSU G := ⟨hδ1, hδ2⟩
    obtain ⟨γ₀, hγ₀, -, hγ₀f⟩ := GlobalTheory.T.exists_rational_special_unitary E r G Ψ θ hθ _ (GlobalTheory.SUCount.isSA_toAd (inv_mem hδs))
    obtain ⟨kH, hkH⟩ := hSA' k ⟨hk.1, hkd⟩
    have hkH' : mat kH = k := hkH
    have hkK : kH ∈ Ks := (hKs kH).2 (hkH' ▸ hk)
    have hy : (e (γ₀ * x)).2 = t j * kH := by
      apply mat_inj
      calc mat (e (γ₀ * x)).2 = mat ((e γ₀).2 * (e x).2) := by rw [map_mul]; rfl
        _ = mat (e γ₀).2 * mat (e x).2 := mat_mul _ _
        _ = GlobalTheory.UCls.ratM (maximalRealSubfield E) ((δg⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
            (GlobalTheory.UCls.ratM (maximalRealSubfield E) (δg : Matrix (Fin r) (Fin r) E) * s j * k) := by
          rw [hfin γ₀ _ hγ₀f, ← hg]
        _ = s j * k := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← GlobalTheory.SUVol.ratM_mul, Units.inv_mul, GlobalTheory.SUVol.ratM_one,
            Matrix.one_mul]
        _ = mat (t j * kH) := by rw [mat_mul, ht' j, hkH']
    obtain ⟨β, hβ, -⟩ := hDu j (e (γ₀ * x)).1
    obtain ⟨β', hβ', hβe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 β.2)
    have hβs : β' ∈ GlobalTheory.SUCount.ratSU G := ⟨hβ'.1, hβ'.2.1⟩
    obtain ⟨γ₁, hγ₁, hγ₁i, hγ₁f⟩ := GlobalTheory.T.exists_rational_special_unitary E r G Ψ θ hθ _ (GlobalTheory.SUCount.isSA_toAd hβs)
    refine ⟨⟨γ₁ * γ₀, mul_mem hγ₁ hγ₀⟩, Set.mem_iUnion.2 ⟨j, ?_, ?_⟩⟩
    · have e1 : (e ((γ₁ * γ₀) * x)).1 = β • (e (γ₀ * x)).1 := by
        rw [mul_assoc, map_mul, Prod.fst_mul, Subgroup.smul_def, smul_eq_mul]
        congr 1
        exact Subtype.ext ((hinf γ₁ β' hγ₁i).trans hβe)
      show (e ((γ₁ * γ₀) * x)).1 ∈ D j
      rw [e1]; exact hβ
    · show (e ((γ₁ * γ₀) * x)).2 ∈ t j • (Ks : Set (finSU (IsCMField.complexConj E).toAlgHom Gᵀ))
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mul_assoc, map_mul, Prod.snd_mul, hy]
      have hc : (t j)⁻¹ * (e γ₁).2 * t j ∈ Ks := by
        rw [hKs]
        have hT : ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ (t j).1 :
            GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
            Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) = s j := ht j
        have hmem := GlobalTheory.SUCount.conj_mem_congSU (G := G) (L := (Λ : Set (Fin r → E)))
          (t := HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ (t j).1)
          (by rw [hT]; exact hs.1 j) (β := β') (by rw [hT]; exact hβ')
        have e2 : mat ((t j)⁻¹ * (e γ₁).2 * t j) = mat (t j)⁻¹ * mat (e γ₁).2 * mat (t j) := rfl
        rw [e2, hfin γ₁ _ hγ₁f]
        exact hmem.1
      have e3 : (t j)⁻¹ * ((e γ₁).2 * (t j * kH)) = (t j)⁻¹ * (e γ₁).2 * t j * kH := by
        simp only [mul_assoc]
      rw [e3]
      exact mul_mem hc hkK

  have huniq : ∀ (a : SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ)
      (η : (SURat (IsCMField.complexConj E).toAlgHom Gᵀ).subgroupOf (SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ)),
      a ∈ ⋃ j, P j → η • a ∈ ⋃ j, P j → η = 1 := by
    intro a η ha hηa
    obtain ⟨i, hai⟩ := Set.mem_iUnion.1 ha
    obtain ⟨j, hbj⟩ := Set.mem_iUnion.1 hηa
    have hak := hai.2
    have hbk := hbj.2
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hak hbk
    obtain ⟨δ, hδ, hδi, hδf⟩ := GlobalTheory.T.rational_special_unitary_mem E r G Ψ θ hΨ hθ η.1 η.2
    have hηa' : η • a = η.1 * a := rfl
    have hmat : mat (e (η • a)).2 = GlobalTheory.UCls.ratM (maximalRealSubfield E) δ * mat (e a).2 := by
      calc mat (e (η • a)).2 = mat ((e η.1).2 * (e a).2) := by rw [hηa', map_mul]; rfl
        _ = _ := by rw [mat_mul, hfin η.1 δ hδf]
    obtain rfl := hsame i j (e a).2 (e (η • a)).2 δ hak hbk hδ hmat
    obtain ⟨hδ1, hδ2⟩ := GlobalTheory.SUCount.rat_of_isSA hδ
    obtain ⟨δg, rfl⟩ : IsUnit δ := (Matrix.isUnit_iff_isUnit_det δ).2 (hδ1 ▸ isUnit_one)
    have hst : δg ∈ ratStab G (Λ : Set (Fin r → E)) (s i) := by
      refine GlobalTheory.SUVol.TamModel.mem_ratStab_of G _ (s i) (mat (((t i)⁻¹ * (e (η • a)).2) * ((t i)⁻¹ * (e a).2)⁻¹))
        δg hδ1 hδ2 ((hKs _).1 (mul_mem hbk (inv_mem hak))) ?_
      rw [← ht' i, ← mat_mul]
      have e4 : t i * ((t i)⁻¹ * (e (η • a)).2 * ((t i)⁻¹ * (e a).2)⁻¹) = (e (η • a)).2 * ((e a).2)⁻¹ * t i := by
        simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
      rw [e4, mat_mul, mat_mul, hmat, Matrix.mul_assoc _ (mat (e a).2), ← mat_mul, mul_inv_cancel, mat_one,
        Matrix.mul_one]
    have hβmem : (⟨embGL Ψ r δg, embGL_mem_realSU Ψ G δg hδ1 hδ2⟩ : realSU Ψ G) ∈
        inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s i)) :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨δg, hst, rfl⟩)
    have hreal : (e (η • a)).1 = (⟨_, hβmem⟩ : inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s i))) • (e a).1 := by
      rw [hηa', map_mul, Prod.fst_mul, Subgroup.smul_def, smul_eq_mul]
      congr 1
      exact Subtype.ext (hinf η.1 δg hδi)
    obtain ⟨g0, -, hg0u⟩ := hDu i (e a).1
    have hβ1 : (⟨_, hβmem⟩ : inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s i))) = 1 :=
      (hg0u _ (by show _ ∈ D i; rw [← hreal]; exact hbj.1)).trans
        (hg0u 1 (by show (1 : inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s i))) • (e a).1 ∈ D i; rw [one_smul]; exact hai.1)).symm
    have hemb : embGL Ψ r δg = 1 := congrArg (fun b : inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s i)) =>
      ((b : realSU Ψ G) : Ψ → GL (Fin r) ℂ)) hβ1
    have hδ1' : δg = 1 := by
      obtain ⟨τ0, hτ0⟩ : ∃ τ : E →+* ℂ, τ ∈ Ψ := by
        let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
        by_cases h : τ ∈ Ψ
        · exact ⟨τ, h⟩
        · exact ⟨_, by_contra fun h' => h ((hΨ τ).2 h')⟩
      have h1 := congrArg (fun g : Ψ → GL (Fin r) ℂ => ((g ⟨τ0, hτ0⟩ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) hemb
      have h2 : (δg : Matrix (Fin r) (Fin r) E).map τ0 = (1 : Matrix (Fin r) (Fin r) E).map τ0 := by
        rw [Matrix.map_one _ (map_zero τ0) (map_one τ0)]
        exact h1
      exact Units.ext (Matrix.map_injective τ0.injective h2)
    subst hδ1'
    have hη1 : e η.1 = 1 := by
      refine Prod.ext ?_ ?_
      · exact Subtype.ext ((hinf η.1 1 hδi).trans (map_one _))
      · apply mat_inj
        rw [hfin η.1 _ hδf, Units.val_one, GlobalTheory.SUVol.ratM_one, Prod.snd_one, mat_one]
    exact Subtype.ext (by simpa using e.injective (hη1.trans (map_one e).symm))

  have hF : IsFundamentalDomain ((SURat (IsCMField.complexConj E).toAlgHom Gᵀ).subgroupOf
      (SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ)) (⋃ j, P j) μ := by
    refine IsFundamentalDomain.mk' (MeasurableSet.iUnion hPm).nullMeasurableSet fun x => ?_
    obtain ⟨g, hg⟩ := hex x
    refine ⟨g, hg, fun g' hg' => mul_inv_eq_one.1 (huniq _ (g' * g⁻¹) hg ?_)⟩
    rwa [mul_smul, inv_smul_smul]

  have hμF : μ (⋃ j, P j) = (∑' j, covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G) μ₀) * c := by
    rw [measure_iUnion hPd hPm, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun j => ?_
    rw [hμ _ (hDm j) (t j)]
    haveI := hdisc j
    haveI := GlobalTheory.countable_of_discrete_subgroup (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j)))
    rw [(hDf j μ₀).covolume_eq_volume]

  have hgB : ∀ ε : ℝ, MeasurableSet (grpBall (realSU Ψ G) ε) := fun ε => by
    refine IsOpen.measurableSet ?_
    have : grpBall (realSU Ψ G) ε = ⋂ τ : Ψ, ⋂ a : Fin r, ⋂ b : Fin r, {g : realSU Ψ G |
        ‖((g.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε} := by
      ext g; simp [grpBall]
    rw [this]
    refine isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    refine isOpen_lt (Continuous.norm (Continuous.sub ?_ continuous_const)) continuous_const
    exact (continuous_apply b).comp ((continuous_apply a).comp
      ((Units.continuous_val (M := Matrix (Fin r) (Fin r) ℂ)).comp ((continuous_apply τ).comp continuous_subtype_val)))
  have hT : ∀ ε : ℝ, μ {h | h ∈ stabSet (IsCMField.complexConj E).toAlgHom Gᵀ Λ ∧ ∀ ρ a b,
      ‖infMat (IsCMField.complexConj E).toAlgHom Gᵀ (θ ρ) h.1 a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε} =
      μ₀ (grpBall (realSU Ψ G) ε) * c := by
    intro ε
    have : {h | h ∈ stabSet (IsCMField.complexConj E).toAlgHom Gᵀ Λ ∧ ∀ ρ a b,
        ‖infMat (IsCMField.complexConj E).toAlgHom Gᵀ (θ ρ) h.1 a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε} =
        e ⁻¹' (grpBall (realSU Ψ G) ε ×ˢ ((1 : finSU (IsCMField.complexConj E).toAlgHom Gᵀ) •
          (Ks : Set (finSU (IsCMField.complexConj E).toAlgHom Gᵀ)))) := by
      ext h
      rw [one_smul, Set.mem_preimage, Set.mem_prod, and_comm]
      refine and_congr ?_ ?_
      · show GlobalTheory.Mem.Vol.StabHat (maximalRealSubfield E) (Λ : Set (Fin r → E)) (finMat (IsCMField.complexConj E).toAlgHom Gᵀ h.1) ↔
          GlobalTheory.Mem.Vol.StabHat (maximalRealSubfield E) (Λ : Set (Fin r → E)) (mat (e h).2)
        rw [show mat (e h).2 = finMat (IsCMField.complexConj E).toAlgHom Gᵀ h.1 from (he h).2]
      · show (∀ ρ a b, ‖infMat (IsCMField.complexConj E).toAlgHom Gᵀ (θ ρ) h.1 a b -
            (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε) ↔
          ∀ τ a b, ‖(((e h).1.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε
        simp only [(he h).1]
    rw [this, hμ _ (hgB ε) 1]
  have hd : Tendsto (fun ε : ℝ => μ₀ (grpBall (realSU Ψ G) ε) / ν (tanBall Ψ r ε)) (𝓝[>] 0) (𝓝 1) := hdens
  refine ⟨μ, ⋃ j, P j, hμH, ?_, hF, hμF⟩
  have h1 := ENNReal.Tendsto.const_mul hd (Or.inr hct) (a := c)
  rw [mul_one] at h1
  refine h1.congr fun ε => ?_
  rw [hT ε, mul_comm (μ₀ _) c, mul_div_assoc]

end GlobalTheory.TamUnf
