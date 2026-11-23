import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Idem3
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneOrthogonalIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMemIffWeightRaisingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipHaar

open GlobalTheory.Mem.UnipCocompact

theorem haar_mass_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N]
    (hc : GlobalTheory.Cusp.Cocompact Γ N) :
    ∃ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure ∧ IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ ∧ μ 𝓕 = 1 := by
  obtain ⟨⟨𝓕, h𝓕⟩, h2⟩ := GlobalTheory.Mem.Vol.fundamentalDomain_exists_measure_eq_of_discrete (Γ.subgroupOf N) (Measure.haar : Measure N)
  have h0 : (Measure.haar : Measure N) 𝓕 ≠ 0 := (h2 𝓕 𝓕 h𝓕 h𝓕).2
  have ht : (Measure.haar : Measure N) 𝓕 ≠ ⊤ := hc.measure_ne_top h𝓕
  refine ⟨((Measure.haar : Measure N) 𝓕)⁻¹ • Measure.haar, 𝓕, Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 ht) (ENNReal.inv_ne_top.2 h0), h𝓕.mono Measure.smul_absolutelyContinuous, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 ht]

end GlobalTheory.UnipHaar

namespace GlobalTheory.UnipHaar
open GlobalTheory.Mem.UnipCocompact

theorem exists_haar_fundamentalDomain_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E d₁) (H' : Plane E n d₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∃ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure ∧ IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro F E _ _ _ _ _ σ B n d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hH
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n W.J
  haveI : DiscreteTopology (ratU σ W.J) := GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ n W.J
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hinv := sigma_invol hB.cm
  have hdet := GlobalTheory.T.skew_hermitian_det_ne_zero F E σ B n W r s hW
  obtain ⟨hcont, hm, hi, h0, hU⟩ := GlobalTheory.T.hermitian_adjoint_involution F E σ n W.J hinv hW.skew hdet
  obtain ⟨he, he0, hs⟩ := GlobalTheory.T.adapted_plane_orthogonal_idempotents F E σ B n d₁ W W₁ H' i₀ i₁ hinv hW.skew hdet hH
  have hmem := GlobalTheory.T.unipotent_mem_iff_weight_raising F E σ B n d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hH
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨eA⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := eA.isEmbedding.t2Space
  have hRc : IsClosed (raise (idem3 σ W.J H') wt3 0 : Set (Matrix (Fin n) (Fin n) (AE F E))) := by
    have e : (raise (idem3 σ W.J H') wt3 0 : Set (Matrix (Fin n) (Fin n) (AE F E))) =
        ⋂ a, ⋂ b, ⋂ (_ : wt3 a ≤ wt3 b + ((0 : ℕ) : ℤ)), {X | idem3 σ W.J H' a * X * idem3 σ W.J H' b = 0} := by
      ext X; simp only [Set.mem_iInter]; rfl
    rw [e]
    exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const) continuous_const
  have hmat : Continuous (fun g : UA σ W.J => mat g) := Units.continuous_val.comp continuous_subtype_val
  have hNc : IsClosed (unip σ W H' : Set (UA σ W.J)) := by
    have e : (unip σ W H' : Set (UA σ W.J)) = (fun g => mat g - 1) ⁻¹' (raise (idem3 σ W.J H') wt3 0 : Set _) := by
      ext g; exact hmem g
    rw [e]; exact hRc.preimage (hmat.sub continuous_const)
  haveI : LocallyCompactSpace (unip σ W H') := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine haar_mass_one (ratU σ W.J) (unip σ W H') ?_
  obtain ⟨K, hK, hKs⟩ := GlobalTheory.AutFunCompare.tens_cocompact (F := F) (E := E)
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  obtain ⟨K', hK', k1, k2⟩ := compact_mod_of_weights (st := adj σ W.J) (w := wt3)
    (φ.mapMatrix (m := Fin n)).range
    (Matrix.scalar _ (φ (1 / 2))) (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K) hcont hm hi h0
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h]⟩
    (by rw [← map_add, ← map_add, add_halves, map_one, map_one])
    (fun x => (Matrix.scalar_commute _ (fun _ => Commute.all _ _) x).eq)
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK)
    (fun X => by
      choose y hy using fun i j => hKs (X i j)
      exact ⟨_, ⟨Matrix.of y, rfl⟩, fun i _ j _ => hy i j⟩) he he0 hs
  let lift : ∀ x : Matrix (Fin n) (Fin n) (AE F E), (adj σ W.J x * x = 1 ∧ x * adj σ W.J x = 1) ∧
      x - 1 ∈ raise (idem3 σ W.J H') wt3 0 → unip σ W H' := fun x hx =>
    ⟨⟨⟨x, adj σ W.J x, hx.1.2, hx.1.1⟩, (hU x).1 hx.1.1⟩, (hmem _).2 hx.2⟩
  let f : unip σ W H' → _ := fun u => Units.embedProduct _ u.1.1
  have hf : Topology.IsInducing f :=
    Units.isInducing_embedProduct.comp (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  refine ⟨f ⁻¹' ((fun x => (x, MulOpposite.op (adj σ W.J x))) '' K'),
    hf.isCompact_preimage' (hK'.image (continuous_id.prodMk (MulOpposite.continuous_op.comp hcont))) ?_, fun u => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨lift x (k1 x hx), rfl⟩
  · have u1 : adj σ W.J (mat u.1) * mat u.1 = 1 := (hU _).2 u.1.2
    obtain ⟨γ, ⟨a, ha⟩, p1, k, hk, p2⟩ := k2 (mat u.1) ⟨⟨u1, mul_eq_one_comm.1 u1⟩, (hmem _).1 u.2⟩
    obtain ⟨b, hb⟩ := h0 γ ⟨a, ha⟩
    have inj : Function.Injective (φ.mapMatrix (m := Fin n)) := Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective
    have hab : a * b = 1 := inj (by rw [map_mul, ha, hb, map_one, p1.1.2])
    have hrat : (lift γ p1 : UA σ W.J) ∈ ratU σ W.J := by
      refine ⟨⟨a, b, hab, mul_eq_one_comm.1 hab⟩, Units.ext ?_⟩
      exact ha
    refine ⟨(lift γ p1)⁻¹, Subgroup.mem_subgroupOf.2 (inv_mem hrat), ?_⟩
    refine ⟨k, hk, ?_⟩
    change (k, MulOpposite.op (adj σ W.J k)) = Units.embedProduct _ ((((lift γ p1)⁻¹ * u : unip σ W H') : UA σ W.J) : GL (Fin n) (AE F E))
    have hv : ((((lift γ p1)⁻¹ * u : unip σ W H') : UA σ W.J) : GL (Fin n) (AE F E)) = ((lift k (k1 k hk) : UA σ W.J) : GL (Fin n) (AE F E)) := by
      refine Units.ext ?_
      change adj σ W.J γ * mat u.1 = k
      rw [p2, ← mul_assoc, p1.1.1, one_mul]
    rw [hv]; rfl

end GlobalTheory.UnipHaar

end
