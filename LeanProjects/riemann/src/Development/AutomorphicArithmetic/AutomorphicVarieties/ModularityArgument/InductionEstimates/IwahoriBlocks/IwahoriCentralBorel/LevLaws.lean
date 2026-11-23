import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AutomorphicArithmetic.AdelicGluing.LevFIsOpenIsCompactLeIntegral

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private def cj {G : Type} [Group G] (c : G) (U : Subgroup G) : Subgroup G where
  carrier := {x | c⁻¹ * x * c ∈ U}
  one_mem' := by simp [U.one_mem]
  mul_mem' {a b} ha hb := by
    have h := U.mul_mem ha hb
    have e : c⁻¹ * (a * b) * c = c⁻¹ * a * c * (c⁻¹ * b * c) := by group
    simpa only [Set.mem_setOf_eq, e] using h
  inv_mem' {a} ha := by
    have h := U.inv_mem ha
    have e : c⁻¹ * a⁻¹ * c = (c⁻¹ * a * c)⁻¹ := by group
    simpa only [Set.mem_setOf_eq, e] using h

private theorem mem_cj {G : Type} [Group G] {c x : G} {U : Subgroup G} : x ∈ cj c U ↔ c⁻¹ * x * c ∈ U := Iff.rfl

private theorem isOpen_cj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (c : G) {U : Subgroup G}
    (hU : IsOpen (U : Set G)) : IsOpen (cj c U : Set G) :=
  hU.preimage (f := fun x => c⁻¹ * x * c) ((continuous_const.mul continuous_id).mul continuous_const)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levLaws :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (S : Finset (Pl K)), (∀ U, Lev U → CO (levOn (n := n) S U) ∧ levOn S U ≤ AdelicGLn.integralFiniteGL K n) ∧
      (∀ U U' : ∀ v : Pl K, Subgroup (Gw n v), Lev U → Lev U' → Lev (fun v => U v ⊓ U' v) ∧ levOn S (fun v => U v ⊓ U' v) = levOn S U ⊓ levOn S U') ∧
      (∀ (k : archCompact K n) (h : FA K n), Commute (arc1 k) (fin1 h)) ∧ Continuous (arc1 : archCompact K n → G1 K n) ∧ CompactSpace (archCompact K n) ∧
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS n w →* FA K n), Function.Injective w → IsEmb w ι → S = im w → ∀ U, Lev U → ∀ g,
        ∃ U', Lev U' ∧ ∀ u ∈ levOn S U', (ι g)⁻¹ * u * ι g ∈ levOn S U := by
  intro K _ _ n S
  have hmem : ∀ (U : ∀ v : Pl K, Subgroup (Gw n v)) (u : FA K n), u ∈ levOn S U ↔ ∀ v, finAt v (finEmb K n u) ∈
      (if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion K) n) := fun _ _ => Iff.rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨ho, hc, hi, -⟩ := UpperTheory.levF_isOpen_isCompact_le_integral K n
      (fun v => if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion K) n) S
      (fun v hv => by simpa only [if_pos hv] using And.intro (hU v).1.2 (hU v).2) (fun v hv => if_neg hv)
    exact ⟨⟨hc, ho⟩, hi⟩
  · intro U U' hU hU'
    refine ⟨fun v => ⟨⟨(hU v).1.1.inter_right (Subgroup.isClosed_of_isOpen _ (hU' v).1.2),
      (hU v).1.2.inter (hU' v).1.2⟩, inf_le_left.trans (hU v).2⟩, ?_⟩
    ext u
    rw [Subgroup.mem_inf, hmem, hmem, hmem]
    constructor
    · intro h
      refine ⟨fun v => ?_, fun v => ?_⟩
      · have h' := h v
        by_cases hv : v ∈ S
        · rw [if_pos hv] at h' ⊢
          exact (Subgroup.mem_inf.1 h').1
        · rw [if_neg hv] at h' ⊢
          exact h'
      · have h' := h v
        by_cases hv : v ∈ S
        · rw [if_pos hv] at h' ⊢
          exact (Subgroup.mem_inf.1 h').2
        · rw [if_neg hv] at h' ⊢
          exact h'
    · rintro ⟨h₁, h₂⟩ v
      have a := h₁ v
      have b := h₂ v
      by_cases hv : v ∈ S
      · rw [if_pos hv] at a b ⊢
        exact Subgroup.mem_inf.2 ⟨a, b⟩
      · rw [if_neg hv] at a b ⊢
        exact a
  · intro k h
    exact (MultiplicityOne.finProj_mul_archProj_comm h _).symm
  · exact continuous_archP.comp continuous_subtype_val
  · have hcl : IsClosed (archCompact K n : Set (archGroup K n)) :=
      (isCompact_maxCompact (K := K) (n := n)).isClosed.preimage continuous_infEmb
    have hg : Continuous fun z : AdelicGLn.AdelicGL K n => archEquiv K n (AdelicGLn.prodEquiv K n z).1 :=
      (archEquiv K n).continuous.comp (continuous_fst.comp (AdelicGLn.prodEquiv K n).continuous)
    refine isCompact_iff_compactSpace.1 (((isCompact_maxCompact (K := K) (n := n)).image hg).of_isClosed_subset hcl ?_)
    intro x hx
    exact ⟨infEmb K n x, hx, by simp [prodEquiv_infEmb]⟩
  · intro r w ι hinj hι hS U hU g
    obtain ⟨-, -, hout, -⟩ := (embEx n w hinj).2 ι hι
    refine ⟨fun v => U v ⊓ cj (GM.cf v (ι g)) (U v), fun v => ?_, fun u hu => ?_⟩
    · have ho := isOpen_cj (GM.cf v (ι g)) (hU v).1.2
      exact ⟨⟨(hU v).1.1.inter_right (Subgroup.isClosed_of_isOpen _ ho), (hU v).1.2.inter ho⟩,
        inf_le_left.trans (hU v).2⟩
    · refine (hmem _ _).2 fun v => ?_
      have hcf : finAt v (finEmb K n ((ι g)⁻¹ * u * ι g)) =
          (GM.cf v (ι g))⁻¹ * finAt v (finEmb K n u) * GM.cf v (ι g) := by
        simp only [map_mul, map_inv, finAt_mul, finAt_inv, GM.cf]
      have hu' := (hmem _ _).1 hu v
      rw [hcf]
      by_cases hv : v ∈ S
      · rw [if_pos hv] at hu' ⊢
        exact mem_cj.1 (Subgroup.mem_inf.1 hu').2
      · rw [if_neg hv] at hu' ⊢
        rw [hout g v (hS ▸ hv)]
        simpa using hu'
