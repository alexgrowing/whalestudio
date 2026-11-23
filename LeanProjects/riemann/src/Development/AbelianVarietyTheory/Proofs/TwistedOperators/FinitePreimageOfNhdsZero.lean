import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix Topology

noncomputable section

namespace GlobalTheory.TrFinite

theorem finite_preimage_of_nhds_zero {A G : Type} [AddCommGroup A] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (f : A →+ G) {U : Set G} (hU : U ∈ 𝓝 (0 : G)) (h : ∀ x, f x ∈ U → x = 0)
    {K : Set G} (hK : IsCompact K) : {x | f x ∈ K}.Finite := by
  obtain ⟨V, hV0, hV⟩ : ∃ V ∈ 𝓝 (0 : G), ∀ a ∈ V, ∀ b ∈ V, a - b ∈ U := by
    have ht : Tendsto (fun p : G × G => p.1 - p.2) (𝓝 ((0 : G), (0 : G))) (𝓝 0) := by
      simpa using (continuous_sub.tendsto ((0 : G), (0 : G)))
    have h2 := ht hU
    rw [nhds_prod_eq] at h2
    obtain ⟨V1, h1, V2, h2', hs⟩ := Filter.mem_prod_iff.1 h2
    exact ⟨V1 ∩ V2, inter_mem h1 h2', fun a ha b hb => @hs (a, b) ⟨ha.1, hb.2⟩⟩
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => (fun y => y - k) ⁻¹' V) (fun k _ => by
    have hc : Continuous fun y : G => y - k := continuous_id.sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV0))
  have hsub : {x | f x ∈ K} ⊆ ⋃ k ∈ t, {x | f x - k ∈ V} := fun x hx => by
    have := ht hx
    simp only [Set.mem_iUnion, Set.mem_preimage] at this ⊢
    exact this
  refine Set.Finite.subset (Set.Finite.biUnion t.finite_toSet fun k _ => ?_) hsub
  refine Set.Subsingleton.finite fun x hx y hy => ?_
  have hm : f (x - y) ∈ U := by
    have := hV _ hx _ hy
    rwa [sub_sub_sub_cancel_right, ← map_sub] at this
  exact sub_eq_zero.1 (h _ hm)

theorem continuous_coeff_charpoly {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

end GlobalTheory.TrFinite

namespace GlobalTheory.TrFinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem charpoly_conj_ratEmb (γ : GRat σ J) (x : GAd σ J) :
    (((matHom (AF F) σ J (x⁻¹ * ratEmb σ J γ * x) : GL (Fin n) (AF F ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).charpoly = γ.1.1.charpoly.map (inclR (AF F)) := by
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']
  exact Matrix.charpoly_map _ _

theorem finite_ratEmb_mem {K : Set (GAd σ J)} (hK : IsCompact K) : {γ : GRat σ J | ratEmb σ J γ ∈ K}.Finite := by
  haveI : DiscreteTopology (ratPts σ J) := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  have hcl : IsClosed (ratPts σ J : Set (GAd σ J)) := Subgroup.isClosed_of_discrete
  have hfin : ((Subtype.val : ratPts σ J → GAd σ J) ⁻¹' K).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK).finite_of_discrete
  let g : GRat σ J → ratPts σ J := fun γ => ⟨ratEmb σ J γ, range_ratEmb σ J ▸ ⟨γ, rfl⟩⟩
  have hg : Function.Injective g := fun a b h => ratEmb_injective σ J (congrArg Subtype.val h)
  exact Set.Finite.preimage (f := g) hg.injOn hfin

theorem finite_charpoly_and_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (GAd σ J)), IsCompact C →
    {Q : E[X] | ∃ γ : GRat σ J, γ.1.1.charpoly = Q ∧ ∃ x, x⁻¹ * ratEmb σ J γ * x ∈ C}.Finite ∧
      ∀ x, {γ : GRat σ J | x⁻¹ * ratEmb σ J γ * x ∈ C}.Finite := by
  intro F E _ _ _ _ _ σ _ n J C hC
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  refine ⟨?_, fun x => ?_⟩
  ·
    let c : Fin (n + 1) → GAd σ J → AF F ⊗[F] E := fun i g =>
      (((matHom (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).charpoly.coeff i
    have hc : ∀ i, Continuous (c i) := fun i =>
      (continuous_coeff_charpoly n i).comp (Units.continuous_val.comp continuous_subtype_val)
    obtain ⟨U, hU, hU0⟩ := GlobalTheory.RationalDiscrete.exists_nhds_zero_inclR (F := F) (E := E)
    let T : Fin (n + 1) → Set E := fun i => {e | (inclR (AF F)).toAddMonoidHom e ∈ c i '' C}
    have hT : ∀ i, (T i).Finite := fun i =>
      finite_preimage_of_nhds_zero _ hU hU0 (hC.image (hc i))
    let S := {Q : E[X] | ∃ γ : GRat σ J, γ.1.1.charpoly = Q ∧ ∃ x, x⁻¹ * ratEmb σ J γ * x ∈ C}
    let φ : E[X] → Fin (n + 1) → E := fun Q i => Q.coeff i
    have hdeg : ∀ Q ∈ S, Q.natDegree = n := by
      rintro Q ⟨γ, rfl, -⟩
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hinj : Set.InjOn φ S := fun P hP Q hQ h => by
      ext i
      by_cases hi : i ≤ n
      · exact congrFun h ⟨i, Nat.lt_succ_of_le hi⟩
      · push_neg at hi
        rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg P hP]; exact hi),
          coeff_eq_zero_of_natDegree_lt (by rw [hdeg Q hQ]; exact hi)]
    have himg : φ '' S ⊆ Set.pi Set.univ T := by
      rintro _ ⟨Q, ⟨γ, rfl, x, hx⟩, rfl⟩ i -
      refine ⟨_, hx, ?_⟩
      change (((matHom (AF F) σ J (x⁻¹ * ratEmb σ J γ * x) : GL (Fin n) (AF F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).charpoly.coeff i = inclR (AF F) (γ.1.1.charpoly.coeff i)
      rw [charpoly_conj_ratEmb, coeff_map]
    exact Set.Finite.of_finite_image ((Set.Finite.pi hT).subset himg) hinj
  · have hK : IsCompact ((fun g => x * g * x⁻¹) '' C) :=
      hC.image ((continuous_const.mul continuous_id).mul continuous_const)
    refine (finite_ratEmb_mem σ J hK).subset fun γ hγ => ⟨_, hγ, ?_⟩
    change x * (x⁻¹ * ratEmb σ J γ * x) * x⁻¹ = ratEmb σ J γ
    group

end GlobalTheory.TrFinite
