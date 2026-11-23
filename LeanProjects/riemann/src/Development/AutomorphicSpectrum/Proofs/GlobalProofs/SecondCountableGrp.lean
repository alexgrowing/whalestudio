import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open MeasureTheory CompanionTheory.D.gk.admitted
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.admitted

variable {n : ℕ}

def grp {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) ℂ) ∈ G}
  mul_mem' := fun {a b} ha hb => hG.mul_mem _ ha _ hb
  one_mem' := hG.one_mem
  inv_mem' := fun {u} hu => by
    show ((u⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ G
    rw [Matrix.coe_units_inv]
    exact hG.inv_mem _ hu

abbrev toMat {G : Set (Matrix (Fin n) (Fin n) ℂ)} {hG : IsLinRed G} (g : grp hG) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

theorem toMat_mem {G : Set (Matrix (Fin n) (Fin n) ℂ)} {hG : IsLinRed G} (g : grp hG) : toMat g ∈ G := g.2

theorem continuous_toMat {G : Set (Matrix (Fin n) (Fin n) ℂ)} {hG : IsLinRed G} :
    Continuous (toMat : grp hG → Matrix (Fin n) (Fin n) ℂ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem toMat_injective {G : Set (Matrix (Fin n) (Fin n) ℂ)} {hG : IsLinRed G} :
    Function.Injective (toMat : grp hG → Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem exists_elt {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ G) :
    ∃ g : grp hG, toMat g = m :=
  ⟨⟨(hG.isUnit m hm).unit, hm⟩, rfl⟩

def kgrp {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) : Subgroup (grp hG) where
  carrier := {g | toMat g ∈ Matrix.unitaryGroup (Fin n) ℂ}
  mul_mem' := fun {a b} ha hb => (Matrix.unitaryGroup (Fin n) ℂ).mul_mem ha hb
  one_mem' := (Matrix.unitaryGroup (Fin n) ℂ).one_mem
  inv_mem' := fun {u} hu => by
    have h1 : (toMat u)ᴴ * toMat u = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
    have h2 : toMat u⁻¹ = (toMat u)ᴴ := by
      have h3 : toMat u⁻¹ * toMat u = 1 := by
        show (((u⁻¹ * u : grp hG) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
        simp
      have h4 : toMat u * (toMat u)ᴴ = 1 := mul_eq_one_comm.1 h1
      calc toMat u⁻¹ = toMat u⁻¹ * (toMat u * (toMat u)ᴴ) := by rw [h4, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
    show toMat u⁻¹ ∈ Matrix.unitaryGroup (Fin n) ℂ
    rw [h2]
    exact Unitary.star_mem hu

theorem isCompact_maxCpt {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) : IsCompact (maxCpt G) := by
  have hUc : IsCompact (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    have hcl : IsClosed (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
      have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) = {A | Aᴴ * A = 1} := by
        ext A
        exact Matrix.mem_unitaryGroup_iff'
      rw [this]
      exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall (0 : ℂ) 1) hcl ?_
    intro A hA i _ j _
    simpa using entry_norm_bound_of_unitary hA i j
  refine hUc.of_isClosed_subset ?_ Set.inter_subset_right
  refine isClosed_of_closure_subset fun g hg => ?_
  have hgU : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) :=
    closure_minimal Set.inter_subset_right hUc.isClosed hg
  have hu : IsUnit g := IsUnit.of_mul_eq_one _ (Matrix.mem_unitaryGroup_iff.1 hgU)
  exact ⟨hG.closed g hu (closure_mono Set.inter_subset_left hg), hgU⟩

instance compactSpace_kgrp {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) : CompactSpace (kgrp hG) := by
  haveI : CompactSpace (maxCpt G) := isCompact_iff_compactSpace.1 (isCompact_maxCpt hG)
  let ψ : maxCpt G → kgrp hG := fun m =>
    ⟨⟨⟨m.1, m.1ᴴ, Matrix.mem_unitaryGroup_iff.1 m.2.2, Matrix.mem_unitaryGroup_iff'.1 m.2.2⟩, m.2.1⟩, by
      show m.1 ∈ Matrix.unitaryGroup (Fin n) ℂ
      exact m.2.2⟩
  have hψ : Continuous ψ := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩
  refine Function.Surjective.compactSpace (f := ψ) hψ ?_
  rintro ⟨⟨u, hu⟩, hk⟩
  refine ⟨⟨u, hu, hk⟩, ?_⟩
  exact Subtype.ext (Subtype.ext (Units.ext rfl))

instance secondCountable_grp {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) : SecondCountableTopology (grp hG) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  exact TopologicalSpace.Subtype.secondCountableTopology _

section Core

variable {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def homG (hG : IsLinRed G) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn G σ) :
    grp hG →* (H →L[ℂ] H) where
  toFun g := σ (toMat g)
  map_one' := hσ.1.1
  map_mul' a b := hσ.1.2 _ a.2 _ b.2

def stdU (hG : IsLinRed G) {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    grp hG →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := Uᴴ * toMat g * U
  map_one' := by
    have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    show Uᴴ * 1 * U = 1
    rw [Matrix.mul_one, h1]
  map_mul' a b := by
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    show Uᴴ * (toMat a * toMat b) * U = _
    calc Uᴴ * (toMat a * toMat b) * U = Uᴴ * toMat a * (U * Uᴴ) * toMat b * U := by
          rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_stable [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hI : ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ G, ∃ k ∈ maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id)
    (hσ : IsURepOn G σ) (hirr : IsIrredOn G σ) (S : Submodule ℂ H) [FiniteDimensional ℂ S] (hS : IsKStable G σ S)
    (v : H) (hv : v ∈ S) :
    ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧
      ∀ T : H →L[ℂ] H, (∀ k ∈ maxCpt G, ∀ u, T (σ k u) = σ k (T u)) → ∀ y ∈ Y, T y ∈ Y := by
  obtain ⟨U, hU, hiwa⟩ := hI
  letI : MeasurableSpace (kgrp hG) := borel _
  haveI : BorelSpace (kgrp hG) := ⟨rfl⟩
  let μ : Measure (kgrp hG) := (Measure.haar : Measure (kgrp hG)).inv
  have hμ : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure
  have hsc : SecondCountableTopology (kgrp hG) := TopologicalSpace.Subtype.secondCountableTopology _
  have hiso : ∀ g u, ‖homG hG hσ g u‖ = ‖u‖ := fun g u => hσ.2.1 _ g.2 u
  have hc : ∀ u, Continuous fun g => homG hG hσ g u := fun u =>
    (hσ.2.2 u).comp_continuous continuous_toMat fun g => g.2
  have hKm : ∀ k : kgrp hG, toMat k.1 ∈ maxCpt G := fun k => ⟨k.1.2, k.2⟩
  obtain ⟨e, E, he, hfin, hE, hEv⟩ := exists_averaging_operator (kgrp hG) μ H ((homG hG hσ).comp (kgrp hG).subtype)
    (fun k u => hiso k u) (fun u => (hc u).comp continuous_subtype_val) S (fun k u hu => hS _ (hKm k) u hu) v hv
  choose st hst using fun g : grp hG => exists_elt hG (hG.star_mem _ g.2)
  let Tr : Set (grp hG) := {s | (stdU hG hU s).BlockTriangular id}
  have hgood : IsGood st Tr (stdU hG hU) := by
    refine ⟨(continuous_const.matrix_mul continuous_toMat).matrix_mul continuous_const, fun g => ?_,
      Fin.val, Fin.val_injective, fun s hs i j hij => hs hij⟩
    show Uᴴ * toMat (st g) * U = (Uᴴ * toMat g * U)ᴴ
    rw [hst]
    simp [Matrix.mul_assoc]
  have hinj : Function.Injective (stdU hG hU) := by
    intro a b hab
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    have key : ∀ g : grp hG, U * stdU hG hU g * Uᴴ = toMat g := fun g => by
      show U * (Uᴴ * toMat g * U) * Uᴴ = _
      calc U * (Uᴴ * toMat g * U) * Uᴴ = (U * Uᴴ) * toMat g * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    exact toMat_injective ((key a).symm.trans (hab ▸ key b))
  have hKS : ∀ g : grp hG, ∃ k ∈ kgrp hG, ∃ s ∈ Tr, g = k * s := by
    intro g
    obtain ⟨k, hk, s, hs, hg, ht⟩ := hiwa (toMat g) g.2
    obtain ⟨k', rfl⟩ := exists_elt hG hk.1
    obtain ⟨s', rfl⟩ := exists_elt hG hs
    exact ⟨k', hk.2, s', ht, toMat_injective hg⟩
  have hPI : ∀ g : Fin (Module.finrank ℂ S ^ 2 + 1) → grp hG, stdPoly E (fun i => homG hG hσ (g i)) = 0 := fun g =>
    transfer_holds (grp hG) (kgrp hG) μ st Tr (Fin n) (stdU hG hU) hgood hinj e he _ g
      (fun ι _ _ ρ hρ E' hE' => goodPI_of small_irreducible_representation (grp hG) (kgrp hG) μ st Tr hKS e _ _ he hfin
        (Nat.lt_succ_self _) ι ρ hρ E' hE' g)
      H (homG hG hσ) hc E hE
  obtain ⟨hfd, -⟩ := finite_rank_of_irreducible_unitary (grp hG) H (homG hG hσ) hiso (fun S' hcl hS' => hirr S' hcl fun g hg u hu => by
    obtain ⟨g, rfl⟩ := exists_elt hG hg
    exact hS' g u hu) E _ hPI
  refine ⟨_, hfd, ⟨v, hEv⟩, ?_⟩
  rintro T hT _ ⟨u, rfl⟩
  refine ⟨T u, ?_⟩
  show E (T u) = T (E u)
  rw [hE, hE, ← T.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show e k • σ (toMat k.1) (T u) = T (e k • σ (toMat k.1) u)
    rw [map_smul, hT _ (hKm k)]
  · exact (he.smul ((hc u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end Core

theorem isAdmOn_of_iwasawa {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hI : ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ G, ∃ k ∈ maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id)
    (hU : IsURepOn G π) (hirr : IsIrredOn G π) : IsAdmOn G π := by
  refine ⟨hU.1, hU.2.2, fun k hk => hU.2.1 k hk.1, ?_⟩
  intro S hfd hS _
  haveI := hfd
  let b := Module.finBasis ℂ S
  choose Y hYfd hvY hY using fun i => exists_stable hG hI hU hirr S hS (b i) (b i).2
  haveI := hYfd
  have hsup : FiniteDimensional ℂ (⨆ i, Y i : Submodule ℂ H) := Submodule.finiteDimensional_iSup Y
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, Y i) (sSup_le ?_)
  rintro _ ⟨Θ₀, rfl, hΘ⟩
  let Θ : S →ₗ[ℂ] H := Θ₀.domRestrict S
  let T : H →L[ℂ] H := (LinearMap.toContinuousLinearMap Θ).comp S.orthogonalProjectionOnto
  have hT : ∀ k ∈ maxCpt G, ∀ u, T (π k u) = π k (T u) := by
    intro k hk u
    have hkG := hk.1
    have hk1 : k * k.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    have hks : k.conjTranspose ∈ maxCpt G := ⟨hG.star_mem _ hkG, Unitary.star_mem hk.2⟩
    have hiso : ∀ x y, ⟪π k x, π k y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y =>
      (LinearIsometry.mk (π k : H →ₗ[ℂ] H) (hU.2.1 k hkG)).inner_map_map x y
    have hP : ((S.orthogonalProjectionOnto (π k u) : S) : H) = π k (S.orthogonalProjectionOnto u : S) := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.orthogonalProjectionOnto u).2) ?_
      intro w hw
      have hw' : π k (π k.conjTranspose w) = w := by
        rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ hkG _ hks.1, hk1, hU.1.1]
        rfl
      rw [← hw', ← map_sub, hiso]
      exact S.starProjection_inner_eq_zero u _ (hS _ hks w hw)
    show Θ₀ ((S.orthogonalProjectionOnto (π k u) : S) : H) = π k (Θ₀ (S.orthogonalProjectionOnto u : S))
    rw [hP]
    exact hΘ k hk _ (S.orthogonalProjectionOnto u).2
  rintro _ ⟨v, hv, rfl⟩
  have hv2 : v = ∑ i, b.repr ⟨v, hv⟩ i • (b i : H) := by
    calc v = ((∑ i, b.repr ⟨v, hv⟩ i • b i : S) : H) := by rw [b.sum_repr]
      _ = _ := (map_sum S.subtype _ _).trans (Finset.sum_congr rfl fun i _ => rfl)
  show Θ₀ v ∈ _
  rw [hv2, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i ?_)
  have := hY i T hT _ (hvY i)
  simpa [T, Θ] using this

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.admitted

end
