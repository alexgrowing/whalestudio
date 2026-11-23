import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEvA

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport

variable {D : D7}

open Classical in

theorem exists_int_off {K : Set (Af D.host.F)} (hK : IsCompact K) :
    ∃ T : Finset (Pl D), ∀ z ∈ K, ∀ v ∉ T, z v ∈ v.adicCompletionIntegers D.host.F := by
  classical
  let O : Finset (Pl D) → Set (Af D.host.F) :=
    fun T => {z | ∀ v, v ∉ T → z v ∈ (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F))}
  have hO : ∀ T, IsOpen (O T) := fun T =>
    RestrictedProduct.isOpen_forall_imp_mem (R := fun v : Pl D => v.adicCompletion D.host.F)
      (A := fun v => (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F)))
      (fun v => Valued.isOpen_valuationSubring _)
  have hcov : K ⊆ ⋃ T, O T := fun z _ => Set.mem_iUnion.2
    ⟨(Filter.eventually_cofinite.1 z.2).toFinset, fun v hv => by
      by_contra h
      exact hv ((Filter.eventually_cofinite.1 z.2).mem_toFinset.2 h)⟩
  obtain ⟨T, hT⟩ := hK.elim_directed_cover O hO hcov fun T T' =>
    ⟨T ∪ T', fun z hz v hv => hz v fun h => hv (Finset.mem_union_left _ h),
      fun z hz v hv => hz v fun h => hv (Finset.mem_union_right _ h)⟩
  exact ⟨T, fun z hz v hv => hT hz v hv⟩

def sPart {a b : ℕ} (S : Finset (Pl D)) (y : Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) :
    Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i j => algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (indS S) * y i j

open Classical in
set_option maxHeartbeats 800000 in

theorem fin_good {a b : ℕ} (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ y, g y =
      if (∀ v ∉ S, ∀ i j, projV v y i j ∈ intLoc D.host.F D.host.E v)
      then g (sPart S y) else 0 := by
  classical
  obtain ⟨hlc, hcs⟩ := hg
  let B := Module.finBasis D.host.F D.host.E
  have hT1 : ∀ (i : Fin a) (j : Fin b) (k : Fin (Module.finrank D.host.F D.host.E)), ∃ T : Finset (Pl D),
      ∀ y ∈ tsupport g, ∀ v ∉ T, crd B (Af D.host.F) (y i j) k v ∈ v.adicCompletionIntegers D.host.F := by
    intro i j k
    have hc : Continuous fun y : Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E => y i j :=
      (continuous_apply j).comp (continuous_apply i)
    obtain ⟨T, hT⟩ := exists_int_off (D := D) (hcs.isCompact.image ((continuous_crd B (Af D.host.F) k).comp hc))
    exact ⟨T, fun y hy v hv => hT _ ⟨y, hy, rfl⟩ v hv⟩
  choose T1 hT1 using hT1
  have hU := invariant_mem_nhds hlc hcs
  let Lc : (Fin a → Fin b → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F) →
      (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af D.host.F) ⊗ₜ[D.host.F] B k)
  have hL : Continuous Lc := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk continuous_const)
  have hL0 : Lc (fun _ _ _ => 0) = 0 := by
    funext x i
    simp [Lc]
  have hp : Lc ⁻¹' {u | ∀ x, g (x + u) = g x} ∈ 𝓝 (fun _ => fun _ => fun _ => (0 : Af D.host.F)) :=
    hL.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hU)
  obtain ⟨W1, hW1, h1⟩ := exists_nhds_of_pi hp
  obtain ⟨W2, hW2, h2⟩ := exists_nhds_of_pi hW1
  obtain ⟨W, hW, h3⟩ := exists_nhds_of_pi hW2
  obtain ⟨T2, P, hPO, hPT, hsub⟩ := exists_box_subset hW
  have hinv : ∀ x u, (∀ i j k v, crd B (Af D.host.F) (u i j) k v ∈ P v) → g (x + u) = g x := by
    intro x u hu
    have hu' : u = Lc fun i j k => crd B (Af D.host.F) (u i j) k := by
      funext i j
      exact eq_sum_crd B (Af D.host.F) (u i j)
    rw [hu']
    exact h1 _ (fun i => h2 _ fun j => h3 _ fun k => hsub (hu i j k)) x
  have hbad := Filter.eventually_cofinite.1 (GlobalTheory.AdelicU.Cofinite.eventually_mem_intLoc_iff_repr B)
  refine ⟨(Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => Finset.univ.biUnion fun k => T1 i j k) ∪ T2 ∪
    hbad.toFinset, fun S hS y => ?_⟩
  have hS1 : ∀ i j k, T1 i j k ⊆ S := fun i j k v hv => hS (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
      Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hv⟩⟩⟩)))
  have hS2 : T2 ⊆ S := fun v hv => hS (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
  have hS3 : ∀ v ∉ S, ∀ z : Fv D.host.F v ⊗[D.host.F] D.host.E, z ∈ intLoc D.host.F D.host.E v ↔
      ∀ k, crd B (Fv D.host.F v) z k ∈ v.adicCompletionIntegers D.host.F := by
    intro v hv
    have h' : v ∉ hbad.toFinset := fun h => hv (hS (Finset.mem_union_right _ h))
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at h'
    exact h'
  have hcrd : ∀ z k, crd B (Af D.host.F) (z - algebraMap (Af D.host.F) _ (indS S) * z) k =
      crd B (Af D.host.F) z k - indS S * crd B (Af D.host.F) z k := by
    intro z k
    simp only [crd, ← Algebra.smul_def, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  split_ifs with h
  · calc g y = g (sPart S y + (y - sPart S y)) := by rw [add_sub_cancel]
      _ = g (sPart S y) := hinv _ _ fun i j k v => ?_
    have e1 : crd B (Af D.host.F) ((y - sPart S y) i j) k v =
        crd B (Af D.host.F) (y i j) k v - indS S v * crd B (Af D.host.F) (y i j) k v := by
      rw [Pi.sub_apply, Pi.sub_apply, sPart, hcrd]
      rfl
    rw [e1, indS_apply]
    by_cases hv : v ∈ S
    · rw [if_pos hv, one_mul, sub_self]
      exact zero_mem _
    · rw [if_neg hv, zero_mul, sub_zero, hPT v fun h' => hv (hS2 h'), mem_intSub, ← crd_projV]
      exact (hS3 v hv _).1 (h v hv i j) k
  · push Not at h
    obtain ⟨v, hv, i, j, hij⟩ := h
    obtain ⟨k, hk⟩ : ∃ k, crd B (Fv D.host.F v) (projV v y i j) k ∉ v.adicCompletionIntegers D.host.F := by
      by_contra hc
      push Not at hc
      exact hij ((hS3 v hv _).2 hc)
    rw [crd_projV] at hk
    refine image_eq_zero_of_notMem_tsupport fun hy => hk ?_
    exact hT1 i j k y hy v fun h' => hv (hS1 i j k h')

end PositivityTheory.Rg.Rsw.L.LGoodEv

end
