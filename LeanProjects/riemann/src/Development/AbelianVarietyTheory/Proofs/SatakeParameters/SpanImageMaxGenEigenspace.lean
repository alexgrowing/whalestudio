import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigAtInfRangeNeBotOfMemSpan

open Formalism.L2.Col

namespace GlobalTheory.ScalarExtEig

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
  {σ : K →+* ℂ} (j : V →ₛₗ[σ] W)

theorem span_image_span (S : Set V) :
    Submodule.span ℂ (j '' (Submodule.span K S : Set V)) = Submodule.span ℂ (j '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem span_image_mono {U U' : Submodule K V} (h : U ≤ U') :
    Submodule.span ℂ (j '' (U : Set V)) ≤ Submodule.span ℂ (j '' (U' : Set V)) :=
  Submodule.span_mono (Set.image_mono h)

theorem span_image_iSup {κ : Sort*} (U : κ → Submodule K V) :
    Submodule.span ℂ (j '' ((⨆ i, U i : Submodule K V) : Set V))
      = ⨆ i, Submodule.span ℂ (j '' (U i : Set V)) := by
  rw [Submodule.iSup_eq_span, span_image_span, Set.image_iUnion, Submodule.span_iUnion]

theorem span_image_bot : Submodule.span ℂ (j '' ((⊥ : Submodule K V) : Set V)) = ⊥ := by
  simp

theorem span_image_sup (U U' : Submodule K V) :
    Submodule.span ℂ (j '' ((U ⊔ U' : Submodule K V) : Set V))
      = Submodule.span ℂ (j '' (U : Set V)) ⊔ Submodule.span ℂ (j '' (U' : Set V)) := by
  rw [← Submodule.span_eq U, ← Submodule.span_eq U', ← Submodule.span_union, span_image_span,
    Set.image_union, Submodule.span_union, span_image_span, span_image_span]

variable {ι : Type} [Finite ι] (b : Module.Basis ι K V)

include b in
theorem finiteDimensional_of_basis : FiniteDimensional K V := Module.Finite.of_basis b

theorem span_image_top (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) :
    Submodule.span ℂ (j '' ((⊤ : Submodule K V) : Set V)) = ⊤ := by
  rw [eq_top_iff, ← hsp]
  exact Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨b k, Submodule.mem_top, rfl⟩)

theorem finiteDimensional_W (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) : FiniteDimensional ℂ W :=
  Module.Finite.of_basis (Module.Basis.mk hli hsp.ge)

theorem finrank_W (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) :
    Module.finrank ℂ W = Module.finrank K V := by
  haveI := Fintype.ofFinite ι
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge), Module.finrank_eq_card_basis b]

theorem linearIndependent_comp (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤)
    {κ : Type} {u : κ → V} (hu : LinearIndependent K u) :
    LinearIndependent ℂ (fun k => j (u k)) := by
  haveI := finiteDimensional_of_basis b
  have hs : LinearIndepOn K id (Set.range u) := hu.linearIndepOn_id
  let B := Module.Basis.extend hs
  haveI : Fintype (hs.extend (Set.subset_univ _)) := Fintype.ofFinite _
  have hB : LinearIndependent ℂ (fun l => j (B l)) := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
    · rw [← hsp]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      have h1 : j (b k) ∈ Submodule.span ℂ (j '' (Submodule.span K (Set.range B) : Set V)) := by
        rw [B.span_eq]; exact Submodule.subset_span ⟨b k, Submodule.mem_top, rfl⟩
      rw [span_image_span, ← Set.range_comp] at h1
      exact h1
    · rw [finrank_W j b hli hsp, Module.finrank_eq_card_basis B]
  let f : κ → hs.extend (Set.subset_univ _) := fun k => ⟨u k, Module.Basis.subset_extend hs ⟨k, rfl⟩⟩
  have hf : Function.Injective f := fun a c h => hu.injective (congrArg Subtype.val h)
  have := hB.comp f hf
  convert this using 1
  funext k
  simp [B, f, Module.Basis.coe_extend]

theorem finrank_span_image (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (U : Submodule K V) :
    Module.finrank ℂ (Submodule.span ℂ (j '' (U : Set V))) = Module.finrank K U := by
  haveI := finiteDimensional_of_basis b
  let bU := Module.finBasis K U
  have hu : LinearIndependent K (fun i => (bU i : V)) :=
    bU.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hspan : Submodule.span K (Set.range fun i => (bU i : V)) = U := by
    have : (Set.range fun i => (bU i : V)) = U.subtype '' Set.range bU := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bU.span_eq, Submodule.map_subtype_top]
  have h2 : Submodule.span ℂ (j '' (U : Set V))
      = Submodule.span ℂ (Set.range fun i => j (bU i : V)) := by
    conv_lhs => rw [← hspan]
    rw [span_image_span, ← Set.range_comp]; rfl
  rw [h2, finrank_span_eq_card (linearIndependent_comp j b hli hsp hu), Fintype.card_fin]

theorem span_image_inf (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (U U' : Submodule K V) :
    Submodule.span ℂ (j '' ((U ⊓ U' : Submodule K V) : Set V))
      = Submodule.span ℂ (j '' (U : Set V)) ⊓ Submodule.span ℂ (j '' (U' : Set V)) := by
  haveI := finiteDimensional_of_basis b
  haveI := finiteDimensional_W j b hli hsp
  refine Submodule.eq_of_le_of_finrank_eq
    (le_inf (span_image_mono j inf_le_left) (span_image_mono j inf_le_right)) ?_
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U U'
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℂ (j '' (U : Set V)))
    (Submodule.span ℂ (j '' (U' : Set V)))
  rw [← span_image_sup] at h2
  simp only [finrank_span_image j b hli hsp] at h2 ⊢
  omega

theorem span_image_finset_inf (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) {I : Type} (U : I → Submodule K V)
    (F : Finset I) :
    Submodule.span ℂ (j '' ((F.inf U : Submodule K V) : Set V))
      = F.inf (fun i => Submodule.span ℂ (j '' (U i : Set V))) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.inf_empty]; exact span_image_top j b hsp
  | insert i F hi ih => rw [Finset.inf_insert, Finset.inf_insert, span_image_inf j b hli hsp, ih]

theorem exists_finset_inf_eq_iInf {I : Type} [FiniteDimensional K V] (U : I → Submodule K V) :
    ∃ F : Finset I, F.inf U = ⨅ i, U i := by
  classical
  have hex : ∃ n, ∃ F : Finset I, Module.finrank K ((F.inf U : Submodule K V)) = n := ⟨_, ∅, rfl⟩
  obtain ⟨F, hF⟩ := Nat.find_spec hex
  refine ⟨F, le_antisymm (le_iInf fun i => ?_) (Finset.le_inf fun i _ => iInf_le U i)⟩
  have hle : (insert i F).inf U ≤ F.inf U := Finset.inf_mono (Finset.subset_insert i F)
  have hmin : Nat.find hex ≤ Module.finrank K (((insert i F).inf U : Submodule K V)) := Nat.find_min' hex ⟨_, rfl⟩
  have heq : (insert i F).inf U = F.inf U := Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [← heq]
  exact Finset.inf_le (Finset.mem_insert_self i F)

theorem span_image_iInf (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) {I : Type} (U : I → Submodule K V) :
    Submodule.span ℂ (j '' ((⨅ i, U i : Submodule K V) : Set V))
      = ⨅ i, Submodule.span ℂ (j '' (U i : Set V)) := by
  haveI := finiteDimensional_of_basis b
  obtain ⟨F, hF⟩ := exists_finset_inf_eq_iInf U
  refine le_antisymm (le_iInf fun i => span_image_mono j (iInf_le U i)) ?_
  rw [← hF, span_image_finset_inf j b hli hsp]
  exact Finset.le_inf fun i _ => iInf_le _ i

theorem span_image_ker (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (f : Module.End K V)
    (fC : Module.End ℂ W) (hf : ∀ v, j (f v) = fC (j v)) :
    Submodule.span ℂ (j '' (LinearMap.ker f : Set V)) = LinearMap.ker fC := by
  haveI := finiteDimensional_of_basis b
  haveI := finiteDimensional_W j b hli hsp
  have hle : Submodule.span ℂ (j '' (LinearMap.ker f : Set V)) ≤ LinearMap.ker fC := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hv ⊢
    rw [← hf, hv, map_zero]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hr : LinearMap.range fC = Submodule.span ℂ (j '' (LinearMap.range f : Set V)) := by
    rw [LinearMap.range_eq_map, ← span_image_top j b hsp, Submodule.map_span, LinearMap.range_eq_map,
      Submodule.map_coe, Set.image_image, Set.image_image]
    simp_rw [hf]
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker fC
  rw [hr, finrank_span_image j b hli hsp, finrank_W j b hli hsp] at h2
  rw [finrank_span_image j b hli hsp]
  omega

theorem span_image_maxGenEigenspace (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (f : Module.End K V)
    (fC : Module.End ℂ W) (hf : ∀ v, j (f v) = fC (j v)) (a : K) :
    Submodule.span ℂ (j '' (f.maxGenEigenspace a : Set V)) = fC.maxGenEigenspace (σ a) := by
  haveI := finiteDimensional_of_basis b
  haveI := finiteDimensional_W j b hli hsp
  have key : ∀ (k : ℕ) (v : V),
      ((fC - σ a • (1 : Module.End ℂ W)) ^ k) (j v) = j (((f - a • (1 : Module.End K V)) ^ k) v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih]
      congr 1
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        map_smulₛₗ, hf]
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat,
    Module.End.genEigenspace_nat, finrank_W j b hli hsp]
  exact span_image_ker j b hli hsp _ _ (fun v => (key _ v).symm)

end GlobalTheory.ScalarExtEig

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open GlobalTheory.ScalarExtEig in

theorem span_image_eigAt_of_basis : ∀ {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) (op : I → Module.End K V) (opC : I → Module.End ℂ W), LinearIndependent ℂ (fun k => j (b k)) → Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤ → (∀ i x, j (op i x) = opC i (j x)) → (∀ s : I → K, Submodule.span ℂ (j '' (Formalism.L2.Col.eigAt op s : Set V)) = Formalism.L2.Col.eigAt opC (fun i => σ (s i))) ∧ (∀ Q : (I → K) → Prop, Submodule.span ℂ (j '' (Formalism.L2.Col.eigSum op Q : Set V)) = Formalism.L2.Col.eigSum opC (fun x => ∃ s, Q s ∧ x = fun i => σ (s i))) ∧ (Formalism.L2.Col.PairComm op → Formalism.L2.Col.SplitOver op → ∀ x, Formalism.L2.Col.Occurs opC x → ∃ s, Formalism.L2.Col.Occurs op s ∧ x = fun i => σ (s i)) := by
  intro K V W I ι _ _ _ _ _ _ σ j b op opC hli hsp hop
  have h1 : ∀ s : I → K, Submodule.span ℂ (j '' (eigAt op s : Set V))
      = eigAt opC (fun i => σ (s i)) := by
    intro s
    rw [eigAt, span_image_iInf j b hli hsp, eigAt]
    exact iInf_congr fun i => span_image_maxGenEigenspace j b hli hsp (op i) (opC i) (hop i) (s i)
  refine ⟨h1, fun Q => ?_, fun hc hs x hx => ?_⟩
  · unfold eigSum
    simp_rw [span_image_iSup, h1]
    apply le_antisymm
    · exact iSup₂_le fun s hs => le_iSup₂_of_le (f := fun (y : I → ℂ) (_ : ∃ s, Q s ∧ y = fun i => σ (s i)) => eigAt opC y) _ ⟨s, hs, rfl⟩ le_rfl
    · refine iSup₂_le fun y hy => ?_
      obtain ⟨s, hs, rfl⟩ := hy
      exact le_iSup₂_of_le (f := fun (s : I → K) (_ : Q s) => eigAt opC (fun i => σ (s i))) s hs le_rfl
  · by_contra hno
    push_neg at hno
    have hcC : PairComm opC := by
      intro i k
      show opC i * opC k = opC k * opC i
      refine LinearMap.ext_on_range hsp fun m => ?_
      have := congrArg (fun g => j (g (b m))) (hc i k).eq
      simpa [Module.End.mul_apply, hop] using this
    haveI := finiteDimensional_of_basis b
    have htop : (⊤ : Submodule ℂ W) ≤ ⨆ (y : I → ℂ) (_ : y ≠ x), eigAt opC y := by
      rw [← span_image_top j b hsp, ← iSup_eigAt_eq_top hc hs, span_image_iSup]
      refine iSup_le fun s => ?_
      by_cases hs0 : Occurs op s
      · rw [h1]
        exact le_iSup₂_of_le (f := fun (y : I → ℂ) (_ : y ≠ x) => eigAt opC y) _ (hno s hs0).symm le_rfl
      · rw [Occurs, not_not] at hs0
        rw [hs0, span_image_bot]
        exact bot_le
    exact hx (disjoint_top.1 (((iSupIndep_eigAt hcC) x).mono_right htop))

end GlobalTheory
