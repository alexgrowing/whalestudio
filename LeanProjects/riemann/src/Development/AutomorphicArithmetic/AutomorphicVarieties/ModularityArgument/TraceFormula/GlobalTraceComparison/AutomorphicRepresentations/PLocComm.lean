import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host Formalism.UG Formalism.BasicNotions

private theorem lv_commute {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (H : Subgroup G) (hH : IsOpen (H : Set G)) (f : G → ℂ)
    (hf : HasCompactSupport f) (T : Module.End ℂ V) (hT : ∀ a, Commute T (ρ a)) : Commute T (Lv ρ H f) := by
  have hs := GlobalTheory.TwTrLevel.finite_supp H hH f hf
  have hsupp : (Function.support fun q : G ⧸ H =>
      f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))).Finite :=
    hs.subset fun q hq h0 => hq (by simp [h0])
  unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.Lv levOp
  rw [finsum_eq_sum_of_support_subset _ (s := hsupp.toFinset) (by simp)]
  refine Commute.smul_right (Commute.sum_right _ _ _ fun q _ => Commute.smul_right ?_ _) _
  rw [LinearMap.comp_id]
  exact hT _

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.locComm_pf :
    SlotBasic → LevTop → LocComm := by
  intro hSF _ E _ _ _ n S Z N hSec _ hG i hi f hf
  obtain ⟨-, -, hloc, hind, -⟩ := hSF E n S hSec
  have hmem : ∀ c, c ∈ Lev S N ↔ ∀ k, Sl S k → qw n k.1 k.2 c ∈ N k.1 := by
    intro c
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
  have hjw : ∀ a ∈ N i.1, jw n i.1 i.2 a ∈ Lev S N := by
    intro a ha
    refine (hmem _).2 fun k hk => ?_
    by_cases h : i = k
    · subst h
      rw [(hloc i.1 i.2).2.2.1]
      exact ha
    · rw [hind i k hi hk h a]
      exact one_mem _
  have hopen := (hG i.1).1
  refine ⟨fun y hy => ?_, fun k hk hik g hg => ?_⟩
  · have hy' := (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ y).1 hy
    have h1 : y ∈ fixed (rw' n i.1 i.2) (N i.1) :=
      (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ y).2 fun a ha => hy' _ (hjw a ha)
    refine ⟨h1, (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ _).2 fun c hc => ?_⟩
    have ha : qw n i.1 i.2 c ∈ N i.1 := (hmem c).1 hc i hi
    obtain ⟨c', hcc⟩ : ∃ c', c' = (jw n i.1 i.2 (qw n i.1 i.2 c))⁻¹ * c := ⟨_, rfl⟩
    have hc' : c' ∈ Lev S N := hcc ▸ mul_mem (inv_mem (hjw _ ha)) hc
    have hq : qw n i.1 i.2 c' = 1 := by
      rw [hcc, map_mul, map_inv, (hloc i.1 i.2).2.2.1, inv_mul_cancel]
    have hc2 : c = jw n i.1 i.2 (qw n i.1 i.2 c) * c' := by
      rw [hcc, mul_inv_cancel_left]
    have hL : Commute (finRep E n c') (Lw N i.1 i.2 f) :=
      lv_commute (rw' n i.1 i.2) (N i.1) hopen f hf.1 _ fun a =>
        (((hloc i.1 i.2).2.2.2 a c' hq).map (finRep E n)).symm
    have hfix : Lw N i.1 i.2 f y ∈ fixed (rw' n i.1 i.2) (N i.1) :=
      GlobalTheory.TwTrLevel.levOp_mem_fixed (rw' n i.1 i.2) (MonoidHom.id _) (fun _ => rfl) LinearMap.id
        (fun _ => rfl) (N i.1) (N i.1) hopen (fun _ h => h) f hf y h1
    have e : finRep E n c' (Lw N i.1 i.2 f y) = Lw N i.1 i.2 f y := by
      have h2 := LinearMap.congr_fun hL.eq y
      rw [Module.End.mul_apply, Module.End.mul_apply, hy' c' hc'] at h2
      exact h2
    have h3 := (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ _).1 hfix _ ha
    rw [hc2, map_mul, Module.End.mul_apply, e]
    exact h3
  · have hrr : ∀ a b, Commute (rw' n i.1 i.2 a) (rw' n k.1 k.2 b) := fun a b =>
      (((hloc k.1 k.2).2.2.2 b (jw n i.1 i.2 a) (hind i k hi hk hik a)).map (finRep E n)).symm
    exact lv_commute (rw' n k.1 k.2) (N k.1) (hG k.1).1 g hg.1 _ fun b =>
      (lv_commute (rw' n i.1 i.2) (N i.1) hopen f hf.1 _ fun a => (hrr a b).symm).symm
