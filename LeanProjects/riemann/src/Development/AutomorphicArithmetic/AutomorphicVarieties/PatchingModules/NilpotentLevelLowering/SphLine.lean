import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SphComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcSumEqOfMk
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem sphLine_eig {T V : Type} [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V) [FiniteDimensional ℂ U]
    (hU : U ≠ ⊥) (θ : T → Module.End ℂ V) (hθ : ∀ t, ∀ v ∈ U, θ t v ∈ U)
    (hc : ∀ s t, ∀ v ∈ U, θ s (θ t v) = θ t (θ s v)) :
    ∃ w ∈ U, w ≠ 0 ∧ ∀ t, ∃ c : ℂ, θ t w = c • w := by
  obtain ⟨S, ⟨hS0, hS⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ U)).has_min
    {S | S ≠ ⊥ ∧ ∀ t, ∀ v ∈ S, (θ t).restrict (hθ t) v ∈ S}
    ⟨⊤, by
      haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU
      exact top_ne_bot, fun _ _ _ => trivial⟩
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
  have key : ∀ t, ∃ c : ℂ, ∀ v ∈ S, (θ t).restrict (hθ t) v = c • v := fun t => by
    obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (((θ t).restrict (hθ t)).restrict (hS t))
    obtain ⟨w, hw⟩ := hc'.exists_hasEigenvector
    have hw1 : (θ t).restrict (hθ t) w = c • (w : U) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨c, fun v hv => ?_⟩
    have h1 : S ⊓ Module.End.eigenspace ((θ t).restrict (hθ t)) c = S := by
      by_contra hne
      refine hmin _ ⟨?_, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
      · exact (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩,
          fun h => hw.2 (Subtype.ext h)⟩
      · rintro s x ⟨hx, hx'⟩
        refine ⟨hS s x hx, Module.End.mem_eigenspace_iff.2 (Subtype.ext ?_)⟩
        have h2 : θ t x = c • (x : V) := congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 hx')
        change θ t (θ s x) = c • θ s x
        rw [hc t s x x.2, h2, map_smul]
    rw [← h1] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS0
  refine ⟨v, v.2, fun h => hv0 (Subtype.ext h), fun t => ?_⟩
  obtain ⟨c, hc⟩ := key t
  exact ⟨c, congrArg Subtype.val (hc v hv)⟩

private theorem sphLine_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (g : G) (hfin : (MulAction.orbit K (g : G ⧸ K)).Finite) {w : V} (hw : w ∈ fixd ρ K) :
    ∃ N : ℂ, N ≠ 0 ∧ dc ρ K K g w - N • ρ g w ∈ GlobalTheory.PRep.twKer ρ K 1 := by
  letI : Fintype (MulAction.orbit K (g : G ⧸ K)) := hfin.fintype
  haveI : Nonempty (MulAction.orbit K (g : G ⧸ K)) := ⟨⟨_, MulAction.mem_orbit_self _⟩⟩
  refine ⟨(Fintype.card (MulAction.orbit K (g : G ⧸ K)) : ℂ), Nat.cast_ne_zero.2 Fintype.card_ne_zero, ?_⟩
  rw [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, Nat.cast_smul_eq_nsmul, ← Finset.card_univ,
    ← Finset.sum_const, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ ?_
  rintro ⟨q, a, ha⟩ -
  have h : (((a : G) * g : G) : G ⧸ K) = (q.out : G ⧸ K) := by
    rw [QuotientGroup.out_eq']; exact ha
  have h1 := hw _ (QuotientGroup.eq.mp h)
  have h2 : ρ q.out w = ρ a (ρ g w) := by
    conv_rhs => rw [← h1]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel_left]
  change ρ q.out w - ρ g w ∈ _
  rw [h2]
  exact GlobalTheory.IwahoriInj.sub_mem_twKer a.2 _

theorem UpperTheory.V.Pa.Lev.sphLine :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (σ : SmIrr (GL (Fin n) k)), ∀ v ∈ fixd σ.ρ (KO k (Fin n)), ∀ v' ∈ fixd σ.ρ (KO k (Fin n)), v ≠ 0 → ∃ c : ℂ, v' = c • v := by
  intro hBZ k _ _ _ _ n σ v hv v' hv' hv0
  obtain ⟨hfin, hcomm, -⟩ := sphComm k n ℂ σ.V σ.ρ
  have hfix : fixd σ.ρ (KO k (Fin n)) = GlobalTheory.PRep.fixed σ.ρ (KO k (Fin n)) := by
    ext u
    exact GlobalTheory.IwahoriInj.mem_fixed.symm
  have hfd : FiniteDimensional ℂ (fixd σ.ρ (KO k (Fin n))) := by
    rw [hfix]
    exact ((hBZ k).1 _ σ.V σ.ρ σ.smooth σ.irred).2 _ GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO
  obtain ⟨w, hw, hw0, hwe⟩ := sphLine_eig (fixd σ.ρ (KO k (Fin n))) ((Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩)
    (fun x => dc σ.ρ (KO k (Fin n)) (KO k (Fin n)) x)
    (fun x => (dcSum ℂ _ σ.V σ.ρ _ _ x (hfin x)).2.1) hcomm
  set J := GlobalTheory.PRep.twKer σ.ρ (KO k (Fin n)) 1 with hJ
  let T : Subrepresentation σ.ρ :=
    ⟨⨅ g, ((ℂ ∙ w) ⊔ J).comap (σ.ρ g), fun g u hu => by
      rw [Submodule.mem_iInf] at hu ⊢
      intro h
      have := hu (h * g)
      rwa [Submodule.mem_comap, map_mul, Module.End.mul_apply] at this⟩
  have hwT : w ∈ T.toSubmodule := by
    refine (Submodule.mem_iInf _).2 fun g => ?_
    obtain ⟨N, hN, h⟩ := sphLine_dc σ.ρ _ g (hfin g) hw
    obtain ⟨c, hc⟩ := hwe g
    rw [hc] at h
    rw [Submodule.mem_comap, ← Submodule.smul_mem_iff _ hN]
    have h3 : N • σ.ρ g w = c • w - (c • w - N • σ.ρ g w) := by abel
    rw [h3]
    exact sub_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)))
      (Submodule.mem_sup_right h)
  have hT : T = ⊤ := by
    haveI := σ.irred
    refine (eq_bot_or_eq_top T).resolve_left fun h => hw0 ?_
    rw [h] at hwT
    exact hwT
  have key : ∀ u ∈ fixd σ.ρ (KO k (Fin n)), ∃ c : ℂ, u = c • w := by
    intro u hu
    have h1 : u ∈ T.toSubmodule := by rw [hT]; trivial
    have h2 := (Submodule.mem_iInf _).1 h1 1
    rw [Submodule.mem_comap, map_one, Module.End.one_apply, Submodule.mem_sup] at h2
    obtain ⟨y, hy, z, hz, hyz⟩ := h2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have h3 : z = u - c • w := by rw [← hyz]; abel
    have h4 : z = 0 := GlobalTheory.IwahoriInj.eq_zero_of_fixed σ.smooth GlobalTheory.SplitFlip.isCompact_KO
      (by rw [← hfix, h3]; exact sub_mem hu (Submodule.smul_mem _ _ hw)) hz
    exact ⟨c, by rw [← hyz, h4, add_zero]⟩
  obtain ⟨a, rfl⟩ := key v hv
  obtain ⟨b, rfl⟩ := key v' hv'
  have ha : a ≠ 0 := fun h => hv0 (by rw [h, zero_smul])
  exact ⟨b / a, by rw [smul_smul, div_mul_cancel₀ _ ha]⟩
