import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.heckeEig_iSup_eq_top_of_sep {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Finite X]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) :
    ⨆ x, heckeEig T act x = ⊤ := by
  classical
  have := Fintype.ofFinite X
  have hs' : ∀ x y : X, ∃ f : T, x ≠ y → (f : X → O) x ≠ (f : X → O) y := by
    intro x y
    by_cases h : x = y
    · exact ⟨1, fun h' => (h' h).elim⟩
    · obtain ⟨f, hf, hne⟩ := hsep x y h
      exact ⟨⟨f, hf⟩, fun _ => hne⟩
  choose s hs using hs'
  let E : X → T := fun x => ∏ y ∈ Finset.univ.erase x, (s x y - algebraMap O T ((s x y : X → O) y))
  have hE : ∀ x z, ((E x : T) : X → O) z = ∏ y ∈ Finset.univ.erase x, ((s x y : X → O) z - (s x y : X → O) y) := by
    intro x z
    simp [E, Subalgebra.coe_prod, Finset.prod_apply]
  let d : X → O := fun x => ((E x : T) : X → O) x
  have hd : ∀ x, d x ≠ 0 := by
    intro x
    simp only [d, hE]
    exact Finset.prod_ne_zero_iff.mpr fun y hy => sub_ne_zero.mpr (hs x y (Ne.symm (Finset.ne_of_mem_erase hy)))
  have hE0 : ∀ x z, z ≠ x → ((E x : T) : X → O) z = 0 := by
    intro x z hz
    rw [hE]
    exact Finset.prod_eq_zero (i := z) (Finset.mem_erase.mpr ⟨hz, Finset.mem_univ _⟩) (sub_self _)
  have hmul : ∀ (g : T) x, g * E x = ((g : X → O) x) • E x := by
    intro g x
    apply Subtype.ext
    funext z
    by_cases hz : z = x
    · subst hz; simp
    · simp [hE0 x z hz]
  let F : X → O := fun x => ∏ x' ∈ Finset.univ.erase x, d x'
  let c : O := ∏ x, d x
  have hsum : ∑ x, F x • E x = algebraMap O T c := by
    apply Subtype.ext
    funext z
    rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single z]
    · simp only [F, c]
      show (∏ x' ∈ Finset.univ.erase z, d x') * d z = _
      rw [mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ z)]
      simp
    · intro x _ hx
      rw [hE0 x z (Ne.symm hx), mul_zero]
    · intro h; exact (h (Finset.mem_univ z)).elim
  let K := FractionRing O
  let ψ : T →ₐ[O] Module.End K (TensorProduct O K M) := (Module.End.baseChangeHom O K M).comp act
  have hψ : ∀ f, ψ f = (act f).baseChange K := fun f => rfl
  have hmem : ∀ x (m : TensorProduct O K M), ψ (E x) m ∈ heckeEig T act x := by
    intro x m
    simp only [heckeEig]
    refine Submodule.mem_iInf _ |>.mpr fun f => ?_
    rw [Module.End.mem_eigenspace_iff, ← hψ]
    rw [show ψ f (ψ (E x) m) = (ψ f * ψ (E x)) m from rfl, ← map_mul, hmul, map_smul,
      LinearMap.smul_apply, algebraMap_smul]
  have hc : algebraMap O K c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact Finset.prod_ne_zero_iff.mpr fun x _ => hd x
  refine eq_top_iff.mpr fun m _ => ?_
  have hcm : algebraMap O K c • m = ∑ x, F x • ψ (E x) m := by
    rw [algebraMap_smul]
    have := congrArg (fun f => ψ f m) hsum
    simp only [map_sum, map_smul, AlgHom.commutes] at this
    rw [LinearMap.sum_apply] at this
    simp only [LinearMap.smul_apply] at this
    rw [this, Module.algebraMap_end_apply]
  have : m = (algebraMap O K c)⁻¹ • (algebraMap O K c • m) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [this, hcm]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun x _ => ?_)
  exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_iSup_of_mem x (hmem x m))

theorem eigSpan_of_record (D : D7) : D.nd.EigSpan :=
  fun i => GlobalTheory.heckeEig_iSup_eq_top_of_sep (D.nd.T i) (D.nd.act i) (D.nd.T_sep i)

theorem ptSt_eigSpan : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → AllSt fun _ _ _ _ _ _ x =>
    ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => D'.nd.EigSpan := by
  intro hL _
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x l
  exact ⟨fun _ => ∅, fun L _ => eigSpan_of_record _⟩

end GlobalTheory.HeightCounting.Up

end
