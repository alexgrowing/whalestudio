import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers

noncomputable section

namespace GlobalTheory.NL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem tmul_basis_inj {O R M : Type} [CommRing O] [AddCommGroup R] [Module O R] [AddCommGroup M]
    [Module O M] (e₀ : M) (hs : Submodule.span O {e₀} = ⊤) (hi : ∀ c : O, c • e₀ = 0 → c = 0)
    {r r' : R} (h : r ⊗ₜ[O] e₀ = r' ⊗ₜ[O] e₀) : r = r' := by
  have hb : Function.Bijective (LinearMap.toSpanSingleton O M e₀) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => hi c (by simpa using hc), fun x => ?_⟩
    have hx : x ∈ Submodule.span O {e₀} := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨c, by simpa using hc⟩
  let f := LinearEquiv.ofBijective _ hb
  have h1 : f.symm e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp [f]
  have := congrArg (fun z => TensorProduct.rid O R (LinearMap.lTensor R f.symm.toLinearMap z)) h
  simpa [h1] using this

theorem ioLaws_of_injective (E : EtTie W RA RW inclR φR gR πA)
    (hO : Function.Injective (algebraMap O LL)) : IoLaws E := by
  obtain ⟨e, e₀, hs, hj, -⟩ := E.one_e
  have h0 : (e₀ : W.one.V) ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hT⟩ := W.one_line
    have hm : u ∈ W.one.L.T := hT ▸ Submodule.mem_span_singleton_self u
    have hx : (⟨u, hm⟩ : ↥W.one.L.T) ∈ Submodule.span O {e₀} := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
    have := congrArg Subtype.val hc
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact hu this.symm
  have hi : ∀ c : O, c • e₀ = 0 → c = 0 := by
    intro c hc
    have h1 : algebraMap O LL c • (e₀ : W.one.V) = 0 := by
      rw [algebraMap_smul]
      exact congrArg Subtype.val hc
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact hO (by rw [h2, map_zero])
    · exact absurd h2 h0
  have hx : ∀ x : W.EE, E.jD W.one (x • e) = E.ioE x ⊗ₜ[O] e₀ := by
    intro x
    rw [E.jD_smul, hj, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hact : ∀ g : G, W.one.actT g e₀ = e₀ := fun g => Subtype.ext (W.one_triv g _)
  have hφ : W.φD W.one e = e := by
    apply E.jD_inj
    rw [E.jD_φ, hj]
    simp [TWmap]
  have hγ : ∀ g : G, W.γD W.one (W.resΓ g) e = e := by
    intro g
    apply E.jD_inj
    rw [E.jD_act, hj]
    simp [TWact, hact]
  refine ⟨fun x => ?_, fun g x => ?_⟩
  · apply tmul_basis_inj e₀ hs hi
    have := E.jD_φ W.one (x • e)
    rw [W.φD_smul, hφ, hx, hx] at this
    simpa [TWmap] using this
  · apply tmul_basis_inj e₀ hs hi
    have := E.jD_act W.one g (x • e)
    rw [W.γD_smul, hγ, hx, hx] at this
    simpa [TWact, hact] using this

end Generic

theorem ioLaws : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; IoLaws E := by
  intro D HW F l _ K s LL h
  exact ioLaws_of_injective _ Subtype.val_injective

end GlobalTheory.NL
