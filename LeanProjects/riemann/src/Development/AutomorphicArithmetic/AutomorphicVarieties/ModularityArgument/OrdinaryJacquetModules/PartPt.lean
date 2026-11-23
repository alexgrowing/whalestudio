import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
import Batteries.Tactic.OpenPrivate

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open private cl_one cl_mem classical_fixed_by_iwahori cl_gen cl_stab cl_Yuz from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ClParts
open private pa_fin pa_part from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0

namespace UpperTheory.V.Z.Ord

private theorem ord_parts {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hH : H.Ax) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A]
    (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ) {P : ∀ (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), H.Part ι lam ξ → Prop}
    (hP : AutY H ι P) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d) (hs : H.IsSpec θ ι x.toRingHom lam ξ c0 sp) (hlam : lam ∈ H.admitted) (K : H.Lev) :
    H.OrdAt θ ι x.toRingHom lam ξ K c0 =
      ⨆ Y : {Y : H.Part ι lam ξ // P lam d ξ Y}, Y.1.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K c0 := by
  have h1 : H.ClAt θ ι x.toRingHom lam ξ K c0 ≤
      ⨆ Y : {Y : H.Part ι lam ξ // P lam d ξ Y}, Y.1.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K c0 := by
    intro F hF
    have hF' := (cl_mem H ι θ _ lam ξ K c0 F).1 hF
    exact cl_one H ι θ _ lam ξ K c0 hH (fun Y : {Y : H.Part ι lam ξ // P lam d ξ Y} => Y.1) F hF
      (hP lam hlam d ξ hs.alg F hF'.1 ⟨K, hF'.2.1⟩ ⟨c0, classical_fixed_by_iwahori H ι θ _ lam ξ K c0 c0 le_rfl hs.triv F hF⟩)
  refine le_antisymm (iSup_le fun μ => ?_) (iSup_le fun _ => inf_le_right)
  haveI := hs.fin K c0 le_rfl
  have h2 := cl_gen (fun Y : {Y : H.Part ι lam ξ // P lam d ξ Y} => Y.1.Y) (H.ClAt θ ι x.toRingHom lam ξ K c0) (H.uzC ι lam d)
    (cl_stab H ι θ _ lam ξ K c0 c0 le_rfl hs.triv) (fun Y => cl_Yuz H ι lam ξ Y.1) h1 μ.1
  have h3 : H.ClAt θ ι x.toRingHom lam ξ K c0 ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1 ≤ H.OrdAt θ ι x.toRingHom lam ξ K c0 :=
    le_iSup (fun μ : {μ : ℂ // ‖ι.symm μ‖ = 1} =>
      H.ClAt θ ι x.toRingHom lam ξ K c0 ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1) μ
  exact h2.trans (iSup_mono fun Y => inf_le_inf_left _ h3)

set_option maxHeartbeats 800000 in
theorem partPt : GlobalTheory.Mem.LiteralAutomorphy.LitN → PartPt := by
  intro _ L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ y hy
  haveI : Finite (ResidueField c.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := IsCNL.finite
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨h0, hfin, hfree, hK⟩ := hiComm L Ω l n c H hH A θ hθ K
  haveI := (hK a).2.1
  obtain ⟨e, he, hi, hY, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A _ _ _ (H.op A) (fun i => algebraMap c.O A (a i)) h0
  obtain ⟨-, -, -, -, -, -, h4, -⟩ := pa_fin (H.X.Ord (H.τA A) θ (H.lev K)) (H.MK θ a K) inf_le_left (H.op A)
    e he hi hY ι x sp (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K)
    _ (Submodule.span ℂ (sp '' H.MK θ a K)) (hsp.span K c0 le_rfl) rfl (fun Y : {Y : H.Part ι lam ξ // P lam d ξ Y} => Y.1.Y)
    (fun Y => pa_part H ι lam ξ Y.1) (ord_parts H hH θ ι hP x lam d ξ c0 sp hsp hlam K)
  obtain ⟨Y, F, hF0, hF, h⟩ := h4 y hy
  exact ⟨Y.1, F, Y.2, hF0, hF, h⟩

end UpperTheory.V.Z.Ord
