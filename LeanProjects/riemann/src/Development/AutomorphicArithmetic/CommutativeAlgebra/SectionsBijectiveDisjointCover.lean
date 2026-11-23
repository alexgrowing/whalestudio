import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecSigmaBijectiveStatement
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Et

theorem UpperTheory.sections_bijective_disjoint_cover :
    ∀ (R : Type) [CommRing R] (G : Shv R) {Y : Scheme.{0}} {ι : Type} (V : ι → Scheme.{0}) (j : ∀ a, V a ⟶ Y) [∀ a, IsOpenImmersion (j a)],
      (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) → (∀ y : Y, ∃ a, y ∈ Set.range (j a)) → Function.Bijective fun (x : Sec G Y) (a : ι) => Sec.res (j a) x := by
  intro R _ G Y ι V j _ hd hc
  have hop : IsOpenImmersion (Sigma.desc j) :=
    isOpenImmersion_sigmaDesc V j (fun a b hab => hd a b hab)
  have htop : (Sigma.desc j).opensRange = ⊤ := by
    refine top_unique fun y _ => ?_
    obtain ⟨a, z, rfl⟩ := hc y
    refine ⟨(Sigma.ι V a) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  have hiso : IsIso (Sigma.desc j) := isIso_of_isOpenImmersion_of_opensRange_eq_top _ htop
  have hb : Function.Bijective (fun x : Sec G Y => Sec.res (Sigma.desc j) x) := by
    have h1 : ∀ x : Sec G Y, Sec.res (inv (Sigma.desc j)) (Sec.res (Sigma.desc j) x) = x := by
      intro x
      have := congrArg (fun f => (G.obj.map f.op).hom x) (IsIso.inv_hom_id (Sigma.desc j))
      simpa [Sec.res] using this
    have h2 : ∀ x : Sec G (∐ V), Sec.res (Sigma.desc j) (Sec.res (inv (Sigma.desc j)) x) = x := by
      intro x
      have := congrArg (fun f => (G.obj.map f.op).hom x) (IsIso.hom_inv_id (Sigma.desc j))
      simpa [Sec.res] using this
    exact Function.bijective_iff_has_inverse.2 ⟨_, h1, h2⟩
  have heq : (fun (x : Sec G Y) (a : ι) => Sec.res (j a) x) =
      (fun (b : Sec G (∐ V)) (a : ι) => Sec.res (Sigma.ι V a) b) ∘
        (fun x : Sec G Y => Sec.res (Sigma.desc j) x) := by
    funext x a
    have e : G.obj.map (j a).op = G.obj.map (Sigma.desc j).op ≫ G.obj.map (Sigma.ι V a).op := by
      rw [← Functor.map_comp, ← op_comp, Sigma.ι_desc]
    show (G.obj.map (j a).op).hom x = _
    rw [e]
    rfl
  rw [heq]
  exact (GlobalTheory.T.sec_sigma_res_bijective R G V).comp hb

end
