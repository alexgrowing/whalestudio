import Development.WeilBound.CoreStatements.PadicHodgeComparison.SaturatedBaseChange.BcBackOffTOfSat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocCompSplit

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.LFun GlobalTheory.PRep Formalism.UG
open GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

theorem compUnique : CompUnique := by
  intro E _ _ _ n π hπ w hw P P' h h'
  let Ψ : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨r, -, -, hr2⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  have hcl : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by rw [← he, e.apply_symm_apply]
  let s : GL (Fin n) (w.adicCompletion E) →* UA E n := (locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have mk : ∀ Q : LocIrr w n, IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) Q.ρ →
      ∃ F : Q.ρ.IntertwiningMap (Ψ.rep.comp s), F ≠ 0 := fun Q ⟨_, f, hf0, hfm, hf⟩ =>
    ⟨⟨f.codRestrict Ψ.V hfm, fun g => LinearMap.ext fun v => Subtype.ext (by
      have := hf (e.symm g) v
      rw [show ((cLoc w).comp (locU n w).subtype) (e.symm g) = g from hcl g] at this
      exact this)⟩, fun h0 => hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h0 v))⟩
  obtain ⟨F, hF⟩ := mk P h
  obtain ⟨F', hF'⟩ := mk P' h'
  refine (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA E n) (GL (Fin n) (w.adicCompletion E)) Ψ.V P.V P'.V Ψ.rep s P.ρ P'.ρ Ψ.isIrreducible_rep P.irred
    P'.irred (fun g => ⟨e (r g), fun y => ?_⟩) F hF).2 F' hF'
  have : s (e (r g)) = (r g : UA E n) := congrArg Subtype.val (e.symm_apply_apply (r g))
  rw [this]
  exact hr2 g (e.symm y)

private theorem speh_single_factor_equiv {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (n m : ℕ)
    (hm : m = n) (h : ∑ _i : Fin 1, m = n) (ρ : LocIrr w n) (σ : Fin 1 → LocIrr w m)
    (hs : IsSpeh (IrrGL.of ρ.ρ ρ.smooth ρ.irred) 1 (σ 0).ρ) :
    Nonempty ((locProd (N := fun _ : Fin 1 => m) h w σ).Equiv ρ.ρ) := by
  subst hm
  obtain ⟨τ, rfl⟩ : ∃ τ, σ = fun _ => τ := ⟨σ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨e₁⟩ := nonempty_equiv_multiProd_one τ.smooth (stdBlocks (fun _ : Fin 1 => m) h) fun a i => Fin.ext (by
    rw [stdBlocks_val, Subsingleton.elim a 0]; simp)
  obtain ⟨hd, hτ, p, hp, -⟩ := hs
  have key : ∀ y : Fin 1 → IrrGL (w.adicCompletion E), y = (fun _ => IrrGL.of ρ.ρ ρ.smooth ρ.irred) →
      ∀ hd : ∑ i, (y i).1 = m, Nonempty ((IrrGL.of ρ.ρ ρ.smooth ρ.irred).rep.Equiv (prodIrr y hd)) := by
    rintro _ rfl hd
    exact nonempty_equiv_prodIrr_one _ hd
  obtain ⟨e⟩ := key _ (funext fun _ => by simp [spehFactor]) hd
  let q : ρ.ρ.IntertwiningMap τ.ρ :=
    p.comp (e.toIntertwiningMap.comp (IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).toIntertwiningMap)
  have hq : Function.Surjective q :=
    hp.comp (e.toLinearEquiv.surjective.comp (IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).toLinearEquiv.surjective)
  have hinj : Function.Injective q := GlobalTheory.DiscreteSpectrumCM.injective_of_irreducible ρ.irred q fun h0 => by
    have : Nontrivial τ.V := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hτ).1
    obtain ⟨y, hy⟩ := exists_ne (0 : τ.V)
    obtain ⟨v, rfl⟩ := hq y
    exact hy (LinearMap.congr_fun h0 v)
  exact ⟨e₁.symm.trans (q.ofBijective ⟨hinj, hq⟩).symm⟩

theorem oneFactor : OneFactor := fun _ _ _ _ w n h ρ σ hs => speh_single_factor_equiv w n (1 * n) (one_mul n) h ρ σ hs

end PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

end
