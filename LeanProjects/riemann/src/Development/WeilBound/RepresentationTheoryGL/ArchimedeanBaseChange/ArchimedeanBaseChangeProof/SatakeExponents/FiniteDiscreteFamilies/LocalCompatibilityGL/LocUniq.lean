import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinDiscNOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.DiscLocEx

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.F5.Bo.LocalUniqueness

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem isoPart_opD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (w : HeightOneSpectrum (𝓞 E)) {W : Type}
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W) (o : Op E a) {x : V}
    (hx : x ∈ GlobalTheory.CuspRep.LocUniq.isoPart σ (locRepD hV w)) :
    opD hV o x ∈ GlobalTheory.CuspRep.LocUniq.isoPart σ (locRepD hV w) := by
  cases o with
  | fin k =>
    exact GlobalTheory.CuspRep.LocUniq.isoPart_fin (finPartD hV) w σ k hx
  | cpt k =>
    refine GlobalTheory.CuspRep.LocUniq.isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine GlobalTheory.CuspRep.LocUniq.isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

theorem equiv_of_isLocCompGL {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) (w : HeightOneSpectrum (𝓞 E))
    (σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))) (h : IsLocCompGL V w σ) (h' : IsLocCompGL V w σ') :
    Nonempty (σ.ρ.Equiv σ'.ρ) := by
  obtain ⟨f, h0, hfV, hf⟩ := h
  obtain ⟨f', h0', hfV', hf'⟩ := h'
  let F : σ.V →ₗ[ℂ] V := f.codRestrict V hfV
  let F' : σ'.V →ₗ[ℂ] V := f'.codRestrict V hfV'
  have hF : ∀ g v, F (σ.ρ g v) = locRepD hV.stable w g (F v) := fun g v => Subtype.ext (hf g v)
  have hF' : ∀ g v, F' (σ'.ρ g v) = locRepD hV.stable w g (F' v) := fun g v => Subtype.ext (hf' g v)
  have := σ.irred
  have := σ'.irred
  refine GlobalTheory.CuspRep.LocUniq.equiv_of_isoPart σ.ρ σ'.ρ (locRepD hV.stable w) ?_
    ⟨F', fun g => LinearMap.ext (hF' g)⟩ fun e => h0' (LinearMap.ext fun v => ?_)
  · have hm := Submodule.map_injective_of_injective V.injective_subtype
    rcases hV.irred ((GlobalTheory.CuspRep.LocUniq.isoPart σ.ρ (locRepD hV.stable w)).map V.subtype)
      (Submodule.map_subtype_le _ _) (by
        rintro o _ ⟨x, hx, rfl⟩
        exact ⟨_, isoPart_opD hV.stable w σ.ρ o hx, rfl⟩) with h1 | h1
    · refine absurd (LinearMap.ext fun v => ?_) h0
      have h2 : GlobalTheory.CuspRep.LocUniq.isoPart σ.ρ (locRepD hV.stable w) = ⊥ := hm (h1.trans (Submodule.map_bot _).symm)
      have h3 : F v ∈ GlobalTheory.CuspRep.LocUniq.isoPart σ.ρ (locRepD hV.stable w) :=
        Submodule.mem_iSup_of_mem (⟨F, fun g => LinearMap.ext (hF g)⟩ : σ.ρ.IntertwiningMap (locRepD hV.stable w))
          ⟨v, rfl⟩
      rw [h2] at h3
      exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h3)
    · exact hm (h1.trans (Submodule.map_subtype_top _).symm)
  · have := congrArg (fun T : σ'.ρ.IntertwiningMap (locRepD hV.stable w) => (T.toLinearMap v : Sm E a)) e
    exact this

end PositivityTheory.Rg.BcB.F.F5.Bo.LocalUniqueness

namespace PositivityTheory.Rg.BcB.F.F5.Bo

theorem LocUniq_holds : LocUniq := by
  intro E _ _ _ N V hV w σ σ' h h'
  obtain ⟨e⟩ := LocalUniqueness.equiv_of_isLocCompGL hV w σ σ' h h'
  exact GlobalTheory.LocGL.IrrGL.of_eq_of.2 ⟨e⟩

end PositivityTheory.Rg.BcB.F.F5.Bo

end
