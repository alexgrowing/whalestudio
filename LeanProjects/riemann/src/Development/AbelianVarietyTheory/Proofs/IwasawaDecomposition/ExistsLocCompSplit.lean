import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGLStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU

theorem exists_locComp_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsAdmissible σ.ρ ∧ π.IsLocComp w σ ∧ (IsUnramU π.V w ↔ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w n)) := by
  intro E _ _ _ n π w hw
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨σ₀, hadm, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.T.exists_admissible_localComponent_definiteUnitary E n π w
  obtain ⟨r, -, -, hr2⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  have hsym : ∀ x : locU n w, e.symm (cLoc w (x : UA E n)) = x := fun x => by
    rw [← he, e.symm_apply_apply]
  have hcl : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  let ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) σ₀.V :=
    σ₀.ρ.comp e.symm.toMulEquiv.toMonoidHom
  have hρ : ∀ g v, ρ g v = σ₀.ρ (e.symm g) v := fun _ _ => rfl
  let σ : SmIrr (GL (Fin n) (w.adicCompletion E)) :=
    { V := σ₀.V
      ρ := ρ
      smooth := fun v => (σ₀.smooth v).preimage e.symm.continuous
      irred := GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ₀.ρ e.symm.toMulEquiv σ₀.irred }
  have hf' : ∀ (x : locU n w) v, f (σ₀.ρ x v) = RU E n x (f v) := hf
  refine ⟨σ, GlobalTheory.CuspMult.isAdmissible_comp_equiv σ₀.ρ e.symm hadm, ⟨σ.irred, f, hf0, hfm, fun x v => ?_⟩, ?_, ?_⟩
  · change f (ρ (cLoc w (x : UA E n)) v) = _
    rw [hρ, hsym, hf']
  · rintro ⟨φ, hφ, h0, hK⟩
    let F : σ₀.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf' x v)⟩
    have hF0 : F ≠ 0 := fun h =>
      hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    have hsup := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA E n) (locU n w) π.V σ₀.V σ₀.V π.rep (locU n w).subtype σ₀.ρ σ₀.ρ
      π.isIrreducible_rep σ₀.irred σ₀.irred (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0).1
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.rep.comp (locU n w).subtype) σ₀.ρ σ₀.irred
      (fun h : σ₀.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) => h.toLinearMap)
      (fun h g u => LinearMap.congr_fun (h.isIntertwining' g) u)
      {k | cLoc w (k : UA E n) ∈ GlobalTheory.LFun.KGL w n} ⟨φ, hφ⟩
      (fun h => h0 (congrArg Subtype.val h)) (fun k hk => Subtype.ext (hK k k.2 hk))
      (hsup ▸ Submodule.mem_top)
    intro hb
    have hmem : v ∈ fixed ρ (GlobalTheory.LFun.KGL w n) := fun g => by
      have h1 : σ₀.ρ (e.symm g.1) v = v := hv _ (by
        have h2 : cLoc w ((e.symm g.1 : locU n w) : UA E n) ∈ GlobalTheory.LFun.KGL w n := by
          rw [hcl]
          exact g.2
        exact h2)
      simpa [hρ] using h1
    have hb' : fixed ρ (GlobalTheory.LFun.KGL w n) = ⊥ := hb
    rw [hb'] at hmem
    exact hv0 ((Submodule.mem_bot _).1 hmem)
  · intro hsph
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsph
    have hinj : Function.Injective f := by
      have hk := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 σ₀.irred).2 (LinearMap.ker f) (fun g u hu => by
        rw [LinearMap.mem_ker] at hu ⊢
        rw [hf', hu, map_zero])
      rcases hk with h | h
      · exact LinearMap.ker_eq_bot.1 h
      · exact absurd (LinearMap.ker_eq_top.1 h) hf0
    refine ⟨f v, hfm v, fun h => hv0 (hinj (h.trans (map_zero f).symm)), fun x hx hk => ?_⟩
    have h1 : σ₀.ρ (⟨x, hx⟩ : locU n w) v = v := by
      have h2 : ρ (cLoc w x) v = v := by simpa using hv ⟨_, hk⟩
      rwa [hρ, hsym (⟨x, hx⟩ : locU n w)] at h2
    have h3 := hf' ⟨x, hx⟩ v
    rw [h1] at h3
    exact h3.symm

end GlobalTheory.DefU
