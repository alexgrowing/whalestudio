import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigOfSat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetEqOne

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL
open GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.GJStandardLCuspidal
open scoped Classical

namespace UpperTheory.V.Z.Inf

private theorem localEmbedding_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (w.adicCompletion K)) :
    AdelicGLn.localEmbedding w g = locGL K n w g := by
  refine Units.ext <| Matrix.ext fun a b => FiniteAdeleRing.ext K fun v => ?_
  change ((AdelicGLn.finiteRestrictedEquiv K n).symm _ : AdelicGLn.FiniteAdelicGL K n) a b v = _
  rw [AdelicGLn.finiteRestrictedEquiv_symm_apply, RestrictedProduct.coe_mulSingle_apply]
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (pLoc_locGL v g)).symm
  · rw [Pi.mulSingle_eq_of_ne h]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (pLoc_locGL_of_ne h g)).symm

private theorem isSatake_of_eig {K : Type} [Field K] [NumberField K] {n : ℕ} (w : HeightOneSpectrum (𝓞 K))
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion K)) V)
    (hirr : ρ.IsIrreducible) (hs : IsSmooth ρ) (y : V) (hy : y ∈ fixedVectors ρ (integralGL (w.adicCompletion K) n))
    (l : Module.Dual ℂ V) (hl : l y ≠ 0) (z : Fin n → ℂˣ)
    (hE : Af.Smo.Eig w (Finset.univ.val.map z) fun g => l (ρ g y)) :
    Spherical.IsSatakeParameter (F := w.adicCompletion K) ρ (localHaar n w) z := by
  obtain ⟨hKeq, hu, hq, -⟩ := UpperTheory.V.Af.Smo.sphDict K n w
  have hTj := UpperTheory.V.Af.Smo.tjSet UpperTheory.V.Af.Smo.sphDict K n w
  have hf : ∀ g, ∀ k ∈ integralGL (w.adicCompletion K) n, l (ρ (g * k) y) = l (ρ g y) := by
    rw [hKeq]
    exact hE.inv
  have hT : ∀ r ≤ n, Spherical.minusculeHecke (localHaar n w) r ∈
      Spherical.eigenSubalgebra (localHaar n w) z (fun g => l (ρ g y)) hf := by
    intro r hr
    refine GlobalTheory.HenQ.ShellOp.minuscule_mem_of z hf hr fun g => ?_
    rw [hKeq, ← hTj r hr, hE.eig _ hu r hr g, hq r hr, GlobalTheory.HenQ.ShellOp.esymm_eq, GlobalTheory.LFun.satEig]
  have htop := Spherical.eigenSubalgebra_eq_top z hf hT (GlobalTheory.HenQ.ShellOp.central_mem_of_top z hf (hT n le_rfl))
  have hne : fixedVectors ρ (integralGL (w.adicCompletion K) n) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨y, hy, fun e => hl (by rw [e, map_zero])⟩
  obtain ⟨z', hz'⟩ := Spherical.exists_satakeParameter (μ := localHaar n w) hs hne
  intro h u hu'
  have h1 : h ∈ Spherical.eigenSubalgebra (localHaar n w) z (fun g => l (ρ g y)) hf := htop ▸ Algebra.mem_top
  have h2 := h1 1
  simp only [one_mul, map_one, Module.End.one_apply] at h2
  have h3 := dual_heckeAct (localHaar n w) (ρ := ρ) (h : HeckeAlgebra (localHaar n w)).mem (hs y) l
  rw [h2, hz' h y hy, map_smul, smul_eq_mul] at h3
  rw [hz' h u hu', mul_right_cancel₀ hl h3]

end UpperTheory.V.Z.Inf

open UpperTheory.V UpperTheory.V.Z.Inf in
theorem UpperTheory.V.Z.Inf.satDict :
    UpperTheory.V.Z.Inf.SatDict := by
  intro K _ _ _ n σ h D v B hB
  obtain ⟨z, rfl⟩ : ∃ z : Fin n → ℂˣ, Finset.univ.val.map z = B := by
    obtain ⟨l, rfl⟩ := Quotient.exists_rep B
    have hl : l.length = n := hB.card
    subst hl
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  refine ⟨z, ?_, rfl⟩
  by_cases hK : fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) = ⊥
  · intro f u hu
    rw [hK, Submodule.mem_bot] at hu
    subst hu
    rw [smul_zero]
    simpa using heckeAct_smul_right (μ := localHaar n v) (ρ := D.finite.π v) (f : HeckeAlgebra (localHaar n v)).mem 0
      (Submodule.zero_mem _)
  obtain ⟨a, x, hx, ha, hx0, hxK⟩ := exists_pureTensor_spherical (Cm.toRep σ h) D
  let J : D.finite.W v →ₗ[ℂ] σ.V := (Cm.carrierEq σ).toLinearMap ∘ₗ Iv D a x hx v
  have hJ : ∀ g y t, (J (D.finite.π v g y)).1.1 t = (J y).1.1 (t * finGL K n (locGL K n v g)) := by
    intro g y t
    have e : J (D.finite.π v g y) = σ.op (.fin (locGL K n v g)) (J y) := by
      rw [← localEmbedding_eq]
      exact (congrArg (Cm.carrierEq σ) (Iv_int D a x hx v g y)).trans (Cm.carrierEq_τ σ _ _)
    rw [e]
    rfl
  have h0 : J (x v) ≠ 0 := by
    intro e
    have e' : Iv D a x hx v (x v) = 0 := (Cm.carrierEq σ).map_eq_zero_iff.1 e
    rw [Iv_self] at e'
    exact phi_ne D a x hx ha hx0 e'
  obtain ⟨t, ht⟩ : ∃ t, (J (x v)).1.1 t ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (Subtype.ext (Subtype.ext (funext hc)))
  let l : Module.Dual ℂ (D.finite.W v) :=
    { toFun := fun y => (J y).1.1 t
      map_add' := fun y y' => by rw [map_add]; rfl
      map_smul' := fun c y => by rw [map_smul]; rfl }
  have hE := Af.StrongMultiplicityOne.eigOfSat K n σ v _ ((CG.hasSat_mk σ v _).1 hB) (J (x v)).1 (J (x v)).2 (fun g k hk => by
    rw [← (Af.Smo.sphDict K n v).1] at hk
    rw [← hJ, hxK v hK k hk]) t
  refine isSatake_of_eig v _ (D.finite.isIrreducible v) (D.finite.isAdmissible v).1 (x v) (hxK v hK) l ht z ?_
  have e : (fun g => l (D.finite.π v g (x v))) = fun g => (J (x v)).1.1 (t * finGL K n (locGL K n v g)) :=
    funext fun g => hJ g _ t
  rw [e]
  exact hE
