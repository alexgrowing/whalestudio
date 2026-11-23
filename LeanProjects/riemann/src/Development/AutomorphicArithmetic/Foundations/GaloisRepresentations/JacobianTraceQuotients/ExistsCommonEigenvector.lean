import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCommonEigenvectorSecond

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private lemma exists_common_eigenvector {ι M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (f : ι → Module.End ℂ M) (hc : ∀ i j, f i * f j = f j * f i) (W : Submodule ℂ M) (hW : W ≠ ⊥)
    (hst : ∀ i, ∀ y ∈ W, f i y ∈ W) :
    ∃ y ∈ W, y ≠ 0 ∧ ∀ i, ∃ c : ℂ, f i y = c • y :=
  _root_.UpperTheory.Reformulated.B.CommonEigenvectorInInvariantComplexSubspace.exists_common_eigenvector f hc W hW hst

theorem UpperTheory.Gal.Join.twExp :
    UpperTheory.Gal.Join.TwExp := by
  intro T X _ _ _ ρ P _ s A hρ hA hAρ t₁ htr
  let r : T → Module.End ℂ P := fun t => (ρ t).restrict (hρ t)
  let A' : Module.End ℂ P := A.restrict hA
  have r_apply : ∀ t (y : P), ((r t y : P) : X) = ρ t y := fun t y => rfl
  have A_apply : ∀ y : P, ((A' y : P) : X) = A y := fun y => rfl
  have r_mul : ∀ a b, r (a * b) = r a * r b := by
    intro a b
    ext y
    simp [r_apply, Module.End.mul_apply, map_mul]
  have hcomm : ∀ a b, r a * r b = r b * r a := by
    intro a b
    rw [← r_mul, ← r_mul, mul_comm]
  have hsemi : ∀ t, A' * r t = r (s t) * A' := by
    intro t
    ext y
    simp [r_apply, A_apply, Module.End.mul_apply, hAρ]
  let N : (T → ℂ) → Submodule ℂ P := fun χ => ⨅ t, (r t).maxGenEigenspace (χ t)
  have hmaps : ∀ a b c, Set.MapsTo (r a) ((r b).maxGenEigenspace c) ((r b).maxGenEigenspace c) :=
    fun a b c => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm b a) c
  have hind : iSupIndep N := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo r hmaps
  have htop : ⨆ χ, N χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute r
      (fun a b _ => hcomm a b) (fun t => Module.End.iSup_maxGenEigenspace_eq_top (r t))
  let f : Module.End ℂ P := r t₁ * A'
  have hAN : ∀ χ, Set.MapsTo f (N χ) (N (χ ∘ s.symm)) := by
    intro χ y hy
    have hy' : ∀ t, y ∈ (r t).maxGenEigenspace (χ t) := fun t => (Submodule.mem_iInf _).mp hy t
    refine (Submodule.mem_iInf _).mpr fun t => ?_
    have key : A' y ∈ (r t).maxGenEigenspace (χ (s.symm t)) := by
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (hy' (s.symm t))
      refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, ?_⟩
      have hsb : SemiconjBy A' (r (s.symm t) - χ (s.symm t) • (1 : Module.End ℂ P))
          (r t - χ (s.symm t) • (1 : Module.End ℂ P)) := by
        have h1 := hsemi (s.symm t)
        rw [MulEquiv.apply_symm_apply] at h1
        unfold SemiconjBy
        rw [mul_sub, sub_mul, h1]
        simp
      have := congrArg (fun g : Module.End ℂ P => g y) (hsb.pow_right k).eq
      simp only [Module.End.mul_apply, hk, map_zero] at this
      exact this.symm
    exact hmaps t₁ t _ key

  have hex : ∃ χ : T → ℂ, χ ∘ s = χ ∧ N χ ≠ ⊥ := by
    by_contra hno
    push_neg at hno
    let J := {χ : T → ℂ // χ ∘ s ≠ χ}
    let N' : J → Submodule ℂ P := fun j => N j.1
    have hind' : iSupIndep N' := hind.comp Subtype.val_injective
    have htop' : ⨆ j, N' j = ⊤ := by
      rw [eq_top_iff, ← htop]
      refine iSup_le fun χ => ?_
      by_cases h : χ ∘ s = χ
      · rw [hno χ h]
        exact bot_le
      · exact le_iSup N' ⟨χ, h⟩
    have hint : DirectSum.IsInternal N' :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind' htop'
    have hne : ∀ χ : T → ℂ, χ ∘ s ≠ χ → χ ∘ s.symm ≠ χ := by
      intro χ h e
      apply h
      funext t
      have := congrFun e (s t)
      simpa using this.symm
    let σ : J → J := fun j => ⟨j.1 ∘ s.symm, by
      intro e
      apply hne j.1 j.2
      funext t
      have := congrFun e t
      simpa [Function.comp] using this.symm⟩
    have hσ : ∀ j, σ j ≠ j := fun j e => hne j.1 j.2 (congrArg Subtype.val e)
    have hzero : LinearMap.trace ℂ P f = 0 :=
      LinearMap.trace_eq_zero_of_mapsTo_ne hint σ hσ (fun j => hAN j.1)
    apply htr
    have hst : ∀ y ∈ P, (ρ t₁ ∘ₗ A) y ∈ P := fun y hy => hρ t₁ _ (hA y hy)
    have hfeq : (ρ t₁ ∘ₗ A).restrict hst = f := by
      ext y
      rfl
    unfold trIn
    rw [dif_pos hst, hfeq, hzero]
  obtain ⟨χ, hχ, hN⟩ := hex
  have hNst : ∀ t, ∀ y ∈ N χ, r t y ∈ N χ := by
    intro t y hy
    exact (Submodule.mem_iInf _).mpr fun t' => hmaps t t' _ ((Submodule.mem_iInf _).mp hy t')
  obtain ⟨y, hyN, hy0, hy⟩ := exists_common_eigenvector r hcomm (N χ) hN hNst
  choose c hc using hy
  have hcχ : ∀ t, c t = χ t := by
    intro t
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp ((Submodule.mem_iInf _).mp hyN t)
    have hpow : ∀ m : ℕ, ((r t - χ t • (1 : Module.End ℂ P)) ^ m) y = (c t - χ t) ^ m • y := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hc t]
        simp only [LinearMap.smul_apply, Module.End.one_apply, ← sub_smul, smul_smul, pow_succ']
        ring_nf
    rw [hpow k] at hk
    have := (smul_eq_zero.mp hk).resolve_right hy0
    by_contra hne
    exact pow_ne_zero k (sub_ne_zero.mpr hne) this
  have hc1 : c 1 = 1 := by
    have h1 : r 1 = 1 := by
      ext v
      simp [r_apply]
    have h2 := hc 1
    rw [h1, Module.End.one_apply] at h2
    have h3 : (c 1 - 1) • y = 0 := by
      rw [sub_smul, one_smul, ← h2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy0)
  have hcmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    have h2 := hc (a * b)
    rw [r_mul, Module.End.mul_apply, hc b, map_smul, hc a, smul_smul] at h2
    have h3 : (c (a * b) - c b * c a) • y = 0 := by
      rw [sub_smul, ← h2, sub_self]
    rw [sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy0), mul_comm]
  let m : T →* ℂ := { toFun := c, map_one' := hc1, map_mul' := hcmul }
  refine ⟨m.toHomUnits, fun t => ?_, (y : X), y.2, fun h => hy0 (Subtype.ext h), fun t => ?_⟩
  · apply Units.ext
    simp only [MonoidHom.coe_toHomUnits]
    change c (s t) = c t
    rw [hcχ, hcχ]
    exact congrFun hχ t
  · simp only [MonoidHom.coe_toHomUnits]
    change ρ t (y : X) = c t • (y : X)
    exact congrArg Subtype.val (hc t)
