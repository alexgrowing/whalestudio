import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCohomologyVanishesTameInertiaNoFixedStatement
import Formalism.SharpRestriction.LevelLetterCocycles.CohomologyScalarsVanish.PfCohScalarsVanish

noncomputable section

namespace GlobalTheory.HOneTwoLevel

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem l_mem_max (N : NData R H what₂) (i : N.Loc) :
    ((N.l i : ℕ) : N.O i) ∈ IsLocalRing.maximalIdeal (N.O i) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hl : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  have hle : (⊤ : Submodule ℤ_[N.l i] (N.O i)) ≤ IsLocalRing.maximalIdeal ℤ_[N.l i] • ⊤ := by
    intro x _
    have hx : x = ((N.l i : ℕ) : ℤ_[N.l i]) • (((hu.unit⁻¹ : (N.O i)ˣ) : N.O i) * x) := by
      rw [Algebra.smul_def, map_natCast, ← mul_assoc]
      have : ((N.l i : ℕ) : N.O i) * ((hu.unit⁻¹ : (N.O i)ˣ) : N.O i) = 1 := by
        exact hu.mul_val_inv
      rw [this, one_mul]
    rw [hx]; exact Submodule.smul_mem_smul hl trivial
  have hjac : IsLocalRing.maximalIdeal ℤ_[N.l i] ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
    (Module.finite_def.1 inferInstance) hle hjac
  have h1 : (1 : N.O i) ∈ (⊤ : Submodule ℤ_[N.l i] (N.O i)) := trivial
  rw [hbot, Submodule.mem_bot] at h1
  exact one_ne_zero h1

theorem isLocalHom (N : NData R H what₂) (i : N.Loc) : IsLocalHom (algebraMap ℤ_[N.l i] (N.O i)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have ha' : a ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := (IsLocalRing.mem_maximalIdeal a).2 h
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at ha'
  obtain ⟨c, rfl⟩ := ha'
  have : algebraMap ℤ_[N.l i] (N.O i) (c * (N.l i : ℤ_[N.l i])) ∈ IsLocalRing.maximalIdeal (N.O i) := by
    rw [map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ (l_mem_max N i)
  exact (IsLocalRing.mem_maximalIdeal _).1 this ha

theorem resFin (N : NData R H what₂) (i : N.Loc) : Finite (IsLocalRing.ResidueField (N.O i)) :=
  haveI := isLocalHom N i
  IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[N.l i]) inferInstance

theorem resChar (N : NData R H what₂) (i : N.Loc) : CharP (IsLocalRing.ResidueField (N.O i)) (N.l i) := by
  rw [CharP.charP_iff_prime_eq_zero (N.lPrime i).out, ← map_natCast (IsLocalRing.residue (N.O i)),
    IsLocalRing.residue_eq_zero_iff]
  exact l_mem_max N i

theorem residue_eq_one (N : NData R H what₂) (i : N.Loc) {x : N.O i}
    (hx : x - 1 ∈ IsLocalRing.maximalIdeal (N.O i)) : IsLocalRing.residue (N.O i) x = 1 := by
  rw [← sub_eq_zero, ← map_one (IsLocalRing.residue (N.O i)), ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hx

theorem chiEpsBar_open (N : NData R H what₂) (i : N.Loc) (e : ℤ) :
    IsOpen ((Formalism.MainNotions.SumRepresentations.At.chiEpsBar N i e).ker : Set (G H.E N.Om)) := by
  have hm : IsOpen (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i)) := by
    have := (isAdic_iff.1 (N.O_adic i)).1 1
    rwa [pow_one] at this
  have hmZ : IsOpen (IsLocalRing.maximalIdeal ℤ_[N.l i] : Set ℤ_[N.l i]) := by
    have : (IsLocalRing.maximalIdeal ℤ_[N.l i] : Set ℤ_[N.l i]) = {x | ‖x‖ < 1} := by
      ext x
      simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, Set.mem_setOf_eq]
      exact PadicInt.mem_nonunits
    rw [this]; exact isOpen_lt continuous_norm continuous_const
  let U1 : Set (G H.E N.Om) :=
    (fun g => ((N.chi i 1 g : (N.O i)ˣ) : N.O i) - 1) ⁻¹' (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i))
  let U2 : Set (G H.E N.Om) :=
    (fun g => ((cycZ H.E N.Om (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) - 1) ⁻¹'
      (IsLocalRing.maximalIdeal ℤ_[N.l i] : Set ℤ_[N.l i])
  have hU1 : IsOpen U1 := hm.preimage ((N.chi_cont i 1).sub continuous_const)
  have hU2 : IsOpen U2 :=
    hmZ.preimage ((Units.continuous_val.comp (continuous_cycZ H.E N.Om (N.l i))).sub continuous_const)
  have h1 : (1 : G H.E N.Om) ∈ U1 ∩ U2 := by
    refine ⟨?_, ?_⟩
    · show ((N.chi i 1 1 : (N.O i)ˣ) : N.O i) - 1 ∈ IsLocalRing.maximalIdeal (N.O i)
      rw [map_one, Units.val_one, sub_self]; exact Ideal.zero_mem _
    · show ((cycZ H.E N.Om (N.l i) 1 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[N.l i]
      rw [map_one, Units.val_one, sub_self]; exact Ideal.zero_mem _
  have hsub : U1 ∩ U2 ⊆ ((Formalism.MainNotions.SumRepresentations.At.chiEpsBar N i e).ker : Set (G H.E N.Om)) := by
    intro g hg
    have ha : Units.map (IsLocalRing.residue (N.O i)).toMonoidHom (N.chi i 1 g) = 1 := by
      ext
      exact residue_eq_one N i hg.1
    have hb : Units.map (IsLocalRing.residue (N.O i)).toMonoidHom (Formalism.MainNotions.N.Glob.epsO N i g) = 1 := by
      ext
      apply residue_eq_one N i
      have := isLocalHom N i
      have h2 : ((cycZ H.E N.Om (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) - 1 ∈
          IsLocalRing.maximalIdeal ℤ_[N.l i] := hg.2
      have h3 : algebraMap ℤ_[N.l i] (N.O i)
          (((cycZ H.E N.Om (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) - 1) ∈ IsLocalRing.maximalIdeal (N.O i) :=
        (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
          (IsLocalRing.mem_maximalIdeal _).1 h2 (isUnit_of_map_unit _ _ hu)
      rw [map_sub, map_one] at h3
      exact h3
    show Formalism.MainNotions.SumRepresentations.At.chiEpsBar N i e g = 1
    delta Formalism.MainNotions.SumRepresentations.At.chiEpsBar
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply,
      MonoidHom.comp_apply, ha, hb, inv_one, one_zpow, one_mul]
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset ((hU1.inter hU2).mem_nhds h1) hsub)

theorem contAction_of_open {k Γ M : Type} [CommRing k] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation k Γ M) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ))
    (h1 : ∀ u ∈ U, rho u = 1) : ReciprocityTheory.Gal.ContAction rho := by
  unfold ReciprocityTheory.Gal.ContAction
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, m⟩
  have hU' : (fun x : Γ => g⁻¹ * x) ⁻¹' (U : Set Γ) ∈ 𝓝 g :=
    (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using U.one_mem)
  have hm : ({m} : Set M) ∈ 𝓝 m := (isOpen_discrete _).mem_nhds rfl
  filter_upwards [prod_mem_nhds hU' hm] with x hx
  have hx2' : x.2 = m := hx.2
  have hx1' : g⁻¹ * x.1 ∈ U := hx.1
  show rho x.1 x.2 = rho g m
  calc rho x.1 x.2 = rho (g * (g⁻¹ * x.1)) m := by rw [mul_inv_cancel_left, hx2']
    _ = rho g (rho (g⁻¹ * x.1) m) := by rw [map_mul]; rfl
    _ = rho g m := by rw [h1 _ hx1']; rfl

theorem twist_sub_bijective {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) (c : k) (hc : c ≠ 0)
    (hne : ¬ A.charpoly.IsRoot c) :
    Function.Bijective (fun v : Fin n → k => c⁻¹ • Matrix.toLin' A v - v) := by
  let f : (Fin n → k) →ₗ[k] (Fin n → k) := c⁻¹ • Matrix.toLin' A - LinearMap.id
  have hf : ∀ v, f v = c⁻¹ • Matrix.toLin' A v - v := fun v => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, hf, sub_eq_zero] at hv
    rw [Submodule.mem_bot]
    by_contra h0
    apply hne
    rw [← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    have hAv : Matrix.toLin' A v = c • v := by
      calc Matrix.toLin' A v = c • (c⁻¹ • Matrix.toLin' A v) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        _ = c • v := by rw [hv]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 hAv, h0⟩
  have hbij : Function.Bijective f := ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  exact hbij

theorem hOneTwo_holds : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ D : D7, HOneTwo D := by
  intro hF hT hE D i rb w hwS hrb hnr e
  have hw : w ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i w (Or.inl hwS)
  haveI := resFin D.nd i
  haveI := resChar D.nd i
  letI : TopologicalSpace (IsLocalRing.ResidueField (D.nd.O i)) := ⊥
  haveI : DiscreteTopology (IsLocalRing.ResidueField (D.nd.O i)) := ⟨rfl⟩
  haveI : CharP (IsLocalRing.ResidueField (D.nd.O i)) (D.nd.l i ^ 1) := by rw [pow_one]; infer_instance
  letI : Module (ZMod (D.nd.l i ^ 1)) (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) :=
    Module.compHom _ (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i)))
  haveI : ContinuousConstSMul (ZMod (D.nd.l i ^ 1)) (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) :=
    ⟨fun _ => continuous_of_discreteTopology⟩
  let rho := (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e)).comp
    (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype
  let rhoZ : Representation (ZMod (D.nd.l i ^ 1)) ↥(Dec (F := D.host.E) (D.nd.plOm.1 w))
      (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) :=
    { toFun := fun g =>
        { toFun := rho g
          map_add' := map_add (rho g)
          map_smul' := fun c m => map_smul (rho g)
            (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i)) c) m }
      map_one' := LinearMap.ext fun m => show rho 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show rho (g * h) m = rho g (rho h m) by
        rw [map_mul]; rfl }
  have hrZ : ∀ g m, rhoZ g m = rho g m := fun _ _ => rfl

  have hU : IsOpen (((rb.ker ⊓ (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e).ker).comap
      (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype : Subgroup _) :
        Set ↥(Dec (F := D.host.E) (D.nd.plOm.1 w))) :=
    (hrb.1.inter (chiEpsBar_open D.nd i e)).preimage continuous_subtype_val
  have h1U : ∀ u ∈ ((rb.ker ⊓ (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e).ker).comap
      (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype), rhoZ u = 1 := by
    intro u hu
    have hu' := Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hu)
    have ha : rb (u : G D.host.E D.nd.Om) = 1 := MonoidHom.mem_ker.1 hu'.1
    have hc : Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e (u : G D.host.E D.nd.Om) = 1 := MonoidHom.mem_ker.1 hu'.2
    apply LinearMap.ext
    intro v
    show ((Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e (u : G D.host.E D.nd.Om) :
        (IsLocalRing.ResidueField (D.nd.O i))ˣ) : IsLocalRing.ResidueField (D.nd.O i)) •
        Matrix.toLin' ((rb (u : G D.host.E D.nd.Om) : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i))) v = v
    rw [ha, hc]
    simp
  have hcZ : ContAction rhoZ := contAction_of_open _ _ hU h1U

  have hγD : D.nd.gam0 i w ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := Ine_le_Dec _ (D.nd.locNd_chebotarevPlace_mem i w)
  have hc0 : IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)) ≠ 0 :=
    ((Units.isUnit (D.nd.chi i 1 (D.nd.gam0 i w))).map (IsLocalRing.residue (D.nd.O i))).ne_zero
  have hbij : Function.Bijective (fun v : Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i) =>
      rhoZ ⟨D.nd.gam0 i w, hγD⟩ v - v) := by
    have h2 : (fun v : Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i) =>
        rhoZ ⟨D.nd.gam0 i w, hγD⟩ v - v) = fun v =>
        (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)))⁻¹ •
          Matrix.toLin' ((rb (D.nd.gam0 i w) : GL _ _) :
          Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i))) v - v := by
      funext v
      show ((Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e (D.nd.gam0 i w) : (IsLocalRing.ResidueField (D.nd.O i))ˣ) :
        IsLocalRing.ResidueField (D.nd.O i)) • Matrix.toLin' ((rb (D.nd.gam0 i w) : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i))) v - v = _
      rw [Formalism.MainNotions.SumRepresentations.twisted_character_at_frobenius D.nd w hw e]
    rw [h2]
    exact twist_sub_bijective _ _ hc0 hnr
  have key := GlobalTheory.T.localCohomology_vanishes_tame_inertia_no_fixed hF hT hE D.host.E D.nd.Om (D.nd.l i)
    (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) (D.nd.plOm.1 w) w rhoZ (D.nd.plOm.2 w) hw hcZ
    ⟨⟨D.nd.gam0 i w, hγD⟩, D.nd.locNd_chebotarevPlace_mem i w, hbij⟩
  have hk := Formalism.MainNotions.N.CohomologyScalarsVanish.cohScalarsVanish (D.nd.l i ^ 1) (IsLocalRing.ResidueField (D.nd.O i))
    ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)) (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) rho rhoZ hrZ key
  exact ⟨hk.2.1, hk.2.2⟩

end GlobalTheory.HOneTwoLevel
