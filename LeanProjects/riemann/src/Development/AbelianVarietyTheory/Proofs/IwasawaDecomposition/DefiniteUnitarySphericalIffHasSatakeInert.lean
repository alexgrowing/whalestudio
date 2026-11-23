import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformiseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterSphericalUnramifiedUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.InertSatake

def transport {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (P : G ≃ₜ* H)
    (σ : SmIrr G) : SmIrr H where
  V := σ.V
  ρ := σ.ρ.comp P.symm.toMulEquiv.toMonoidHom
  smooth v := (σ.smooth v).preimage P.symm.continuous
  irred := by
    obtain ⟨h0, h⟩ := (CuspRep.isIrreducible_iff _).1 σ.irred
    refine (CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    have := hW (P g) v hv
    change σ.ρ (P.symm (P g)) v ∈ W at this
    rwa [P.symm_apply_apply] at this

theorem transport_apply {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (P : G ≃ₜ* H)
    (σ : SmIrr G) (g : G) (v : σ.V) : (transport P σ).ρ (P g) v = σ.ρ g v := by
  change σ.ρ (P.symm (P g)) v = _
  rw [P.symm_apply_apply]

theorem isAdmissible_transport {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (P : G ≃ₜ* H) (σ : SmIrr G) (h : IsAdmissible σ.ρ) : IsAdmissible (transport P σ).ρ := by
  refine ⟨(transport P σ).smooth, fun K ho hc => ?_⟩
  let K' : Subgroup G := K.comap P.toMulEquiv.toMonoidHom
  show FiniteDimensional ℂ (fixed (σ.ρ.comp P.symm.toMulEquiv.toMonoidHom) K)
  have e : fixed (σ.ρ.comp P.symm.toMulEquiv.toMonoidHom) K = fixed σ.ρ K' := by
    ext x
    rw [GlobalTheory.LGrp.mem_fixed, GlobalTheory.LGrp.mem_fixed]
    constructor
    · intro hx k hk
      have := hx (P k) hk
      change σ.ρ (P.symm (P k)) x = x at this
      rwa [P.symm_apply_apply] at this
    · intro hx k hk
      exact hx (P.symm k) (by change P (P.symm k) ∈ K; rwa [P.apply_symm_apply])
  rw [e]
  refine h.2 K' (ho.preimage P.continuous) ?_
  have : (K' : Set G) = P.toHomeomorph ⁻¹' (K : Set H) := rfl
  rw [this]
  exact P.toHomeomorph.isCompact_preimage.2 hc

variable {L : Type} [Field L] [TopologicalSpace L] [IsTopologicalRing L] {n : ℕ}

def conjEquiv (s : L →+* L) (b : GL (Fin n) L) (hb : cT s b.1 * 1 * b.1 = antiJ L n) :
    UJ s (1 : Matrix (Fin n) (Fin n) L) ≃ₜ* GU s n where
  toFun g := ⟨b⁻¹ * g * b, GlobalTheory.InertDoubleCoset.conj_mem_UJ s hb g.2⟩
  invFun h := ⟨b * h * b⁻¹, by simpa using GlobalTheory.InertDoubleCoset.conj_mem_UJ s (GlobalTheory.InertDoubleCoset.inv_frame s hb) h.2⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end GlobalTheory.InertSatake

open GlobalTheory.InertSatake in

theorem GlobalTheory.InertSatake.sph_iff_isSat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w →
    (π.Sph w ↔ ∃ α, π.IsSat w α) := by
  intro E _ _ _ n π w hun hns
  obtain ⟨π, rfl⟩ := AU.mk_surjective π
  show IsUnramU π.V w ↔ ∃ α, π.IsSat w α
  constructor
  · rintro ⟨φ, hφ, h0, hfix⟩
    obtain ⟨s, ϖ, q, hs, hU⟩ := GlobalTheory.T.unramified_nonsplit_exists_conj_involution_uniformiser E w hun hns
    obtain ⟨e, he⟩ := GlobalTheory.T.fixedPlace_unitaryLocalPoints_equiv_localUnitaryGroup E n w s hs hU.2.1
    obtain ⟨b, hbK, hb⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ hU (one_mem (GlobalTheory.LFun.KGL w n))
      (by rw [Units.val_one, cT_one])
    let P : locU n w ≃ₜ* GU s n := e.trans (conjEquiv s b hb)
    have hP : ∀ x : locU n w, ((P x : GU s n) : GL (Fin n) (w.adicCompletion E)) = b⁻¹ * cLoc w x.1 * b := fun x => by
      change b⁻¹ * (e x : GL (Fin n) _) * b = _
      rw [he]
    obtain ⟨σ0, hadm, hcomp⟩ := GlobalTheory.T.exists_admissible_localComponent_definiteUnitary E n π w
    obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
    obtain ⟨-, f, hf0, hfm, hf⟩ := hcomp
    let F : σ0.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
    have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
      have := congrArg Subtype.val (DFunLike.congr_fun h v)
      exact this)
    have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA E n) (locU n w) π.V σ0.V σ0.V π.rep (locU n w).subtype σ0.ρ σ0.ρ
      π.isIrreducible_rep σ0.irred σ0.irred (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.rep.comp (locU n w).subtype) σ0.ρ σ0.irred
      (fun i : σ0.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) => i.toLinearMap)
      (fun i g u => Representation.IntertwiningMap.isIntertwining _ _ i g u) {x | cLoc w x.1 ∈ GlobalTheory.LFun.KGL w n} ⟨φ, hφ⟩
      (fun h => h0 (congrArg Subtype.val h)) (fun k hk => Subtype.ext (hfix k.1 k.2 hk))
      (htop ▸ Submodule.mem_top)
    let σ1 := transport P σ0
    have hsph : GlobalTheory.LGrp.IsSpherical σ1.ρ (KU s n) := by
      refine (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, hv0⟩
      obtain ⟨x, rfl⟩ := P.surjective k
      rw [transport_apply]
      refine hv x ?_
      have h1 : ((P x : GU s n) : GL (Fin n) (w.adicCompletion E)) ∈ GLint (Fin n) (intL (w.adicCompletion E)) :=
        (Set.ext_iff.1 (GlobalTheory.LFun.IntPtsUnitary.coe_KU s n) (P x)).1 hk
      have h2 : cLoc w x.1 = b * (P x : GL (Fin n) (w.adicCompletion E)) * b⁻¹ := by rw [hP]; group
      show cLoc w x.1 ∈ GlobalTheory.LFun.KGL w n
      rw [h2]
      exact mul_mem (mul_mem hbK h1) (inv_mem hbK)
    obtain ⟨α, hα⟩ := GlobalTheory.T.exists_satake_parameter_spherical_unramifiedUnitary E w ϖ s q n hU σ1.V σ1.ρ σ1.irred (isAdmissible_transport P σ0 hadm) hsph
    refine ⟨α, s, ϖ, q, hs, hU, b, hbK, by have h := hb; rw [Units.val_one, Matrix.mul_one] at h; exact h, P.toMulEquiv.toMonoidHom, hP, σ1,
      ⟨σ1.irred, f, hf0, hfm, fun x u => ?_⟩, hα⟩
    change f (σ0.ρ (P.symm (P x)) u) = _
    rw [P.symm_apply_apply]
    exact hf x u
  · rintro ⟨α, s, ϖ, q, hs, hU, b, hbK, hb, p, hp, σ, ⟨-, f, hf0, hfm, hf⟩, hsat⟩
    obtain ⟨e, he⟩ := GlobalTheory.T.fixedPlace_unitaryLocalPoints_equiv_localUnitaryGroup E n w s hs hU.2.1
    have hb1 : cT s b.1 * 1 * b.1 = antiJ _ n := by rwa [Matrix.mul_one]
    have hsurj : Function.Surjective p := fun g => by
      let P := e.trans (conjEquiv s b hb1)
      have hP : ((P (P.symm g) : GU s n) : GL (Fin n) (w.adicCompletion E)) =
          b⁻¹ * cLoc w (P.symm g).1 * b := by
        change b⁻¹ * (e _ : GL (Fin n) _) * b = _
        rw [he]
      refine ⟨P.symm g, Subtype.ext ?_⟩
      rw [hp, ← hP, P.apply_symm_apply]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
    have hfv : f v ≠ 0 := by
      intro h
      have hker := ((CuspRep.isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) fun g u hu => by
        obtain ⟨x, rfl⟩ := hsurj g
        rw [LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hu, map_zero]
      rcases hker with h1 | h1
      · have m : v ∈ LinearMap.ker f := LinearMap.mem_ker.2 h
        rw [h1] at m
        exact hv0 ((Submodule.mem_bot ℂ).1 m)
      · exact hf0 (LinearMap.ker_eq_top.1 h1)
    refine ⟨f v, hfm v, hfv, fun x hx hk => ?_⟩
    have hpk : p ⟨x, hx⟩ ∈ KU s n := by
      refine (Set.ext_iff.1 (GlobalTheory.LFun.IntPtsUnitary.coe_KU s n) _).2 ?_
      show ((p ⟨x, hx⟩ : GU s n) : GL (Fin n) (w.adicCompletion E)) ∈ GLint (Fin n) (intL _)
      rw [hp]
      exact mul_mem (mul_mem (inv_mem hbK) hk) hbK
    refine (hf ⟨x, hx⟩ v).symm.trans ?_
    rw [GlobalTheory.LGrp.mem_fixed.1 hv _ hpk]
