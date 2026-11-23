import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLiftFormsEqGoodForms
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMtTieCoord

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.ThOrth

open Formalism.IndefR.CxPass.LevelOperators

theorem theta_eq_zero_of_orth {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {F : Type} [AddCommGroup F] [Module K F]
    {σ : K →+* ℂ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {j : F →ₛₗ[σ] V} {r : Representation K G F} {ρ : G → V →ₗ[ℂ] V} {gE : Representation ℂ G E} {Θ : V →ₗ[ℂ] E}
    (H : Hyp σ j r ρ gE Θ)
    (hRZ : Submodule.span ℂ (j '' ((LinearMap.range (LinearMap.adjoint Θ)).comap j : Set F)) =
      LinearMap.range (LinearMap.adjoint Θ))
    (e a : MonoidAlgebra K G) (he : opF r e ∘ₗ opF r e = opF r e)
    (hfix : ∀ y ∈ LinearMap.range Θ, opV σ (fun g => gE g) a y = y) (f : F) (hea : opF r e f = opF r a f)
    (horth : ∀ z ∈ ((LinearMap.range (LinearMap.adjoint Θ)).comap j ⊓ LinearMap.range (opF r e) : Submodule K F),
      ⟪j z, j f⟫_ℂ = 0) : Θ (j f) = 0 := by
  have h1 : Θ (j (opF r e f)) = Θ (j f) := by
    rw [hea, j_opF H.jr, theta_opV H.sp H.jr H.eq, hfix _ ⟨_, rfl⟩]
  have h2 : j (opF r e f) ∈ LinearMap.range (opV σ ρ e) := ⟨j f, (j_opF H.jr e f).symm⟩
  obtain ⟨u', hu', hθ⟩ := H.dn e he h2
  have hu'' : u' ∈ Submodule.span ℂ (j '' ((((LinearMap.range (LinearMap.adjoint Θ)).comap j) ⊓
      LinearMap.range (opF r e) : Submodule K F) : Set F)) := by
    rw [H.ratLev hRZ e he]
    exact hu'
  have h3 : ⟪u', j f⟫_ℂ = 0 := by
    have hle : Submodule.span ℂ (j '' ((((LinearMap.range (LinearMap.adjoint Θ)).comap j) ⊓
        LinearMap.range (opF r e) : Submodule K F) : Set F)) ≤ (Submodule.span ℂ {j f})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact horth z hz
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hu'')
  obtain ⟨⟨w, rfl⟩, -⟩ := hu'
  have h4 : Θ (LinearMap.adjoint Θ w - j f) = 0 := by
    rw [map_sub, hθ, h1, sub_self]
  have h5 : ⟪LinearMap.adjoint Θ w, LinearMap.adjoint Θ w - j f⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left, h4, inner_zero_right]
  rw [inner_sub_right, h3, sub_zero, inner_self_eq_zero] at h5
  rw [← h1, ← hθ, h5, map_zero]

theorem opF_lvlIdem_fix {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (H : Subgroup G) (ψ : H →* Kˣ) (v : V)
    (hv : ∀ a : H, ρ a.1 v = ((ψ a : Kˣ) : K) • v) : opF ρ (lvlIdem H ψ) v = v := by
  classical
  rw [opF_eq_lift]
  unfold lvlIdem
  rw [map_sum, LinearMap.sum_apply]
  have : ∀ h : H, MonoidAlgebra.lift K (V →ₗ[K] V) G ρ
      (MonoidAlgebra.single (h : G) ((Nat.card H : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K))) v = (Nat.card H : K)⁻¹ • v := by
    intro h
    rw [MonoidAlgebra.lift_single, LinearMap.smul_apply, hv, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul,
      inv_mul_cancel, map_one, Units.val_one, mul_one]
  rw [Finset.sum_congr rfl fun h _ => this h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne'), one_smul]

end GlobalTheory.Mem.ThOrth

namespace GlobalTheory.Mem.ThOrth

open Formalism.IndefR.CxPass.LevelOperators

set_option maxHeartbeats 4000000 in

theorem thG_eq_zero_of_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL), (∀ z, Formalism.DivisionValues.hform (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) x = 0) → R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y _Z hP hH i t x hx
  have hok := hH.ok
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak hP.char hH.aux.ex
  have hM := hc.models
  have hCore : GlobalTheory.Hk3.Core R.toRealDat F.lv2 := ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩
  have hL := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hok.ok2.irr i
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hM
  have hJ : (R.toCx3 F).JIsoL F.cv := Formalism.IndefR.Links.RealDat3.jIsoL_of (F := F) hM
  have hRZ : (R.toCx3 F).RatZ := (complex_data_conditions_base_level_of_primitive_links hok hH.sep hP.char hH.prim).ratZ
  have H := Formalism.IndefR.CxPass.lift_hypotheses_of_unitary hok hK F.cv (fun _ _ _ _ => rfl) hJ hH.prim.gUnit.2 hH.prim.gEquiv.2 i t
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 := ⟨hok.ok2.conj, hok.ok2.irr, hok.ok2.lifts i t⟩

  have hopE : opV A3.fam3.base3.v0.embedding (fun g => R.gWx F i g) (idemOf A3.A.X) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i) := by
    let mA : ((R.HW i (sg0 D A3.A)).H →ₗ[ℂ] (R.HW i (sg0 D A3.A)).H) →+
        (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H →ₗ[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H) :=
      { toFun := Tw.map (twAt D.what₂.embLL A3.A.v0), map_zero' := LinearMap.ext fun _ => rfl,
        map_add' := fun _ _ => LinearMap.ext fun _ => rfl }
    rw [show Tw.map (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i) = mA (GlobalTheory.Hk3.eH R.toRealDat i) from rfl]
    unfold opV GlobalTheory.Hk3.eH
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => LinearMap.ext fun y => ?_
    show cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((idemOf A3.A.X).coeff g)) •
        R.gW i (sg0 D A3.A) g (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) y) =
      RealDat.eC (A := A3.A) (sg0 D A3.A) g •
        R.gW i (sg0 D A3.A) g (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) y)
    rw [Formalism.IndefR.Links.emb_eq D.what₂.embLL A3.A.v0, cj_cj]
    rfl
  have hθ : ∀ (u : (R.toCx3 F).FLC i t),
      Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) =
        cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u) :=
    fun u => rfl
  have hfix : ∀ y ∈ LinearMap.range ((R.toCx3 F).θ' i t),
      opV A3.fam3.base3.v0.embedding (fun g => R.gWx F i g) (idemOf A3.A.X) y = y := by
    rintro _ ⟨u, rfl⟩
    rw [hopE]
    change Tw.mk (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i
      (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u))) =
      (R.toCx3 F).θ' i t u
    rw [hθ, map_smul, hL.2.2.2, ← hθ]
    rfl

  set ℓ := A3.A.fam.lvlA F.P0 F.ψ0 with hℓ
  set f0 := liftForm A3.A F.P0 F.ψ0 i t x with hf0
  have hf0l : f0 = GlobalTheory.Mem.LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r ℓ.P ℓ.ψ x := rfl
  have hlev : f0 ∈ lvlForms (A3.A.fam.L i t).S (A3.A.fam.L i t).r ℓ.P ℓ.ψ := by
    rw [← GlobalTheory.Mem.LiftForms.range_lvlForm]
    exact ⟨x, hf0l.symm⟩
  have hfix0 : opF (A3.A.fam.L i t).r (lvlIdem ℓ.P ℓ.ψ) f0 = f0 := by
    exact opF_lvlIdem_fix (A3.A.fam.L i t).r ℓ.P ℓ.ψ f0 hlev
  have hea : opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ) f0 = opF (A3.A.fam.L i t).r (idemOf A3.A.X) f0 := by
    rw [goodAt, opF_mul, LinearMap.comp_apply, hfix0]
    rfl
  have horth : ∀ z ∈ ((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) ⊓
      LinearMap.range (opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) : Submodule _ _),
      ⟪(R.toCx3 F).jL i t z, (R.toCx3 F).jL i t f0⟫_ℂ = 0 := by
    intro z hz
    have hZeq : (((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t)) ⊓
        LinearMap.range (opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) : Submodule _ _) =
        LinearMap.range ((A3.A.fam.L i t).toF ℓ ((R.toCx3 F).Zl i t)) := by
      refine Eq.trans ?_ (Formalism.IndefR.CxPass.LevelOperators.range_toF (A3.A.fam.L i t) ℓ _).symm
      rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq]
      rfl
    have hz' : z ∈ LinearMap.range ((A3.A.fam.L i t).toF ℓ ((R.toCx3 F).Zl i t)) := hZeq ▸ hz
    obtain ⟨c, rfl⟩ := hz'
    rw [← GlobalTheory.Mem.LiftForms.lvlForm_lE hB c]
    refine (hJ i t _ _).trans ?_
    have h0 : Formalism.DivisionValues.hform ((A3.A.fam.L i t).S.lvlH (A3.A.fam.L i t).r ℓ.P ℓ.ψ)
        ((A3.A.fam.L i t).lE ℓ ((R.toCx3 F).Zl i t) *ᵥ c) x = 0 := hx c
    show A3.fam3.base3.v0.embedding (CSDForm.csumForm (A3.A.fam.L i t).S _ _) = 0
    rw [CSDForm.csumForm_apply, hf0l, GlobalTheory.Mem.LiftForms.csum_lvlForm, h0, mul_zero, map_zero]
  have key := theta_eq_zero_of_orth H (hRZ.2 i t) (goodAt ℓ.X ℓ.P ℓ.ψ) (idemOf A3.A.X)
    (opF_goodAt_idem _ _ hok.ok2.irr _ _) hfix f0 hea horth
  have h2 := congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) key
  rw [hθ, hP.phs i, map_one, one_smul] at h2
  exact h2

end GlobalTheory.Mem.ThOrth

end
