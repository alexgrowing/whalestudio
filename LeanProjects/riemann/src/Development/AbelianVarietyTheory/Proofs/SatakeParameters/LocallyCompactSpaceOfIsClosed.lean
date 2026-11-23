import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatsushimaLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryRepR

noncomputable section

open GlobalTheory.BorelCoh GroundTheory.Automorphic MeasureTheory
open scoped Matrix ComplexOrder

namespace GlobalTheory.Mt.Adelic

section LC

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

end LC

section HeckeFam

variable {Gf : Type} [Group Gf] (Kf : Subgroup Gf)

def IsHeckeFam {n : ℕ} (z : Fin n → Gf) : Prop :=
  ∀ k ∈ Kf, (Finset.univ.val.map fun i => ((k * z i : Gf) : Gf ⧸ Kf)) =
    Finset.univ.val.map fun i => ((z i : Gf) : Gf ⧸ Kf)

variable {Kf}

theorem sum_heckeFam {M : Type*} [AddCommMonoid M] {n : ℕ} {z : Fin n → Gf} (hz : IsHeckeFam Kf z)
    (F : Gf ⧸ Kf → M) {k : Gf} (hk : k ∈ Kf) :
    ∑ i, F ((k * z i : Gf) : Gf ⧸ Kf) = ∑ i, F ((z i : Gf) : Gf ⧸ Kf) := by
  have h := congrArg (fun m => (m.map F).sum) (hz k hk)
  simpa only [Finset.sum_eq_multiset_sum, Multiset.map_map, Function.comp_def] using h

end HeckeFam

section Fix

variable {G Gf : Type} [Group G] [TopologicalSpace G] [Group Gf] [TopologicalSpace Gf]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def infRep (π : UnitaryRep (G × Gf) H) : UnitaryRep G H where
  toHom := π.toHom.comp (MonoidHom.inl G Gf)
  continuous_orbit' v := (π.continuous_orbit v).comp (continuous_id.prodMk continuous_const)

theorem infRep_apply (π : UnitaryRep (G × Gf) H) (g : G) (v : H) : infRep π g v = π (g, 1) v := rfl

def fixSub (π : UnitaryRep (G × Gf) H) (Kf : Subgroup Gf) : Submodule ℂ H where
  carrier := {v | ∀ k ∈ Kf, π (1, k) v = v}
  add_mem' {a b} ha hb k hk := by simp only [Set.mem_setOf_eq, map_add, ha k hk, hb k hk]
  zero_mem' k _ := map_zero _
  smul_mem' c v hv k hk := by simp only [Set.mem_setOf_eq, map_smul, hv k hk]

variable (π : UnitaryRep (G × Gf) H) (Kf : Subgroup Gf)

theorem mem_fixSub {v : H} : v ∈ fixSub π Kf ↔ ∀ k ∈ Kf, π (1, k) v = v := Iff.rfl

theorem isClosed_fixSub : IsClosed (fixSub π Kf : Set H) := by
  have e : (fixSub π Kf : Set H) = ⋂ k ∈ Kf, {v | π (1, k) v = v} := by
    ext v; simp [mem_fixSub]
  rw [e]
  exact isClosed_biInter fun k _ => isClosed_eq (π (1, k)).continuous continuous_id

instance completeSpace_fixSub : CompleteSpace (fixSub π Kf) := (isClosed_fixSub π Kf).completeSpace_coe

theorem isInvariant_fixSub : (infRep π).IsInvariant (fixSub π Kf) := by
  intro g v hv k hk
  rw [infRep_apply, ← UnitaryRep.map_mul_apply,
    show ((1 : G), k) * (g, 1) = (g, 1) * (1, k) by ext <;> simp, UnitaryRep.map_mul_apply, hv k hk]

def fixRep : UnitaryRep G (fixSub π Kf) := (infRep π).restrict _ (isInvariant_fixSub π Kf)

variable {π Kf}

theorem op_fix_congr {v : H} (hv : v ∈ fixSub π Kf) {x y : Gf} (h : (x : Gf ⧸ Kf) = y) :
    π (1, x) v = π (1, y) v := by
  rw [QuotientGroup.eq] at h
  rw [show ((1 : G), y) = (1, x) * (1, x⁻¹ * y) by ext <;> simp, UnitaryRep.map_mul_apply, hv _ h]

theorem heckeVec_mem {n : ℕ} {z : Fin n → Gf} (hz : IsHeckeFam Kf z) {v : H} (hv : v ∈ fixSub π Kf) :
    (∑ i, π (1, z i)) v ∈ fixSub π Kf := by
  intro k hk
  let F : Gf ⧸ Kf → H := fun y => π (1, y.out) v
  have hF : ∀ x : Gf, π (1, x) v = F (x : Gf ⧸ Kf) := fun x =>
    op_fix_congr hv (QuotientGroup.out_eq' (x : Gf ⧸ Kf)).symm
  simp only [ContinuousLinearMap.sum_apply, map_sum]
  calc ∑ i, π (1, k) (π (1, z i) v) = ∑ i, F ((k * z i : Gf) : Gf ⧸ Kf) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← UnitaryRep.map_mul_apply, show ((1 : G), k) * (1, z i) = (1, k * z i) by ext <;> simp, hF]
    _ = ∑ i, F ((z i : Gf) : Gf ⧸ Kf) := sum_heckeFam hz F hk
    _ = ∑ i, π (1, z i) v := Finset.sum_congr rfl fun i _ => (hF _).symm

def heckeOp {n : ℕ} {z : Fin n → Gf} (hz : IsHeckeFam Kf z) : fixSub π Kf →L[ℂ] fixSub π Kf :=
  ((∑ i, π (1, z i)).comp (fixSub π Kf).subtypeL).codRestrict (fixSub π Kf) fun v => heckeVec_mem hz v.2

theorem coe_heckeOp {n : ℕ} {z : Fin n → Gf} (hz : IsHeckeFam Kf z) (v : fixSub π Kf) :
    ((heckeOp hz v : fixSub π Kf) : H) = ∑ i, π (1, z i) (v : H) := by
  show (∑ i, π (1, z i)) (v : H) = _
  exact ContinuousLinearMap.sum_apply _ _ _

theorem heckeOp_fixRep {n : ℕ} {z : Fin n → Gf} (hz : IsHeckeFam Kf z) (g : G) (v : fixSub π Kf) :
    heckeOp hz (fixRep π Kf g v) = fixRep π Kf g (heckeOp hz v) := by
  apply Subtype.ext
  rw [coe_heckeOp]
  show _ = π (g, 1) ((heckeOp hz v : fixSub π Kf) : H)
  rw [coe_heckeOp, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show π (1, z i) (π (g, 1) (v : H)) = _
  rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply,
    show ((1 : G), z i) * (g, 1) = (g, 1) * (1, z i) by ext <;> simp]

end Fix

end GlobalTheory.Mt.Adelic

namespace GlobalTheory.Mt.Adelic

section Rel

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (D : CartanData G 𝔤)

section Coch

variable {P M : Type} [AddCommGroup P] [Module ℝ P] [AddCommGroup M] [Module ℂ M] [Module ℝ M]
  [IsScalarTower ℝ ℂ M]

def postL (Φ : Module.End ℂ M) (q : ℕ) : (P [⋀^Fin q]→ₗ[ℝ] M) →ₗ[ℂ] (P [⋀^Fin q]→ₗ[ℝ] M) where
  toFun f := (Φ.restrictScalars ℝ).compAlternatingMap f
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp

theorem postL_apply (Φ : Module.End ℂ M) {q : ℕ} (f : P [⋀^Fin q]→ₗ[ℝ] M) (v : Fin q → P) :
    postL Φ q f v = Φ (f v) := rfl

theorem gd_postL (L : P →ₗ[ℝ] Module.End ℂ M) (Φ : Module.End ℂ M) (hΦ : ∀ X m, Φ (L X m) = L X (Φ m))
    {q : ℕ} (f : P [⋀^Fin q]→ₗ[ℝ] M) : gd L (postL Φ q f) = postL Φ (q + 1) (gd L f) := by
  ext v
  simp [gd, AlternatingMap.alternatizeUncurryFin_apply, postL_apply, map_sum, hΦ]

theorem relCo_postL {K : Type} (ad : K → P → P) (κ : K → Module.End ℂ M) (Φ : Module.End ℂ M)
    (hκ : ∀ k m, Φ (κ k m) = κ k (Φ m)) {q : ℕ} {f : P [⋀^Fin q]→ₗ[ℝ] M} (hf : f ∈ relCo ad κ ⊤ q) :
    postL Φ q f ∈ relCo ad κ ⊤ q :=
  ⟨fun k X => by simp only [postL_apply, hf.1 k X, hκ], fun _ => Submodule.mem_top⟩

end Coch

section Hrel

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  (L : D.p →ₗ[ℝ] Module.End ℂ M) (κ : D.K → Module.End ℂ M) (Φ : Module.End ℂ M)
  (hL : ∀ X m, Φ (L X m) = L X (Φ m)) (hK : ∀ k m, Φ (κ k m) = κ k (Φ m))

include hL hK in
theorem cocyc_le_comap (q : ℕ) : D.cocyc L κ q ≤ (D.cocyc L κ q).comap (postL Φ q) := by
  refine Submodule.span_le.2 fun f hf => Submodule.subset_span ⟨relCo_postL D.adP κ Φ hK hf.1, ?_⟩
  rw [gd_postL L Φ hL, hf.2]
  ext v; simp [postL_apply]

include hL hK in
theorem cobd_le_comap (q : ℕ) : D.cobd L κ q ≤ (D.cobd L κ q).comap (postL Φ q) := by
  cases q with
  | zero => intro f hf; rw [CartanData.cobd, Submodule.mem_bot] at hf; subst hf; simp [CartanData.cobd]
  | succ q =>
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact Submodule.subset_span ⟨postL Φ q f, relCo_postL D.adP κ Φ hK hf, gd_postL L Φ hL f⟩

def hrelMap (q : ℕ) : D.Hrel L κ q →ₗ[ℂ] D.Hrel L κ q :=
  Submodule.mapQ _ _ ((postL Φ q).restrict fun f hf => cocyc_le_comap D L κ Φ hL hK q hf)
    fun f hf => cobd_le_comap D L κ Φ hL hK q hf

end Hrel

section Smooth

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
  (T : H →L[ℂ] H) (hT : ∀ g v, T (π g v) = π g (T v))

include hT in
theorem expOrbit_op (v : H) : D.lie.expOrbit (CartanData.toBanach π) (T v) =
    (T.restrictScalars ℝ) ∘ D.lie.expOrbit (CartanData.toBanach π) v := by
  funext Y
  exact (hT _ v).symm

include hT in
theorem smooth_op {v : H} (hv : v ∈ D.SmV π) : T v ∈ D.SmV π := by
  have hv' : D.lie.IsSmoothVector (CartanData.toBanach π) v := hv
  show D.lie.IsSmoothVector (CartanData.toBanach π) (T v)
  rw [IsExpLieAlgebra.isSmoothVector_iff] at hv' ⊢
  rw [expOrbit_op D π T hT]
  exact (T.restrictScalars ℝ).contDiff.comp hv'

include hT in
theorem derivOp_op {v : H} (hv : v ∈ D.SmV π) (X : 𝔤) :
    D.lie.derivOp (CartanData.toBanach π) X (T v) = T (D.lie.derivOp (CartanData.toBanach π) X v) := by
  have hv' : D.lie.IsSmoothVector (CartanData.toBanach π) v := hv
  unfold IsExpLieAlgebra.derivOp
  rw [expOrbit_op D π T hT,
    ((T.restrictScalars ℝ).hasFDerivAt.comp 0
      (D.lie.differentiable_expOrbit (CartanData.toBanach π) hv' 0).hasFDerivAt).fderiv]
  rfl

def opS : Module.End ℂ (D.SmV π) :=
  (T : H →ₗ[ℂ] H).restrict fun _ hv => smooth_op D π T hT hv

def opT (d : ℕ) : Module.End ℂ (Fin d → D.SmV π) :=
  LinearMap.pi fun i => (opS D π T hT).comp (LinearMap.proj i)

theorem opT_apply {d : ℕ} (w : Fin d → D.SmV π) (i : Fin d) : opT D π T hT d w i = opS D π T hT (w i) := rfl

variable {d : ℕ} (ξ : G →* Matrix (Fin d) (Fin d) ℂ)

theorem opS_dOp (X : 𝔤) (v : D.SmV π) : opS D π T hT (D.dOp π X v) = D.dOp π X (opS D π T hT v) :=
  Subtype.ext (derivOp_op D π T hT v.2 X).symm

theorem opS_gOp (g : G) (v : D.SmV π) : opS D π T hT (D.gOp π g v) = D.gOp π g (opS D π T hT v) :=
  Subtype.ext (hT g v)

theorem opT_tOp (X : 𝔤) (w : Fin d → D.SmV π) :
    opT D π T hT d (D.tOp π ξ X w) = D.tOp π ξ X (opT D π T hT d w) := by
  funext i
  simp only [opT_apply, CartanData.tOp, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add, map_sum, map_smul, opS_dOp]

theorem opT_gkL (X : D.p) (w : Fin d → D.SmV π) :
    opT D π T hT d (D.gkL π ξ X w) = D.gkL π ξ X (opT D π T hT d w) := by
  rw [CartanData.gkL, Module.Basis.constr_apply, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.map_smul_of_tower, opT_tOp]

theorem opT_gkK (k : D.K) (w : Fin d → D.SmV π) :
    opT D π T hT d (D.gkK π ξ k w) = D.gkK π ξ k (opT D π T hT d w) := by
  funext i
  simp only [opT_apply, CartanData.gkK, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, opS_gOp]

def hgkMap (q : ℕ) : D.HGK π ξ q →ₗ[ℂ] D.HGK π ξ q :=
  hrelMap D (D.gkL π ξ) (D.gkK π ξ) (opT D π T hT d) (opT_gkL D π T hT ξ) (opT_gkK D π T hT ξ) q

end Smooth

end Rel

end GlobalTheory.Mt.Adelic

namespace GlobalTheory.Mt.Adelic

section Left

variable {Γ₀ Gf : Type} [Group Γ₀] [Group Gf] (ρf : Γ₀ →* Gf) (Kf : Subgroup Gf)

abbrev yAct : MulAction Γ₀ (Gf ⧸ Kf) := MulAction.compHom (Gf ⧸ Kf) ρf

def funRepY {d : ℕ} (ξ₀ : Γ₀ →* Matrix (Fin d) (Fin d) ℂ) : Representation ℂ Γ₀ (Gf ⧸ Kf → Fin d → ℂ) :=
  @funRep Γ₀ _ (Gf ⧸ Kf) (yAct ρf Kf) d ξ₀

theorem funRepY_apply {d : ℕ} (ξ₀ : Γ₀ →* Matrix (Fin d) (Fin d) ℂ) (γ : Γ₀) (φ : Gf ⧸ Kf → Fin d → ℂ) (x : Gf) :
    funRepY ρf Kf ξ₀ γ φ (x : Gf ⧸ Kf) = ξ₀ γ *ᵥ φ ((ρf γ⁻¹ * x : Gf) : Gf ⧸ Kf) := rfl

variable {ρf Kf} {d : ℕ}

def heckeFunLin {n : ℕ} (z : Fin n → Gf) : (Gf ⧸ Kf → Fin d → ℂ) →ₗ[ℂ] (Gf ⧸ Kf → Fin d → ℂ) where
  toFun φ y := ∑ i, φ ((y.out * z i : Gf) : Gf ⧸ Kf)
  map_add' φ ψ := by ext y j; simp [Finset.sum_add_distrib]
  map_smul' c φ := by ext y j; simp [Finset.mul_sum]

theorem heckeFunLin_mk {n : ℕ} {z : Fin n → Gf} (hz : IsHeckeFam Kf z) (φ : Gf ⧸ Kf → Fin d → ℂ) (x : Gf) :
    heckeFunLin z φ (x : Gf ⧸ Kf) = ∑ i, φ ((x * z i : Gf) : Gf ⧸ Kf) := by
  set x' := (x : Gf ⧸ Kf).out
  have hx : x'⁻¹ * x ∈ Kf := QuotientGroup.eq.1 (QuotientGroup.out_eq' (x : Gf ⧸ Kf))
  show ∑ i, φ ((x' * z i : Gf) : Gf ⧸ Kf) = _
  have h := sum_heckeFam hz (fun w : Gf ⧸ Kf => φ (x' • w)) hx
  have h2 : ∀ i, x' * (x'⁻¹ * x * z i) = x * z i := fun i => by group
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, h2] at h
  exact h.symm

theorem heckeFunLin_comm {n : ℕ} {z : Fin n → Gf} (hz : IsHeckeFam Kf z) (ξ₀ : Γ₀ →* Matrix (Fin d) (Fin d) ℂ)
    (γ : Γ₀) (φ : Gf ⧸ Kf → Fin d → ℂ) :
    heckeFunLin z (funRepY ρf Kf ξ₀ γ φ) = funRepY ρf Kf ξ₀ γ (heckeFunLin z φ) := by
  funext y
  induction y using QuotientGroup.induction_on with
  | H x =>
    rw [heckeFunLin_mk hz, funRepY_apply, heckeFunLin_mk hz, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [funRepY_apply, mul_assoc]

def heckeMor {n : ℕ} {z : Fin n → Gf} (hz : IsHeckeFam Kf z) (ξ₀ : Γ₀ →* Matrix (Fin d) (Fin d) ℂ) :
    Rep.of (funRepY ρf Kf ξ₀) ⟶ Rep.of (funRepY ρf Kf ξ₀) :=
  Rep.ofHom
    { toLinearMap := heckeFunLin z
      isIntertwining' := fun γ => by
        ext φ : 1
        exact heckeFunLin_comm hz ξ₀ γ φ }

def heckeCoh {n : ℕ} {z : Fin n → Gf} (hz : IsHeckeFam Kf z) (ξ₀ : Γ₀ →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) :
    groupCohomology (Rep.of (funRepY ρf Kf ξ₀)) q →ₗ[ℂ] groupCohomology (Rep.of (funRepY ρf Kf ξ₀)) q :=
  ((groupCohomology.functor ℂ Γ₀ q).map (heckeMor hz ξ₀)).hom

end Left

end GlobalTheory.Mt.Adelic

namespace GlobalTheory.Mt.Adelic

section Int

variable {G : Type} [Group G] [TopologicalSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {H' : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

def postInt (σ : UnitaryRep G H') (π : UnitaryRep G H) (T : H →L[ℂ] H) (hT : ∀ g v, T (π g v) = π g (T v)) :
    σ.intertwiners π →ₗ[ℂ] σ.intertwiners π where
  toFun S := ⟨T ∘L (S : H' →L[ℂ] H), fun g v => by
    simp only [ContinuousLinearMap.comp_apply, S.2 g v, hT]⟩
  map_add' S S' := Subtype.ext (ContinuousLinearMap.comp_add _ _ _)
  map_smul' c S := Subtype.ext (ContinuousLinearMap.comp_smul _ _ _)

end Int

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (D : CartanData G 𝔤)

def MatsushimaAdelic : Prop :=
  ∀ (Gf : Type) [Group Gf] [TopologicalSpace Gf] [IsTopologicalGroup Gf] [LocallyCompactSpace Gf] [T2Space Gf]
    [TotallyDisconnectedSpace Gf] [SecondCountableTopology Gf] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace Gf] [BorelSpace Gf]
    (Γ₀ : Type) [Group Γ₀] (ρi : Γ₀ →* G) (ρf : Γ₀ →* Gf) [DiscreteTopology (ρi.prod ρf).range],
    CompactSpace (GlobalTheory.AutomorphicL2Unitary.Quot (ρi.prod ρf).range) →
    (∀ U : Subgroup Gf, IsOpen (U : Set Gf) → IsCompact (U : Set Gf) → {γ : Γ₀ | ρi γ = 1 ∧ ρf γ ∈ U}.Finite) →
    ∀ (μ : Measure (G × Gf)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (Kf : Subgroup Gf),
    IsOpen (Kf : Set Gf) → IsCompact (Kf : Set Gf) →
    ∀ (d : ℕ) (ξ : G →* Matrix (Fin d) (Fin d) ℂ), D.IsAdm ξ → ∀ q : ℕ,

      (∃ e : groupCohomology (Rep.of (funRepY ρf Kf (ξ.comp ρi))) q ≃ₗ[ℂ]
          D.HGK (fixRep (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf) ξ q,
        ∀ (n : ℕ) (z : Fin n → Gf) (hz : IsHeckeFam Kf z),
          e.toLinearMap ∘ₗ heckeCoh (ρf := ρf) hz (ξ.comp ρi) q =
            hgkMap D (fixRep (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf) (heckeOp hz) (heckeOp_fixRep hz) ξ q ∘ₗ
              e.toLinearMap) ∧

      FiniteDimensional ℂ (groupCohomology (Rep.of (funRepY ρf Kf (ξ.comp ρi))) q) ∧
      (∀ (s : Set (Submodule ℂ (fixSub (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf)))
        (hc : ∀ V : s, CompleteSpace (V : Submodule ℂ (fixSub (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf)))
        (hinv : ∀ V : s, (fixRep (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf).IsInvariant V),
        IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ (fixSub (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf))) (fun V => (V : Submodule ℂ (fixSub (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf)).subtypeₗᵢ) →
        (∀ V : s, letI := hc V; ((fixRep (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf).restrict V (hinv V)).IsIrreducible) →
        {V : s | letI := hc V;
          Nontrivial (D.HGK ((fixRep (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf).restrict V (hinv V)) ξ q)}.Finite ∧
        Module.finrank ℂ (groupCohomology (Rep.of (funRepY ρf Kf (ξ.comp ρi))) q) =
          ∑ᶠ V : s, letI := hc V;
            Module.finrank ℂ (D.HGK ((fixRep (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf).restrict V (hinv V)) ξ q)) ∧

      (∀ (m : ℕ) (Hσ : Fin m → Type) [∀ j, NormedAddCommGroup (Hσ j)] [∀ j, InnerProductSpace ℂ (Hσ j)]
        [∀ j, CompleteSpace (Hσ j)] (σ : ∀ j, UnitaryRep G (Hσ j)),
        (∀ j, (σ j).IsIrreducible) → (∀ i j, (σ i).IsEquivalent (σ j) → i = j) →
        (∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (τ : UnitaryRep G H'),
          τ.IsIrreducible → τ.intertwiners (fixRep (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf) ≠ ⊥ →
          Nontrivial (D.HGK τ ξ q) → ∃ j, τ.IsEquivalent (σ j)) →
        (∀ j, FiniteDimensional ℂ ((σ j).intertwiners (fixRep (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf))) ∧
        Module.finrank ℂ (groupCohomology (Rep.of (funRepY ρf Kf (ξ.comp ρi))) q) =
          ∑ j, Module.finrank ℂ ((σ j).intertwiners (fixRep (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf)) *
            Module.finrank ℂ (D.HGK (σ j) ξ q) ∧
        ∀ (n : ℕ) (z : Fin n → Gf) (hz : IsHeckeFam Kf z),
          LinearMap.trace ℂ _ (heckeCoh (ρf := ρf) hz (ξ.comp ρi) q) =
            ∑ j, LinearMap.trace ℂ _ (postInt (σ j) (fixRep (GlobalTheory.AutomorphicL2Unitary.Rurep (ρi.prod ρf).range μ) Kf) (heckeOp hz)
              (heckeOp_fixRep hz)) * (Module.finrank ℂ (D.HGK (σ j) ξ q) : ℂ))

end GlobalTheory.Mt.Adelic
