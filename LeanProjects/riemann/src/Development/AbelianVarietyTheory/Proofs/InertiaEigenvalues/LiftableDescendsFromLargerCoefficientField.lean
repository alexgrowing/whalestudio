import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

noncomputable section

namespace GlobalTheory.CoefDescent

section General
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {E E' : Type} [Field E] [Algebra Qp E] [Field E'] [Algebra Qp E']
    {O O' : Type} [CommRing O] [Algebra O E] [CommRing O'] [Algebra O' E']

theorem blochKatoCocycle_comp_equivariant_map
    {V : Type} [AddCommGroup V] [Module E V] [Module Qp V] [IsScalarTower Qp E V]
    [Module O V] [IsScalarTower O E V] {ρ : Representation E G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul E V]
    {V' : Type} [AddCommGroup V'] [Module E' V'] [Module Qp V'] [IsScalarTower Qp E' V']
    [Module O' V'] [IsScalarTower O' E' V'] {ρ' : Representation E' G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul E' V']
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O') ρ') (φ : V →ₗ[Qp] V')
    (he : ∀ g x, φ (ρ g x) = ρ' g (φ x)) (hc : Continuous φ) (hT : ∀ x ∈ L.T, φ x ∈ L'.T)
    (c : G → V) (h : c ∈ latticeFiniteCocycles PD L) : (fun g => φ (c g)) ∈ latticeFiniteCocycles PD L' := by
  obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, -, x, hx⟩ := h
  have hz : (fun g => φ (c g)) ∈ continuousCocycles ρ' := by
    refine ⟨hc.comp hc1, fun g h => ?_⟩
    change φ (c (g * h)) = φ (c g) + ρ' g (φ (c h))
    rw [hc2, map_add, he]
  refine ⟨⟨hz, fun g _ => hT _ (hc3 g (Set.mem_univ g))⟩, hz, LinearMap.rTensor B φ x, fun g => ?_⟩
  have key : ∀ y : V ⊗[Qp] B, LinearMap.rTensor B φ (actVB PD ρ g y) =
      actVB PD ρ' g (LinearMap.rTensor B φ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actVB, he]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [← key, ← map_sub, ← hx, LinearMap.rTensor_tmul]

theorem liftF_of_retract
    {V₁ : Type} [AddCommGroup V₁] [Module E V₁] [Module Qp V₁] [IsScalarTower Qp E V₁]
    [Module O V₁] [IsScalarTower O E V₁] {ρ₁ : Representation E G V₁}
    [TopologicalSpace V₁] [ContinuousAdd V₁] [ContinuousConstSMul E V₁]
    {V₂ : Type} [AddCommGroup V₂] [Module E V₂] [Module Qp V₂] [IsScalarTower Qp E V₂]
    [Module O V₂] [IsScalarTower O E V₂] {ρ₂ : Representation E G V₂}
    [TopologicalSpace V₂] [ContinuousAdd V₂] [ContinuousConstSMul E V₂]
    {W₁ : Type} [AddCommGroup W₁] [Module E' W₁] [Module Qp W₁] [IsScalarTower Qp E' W₁]
    [Module O' W₁] [IsScalarTower O' E' W₁] {σ₁ : Representation E' G W₁}
    [TopologicalSpace W₁] [ContinuousAdd W₁] [ContinuousConstSMul E' W₁]
    {W₂ : Type} [AddCommGroup W₂] [Module E' W₂] [Module Qp W₂] [IsScalarTower Qp E' W₂]
    [Module O' W₂] [IsScalarTower O' E' W₂] {σ₂ : Representation E' G W₂}
    [TopologicalSpace W₂] [ContinuousAdd W₂] [ContinuousConstSMul E' W₂]
    {L₁ : Lattice (O := O) ρ₁} {L₂ : Lattice (O := O) ρ₂}
    {M₁ : Lattice (O := O') σ₁} {M₂ : Lattice (O := O') σ₂}
    (F : LatHom L₁ L₂) (F' : LatHom M₁ M₂)
    (ι : V₂ →ₗ[Qp] W₂) (R₁ : W₁ →ₗ[Qp] V₁) (R₂ : W₂ →ₗ[Qp] V₂)
    (ιe : ∀ g x, ι (ρ₂ g x) = σ₂ g (ι x)) (ιc : Continuous ι) (ιT : ∀ x ∈ L₂.T, ι x ∈ M₂.T)
    (R₁e : ∀ g x, R₁ (σ₁ g x) = ρ₁ g (R₁ x)) (R₁c : Continuous R₁) (R₁T : ∀ x ∈ M₁.T, R₁ x ∈ L₁.T)
    (R₂e : ∀ g x, R₂ (σ₂ g x) = ρ₂ g (R₂ x)) (R₂T : ∀ x ∈ M₂.T, R₂ x ∈ L₂.T)
    (hret : ∀ x, R₂ (ι x) = x) (hF : ∀ x, R₂ (F'.f x) = F.f (R₁ x))
    (e : ℕ) (h : F'.LiftF PD e) : F.LiftF PD e := by
  intro c hc
  have h1 := h _ (blochKatoCocycle_comp_equivariant_map PD L₂ M₂ ι ιe ιc ιT c hc)
  obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨y, hy, rfl⟩, hsum⟩ := Submodule.mem_sup.1 h1
  refine Submodule.mem_sup.2 ⟨_, ⟨_, blochKatoCocycle_comp_equivariant_map PD M₁ L₁ R₁ R₁e R₁c R₁T d hd, rfl⟩, _,
    ⟨R₂ y, R₂T y hy, rfl⟩, ?_⟩
  funext g
  have h2 := congrArg R₂ (congrFun hsum g)
  change R₂ (F'.f (d g) + (σ₂ g y - y)) = R₂ (((PD.p : O') ^ e) • ι (c g)) at h2
  change F.f (R₁ (d g)) + (ρ₂ g (R₂ y) - R₂ y) = ((PD.p : O) ^ e) • c g
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, hret, map_add, map_sub, hF, R₂e] at h2
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, h2]

end General

section Maps
variable {Qp E E' : Type} [Field Qp] [Field E] [Algebra Qp E] [Field E'] [Algebra Qp E']
  {V : Type} [AddCommGroup V] [Module E V] [Module Qp V] [IsScalarTower Qp E V]
  {V' : Type} [AddCommGroup V'] [Module E V'] [Module Qp V'] [IsScalarTower Qp E V']
  {k k' : ℕ}

def emb (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) : V →ₗ[Qp] (Fin k → E') :=
  LinearMap.pi fun i => j.toLinearMap ∘ₗ (b.coord i).restrictScalars Qp

theorem emb_apply (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) (v : V) (i : Fin k) :
    emb j b v i = j (b.repr v i) := rfl

def ret (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) : (Fin k → E') →ₗ[Qp] V :=
  (b.equivFun.symm.toLinearMap.restrictScalars Qp) ∘ₗ LinearMap.compLeft r (Fin k)

theorem ret_apply (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) (w : Fin k → E') :
    ret r b w = ∑ i, r (w i) • b i := by
  simp [ret, Module.Basis.equivFun_symm_apply]

theorem repr_ret (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) (w : Fin k → E') (i : Fin k) :
    b.repr (ret r b w) i = r (w i) := by
  rw [ret_apply]; simp [Finsupp.single_apply]

theorem ret_emb (j : E →ₐ[Qp] E') (r : E' →ₗ[Qp] E) (hr : ∀ a x, r (j a * x) = a * r x) (h1 : r 1 = 1)
    (b : Module.Basis (Fin k) E V) (v : V) : ret r b (emb j b v) = v := by
  refine b.ext_elem fun i => ?_
  have := hr (b.repr v i) 1
  rw [mul_one, h1, mul_one] at this
  rw [repr_ret, emb_apply, this]

theorem emb_map (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) (b' : Module.Basis (Fin k') E V')
    (f : V →ₗ[E] V') (v : V) :
    emb j b' (f v) = ((LinearMap.toMatrix b b' f).map j).mulVec (emb j b v) := by
  funext i
  have := congrFun (LinearMap.toMatrix_mulVec_repr b b' f v) i
  rw [emb_apply, ← this]
  simp [Matrix.mulVec, dotProduct, emb_apply]

theorem ret_map (j : E →ₐ[Qp] E') (r : E' →ₗ[Qp] E) (hr : ∀ a x, r (j a * x) = a * r x)
    (b : Module.Basis (Fin k) E V) (b' : Module.Basis (Fin k') E V')
    (f : V →ₗ[E] V') (w : Fin k → E') :
    ret r b' (((LinearMap.toMatrix b b' f).map j).mulVec w) = f (ret r b w) := by
  refine b'.ext_elem fun i => ?_
  have := congrFun (LinearMap.toMatrix_mulVec_repr b b' f (ret r b w)) i
  rw [repr_ret, ← this]
  simp [Matrix.mulVec, dotProduct, repr_ret, hr]

end Maps

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem liftF_descends : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {K₀ K B BdR : Type} [Field K₀] [Field K] [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B] [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR] (PD : PeriodData G ℚ_[l] K₀ K B BdR) (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) (r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1), (∀ a x, r (incl hL a * x) = a * r x) → r 1 = 1 → (∀ x ∈ OL LL', r x ∈ OL LL) → Continuous r → ∀ e : ℕ, (extHom hL hb₁ hb₂ F).LiftF PD e → F.LiftF PD e := by
  intro l _ G _ _ K₀ K B BdR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PD LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F r hr h1
    hint hrc e h
  have hincl : Continuous (incl hL) := continuous_subtype_val.subtype_mk _
  have retT : ∀ {T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k : ℕ} {b : Module.Basis (Fin k) ↥LL.1 T.V},
      IsLatBasis T b → ∀ x ∈ intVec LL' k, ret r b x ∈ T.L.T := by
    intro T k b hb x hx
    rw [ret_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    have := T.L.T.smul_mem (⟨r (x i), hint _ (hx i)⟩ : ↥(OL LL)) (hb.1 i)
    rwa [← algebraMap_smul ↥LL.1] at this
  refine liftF_of_retract PD F (extHom hL hb₁ hb₂ F) (emb (incl hL) b₂) (ret r b₁) (ret r b₂)
    (fun g x => emb_map (incl hL) b₂ b₂ (T₂.ρ g) x) ?_ ?_
    (fun g x => ret_map (incl hL) r hr b₁ b₁ (T₁.ρ g) x) ?_ (retT hb₁)
    (fun g x => ret_map (incl hL) r hr b₂ b₂ (T₂.ρ g) x) (retT hb₂)
    (ret_emb (incl hL) r hr h1 b₂) (fun x => ret_map (incl hL) r hr b₁ b₂ F.f x) e h
  · exact continuous_pi fun i => hincl.comp (IsModuleTopology.continuous_of_linearMap (b₂.coord i))
  · intro x hx i
    exact incl_integral hL (hb₂.2 x hx i)
  · have hc : Continuous (b₁.equivFun.symm.toLinearMap) := IsModuleTopology.continuous_of_linearMap _
    exact hc.comp (continuous_pi fun i => hrc.comp (continuous_apply i))

end GlobalTheory.CoefDescent
