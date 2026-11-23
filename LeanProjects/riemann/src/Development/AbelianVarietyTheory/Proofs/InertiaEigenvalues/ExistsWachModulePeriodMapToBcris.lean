import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SandZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocAinfUntiltEpsOneEqZeta

noncomputable section

namespace GlobalTheory.HWL.Cmp.PerMap

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

section Val

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {B : Type} [CommRing B] [Algebra Qp B]
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
    (β : RA →+* LL ⊗[Qp] B) (hβ : ∀ (o : O) (r : RA), β (o • r) = algebraMap O LL o • β r)

def βB (T : LocLat G Qp LL O) : TW RA T →+ T.V ⊗[Qp] B :=
  TensorProduct.liftAddHom
    { toFun := fun r =>
        { toFun := fun t => actS T.V B (β r) ((t : T.V) ⊗ₜ[Qp] (1 : B))
          map_zero' := by simp
          map_add' := fun a b => by simp [add_tmul] }
      map_zero' := by ext t; simp
      map_add' := fun a b => by ext t; simp }
    (fun o r t => by
      change actS T.V B (β (o • r)) ((t : T.V) ⊗ₜ[Qp] (1 : B)) =
        actS T.V B (β r) ((o • (t : T.V)) ⊗ₜ[Qp] (1 : B))
      rw [hβ, map_smul, LinearMap.smul_apply, ← map_smul, smul_tmul', algebraMap_smul])

theorem βB_tmul (T : LocLat G Qp LL O) (r : RA) (t : ↥T.L.T) :
    βB β hβ T (r ⊗ₜ[O] t) = actS T.V B (β r) ((t : T.V) ⊗ₜ[Qp] (1 : B)) := rfl

theorem βB_smul (T : LocLat G Qp LL O) (r : RA) (y : TW RA T) :
    βB β hβ T (r • y) = actS T.V B (β r) (βB β hβ T y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul a t => rw [smul_tmul', βB_tmul, βB_tmul, smul_eq_mul, map_mul, map_mul, Module.End.mul_apply]

theorem map_smul_semi {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (σ : RA →ₐ[O] RW) (f : M →ₗ[O] N) (r : RA) (y : RA ⊗[O] M) :
    TensorProduct.map σ.toLinearMap f (r • y) = σ r • TensorProduct.map σ.toLinearMap f y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul a t => simp [smul_tmul']

variable (inclR : RA →ₐ[O] RW)

theorem incl_smul (T : LocLat G Qp LL O) (r : RA) (y : TW RA T) :
    TWincl inclR T (r • y) = inclR r • TWincl inclR T y := map_smul_semi _ _ _ _

theorem incl_inj (hinj : Function.Injective inclR) (T : LocLat G Qp LL O) :
    Function.Injective (TWincl inclR T) := by
  haveI : Module.Free O ↥T.L.T := T.L.free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) inclR.toLinearMap hinj

def Val (T : LocLat G Qp LL O) (j : TW RW T) (z : T.V ⊗[Qp] B) : Prop :=
  ∃ (r : RA) (y : TW RA T), IsUnit (β r) ∧ TWincl inclR T y = inclR r • j ∧
    βB β hβ T y = actS T.V B (β r) z

variable {β hβ inclR}

theorem act_inj (T : LocLat G Qp LL O) {u : LL ⊗[Qp] B} (hu : IsUnit u) {z z' : T.V ⊗[Qp] B}
    (h : actS T.V B u z = actS T.V B u z') : z = z' :=
  ((Module.End.isUnit_iff _).mp (hu.map (actS T.V B))).1 h

theorem act_comm (T : LocLat G Qp LL O) (u u' : LL ⊗[Qp] B) (z : T.V ⊗[Qp] B) :
    actS T.V B u (actS T.V B u' z) = actS T.V B u' (actS T.V B u z) := by
  rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]

theorem Val.exists {T : LocLat G Qp LL O} {j : TW RW T} {r : RA} {y : TW RA T} (hr : IsUnit (β r))
    (hy : TWincl inclR T y = inclR r • j) : ∃ z, Val β hβ inclR T j z := by
  obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp (hr.map (actS T.V B))).2 (βB β hβ T y)
  exact ⟨z, r, y, hr, hy, hz.symm⟩

theorem Val.spec (hinj : Function.Injective inclR) {T : LocLat G Qp LL O} {j : TW RW T} {z : T.V ⊗[Qp] B}
    (h : Val β hβ inclR T j z) {r : RA} {y : TW RA T} (hy : TWincl inclR T y = inclR r • j) :
    βB β hβ T y = actS T.V B (β r) z := by
  obtain ⟨r₀, y₀, hu, h1, h2⟩ := h
  have h3 : r₀ • y = r • y₀ := incl_inj inclR hinj T (by
    rw [incl_smul, incl_smul, hy, h1, smul_comm])
  apply act_inj T hu
  rw [← βB_smul, h3, βB_smul, h2, act_comm]

theorem Val.unique (hinj : Function.Injective inclR) {T : LocLat G Qp LL O} {j : TW RW T} {z z' : T.V ⊗[Qp] B}
    (h : Val β hβ inclR T j z) (h' : Val β hβ inclR T j z') : z = z' := by
  obtain ⟨r₀, y₀, hu, h1, h2⟩ := h'
  apply act_inj T hu
  rw [← h.spec hinj h1, h2]

theorem Val.add {T : LocLat G Qp LL O} {j j' : TW RW T} {z z' : T.V ⊗[Qp] B}
    (h : Val β hβ inclR T j z) (h' : Val β hβ inclR T j' z') : Val β hβ inclR T (j + j') (z + z') := by
  obtain ⟨r, y, hu, h1, h2⟩ := h
  obtain ⟨r', y', hu', h1', h2'⟩ := h'
  refine ⟨r * r', r' • y + r • y', by rw [map_mul]; exact hu.mul hu', ?_, ?_⟩
  · rw [map_add, incl_smul, incl_smul, h1, h1', smul_smul, smul_smul, map_mul, smul_add, mul_comm (inclR r')]
  · rw [map_add, βB_smul, βB_smul, h2, h2', act_comm, map_mul, map_mul, map_add]
    rfl

theorem Val.smul {T : LocLat G Qp LL O} {j : TW RW T} {z : T.V ⊗[Qp] B}
    (h : Val β hβ inclR T j z) (a : RA) : Val β hβ inclR T (inclR a • j) (actS T.V B (β a) z) := by
  obtain ⟨r, y, hu, h1, h2⟩ := h
  refine ⟨r, a • y, hu, ?_, ?_⟩
  · rw [incl_smul, h1, smul_comm]
  · rw [βB_smul, h2, act_comm]

theorem Val.map {T T' : LocLat G Qp LL O} (f : T.V →ₗ[LL] T'.V) (fT : ↥T.L.T →ₗ[O] ↥T'.L.T)
    (hf : ∀ t, (fT t : T'.V) = f t) (σA : RA →ₐ[O] RA) (σW : RW →ₐ[O] RW) (hB : B →ₐ[Qp] B)
    (h1 : ∀ r, inclR (σA r) = σW (inclR r))
    (h2 : ∀ r, β (σA r) = Algebra.TensorProduct.map (AlgHom.id Qp LL) hB (β r))
    {j : TW RW T} {z : T.V ⊗[Qp] B} (h : Val β hβ inclR T j z) :
    Val β hβ inclR T' (TensorProduct.map σW.toLinearMap fT j) (AlgebraTensorModule.map f hB.toLinearMap z) := by
  obtain ⟨r, y, hu, h3, h4⟩ := h
  have e1 : ∀ y : TW RA T, TWincl inclR T' (TensorProduct.map σA.toLinearMap fT y) =
      TensorProduct.map σW.toLinearMap fT (TWincl inclR T y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a t => simp [TWincl, h1]
  have e2 : ∀ y : TW RA T, βB β hβ T' (TensorProduct.map σA.toLinearMap fT y) =
      AlgebraTensorModule.map f hB.toLinearMap (βB β hβ T y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a t =>
      rw [TensorProduct.map_tmul, βB_tmul, βB_tmul, map_actS, ← h2, hf]
      simp
  refine ⟨σA r, TensorProduct.map σA.toLinearMap fT y, by rw [h2]; exact hu.map _, ?_, ?_⟩
  · rw [e1, h3, map_smul_semi, h1]
  · rw [e2, h4, map_actS, h2]

end Val

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s}
    {R : WSer Γ} {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n}

theorem exists_isPer (Mo : WN E zl) (β : O ⊗[Zl] Ai →+* LL ⊗[Qp] B) (ιA : Ai →+* B) (ιdR : Ai →+* BdR) (p1 : Ai)
    (hβ₀ : ∀ (o : O) (w : Ai), β (o ⊗ₜ[Zl] w) = algebraMap O LL o ⊗ₜ[Qp] ιA w)
    (hdR : ∀ w, ιdR w = PD.ι (ιA w)) (hinj : Function.Injective inclR) (hu : IsUnit (ιA p1))
    (gA : G → (O ⊗[Zl] Ai →ₐ[O] O ⊗[Zl] Ai)) (hg1 : ∀ g r, inclR (gA g r) = gR g (inclR r))
    (hg2 : ∀ g r, β (gA g r) =
      Algebra.TensorProduct.map (AlgHom.id Qp LL) ((PD.actB g).toAlgHom.restrictScalars Qp) (β r))
    (φA : O ⊗[Zl] Ai →ₐ[O] O ⊗[Zl] Ai) (hφ1 : ∀ r, inclR (φA r) = φR (inclR r))
    (hφ2 : ∀ r, β (φA r) = Algebra.TensorProduct.map (AlgHom.id Qp LL) PD.φ (β r))
    (hS : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∃ m : ℕ, Sand Mo T ((1 : O) ⊗ₜ[Zl] (p1 ^ m))) :
    ∃ βdR bT, IsPer Mo (β.comp I.io.toRingHom) ιdR p1 βdR bT := by
  classical
  have hβ : ∀ (o : O) (r : O ⊗[Zl] Ai), β (o • r) = algebraMap O LL o • β r := by
    intro o r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [smul_add, map_add, ha, hb]
    | tmul a w => rw [smul_tmul', hβ₀, hβ₀, smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  have hex : ∀ T : LocLat G Qp LL O, ∀ x : ↥(Mo.N T), ∃ z, IsCrys PD T.ρ → Val β hβ inclR T (E.jD T x) z := by
    intro T x
    by_cases hT : IsCrys PD T.ρ
    · obtain ⟨m, hm, -⟩ := hS T hT
      obtain ⟨y, hy⟩ := hm x x.2
      have hun : IsUnit (β ((1 : O) ⊗ₜ[Zl] (p1 ^ m))) := by
        rw [hβ₀, map_one, map_pow]
        exact (hu.pow m).map (Algebra.TensorProduct.includeRight : B →ₐ[Qp] LL ⊗[Qp] B)
      obtain ⟨z, hz⟩ := Val.exists (hβ := hβ) hun hy
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hT⟩
  choose b hb using hex
  let bT : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B := fun T =>
    if hT : IsCrys PD T.ρ then
      AddMonoidHom.mk' (b T) (fun x y => (hb T (x + y) hT).unique hinj (by
        rw [Submodule.coe_add, map_add]
        exact (hb T x hT).add (hb T y hT)))
    else 0
  have hv : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ x : ↥(Mo.N T), Val β hβ inclR T (E.jD T x) (bT T x) := by
    intro T hT x
    simp only [bT, dif_pos hT]
    exact hb T x hT
  have hj : ∀ (T : LocLat G Qp LL O) (a : LetA O n) (x : E.DD T), E.jD T (a • x) = inclR (I.io a) • E.jD T x := by
    intro T a x
    rw [← algebraMap_smul R.EE a x, E.jD_smul, I.ioE_ext]
  refine ⟨fun T => (ιV PD (LL := LL) (V := T.V)).toAddMonoidHom.comp (βB β hβ T), bT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T a w t
    change ιV PD (LL := LL) (V := T.V) (βB β hβ T _) = _
    rw [βB_tmul, hβ₀, actS_tmul, hdR, mul_one, algebraMap_smul]
    rfl
  · intro T hT a x
    refine (hv T hT (a • x)).unique hinj ?_
    rw [Submodule.coe_smul, hj]
    exact (hv T hT x).smul _
  · intro T hT g x
    refine (hv T hT _).unique hinj ?_
    change Val β hβ inclR T (E.jD T (E.γD T (Γ.resΓ g) x)) _
    rw [E.jD_act]
    exact Val.map (T.ρ g) (T.actT g) (fun _ => rfl) (gA g) (gR g) _ (hg1 g) (hg2 g) (hv T hT x)
  · intro T hT x m hx
    refine (hv T hT _).unique hinj ?_
    change Val β hβ inclR T (E.jD T (R.Q ^ m • E.φD T x)) _
    rw [hj, E.jD_φ]
    exact (Val.map LinearMap.id LinearMap.id (fun _ => rfl) φA φR _ hφ1 hφ2 (hv T hT x)).smul _
  · intro T T' f hT hT' x hx
    refine (hv T' hT' _).unique hinj ?_
    change Val β hβ inclR T' (E.jD T' (E.map f x)) _
    rw [E.jD_map]
    exact Val.map (inclR := inclR) f.f _ (fun _ => rfl) (AlgHom.id O _) (AlgHom.id O _) (AlgHom.id Qp B) (fun _ => rfl)
      (fun r => by simp) (hv T hT x)
  · intro T hT x k y hy
    rw [← map_pow] at hy
    change ιV PD (LL := LL) (V := T.V) (βB β hβ T _) = _
    rw [(hv T hT x).spec hinj hy, Algebra.TensorProduct.tmul_pow, one_pow, hβ₀, map_one]
    refine (map_actS (LinearMap.id : T.V →ₗ[LL] T.V) (PD.ι.restrictScalars Qp) _ _).trans ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, actS_one_tmul, ← map_pow, hdR]
    rfl

omit [TopologicalSpace LL] in
theorem beta_map (β : O ⊗[Zl] Ai →+* LL ⊗[Qp] B) (ιA : Ai →+* B)
    (hβ₀ : ∀ (o : O) (w : Ai), β (o ⊗ₜ[Zl] w) = algebraMap O LL o ⊗ₜ[Qp] ιA w)
    (a : Ai →ₐ[Zl] Ai) (h : B →ₐ[Qp] B) (hc : ∀ w, ιA (a w) = h (ιA w)) (r : O ⊗[Zl] Ai) :
    β (Algebra.TensorProduct.map (AlgHom.id O O) a r) = Algebra.TensorProduct.map (AlgHom.id Qp LL) h (β r) := by
  induction r using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul o w => simp [hβ₀, hc]

theorem map_map_comm {Wc : Type} [CommRing Wc] [Algebra Zl Wc] (i : Ai →ₐ[Zl] Wc)
    (a : Ai →ₐ[Zl] Ai) (b : Wc →ₐ[Zl] Wc) (hc : ∀ w, i (a w) = b (i w)) (r : O ⊗[Zl] Ai) :
    Algebra.TensorProduct.map (AlgHom.id O O) i (Algebra.TensorProduct.map (AlgHom.id O O) a r) =
      Algebra.TensorProduct.map (AlgHom.id O O) b (Algebra.TensorProduct.map (AlgHom.id O O) i r) := by
  induction r using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul o w => simp [hc]

end Generic

variable {l : ℕ} [Fact l.Prime]

def frobA (l : ℕ) [Fact l.Prime] : Ainf l →ₐ[ℤ_[l]] Ainf l where
  toRingHom := WittVector.map (frobenius (OCb l) l)
  commutes' := fun x => map_zlW l _ x

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (E : WEt I) (Mo : NS E), (∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ → ∃ m : ℕ, Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL)) → ∃ βdR bT, IsPer Mo (β.comp I.io.toRingHom) (P.ιB.toRingHom.comp AI.ιA) AI.π₁ βdR bT := by
  intro l _ P AI hT K s LL _ Γ R I _ β hβ E Mo hS
  refine exists_isPer Mo β AI.ιA _ AI.π₁ hβ (fun w => (P.PD_ι K _).symm) (GlobalTheory.HWL.TensorWitt.main l LL).2.2.1
    ((GlobalTheory.TiedMu.tied_mu_units l P AI hT).1 1)
    (fun g => Algebra.TensorProduct.map (AlgHom.id _ _) (AI.actWHom (g : GQ l)).toAlgHom) (fun g r => ?_)
    (fun g r => ?_) (Algebra.TensorProduct.map (AlgHom.id _ _) (frobA l)) (fun r => ?_) (fun r => ?_) hS
  · refine map_map_comm (inclWA l) _ _ (fun w => ?_) r
    ext k
    exact (autCb_alg l (AI.actT (g : GQ l)) (w.coeff k)).symm
  · exact beta_map β AI.ιA hβ _ _ (fun w => (AI.ιA_act g w).trans (P.PD_actB K g _).symm) r
  · refine map_map_comm (inclWA l) _ _ (fun w => ?_) r
    ext k
    exact map_pow (algebraMap (OCb l) (Cb l)) (w.coeff k) l
  · refine beta_map β AI.ιA hβ _ _ (fun w => ?_) r
    refine Eq.trans ?_ ((AI.ιA_φ w).trans (P.PD_φ K _).symm)
    rw [WittVector.frobenius_eq_map_frobenius]
    rfl

end GlobalTheory.HWL.Cmp.PerMap
