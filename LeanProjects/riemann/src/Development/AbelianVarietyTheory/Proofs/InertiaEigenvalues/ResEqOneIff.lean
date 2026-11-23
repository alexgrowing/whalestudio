import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByCyclotomicKernelEtalePhiSolutionMemWachStatement

noncomputable section

namespace GlobalTheory.HWL.EtMod

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

section Abstract

variable {O E R : Type} [CommRing O] [CommRing E] [CommRing R] [Algebra O E] [Algebra O R]
  {M M' : Type} [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower O R M]
  [AddCommGroup M'] [Module R M'] [Module O M'] [IsScalarTower O R M']

def jB (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) : (Fin r → E) →ₗ[O] M where
  toFun x := ∑ i, ι (x i) • e i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_assoc]

theorem jB_apply (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) (x : Fin r → E) :
    jB ι e x = ∑ i, ι (x i) • e i := rfl

theorem repr_jB (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) (x : Fin r → E) (i) :
    e.repr (jB ι e x) i = ι (x i) := by
  rw [jB_apply, e.repr_sum_self]

theorem jB_smul (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) (a : E) (x : Fin r → E) :
    jB ι e (a • x) = ι a • jB ι e x := by
  simp [jB_apply, Finset.smul_sum, mul_smul]

theorem jB_inj (ι : E →ₐ[O] R) (hι : Function.Injective ι) {r : ℕ} (e : Module.Basis (Fin r) R M) :
    Function.Injective (jB ι e) := fun x y h => funext fun i => hι (by
  rw [← repr_jB ι e, h, repr_jB])

theorem jB_single (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) (i) :
    jB ι e (Pi.single i 1) = e i := by
  apply e.repr.injective
  ext k
  rw [repr_jB, e.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : k = i
  · simp [h]
  · simp [h, Ne.symm h]

theorem jB_span (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) :
    Submodule.span R (Set.range (jB ι e)) = ⊤ := by
  rw [eq_top_iff, ← e.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨_, jB_single ι e i⟩

theorem mem_range_jB (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) (y : M)
    (h : ∀ i, e.repr y i ∈ Set.range ι) : ∃ x, jB ι e x = y := by
  choose x hx using h
  exact ⟨x, by simp [jB_apply, hx]⟩

theorem exists_lift (ι : E →ₐ[O] R) (hι : Function.Injective ι) {r r' : ℕ}
    (e : Module.Basis (Fin r) R M) (e' : Module.Basis (Fin r') R M') (F : M →ₗ[O] M')
    (σ : E → E) (hF : ∀ a y, F (ι a • y) = ι (σ a) • F y)
    (h : ∀ j i, e'.repr (F (e j)) i ∈ Set.range ι) :
    ∃ f : (Fin r → E) →ₗ[O] (Fin r' → E), ∀ x, jB ι e' (f x) = F (jB ι e x) := by
  choose y hy using fun j => mem_range_jB ι e' _ (h j)
  have h1 : ∀ x, ∃ z, jB ι e' z = F (jB ι e x) := fun x =>
    ⟨∑ j, σ (x j) • y j, by simp [map_sum, jB_smul, hy, jB_apply ι e, hF]⟩
  choose f hf using h1
  exact ⟨⟨⟨f, fun a b => jB_inj ι hι e' (by simp [hf])⟩,
    fun c a => jB_inj ι hι e' (by simp [hf])⟩, hf⟩

theorem repr_semi {r : ℕ} (e : Module.Basis (Fin r) R M) (F : M →ₗ[O] M) (σ : R → R)
    (hF : ∀ a y, F (a • y) = σ a • F y) (y : M) (i) :
    e.repr (F y) i = ∑ k, e.repr (F (e k)) i * σ (e.repr y k) := by
  have : F y = ∑ k, σ (e.repr y k) • F (e k) := by
    conv_lhs => rw [← e.sum_repr y]
    simp only [map_sum, hF]
  rw [this]
  simp [map_sum, mul_comm]

theorem isUnit_of_span {r : ℕ} (e : Module.Basis (Fin r) R M) (x : Fin r → M)
    (h : ∀ y, y ∈ Submodule.span R (Set.range x)) :
    IsUnit (Matrix.of fun i j => e.repr (x j) i).det := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun R).1 (h (e k))
  apply Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun j k => c k j)
  ext i k
  have := congrArg (fun y => e.repr y i) (hc k)
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, e.repr_self, Finsupp.single_apply] at this
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, mul_comm (e.repr _ _), this, eq_comm]

end Abstract

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {RW : Type} [CommRing RW] [Algebra O RW]

theorem act_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (g : G) (r : RW) (y : TW RW T) :
    TWact f T g (r • y) = f r • TWact f T g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWact, TensorProduct.smul_tmul']
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]

theorem phi_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (r : RW) (y : TW RW T) :
    TWmap f T (r • y) = f r • TWmap f T y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWmap, TensorProduct.smul_tmul']
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]

theorem act_mul (f f' f'' : RW →ₐ[O] RW) (hf : ∀ x, f x = f' (f'' x)) (T : LocLat G Qp LL O) (g h : G)
    (y : TW RW T) : TWact f T (g * h) y = TWact f' T g (TWact f'' T h y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have : T.actT (g * h) t = T.actT g (T.actT h t) := Subtype.ext (by
      change T.ρ (g * h) t = T.ρ g (T.ρ h t)
      rw [map_mul]; rfl)
    simp [TWact, this, hf]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem phi_act (φ f : RW →ₐ[O] RW) (hf : ∀ x, φ (f x) = f (φ x)) (T : LocLat G Qp LL O) (g : G)
    (y : TW RW T) : TWmap φ T (TWact f T g y) = TWact f T g (TWmap φ T y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWact, TWmap, hf]
  | add a b ha hb => simp only [map_add, ha, hb]

abbrev oneT (RW : Type) [CommRing RW] [Algebra O RW] {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) :
    TW RW T →ₗ[O] TW RW T' :=
  TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) ((f.f.restrictScalars O).restrict f.T_le)

theorem oneT_smul {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (r : RW) (y : TW RW T) :
    oneT RW f (r • y) = r • oneT RW f y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul a m =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul']
    rfl
  | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

theorem oneT_phi {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (φ : RW →ₐ[O] RW) (y : TW RW T) :
    oneT RW f (TWmap φ T y) = TWmap φ T' (oneT RW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWmap]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem oneT_act {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (φ : RW →ₐ[O] RW) (g : G)
    (y : TW RW T) : oneT RW f (TWact φ T g y) = TWact φ T' g (oneT RW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have : (f.f.restrictScalars O).restrict f.T_le (T.actT g t) =
        T'.actT g ((f.f.restrictScalars O).restrict f.T_le t) := Subtype.ext (f.equiv g t)
    simp [TWact, this]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem oneT_id (T : LocLat G Qp LL O) (y : TW RW T) : oneT RW (latId T) y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem oneT_comp {T T' T'' : LocLat G Qp LL O} (g : LatHom T'.L T''.L) (f : LatHom T.L T'.L)
    (y : TW RW T) : oneT RW (latComp g f) y = oneT RW g (oneT RW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem oneT_add {T T' : LocLat G Qp LL O} (f g : LatHom T.L T'.L)
    (y : TW RW T) : oneT RW (latAdd f g) y = oneT RW f y + oneT RW g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_add]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]; abel

theorem oneT_latSmul (T : LocLat G Qp LL O) (c : O)
    (y : TW RW T) : oneT RW (latSmul T c) y = c • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_smul]
    congr 1
    apply Subtype.ext
    change algebraMap O LL c • (t : T.V) = c • (t : T.V)
    rw [algebraMap_smul]
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]

theorem span_phi (φ : RW →ₐ[O] RW) (T : LocLat G Qp LL O) {r : ℕ}
    (e : Module.Basis (Fin r) RW (TW RW T)) (y : TW RW T) :
    y ∈ Submodule.span RW (Set.range fun j => TWmap φ T (e j)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have : a ⊗ₜ[O] t = a • TWmap φ T ((1 : RW) ⊗ₜ[O] t) := by
      simp [TWmap, TensorProduct.smul_tmul']
    rw [this, ← e.sum_repr ((1 : RW) ⊗ₜ[O] t), map_sum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
    rw [phi_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

variable {Γ : WGam PD LL O v n s} {R : WSer Γ} {RA : Type} [CommRing RA] [Algebra O RA]
  {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem exists_et (I : WIo R RA RW inclR φR gR πA)
    (hmul : ∀ g h x, gR (g * h) x = gR g (gR h x)) (hφ : ∀ g x, φR (gR g x) = gR g (φR x))
    (hinj : Function.Injective I.ioE) (hunit : ∀ x, IsUnit (I.ioE x) → IsUnit x)
    (hrat : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) R.EE) (A' : Matrix (Fin q) (Fin q) R.EE)
      (U : Matrix (Fin p) (Fin q) RW), IsUnit A → IsUnit A' →
      (∀ i j g, Γ.resΓ g = 1 → gR g (U i j) = U i j) →
      A.map I.ioE * U.map φR = U * A'.map I.ioE → ∀ i j, U i j ∈ Set.range I.ioE)
    (e : ∀ T : LocLat G Qp LL O, Module.Basis (Fin (Module.finrank O ↥T.L.T)) RW (TW RW T))
    (hfix : ∀ T g, Γ.resΓ g = 1 → ∀ i, TWact (gR g) T g (e T i) = e T i)
    (het : ∀ T i j, (e T).repr (TWmap φR T (e T j)) i ∈ Set.range I.ioE) : Nonempty (WEt I) := by
  classical
  choose A hA using het
  have hAu : ∀ T, IsUnit (Matrix.of (A T)) := fun T => by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply hunit
    have h := isUnit_of_span (e T) _ (span_phi φR T (e T))
    rw [AlgHom.map_det]
    convert h using 2
    ext i j
    exact hA T i j
  have key : ∀ (T : LocLat G Qp LL O) (q : ℕ) (x : Fin q → TW RW T) (Bm : Matrix (Fin q) (Fin q) R.EE),
      IsUnit Bm → (∀ g, Γ.resΓ g = 1 → ∀ j, TWact (gR g) T g (x j) = x j) →
      (∀ j, TWmap φR T (x j) = ∑ k, I.ioE (Bm k j) • x k) →
      ∀ j i, (e T).repr (x j) i ∈ Set.range I.ioE := by
    intro T q x Bm hB hx hφx j i
    refine hrat _ q (Matrix.of (A T)) Bm (Matrix.of fun i j => (e T).repr (x j) i) (hAu T) hB ?_ ?_ i j
    · intro i j g hg
      have h := repr_semi (e T) (TWact (gR g) T g) (gR g) (act_smul _ T g) (x j) i
      simp only [hx g hg, hfix T g hg, Module.Basis.repr_self, Finsupp.single_apply, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
      exact h.symm
    · ext i j
      have h := repr_semi (e T) (TWmap φR T) φR (phi_smul _ T) (x j) i
      rw [hφx] at h
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
        smul_eq_mul] at h
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, hA]
      rw [← h]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hφe : ∀ T j, TWmap φR T (e T j) = ∑ k, I.ioE (A T k j) • e T k := fun T j => by
    simp only [hA, Module.Basis.sum_repr]
  have h1 := fun T => exists_lift I.ioE hinj (e T) (e T) (TWmap φR T) R.φE
    (fun a y => by rw [phi_smul, I.ioE_φ]) (fun j i => ⟨_, hA T i j⟩)
  choose φD hφD using h1
  have h2 := fun T g => exists_lift I.ioE hinj (e T) (e T) (TWact (gR g) T g) (R.γE (Γ.resΓ g))
    (fun a y => by rw [act_smul, I.ioE_γ])
    (key T _ _ ((R.γE (Γ.resΓ g)).mapMatrix (Matrix.of (A T))) ((hAu T).map _)
      (fun h hh j => by
        rw [← act_mul _ _ _ (hmul h g), show h * g = g * (g⁻¹ * h * g) by group,
          act_mul _ _ _ (hmul g _), hfix T _ (by simp [hh])])
      (fun j => by
        rw [phi_act _ _ (hφ g), hφe, map_sum]
        simp only [act_smul, ← I.ioE_γ]
        rfl))
  choose γG hγG using h2
  have h3 := fun (T T' : LocLat G Qp LL O) (f : LatHom T.L T'.L) =>
    exists_lift I.ioE hinj (e T) (e T') (oneT RW f) id
    (fun a y => oneT_smul f _ y)
    (key T' _ _ (Matrix.of (A T)) (hAu T)
      (fun h hh j => by rw [← oneT_act, hfix T h hh])
      (fun j => by
        rw [← oneT_phi, hφe, map_sum]
        simp only [oneT_smul]
        rfl))
  choose mp hmp using h3
  have hker : ∀ T h, Γ.resΓ h = 1 → ∀ x, TWact (gR h) T h (jB I.ioE (e T) x) = jB I.ioE (e T) x := by
    intro T h hh x
    simp only [jB_apply, map_sum, act_smul, ← I.ioE_γ, hh, hfix T h hh, map_one, AlgHom.one_apply]
  choose sec hsec using Γ.resΓ_onto
  have hact : ∀ T g x, jB I.ioE (e T) (γG T (sec (Γ.resΓ g)) x) =
      TWact (gR g) T g (jB I.ioE (e T) x) := by
    intro T g x
    rw [hγG, show sec (Γ.resΓ g) = g * (g⁻¹ * sec (Γ.resΓ g)) by group, act_mul _ _ _ (hmul g _),
      hker T _ (by simp [hsec])]
  have hj := fun T => jB_inj I.ioE hinj (e T)
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI : Nontrivial R.EE := R.EE_inj.nontrivial
  exact ⟨{
    DD := fun T => Fin (Module.finrank O ↥T.L.T) → R.EE
    φD := φD
    φD_smul := fun T a x => hj T (by rw [hφD, jB_smul, jB_smul, phi_smul, hφD, I.ioE_φ])
    γD := fun T g => γG T (sec g)
    γD_smul := fun T g a x => hj T (by
      rw [hγG, jB_smul, jB_smul, act_smul, hγG, ← I.ioE_γ, hsec])
    γD_one := fun T x => hj T (by rw [hγG, hker T _ (hsec 1)])
    γD_mul := fun T g h x => hj T (by
      rw [hγG T (sec g), hγG T (sec h), ← act_mul _ _ _ (hmul _ _), ← hact, map_mul, hsec, hsec])
    φγ_comm := fun T g x => hj T (by rw [hφD, hγG, hγG, hφD, phi_act _ _ (hφ _)])
    DD_free := fun T => ⟨inferInstance, Module.finrank_fin_fun _⟩
    map := fun {T T'} f =>
      { toFun := mp T T' f
        map_add' := map_add _
        map_smul' := fun a x => hj T' (by
          rw [hmp, jB_smul, RingHom.id_apply, jB_smul, oneT_smul, hmp]) }
    map_φ := fun {T T'} f x => hj T' (by
      change jB _ _ (mp T T' f _) = jB _ _ (φD T' (mp T T' f x))
      rw [hmp, hφD, hφD, hmp, oneT_phi])
    map_γ := fun {T T'} f g x => hj T' (by
      change jB _ _ (mp T T' f _) = jB _ _ (γG T' _ (mp T T' f x))
      rw [hmp, hγG, hγG, hmp, oneT_act])
    map_id := fun T x => hj T ((hmp _ _ _ x).trans (oneT_id T _))
    map_comp := fun {T T' T''} g f x => hj T'' (by
      change jB _ _ (mp T T'' _ x) = jB _ _ (mp T' T'' g (mp T T' f x))
      rw [hmp, hmp, hmp, oneT_comp])
    map_latAdd := fun {T T'} f g x => hj T' (by
      change jB _ _ (mp T T' _ x) = jB _ _ (mp T T' f x + mp T T' g x)
      rw [map_add, hmp, hmp, hmp, oneT_add])
    map_latSmul := fun T c x => hj T (by
      change jB _ _ (mp T T _ x) = _
      rw [hmp, oneT_latSmul, map_smul])
    jD := fun T => jB I.ioE (e T)
    jD_smul := fun T => jB_smul _ _
    jD_φ := hφD
    jD_act := hact
    jD_inj := hj
    jD_span := fun T => jB_span _ _
    jD_map := fun {T T'} f x => hmp T T' f x }⟩

end Generic

section Concrete

theorem map_id_comm {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f g f' g' : W →ₐ[Z] W) (h : ∀ w, f (g w) = f' (g' w)) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f (Algebra.TensorProduct.map (AlgHom.id O O) g x) =
    Algebra.TensorProduct.map (AlgHom.id O O) f' (Algebra.TensorProduct.map (AlgHom.id O O) g' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a w => simp [h]

theorem map_id_comp {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f f' g' : W →ₐ[Z] W) (h : ∀ w, f w = f' (g' w)) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f x =
    Algebra.TensorProduct.map (AlgHom.id O O) f' (Algebra.TensorProduct.map (AlgHom.id O O) g' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a w => simp [h]

variable {l : ℕ} [Fact l.Prime]

theorem gRW_mul {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g h : GQ l) (x : RW LL) :
    AI.gRW LL (g * h) x = AI.gRW LL g (AI.gRW LL h x) :=
  map_id_comp _ _ _ (fun w => by simp) x

theorem phi_gRW {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) (x : RW LL) :
    φRW LL (AI.gRW LL g x) = AI.gRW LL g (φRW LL x) := by
  refine map_id_comm _ _ _ _ (fun w => ?_) x
  ext n
  change (WittVector.map (frobenius (Cb l) l)
      (WittVector.map (autCb l (AI.actT g)).toRingHom w)).coeff n =
    (WittVector.map (autCb l (AI.actT g)).toRingHom (WittVector.map (frobenius (Cb l) l) w)).coeff n
  simp [WittVector.map_coeff, frobenius_def]

theorem res_eq_one_iff {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l} (Γ : GamS P K s LL)
    (g : ↥(GK K)) : Γ.resΓ g = 1 ↔ P.χQ (g : GQ l) = 1 := by
  have h : algebraMap ↥(OL LL) ↥LL.1 (Γ.χΓ (Γ.resΓ g) : ↥(OL LL)) =
      algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) := by
    rw [Γ.χΓ_res g, P.PD_χ]
  constructor
  · intro hg
    rw [hg, map_one, Units.val_one, map_one] at h
    apply Units.ext
    apply (algebraMap ℚ_[l] ↥LL.1).injective
    rw [← h, Units.val_one, map_one]
  · intro hg
    rw [hg, Units.val_one, map_one] at h
    apply Γ.χΓ_inj
    rw [map_one]
    apply Units.ext
    exact Subtype.ext h

set_option maxHeartbeats 1000000 in

theorem nonempty_wEt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → (∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ e : Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (RW LL) (TW (RW LL) T), EtBasis I T e) → Nonempty (WEt I) := by
  intro l _ P AI K s LL hg Γ R I hI h
  choose e he using h
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.wachInclusion_injective_saturated_inter l P AI K s LL hg Γ R I hI
  refine exists_et I (fun g h x => gRW_mul AI LL _ _ x) (fun g x => phi_gRW AI LL _ x) h1 h2
    (fun p q A A' U hA hA' hU hφ => GlobalTheory.T.fixedByCyclotomicKernel_etalePhi_solution_mem_wach l P AI K s LL hg Γ R I hI p q A A' 0 U hA hA'
      (fun i j g hgK hχ => hU i j ⟨g, hgK⟩ ((res_eq_one_iff Γ _).2 hχ)) ?_) e
    (fun T g hg => (he T).1 g ((res_eq_one_iff Γ g).1 hg)) (fun T => (he T).2)
  rw [hφ, Matrix.map_zero _ (map_zero _), add_zero]

end Concrete

end GlobalTheory.HWL.EtMod
