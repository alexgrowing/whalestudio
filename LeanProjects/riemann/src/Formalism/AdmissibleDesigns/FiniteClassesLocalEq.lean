import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
import Formalism.AdmissibleDesigns.SelfGood
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
import Formalism.AdmissibleDesigns.RankReductionIdempotentOne

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KLift

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Formalism.NG Module

section Gen

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] (eO : O ≃+* Ow)

scoped instance (priority := low) modOw (V : Type) [AddCommGroup V] [Module (FractionRing O) V] : Module Ow (TrV e V) :=
  Module.compHom (TrV e V) (algebraMap Ow LL)

variable {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]

instance towOw : IsScalarTower Ow LL (TrV e V) :=
  ⟨fun a b v => by
    show (a • b) • v = (algebraMap Ow LL a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩

variable {e eO}

def tr (e : FractionRing O ≃+* LL) (v : V) : TrV e V := v

def untr (e : FractionRing O ≃+* LL) (v : TrV e V) : V := v

theorem smul_eO (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (a : O) (v : V) : (eO a • tr e v : TrV e V) = tr e (a • v) := by
  show (e.symm (algebraMap Ow LL (eO a))) • v = a • v
  rw [heO, RingEquiv.symm_apply_apply, algebraMap_smul]

theorem smul_Ow (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (c : Ow) (v : V) : (c • tr e v : TrV e V) = tr e (eO.symm c • v) := by
  rw [← smul_eO heO, RingEquiv.apply_symm_apply]

variable {M : Type} [AddCommGroup M] [Module O M] (j : M →ₗ[O] V)

variable (e eO) in

def latT (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a)) :
    Submodule Ow (TrV e V) where
  carrier := Set.range fun m => tr e (j m)
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add j a b⟩
  zero_mem' := ⟨0, map_zero j⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    refine ⟨eO.symm c • a, ?_⟩
    show tr e (j (eO.symm c • a)) = c • tr e (j a)
    rw [smul_Ow heO, map_smul]

theorem mem_latT (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (v : TrV e V) : v ∈ latT e eO j heO ↔ ∃ m, tr e (j m) = v := Iff.rfl

def MO (_eO : O ≃+* Ow) (M : Type) : Type := M

instance : AddCommGroup (MO eO M) := ‹AddCommGroup M›
instance : Module O (MO eO M) := ‹Module O M›
instance instModMO : Module Ow (MO eO M) := Module.compHom M eO.symm.toRingHom

def latMap (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a)) :
    MO eO M →ₗ[Ow] ↥(latT e eO j heO) where
  toFun m := ⟨tr e (j m), m, rfl⟩
  map_add' a b := Subtype.ext (map_add j a b)
  map_smul' c a := Subtype.ext (by
    show tr e (j (eO.symm c • (show M from a))) = c • tr e (j a)
    rw [smul_Ow heO, map_smul])

def latEquiv (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (hj : Function.Injective j) : MO eO M ≃ₗ[Ow] ↥(latT e eO j heO) :=
  LinearEquiv.ofBijective (latMap j heO)
    ⟨fun a b h => hj (congrArg Subtype.val h : tr e (j a) = tr e (j b)),
      fun ⟨_, m, hm⟩ => ⟨m, Subtype.ext hm⟩⟩

def basMO [Module.Free O M] : Basis (Module.Free.ChooseBasisIndex O M) O (MO eO M) := Module.Free.chooseBasis O M

theorem free_MO [Module.Free O M] : Module.Free Ow (MO eO M) :=
  Module.Free.of_basis ((basMO (eO := eO)).mapCoeffs eO (fun c (x : MO eO M) => by
    show eO.symm (eO c) • (show M from x) = c • (show M from x)
    rw [RingEquiv.symm_apply_apply]))

theorem finite_MO [Module.Finite O M] [Module.Free O M] : Module.Finite Ow (MO eO M) :=
  Module.Finite.of_basis ((basMO (eO := eO)).mapCoeffs eO (fun c (x : MO eO M) => by
    show eO.symm (eO c) • (show M from x) = c • (show M from x)
    rw [RingEquiv.symm_apply_apply]))

variable {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)

variable (e eO) in

def latOf (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (ρV : Representation O Γ V) (ρM : Representation O Γ M) (hj : Function.Injective j)
    (hjeq : ∀ γ m, j (ρM γ m) = ρV γ (j m))
    (hsp : ∀ v : V, ∃ c : O, c ≠ 0 ∧ ∃ m, j m = c • v) [Module.Finite O M] [Module.Free O M] :
    Lattice (O := Ow) (repL e ρV ι) where
  T := latT e eO j heO
  stable g := by
    rintro _ ⟨m, rfl⟩
    exact ⟨ρM (ι g) m, hjeq _ _⟩
  fg := by
    haveI := finite_MO (eO := eO) (M := M)
    haveI : Module.Finite Ow ↥(latT e eO j heO) := Module.Finite.equiv (latEquiv j heO hj)
    exact (Module.Finite.iff_fg).1 inferInstance
  free := by
    haveI := free_MO (eO := eO) (M := M)
    exact Module.Free.of_equiv (latEquiv j heO hj)
  span := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, hc, m, hm⟩ := hsp (untr e v)
    have hk : algebraMap O (FractionRing O) c ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
    have hv0 : untr e v = (algebraMap O (FractionRing O) c)⁻¹ • j m := by
      rw [hm, ← algebraMap_smul (FractionRing O) c (untr e v), smul_smul, inv_mul_cancel₀ hk, one_smul]
    have hv : v = e (algebraMap O (FractionRing O) c)⁻¹ • tr e (j m) := by
      show untr e v = e.symm (e (algebraMap O (FractionRing O) c)⁻¹) • j m
      rw [RingEquiv.symm_apply_apply, hv0]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

end Gen

section Lift

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  {e : FractionRing O ≃+* LL} {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {P Q VP VQ : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
  [AddCommGroup VP] [Module (FractionRing O) VP] [Module O VP] [IsScalarTower O (FractionRing O) VP]
  [AddCommGroup VQ] [Module (FractionRing O) VQ] [Module O VQ] [IsScalarTower O (FractionRing O) VQ]
  [Module.Finite O P] [Module.Free O P] [Module.Finite O Q] [Module.Free O Q]
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {ρP : Representation O Γ P} {ρQ : Representation O Γ Q} {ρVP : Representation O Γ VP}
  {ρVQ : Representation O Γ VQ} {jP : P →ₗ[O] VP} {jQ : Q →ₗ[O] VQ}
  (hjP : Function.Injective jP) (hjQ : Function.Injective jQ)
  (hjeqP : ∀ γ m, jP (ρP γ m) = ρVP γ (jP m)) (hjeqQ : ∀ γ m, jQ (ρQ γ m) = ρVQ γ (jQ m))
  (hspP : ∀ v : VP, ∃ c : O, c ≠ 0 ∧ ∃ m, jP m = c • v) (hspQ : ∀ v : VQ, ∃ c : O, c ≠ 0 ∧ ∃ m, jQ m = c • v)
  {ev : P →ₗ[O] Q} {f0 : VP →ₗ[O] VQ}
  (hf0 : ∀ γ v, f0 (ρVP γ v) = ρVQ γ (f0 v)) (hcomm : ∀ m, f0 (jP m) = jQ (ev m))

def latHom : LatHom (latOf e eO jP ι heO ρVP ρP hjP hjeqP hspP) (latOf e eO jQ ι heO ρVQ ρQ hjQ hjeqQ hspQ) where
  f := trL e f0
  equiv g x := hf0 (ι g) x
  cont := trL_cont e f0
  T_le := by
    rintro _ ⟨m, rfl⟩
    exact ⟨ev m, (hcomm m).symm⟩

theorem latHom_onto (hev : Function.Surjective ev) :
    (latHom ι heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm).Onto := by
  rintro _ ⟨q, rfl⟩
  obtain ⟨p, rfl⟩ := hev q
  exact ⟨tr e (jP p), ⟨p, rfl⟩, hcomm p⟩

theorem liftO_of_liftF (ℓ : ℕ) (hp : PD.p = ℓ) (hι : Function.Bijective ι) (hev : IsEquivMap ρP ρQ ev) (n : ℕ)
    (hL : (latHom ι heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm).LiftF PD n) :
    Formalism.RepresentationBoundsCohomology.JL.LiftO ℓ (finiteClassesModel e PD ι ρVP ρP jP) (finiteClassesModel e PD ι ρVQ ρQ jQ)
      (Formalism.RepresentationBoundsCohomology.JL.mapH1 ρP ρQ ev hev) n := by
  intro κ hκ
  obtain ⟨z, hz, rfl⟩ := hκ
  let σ : Γ ≃ G := (Equiv.ofBijective ι hι).symm
  have hισ : ∀ γ, ι (σ γ) = γ := fun γ => (Equiv.ofBijective ι hι).apply_symm_apply γ
  have hσι : ∀ g, σ (ι g) = g := fun g => (Equiv.ofBijective ι hι).symm_apply_apply g

  let c2 : G → TrV e VQ := fun g => tr e (jQ ((z : Γ → Q) (ι g)))
  have hz' : c2 ∈ finiteCocycles PD (repL e ρVQ ι) := hz
  have hc2 : c2 ∈ latticeFiniteCocycles PD (latOf e eO jQ ι heO ρVQ ρQ hjQ hjeqQ hspQ) :=
    ⟨⟨hz'.1, fun g _ => ⟨_, rfl⟩⟩, hz'⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hL c2 hc2)
  obtain ⟨c1, hc1, rfl⟩ := ha
  obtain ⟨y, ⟨q, rfl⟩, rfl⟩ := hb
  have hval : ∀ g, ∃ m, tr e (jP m) = c1 g := fun g => hc1.1.2 g (Set.mem_univ g)
  let z1 : Γ → P := fun γ => Classical.choose (hval (σ γ))
  have hz1 : ∀ γ, jP (z1 γ) = untr e (c1 (σ γ)) := fun γ => Classical.choose_spec (hval (σ γ))
  have hcoc : ∀ g h, c1 (g * h) = c1 g + repL e ρVP ι g (c1 h) := hc1.2.1.2
  have hσmul : ∀ γ δ, σ (γ * δ) = σ γ * σ δ := fun γ δ => hι.1 (by rw [hισ, ι.map_mul, hισ, hισ])
  have hz1c : z1 ∈ coZ1s ρP := by
    intro γ δ
    apply hjP
    rw [map_add, hz1, hz1, hjeqP, hz1, hσmul, hcoc]
    show untr e (c1 (σ γ)) + ρVP (ι (σ γ)) (untr e (c1 (σ δ))) = _
    rw [hισ]
  have hz1f : (fun g => tr e (jP (z1 (ι g)))) = c1 := by
    funext g
    show jP (z1 (ι g)) = untr e (c1 g)
    rw [hz1, hσι]
  refine ⟨Submodule.mkQ _ ⟨z1, hz1c⟩, ⟨⟨z1, hz1c⟩, ?_, rfl⟩, ?_⟩
  · show (fun g => tr e (jP (z1 (ι g)))) ∈ finiteCocycles PD (repL e ρVP ι)
    rw [hz1f]
    exact hc1.2

  have heq : ∀ g, (((PD.p : ℕ) : Ow) ^ n • c2) g =
      trL e f0 (c1 g) + (repL e ρVQ ι g (tr e (jQ q)) - tr e (jQ q)) := fun g => congrFun hab.symm g
  have heqV : ∀ γ, jQ (((ℓ : O) ^ n) • (z : Γ → Q) γ) =
      jQ (ev (z1 γ)) + (jQ (ρQ γ q) - jQ q) := by
    intro γ
    have h := heq (σ γ)
    rw [Pi.smul_apply, hp] at h
    have h1 : ((ℓ : Ow) ^ n) = eO ((ℓ : O) ^ n) := by rw [map_pow, map_natCast]
    rw [h1] at h
    have h2 := h
    simp only [c2] at h2
    rw [smul_eO heO, hισ] at h2
    rw [repL_apply, hισ] at h2
    rw [map_smul, ← hcomm, hz1, hjeqQ]
    exact h2
  show Submodule.mapQ _ _ _ _ (Submodule.Quotient.mk _) = _
  rw [Submodule.mapQ_apply, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine ⟨-q, funext fun γ => ?_⟩
  apply hjQ
  show jQ (ρQ γ (-q) - (-q)) = jQ (ev (z1 γ) - ((ℓ : O) ^ n) • (z : Γ → Q) γ)
  rw [map_sub, map_sub, heqV]
  simp only [map_neg]
  abel

end Lift

section FromAt

theorem finDim_of_lat {LL Ow : Type} [Field LL] [CommRing Ow] [Algebra Ow LL] {G : Type} [Group G]
    {Qp : Type} [Field Qp] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module Ow V]
    [IsScalarTower Ow LL V] {ρ : Representation LL G V} (L : Lattice (O := Ow) ρ) : FiniteDimensional LL V := by
  obtain ⟨s, hs⟩ := L.fg
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff, ← L.span, Submodule.span_le, ← hs]
  exact Submodule.span_le_restrictScalars Ow LL (s : Set V)

theorem subq_of_onto {LL : Type} [Field LL] {G : Type} [Group G] {V W : Type} [AddCommGroup V] [Module LL V]
    [AddCommGroup W] [Module LL W] {ρ : Representation LL G V} {ρ' : Representation LL G W}
    {ιx : Type} {k : ℕ} {Ms : ιx → G → Matrix (Fin k) (Fin k) LL} (f : V →ₗ[LL] W)
    (hf : Function.Surjective f) (heq : ∀ g v, f (ρ g v) = ρ' g (f v))
    (h : Formalism.MainNotions.N.IsSubquotOfSums ρ Ms) : Formalism.MainNotions.N.IsSubquotOfSums ρ' Ms := by
  obtain ⟨m, xs, U, q, hU, hq, hqe⟩ := h
  refine ⟨m, xs, U, f ∘ₗ q, hU, fun w => ?_, fun g u hu => ?_⟩
  · obtain ⟨v, rfl⟩ := hf w
    obtain ⟨u, hu, rfl⟩ := hq v
    exact ⟨u, hu, rfl⟩
  · rw [LinearMap.comp_apply, hqe g u hu, heq, LinearMap.comp_apply]

end FromAt

section Lift2

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL]
  {e : FractionRing O ≃+* LL} {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {P Q VP VQ : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
  [AddCommGroup VP] [Module (FractionRing O) VP] [Module O VP] [IsScalarTower O (FractionRing O) VP]
  [AddCommGroup VQ] [Module (FractionRing O) VQ] [Module O VQ] [IsScalarTower O (FractionRing O) VQ]
  [Module.Finite O P] [Module.Free O P] [Module.Finite O Q] [Module.Free O Q]
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {ρP : Representation O Γ P} {ρQ : Representation O Γ Q} {ρVP : Representation O Γ VP}
  {ρVQ : Representation O Γ VQ} {jP : P →ₗ[O] VP} {jQ : Q →ₗ[O] VQ}
  (hjP : Function.Injective jP) (hjQ : Function.Injective jQ)
  (hjeqP : ∀ γ m, jP (ρP γ m) = ρVP γ (jP m)) (hjeqQ : ∀ γ m, jQ (ρQ γ m) = ρVQ γ (jQ m))
  (hspP : ∀ v : VP, ∃ c : O, c ≠ 0 ∧ ∃ m, jP m = c • v) (hspQ : ∀ v : VQ, ∃ c : O, c ≠ 0 ∧ ∃ m, jQ m = c • v)
  {ev : P →ₗ[O] Q} {f0 : VP →ₗ[O] VQ}
  (hf0 : ∀ γ v, f0 (ρVP γ v) = ρVQ γ (f0 v)) (hcomm : ∀ m, f0 (jP m) = jQ (ev m))

include hspQ hcomm in

theorem trL_onto (hev : Function.Surjective ev) : Function.Surjective (trL e f0) := by
  intro v
  obtain ⟨c, hc, m, hm⟩ := hspQ (untr e v)
  obtain ⟨p, rfl⟩ := hev m
  have hk : algebraMap O (FractionRing O) c ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
  refine ⟨tr e ((algebraMap O (FractionRing O) c)⁻¹ • jP p), ?_⟩
  show f0 ((algebraMap O (FractionRing O) c)⁻¹ • jP p) = untr e v
  rw [smulK, hcomm, hm, ← algebraMap_smul (FractionRing O) c (untr e v), smul_smul, inv_mul_cancel₀ hk, one_smul]

include heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm in

theorem liftO_of_liftAt (ℓ : ℕ) (hp : PD.p = ℓ) (hι : Function.Bijective ι) (hev : IsEquivMap ρP ρQ ev)
    (hevs : Function.Surjective ev) {ιx : Type} {k : ℕ} (Ms : ιx → G → Matrix (Fin k) (Fin k) LL) (n : ℕ)
    (hA : Formalism.MainNotions.N.LiftAt PD (O := Ow) Ms n)
    (hcP : ∀ x, Continuous fun g => repL e ρVP ι g x)
    (hsP : Formalism.MainNotions.N.IsSubquotOfSums (repL e ρVP ι) Ms) :
    Formalism.RepresentationBoundsCohomology.JL.LiftO ℓ (finiteClassesModel e PD ι ρVP ρP jP) (finiteClassesModel e PD ι ρVQ ρQ jQ)
      (Formalism.RepresentationBoundsCohomology.JL.mapH1 ρP ρQ ev hev) n := by
  let L1 := latOf e eO jP ι heO ρVP ρP hjP hjeqP hspP
  let L2 := latOf e eO jQ ι heO ρVQ ρQ hjQ hjeqQ hspQ
  haveI := finDim_of_lat (Ow := Ow) (Qp := Qp) L1
  haveI := finDim_of_lat (Ow := Ow) (Qp := Qp) L2
  have hons : Function.Surjective (trL e f0) := trL_onto (hspQ := hspQ) (hcomm := hcomm) hevs
  have heq : ∀ g v, trL e f0 (repL e ρVP ι g v) = repL e ρVQ ι g (trL e f0 v) := fun g v => hf0 (ι g) v
  have hcQ : ∀ y, Continuous fun g => repL e ρVQ ι g y := by
    intro y
    obtain ⟨x, rfl⟩ := hons y
    have h : (fun g => repL e ρVQ ι g (trL e f0 x)) = fun g => trL e f0 (repL e ρVP ι g x) :=
      funext fun g => (heq g x).symm
    rw [h]
    exact (trL_cont e f0).comp (hcP x)
  have hsQ := subq_of_onto (trL e f0) hons heq hsP
  exact liftO_of_liftF PD ι heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm ℓ hp hι hev n
    (hA (TrV e VP) (repL e ρVP ι) L1 hcP hsP (TrV e VQ) (repL e ρVQ ι) L2 hcQ hsQ
      (latHom ι heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm)
      (latHom_onto ι heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm hevs))

end Lift2

section Rec

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem finite_classes_local_eq {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {V M : Type} [AddCommGroup V]
    [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V] [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
    [AddCommGroup M] [Module (D.nd.O i) M]
    (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V) (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M)
    (φ : M →ₗ[D.nd.O i] V) :
    finiteClassesCocyclesMap i dc n ρ ρM φ = finiteClassesModel (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Br.iota D.nbr i _ hn) ρ ρM φ := by
  unfold finiteClassesCocyclesMap fPre finiteClassesModel finPre
  rw [fZ_pos i dc ρ hn]
  rfl

theorem heO_br {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (a : D.nd.O i) :
    algebraMap (Br.Ow (D.nbr i _ hn)) (Br.LLw (D.nbr i _ hn)) ((D.nbr i _ hn).eO a) =
      eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a) :=
  (Br.toLLK_alg (D.nbr i _ hn) a).symm

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem liftO_col (eR : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hA : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc eR) (hG : K.SelfGood i)
    {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (hc : K.plOf i dc n ∈ dc.col)
    {P Q VP VQ : Type} [AddCommGroup P] [Module (D.nd.O i) P] [AddCommGroup Q] [Module (D.nd.O i) Q]
    [AddCommGroup VP] [Module (FractionRing (D.nd.O i)) VP] [Module (D.nd.O i) VP]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VP]
    [AddCommGroup VQ] [Module (FractionRing (D.nd.O i)) VQ] [Module (D.nd.O i) VQ]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VQ]
    [Module.Finite (D.nd.O i) P] [Module.Free (D.nd.O i) P] [Module.Finite (D.nd.O i) Q] [Module.Free (D.nd.O i) Q]
    {ρP : Representation (D.nd.O i) ↥(Γn i dc n) P} {ρQ : Representation (D.nd.O i) ↥(Γn i dc n) Q}
    {ρVP : Representation (D.nd.O i) ↥(Γn i dc n) VP} {ρVQ : Representation (D.nd.O i) ↥(Γn i dc n) VQ}
    {jP : P →ₗ[D.nd.O i] VP} {jQ : Q →ₗ[D.nd.O i] VQ}
    (hjP : Function.Injective jP) (hjQ : Function.Injective jQ)
    (hjeqP : ∀ γ m, jP (ρP γ m) = ρVP γ (jP m)) (hjeqQ : ∀ γ m, jQ (ρQ γ m) = ρVQ γ (jQ m))
    (hspP : ∀ v : VP, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m, jP m = c • v)
    (hspQ : ∀ v : VQ, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m, jQ m = c • v)
    {ev : P →ₗ[D.nd.O i] Q} {f0 : VP →ₗ[D.nd.O i] VQ}
    (hf0 : ∀ γ v, f0 (ρVP γ v) = ρVQ γ (f0 v)) (hcomm : ∀ m, f0 (jP m) = jQ (ev m))
    (hev : IsEquivMap ρP ρQ ev) (hevs : Function.Surjective ev)
    (hcP : ∀ x, Continuous fun g => repL (eK (D.nbr i _ hn)) ρVP (Br.iota D.nbr i _ hn) g x)
    (hsP : Formalism.MainNotions.N.IsSubquotOfSums (repL (eK (D.nbr i _ hn)) ρVP (Br.iota D.nbr i _ hn))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rTwO D.nd i r x)))) :
    Formalism.RepresentationBoundsCohomology.JL.LiftO (D.nd.l i) (finiteClassesCocyclesMap i dc n ρVP ρP jP) (finiteClassesCocyclesMap i dc n ρVQ ρQ jQ)
      (Formalism.RepresentationBoundsCohomology.JL.mapH1 ρP ρQ ev hev) (eR (K.plOf i dc n)) := by
  rw [finite_classes_local_eq i dc hn, finite_classes_local_eq i dc hn]
  have hbij : Function.Bijective (Br.iota D.nbr i _ hn) := (D.nbr i _ hn).e.symm.bijective
  exact liftO_of_liftAt (Br.PD D.loc D.nbr i _ hn) (Br.iota D.nbr i _ hn) (heO_br i dc hn)
    hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm (D.nd.l i) (Br.PD_p D.loc D.nbr i _ hn) hbij hev hevs _ _
    (hA _ hn hc (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (hG _ hn)) hcP hsP

end Rec

section Emb

theorem subq_of_inj {LL : Type} [Field LL] {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module LL V]
    {ρ : Representation LL G V} {ιx : Type} {k : ℕ} {Ms : ιx → G → Matrix (Fin k) (Fin k) LL}
    {m : ℕ} (xs : Fin m → ιx) (φ : V →ₗ[LL] (Fin m → Fin k → LL)) (hφ : Function.Injective φ)
    (heq : ∀ g v, φ (ρ g v) = fun a => (Ms (xs a) g).mulVec (φ v a)) : Formalism.MainNotions.N.IsSubquotOfSums ρ Ms := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ (LinearMap.ker_eq_bot.2 hφ)
  have hψv : ∀ v, ψ (φ v) = v := fun v => by rw [← LinearMap.comp_apply, hψ, LinearMap.id_apply]
  refine ⟨m, xs, LinearMap.range φ, ψ, ?_, fun v => ⟨φ v, ⟨v, rfl⟩, hψv v⟩, ?_⟩
  · rintro g _ ⟨v, rfl⟩
    exact ⟨ρ g v, heq g v⟩
  · rintro g _ ⟨v, rfl⟩
    rw [← heq, hψv, hψv]

theorem cont_of_inj {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] {G : Type} [Group G]
    [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    [ContinuousAdd V] [ContinuousSMul LL V]
    {ρ : Representation LL G V} {ιx : Type} {k : ℕ} {Ms : ιx → G → Matrix (Fin k) (Fin k) LL}
    {m : ℕ} (xs : Fin m → ιx) (φ : V →ₗ[LL] (Fin m → Fin k → LL)) (hφ : Function.Injective φ)
    (heq : ∀ g v, φ (ρ g v) = fun a => (Ms (xs a) g).mulVec (φ v a)) (hMs : ∀ x, Continuous (Ms x))
    (v : V) : Continuous fun g => ρ g v := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ (LinearMap.ker_eq_bot.2 hφ)
  have hψv : ∀ v, ψ (φ v) = v := fun v => by rw [← LinearMap.comp_apply, hψ, LinearMap.id_apply]
  have h : (fun g => ρ g v) = fun g => ψ (fun a => (Ms (xs a) g).mulVec (φ v a)) :=
    funext fun g => by rw [← heq, hψv]
  rw [h]
  have hψc : Continuous ψ := IsModuleTopology.continuous_of_linearMap ψ
  refine hψc.comp (continuous_pi fun a => continuous_pi fun i => ?_)
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finset_sum _ fun j _ => ((hMs (xs a)).matrix_elem i j).mul continuous_const

end Emb

section Loc

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module O M]

theorem mkK_inj [Module.Free O M] : Function.Injective (mkK (O := O) (M := M)) := by
  intro a b h
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) (f := mkK (O := O) (M := M)) h
  rw [Submonoid.smul_def, Submonoid.smul_def] at hc
  exact smul_right_injective M (nonZeroDivisors.coe_ne_zero c) hc

theorem mkK_span (v : MK (O := O) M) : ∃ c : O, c ≠ 0 ∧ ∃ m, mkK m = c • v := by
  induction v using LocalizedModule.induction_on with
  | h m s =>
    refine ⟨(s : O), nonZeroDivisors.coe_ne_zero s, m, ?_⟩
    rw [LocalizedModule.smul'_mk]
    show LocalizedModule.mk m 1 = _
    rw [LocalizedModule.mk_eq]
    exact ⟨1, by simp [Submonoid.smul_def]⟩

end Loc

section RecCol

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

abbrev MsAt {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    Br.G D.nbr i _ hn → Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LLw (D.nbr i _ hn)) :=
  ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rTwO D.nd i r x))

def EmbAt {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {VP : Type} [AddCommGroup VP]
    [Module (FractionRing (D.nd.O i)) VP] [Module (D.nd.O i) VP] [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VP]
    (ρVP : Representation (D.nd.O i) ↥(Γn i dc n) VP) : Prop :=
  ∃ (m : ℕ) (xs : Fin m → D.nd.X i)
    (φ : TrV (eK (D.nbr i _ hn)) VP →ₗ[Br.LLw (D.nbr i _ hn)] (Fin m → Fin D.R.nV → Br.LLw (D.nbr i _ hn))),
    Function.Injective φ ∧ ∀ g v, φ (repL (eK (D.nbr i _ hn)) ρVP (Br.iota D.nbr i _ hn) g v) =
      fun a => (MsAt i dc r hn (xs a) g).mulVec (φ v a)

def MsCont {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) : Prop :=
  ∀ x, Continuous (MsAt i dc r hn x)

theorem lift_integral_column (eR : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hA : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc eR) (hG : K.SelfGood i)
    {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (hc : K.plOf i dc n ∈ dc.col)
    {P Q VP VQ : Type} [AddCommGroup P] [Module (D.nd.O i) P] [AddCommGroup Q] [Module (D.nd.O i) Q]
    [AddCommGroup VP] [Module (FractionRing (D.nd.O i)) VP] [Module (D.nd.O i) VP]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VP]
    [AddCommGroup VQ] [Module (FractionRing (D.nd.O i)) VQ] [Module (D.nd.O i) VQ]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VQ]
    [Module.Finite (D.nd.O i) P] [Module.Free (D.nd.O i) P] [Module.Finite (D.nd.O i) Q] [Module.Free (D.nd.O i) Q]
    {ρP : Representation (D.nd.O i) ↥(Γn i dc n) P} {ρQ : Representation (D.nd.O i) ↥(Γn i dc n) Q}
    {ρVP : Representation (D.nd.O i) ↥(Γn i dc n) VP} {ρVQ : Representation (D.nd.O i) ↥(Γn i dc n) VQ}
    {jP : P →ₗ[D.nd.O i] VP} {jQ : Q →ₗ[D.nd.O i] VQ}
    (hjP : Function.Injective jP) (hjQ : Function.Injective jQ)
    (hjeqP : ∀ γ m, jP (ρP γ m) = ρVP γ (jP m)) (hjeqQ : ∀ γ m, jQ (ρQ γ m) = ρVQ γ (jQ m))
    (hspP : ∀ v : VP, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m, jP m = c • v)
    (hspQ : ∀ v : VQ, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m, jQ m = c • v)
    {ev : P →ₗ[D.nd.O i] Q} {f0 : VP →ₗ[D.nd.O i] VQ}
    (hf0 : ∀ γ v, f0 (ρVP γ v) = ρVQ γ (f0 v)) (hcomm : ∀ m, f0 (jP m) = jQ (ev m))
    (hev : IsEquivMap ρP ρQ ev) (hevs : Function.Surjective ev)
    (hemb : EmbAt i dc r hn ρVP) (hMs : MsCont i dc r hn) :
    Formalism.RepresentationBoundsCohomology.JL.LiftO (D.nd.l i) (finiteClassesCocyclesMap i dc n ρVP ρP jP) (finiteClassesCocyclesMap i dc n ρVQ ρQ jQ)
      (Formalism.RepresentationBoundsCohomology.JL.mapH1 ρP ρQ ev hev) (eR (K.plOf i dc n)) := by
  obtain ⟨m, xs, φ, hφ, heq⟩ := hemb
  exact liftO_col i dc r eR hA hG hn hc hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm hev hevs
    (cont_of_inj xs φ hφ heq hMs) (subq_of_inj xs φ hφ heq)

end RecCol

section Cols

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem plOf_col (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) = l.1 :=
  K.plOf_idx i dc (Finset.mem_union_left _ (Finset.mem_union_right _ l.2))

theorem hcCol (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ dc.col := by
  rw [plOf_col]
  exact l.2

theorem hnCol (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ placesOver D.host.E (D.nd.l i) :=
  (dc.cover _).1 (Or.inr (hcCol i dc l))

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r' : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem liftCol_eve (eR : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hA : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc eR) (hG : K.SelfGood i)
    {Pe L V : Type} [AddCommGroup Pe] [Module R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass R' (D.nd.O i) Pe]
    [Module.Finite (D.nd.O i) Pe] [Module.Free (D.nd.O i) Pe]
    [AddCommGroup L] [Module R' L] [Module (D.nd.O i) L] [SMulCommClass R' (D.nd.O i) L]
    [Module.Finite (D.nd.O i) L] [Module.Free (D.nd.O i) L]
    [AddCommGroup V] [Module R' V] [Module (D.nd.O i) V] [Module (FractionRing (D.nd.O i)) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] [SMulCommClass R' (FractionRing (D.nd.O i)) V]
    (ince : Pe →ₗ[R'] R') (v₁ : L) (eve : Pe →ₗ[D.nd.O i] L) (heve : ∀ a, eve a = ince a • v₁)
    (hevs : Function.Surjective eve)
    (iL : L →ₗ[D.nd.O i] V) (hiL : Function.Injective iL) (hiLeq : ∀ (a : R') m, iL (a • m) = a • iL m)
    (hspL : ∀ v : V, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m, iL m = c • v)
    (hemb : ∀ l, EmbAt i dc r (hnCol i dc l)
      (locRep (resRep (uRep (D.nd.O i) (M := Pe) r' χ) (Γn i dc (K.colIdx i dc l)))))
    (hMs : ∀ l, MsCont i dc r (hnCol i dc l)) :
    LiftCol i dc (Hfe₁ i dc r' χ) (Ff i dc r' χ iL)
      (fun l => Formalism.RepresentationBoundsCohomology.JL.mapH1 _ _ eve (Formalism.RepresentationBoundsCohomology.JL.ev_equiv r' χ (Γn i dc (K.colIdx i dc l)) ince v₁ eve heve))
      (fun n => eR (K.plOf i dc n)) := by
  haveI := smulComm_O i (A := R') (V := V)
  intro l
  have hQ : ∀ (γ : ↥(Γn i dc (K.colIdx i dc l))) m,
      iL (resRep (uRep (D.nd.O i) (M := L) r' χ) (Γn i dc (K.colIdx i dc l)) γ m) =
        resRep (uRep (D.nd.O i) (M := V) r' χ) (Γn i dc (K.colIdx i dc l)) γ (iL m) :=
    fun γ m => hiLeq _ m
  have hev := Formalism.RepresentationBoundsCohomology.JL.ev_equiv r' χ (Γn i dc (K.colIdx i dc l)) ince v₁ eve heve
  exact lift_integral_column i dc r eR hA hG (hnCol i dc l) (hcCol i dc l)
    (ρVP := locRep (resRep (uRep (D.nd.O i) (M := Pe) r' χ) (Γn i dc (K.colIdx i dc l))))
    (ρVQ := resRep (uRep (D.nd.O i) (M := V) r' χ) (Γn i dc (K.colIdx i dc l)))
    (jP := mkK) (jQ := iL) mkK_inj hiL (fun γ m => (locRep_mkK _ γ m).symm) hQ mkK_span hspL
    (f0 := liftK (iL ∘ₗ eve))
    (liftK_equiv _ _ (iL ∘ₗ eve) (fun γ m => by rw [LinearMap.comp_apply, LinearMap.comp_apply, hev, hQ]))
    (fun m => liftK_mkK _ m) hev hevs (hemb l) (hMs l)

theorem liftCol_evE (eR : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hA : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc eR) (hG : K.SelfGood i)
    (δO : D.nd.O i) [Module.Finite (D.nd.O i) ↥(Ideal.span {δO})] [Module.Free (D.nd.O i) ↥(Ideal.span {δO})]
    {PE : Type} [AddCommGroup PE] [Module R' PE] [Module (D.nd.O i) PE] [SMulCommClass R' (D.nd.O i) PE]
    [Module.Finite (D.nd.O i) PE] [Module.Free (D.nd.O i) PE]
    (evE : PE →ₗ[D.nd.O i] ↥(Ideal.span {δO})) (hevE : ∀ g a, evE (uElt r' χ g • a) = evE a)
    (hevs : Function.Surjective evE)
    (hemb : ∀ l, EmbAt i dc r (hnCol i dc l)
      (locRep (resRep (uRep (D.nd.O i) (M := PE) r' χ) (Γn i dc (K.colIdx i dc l)))))
    (hMs : ∀ l, MsCont i dc r (hnCol i dc l)) :
    LiftCol i dc (Hfe₁ i dc r' χ) (HfE₂ i dc δO)
      (fun l => Formalism.RepresentationBoundsCohomology.JL.mapH1 _ _ evE (Formalism.RepresentationBoundsCohomology.JL.ev_equiv_triv r' χ (Γn i dc (K.colIdx i dc l)) evE hevE))
      (fun n => eR (K.plOf i dc n)) := by
  intro l
  have hev := Formalism.RepresentationBoundsCohomology.JL.ev_equiv_triv r' χ (Γn i dc (K.colIdx i dc l)) evE hevE
  have hQ : ∀ (γ : ↥(Γn i dc (K.colIdx i dc l))) (m : ↥(Ideal.span {δO})),
      mkK (O := D.nd.O i) (Representation.trivial (D.nd.O i) ↥(Γn i dc (K.colIdx i dc l)) ↥(Ideal.span {δO}) γ m) =
        locRep (Representation.trivial (D.nd.O i) ↥(Γn i dc (K.colIdx i dc l)) ↥(Ideal.span {δO})) γ (mkK m) :=
    fun γ m => (locRep_mkK _ γ m).symm
  exact lift_integral_column i dc r eR hA hG (hnCol i dc l) (hcCol i dc l)
    (ρVP := locRep (resRep (uRep (D.nd.O i) (M := PE) r' χ) (Γn i dc (K.colIdx i dc l))))
    (ρVQ := locRep (Representation.trivial (D.nd.O i) ↥(Γn i dc (K.colIdx i dc l)) ↥(Ideal.span {δO})))
    (jP := mkK) (jQ := mkK) mkK_inj mkK_inj (fun γ m => (locRep_mkK _ γ m).symm) hQ mkK_span mkK_span
    (f0 := liftK (mkK ∘ₗ evE))
    (liftK_equiv _ _ (mkK ∘ₗ evE) (fun γ m => by rw [LinearMap.comp_apply, LinearMap.comp_apply, hev, hQ]))
    (fun m => liftK_mkK _ m) hev hevs (hemb l) (hMs l)

end Cols

section Cont

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem msCont_of (hr : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    MsCont i dc r hn := by
  intro x
  have hM := rTwO_cont D i r hr x
  refine continuous_matrix fun a b => ?_
  have h1 : Continuous fun g : Br.G D.nbr i _ hn =>
      rTwO D.nd i r x ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) a b :=
    (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i _ hn))
  have h2 : Continuous fun y : D.nd.O i => (((D.nbr i _ hn).eO y : ↥(OL (D.nbr i _ hn).LL)) :
      ↥(D.nbr i _ hn).LL.1) := continuous_subtype_val.comp (D.nbr i _ hn).eO_cont
  have h3 : Continuous fun y : ↥(D.nbr i _ hn).LL.1 => (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn).inc y :=
    Continuous.subtype_mk continuous_subtype_val _
  exact h3.comp (h2.comp h1)

end Cont

section Sel

theorem fin_sel {LL V : Type} [Field LL] [AddCommGroup V] [Module LL V] [FiniteDimensional LL V] {I : Type} {k : ℕ}
    (Ψ : I → V →ₗ[LL] (Fin k → LL)) (h : ∀ v, (∀ i, Ψ i v = 0) → v = 0) :
    ∃ (m : ℕ) (xs : Fin m → I), ∀ v, (∀ a, Ψ (xs a) v = 0) → v = 0 := by
  let f : I × Fin k → Module.Dual LL V := fun p => (LinearMap.proj p.2) ∘ₗ Ψ p.1
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent LL (Set.range f)
  have hfin : b.Finite := hli.setFinite
  have hpre : ∀ φ : b, ∃ p, f p = φ := fun φ => hbs φ.2
  haveI : Fintype b := hfin.fintype
  let eb := Fintype.equivFin b
  refine ⟨Fintype.card b, fun a => (Classical.choose (hpre (eb.symm a))).1, fun v hv => h v fun i => ?_⟩
  have hb : ∀ φ ∈ b, φ v = 0 := by
    intro φ hφ
    have hc := Classical.choose_spec (hpre (eb.symm (eb ⟨φ, hφ⟩)))
    have hψ : ((eb.symm (eb ⟨φ, hφ⟩) : b) : Module.Dual LL V) = φ := by rw [Equiv.symm_apply_apply]
    rw [← hψ, ← hc]
    show (Ψ _ v) _ = 0
    rw [hv (eb ⟨φ, hφ⟩)]
    rfl
  have hall : ∀ φ ∈ Submodule.span LL b, φ v = 0 := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hb x hx
    | zero => rfl
    | add x y _ _ hx hy => rw [LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]
  funext c
  exact hall (f (i, c)) (hspan ▸ Submodule.subset_span ⟨(i, c), rfl⟩)

end Sel

section EmbFam

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem embAt_of_fam {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {VP : Type} [AddCommGroup VP]
    [Module (FractionRing (D.nd.O i)) VP] [Module (D.nd.O i) VP] [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VP]
    (ρVP : Representation (D.nd.O i) ↥(Γn i dc n) VP)
    [FiniteDimensional (Br.LLw (D.nbr i _ hn)) (TrV (eK (D.nbr i _ hn)) VP)] {I : Type} (xx : I → D.nd.X i)
    (Ψ : I → TrV (eK (D.nbr i _ hn)) VP →ₗ[Br.LLw (D.nbr i _ hn)] (Fin D.R.nV → Br.LLw (D.nbr i _ hn)))
    (hinj : ∀ v, (∀ a, Ψ a v = 0) → v = 0)
    (heq : ∀ a g v, Ψ a (repL (eK (D.nbr i _ hn)) ρVP (Br.iota D.nbr i _ hn) g v) =
      (MsAt i dc r hn (xx a) g).mulVec (Ψ a v)) : EmbAt i dc r hn ρVP := by
  obtain ⟨m, xs, hxs⟩ := fin_sel Ψ hinj
  refine ⟨m, xx ∘ xs, LinearMap.pi fun a => Ψ (xs a), fun v w hvw => ?_, fun g v => funext fun a => heq _ g v⟩
  rw [← sub_eq_zero]
  refine hxs _ fun a => ?_
  rw [map_sub, sub_eq_zero]
  exact congrFun hvw a

end EmbFam

section Dd

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem chiInv_at (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    (g : GE D.nd) (x' : Dd.X') :
    ((((Dd.χ g)⁻¹ : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
  have h1 : ((((Dd.χ g)⁻¹ : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' * (chiU D.nd i 1 g : D.nd.O i) = 1 := by
    have h0 : (((Dd.χ g)⁻¹ : (Dd.T')ˣ) : Dd.T') * (Dd.χ g : Dd.T') = 1 := Units.inv_mul _
    have := congrArg (fun f : Dd.T' => (f : Dd.X' → D.nd.O i) x') h0
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one, Pi.mul_apply, Pi.one_apply] at this
    rwa [hχ g x'] at this
  exact Units.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)

theorem uElt_at
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    (g : GE D.nd) (x' : Dd.X') :
    ((Formalism.NG.uElt Dd.r Dd.χ g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rTwO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) := by
  show (((((Dd.χ g)⁻¹ : (Dd.T')ˣ) : Dd.T') • Dd.r g : Dd.R') :
    Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' = _
  rw [hsm, hr', chiInv_at i Dd hχ]
  ext a b
  simp [rTwO, twistM, Matrix.map_apply, Matrix.smul_apply]

end Dd

section DdEmb

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem smul_mk {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] (m : M) (s : nonZeroDivisors O) :
    ((s : O) • LocalizedModule.mk m s : MK (O := O) M) = mkK m := by
  rw [LocalizedModule.smul'_mk]
  show _ = LocalizedModule.mk m 1
  rw [LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def]⟩

theorem smul_cancel {O A : Type} [CommRing O] [IsDomain O] [AddCommGroup A] [Module (FractionRing O) A] [Module O A]
    [IsScalarTower O (FractionRing O) A] (s : nonZeroDivisors O) {y z : A} (h : (s : O) • y = (s : O) • z) : y = z := by
  have hu := (Module.End.isUnit_iff _).1 (isUnit_end (V := A) s)
  apply hu.1
  simpa [Module.algebraMap_end_apply] using h

theorem msAt_apply {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i)
    (g : Br.G D.nbr i _ hn) (a b : Fin D.R.nV) :
    MsAt i dc r hn x g a b = eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (rTwO D.nd i r x ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) a b)) := by
  rw [← heO_br i dc hn]
  rfl

theorem embAt_Dd {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    {Pe : Type} [AddCommGroup Pe] [Module Dd.R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass Dd.R' (D.nd.O i) Pe]
    [Module.Finite (D.nd.O i) Pe] [Module.Free (D.nd.O i) Pe]
    (κ : Pe →ₗ[D.nd.O i] (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))))
    (hκ : Function.Injective κ)
    (hκa : ∀ (a : Dd.R') p, κ (a • p) = (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * κ p) :
    EmbAt i dc r hn (locRep (resRep (uRep (D.nd.O i) (M := Pe) Dd.r Dd.χ) (Γn i dc n))) := by
  set ρP := resRep (uRep (D.nd.O i) (M := Pe) Dd.r Dd.χ) (Γn i dc n) with hρP
  set e := eK (D.nbr i _ hn)
  let Λ := liftK (V := Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) κ
  have hΛs : ∀ m (s : nonZeroDivisors (D.nd.O i)), (s : D.nd.O i) • Λ (LocalizedModule.mk m s) = κ m := by
    intro m s
    rw [← map_smul, smul_mk, liftK_mkK]
  have hΛi : ∀ v, Λ v = 0 → v = 0 := by
    intro v hv
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h1 := hΛs m s
      rw [hv, smul_zero] at h1
      rw [hκ (h1.symm.trans (map_zero κ).symm), LocalizedModule.zero_mk]
  have hΛe : ∀ (γ : ↥(Γn i dc n)) v, Λ (locRep ρP γ v) =
      ((Formalism.NG.uElt Dd.r Dd.χ (γ : GE D.nd) : Dd.R') :
        Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * Λ v := by
    intro γ v
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h0 : locRep ρP γ (LocalizedModule.mk m s) = LocalizedModule.mk (ρP γ m) s := LocalizedModule.map_mk _ _ _ _
      rw [h0]
      apply smul_cancel s
      rw [hΛs, ← mul_smul_comm, hΛs]
      exact hκa _ m
  let Ψ : Dd.X' × Fin D.R.nV → TrV e (MK (O := D.nd.O i) Pe) →ₗ[Br.LLw (D.nbr i _ hn)]
      (Fin D.R.nV → Br.LLw (D.nbr i _ hn)) := fun q =>
    { toFun := fun v a => e ((Λ (untr e v)) q.1 a q.2)
      map_add' := fun v w => funext fun a => by
        show e ((Λ (untr e v + untr e w)) q.1 a q.2) = _
        rw [map_add]
        simp [map_add]
      map_smul' := fun c v => funext fun a => by
        show e ((Λ (e.symm c • untr e v)) q.1 a q.2) = c * e ((Λ (untr e v)) q.1 a q.2)
        rw [smulK]
        simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul] }
  haveI : FiniteDimensional (Br.LLw (D.nbr i _ hn)) (TrV e (MK (O := D.nd.O i) Pe)) :=
    finDim_of_lat (Ow := Br.Ow (D.nbr i _ hn)) (Qp := ℚ_[D.nd.l i])
      (latOf e (D.nbr i _ hn).eO mkK (Br.iota D.nbr i _ hn) (heO_br i dc hn) (locRep ρP) ρP mkK_inj
        (fun γ m => (locRep_mkK _ γ m).symm) mkK_span)
  refine embAt_of_fam i dc r hn _ (fun q => Dd.p q.1) Ψ (fun v hv => ?_) (fun q g v => ?_)
  · have h0 : Λ (untr e v) = 0 := by
      funext x'
      ext a b
      have := congrFun (hv (x', b)) a
      simpa [Ψ] using this
    exact hΛi _ h0
  · funext a
    have key : ∀ γ : ↥(Γn i dc n), (γ : GE D.nd) = ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) →
        e ((Λ (locRep ρP γ (untr e v))) q.1 a q.2) = (MsAt i dc r hn (Dd.p q.1) g).mulVec (Ψ q v) a := by
      intro γ hγ
      rw [hΛe, Pi.mul_apply, hγ, uElt_at i r Dd hr' hsm hχ, Matrix.mul_apply, map_sum]
      simp only [Matrix.mulVec, dotProduct, msAt_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [Ψ, Matrix.map_apply, map_mul]
      exact Or.inl rfl
    exact key (Br.iota D.nbr i _ hn g) rfl

end DdEmb

section Final

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem ringDef_lift {T : Subalgebra (D.nd.O i) (D.nd.X i → D.nd.O i)} {π : D.nd.X i} {ε : GE D.nd →* (D.nd.O i)ˣ}
    {g0 : GE D.nd} {eB e₁ s : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) T (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) ε g0 eB e₁ s Dd) :
    (∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) ∧
    (∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x') ∧
    (∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i)) :=
  ⟨hD.2.2.2.2.2.2.1, hD.2.2.2.2.2.2.2.2.1, hD.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem liftCol_eve_Dd (eR : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hA : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc eR) (hG : K.SelfGood i)
    (hC : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
    {T : Subalgebra (D.nd.O i) (D.nd.X i → D.nd.O i)} {π : D.nd.X i} {ε : GE D.nd →* (D.nd.O i)ˣ}
    {g0 : GE D.nd} {eB e₁ s : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) T (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) ε g0 eB e₁ s Dd)
    {Pe L V : Type} [AddCommGroup Pe] [Module Dd.R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass Dd.R' (D.nd.O i) Pe]
    [Module.Finite (D.nd.O i) Pe] [Module.Free (D.nd.O i) Pe]
    [AddCommGroup L] [Module Dd.R' L] [Module (D.nd.O i) L] [SMulCommClass Dd.R' (D.nd.O i) L]
    [Module.Finite (D.nd.O i) L] [Module.Free (D.nd.O i) L]
    [AddCommGroup V] [Module Dd.R' V] [Module (D.nd.O i) V] [Module (FractionRing (D.nd.O i)) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] [SMulCommClass Dd.R' (FractionRing (D.nd.O i)) V]
    (κ : Pe →ₗ[D.nd.O i] (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))))
    (hκ : Function.Injective κ)
    (hκa : ∀ (a : Dd.R') p, κ (a • p) = (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * κ p)
    (ince : Pe →ₗ[Dd.R'] Dd.R') (v₁ : L) (eve : Pe →ₗ[D.nd.O i] L) (heve : ∀ a, eve a = ince a • v₁)
    (hevs : Function.Surjective eve)
    (iL : L →ₗ[D.nd.O i] V) (hiL : Function.Injective iL) (hiLeq : ∀ (a : Dd.R') m, iL (a • m) = a • iL m)
    (hspL : ∀ v : V, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m, iL m = c • v) :
    LiftCol i dc (Hfe₁ i dc Dd.r Dd.χ) (Ff i dc Dd.r Dd.χ iL)
      (fun l => Formalism.RepresentationBoundsCohomology.JL.mapH1 _ _ eve (Formalism.RepresentationBoundsCohomology.JL.ev_equiv Dd.r Dd.χ (Γn i dc (K.colIdx i dc l)) ince v₁ eve heve))
      (fun n => eR (K.plOf i dc n)) := by
  obtain ⟨hr', hsm, hχ⟩ := ringDef_lift i r Dd hD
  exact liftCol_eve i dc r Dd.r Dd.χ eR hA hG ince v₁ eve heve hevs iL hiL hiLeq hspL
    (fun l => embAt_Dd i dc r Dd (hnCol i dc l) hr' hsm hχ κ hκ hκa) (fun l => msCont_of i dc r hC (hnCol i dc l))

theorem liftCol_evE_Dd (eR : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hA : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc eR) (hG : K.SelfGood i)
    (hC : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
    {T : Subalgebra (D.nd.O i) (D.nd.X i → D.nd.O i)} {π : D.nd.X i} {ε : GE D.nd →* (D.nd.O i)ˣ}
    {g0 : GE D.nd} {eB e₁ s : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) T (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) ε g0 eB e₁ s Dd)
    (δO : D.nd.O i) [Module.Finite (D.nd.O i) ↥(Ideal.span {δO})] [Module.Free (D.nd.O i) ↥(Ideal.span {δO})]
    {PE : Type} [AddCommGroup PE] [Module Dd.R' PE] [Module (D.nd.O i) PE] [SMulCommClass Dd.R' (D.nd.O i) PE]
    [Module.Finite (D.nd.O i) PE] [Module.Free (D.nd.O i) PE]
    (κ : PE →ₗ[D.nd.O i] (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))))
    (hκ : Function.Injective κ)
    (hκa : ∀ (a : Dd.R') p, κ (a • p) = (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * κ p)
    (evE : PE →ₗ[D.nd.O i] ↥(Ideal.span {δO})) (hevE : ∀ g a, evE (uElt Dd.r Dd.χ g • a) = evE a)
    (hevs : Function.Surjective evE) :
    LiftCol i dc (Hfe₁ i dc Dd.r Dd.χ) (HfE₂ i dc δO)
      (fun l => Formalism.RepresentationBoundsCohomology.JL.mapH1 _ _ evE (Formalism.RepresentationBoundsCohomology.JL.ev_equiv_triv Dd.r Dd.χ (Γn i dc (K.colIdx i dc l)) evE hevE))
      (fun n => eR (K.plOf i dc n)) := by
  obtain ⟨hr', hsm, hχ⟩ := ringDef_lift i r Dd hD
  exact liftCol_evE i dc r Dd.r Dd.χ eR hA hG δO evE hevE hevs
    (fun l => embAt_Dd i dc r Dd (hnCol i dc l) hr' hsm hχ κ hκ hκa) (fun l => msCont_of i dc r hC (hnCol i dc l))

end Final

section Inst

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

def kappaL (x : Dd.R') :
    K.LeftId (D.nd.O i) x →ₗ[D.nd.O i] (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) where
  toFun p := ((K.incl (D.nd.O i) x p : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i)))
  map_add' p q := by rw [map_add]; rfl
  map_smul' c p := rfl

theorem kappaL_inj (x : Dd.R') : Function.Injective (kappaL i Dd x) := by
  intro p q h
  exact Subtype.ext (Subtype.ext h)

theorem kappaL_mul (x : Dd.R') (a : Dd.R') (p : K.LeftId (D.nd.O i) x) :
    kappaL i Dd x (a • p) = (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * kappaL i Dd x p :=
  rfl

theorem ideal_finite (δO : D.nd.O i) : Module.Finite (D.nd.O i) ↥(Ideal.span {δO}) :=
  Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_singleton δO))

theorem ideal_free [IsDiscreteValuationRing (D.nd.O i)] (δO : D.nd.O i) : Module.Free (D.nd.O i) ↥(Ideal.span {δO}) := by
  haveI := ideal_finite i δO
  exact Module.free_of_finite_type_torsion_free'

end Inst

section LeftFin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem leftId_finite [Module.Finite (D.nd.O i) Dd.R'] (x : Dd.R') : Module.Finite (D.nd.O i) (K.LeftId (D.nd.O i) x) := by
  let S : Submodule (D.nd.O i) Dd.R' := (Submodule.span Dd.R' ({x} : Set Dd.R')).restrictScalars (D.nd.O i)
  haveI : Module.Finite (D.nd.O i) S := Module.IsNoetherian.finite (D.nd.O i) S
  let f : S ≃ₗ[D.nd.O i] K.LeftId (D.nd.O i) x :=
    { toFun := fun a => K.lmk (D.nd.O i) x a.1 a.2
      invFun := fun p => ⟨K.lv (D.nd.O i) x p, K.lv_mem (D.nd.O i) x p⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Finite.equiv f

theorem leftId_free [Module.Finite (D.nd.O i) Dd.R'] (x : Dd.R') : Module.Free (D.nd.O i) (K.LeftId (D.nd.O i) x) := by
  haveI := leftId_finite i Dd x
  haveI : NoZeroSMulDivisors (D.nd.O i) (K.LeftId (D.nd.O i) x) :=
    ⟨fun {c p} h => by
      by_cases hc : c = 0
      · exact Or.inl hc
      right
      apply kappaL_inj i Dd x
      rw [map_zero]
      apply smul_cancel (⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩ : nonZeroDivisors (D.nd.O i))
      show c • kappaL i Dd x p = c • 0
      rw [← map_smul, h, map_zero, smul_zero]⟩
  exact Module.free_of_finite_type_torsion_free'

end LeftFin

section LatMInst

theorem latM_finite (O : Type) [CommRing O] {R : Type} [Ring R] (n : Type) [Fintype n] [DecidableEq n]
    (ρ : R →+* Matrix n n O) : Module.Finite O (Formalism.RepresentationBoundsCohomology.SF.LatM O O n ρ) :=
  inferInstanceAs (Module.Finite O (n → O))

theorem latM_free (O : Type) [CommRing O] {R : Type} [Ring R] (n : Type) [Fintype n] [DecidableEq n]
    (ρ : R →+* Matrix n n O) : Module.Free O (Formalism.RepresentationBoundsCohomology.SF.LatM O O n ρ) :=
  inferInstanceAs (Module.Free O (n → O))

end LatMInst

end Formalism.MainNotions.N.KLift
