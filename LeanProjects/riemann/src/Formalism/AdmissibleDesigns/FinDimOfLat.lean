import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
import Formalism.AdmissibleDesigns.LengthSemilinear

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

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
  show (algebraMap Ow LL (eO a)) • tr e v = tr e (a • v)
  rw [smulLL_def, heO, RingEquiv.symm_apply_apply]
  exact algebraMap_smul (FractionRing O) a v

theorem smul_Ow (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (c : Ow) (v : V) : (c • tr e v : TrV e V) = tr e (eO.symm c • v) := by
  have h := smul_eO heO (eO.symm c) v
  rwa [RingEquiv.apply_symm_apply] at h

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
    (v : TrV e V) : v ∈ latT e eO j heO ↔ ∃ m, tr e (j m) = v := by
  exact Iff.rfl

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

theorem free_MO [Module.Free O M] : Module.Free Ow (MO eO M) := by
  exact Module.Free.of_basis ((basMO (eO := eO) (M := M)).mapCoeffs eO (fun c x => by
    show eO.symm (eO c) • x = c • x
    rw [RingEquiv.symm_apply_apply]))

theorem finite_MO [Module.Finite O M] [Module.Free O M] : Module.Finite Ow (MO eO M) := by
  exact Module.Finite.of_basis ((basMO (eO := eO) (M := M)).mapCoeffs eO (fun c x => by
    show eO.symm (eO c) • x = c • x
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
  intro y hy
  obtain ⟨q, rfl⟩ := (mem_latT jQ heO y).mp hy
  obtain ⟨p, rfl⟩ := hev q
  refine ⟨tr e (jP p), (mem_latT jP heO _).mpr ⟨p, rfl⟩, ?_⟩
  show trL e f0 (tr e (jP p)) = tr e (jQ (ev p))
  rw [trL_apply]
  exact hcomm p

end Lift

section FromAt

theorem finDim_of_lat {LL Ow : Type} [Field LL] [CommRing Ow] [Algebra Ow LL] {G : Type} [Group G]
    {Qp : Type} [Field Qp] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module Ow V]
    [IsScalarTower Ow LL V] {ρ : Representation LL G V} (L : Lattice (O := Ow) ρ) : FiniteDimensional LL V := by
  obtain ⟨s, hs⟩ := L.fg
  have h1 : (L.T : Set V) ⊆ Submodule.span LL (s : Set V) := by
    rw [← hs]
    exact Submodule.span_subset_span Ow LL _
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff, ← L.span]
  exact Submodule.span_le.mpr h1

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
  intro w
  obtain ⟨c, hc, q, hq⟩ := hspQ (untr e w)
  obtain ⟨p, rfl⟩ := hev q
  have hk : algebraMap O (FractionRing O) c ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
  refine ⟨tr e ((algebraMap O (FractionRing O) c)⁻¹ • jP p), ?_⟩
  rw [trL_apply]
  show f0 ((algebraMap O (FractionRing O) c)⁻¹ • jP p) = untr e w
  rw [smulK, hcomm, hq, ← algebraMap_smul (FractionRing O) c, smul_smul, inv_mul_cancel₀ hk, one_smul]

end Lift2

section Loc

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module O M]

theorem mkK_inj [Module.Free O M] : Function.Injective (mkK (O := O) (M := M)) := by
  intro a b h
  simp only [LocalizedModule.mkLinearMap_apply] at h
  rw [LocalizedModule.mk_eq] at h
  obtain ⟨u, hu⟩ := h
  simp only [one_smul, Submonoid.smul_def] at hu
  exact smul_right_injective M (nonZeroDivisors.coe_ne_zero u) hu

theorem mkK_span (v : MK (O := O) M) : ∃ c : O, c ≠ 0 ∧ ∃ m, mkK m = c • v := by
  refine LocalizedModule.induction_on (fun m s => ?_) v
  refine ⟨s, nonZeroDivisors.coe_ne_zero s, m, ?_⟩
  rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def]⟩

end Loc

end Formalism.MainNotions.N.KRow

end
