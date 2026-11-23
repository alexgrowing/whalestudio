import Formalism.AdmissibleDesigns.YtTarget
import Formalism.AdmissibleDesigns.TensSubsingleton

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

theorem baer_of_div {R Q : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup Q] [Module R Q]
    (hdiv : ∀ a : R, a ≠ 0 → ∀ y : Q, ∃ q : Q, a • q = y) : Module.Baer R Q := by
  intro I g
  have ha : Submodule.IsPrincipal.generator I ∈ I := Submodule.IsPrincipal.generator_mem I
  by_cases h0 : Submodule.IsPrincipal.generator I = 0
  · refine ⟨0, fun x hx => ?_⟩
    obtain ⟨s, rfl⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).1 hx
    have : (⟨s • Submodule.IsPrincipal.generator I, hx⟩ : I) = 0 := Subtype.ext (by simp [h0])
    rw [this, map_zero, LinearMap.zero_apply]
  · obtain ⟨q, hq⟩ := hdiv _ h0 (g ⟨_, ha⟩)
    refine ⟨LinearMap.toSpanSingleton R Q q, fun x hx => ?_⟩
    obtain ⟨s, rfl⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).1 hx
    rw [LinearMap.toSpanSingleton_apply, smul_assoc, hq, ← map_smul]
    rfl

section Gen

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {Ow : Type} [CommRing Ow] [Algebra Ow LL] (eO : O ≃+* Ow)

scoped instance (priority := low) modOwY (V : Type) [AddCommGroup V] [Module (FractionRing O) V] :
    Module Ow (TrV e V) :=
  Module.compHom (TrV e V) (algebraMap Ow LL)

variable {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]

instance towOwY : IsScalarTower Ow LL (TrV e V) :=
  ⟨fun a b v => by
    show (a • b) • v = (algebraMap Ow LL a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩

def trY (v : V) : TrV e V := v

variable {e eO}

theorem smul_OwY (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (c : Ow) (v : V) : (c • trY e v : TrV e V) = trY e (eO.symm c • v) := by
  show (e.symm (algebraMap Ow LL c)) • v = eO.symm c • v
  conv_lhs => rw [← RingEquiv.apply_symm_apply eO c]
  rw [heO, RingEquiv.symm_apply_apply, algebraMap_smul]

variable {M : Type} [AddCommGroup M] [Module O M]

variable (e eO) in

def latTY (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a)) :
    Submodule Ow (TrV e (MK (O := O) M)) where
  carrier := Set.range fun m : M => trY e (mkK (O := O) m)
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add (mkK (O := O) (M := M)) a b⟩
  zero_mem' := ⟨0, map_zero (mkK (O := O) (M := M))⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    refine ⟨eO.symm c • a, ?_⟩
    show trY e (mkK (O := O) (eO.symm c • a)) = c • trY e (mkK (O := O) a)
    rw [smul_OwY heO, map_smul]

def MOY (_eO : O ≃+* Ow) (M : Type) : Type := M

instance : AddCommGroup (MOY eO M) := ‹AddCommGroup M›
instance : Module O (MOY eO M) := ‹Module O M›
instance instModMOY : Module Ow (MOY eO M) := Module.compHom M eO.symm.toRingHom

variable (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))

def latMapY : MOY eO M →ₗ[Ow] ↥(latTY e eO (M := M) heO) where
  toFun m := ⟨trY e (mkK (O := O) (show M from m)), m, rfl⟩
  map_add' a b := Subtype.ext (map_add (mkK (O := O) (M := M)) a b)
  map_smul' c a := Subtype.ext (by
    show trY e (mkK (O := O) (eO.symm c • (show M from a))) = c • trY e (mkK (O := O) (show M from a))
    rw [smul_OwY heO, map_smul])

theorem latMapY_bij (hinj : Function.Injective (mkK (O := O) (M := M))) :
    Function.Bijective (latMapY (eO := eO) (M := M) heO) :=
  ⟨fun a b h => hinj (congrArg Subtype.val h : trY e (mkK (O := O) (show M from a)) = trY e (mkK (show M from b))),
    fun ⟨_, m, hm⟩ => ⟨m, Subtype.ext hm⟩⟩

def latEquivY (hinj : Function.Injective (mkK (O := O) (M := M))) : MOY eO M ≃ₗ[Ow] ↥(latTY e eO (M := M) heO) :=
  LinearEquiv.ofBijective (latMapY heO) (latMapY_bij heO hinj)

def basMOY [Module.Free O M] : Basis (Module.Free.ChooseBasisIndex O M) O (MOY eO M) := Module.Free.chooseBasis O M

theorem free_MOY [Module.Free O M] : Module.Free Ow (MOY eO M) :=
  Module.Free.of_basis ((basMOY (eO := eO)).mapCoeffs eO
    (fun c (x : MOY eO M) => by
      show eO.symm (eO c) • (show M from x) = c • (show M from x)
      rw [RingEquiv.symm_apply_apply]))

theorem finite_MOY [Module.Finite O M] [Module.Free O M] : Module.Finite Ow (MOY eO M) :=
  Module.Finite.of_basis ((basMOY (eO := eO)).mapCoeffs eO
    (fun c (x : MOY eO M) => by
      show eO.symm (eO c) • (show M from x) = c • (show M from x)
      rw [RingEquiv.symm_apply_apply]))

theorem mkK_spanY (v : MK (O := O) M) : ∃ c : O, c ≠ 0 ∧ ∃ m, mkK m = c • v := by
  induction v using LocalizedModule.induction_on with
  | h m s =>
    refine ⟨(s : O), nonZeroDivisors.coe_ne_zero s, m, ?_⟩
    rw [LocalizedModule.smul'_mk]
    show LocalizedModule.mk m 1 = _
    rw [LocalizedModule.mk_eq]
    exact ⟨1, by simp [Submonoid.smul_def]⟩

theorem mkK_injY [NoZeroSMulDivisors O M] : Function.Injective (mkK (O := O) (M := M)) := by
  intro a b h
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) (f := mkK (O := O) (M := M)) h
  rw [Submonoid.smul_def, Submonoid.smul_def] at hc
  exact smul_right_injective M (nonZeroDivisors.coe_ne_zero c) hc

variable {Γ G : Type} [Group Γ] [Group G] (ι : G →* Γ)

def latY [Module.Finite O M] [Module.Free O M] [NoZeroSMulDivisors O M] (ρM : Representation O Γ M) :
    Lattice (O := Ow) (repL e (locRep ρM) ι) where
  T := latTY e eO heO
  stable g := by
    rintro _ ⟨m, rfl⟩
    exact ⟨ρM (ι g) m, (locRep_mkK ρM (ι g) m).symm⟩
  fg := by
    haveI := finite_MOY (eO := eO) (M := M)
    haveI : Module.Finite Ow ↥(latTY e eO (M := M) heO) := Module.Finite.equiv (latEquivY heO mkK_injY)
    exact (Module.Finite.iff_fg).1 inferInstance
  free := by
    haveI := free_MOY (eO := eO) (M := M)
    exact Module.Free.of_equiv (latEquivY heO mkK_injY)
  span := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, hc, m, hm⟩ := mkK_spanY (O := O) (show MK (O := O) M from v)
    have hk : algebraMap O (FractionRing O) c ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
    have hv0 : (show MK (O := O) M from v) = (algebraMap O (FractionRing O) c)⁻¹ • mkK m := by
      rw [hm, ← algebraMap_smul (FractionRing O) c (show MK (O := O) M from v), smul_smul, inv_mul_cancel₀ hk, one_smul]
    have hv : v = e (algebraMap O (FractionRing O) c)⁻¹ • trY e (mkK (O := O) m) := by
      show (show MK (O := O) M from v) = e.symm (e (algebraMap O (FractionRing O) c)⁻¹) • mkK m
      rw [RingEquiv.symm_apply_apply, hv0]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

end Gen

section Gen2

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  {e : FractionRing O ≃+* LL} {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {Γ G : Type} [Group Γ] [Group G] (ι : G →* Γ)
  {N : Type} [AddCommGroup N] [Module O N]

variable (e) in

def eLin : TrV e (FractionRing O) →ₗ[LL] LL where
  toFun x := e (show FractionRing O from x)
  map_add' x y := map_add e _ _
  map_smul' c x := by
    show e (e.symm c * (show FractionRing O from x)) = c * e (show FractionRing O from x)
    rw [map_mul, RingEquiv.apply_symm_apply]

variable (e N) in

def pY : TrV e (MK (O := O) (N × O)) →ₗ[LL] LL :=
  eLin e ∘ₗ trL e (liftK (V := FractionRing O) (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O N O))

theorem pY_mk (m : N × O) : pY e N (trY e (mkK (O := O) m)) = e (algebraMap O (FractionRing O) m.2) := by
  show e (liftK (V := FractionRing O) (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O N O) (mkK m)) = _
  rw [liftK_mkK]
  rfl

theorem pY_inv (ρM : Representation O Γ (N × O)) (h2 : ∀ g m, (ρM g m).2 = m.2) (g : G)
    (v : TrV e (MK (O := O) (N × O))) : pY e N (repL e (locRep ρM) ι g v) = pY e N v := by
  have h := liftK_equiv (Representation.trivial O Γ (FractionRing O)) ρM
    (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O N O)
    (fun g m => by
      show algebraMap O (FractionRing O) (ρM g m).2 = algebraMap O (FractionRing O) m.2
      rw [h2]) (ι g) (show MK (O := O) (N × O) from v)
  show e (liftK _ (locRep ρM (ι g) (show MK (O := O) (N × O) from v))) = e (liftK _ (show MK (O := O) (N × O) from v))
  rw [h]
  rfl

include heO in
theorem pY_int (v : TrV e (MK (O := O) (N × O))) (hv : ∃ m : N × O, trY e (mkK (O := O) m) = v) :
    pY e N v ∈ Set.range (algebraMap Ow LL) := by
  obtain ⟨m, rfl⟩ := hv
  rw [pY_mk, ← heO]
  exact ⟨_, rfl⟩

theorem pY_zero (m : N × O) (h : pY e N (trY e (mkK (O := O) m)) = 0) : m.2 = 0 := by
  rw [pY_mk] at h
  have h1 : algebraMap O (FractionRing O) m.2 = 0 := by
    rwa [map_eq_zero_iff e e.injective] at h
  exact (IsFractionRing.injective O (FractionRing O)) (h1.trans (map_zero _).symm)

include heO in

theorem div_quot {V : Type} [AddCommGroup V] [Module LL V] [Module Ow V] [IsScalarTower Ow LL V]
    (T : Submodule Ow V) (a : O) (ha : a ≠ 0) (y : V ⧸ T) : ∃ q : V ⧸ T, eO a • q = y := by
  induction y using Submodule.Quotient.induction_on with
  | H v =>
    have hc : algebraMap Ow LL (eO a) ≠ 0 := by
      rw [heO]
      exact (map_ne_zero e).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha))
    refine ⟨Submodule.Quotient.mk ((algebraMap Ow LL (eO a))⁻¹ • v), ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← algebraMap_smul LL (eO a), smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem nzsd_prod [NoZeroSMulDivisors O N] : NoZeroSMulDivisors O (N × O) :=
  ⟨fun {c x} h => by
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have h1 : c • x.1 = 0 := congrArg Prod.fst h
      have h2 : c * x.2 = 0 := congrArg Prod.snd h
      exact Prod.ext ((smul_eq_zero.1 h1).resolve_left hc) ((mul_eq_zero.1 h2).resolve_left hc)⟩

include heO in

theorem ext_of_baer [IsPrincipalIdealRing O] [NoZeroSMulDivisors O N] {Q : Type} [AddCommGroup Q] [Module Ow Q]
    (hdiv : ∀ a : O, a ≠ 0 → ∀ y : Q, ∃ q : Q, eO a • q = y) (g₀ : N →+ Q)
    (hg : ∀ (a : O) (n : N), g₀ (a • n) = eO a • g₀ n) :
    ∃ φ : TrV e (MK (O := O) (N × O)) →ₗ[Ow] Q, ∀ n : N, φ (trY e (mkK (O := O) (n, (0 : O)))) = g₀ n := by
  letI : Module O Q := Module.compHom Q eO.toRingHom
  have hB : Module.Baer O Q := baer_of_div fun a ha y => hdiv a ha y
  let f : N →ₗ[O] MK (O := O) (N × O) := mkK ∘ₗ LinearMap.inl O N O
  haveI := nzsd_prod (O := O) (N := N)
  have hf : Function.Injective f := mkK_injY.comp LinearMap.inl_injective
  let g : N →ₗ[O] Q := { toFun := g₀, map_add' := g₀.map_add, map_smul' := fun a n => hg a n }
  obtain ⟨h, hh⟩ := hB.extension_property f hf g
  refine ⟨⟨⟨fun v => h (show MK (O := O) (N × O) from v), fun x y => h.map_add _ _⟩, fun c v => ?_⟩,
    fun n => LinearMap.congr_fun hh n⟩
  have hs := smul_OwY (V := MK (O := O) (N × O)) heO c (show MK (O := O) (N × O) from v)
  show h (show MK (O := O) (N × O) from (c • v)) = c • h (show MK (O := O) (N × O) from v)
  have hs' : (show MK (O := O) (N × O) from (c • v)) = eO.symm c • (show MK (O := O) (N × O) from v) := hs
  rw [hs', h.map_smul]
  show eO (eO.symm c) • h _ = _
  rw [RingEquiv.apply_symm_apply]

end Gen2

end Formalism.MainNotions.N.K.TBa

end
