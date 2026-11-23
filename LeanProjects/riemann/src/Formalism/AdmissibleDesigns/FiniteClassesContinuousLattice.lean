import Formalism.AdmissibleDesigns.NonemptyPl
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Galois

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KHf

open Module TensorProduct Formalism.WeaklyAdmissibleFiltrations

section Onto

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem toLLK_surj : Function.Surjective (Br.toLLK Bw) := by
  intro y
  have halg : IsAlgebraic ℚ_[l] y := Algebra.IsAlgebraic.isAlgebraic y
  have halg' : IsAlgebraic ℤ_[l] y := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] (Br.LLw Bw)).mpr halg
  obtain ⟨n, hn, hint⟩ := IsAlgebraic.exists_integral_multiple halg'
  let x : Formalism.BasicNotions.Loc.OL Bw.LL := ⟨n • y, hint⟩
  have hn' : algebraMap ℤ_[l] (Br.LLw Bw) n ≠ 0 := by
    intro h0
    apply hn
    have : algebraMap ℚ_[l] (Br.LLw Bw) (algebraMap ℤ_[l] ℚ_[l] n) = 0 := by
      rw [← IsScalarTower.algebraMap_apply]; exact h0
    have h2 := (algebraMap ℚ_[l] (Br.LLw Bw)).injective (this.trans (map_zero _).symm)
    exact (IsFractionRing.injective ℤ_[l] ℚ_[l]) (h2.trans (map_zero _).symm)
  refine ⟨algebraMap O (FractionRing O) (Bw.eO.symm x) /
    algebraMap O (FractionRing O) (Bw.eO.symm (algebraMap ℤ_[l] (Formalism.BasicNotions.Loc.OL Bw.LL) n)), ?_⟩
  rw [map_div₀, Br.toLLK_alg, Br.toLLK_alg, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rw [← IsScalarTower.algebraMap_apply, div_eq_iff hn']
  change n • y = y * _
  rw [Algebra.smul_def, mul_comm]

def eK : FractionRing O ≃+* Br.LLw Bw :=
  RingEquiv.ofBijective (Br.toLLK Bw) ⟨(Br.toLLK Bw).injective, toLLK_surj Bw⟩

theorem eK_apply (k : FractionRing O) : eK Bw k = Br.toLLK Bw k := rfl

end Onto

section Tr

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] (e : FractionRing O ≃+* LL)

def TrV (_e : FractionRing O ≃+* LL) (V : Type) : Type := V

variable {V : Type} [AddCommGroup V] [Module (FractionRing O) V]

instance : AddCommGroup (TrV e V) := ‹AddCommGroup V›

instance instModLL : Module LL (TrV e V) := Module.compHom V e.symm.toRingHom

theorem smulLL_def (c : LL) (v : TrV e V) : c • v = (e.symm c • (show V from v) : V) := rfl

variable {Qp : Type} [Field Qp] [Algebra Qp LL]

instance instModQp : Module Qp (TrV e V) := Module.compHom V (e.symm.toRingHom.comp (algebraMap Qp LL))

instance : IsScalarTower Qp LL (TrV e V) :=
  ⟨fun c a v => by
    show (e.symm (c • a)) • (show V from v) = (e.symm (algebraMap Qp LL c)) • ((e.symm a) • (show V from v))
    rw [Algebra.smul_def, map_mul, mul_smul]⟩

variable [TopologicalSpace LL]

instance instTop : TopologicalSpace (TrV e V) := moduleTopology LL (TrV e V)

instance : IsModuleTopology LL (TrV e V) := ⟨rfl⟩

instance : ContinuousAdd (TrV e V) := IsModuleTopology.toContinuousAdd LL (TrV e V)

instance : ContinuousSMul LL (TrV e V) := IsModuleTopology.toContinuousSMul LL (TrV e V)

instance : ContinuousNeg (TrV e V) := ⟨by
  have h : (fun v : TrV e V => -v) = fun v => (-1 : LL) • v := by
    funext v
    rw [neg_one_smul]
  rw [h]
  exact continuous_const_smul _⟩

instance : IsTopologicalAddGroup (TrV e V) where

variable [Module O V] [IsScalarTower O (FractionRing O) V]
  {W : Type} [AddCommGroup W] [Module (FractionRing O) W] [Module O W] [IsScalarTower O (FractionRing O) W]

theorem smulK (f : V →ₗ[O] W) (k : FractionRing O) (v : V) : f (k • v) = k • f v :=
  (LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O) f).map_smul k v

def trL (f : V →ₗ[O] W) : TrV e V →ₗ[LL] TrV e W where
  toFun v := (f v : W)
  map_add' u v := f.map_add u v
  map_smul' c v := smulK f (e.symm c) v

theorem trL_apply (f : V →ₗ[O] W) (v : TrV e V) : trL e f v = (f v : W) := rfl

theorem trL_cont (f : V →ₗ[O] W) : Continuous (trL e f) :=
  IsModuleTopology.continuous_of_linearMap (trL e f)

variable {Γ G : Type} [Group Γ] [Group G]

def repL (ρ : Representation O Γ V) (ι : G →* Γ) : Representation LL G (TrV e V) where
  toFun g := trL e (ρ (ι g))
  map_one' := LinearMap.ext fun v => by
    show ρ (ι 1) v = v
    simp only [map_one]
    rfl
  map_mul' g h := LinearMap.ext fun v => by
    show ρ (ι (g * h)) v = ρ (ι g) (ρ (ι h) v)
    simp only [map_mul]
    rfl

theorem repL_apply (ρ : Representation O Γ V) (ι : G →* Γ) (g : G) (v : TrV e V) :
    repL e ρ ι g v = (ρ (ι g) v : V) := rfl

variable [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)

def finZ (ρ : Representation O Γ V) (ι : G →* Γ) : Submodule (FractionRing O) (Γ → V) where
  carrier := {c | (fun g => (c (ι g) : TrV e V)) ∈ finiteCocycles PD (repL e ρ ι)}
  zero_mem' := (finiteCocycles PD (repL e ρ ι)).zero_mem
  add_mem' ha hb := (finiteCocycles PD (repL e ρ ι)).add_mem ha hb
  smul_mem' k c hc := by
    have h := (finiteCocycles PD (repL e ρ ι)).smul_mem (e k) hc
    have heq : (show G → TrV e V from fun g => (k • c) (ι g)) =
        e k • (show G → TrV e V from fun g => c (ι g)) := by
      funext g
      show k • c (ι g) = e.symm (e k) • c (ι g)
      rw [RingEquiv.symm_apply_apply]
    show (show G → TrV e V from fun g => (k • c) (ι g)) ∈ finiteCocycles PD (repL e ρ ι)
    rw [heq]
    exact h

theorem mem_finZ (ρ : Representation O Γ V) (ι : G →* Γ) (c : Γ → V) :
    c ∈ finZ e PD ρ ι ↔ (fun g => (c (ι g) : TrV e V)) ∈ finiteCocycles PD (repL e ρ ι) := Iff.rfl

theorem finZ_map (ρ : Representation O Γ V) (ρ' : Representation O Γ W) (ι : G →* Γ) (f : V →ₗ[O] W)
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (c : Γ → V) (hc : c ∈ finZ e PD ρ ι) :
    (fun g => f (c g)) ∈ finZ e PD ρ' ι :=
  (cocyclesFunctorial_holds G Qp K₀ Kk B BdR PD LL (TrV e V) (TrV e W) (repL e ρ ι) (repL e ρ' ι) (trL e f)
    (trL_cont e f) (fun g v => hf (ι g) v) _).2 hc

end Tr

section Cls

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  (ρ : Representation O Γ V)
  {M : Type} [AddCommGroup M] [Module O M]

def finPre (φ : M →ₗ[O] V) : Submodule O (Γ → M) :=
  ((finZ e PD ρ ι).restrictScalars O).comap (LinearMap.compLeft φ Γ)

def finiteClassesModel (ρM : Representation O Γ M) (φ : M →ₗ[O] V) : Submodule O (Formalism.NG.H1z ρM) :=
  ((finPre e PD ι ρ φ).comap (Formalism.NG.coZ1s ρM).subtype).map (Submodule.mkQ _)

def finiteClassesContinuous [TopologicalSpace Γ] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M]
    (ρM : Representation O Γ M) (φ : M →ₗ[O] V) : Submodule O (ReciprocityTheory.Gal.H1 ρM) :=
  ((finPre e PD ι ρ φ).comap (ReciprocityTheory.Gal.Z1 ρM).subtype).map (Submodule.mkQ _)

abbrev MK (M : Type) [AddCommGroup M] [Module O M] : Type := LocalizedModule (nonZeroDivisors O) M

abbrev mkK : M →ₗ[O] MK (O := O) M := LocalizedModule.mkLinearMap (nonZeroDivisors O) M

def locRep (ρM : Representation O Γ M) : Representation O Γ (MK (O := O) M) where
  toFun g := (LocalizedModule.map (nonZeroDivisors O) (ρM g)).restrictScalars O
  map_one' := LinearMap.ext fun x => by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      show LocalizedModule.map (nonZeroDivisors O) (ρM 1) (LocalizedModule.mk m s) = LocalizedModule.mk m s
      rw [LocalizedModule.map_mk, map_one]
      rfl
  map_mul' g h := LinearMap.ext fun x => by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      show LocalizedModule.map (nonZeroDivisors O) (ρM (g * h)) (LocalizedModule.mk m s) =
        LocalizedModule.map (nonZeroDivisors O) (ρM g)
          (LocalizedModule.map (nonZeroDivisors O) (ρM h) (LocalizedModule.mk m s))
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk, map_mul]
      rfl

theorem locRep_mkK (ρM : Representation O Γ M) (g : Γ) (m : M) :
    locRep ρM g (mkK m) = mkK (ρM g m) :=
  LocalizedModule.map_mk _ _ _ _

def finLoc (ρM : Representation O Γ M) : Submodule O (Γ → M) :=
  finPre e PD ι (locRep ρM) mkK

def finiteClassesModelLattice (ρM : Representation O Γ M) : Submodule O (Formalism.NG.H1z ρM) :=
  finiteClassesModel e PD ι (locRep ρM) ρM mkK

def finiteClassesContinuousLattice [TopologicalSpace Γ] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M]
    (ρM : Representation O Γ M) : Submodule O (ReciprocityTheory.Gal.H1 ρM) :=
  finiteClassesContinuous e PD ι (locRep ρM) ρM mkK

theorem isUnit_end (s : nonZeroDivisors O) :
    IsUnit ((algebraMap O (Module.End O V)) (s : O)) := by
  have hs : algebraMap O (FractionRing O) (s : O) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  rw [Module.End.isUnit_iff]
  constructor
  · intro a b hab
    have hab' : algebraMap O (FractionRing O) (s : O) • a = algebraMap O (FractionRing O) (s : O) • b := by
      simpa [algebraMap_smul] using hab
    exact smul_right_injective V hs hab'
  · intro y
    refine ⟨(algebraMap O (FractionRing O) (s : O))⁻¹ • y, ?_⟩
    show (s : O) • ((algebraMap O (FractionRing O) (s : O))⁻¹ • y) = y
    rw [← algebraMap_smul (FractionRing O) (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]

def liftK (f : M →ₗ[O] V) : MK (O := O) M →ₗ[O] V :=
  IsLocalizedModule.lift (nonZeroDivisors O) mkK f (isUnit_end (V := V))

theorem liftK_mkK (f : M →ₗ[O] V) (m : M) : liftK f (mkK m) = f m :=
  IsLocalizedModule.lift_apply _ _ _ _ _

theorem liftK_equiv (ρM : Representation O Γ M) (f : M →ₗ[O] V) (hf : ∀ g m, f (ρM g m) = ρ g (f m))
    (g : Γ) (x : MK (O := O) M) : liftK f (locRep ρM g x) = ρ g (liftK f x) := by
  have h : (liftK f) ∘ₗ (locRep ρM g) = (ρ g) ∘ₗ (liftK f) := by
    apply IsLocalizedModule.ext (nonZeroDivisors O) (mkK (O := O) (M := M)) (isUnit_end (V := V))
    refine LinearMap.ext fun m => ?_
    simp only [LinearMap.comp_apply]
    rw [locRep_mkK, liftK_mkK, liftK_mkK, hf]
  exact congrArg (fun F : MK (O := O) M →ₗ[O] V => F x) h

theorem finLoc_map (ρM : Representation O Γ M) (f : M →ₗ[O] V) (hf : ∀ g m, f (ρM g m) = ρ g (f m))
    (c : Γ → M) (hc : c ∈ finLoc e PD ι ρM) : (fun g => f (c g)) ∈ finZ e PD ρ ι := by
  have h := finZ_map e PD (locRep ρM) ρ ι (liftK f) (liftK_equiv ρ ρM f hf) _ hc
  have e2 : (fun g => f (c g)) = (fun g => liftK f (mkK (c g))) := by
    funext g
    rw [liftK_mkK]
  rw [e2]
  exact h

end Cls

section Rec

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

abbrev Γn (n : ℕ) : Subgroup (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) := Formalism.RepresentationBoundsCohomology.FIN.decs D.host.E (K.Aw i dc) n

def fZ (n : ℕ) {V : Type} [AddCommGroup V] [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V) :
    Submodule (FractionRing (D.nd.O i)) (↥(Γn i dc n) → V) :=
  if hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i) then
    finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) ρ (Br.iota D.nbr i _ hn)
  else ⊤

section Gen

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V)
  {M : Type} [AddCommGroup M] [Module (D.nd.O i) M]

theorem fZ_pos (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    fZ i dc n ρ = finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) ρ (Br.iota D.nbr i _ hn) :=
  dif_pos hn

variable (n) in

def fPre (φ : M →ₗ[D.nd.O i] V) : Submodule (D.nd.O i) (↥(Γn i dc n) → M) :=
  ((fZ i dc n ρ).restrictScalars (D.nd.O i)).comap (LinearMap.compLeft φ _)

variable (n) in

def finiteClassesCocyclesMap (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M) (φ : M →ₗ[D.nd.O i] V) :
    Submodule (D.nd.O i) (Formalism.NG.H1z ρM) :=
  ((fPre i dc n ρ φ).comap (Formalism.NG.coZ1s ρM).subtype).map (Submodule.mkQ _)

variable (n) in

def finiteClassesContinuousMap [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul (D.nd.O i) M]
    (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M) (φ : M →ₗ[D.nd.O i] V) :
    Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 ρM) :=
  ((fPre i dc n ρ φ).comap (ReciprocityTheory.Gal.Z1 ρM).subtype).map (Submodule.mkQ _)

end Gen

section GenL

variable (n : ℕ) {M : Type} [AddCommGroup M] [Module (D.nd.O i) M]

def finiteClassesLocalModel (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M) : Submodule (D.nd.O i) (Formalism.NG.H1z ρM) :=
  finiteClassesCocyclesMap i dc n (locRep ρM) ρM mkK

def finiteClassesContinuousLocal [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul (D.nd.O i) M]
    (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M) : Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 ρM) :=
  finiteClassesContinuousMap i dc n (locRep ρM) ρM mkK

end GenL

end Rec

section Dict

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem smulComm_O {A V : Type} [Ring A] [AddCommGroup V] [Module A V] [Module (FractionRing (D.nd.O i)) V]
    [SMulCommClass A (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] : SMulCommClass A (D.nd.O i) V :=
  ⟨fun a c v => by
    rw [← algebraMap_smul (FractionRing (D.nd.O i)) c v, ← algebraMap_smul (FractionRing (D.nd.O i)) c (a • v),
      smul_comm]⟩

section Rows

variable [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

def HfW (w : ℕ) : Submodule (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT) :=
  Submodule.span (FractionRing (D.nd.O i))
    (finiteClassesContinuousMap i dc w (Dat w).ρT (Dat w).ρT LinearMap.id : Set (ReciprocityTheory.Gal.H1 (Dat w).ρT))

def Hf₂ (w : ℕ) : Submodule (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT') :=
  Submodule.span (FractionRing (D.nd.O i))
    (finiteClassesContinuousMap i dc w (Dat w).ρT' (Dat w).ρT' LinearMap.id : Set (ReciprocityTheory.Gal.H1 (Dat w).ρT'))

def Fs (w : ℕ) : Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 (Dat w).ρTl') :=
  ((Hf₂ i dc VT VT' Dat w).restrictScalars (D.nd.O i)).comap (Dat w).j'

def BKa (w : ℕ) : Prop :=
  ∀ a, a ∈ HfW i dc VT VT' Dat w ↔ ∀ b ∈ Hf₂ i dc VT VT' Dat w, ReciprocityTheory.ChartRestriction.T2.cupFG (Dat w) a b = 0

end Rows

def Hf₁ {T₁ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
    [ContinuousConstSMul (D.nd.O i) T₁] (ρ₁ : Representation (D.nd.O i) (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) T₁)
    (w : ℕ) : Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 (resRep ρ₁ (Γn i dc w))) :=
  finiteClassesContinuousLocal i dc w (resRep ρ₁ (Γn i dc w))

section Cols

variable {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

def Ff {L : Type} [AddCommGroup L] [Module R' L] [Module (D.nd.O i) L] [SMulCommClass R' (D.nd.O i) L]
    {V : Type} [AddCommGroup V] [Module R' V] [Module (D.nd.O i) V] [Module (FractionRing (D.nd.O i)) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] [SMulCommClass R' (FractionRing (D.nd.O i)) V]
    (iL : L →ₗ[D.nd.O i] V) (l : K.Col i dc) :
    Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := L) r χ) (Γn i dc (K.colIdx i dc l)))) :=
  haveI := smulComm_O i (A := R') (V := V)
  finiteClassesCocyclesMap i dc (K.colIdx i dc l) (resRep (uRep (D.nd.O i) (M := V) r χ) (Γn i dc (K.colIdx i dc l)))
    (resRep (uRep (D.nd.O i) (M := L) r χ) (Γn i dc (K.colIdx i dc l))) iL

def Hfe₁ {Pe : Type} [AddCommGroup Pe] [Module R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass R' (D.nd.O i) Pe]
    (l : K.Col i dc) :
    Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := Pe) r χ) (Γn i dc (K.colIdx i dc l)))) :=
  finiteClassesLocalModel i dc (K.colIdx i dc l) (resRep (uRep (D.nd.O i) (M := Pe) r χ) (Γn i dc (K.colIdx i dc l)))

def HfE₂ (δO : D.nd.O i) (l : K.Col i dc) :
    Submodule (D.nd.O i)
      (H1z (Representation.trivial (D.nd.O i) ↥(Γn i dc (K.colIdx i dc l)) ↥(Ideal.span {δO}))) :=
  finiteClassesLocalModel i dc (K.colIdx i dc l) (Representation.trivial (D.nd.O i) ↥(Γn i dc (K.colIdx i dc l)) ↥(Ideal.span {δO}))

abbrev evalModO (x' : X') : Module (D.nd.O i) (Formalism.NG.EvalSp (D.nd.O i) d R' x') :=
  Module.compHom _ (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))

end Cols

end Dict

section Cols2

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem evalTower (x' : X') :
    letI := evalModO i (R' := R') x'
    IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (EvalSp (D.nd.O i) d R' x') :=
  letI := evalModO i (R' := R') x'
  ⟨fun a b v => by
    show (a • b) • v = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩

theorem evalComm (x' : X') : SMulCommClass R' (FractionRing (D.nd.O i)) (EvalSp (D.nd.O i) d R' x') :=
  ⟨fun a c v => by
    show (Formalism.NG.matEnd (FractionRing (D.nd.O i)) (FractionRing (D.nd.O i)) d (Formalism.NG.evalAt (D.nd.O i) d R' x' a))
        (c • v) = c • (Formalism.NG.matEnd (FractionRing (D.nd.O i)) (FractionRing (D.nd.O i)) d
          (Formalism.NG.evalAt (D.nd.O i) d R' x' a)) v
    exact map_smul _ c v⟩

def repE (x' : X') (n : ℕ) :
    letI := evalModO i (R' := R') x'
    Representation (D.nd.O i) ↥(Γn i dc n) (EvalSp (D.nd.O i) d R' x') :=
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  haveI := evalComm i (R' := R') x'
  haveI := smulComm_O i (A := R') (V := EvalSp (D.nd.O i) d R' x')
  resRep (uRep (D.nd.O i) (M := EvalSp (D.nd.O i) d R' x') r χ) (Γn i dc n)

def Lx (x' : X') (l : K.Col i dc) :
    Submodule (FractionRing (D.nd.O i)) (↥(Γn i dc (K.colIdx i dc l)) → EvalSp (D.nd.O i) d R' x') :=
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  fZ i dc (K.colIdx i dc l) (repE i dc r χ x' (K.colIdx i dc l))

def F0col {V : Type} [AddCommGroup V] [Module (D.nd.O i) V] [Module (FractionRing (D.nd.O i)) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] {M : Type} [AddCommGroup M] [Module (D.nd.O i) M]
    (n : ℕ) (ρV : Representation (D.nd.O i) ↥(Γn i dc n) V) (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M)
    (qV : V →ₗ[D.nd.O i] M) : Submodule (D.nd.O i) (H1z ρM) :=
  ((((fZ i dc n ρV).restrictScalars (D.nd.O i)).map (LinearMap.compLeft qV _) ⊔ coB1 ρM).comap
    (coZ1s ρM).subtype).map (Submodule.mkQ _)

def Fρ {M : Type} [AddCommGroup M] [Module (D.nd.O i) M] (what₂ : Finset ℕ)
    (ρM : ∀ n, Representation (D.nd.O i) ↥(Γn i dc n) M) (Frow Fcol : ∀ n, Submodule (D.nd.O i) (H1z (ρM n)))
    (n : ℕ) : Submodule (D.nd.O i) (H1z (ρM n)) :=
  if n ∈ what₂ then Frow n else Fcol n

def LiftCol {P Q : ∀ _ : K.Col i dc, Type} [∀ l, AddCommGroup (P l)] [∀ l, Module (D.nd.O i) (P l)]
    [∀ l, AddCommGroup (Q l)] [∀ l, Module (D.nd.O i) (Q l)]
    (Hp : ∀ l, Submodule (D.nd.O i) (P l)) (Hq : ∀ l, Submodule (D.nd.O i) (Q l))
    (g : ∀ l, P l →ₗ[D.nd.O i] Q l) (e' : ℕ → ℕ) : Prop :=
  ∀ l, Formalism.RepresentationBoundsCohomology.JL.LiftO (D.nd.l i) (Hp l) (Hq l) (g l) (e' (K.colIdx i dc l))

def UnrFin (δO : D.nd.O i)
    (uz : ∀ l : K.Col i dc,
      coZ1s (Representation.trivial (D.nd.O i) ↥(Γn i dc (K.colIdx i dc l)) ↥(Ideal.span {δO}))) : Prop :=
  ∀ l, Submodule.mkQ _ (uz l) ∈ HfE₂ i dc δO l

def jK (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (n : ℕ) : ℕ :=
  if hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i) then Br.jW D.loc D.nbr i _ hn ρ π else 0

def DimLx (j : ℕ → ℕ) (x' : X') (l : K.Col i dc) : Prop :=
  Module.rank (FractionRing (D.nd.O i))
      (↥(Lx i dc r χ x' l) ⧸ (LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x')
        r χ (Γn i dc (K.colIdx i dc l)))).comap (Lx i dc r χ x' l).subtype) ≤
    (j (K.colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
      (LinearMap.ker (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x')
        r χ (Γn i dc (K.colIdx i dc l)))) : ℕ)

def FinRhoAt {L : Type} [AddCommGroup L] [Module R' L] [Module (D.nd.O i) L] [SMulCommClass R' (D.nd.O i) L]
    (Ff : ∀ l : K.Col i dc, Submodule (D.nd.O i)
      (H1z (resRep (uRep (D.nd.O i) (M := L) r χ) (Γn i dc (K.colIdx i dc l)))))
    (j : ℕ → ℕ) (κ : ∀ l : K.Col i dc, Fin (j (K.colIdx i dc l)) → (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) → L)
    (κz : ∀ l : K.Col i dc, Fin (j (K.colIdx i dc l)) →
      coZ1s (resRep (uRep (D.nd.O i) (M := L) r χ) (Γn i dc (K.colIdx i dc l))))
    (l : K.Col i dc) : Prop :=
  (∀ a (g : Γn i dc (K.colIdx i dc l)), (κz l a : Γn i dc (K.colIdx i dc l) → L) g = κ l a g) ∧
    (∀ (c : D.nd.O i) z, c ≠ 0 → c • z ∈ Ff l → z ∈ Ff l) ∧
    (∀ a, Submodule.mkQ _ (κz l a) ∈ Ff l) ∧
    (∀ z ∈ Ff l, ∃ (b : Fin (j (K.colIdx i dc l)) → D.nd.O i) (c : D.nd.O i), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (κz l a) :
        H1z (resRep (uRep (D.nd.O i) (M := L) r χ) (Γn i dc (K.colIdx i dc l))))) = 0) ∧
    (∀ (b : Fin (j (K.colIdx i dc l)) → D.nd.O i) (c : D.nd.O i), c ≠ 0 →
      c • ∑ a, b a • (Submodule.mkQ _ (κz l a) :
        H1z (resRep (uRep (D.nd.O i) (M := L) r χ) (Γn i dc (K.colIdx i dc l)))) = 0 → b = 0)

end Cols2

section Prf

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) {n : ℕ}
  {V : Type} [AddCommGroup V] [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
  {W : Type} [AddCommGroup W] [Module (FractionRing (D.nd.O i)) W] [Module (D.nd.O i) W]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) W]
  {M : Type} [AddCommGroup M] [Module (D.nd.O i) M]

theorem fZ_map (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V) (ρ' : Representation (D.nd.O i) ↥(Γn i dc n) W)
    (f : V →ₗ[D.nd.O i] W) (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (c : ↥(Γn i dc n) → V)
    (hc : c ∈ fZ i dc n ρ) : (fun g => f (c g)) ∈ fZ i dc n ρ' := by
  by_cases hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)
  · rw [fZ_pos i dc ρ hn] at hc
    rw [fZ_pos i dc ρ' hn]
    exact finZ_map _ _ ρ ρ' _ f hf c hc
  · unfold fZ
    rw [dif_neg hn]
    trivial

theorem fLoc_map (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M) (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V)
    (f : M →ₗ[D.nd.O i] V) (hf : ∀ g m, f (ρM g m) = ρ g (f m)) (c : ↥(Γn i dc n) → M)
    (hc : c ∈ fPre i dc n (locRep ρM) mkK) : (fun g => f (c g)) ∈ fZ i dc n ρ := by
  by_cases hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)
  · unfold fPre at hc
    rw [fZ_pos i dc (locRep ρM) hn] at hc
    rw [fZ_pos i dc ρ hn]
    exact finLoc_map _ _ _ ρ ρM f hf c hc
  · unfold fZ
    rw [dif_neg hn]
    trivial

def OrbC (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V) : Prop :=
  ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i), ∀ v : TrV (eK (D.nbr i _ hn)) V,
    Continuous fun g => repL (eK (D.nbr i _ hn)) ρ (Br.iota D.nbr i _ hn) g v

theorem cob_mem_fZ (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V) (h : OrbC i dc ρ) (v : V) :
    (fun g => ρ g v - v) ∈ fZ i dc n ρ := by
  by_cases hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)
  · rw [fZ_pos i dc ρ hn]
    exact coboundaryMap_mem_finiteCocycles (PD := Br.PD D.loc D.nbr i _ hn) (h hn) v
  · unfold fZ
    rw [dif_neg hn]
    trivial

end Prf

section PrfRow

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

theorem im_le_Fs (w : ℕ) {T₁ T₂ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁]
    [IsTopologicalAddGroup T₁] [ContinuousConstSMul (D.nd.O i) T₁] [AddCommGroup T₂] [Module (D.nd.O i) T₂]
    (ρ₁ : Representation (D.nd.O i) (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) T₁) (π : T₁ →ₗ[D.nd.O i] T₂)
    (vD : T₂ ≃ₗ[D.nd.O i] (Dat w).T') (hpD : Continuous fun t => vD (π t))
    (heD : ∀ g t, vD (π (resRep ρ₁ (Γn i dc w) g t)) = (Dat w).ρTl' g (vD (π t))) :
    (Hf₁ i dc ρ₁ w).map (Formalism.RepresentationBoundsCohomology.FIN.gRow (Dat w) (resRep ρ₁ (Γn i dc w)) π vD hpD heD) ≤
      Fs i dc VT VT' Dat w := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hx
  let f : T₁ →ₗ[D.nd.O i] VT' w := (Dat w).T'.subtype ∘ₗ vD.toLinearMap ∘ₗ π
  have hf : ∀ g t, f (resRep ρ₁ (Γn i dc w) g t) = (Dat w).ρT' g (f t) := by
    intro g t
    show (((vD (π (resRep ρ₁ (Γn i dc w) g t)) : (Dat w).T') : VT' w)) = _
    rw [heD]
    rfl
  have hmem := fLoc_map i dc (resRep ρ₁ (Γn i dc w)) (Dat w).ρT' f hf _ hz
  show _ ∈ Hf₂ i dc VT VT' Dat w
  refine Submodule.subset_span ⟨ReciprocityTheory.Gal.cocycles1MapOfEquivariant (Dat w).ρTl' (Dat w).ρT' (Dat w).T'.subtype
    continuous_subtype_val (fun _ _ => rfl)
    (ReciprocityTheory.Gal.cocycles1MapOfEquivariant _ _ (vD.toLinearMap ∘ₗ π) hpD heD z), hmem, rfl⟩

end PrfRow

section PrfCol

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem evalScalar (x' : X') (c : D.nd.O i) (v : EvalSp (D.nd.O i) d R' x') :
    (algebraMap (D.nd.O i) R' c) • v = (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c) • v := by
  funext j
  show ∑ k, (Formalism.NG.evalAt (D.nd.O i) d R' x' (algebraMap (D.nd.O i) R' c)) j k • v k =
    algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c • v j
  simp [Formalism.NG.evalAt, Matrix.algebraMap_matrix_apply, Finset.sum_ite_eq, Pi.algebraMap_apply]

theorem colD_le_Lx (x' : X') (l : K.Col i dc) :
    letI := evalModO i (R' := R') x'
    haveI := evalTower i (R' := R') x'
    OrbC i dc (repE i dc r χ x' (K.colIdx i dc l)) →
      LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
        (Γn i dc (K.colIdx i dc l))) ≤ Lx i dc r χ x' l := by
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  intro hO
  rintro _ ⟨η, rfl⟩
  exact cob_mem_fZ i dc _ hO η

theorem comp_mem_Lx {P : Type} [AddCommGroup P] [Module R' P] [Module (D.nd.O i) P] [SMulCommClass R' (D.nd.O i) P]
    (hP : ∀ (c : D.nd.O i) (m : P), c • m = (algebraMap (D.nd.O i) R' c) • m) (x' : X') (l : K.Col i dc) :
    letI := evalModO i (R' := R') x'
    haveI := evalTower i (R' := R') x'
    OrbC i dc (repE i dc r χ x' (K.colIdx i dc l)) →
      ∀ (f : P →ₗ[R'] EvalSp (D.nd.O i) d R' x')
        (z : coZ1s (resRep (uRep (D.nd.O i) (M := P) r χ) (Γn i dc (K.colIdx i dc l)))),
        Submodule.mkQ _ z ∈ Hfe₁ i dc r χ (Pe := P) l →
        (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → P) g)) ∈ Lx i dc r χ x' l := by
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  intro hO f z hz
  obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.1 hz
  have hb := (Submodule.Quotient.eq _).1 hyz
  obtain ⟨m, hm⟩ := hb
  let fO : P →ₗ[D.nd.O i] EvalSp (D.nd.O i) d R' x' :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c m => by
        rw [hP, f.map_smul, evalScalar]
        rfl }
  have hfe : ∀ g m, fO (resRep (uRep (D.nd.O i) (M := P) r χ) (Γn i dc (K.colIdx i dc l)) g m) =
      repE i dc r χ x' (K.colIdx i dc l) g (fO m) := fun g m => f.map_smul _ _
  have h1 := fLoc_map i dc _ (repE i dc r χ x' (K.colIdx i dc l)) fO hfe _ hy
  have h2 := cob_mem_fZ i dc _ hO (f m)
  have heq : (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → P) g)) =
      (fun g => fO ((y : Γn i dc (K.colIdx i dc l) → P) g)) -
        (fun g => repE i dc r χ x' (K.colIdx i dc l) g (f m) - f m) := by
    funext g
    have hg : resRep (uRep (D.nd.O i) (M := P) r χ) (Γn i dc (K.colIdx i dc l)) g m - m =
        (y : Γn i dc (K.colIdx i dc l) → P) g - (z : Γn i dc (K.colIdx i dc l) → P) g := congrFun hm g
    have hz' : (z : Γn i dc (K.colIdx i dc l) → P) g = (y : Γn i dc (K.colIdx i dc l) → P) g -
        (resRep (uRep (D.nd.O i) (M := P) r χ) (Γn i dc (K.colIdx i dc l)) g m - m) := by
      rw [hg]
      abel
    simp only [Pi.sub_apply]
    rw [hz', map_sub, map_sub]
    rw [show f (resRep (uRep (D.nd.O i) (M := P) r χ) (Γn i dc (K.colIdx i dc l)) g m) =
      repE i dc r χ x' (K.colIdx i dc l) g (f m) from hfe g m]
    rfl
  show _ ∈ fZ i dc _ _
  rw [heq]
  exact sub_mem h1 h2

end PrfCol

section PrfKappa

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

end PrfKappa

end Formalism.MainNotions.N.KHf
