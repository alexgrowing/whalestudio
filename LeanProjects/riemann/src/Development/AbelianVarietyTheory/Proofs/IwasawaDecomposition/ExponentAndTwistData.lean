import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

section Forms

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

def readT (i : T.Tw) (b : Bool) : ↥D.LL0 →+* FractionRing (T.O i) :=
  (IsFractionRing.map (A := T.O0 i) (B := T.O i) (K := FractionRing (T.O0 i)) (L := FractionRing (T.O i))
    (T.O_inj i)).comp (if b then T.emb0 i else T.emb0b i)

def KT (i : T.Tw) (_b : Bool) : Type := FractionRing (T.O i)

instance (i : T.Tw) (b : Bool) : Field (KT D T i b) := inferInstanceAs (Field (FractionRing (T.O i)))

instance algKT (i : T.Tw) (b : Bool) : Algebra S.Ks (KT D T i b) := ((readT D T i b).comp S.kKs).toAlgebra

def WKr (j : ℕ) : Submodule S.Ks (S.WL j) := if 1 ≤ j ∧ j ≤ D.R.m then (S.A j).WK else ⊥

theorem WKr_of {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : WKr D S j = (S.A j).WK := if_pos ⟨h1, h2⟩

theorem WKr_off {j : ℕ} (h : ¬ (1 ≤ j ∧ j ≤ D.R.m)) : WKr D S j = ⊥ := if_neg h

def FmT (i : T.Tw) (j : ℕ) (b : Bool) : Type := KT D T i b ⊗[S.Ks] ↥(WKr D S j)

instance acgFmT (i : T.Tw) (j : ℕ) (b : Bool) : AddCommGroup (FmT D T S i j b) :=
  inferInstanceAs (AddCommGroup (KT D T i b ⊗[S.Ks] ↥(WKr D S j)))

instance modKFmT (i : T.Tw) (j : ℕ) (b : Bool) : Module (FractionRing (T.O i)) (FmT D T S i j b) :=
  inferInstanceAs (Module (KT D T i b) (KT D T i b ⊗[S.Ks] ↥(WKr D S j)))

instance modOFmT (i : T.Tw) (j : ℕ) (b : Bool) : Module (T.O i) (FmT D T S i j b) :=
  Module.compHom (FmT D T S i j b) (algebraMap (T.O i) (FractionRing (T.O i)))

instance towFmT (i : T.Tw) (j : ℕ) (b : Bool) : IsScalarTower (T.O i) (FractionRing (T.O i)) (FmT D T S i j b) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def BsupT (i : T.Tw) (j : ℕ) (b : Bool) : Submodule (T.O i) (FmT D T S i j b) :=
  Submodule.span (T.O i)
    {f | ∃ x : ↥(WKr D S j), (x : S.WL j) ∈ (S.A j).MK ∧ f = ((1 : KT D T i b) ⊗ₜ[S.Ks] x : KT D T i b ⊗[S.Ks] ↥(WKr D S j))}

end Forms

section Act

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

def readK (i : T.Tw) (b : Bool) : ↥D.LL0 →+* KT D T i b := readT D T i b

theorem stabR (hR : ∀ j, 1 ≤ j → j ≤ D.R.m → RhoStab S j) (j : ℕ) (g : S.G) (x : S.WL j) (hx : x ∈ WKr D S j) :
    (S.A j).ρ g x ∈ WKr D S j := by
  by_cases h : 1 ≤ j ∧ j ≤ D.R.m
  · rw [WKr_of D S h.1 h.2] at hx ⊢
    exact hR j h.1 h.2 g x hx
  · rw [WKr_off D S h] at hx ⊢
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

def rhoR (hR : ∀ j, 1 ≤ j → j ≤ D.R.m → RhoStab S j) (j : ℕ) : S.G →* Module.End S.Ks ↥(WKr D S j) where
  toFun g := (((S.A j).ρ g).restrictScalars S.Ks).restrict (p := WKr D S j) (q := WKr D S j)
    fun x hx => stabR D S hR j g x hx
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (S.A j).ρ 1 (x : S.WL j) = (x : S.WL j)
    rw [map_one]; rfl
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (S.A j).ρ (g * h) (x : S.WL j) = (S.A j).ρ g ((S.A j).ρ h (x : S.WL j))
    rw [map_mul]; rfl

open Classical in

def cR (hC : ∀ j, 1 ≤ j → j ≤ D.R.m → ChiInLL0 S j) (j : ℕ) (g : S.G) : ↥D.LL0 :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then chiL S j (hC j h.1 h.2) g else 1

theorem cR_one (hC : ∀ j, 1 ≤ j → j ≤ D.R.m → ChiInLL0 S j) (j : ℕ) : cR D S hC j 1 = 1 := by
  unfold cR
  split_ifs with h
  · exact chiL_one S j _
  · rfl

theorem cR_mul (hC : ∀ j, 1 ≤ j → j ≤ D.R.m → ChiInLL0 S j) (j : ℕ) (g h : S.G) :
    cR D S hC j (g * h) = cR D S hC j g * cR D S hC j h := by
  unfold cR
  split_ifs with h'
  · exact chiL_mul S j _ g h
  · exact (mul_one 1).symm

def actEndT (hR : ∀ j, 1 ≤ j → j ≤ D.R.m → RhoStab S j) (hC : ∀ j, 1 ≤ j → j ≤ D.R.m → ChiInLL0 S j)
    (i : T.Tw) (j : ℕ) (b : Bool) : S.G →* Module.End (KT D T i b) (KT D T i b ⊗[S.Ks] ↥(WKr D S j)) where
  toFun g := (readK D T i b (cR D S hC j g))⁻¹ •
    Module.End.baseChangeHom S.Ks (KT D T i b) ↥(WKr D S j) (rhoR D S hR j g)
  map_one' := by rw [cR_one, map_one, inv_one, one_smul, map_one, map_one]
  map_mul' g h := by
    rw [cR_mul, map_mul, mul_inv, map_mul, map_mul]
    exact (smul_mul_smul_comm _ _ _ _).symm

def actGT (hR : ∀ j, 1 ≤ j → j ≤ D.R.m → RhoStab S j) (hC : ∀ j, 1 ≤ j → j ≤ D.R.m → ChiInLL0 S j)
    (i : T.Tw) (j : ℕ) (b : Bool) : G0g D.nd →* (FmT D T S i j b ≃ₗ[FractionRing (T.O i)] FmT D T S i j b) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (KT D T i b) (KT D T i b ⊗[S.Ks] ↥(WKr D S j))).toMonoidHom.comp
    (MonoidHom.toHomUnits ((actEndT D T S hR hC i j b).comp S.eG.symm.toMonoidHom))

def psiUT (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (b : Bool) :
    Formalism.IndefR.NX.U D.nd →* (FractionRing (T.O i))ˣ :=
  (Units.map (readT D T i b).toMonoidHom).comp (psiUOf D.nd (NX.xiRed D) θ)

instance instFiniteFiniteLevelQuotientGroup : Finite (G0g D.nd) := by
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  infer_instance

def eAlgT (i : T.Tw) (b : Bool) : MonoidAlgebra (FractionRing (T.O i)) (G0g D.nd) :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => readT D T i b (D.nexp.eLL0 g))

def eGT (hR : ∀ j, 1 ≤ j → j ≤ D.R.m → RhoStab S j) (hC : ∀ j, 1 ≤ j → j ≤ D.R.m → ChiInLL0 S j)
    (i : T.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  MonoidAlgebra.lift (FractionRing (T.O i)) (Module.End (FractionRing (T.O i)) (FmT D T S i j b)) (G0g D.nd)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (actGT D T S hR hC i j b)) (eAlgT D T i b)

def Fm0T (hR : ∀ j, 1 ≤ j → j ≤ D.R.m → RhoStab S j) (hC : ∀ j, 1 ≤ j → j ≤ D.R.m → ChiInLL0 S j)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (j : ℕ) (b : Bool) :
    Submodule (FractionRing (T.O i)) (FmT D T S i j b) :=
  ⨅ u : Formalism.IndefR.NX.U D.nd, LinearMap.ker ((actGT D T S hR hC i j b u).toLinearMap -
    ((psiUT D T θ i b u : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) • LinearMap.id)

def V0T (hR : ∀ j, 1 ≤ j → j ≤ D.R.m → RhoStab S j) (hC : ∀ j, 1 ≤ j → j ≤ D.R.m → ChiInLL0 S j)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (j : ℕ) (b : Bool) :
    Submodule (FractionRing (T.O i)) (FmT D T S i j b) :=
  (Fm0T D T S hR hC θ i j b).map (eGT D T S hR hC i j b)

def BT (hR : ∀ j, 1 ≤ j → j ≤ D.R.m → RhoStab S j) (hC : ∀ j, 1 ≤ j → j ≤ D.R.m → ChiInLL0 S j)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (j : ℕ) (b : Bool) :
    Submodule (T.O i) (FmT D T S i j b) :=
  BsupT D T S i j b ⊓ (V0T D T S hR hC θ i j b).restrictScalars (T.O i)

open Classical in

def cHkT (i : T.Tw) (b : Bool) (P : PlE D.host) : (T.O i)ˣ :=
  if h : ∃ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ then
    Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom (if b then T.delta i h.choose else (T.delta i h.choose)⁻¹)
  else 1

open Classical in

def hLr (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Module.End S.Ks ↥(WKr D S j) :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then
    ((In.hL j k P).restrictScalars S.Ks).restrict (p := WKr D S j) (q := WKr D S j) (fun x hx => by
      rw [WKr_of D S h.1 h.2] at hx ⊢
      exact In.hs j h.1 h.2 k P x hx)
  else 1

def hkT (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  ((show KT D T i b from algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i)) ^ k •
    Module.End.baseChangeHom S.Ks (KT D T i b) ↥(WKr D S j) (hLr D S In j k P) :
      Module.End (KT D T i b) (KT D T i b ⊗[S.Ks] ↥(WKr D S j)))

end Act

section Lat

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S)

abbrev BI (i : T.Tw) (j : ℕ) (b : Bool) : Submodule (T.O i) (FmT D T S i j b) :=
  BT D T S In.rho In.chi In.θ i j b

def HkCond (i : T.Tw) (j k : ℕ) (P : PlE D.host) : Prop :=
  1 ≤ j ∧ j ≤ D.R.m ∧ 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ T.S0 i

def HkStab : Prop :=
  ∀ i j b k P, HkCond D T i j k P → ∀ x ∈ BI D T S In i j b, hkT D T S In i j b k P x ∈ BI D T S In i j b

open Classical in

def hkB (hst : HkStab D T S In) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (T.O i) ↥(BI D T S In i j b) :=
  if h : HkCond D T i j k P then
    ((hkT D T S In i j b k P).restrictScalars (T.O i)).restrict (p := BI D T S In i j b) (q := BI D T S In i j b)
      (fun x hx => hst i j b k P h x hx)
  else 1

theorem hkB_zero (hst : HkStab D T S In) (i : T.Tw) (j : ℕ) (b : Bool) (P : PlE D.host) :
    hkB D T S In hst i j b 0 P = 1 := by
  unfold hkB
  rw [dif_neg]
  intro h
  exact absurd h.2.2.1 (by omega)

theorem fg_BI (hfg : ∀ i j b, (BsupT D T S i j b).FG) (i : T.Tw) (j : ℕ) (b : Bool) : (BI D T S In i j b).FG := by
  haveI : IsNoetherian (T.O i) ↥(BsupT D T S i j b) := isNoetherian_of_fg_of_noetherian _ (hfg i j b)
  have h1 : ((BI D T S In i j b).comap (BsupT D T S i j b).subtype).map (BsupT D T S i j b).subtype =
      BI D T S In i j b := by
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr inf_le_left
  rw [← h1]
  exact (IsNoetherian.noetherian _).map _

structure SigData where
  Sig : T.Tw → Type
  [fin : ∀ i, Fintype (Sig i)]
  jS : ∀ i, Sig i → ℕ
  jS_range : ∀ i s, 1 ≤ jS i s ∧ jS i s ≤ D.R.m
  side : ∀ i, Sig i → Bool
  hEig : ∀ i, Sig i → ℕ → PlE D.host → T.O i
  rowS : ∀ i, Sig i → D.what₂.FT

attribute [instance] SigData.fin

end Lat

section Make

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S)

theorem tf_BI (i : T.Tw) (j : ℕ) (b : Bool) : Module.IsTorsionFree (T.O i) ↥(BI D T S In i j b) := by
  refine ⟨fun r hr x y hxy => ?_⟩
  have hr0 : r ≠ 0 := hr.ne_zero
  have hk : algebraMap (T.O i) (FractionRing (T.O i)) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (T.O i) (FractionRing (T.O i)))).mpr hr0
  apply Subtype.ext
  have h : r • (x : FmT D T S i j b) = r • (y : FmT D T S i j b) := congrArg Subtype.val hxy
  rw [← algebraMap_smul (FractionRing (T.O i)) r, ← algebraMap_smul (FractionRing (T.O i)) r] at h
  exact smul_right_injective _ hk h

abbrev RhoFam : Type :=
  ∀ i : T.Tw, D.what₂.FT → Bool → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (T.O0 i))

def mkF (hfg : ∀ i j b, (BsupT D T S i j b).FG) (hst : HkStab D T S In) (sd : SigData D T) (rho : RhoFam D T)
    (hrho : ∀ i σ b, Continuous fun g =>
      ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) : TwF T where
  Sig := sd.Sig
  finSig := sd.fin
  jS := sd.jS
  jS_range := sd.jS_range
  side := sd.side
  rhoS := fun i s => rho i (sd.rowS i s) (sd.side i s)
  rhoS_cont := fun i s => hrho i _ _
  B := fun i j b => ↥(BI D T S In i j b)
  acgB := fun _ _ _ => inferInstance
  modB := fun _ _ _ => inferInstance
  freeB := fun i j b => by
    haveI := Module.Finite.iff_fg.mpr (fg_BI D T S In hfg i j b)
    haveI := tf_BI D T S In i j b
    exact Module.free_of_finite_type_torsion_free'
  finB := fun i j b => Module.Finite.iff_fg.mpr (fg_BI D T S In hfg i j b)
  Theta := fun _ _ _ => ⊥
  ThetaPsi := fun _ _ _ _ _ _ => ⊥
  ThetaPsi_one := fun _ _ _ _ => (Submodule.baseChange_bot _).symm
  hk := hkB D T S In hst
  hk_zero := hkB_zero D T S In hst
  hEig := sd.hEig

def eL : MonoidAlgebra ↥D.LL0 (G0g D.nd) := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm D.nexp.eLL0)

def EIdem : Prop :=
  eL D * eL D = eL D ∧ ∀ g : G0g D.nd, eL D * MonoidAlgebra.of _ _ g = MonoidAlgebra.of _ _ g * eL D

theorem eAlgT_eq (i : T.Tw) (b : Bool) :
    eAlgT D T i b = MonoidAlgebra.mapRangeRingHom (G0g D.nd) (readT D T i b) (eL D) := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  simp [eAlgT, eL, MonoidAlgebra.mapRangeRingHom]

theorem eAlgT_idem (he : EIdem D) (i : T.Tw) (b : Bool) : eAlgT D T i b * eAlgT D T i b = eAlgT D T i b := by
  rw [eAlgT_eq, ← map_mul, he.1]

theorem eAlgT_central (he : EIdem D) (i : T.Tw) (b : Bool) (x : MonoidAlgebra (FractionRing (T.O i)) (G0g D.nd)) :
    eAlgT D T i b * x = x * eAlgT D T i b := by
  rw [eAlgT_eq]
  refine MonoidAlgebra.induction_on (motive := fun x => MonoidAlgebra.mapRangeRingHom (G0g D.nd) (readT D T i b) (eL D) * x =
    x * MonoidAlgebra.mapRangeRingHom (G0g D.nd) (readT D T i b) (eL D)) x (fun g => ?_) (fun x y hx hy => ?_) (fun r x hx => ?_)
  · have h := congrArg (MonoidAlgebra.mapRangeRingHom (G0g D.nd) (readT D T i b)) (he.2 g)
    have hs : MonoidAlgebra.mapRangeRingHom (G0g D.nd) (readT D T i b) (MonoidAlgebra.of _ _ g) = MonoidAlgebra.of _ _ g := by
      simp [MonoidAlgebra.of_apply, MonoidAlgebra.mapRangeRingHom]
    rw [map_mul, map_mul, hs] at h
    exact h
  · rw [mul_add, add_mul, hx, hy]
  · rw [mul_smul_comm, smul_mul_assoc, hx]

end Make

section Mt

variable (D : D7) (T : TwR D.LL0 D.nd)

structure WtData where
  Wt : T.Tw → ℕ → Bool → Type
  [acg : ∀ i j b, AddCommGroup (Wt i j b)]
  [mod : ∀ i j b, Module (FractionRing (T.O i)) (Wt i j b)]
  [fd : ∀ i j b, FiniteDimensional (FractionRing (T.O i)) (Wt i j b)]
  rhoW : ∀ i j b, Representation (FractionRing (T.O i)) (GQ D.host.E D.R.nV) (Wt i j b)

attribute [instance] WtData.acg WtData.mod WtData.fd

def toKkT (i : T.Tw) (k : ℕ) : FractionRing (T.O i) →+* FractionRing (T.Ok i k) :=
  IsFractionRing.map (A := T.O i) (B := T.Ok i k) (K := FractionRing (T.O i)) (L := FractionRing (T.Ok i k))
    (j := algebraMap (T.O i) (T.Ok i k)) (T.Ok_inj i k)

abbrev algKkT (i : T.Tw) (k : ℕ) : Algebra (FractionRing (T.O i)) (FractionRing (T.Ok i k)) := (toKkT D T i k).toAlgebra

attribute [local instance] algKkT

abbrev WkT (wt : WtData D T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) : Type :=
  FractionRing (T.Ok i k) ⊗[FractionRing (T.O i)] wt.Wt i j b

def rhoKT (wt : WtData D T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) :
    Representation (FractionRing (T.Ok i k)) (GQ D.host.E D.R.nV) (WkT D T wt i j b k) :=
  bcRep (K' := FractionRing (T.Ok i k)) (wt.rhoW i j b)

structure LevT (i : T.Tw) (k : ℕ) where
  J : Subgroup (GAf D.host.E D.R.nV)
  χ : J →* (FractionRing (T.Ok i k))ˣ
  QP : Finset (PlE D.host)
  DP : Finset (PlE D.host)
  sp : PlE D.host → SplitPlace D.host.E
  redG : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
    (sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)

open Classical in

def MtSubT (wt : WtData D T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Good : LevT D T i k → Prop) :
    Submodule (FractionRing (T.Ok i k)) (GAf D.host.E D.R.nV → WkT D T wt i j b k) :=
  if h : ∃ L : LevT D T i k, Good L ∧
      FiniteDimensional (FractionRing (T.Ok i k)) ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ)
  then NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) h.choose.J h.choose.χ
  else ⊥

theorem fd_MtSubT (wt : WtData D T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Good : LevT D T i k → Prop) :
    FiniteDimensional (FractionRing (T.Ok i k)) ↥(MtSubT D T wt i j b k Good) := by
  by_cases h : ∃ L : LevT D T i k, Good L ∧
      FiniteDimensional (FractionRing (T.Ok i k)) ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ)
  · rw [MtSubT, dif_pos h]
    exact h.choose_spec.2
  · rw [MtSubT, dif_neg h]
    infer_instance

end Mt

section Laws

variable (D : D7) (T : TwR D.LL0 D.nd)

attribute [local instance] algKkT

open Classical in

def psiUTotT (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (b : Bool) (u : G0g D.nd) :
    FractionRing (T.O i) :=
  if h : u ∈ Formalism.IndefR.NX.U D.nd then ((psiUT D T θ i b ⟨u, h⟩ : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) else 1

open Classical in

def gValT (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (k : ℕ) (b : Bool)
    (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (T.O i))ˣ)
    (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) : FractionRing (T.Ok i k) :=
  toKkT D T i k (psiUTotT D T θ i b (Pi.mulSingle kv
    (NX.glOf (NX.redMat s.v red (NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) x))))) *
  (if h : IsUnit (red (NX.intLift s.v (NX.detT D.R.r x))) then
    toKkT D T i k ((τ h.unit : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) else 1)

def baseCoeffToFractionRing (i : T.Tw) : T.O0 i →+* FractionRing (T.O i) :=
  (algebraMap (T.O i) (FractionRing (T.O i))).comp (algebraMap (T.O0 i) (T.O i))

def baseCoeffToExtFractionRing (i : T.Tw) (k : ℕ) : T.O0 i →+* FractionRing (T.Ok i k) :=
  (algebraMap (T.Ok i k) (FractionRing (T.Ok i k))).comp ((algebraMap (T.O i) (T.Ok i k)).comp (algebraMap (T.O0 i) (T.O i)))

def TauTameT (i : T.Tw) (j : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) : Prop :=
  ∃ τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (T.O i))ˣ, ∀ (x : (ZMod (D.host.g kv.1))ˣ) (u : 𝓞 D.host.E),
    (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - u) ∈ (NX.pG D kv).asIdeal →
    ((τ x : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) = baseCoeffToFractionRing D T i (NX.tameVal (T.chi1 i j b) (NX.pG D kv) 1 u).1

open Classical in

def tauT (i : T.Tw) (j : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) :
    (ZMod (D.host.g kv.1))ˣ →* (FractionRing (T.O i))ˣ :=
  if h : TauTameT D T i j b kv then h.choose else 1

def badVT (i : T.Tw) (Q : Finset (PlE D.host)) : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) :=
  {v | ∃ w : PlE D.host, NG.OverPl w v ∧ (w ∈ Q ∨ (∃ k, w ∈ placesOver D.host.E (D.host.g k)) ∨ w ∈ T.pD i)}

def LevLawsT (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ)
    (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ) (L : LevT D T i k) : Prop :=
  (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ L.J, L.χ ⟨κ, h⟩ = 1) ∧
  NX.HypOutsideF L.J L.χ (badVT D T i Q) ∧
  L.QP = qpOf D Pq Q ∧ L.DP = qpOf D Pq (T.pD i) ∧
  L.QP ⊆ Q ∧ (∀ P ∈ Q, ∃ P' ∈ L.QP, P' = P ∨ IsConjPl D.host P P') ∧
  (∀ P ∈ L.QP, ∀ P' ∈ L.QP, ¬ IsConjPl D.host P P') ∧
  L.DP ⊆ T.pD i ∧ (∀ P ∈ T.pD i, ∃ P' ∈ L.DP, P' = P ∨ IsConjPl D.host P P') ∧
  (∀ P ∈ L.DP, ∀ P' ∈ L.DP, ¬ IsConjPl D.host P P') ∧
  (∀ P, (P ∈ L.QP ∨ P ∈ L.DP ∨ ∃ kv, P = NX.pG D kv) → (L.sp P).w = P) ∧
  (∀ κ : GAf D.host.E D.R.nV, κ ∈ L.J ↔ κ ∈ Umax D.host.E D.R.nV ∧
    (∀ kv, NX.InLevG (L.sp (NX.pG D kv)).v D.R.r (NX.locM (L.sp (NX.pG D kv)) κ)) ∧
    (∀ P ∈ L.QP, NX.InParah (L.sp P).v D.R.r (NX.locM (L.sp P) κ)) ∧
    (∀ P ∈ L.DP, NX.InParah (L.sp P).v D.R.r (NX.locM (L.sp P) κ))) ∧
  ∀ κ (h : κ ∈ L.J), ((L.χ ⟨κ, h⟩ : (FractionRing (T.Ok i k))ˣ) : FractionRing (T.Ok i k)) =
    (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), gValT D T θ i k b kv (L.sp (NX.pG D kv)) (L.redG kv) (tauT D T i j b kv)
      (NX.locM (L.sp (NX.pG D kv)) κ)) *
    (∏ P ∈ L.QP, algebraMap (T.Ok i k) (FractionRing (T.Ok i k))
      (NX.tameVal ψ P 1 (NX.resRep (L.sp P) P (NX.detT D.R.r (NX.locM (L.sp P) κ)))).1) *
    (∏ P ∈ L.DP, baseCoeffToExtFractionRing D T i k (NX.tameVal (T.delta i) P (if b then 1 else -1)
      (NX.resRep (L.sp P) P (NX.detT D.R.r (NX.locM (L.sp P) κ)))).1)

end Laws

section Exp

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

theorem fd_WKr (In : RatIn D S) (j : ℕ) : FiniteDimensional S.Ks ↥(WKr D S j) := by
  by_cases h : 1 ≤ j ∧ j ≤ D.R.m
  · rw [WKr_of D S h.1 h.2]
    exact In.fd j h.1 h.2
  · rw [WKr_off D S h]
    infer_instance

theorem fdFmT (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) : FiniteDimensional (FractionRing (T.O i)) (FmT D T S i j b) := by
  haveI := fd_WKr D S In j
  exact (inferInstance : Module.Finite (KT D T i b) (KT D T i b ⊗[S.Ks] ↥(WKr D S j)))

attribute [local instance] algKkT

abbrev MtVT (In : RatIn D S) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T) (i : T.Tw) (j : ℕ)
    (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ) : Type :=
  ↥(MtSubT D T wt i j b k (LevLawsT D T Pq In.θ i j b k Q ψ))

instance fdMtVT (In : RatIn D S) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T) (i : T.Tw)
    (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ) :
    FiniteDimensional (FractionRing (T.Ok i k)) (MtVT D T S In Pq wt i j b k Q ψ) :=
  fd_MtSubT D T wt i j b k _

def MtLatT (In : RatIn D S) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T)
    (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ) :
    Submodule (T.Ok i k) (MtVT D T S In Pq wt i j b k Q ψ) :=
  Submodule.span (T.Ok i k) (Set.range (Module.finBasis (FractionRing (T.Ok i k)) (MtVT D T S In Pq wt i j b k Q ψ)))

theorem MtLatT_fg (In : RatIn D S) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T)
    (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ) :
    (MtLatT D T S In Pq wt i j b k Q ψ).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem MtLatT_span (In : RatIn D S) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T)
    (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ) :
    Submodule.span (FractionRing (T.Ok i k)) (MtLatT D T S In Pq wt i j b k Q ψ : Set (MtVT D T S In Pq wt i j b k Q ψ)) = ⊤ := by
  rw [MtLatT, Submodule.span_span_of_tower, (Module.finBasis _ _).span_eq]

def twDelT (i : T.Tw) (j : ℕ) (b : Bool) (Q : Finset (PlE D.host)) (M : ℕ) :
    FmT D T S i j b →ₗ[T.O i] FmT D T S i j b ⊗[T.O i] AddMonoidAlgebra (T.O i) (DelQM D.host (T.l i) Q M) := 0

def eHT (i : T.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (T.O i)) (FmT D T S i j b) := 1

theorem eHT_idem (i : T.Tw) (j : ℕ) (b : Bool) : eHT D T S i j b * eHT D T S i j b = eHT D T S i j b := one_mul _

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

def mkEx (In : RatIn D S) (hE : IsEmpty D.nd.Loc) (hfg : ∀ i j b, (BsupT D T S i j b).FG) (hst : HkStab D T S In) (sd : SigData D T)
    (rho : RhoFam D T) (hrho : ∀ i σ b, Continuous fun g =>
      ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i)))
    (he : EIdem D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T) :
    NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)) where
  Fm := FmT D T S
  acgFm := fun (i : T.Tw) j b => acgFmT D T S i j b
  modFmK := fun (i : T.Tw) j b => modKFmT D T S i j b
  modFmO := fun (i : T.Tw) j b => modOFmT D T S i j b
  towFm := fun (i : T.Tw) j b => towFmT D T S i j b
  fdFm := fun (i : T.Tw) j b => fdFmT D T S In i j b
  actG := actGT D T S In.rho In.chi
  U := Formalism.IndefR.NX.U D.nd
  psiU := psiUT D T In.θ
  eAlg := eAlgT D T
  eLL0 := D.nexp.eLL0
  eAlg_def := fun i b g => rfl
  eAlg_idem := eAlgT_idem D T he
  eAlg_central := eAlgT_central D T he
  Bsup := BsupT D T S
  Dat := fun _ _ _ => PEmpty
  th := fun _ _ _ d => d.elim
  lev := fun _ _ _ d => d.elim
  thPsi := fun _ _ _ _ _ _ d => d.elim
  thPsi_one := fun _ _ _ _ d => d.elim
  thU := fun _ _ _ _ _ d => d.elim
  twPsi := fun (i : T.Tw) j b k _ => TensorProduct.mk (T.O i) (T.Ok i k) (FmT D T S i j b) 1
  twPsi_one := fun _ _ _ _ _ => rfl
  twDel := fun (i : T.Tw) j b Q M => twDelT D T S i j b Q M
  delU := fun i Q M => GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M
  delU_unr := fun i Q M v hv A hA σ hσ => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).1 Q M v hv A hA σ hσ
  delU_l := fun i Q M v hv A hA σ hσ => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.1 Q M v hv A hA σ hσ
  delU_anti := fun i Q M => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.2.1 Q M
  delU_open := fun i Q M => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.2.2.1 Q M
  delU_res := fun i M Q' Q h h1 h2 σ P hP => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.2.2.2.1 M Q' Q h h1 h2 σ P hP
  delU_conj := fun i Q M P hP P' hP' h => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.2.2.2.2.1 Q M P hP P' hP' h
  MtV := MtVT D T S In Pq wt
  acgMt := fun (i : T.Tw) j b k Q ψ => inferInstanceAs (AddCommGroup (MtVT D T S In Pq wt i j b k Q ψ))
  modMtK := fun (i : T.Tw) j b k Q ψ => inferInstanceAs (Module (FractionRing (T.Ok i k)) (MtVT D T S In Pq wt i j b k Q ψ))
  modMtO := fun (i : T.Tw) j b k Q ψ => inferInstanceAs (Module (T.Ok i k) (MtVT D T S In Pq wt i j b k Q ψ))
  towMt := fun (i : T.Tw) j b k Q ψ =>
    inferInstanceAs (IsScalarTower (T.Ok i k) (FractionRing (T.Ok i k)) (MtVT D T S In Pq wt i j b k Q ψ))
  fdMt := fun (i : T.Tw) j b k Q ψ => fdMtVT D T S In Pq wt i j b k Q ψ
  MtLat := fun (i : T.Tw) j b k Q ψ => MtLatT D T S In Pq wt i j b k Q ψ
  MtLat_fg := fun (i : T.Tw) j b k Q ψ => MtLatT_fg D T S In Pq wt i j b k Q ψ
  MtLat_span := fun (i : T.Tw) j b k Q ψ => MtLatT_span D T S In Pq wt i j b k Q ψ
  thP := fun _ _ _ _ _ _ => 0
  hkF := fun (i : T.Tw) j b k P => hkT D T S In i j b k P
  embB := fun (i : T.Tw) j b => (BI D T S In i j b).subtype
  embB_inj := fun (i : T.Tw) j b => Subtype.val_injective
  eH := fun (i : T.Tw) j b => eHT D T S i j b
  eH_idem := fun (i : T.Tw) j b => eHT_idem D T S i j b

end Exp

section Extra

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

theorem hLr_zero (In : RatIn D S) (j : ℕ) (P : PlE D.host) : hLr D S In j 0 P = 1 := by
  unfold hLr
  split_ifs with h
  · refine LinearMap.ext fun x => Subtype.ext ?_
    change In.hL j 0 P (x : S.WL j) = (x : S.WL j)
    rw [In.hL_zero]
    rfl
  · rfl

theorem hkT_zero (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (P : PlE D.host) : hkT D T S In i j b 0 P = 1 := by
  unfold hkT
  rw [hLr_zero, map_one, pow_zero, one_smul]
  rfl

def kEmbT (i : T.Tw) (b : Bool) (t : D.what₂.Tau) : D.host.E →+* FractionRing (T.O i) :=
  (readT D T i b).comp ((NX.embEL0 D).comp
    (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) : D.host.E →+* D.host.E))

def SigData.unit (hm : 1 ≤ D.R.m) (σ₀ : D.what₂.FT) : SigData D T where
  Sig := fun _ => Unit
  jS := fun _ _ => 1
  jS_range := fun _ _ => ⟨le_rfl, hm⟩
  side := fun _ _ => true
  hEig := fun _ _ _ _ => 1
  rowS := fun _ _ => σ₀

def WtData.triv : WtData D T where
  Wt := fun i _ _ => FractionRing (T.O i)
  rhoW := fun i _ _ => Representation.trivial (FractionRing (T.O i)) (GQ D.host.E D.R.nV) (FractionRing (T.O i))

def LevT.ofPlaces (i : T.Tw) (k : ℕ) (sp : PlE D.host → SplitPlace D.host.E)
    (redG : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      (sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)) :
    LevT D T i k where
  J := ⊤
  χ := 1
  QP := ∅
  DP := ∅
  sp := sp
  redG := redG

end Extra

end GlobalTheory.HeightCounting.FormsStep
