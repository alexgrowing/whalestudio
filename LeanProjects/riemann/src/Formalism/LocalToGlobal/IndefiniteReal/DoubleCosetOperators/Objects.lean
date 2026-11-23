import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose

noncomputable section

open NumberField TensorProduct Formalism.BasicNotions

namespace Formalism.IndefR.NX

section Dat

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂}

structure RatDat (tw : NTw R H what₂ LL0 N) where
  Ks : Type
  [fKs : Field Ks]
  [nfKs : NumberField Ks]
  [algKs : Algebra Ks what₂.LL]
  WL : ℕ → Type
  [acgWL : ∀ j, AddCommGroup (WL j)]
  [modWL : ∀ j, Module what₂.LL (WL j)]
  [modKsWL : ∀ j, Module Ks (WL j)]
  [towWL : ∀ j, IsScalarTower Ks what₂.LL (WL j)]
  [modOLLWL : ∀ j, Module (𝓞 what₂.LL) (WL j)]
  [towOLLWL : ∀ j, IsScalarTower (𝓞 what₂.LL) what₂.LL (WL j)]
  [modOKsWL : ∀ j, Module (𝓞 Ks) (WL j)]
  [towOKsWL : ∀ j, IsScalarTower (𝓞 Ks) Ks (WL j)]
  W : ℕ → (what₂.LL →+* ℂ) → Type
  [nW : ∀ j σ, NormedAddCommGroup (W j σ)]
  [ipW : ∀ j σ, InnerProductSpace ℂ (W j σ)]

  G : Type
  [grpG : Group G]
  eG : G ≃* G0g N

  A : ∀ j, Arith.FormsL what₂.LL Ks (WL j) (W j) G

  kKs : Ks →+* ↥LL0
  kKs_spec : ∀ x : Ks, ((kKs x : ↥LL0) : what₂.LL) = algebraMap Ks what₂.LL x

attribute [instance] RatDat.fKs RatDat.nfKs RatDat.algKs RatDat.acgWL RatDat.modWL RatDat.modKsWL RatDat.towWL
  RatDat.modOLLWL RatDat.towOLLWL RatDat.modOKsWL RatDat.towOKsWL RatDat.nW RatDat.ipW RatDat.grpG

variable {tw : NTw R H what₂ LL0 N} (S : RatDat tw)

def KB (_S : RatDat tw) (i : tw.Tw) (_b : Bool) : Type := FractionRing (tw.O i)

instance (i : tw.Tw) (b : Bool) : Field (KB S i b) := inferInstanceAs (Field (FractionRing (tw.O i)))

def readLL0 (i : tw.Tw) (b : Bool) : ↥LL0 →+* KB S i b :=
  (IsFractionRing.map (A := tw.O0 i) (B := tw.O i) (K := FractionRing (tw.O0 i)) (L := FractionRing (tw.O i))
    (tw.O_inj i)).comp (if b then tw.emb0 i else tw.emb0b i)

def ιK (i : tw.Tw) (b : Bool) : S.Ks →+* KB S i b := (readLL0 S i b).comp S.kKs

instance (i : tw.Tw) (b : Bool) : Algebra S.Ks (KB S i b) := (ιK S i b).toAlgebra

def FmK (j : ℕ) : Type := ↥(S.A j).WK

instance (j : ℕ) : AddCommGroup (FmK S j) := inferInstanceAs (AddCommGroup ↥(S.A j).WK)

instance (j : ℕ) : Module S.Ks (FmK S j) := inferInstanceAs (Module S.Ks ↥(S.A j).WK)

def Fm (i : tw.Tw) (j : ℕ) (b : Bool) : Type := KB S i b ⊗[S.Ks] FmK S j

instance acgFm (i : tw.Tw) (j : ℕ) (b : Bool) : AddCommGroup (Fm S i j b) :=
  inferInstanceAs (AddCommGroup (KB S i b ⊗[S.Ks] FmK S j))

instance modKB (i : tw.Tw) (j : ℕ) (b : Bool) : Module (KB S i b) (Fm S i j b) :=
  inferInstanceAs (Module (KB S i b) (KB S i b ⊗[S.Ks] FmK S j))

instance modFmK (i : tw.Tw) (j : ℕ) (b : Bool) : Module (FractionRing (tw.O i)) (Fm S i j b) :=
  modKB S i j b

instance modFmO (i : tw.Tw) (j : ℕ) (b : Bool) : Module (tw.O i) (Fm S i j b) :=
  Module.compHom (Fm S i j b) (algebraMap (tw.O i) (FractionRing (tw.O i)))

instance towFm (i : tw.Tw) (j : ℕ) (b : Bool) :
    IsScalarTower (tw.O i) (FractionRing (tw.O i)) (Fm S i j b) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem finiteDimensional_Fm (i : tw.Tw) (j : ℕ) (b : Bool) [FiniteDimensional S.Ks (FmK S j)] :
    FiniteDimensional (FractionRing (tw.O i)) (Fm S i j b) := by
  change Module.Finite (KB S i b) (KB S i b ⊗[S.Ks] FmK S j)
  infer_instance

def Bsup (i : tw.Tw) (j : ℕ) (b : Bool) : Submodule (tw.O i) (Fm S i j b) :=
  Submodule.span (tw.O i)
    {f | ∃ x : FmK S j, (show ↥(S.A j).WK from x).1 ∈ (S.A j).MK ∧
      f = ((1 : KB S i b) ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j)}

end Dat

section Act

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} {tw : NTw R H what₂ LL0 N} (S : RatDat tw)

def RhoStab (j : ℕ) : Prop := ∀ (g : S.G) (x : S.WL j), x ∈ (S.A j).WK → (S.A j).ρ g x ∈ (S.A j).WK

def ChiInLL0 (j : ℕ) : Prop := ∀ g : S.G, (((S.A j).chi g : what₂.LLˣ) : what₂.LL) ∈ LL0

def chiL (j : ℕ) (hχ : ChiInLL0 S j) (g : S.G) : ↥LL0 := ⟨(((S.A j).chi g : what₂.LLˣ) : what₂.LL), hχ g⟩

theorem chiL_one (j : ℕ) (hχ : ChiInLL0 S j) : chiL S j hχ 1 = 1 := by
  apply Subtype.ext
  simp [chiL]

theorem chiL_mul (j : ℕ) (hχ : ChiInLL0 S j) (g h : S.G) : chiL S j hχ (g * h) = chiL S j hχ g * chiL S j hχ h := by
  apply Subtype.ext
  simp [chiL]

def rhoKG (j : ℕ) (hst : RhoStab S j) : S.G →* Module.End S.Ks (FmK S j) where
  toFun g := (((S.A j).ρ g).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK)
    fun x hx => hst g x hx
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (S.A j).ρ 1 (show ↥(S.A j).WK from x).1 = (show ↥(S.A j).WK from x).1
    rw [map_one]
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (S.A j).ρ (g * h) (show ↥(S.A j).WK from x).1 =
      (S.A j).ρ g ((S.A j).ρ h (show ↥(S.A j).WK from x).1)
    rw [map_mul]
    rfl

def actEnd (i : tw.Tw) (j : ℕ) (b : Bool) (hst : RhoStab S j) (hχ : ChiInLL0 S j) :
    S.G →* Module.End (KB S i b) (KB S i b ⊗[S.Ks] FmK S j) where
  toFun g := (readLL0 S i b (chiL S j hχ g))⁻¹ •
    Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst g)
  map_one' := by
    rw [chiL_one, map_one, inv_one, one_smul, map_one, map_one]
  map_mul' g h := by
    rw [chiL_mul, map_mul, mul_inv, map_mul, map_mul]
    exact (smul_mul_smul_comm _ _ _ _).symm

def actG (i : tw.Tw) (j : ℕ) (b : Bool) (hst : RhoStab S j) (hχ : ChiInLL0 S j) :
    G0g N →* (Fm S i j b ≃ₗ[FractionRing (tw.O i)] Fm S i j b) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (KB S i b) (KB S i b ⊗[S.Ks] FmK S j)).toMonoidHom.comp
    (MonoidHom.toHomUnits ((actEnd S i j b hst hχ).comp S.eG.symm.toMonoidHom))

instance : Algebra S.Ks ↥LL0 := S.kKs.toAlgebra

def inWL (j : ℕ) : ↥LL0 ⊗[S.Ks] FmK S j →ₗ[S.Ks] S.WL j :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun f => ((x : ↥LL0) : what₂.LL) • (show ↥(S.A j).WK from f).1
          map_add' := fun f f' => by
            change ((x : ↥LL0) : what₂.LL) • ((show ↥(S.A j).WK from f).1 + (show ↥(S.A j).WK from f').1) = _
            rw [smul_add]
          map_smul' := fun c f => by
            change ((x : ↥LL0) : what₂.LL) • (c • (show ↥(S.A j).WK from f).1) = c • (((x : ↥LL0) : what₂.LL) • _)
            rw [smul_comm] }
      map_add' := fun x y => by
        ext f
        simp [add_smul]
      map_smul' := fun c x => by
        ext f
        change (((c • x : ↥LL0) : ↥LL0) : what₂.LL) • (show ↥(S.A j).WK from f).1 =
          c • (((x : ↥LL0) : what₂.LL) • (show ↥(S.A j).WK from f).1)
        rw [Algebra.smul_def, IntermediateField.coe_mul, mul_smul]
        change ((S.kKs c : ↥LL0) : what₂.LL) • _ = _
        rw [S.kKs_spec, algebraMap_smul] }

def IsThOf (j : ℕ) (σ0 : what₂.LL →+* ℂ) (thC : S.W j σ0) (x : ↥LL0 ⊗[S.Ks] FmK S j) : Prop :=
  (S.A j).j σ0 (inWL S j x) = thC

theorem IsThOf.unique {j : ℕ} {σ0 : what₂.LL →+* ℂ} {thC : S.W j σ0} {x y : ↥LL0 ⊗[S.Ks] FmK S j}
    (hinj : Function.Injective fun z : ↥LL0 ⊗[S.Ks] FmK S j => (S.A j).j σ0 (inWL S j z))
    (hx : IsThOf S j σ0 thC x) (hy : IsThOf S j σ0 thC y) : x = y :=
  hinj ((show (S.A j).j σ0 (inWL S j x) = thC from hx).trans (show (S.A j).j σ0 (inWL S j y) = thC from hy).symm)

def ThExists {Dat : Type} (j : ℕ) (σ0 : what₂.LL →+* ℂ) (thC : Dat → S.W j σ0) : Prop :=
  ∀ d, ∃ x : ↥LL0 ⊗[S.Ks] FmK S j, IsThOf S j σ0 (thC d) x

def thK {Dat : Type} (j : ℕ) (σ0 : what₂.LL →+* ℂ) (thC : Dat → S.W j σ0) (h : ThExists S j σ0 thC) (d : Dat) :
    ↥LL0 ⊗[S.Ks] FmK S j :=
  (h d).choose

theorem thK_spec {Dat : Type} (j : ℕ) (σ0 : what₂.LL →+* ℂ) (thC : Dat → S.W j σ0) (h : ThExists S j σ0 thC)
    (d : Dat) : IsThOf S j σ0 (thC d) (thK S j σ0 thC h d) :=
  (h d).choose_spec

def readLL0Ks (i : tw.Tw) (b : Bool) : ↥LL0 →ₗ[S.Ks] KB S i b where
  toFun := readLL0 S i b
  map_add' := map_add _
  map_smul' c x := by
    change readLL0 S i b (S.kKs c * x) = ιK S i b c * readLL0 S i b x
    rw [map_mul]
    rfl

def thOf {Dat : Type} (i : tw.Tw) (j : ℕ) (b : Bool) (σ0 : what₂.LL →+* ℂ) (thC : Dat → S.W j σ0)
    (h : ThExists S j σ0 thC) (d : Dat) : Fm S i j b :=
  (LinearMap.rTensor (FmK S j) (readLL0Ks S i b) (thK S j σ0 thC h d) : KB S i b ⊗[S.Ks] FmK S j)

end Act

end Formalism.IndefR.NX
