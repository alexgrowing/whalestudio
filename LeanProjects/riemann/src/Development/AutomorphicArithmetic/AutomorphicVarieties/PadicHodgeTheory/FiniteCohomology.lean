import Mathlib
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

noncomputable section

namespace UpperTheory.V.Loc

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module

section Groups

variable (v : ℕ) [Fact v.Prime]

def Iq : Subgroup (GQ v) := (MaximalUnramifiedExtension v).fixingSubgroup

variable {v} in

def IsFrob (σ : GQ v) : Prop := ∀ x : Om v, ‖x‖ ≤ 1 → ‖σ x - x ^ v‖ < 1

def cyc (l : ℕ) [Fact l.Prime] : GQ v →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (Om v) l).comp (MulSemiringAction.toRingAut (GQ v) (Om v))

def cycA (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [Algebra ℤ_[l] A] : GQ v →* Aˣ :=
  (Units.map (algebraMap ℤ_[l] A : ℤ_[l] →* A)).comp (cyc v l)

def botExt : FinExt v := ⟨⊥, inferInstance⟩

variable {v}

def incl {K K' : FinExt v} (h : K.1 ≤ K'.1) : ↥(GK K') →* ↥(GK K) :=
  Subgroup.inclusion fun _ hg x => hg ⟨x.1, h x.2⟩

def HasWeight {G A : Type} [Group G] [TopologicalSpace G] [CommRing A] [Algebra ℤ_[v] A]
    (φ : G →* GQ v) (κ : G →* Aˣ) (w : ℤ) : Prop :=
  ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g ∈ U, φ g ∈ Iq v → κ g = cycA v v A (φ g) ^ w

end Groups

section Rep

variable {G A : Type} [Group G] [CommRing A]

def chRep (κ : G →* Aˣ) : Representation A G A where
  toFun g := ((κ g : Aˣ) : A) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]

def colRep {n : Type} [Fintype n] [DecidableEq n] (r : G →* GL n A) : Representation A G (n → A) where
  toFun g := Matrix.toLin' (r g : Matrix n n A)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Module.End.mul_eq_comp]

def adGL {n : Type} [Fintype n] [DecidableEq n] (r : G →* GL n A) : Representation A G (Matrix n n A) where
  toFun g :=
    { toFun := fun X => (r g : Matrix n n A) * X * ((r g)⁻¹ : GL n A)
      map_add' := fun X Y => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a X => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  map_one' := by ext1 X; simp
  map_mul' g h := by
    ext1 X
    simp only [map_mul, Units.val_mul, mul_inv_rev, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
      Matrix.mul_assoc]

def resCoef (Q : Type) [CommRing Q] [Algebra Q A] {V : Type} [AddCommGroup V] [Module A V] [Module Q V]
    [IsScalarTower Q A V] (ρ : Representation A G V) : Representation Q G V where
  toFun g := (ρ g).restrictScalars Q
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

end Rep

section Period

variable (l : ℕ) [Fact l.Prime]

def PP : LocPrime l := (GlobalTheory.MemLoc.exists_locPrime_tied l).choose

def AIP : LocAinf l (PP l) := (GlobalTheory.MemLoc.exists_locPrime_tied l).choose_spec.choose

theorem tiedP : Nonempty (LocTied l (PP l) (AIP l)) := (GlobalTheory.MemLoc.exists_locPrime_tied l).choose_spec.choose_spec

abbrev Bcr : Type := (PP l).R.B

abbrev Bdr : Type := (PP l).R.BdR

variable {l}
variable {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (ρ : Representation A G V)

def actC (g : G) : V ⊗[ℚ_[l]] Bcr l →ₗ[A] V ⊗[ℚ_[l]] Bcr l :=
  AlgebraTensorModule.map (ρ g) ((PP l).actQ (φ g)).toLinearMap

def actD (g : G) : V ⊗[ℚ_[l]] Bdr l →ₗ[A] V ⊗[ℚ_[l]] Bdr l :=
  AlgebraTensorModule.map (ρ g) ((PP l).actQdR (φ g)).toLinearMap

def Dcr : Submodule A (V ⊗[ℚ_[l]] Bcr l) := ⨅ g : G, LinearMap.ker (actC φ ρ g - LinearMap.id)

def Ddr : Submodule A (V ⊗[ℚ_[l]] Bdr l) := ⨅ g : G, LinearMap.ker (actD φ ρ g - LinearMap.id)

variable (A V) in

def FilT (a : ℤ) : Submodule A (V ⊗[ℚ_[l]] Bdr l) :=
  LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[A] V)
    ((((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l]).subtype)

def FilD (a : ℤ) : Submodule A (V ⊗[ℚ_[l]] Bdr l) := Ddr φ ρ ⊓ FilT A V a

def finiteCocycles [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] :
    Submodule A (G → V) where
  carrier := {c | c ∈ Z1 ρ ∧ ∃ x : V ⊗[ℚ_[l]] Bcr l, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actC φ ρ g x - x}
  zero_mem' := ⟨(Z1 ρ).zero_mem, 0, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hx⟩ ⟨hb, y, hy⟩
    refine ⟨(Z1 ρ).add_mem ha hb, x + y, fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hx⟩
    refine ⟨(Z1 ρ).smul_mem c ha, c • x, fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

def finiteCohomology [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] :
    Submodule A (H1 ρ) :=
  ((finiteCocycles φ ρ).comap (Z1 ρ).subtype).map (Submodule.mkQ _)

end Period

section admitted

variable {l : ℕ} [Fact l.Prime] {A V : Type} [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]

def Crys (K : FinExt l) (ρ : Representation A ↥(GK K) V) : Prop := IsCrys ((PP l).PD K) (resCoef ℚ_[l] ρ)

def DeRham (K : FinExt l) (ρ : Representation A ↥(GK K) V) : Prop := IsDR ((PP l).PD K) (resCoef ℚ_[l] ρ)

def Semist (K : FinExt l) (ρ : Representation A ↥(GK K) V) : Prop := GlobalTheory.Pst.IsSst (PP l) (resCoef ℚ_[l] ρ)

variable (V) in

def smulD (K : FinExt l) : A ⊗[ℚ_[l]] ↥K.1 →ₗ[ℚ_[l]] Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bdr l) :=
  (TensorProduct.homTensorHomMap (RingHom.id ℚ_[l]) V (Bdr l) V (Bdr l)).comp
    (TensorProduct.map (Algebra.lsmul ℚ_[l] ℚ_[l] V : A →ₐ[ℚ_[l]] Module.End ℚ_[l] V).toLinearMap
      (Algebra.lsmul ℚ_[l] ℚ_[l] (Bdr l) : ↥K.1 →ₐ[ℚ_[l]] Module.End ℚ_[l] (Bdr l)).toLinearMap)

variable (V) in

def smulC (K : FinExt l) : A ⊗[ℚ_[l]] ↥(K0 K) →ₗ[ℚ_[l]] Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bcr l) :=
  (TensorProduct.homTensorHomMap (RingHom.id ℚ_[l]) V (Bcr l) V (Bcr l)).comp
    (TensorProduct.map (Algebra.lsmul ℚ_[l] ℚ_[l] V : A →ₐ[ℚ_[l]] Module.End ℚ_[l] V).toLinearMap
      (Algebra.lsmul ℚ_[l] ℚ_[l] (Bcr l) : ↥(K0 K) →ₐ[ℚ_[l]] Module.End ℚ_[l] (Bcr l)).toLinearMap)

def HodgeType (K : FinExt l) (ρ : Representation A ↥(GK K) V) (m : ℤ → ℕ) : Prop :=
  ∀ i : ℤ, ∃ x : Fin (m i) → V ⊗[ℚ_[l]] Bdr l, (∀ a, x a ∈ FilD (GK K).subtype ρ i) ∧
    ∀ y ∈ FilD (GK K).subtype ρ i, ∃! c : Fin (m i) → A ⊗[ℚ_[l]] ↥K.1,
      y - ∑ a, smulD V K (c a) (x a) ∈ FilD (GK K).subtype ρ (i + 1)

def CrysTypeOver (K L : FinExt l) (h : K.1 ≤ L.1) (ρ : Representation A ↥(GK K) V) (n : ℕ)
    (t : ↥(GK K) → A) : Prop :=
  ((GK L).subgroupOf (GK K)).Normal ∧ Crys L (ρ.comp (incl h)) ∧
  ∃ x : Fin n → V ⊗[ℚ_[l]] Bcr l, (∀ a, x a ∈ Dcr (GK L).subtype (ρ.comp (incl h))) ∧
    (∀ y ∈ Dcr (GK L).subtype (ρ.comp (incl h)), ∃! c : Fin n → A ⊗[ℚ_[l]] ↥(K0 L),
      y = ∑ a, smulC V L (c a) (x a)) ∧
    ∀ γ : ↥(GK K), (γ : GQ l) ∈ Iq l → ∀ M : Matrix (Fin n) (Fin n) (A ⊗[ℚ_[l]] ↥(K0 L)),
      (∀ b, actC (GK K).subtype ρ γ (x b) = ∑ a, smulC V L (M a b) (x a)) → M.trace = t γ ⊗ₜ[ℚ_[l]] 1

def PotCrysType (K : FinExt l) (ρ : Representation A ↥(GK K) V) (n : ℕ) (m : ℤ → ℕ) (t : ↥(GK K) → A) : Prop :=
  HodgeType K ρ m ∧ ∃ (L : FinExt l) (h : K.1 ≤ L.1), CrysTypeOver K L h ρ n t

end admitted

end UpperTheory.V.Loc
