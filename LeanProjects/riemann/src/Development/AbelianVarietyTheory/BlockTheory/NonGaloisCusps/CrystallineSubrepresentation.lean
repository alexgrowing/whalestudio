import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Objects

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

def IsEquivariant (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V') :
    Prop :=
  ∀ g x, f (ρ g x) = ρ' g (f x)

theorem mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem actVB_mulVB (ρ : Representation LL G V) (g : G) (c : K₀) (x : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (actVB PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, mulVB]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem comm_smul (c : K₀) (x : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (c • x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (TensorProduct.comm Qp B V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
    rw [TensorProduct.smul_tmul', Algebra.smul_def]
    simp [mulVB]
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]

def DcrisK₀ (ρ : Representation LL G V) : Submodule K₀ (B ⊗[Qp] V) where
  carrier := {x | TensorProduct.comm Qp B V x ∈ Dcris PD ρ}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact (Dcris PD ρ).add_mem ha hb
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, mem_Dcris] at hx ⊢
    intro g
    rw [comm_smul (LL := LL), actVB_mulVB, hx]

def comparison (ρ : Representation LL G V) :
    B ⊗[K₀] ↥(DcrisK₀ PD ρ) →ₗ[B] B ⊗[Qp] V :=
  LinearMap.liftBaseChange B (DcrisK₀ PD ρ).subtype

theorem comparison_tmul (ρ : Representation LL G V) (b : B) (d : ↥(DcrisK₀ PD ρ)) :
    comparison PD ρ (b ⊗ₜ[K₀] d) = b • (d : B ⊗[Qp] V) := by
  simp [comparison]

def tensorB (f : V →ₗ[LL] V') : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B :=
  AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)

theorem tensorB_mem {ρ : Representation LL G V} {ρ' : Representation LL G V'} {f : V →ₗ[LL] V'}
    (hf : IsEquivariant ρ ρ' f) (x : V ⊗[Qp] B) (hx : x ∈ Dcris PD ρ) :
    tensorB (Qp := Qp) (B := B) f x ∈ Dcris PD ρ' := by
  have hm : ∀ g y, tensorB (Qp := Qp) (B := B) f (actVB PD ρ g y) =
      actVB PD ρ' g (tensorB (Qp := Qp) (B := B) f y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [tensorB, actVB, hf g]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [mem_Dcris] at hx ⊢
  intro g
  rw [← hm, hx]

def DcrisMap {ρ : Representation LL G V} {ρ' : Representation LL G V'} {f : V →ₗ[LL] V'}
    (hf : IsEquivariant ρ ρ' f) : ↥(Dcris PD ρ) →ₗ[LL] ↥(Dcris PD ρ') :=
  (tensorB (Qp := Qp) (B := B) f).restrict (tensorB_mem PD hf)

def prodB : (V ⊗[Qp] B) ⊗[LL] (V' ⊗[Qp] B) →ₗ[LL] (V ⊗[LL] V') ⊗[Qp] B :=
  (AlgebraTensorModule.map (LinearMap.id : V ⊗[LL] V' →ₗ[LL] V ⊗[LL] V')
      (LinearMap.mul' Qp B)).comp
    (AlgebraTensorModule.tensorTensorTensorComm Qp Qp LL LL V B V' B).toLinearMap

theorem prodB_tmul (v : V) (b : B) (v' : V') (b' : B) :
    prodB (LL := LL) ((v ⊗ₜ[Qp] b) ⊗ₜ[LL] (v' ⊗ₜ[Qp] b')) = (v ⊗ₜ[LL] v') ⊗ₜ[Qp] (b * b') := by
  simp [prodB]

end Objects

def InvariantsEq : Prop :=
  ∀ b : B, (∀ g, PD.actB g b = b) ↔ b ∈ Set.range (algebraMap K₀ B)

theorem invariantsEq : InvariantsEq PD := fun b =>
  ⟨fun h => PD.invB b h, by
    rintro ⟨c, rfl⟩ g
    exact (PD.actB g).commutes c⟩

variable (LL : Type) [Field LL] [Algebra Qp LL]

def DimLe : Prop :=
  FontaineLe PD LL ∧
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V), FiniteDimensional LL ↥(Dcris PD ρ)

def ComparisonBij : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    IsCrys PD ρ → Function.Bijective (comparison PD ρ)

def SubCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V') (f : V' →ₗ[LL] V),
    IsEquivariant ρ' ρ f → Function.Injective f → IsCrys PD ρ → IsCrys PD ρ'

def QuotCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V') (f : V →ₗ[LL] V'),
    IsEquivariant ρ ρ' f → Function.Surjective f → IsCrys PD ρ → IsCrys PD ρ'

def SumCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' → IsCrys PD (ρ.prod ρ')

def TensorCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' → IsCrys PD (ρ.tprod ρ')

def DualCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    IsCrys PD ρ → IsCrys PD ρ.dual

def DcrisExact : Prop :=
  ∀ (V₀ : Type) [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    [FiniteDimensional LL V₀] (ρ₀ : Representation LL G V₀)
    (V₁ : Type) [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [FiniteDimensional LL V₁] (ρ₁ : Representation LL G V₁)
    (V₂ : Type) [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    [FiniteDimensional LL V₂] (ρ₂ : Representation LL G V₂)
    (i : V₀ →ₗ[LL] V₁) (p : V₁ →ₗ[LL] V₂) (hi : IsEquivariant ρ₀ ρ₁ i) (hp : IsEquivariant ρ₁ ρ₂ p),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    IsCrys PD ρ₀ → IsCrys PD ρ₁ → IsCrys PD ρ₂ →
    Function.Injective (DcrisMap PD hi) ∧ Function.Exact (DcrisMap PD hi) (DcrisMap PD hp) ∧
      Function.Surjective (DcrisMap PD hp)

def LetterDim : Prop :=
  Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀ →
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V), IsCrys PD ρ →
    ∀ τ₀ : K₀ →ₐ[Qp] LL,
      FiniteDimensional LL ↥(DcrisL PD ρ τ₀) ∧ finrank LL ↥(DcrisL PD ρ τ₀) = finrank LL V

def DcrisTensor : Prop :=
  Dcris PD (Representation.trivial LL G LL) =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) ∧
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' →
    LinearMap.range ((prodB (LL := LL)).comp
        (TensorProduct.map (Dcris PD ρ).subtype (Dcris PD ρ').subtype)) = Dcris PD (ρ.tprod ρ') ∧
    ∀ τ₀ : K₀ →ₐ[Qp] LL,
      Function.Injective ((prodB (LL := LL)).comp
        (TensorProduct.map (DcrisL PD ρ τ₀).subtype (DcrisL PD ρ' τ₀).subtype)) ∧
      LinearMap.range ((prodB (LL := LL)).comp
        (TensorProduct.map (DcrisL PD ρ τ₀).subtype (DcrisL PD ρ' τ₀).subtype)) =
        DcrisL PD (ρ.tprod ρ') τ₀

def FormalismFor : Prop :=
  InvariantsEq PD ∧ DimLe PD LL ∧ ComparisonBij PD LL ∧ SubCrys PD LL ∧ QuotCrys PD LL ∧
    SumCrys PD LL ∧ TensorCrys PD LL ∧ DualCrys PD LL ∧ DcrisExact PD LL ∧ LetterDim PD LL

end Generic

section Local

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

def LocInvariantsEq : Prop := ∀ K : FinExt l, InvariantsEq (P.PD K)

def LocDimLe : Prop := ∀ K LL : FinExt l, DimLe (P.PD K) ↥LL.1

def LocComparisonBij : Prop := ∀ K LL : FinExt l, ComparisonBij (P.PD K) ↥LL.1

def LocSubCrys : Prop := ∀ K LL : FinExt l, SubCrys (P.PD K) ↥LL.1

def LocQuotCrys : Prop := ∀ K LL : FinExt l, QuotCrys (P.PD K) ↥LL.1

def LocSumCrys : Prop := ∀ K LL : FinExt l, SumCrys (P.PD K) ↥LL.1

def LocTensorCrys : Prop := ∀ K LL : FinExt l, TensorCrys (P.PD K) ↥LL.1

def LocDualCrys : Prop := ∀ K LL : FinExt l, DualCrys (P.PD K) ↥LL.1

def LocDcrisExact : Prop := ∀ K LL : FinExt l, DcrisExact (P.PD K) ↥LL.1

def LocLetterDim : Prop := ∀ K LL : FinExt l, LetterDim (P.PD K) ↥LL.1

def LocDcrisTensor : Prop := ∀ K LL : FinExt l, DcrisTensor (P.PD K) ↥LL.1

def FontaineFormalism : Prop :=
  LocInvariantsEq l P ∧ LocDimLe l P ∧ LocComparisonBij l P ∧ LocSubCrys l P ∧ LocQuotCrys l P ∧
    LocSumCrys l P ∧ LocTensorCrys l P ∧ LocDualCrys l P ∧ LocDcrisExact l P ∧ LocLetterDim l P

def FontaineFormalismTensor : Prop := FontaineFormalism l P ∧ LocDcrisTensor l P

theorem fontaineFormalism_iff :
    FontaineFormalism l P ↔ ∀ K LL : FinExt l, FormalismFor (P.PD K) ↥LL.1 :=
  ⟨fun h K LL => ⟨h.1 K, h.2.1 K LL, h.2.2.1 K LL, h.2.2.2.1 K LL, h.2.2.2.2.1 K LL,
      h.2.2.2.2.2.1 K LL, h.2.2.2.2.2.2.1 K LL, h.2.2.2.2.2.2.2.1 K LL, h.2.2.2.2.2.2.2.2.1 K LL,
      h.2.2.2.2.2.2.2.2.2 K LL⟩,
    fun h => ⟨fun K => (h K K).1, fun K LL => (h K LL).2.1, fun K LL => (h K LL).2.2.1,
      fun K LL => (h K LL).2.2.2.1, fun K LL => (h K LL).2.2.2.2.1,
      fun K LL => (h K LL).2.2.2.2.2.1, fun K LL => (h K LL).2.2.2.2.2.2.1,
      fun K LL => (h K LL).2.2.2.2.2.2.2.1, fun K LL => (h K LL).2.2.2.2.2.2.2.2.1,
      fun K LL => (h K LL).2.2.2.2.2.2.2.2.2⟩⟩

example (h : FontaineFormalism l P) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys (P.PD K) T.ρ) :
    IsCrys (P.PD K) T.ρ.dual ∧ Function.Bijective (comparison (P.PD K) T.ρ) :=
  ⟨h.2.2.2.2.2.2.2.1 K LL T.V T.ρ hT, h.2.2.1 K LL T.V T.ρ hT⟩

end Local

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation
