import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership

open NumberField IsDedekindDomain Formalism.IndefR.Arith

section Clause

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL)

def IsCoord {d : ℕ} (b : Fin d → WL) : Prop :=
  LinearIndependent LL b ∧ Submodule.span LL (Set.range b) = A.Wgood J0 lam0 eC

def MjLatticeIn {d : ℕ} (b : Fin d → WL) : Prop :=
  IsCoord A J0 lam0 eC b ∧ Submodule.IsLattice LL (A.Mcoord J0 lam0 eC b)

def MjLattice : Prop :=
  (∃ (d : ℕ) (b : Fin d → WL), IsCoord A J0 lam0 eC b) ∧
    ∀ (d : ℕ) (b : Fin d → WL), IsCoord A J0 lam0 eC b → MjLatticeIn A J0 lam0 eC b

variable {A J0 lam0 eC}

end Clause

section Level

open Formalism.BasicNotions Formalism.L2.DIV

variable (D : D7) {LL : Type} [Field LL]

abbrev TypePl : Type := Σ k : Fin 2, D.nd.PlG k

instance finiteLevelGroupFintype : Fintype (G0g D.nd) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  Fintype.ofFinite _

def unipG : Subgroup (G0g D.nd) :=
  Subgroup.pi Set.univ fun v : TypePl D => unip (ZMod (D.host.g v.1)) D.R.r

def unipAt (v : TypePl D) : unipG D →* unip (ZMod (D.host.g v.1)) D.R.r :=
  ((Pi.evalMonoidHom (fun v : TypePl D => GL (Fin D.R.r) (ZMod (D.host.g v.1))) v).comp
    (unipG D).subtype).codRestrict _ fun x => x.2 v (Set.mem_univ _)

def unipotentCharacterOfAddChars (ψ : ∀ v : TypePl D, AddChar (ZMod (D.host.g v.1)) LL) : unipG D →* LLˣ :=
  (∏ v : TypePl D, (addCharHom (ψ v) (supHom (ZMod (D.host.g v.1)) D.R.r)).comp (unipAt D v))⁻¹

def chiDetG (χ : ∀ v : TypePl D, (ZMod (D.host.g v.1))ˣ →* LLˣ) : G0g D.nd →* LLˣ :=
  ∏ v : TypePl D, ((χ v).comp Matrix.GeneralLinearGroup.det).comp
    (Pi.evalMonoidHom (fun v : TypePl D => GL (Fin D.R.r) (ZMod (D.host.g v.1))) v)

end Level

section Rec

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.MainNotions.DIV.Cons

variable {D : D7}

def IsFormsOf (T : Core D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
    [Module (𝓞 T.Q.c.F) WL] [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] (A : FormsL LL T.Q.c.F WL W G0) (ι : T.cuspA j a n →ₗ[T.Q.c.F] WL) : Prop :=
  IsBaseChange LL ι ∧ A.WK = LinearMap.range ι ∧
    ∀ f : T.cuspA j a n, ι f ∈ A.MK ↔ ∀ la (y : T.PtM j la), T.nrmM j la y (f : T.R j) ≤ 1

def MjLatticeRec (D : D7) : Prop :=
  ∀ (T : CoreJ D), LawsJ T → ∀ (hK : DV.KapDef D) (hn : Even D.R.nV) (j : ℕ), InR D j →
  ∀ (LL : Type) [Field LL] [NumberField LL] [Algebra T.Q.c.F LL] (σ₀ : LL →+* ℂ), BaseEmbeddingInclusion T.Q.c.F σ₀ →
  ∀ (WL : Type) [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 T.Q.c.F) WL] [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
    (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    (A : FormsL LL T.Q.c.F WL W (G0g D.nd))
    (ι : T.cuspA j (wtA (kaWt D hK hn j)) (kaWt D hK hn j).n →ₗ[T.Q.c.F] WL),
    IsFormsOf T.toCore j (wtA (kaWt D hK hn j)) (kaWt D hK hn j).n A ι →
  ∀ (χ : ∀ v : TypePl D, (ZMod (D.host.g v.1))ˣ →* LLˣ), A.chi = chiDetG D χ →
  ∀ (ψ : ∀ v : TypePl D, AddChar (ZMod (D.host.g v.1)) LL), (∀ v, ψ v ≠ 1) →
  ∀ (eC : G0g D.nd → LL), (∀ g, σ₀ (eC g) = D.ntypes.e0.coeff g) →
    MjLattice A (unipG D) (unipotentCharacterOfAddChars D ψ) eC

end Rec

end GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership
