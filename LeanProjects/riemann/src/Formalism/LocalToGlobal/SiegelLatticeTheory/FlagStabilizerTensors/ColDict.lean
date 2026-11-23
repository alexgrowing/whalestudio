import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero

noncomputable section

open scoped Classical InnerProductSpace TensorProduct
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.ColDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Frames

variable {D : D7}

def xFr (D : D7) (j : Fin (D.R.N 0)) : (VS D).V :=
  D.sp.iXY 0 ((D.sp.X 0).frame (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)).symm j))

variable (X : HidaSetting D)

def qFr (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (j : Fin (D.R.N 0)) : (VS D).V := wt.symm (xFr D j)

def rvV (v : InfinitePlace X.B.I.F) (x : (VS D).V) : Fin X.B.I.n → ℂ := rv X.B.I v (X.crd x)

def qA (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (j : Fin (D.R.N 0)) : VA X.B.I := incl X.B.I (X.crd (qFr wt j))

def RepF (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (h : X.B.I.Gf)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  ∀ j, X.B.I.fmat h *ᵥ qA X wt j =
    ∑ i, ιA.symm (y.1.1 i j) •
      qA X wt i

def gramQ (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  Matrix.of fun a b => hJ (X.B.I.ε v) (rvV X v (qFr wt a)) (rvV X v (qFr wt b))

def sTil (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s : X.B.I.Ginf) (τ : D.what₂.Tau) :
    Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  (gramQ X wt (X.pl.symm τ))⁻¹ * Matrix.of fun a b =>
    hJ (X.B.I.ε (X.pl.symm τ)) (rvV X (X.pl.symm τ) (qFr wt a))
      (uMat (s (X.pl.symm τ)) *ᵥ rvV X (X.pl.symm τ) (qFr wt b))

end Frames

section Transport

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

structure Transport (F : Formalism.L2.Forms.Forms0 D u) where

  wt : (VS D).V ≃ₗ[D.host.E] (VS D).V
  wt_isom : ∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y
  wt_e : ∀ a, wt (X.eX a) = D.sp.hypE a
  wt_f : ∀ a, wt (X.fY a) = D.sp.hypF a
  weight_z : wt (X.zu u) = D.zmOf u

  ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F
  ιA_rat : ∀ x : X.B.I.E, ιA (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x) =
    Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (X.ιE x)
  ιA_int : ∀ a, a ∈ IntAf X.B.I.F X.B.I.E ↔ ιA a ∈ IntAf D.host.F D.host.E

  h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
    (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

  hc : (D.mem u).C.cls 0 → Hfin X u
  hc_rep : ∀ c, RepF X wt ιA (hc c : X.B.I.Gf) (F.cls0.y c * h0⁻¹)

  J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ)

  J_eqv : ∀ s ∈ Hinf X u, ∀ (ξ : X.Vpi u) (y y' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)),
    Formalism.L2.Forms.IsTr (sTil X wt s) y' y → J (X.piU u s ξ) y = J ξ y'

  J_val : ∀ ξ, J ξ ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
    (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0)

  J_isom : ∀ (c : (D.mem u).C.cls 0) (ξ η : X.Vpi u),
    (D.fm u).ipV 0 c (fun z => J ξ (F.val0.eY z))
      (fun z => J η (F.val0.eY z)) = ⟪η, ξ⟫_ℂ

end Transport

section Dict

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def shP (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (h : Hfin X u) : X.Vpi u :=
  (InnerProductSpace.toDual ℂ (X.Vpi u)).symm
    (LinearMap.toContinuousLinearMap ((LinearMap.proj ((1 : Hinf X u), h)).comp T))

theorem rieszVector_add (T T' : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (h : Hfin X u) :
    shP X u (T + T') h = shP X u T h + shP X u T' h := by
  simp only [shP, LinearMap.comp_add, map_add]

theorem rieszVector_smul (c : ℂ) (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (h : Hfin X u) :
    shP X u (c • T) h = (starRingEnd ℂ c) • shP X u T h := by
  simp only [shP, LinearMap.comp_smul, map_smul, map_smulₛₗ]

theorem inner_shP (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (h : Hfin X u) (ξ : X.Vpi u) :
    ⟪shP X u T h, ξ⟫_ℂ = T ξ (1, h) := by
  simp [shP, InnerProductSpace.toDual_symm_apply]

variable {u} {F : Formalism.L2.Forms.Forms0 D u}

def dictA (Tr : Transport X u F) :
    (X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) →ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) where
  toFun T := fun c z => Tr.J (shP X u T (Tr.hc c)) (F.val0.eY z)
  map_add' T T' := by
    funext c z
    simp [rieszVector_add]
  map_smul' a T := by
    funext c z
    simp [rieszVector_smul]

def colDictL (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter) :
    Cu X u hK →ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :=
  (dictA X Tr).comp (Cu X u hK).subtype

def rtr (δ : Hfin X u) :
    (X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) →ₗ[ℂ] (X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) where
  toFun T :=
    { toFun := fun ξ y => T ξ (y * (1, δ))
      map_add' := fun ξ ξ' => by funext y; simp
      map_smul' := fun a ξ => by funext y; simp }
  map_add' T T' := by ext ξ y; simp
  map_smul' a T := by ext ξ y; simp

end Dict

section Stmts

variable {D : D7} (X : HidaSetting D) {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
  (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter)

def LevelMatch : Prop :=
  (∀ x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F,
    (Tr.h0⁻¹).1.1 *ᵥ x ∈
      Formalism.UG.latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
        (Formalism.UG.tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Formalism.UG.intOE D.host.E)
          (Formalism.UG.intAd D.host.F)) F.cls0.lev.Lb ↔
    (∑ j, Tr.ιA.symm (x j) • qA X Tr.wt j) ∈ X.B.I.Lf) ∧
  ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), RepF X Tr.wt Tr.ιA (h : X.B.I.Gf) y →
    (h ∈ Ku X u hK ↔ ((Tr.h0⁻¹ * y * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
      F.cls0.lev.U) ∧
    ∀ (hk : h ∈ Ku X u hK) (hy : ((Tr.h0⁻¹ * y * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
        F.cls0.lev.U),
      ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = ((F.cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ)

def ClsMatch : Prop :=
  ∀ h : Hfin X u, ∃! c : (D.mem u).C.cls 0, ∃ (γ : Gam X u) (κ : Ku X u hK),
    h = iotaF X u γ * Tr.hc c * (κ : Hfin X u)

def ColDictInto : Prop := ∀ T : Cu X u hK, colDictL X Tr hK T ∈ (D.mem u).A.Mu0

def ColDictBij : Prop :=
  Function.Injective (colDictL X Tr hK) ∧ ∀ φ ∈ (D.mem u).A.Mu0, ∃ T, colDictL X Tr hK T = φ

def colDict (hI : ColDictInto X Tr hK) (hB : ColDictBij X Tr hK) : Cu X u hK ≃ₗ[ℂ] (D.mem u).A.Mu0 :=
  LinearEquiv.ofBijective ((colDictL X Tr hK).codRestrict (D.mem u).A.Mu0 hI)
    ⟨fun a b h => hB.1 (congrArg Subtype.val h), fun φ => by
      obtain ⟨T, hT⟩ := hB.2 φ.1 φ.2
      exact ⟨T, Subtype.ext hT⟩⟩

theorem colDict_apply (hI : ColDictInto X Tr hK) (hB : ColDictBij X Tr hK) (T : Cu X u hK) :
    (colDict X Tr hK hI hB T : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) = colDictL X Tr hK T := rfl

def colDictT {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {cs : ColSys X u what₂}
    (hinj : Function.Injective (sharp hK cs)) (hI : ColDictInto X Tr hK) (hB : ColDictBij X Tr hK) :
    Formalism.L2.SG.PackageTie2.ColT hinj ≃ₗ[ℂ] (D.mem u).A.Mu0 :=
  colDict X Tr hK hI hB

def toCu {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {cs : ColSys X u what₂}
    {hinj : Function.Injective (sharp hK cs)} (T : Formalism.L2.SG.PackageTie2.ColT hinj) : Cu X u hK := T

def ColDictIsom {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)
    (hinj : Function.Injective (sharp hK cs)) : Prop :=
  ∀ T T' : Formalism.L2.SG.PackageTie2.ColT hinj, inner ℂ T T' =
    (D.fm u).ipC 0 (colDictL X Tr hK (toCu X hK T)) (colDictL X Tr hK (toCu X hK T'))

def ColDictDia : Prop :=
  ∀ (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ), (k : (D.mem u).A.Fv v) = a →
    ∀ (δ : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), RepF X Tr.wt Tr.ιA (δ : X.B.I.Gf) (Tr.h0 * y * Tr.h0⁻¹) →
    Formalism.L2.Forms.IsDia F.cls0.lev (F.atT.eV v).1 (F.atT.eV v).2 k y →
    ∀ T ∈ Cu X u hK, dictA X Tr (rtr X δ T) = (D.mem u).A.rhoT v a (dictA X Tr T)

def ColDictWellDef : Prop :=
  ∀ Tr' : Transport X u F, LevelMatch X Tr hK → LevelMatch X Tr' hK →
    ∃ A : ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) ≃ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ),
      (D.mem u).A.Mu0.map (A : ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) →ₗ[ℂ] _) = (D.mem u).A.Mu0 ∧
      (∀ φ ∈ (D.mem u).A.Mu0, ∀ ψ ∈ (D.mem u).A.Mu0, (D.fm u).ipC 0 (A φ) (A ψ) = (D.fm u).ipC 0 φ ψ) ∧
      ∀ T : Cu X u hK, colDictL X Tr' hK T = A (colDictL X Tr hK T)

def ColumnDictionary : Prop :=
  LevelMatch X Tr hK → Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) →
    ClsMatch X Tr hK ∧ ColDictInto X Tr hK ∧ ColDictBij X Tr hK ∧ ColDictDia X Tr hK ∧
      ColDictWellDef X Tr hK ∧
      ∀ (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (cs : ColSys X u what₂)
        (hinj : Function.Injective (sharp hK cs)), ColReps hK cs → ColDictIsom X Tr hK cs hinj

end Stmts

def TransportExists (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∃ X : HidaSetting D, ∃ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    X.MeasTie hb ∧ Formalism.L2.SG.WuDecay.WuDecay X ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
    ∃ hK : X.LevelSubgroupCharacter, ∀ u, ∃ Tr : Transport X u (F u), LevelMatch X Tr hK

section Checks

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}

theorem Transport.J_injective (Tr : Transport X u F) (c : (D.mem u).C.cls 0) : Function.Injective Tr.J := by
  intro ξ η hJ
  refine ext_inner_left ℂ fun ζ => ?_
  rw [← Tr.J_isom c ξ ζ, ← Tr.J_isom c η ζ, hJ]

end Checks

end Formalism.L2.SG.ColDict
