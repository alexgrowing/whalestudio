import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfStabN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

namespace StabFlagPf

open Matrix

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def toVHom : (Fin X.B.I.n → X.B.I.E) →+ (VS D).V where
  toFun := Formalism.L2.SG.Pf.Level.toV X
  map_zero' := by simp [Formalism.L2.SG.Pf.Level.toV]
  map_add' := Formalism.L2.SG.Pf.Level.toV_add X

theorem toV_span {T : Set (Fin X.B.I.n → X.B.I.E)} {w : Fin X.B.I.n → X.B.I.E}
    (hw : w ∈ Submodule.span X.B.I.E T) :
    Formalism.L2.SG.Pf.Level.toV X w ∈ Submodule.span D.host.E (Formalism.L2.SG.Pf.Level.toV X '' T) :=
  Formalism.L2.SG.Pf.Vanish2.tr_span X.ιE.toRingHom (toVHom X) (fun c x => Formalism.L2.SG.Pf.Level.toV_smul X c x) hw

theorem flag_e {u' : D.what₂.Word} {s : X.B.I.GA} {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hs : RatLink X s σ) (hS : s ∈ Srat X u') (a : Fin D.R.rS) :
    σ (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {b | b.1 < a.1}) := by
  obtain ⟨M, -, -, h2, h3⟩ := hs
  obtain ⟨-, hsf⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' _ hS
  obtain ⟨hfe, -⟩ := hsf
  have hf := hfe a
  have hG : ∀ y, X.B.I.fmat s.2 *ᵥ Formalism.L2.SG.Pf.Vanish2.inclHom X.B.I y =
      Formalism.L2.SG.Pf.Vanish2.inclHom X.B.I ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
    intro y
    rw [Formalism.L2.SG.Pf.Vanish2.inclHom_apply, Formalism.L2.SG.Pf.Vanish2.inclHom_apply, h2]
    exact Formalism.L2.SG.Pf.Level.incl_mulVec X _ y
  have e := Formalism.L2.SG.Pf.Vanish2.tr_sub (Formalism.L2.SG.Pf.Vanish2.inclHom X.B.I) _ _ hG (X.eR a)
  rw [Formalism.L2.SG.Pf.Vanish2.inclHom_apply, Formalism.L2.SG.Pf.Vanish2.inclHom_apply] at e
  rw [e] at hf
  have hd := Formalism.L2.SG.Pf.Level.descend X _ _ hf
  have hm : ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) - 1) *ᵥ X.eR a = X.crd (σ (X.eX a) - X.eX a) :=
    Formalism.L2.SG.Pf.Vanish2.mcrd X h3 (X.eX a)
  rw [hm] at hd
  have ht := toV_span X hd
  rw [Formalism.L2.SG.Pf.Level.toV_crd, Set.image_image] at ht
  have e2 : (fun b => Formalism.L2.SG.Pf.Level.toV X (X.eR b)) = X.eX :=
    funext fun b => Formalism.L2.SG.Pf.Level.toV_crd X (X.eX b)
  rwa [e2] at ht

end StabFlagPf

theorem flag_stabilizer_holds : StabFlagC := by
  intro D X Y u u' _ s σ hs _ hS j x hx
  have e : ∀ k, Xflag (lf D (X.Fu u')) k = Submodule.span D.host.E (X.eX '' {i | i.1 < k}) := by
    intro k
    show Submodule.span D.host.E ((X.Fu u').e '' {i | i.1 < k}) = _
    rw [X.Fu_e]
  rw [e] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    refine Submodule.span_mono ?_ (StabFlagPf.flag_e X hs hS a)
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, lt_of_lt_of_le hb (Nat.lt_succ_iff.1 ha), rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add, add_sub_add_comm]
    exact add_mem hy hz
  | smul c y _ hy =>
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ hy

end Formalism.L2.SG.Pf.RegroupPf
