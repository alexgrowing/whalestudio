import Formalism.LocalRingCardinality.DataExtra
import Formalism.SharpRestriction.InertJacobiLevels.ExtraZero
import Formalism.SharpRestriction.InertJacobiLevels.ExtraKer
import Formalism.SharpRestriction.InertJacobiLevels.ExtraNch

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped TensorProduct

theorem idxDefs_zero (D : D7) (X : DivX D) [∀ j, Subsingleton (X.MjH j).V] [∀ μ j, Subsingleton (D.what₂.MtL μ j)]
    (hI : ∀ μ j w, D.what₂.Ij μ j w = 0) (hj : ∀ μ j w, D.what₂.jw μ j w = 0) : IdxDefs D X where
  Ij_def := fun μ j w _ _ => by rw [hI, Idx.IjIdx_of_subsingleton]
  jw_def := fun μ j w _ _ => by rw [hj, Idx.jwIdx_of_subsingleton]

theorem lamDef_zero (D : D7) [∀ j, Subsingleton (D.what₂.Mj j)] : DV.LamDef D :=
  fun _ _ _ _ _ h => absurd (Subsingleton.elim _ _) h

theorem kapOf_zero {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {n : ℕ} (ty : Fin n → D.what₂.FT) (hn : n = 0) : S.kapOf ty = 1 := by
  subst hn
  unfold RowSide.kapOf
  split_ifs <;> simp

theorem kapSharp_zero (D : D7) (h : D.what₂.Drows = 0) : kapSharp D = 1 := kapOf_zero _ _ h

theorem kapRBase_zero {D : D7} (X : DivX D) (h : D.what₂.Drows = 0) (hk : X.kapR D.what₂.embLL = 1) : DV.KapRBase X :=
  hk.trans (kapSharp_zero D h).symm

theorem nuUnserved_zero {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) [∀ u, Subsingleton (D.div.Nu u).V] :
    NuUnserved X K := fun _ _ _ _ => ⟨locLe_of_subsingleton _ _ _ _, locLe_of_subsingleton _ _ _ _⟩

theorem dGamDef_of (D : D7) (h : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam) : DGamDef D :=
  fun u μ => ⟨fun u' μ' i hi c => by
    rw [h u μ, ← h u' μ']
    exact (D.chTw u' μ').dvd_DGam i hi c, h u μ⟩

theorem tensor_subsingleton (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    [Subsingleton M] : Subsingleton (A ⊗[R] M) :=
  ⟨fun x y => by
    have h : ∀ z : A ⊗[R] M, z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul a m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    rw [h x, h y]⟩

set_option synthInstance.maxHeartbeats 400000 in

def nmjZero (D : D7) (X : DivX D) (c : NChoice D) [∀ j, Subsingleton (X.MjH j).V]
    [∀ i j b, Subsingleton (D.nexp.Fm i j b)] : NMj D X c where
  eMj := fun _ _ => 0
  eMj_smul := fun _ _ _ _ _ _ => by simp
  eMj_li := fun _ j _ _ _ => by
    have := hlat_index_isEmpty (X.MjH j)
    exact linearIndependent_empty_type
  eMj_lat := fun w j _ _ _ => by
    have := tensor_subsingleton (D.ntw.O (c.twI w)) (c.Oe w) (D.nexp.Fm (c.twI w) j (c.sd w))
    refine ⟨?_, le_of_eq (Subsingleton.elim _ _), fun x _ => ⟨1, one_ne_zero, ?_⟩⟩
    · rw [Subsingleton.elim (Submodule.span _ _) ⊥]
      exact Submodule.fg_bot
    · rw [Subsingleton.elim ((1 : c.Oe w) • x) 0]
      exact Submodule.zero_mem _
  eMj_th := fun w j _ _ _ _ _ _ _ => by
    have := tensor_subsingleton (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) (D.nexp.Fm (c.twI w) j (c.sd w))
    exact Subsingleton.elim _ _

def ambZero (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) [∀ μ, Subsingleton (S.Amb μ)] : AmbForm D S where
  MtH := fun _ => Examples₂.zeroHLat D.what₂.LL
  jAmb := fun _ => 0
  MtH_good := fun _ _ => Examples₂.zeroHLat_good D.what₂.LL
  jAmb_basis := fun _ _ => ⟨by
    have : IsEmpty (Examples₂.zeroHLat D.what₂.LL).ι := inferInstanceAs (IsEmpty (Fin 0))
    exact linearIndependent_empty_type, Subsingleton.elim _ _⟩
  jAmb_lat := fun _ _ _ => ⟨fun _ => ⟨fun _ => 0, Subsingleton.elim _ _⟩, fun _ => Submodule.mem_top⟩
  jAmb_gen := fun _ _ v _ => ⟨0, Subsingleton.elim _ _⟩
  jAmb_norm := fun _ _ x => (Examples₂.normAt_empty (ι := Fin 0) _ _ _ _).trans (by simp)

instance trivialSide_ambient_subsingleton (D : D7) [Subsingleton D.what₂.EE0] (μ : D.what₂.Tup) : Subsingleton ((trivialSide D).s.Amb μ) :=
  inferInstanceAs (Subsingleton Examples₂.Z0)

end Formalism.MainNotions.Inhab

end
