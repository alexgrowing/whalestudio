import Formalism.SharpRestriction.InertJacobiLevels.ExtraKer
import Formalism.SharpRestriction.InertJacobiLevels.ResCharConj
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.DataNChTie
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsHomOfBasis

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

structure PlEmb (D : D7) where
  lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]
  iL : ∀ w : D.what₂.places.Pl, D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]
  iL_spec : ∀ w x, ∃ hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ, iL w x = lam w ⟨D.what₂.embLL x, hx⟩
  iL_int : ∀ w x, x ∈ intW D.what₂.places w ↔ ‖iL w x‖ ≤ 1

def plEmb (D : D7) : PlEmb D where
  lam := fun w => (Examples₂.exists_placeEmb D w).choose
  iL := fun w => (Examples₂.exists_placeEmb D w).choose_spec.choose
  iL_spec := fun w => (Examples₂.exists_placeEmb D w).choose_spec.choose_spec.1
  iL_int := fun w => (Examples₂.exists_placeEmb D w).choose_spec.choose_spec.2

def entZero (D : D7) (Dx : DivX D) (Tw : TwForms D) (PE : PlEmb D) [∀ u μ i, IsEmpty ((D.chTw u μ).Y i)]
    [∀ u μ j, IsEmpty ((D.chTw u μ).cls (j + 1))] : KerEnt D Dx Tw where
  lam := PE.lam
  iL := PE.iL
  iL_lam := fun w x => by
    obtain ⟨hx, h⟩ := PE.iL_spec w x
    unfold lamV
    rw [dif_pos hx, h]
  iL_int := PE.iL_int
  Th := fun _ _ _ _ _ _ => 0
  VQ := fun _ _ _ _ => PUnit
  ev := fun _ _ _ _ => 0
  ev_inj := fun _ _ _ _ _ _ _ => rfl
  prS := fun _ _ _ _ _ => 0
  prT := fun _ _ _ _ _ => 0
  prT_val := fun _ _ _ _ _ _ c' => isEmptyElim c'
  lat_S := fun u μ w _ i _ φ =>
    ⟨fun _ => ⟨by
        rw [show φ = 0 from funext fun _ => funext fun y => isEmptyElim y]
        exact Submodule.zero_mem _, fun c => ⟨0, funext fun y => isEmptyElim y, fun _ => by simp⟩⟩,
      fun _ => ⟨0, Submodule.zero_mem _, funext fun _ => funext fun y => isEmptyElim y⟩⟩
  levelFree_lattice_condition := fun u μ w _ i _ φ =>
    ⟨fun _ => ⟨by
        rw [show φ = 0 from funext fun _ => funext fun y => isEmptyElim y]
        exact Submodule.zero_mem _, fun c' => isEmptyElim c'⟩,
      fun _ => ⟨0, Submodule.zero_mem _, funext fun _ => funext fun y => isEmptyElim y⟩⟩
  un := fun _ _ _ _ _ _ => 1
  un_ne := fun _ _ _ _ _ _ => one_ne_zero
  kform := fun _ _ _ _ _ _ _ c' => isEmptyElim c'

theorem entZero_lam (D : D7) (Dx : DivX D) (Tw : TwForms D) (PE : PlEmb D) [∀ u μ i, IsEmpty ((D.chTw u μ).Y i)]
    [∀ u μ j, IsEmpty ((D.chTw u μ).cls (j + 1))] (w) : (entZero D Dx Tw PE).lam w = PE.lam w := rfl

section Ker

variable (D : D7) (Gt : GatTies D) [∀ u j, Subsingleton ((D.fm u).lat j).V]
  (hM : ∀ u w h, (D.gat u w h).M = ⊥)
  (S : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), ServedEmb D u w h)
  (Tw : TwForms D) [∀ u μ j, Subsingleton ((Tw.fm u μ).lat j).V] (PE : PlEmb D)
  (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)

def kerZeroE [∀ j, IsEmpty ((D.chTw u (D.what₂.muAt w)).cls (j + 1))]
    [∀ j, IsEmpty (Lv.compS j)] (ht : Fl.t = D.R.t) (hm : Fl.mm = D.R.m)
    (e : (D.gat u w h).comp ≃ (D.chTw u (D.what₂.muAt w)).cls 0)
    (htr : ∀ (c : (D.gat u w h).comp) (L L' : (D.gat u w h).P.Tup), (D.gat u w h).P.IsLatTup L →
      (D.gat u w h).P.IsLatTup L' → ∃ γ : ((D.gat u w h).lev c).Γ, L' = ((D.gat u w h).lev c).smul γ L)
    (hex : ∃ L : (D.gat u w h).P.Tup, (D.gat u w h).P.IsLatTup L) :
    LocalToGlobal₂ D Gt (latCmpZero D hM S) Tw u w h Ch :=
  { kerZero D Gt hM S Tw u w h Ch ht hm e htr hex with
    lam := PE.lam w
    iK := (Examples₂.exists_iK (S u w h).iLL (S u w h).iK (PE.iL w)).choose
    iLL_lam := fun x hx => by
      obtain ⟨_, h2⟩ := PE.iL_spec w x
      exact ((Examples₂.exists_iK (S u w h).iLL (S u w h).iK (PE.iL w)).choose_spec x).trans h2 }

end Ker

def thDataZero (D : D7) : ThData D where
  xd0 := fun _ _ _ => ∅
  thetaBase_invariant_action := fun _ _ _ _ h => absurd h (Set.notMem_empty _)

theorem embAt_frac (D : D7) (hLL0 : ∀ x : D.what₂.LL, x ∈ D.LL0) (i : D.ntw.Tw) (x : D.LL0) (y z : D.ntw.O0 i)
    (h : D.ntw.emb0 i x * algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) z =
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y) :
    embAt D hLL0 i (x : D.what₂.LL) * algebraMap (D.ntw.Ok i 1) (FractionRing (D.ntw.Ok i 1))
        (algebraMap (D.ntw.O i) (D.ntw.Ok i 1) (algebraMap (D.ntw.O0 i) (D.ntw.O i) z)) =
      algebraMap (D.ntw.Ok i 1) (FractionRing (D.ntw.Ok i 1))
        (algebraMap (D.ntw.O i) (D.ntw.Ok i 1) (algebraMap (D.ntw.O0 i) (D.ntw.O i) y)) := by
  have h2 := congrArg (iotaOk D i 1) h
  rw [map_mul, iotaOk_alg, iotaOk_alg] at h2
  exact h2

theorem embAtB_frac (D : D7) (hLL0 : ∀ x : D.what₂.LL, x ∈ D.LL0) (i : D.ntw.Tw) (x : D.LL0) (y z : D.ntw.O0 i)
    (h : D.ntw.emb0b i x * algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) z =
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y) :
    embAtB D hLL0 i (x : D.what₂.LL) * algebraMap (D.ntw.Ok i 1) (FractionRing (D.ntw.Ok i 1))
        (algebraMap (D.ntw.O i) (D.ntw.Ok i 1) (algebraMap (D.ntw.O0 i) (D.ntw.O i) z)) =
      algebraMap (D.ntw.Ok i 1) (FractionRing (D.ntw.Ok i 1))
        (algebraMap (D.ntw.O i) (D.ntw.Ok i 1) (algebraMap (D.ntw.O0 i) (D.ntw.O i) y)) := by
  have h2 := congrArg (iotaOk D i 1) h
  rw [map_mul, iotaOk_alg, iotaOk_alg] at h2
  exact h2

open Classical in
theorem nchEmbOf_frac (D : D7) (hLL0 : ∀ x : D.what₂.LL, x ∈ D.LL0) (hc : NTw.TwCover D.ntw) (w : D.what₂.places.Pl)
    (x : D.LL0) (y z : D.ntw.O0 ((nchEmbOf D hLL0 hc).twI w))
    (h : (if (nchEmbOf D hLL0 hc).sd w = true then D.ntw.emb0 ((nchEmbOf D hLL0 hc).twI w)
        else D.ntw.emb0b ((nchEmbOf D hLL0 hc).twI w)) x *
        algebraMap (D.ntw.O0 ((nchEmbOf D hLL0 hc).twI w)) (FractionRing (D.ntw.O0 ((nchEmbOf D hLL0 hc).twI w))) z =
      algebraMap (D.ntw.O0 ((nchEmbOf D hLL0 hc).twI w)) (FractionRing (D.ntw.O0 ((nchEmbOf D hLL0 hc).twI w))) y) :
    (nchEmbOf D hLL0 hc).embW w (x : D.what₂.LL) *
        algebraMap (D.ntw.Ok ((nchEmbOf D hLL0 hc).twI w) 1) (FractionRing (D.ntw.Ok ((nchEmbOf D hLL0 hc).twI w) 1))
          (algebraMap (D.ntw.O ((nchEmbOf D hLL0 hc).twI w)) (D.ntw.Ok ((nchEmbOf D hLL0 hc).twI w) 1)
            (algebraMap (D.ntw.O0 ((nchEmbOf D hLL0 hc).twI w)) (D.ntw.O ((nchEmbOf D hLL0 hc).twI w)) z)) =
      algebraMap (D.ntw.Ok ((nchEmbOf D hLL0 hc).twI w) 1) (FractionRing (D.ntw.Ok ((nchEmbOf D hLL0 hc).twI w) 1))
        (algebraMap (D.ntw.O ((nchEmbOf D hLL0 hc).twI w)) (D.ntw.Ok ((nchEmbOf D hLL0 hc).twI w) 1)
          (algebraMap (D.ntw.O0 ((nchEmbOf D hLL0 hc).twI w)) (D.ntw.O ((nchEmbOf D hLL0 hc).twI w)) y)) := by
  by_cases hr : repW D w = w
  · have hs : (nchEmbOf D hLL0 hc).sd w = true := decide_eq_true hr
    have he : (nchEmbOf D hLL0 hc).embW w = embAt D hLL0 ((nchEmbOf D hLL0 hc).twI w) := if_pos hr
    rw [if_pos hs] at h
    rw [he]
    exact embAt_frac D hLL0 _ x y z h
  · have hs : ¬ (nchEmbOf D hLL0 hc).sd w = true := by
      have : (nchEmbOf D hLL0 hc).sd w = false := decide_eq_false hr
      rw [this]; exact Bool.false_ne_true
    have he : (nchEmbOf D hLL0 hc).embW w = embAtB D hLL0 ((nchEmbOf D hLL0 hc).twI w) := if_neg hr
    rw [if_neg hs] at h
    rw [he]
    exact embAtB_frac D hLL0 _ x y z h

set_option synthInstance.maxHeartbeats 400000 in

theorem nchTie_zero (D : D7) [∀ μ j, Subsingleton (D.what₂.MtL μ j)]
    [∀ i j b k Q ψ, Subsingleton (D.nexp.MtV i j b k Q ψ)] [IsEmpty D.nd.Loc]
    (hLL0 : ∀ x : D.what₂.LL, x ∈ D.LL0) (hc : NTw.TwCover D.ntw) :
    NChTie D (nchZero D (nchEmbOf D hLL0 hc)) where
  twOf_eq := fun a => isEmptyElim a
  twSide_eq := fun a => isEmptyElim a
  Q_eq := fun a => isEmptyElim a
  psi_eq := ⟨fun _ => 1, fun _ => rfl, fun w _ =>
    (map_one ((nchEmbOf D hLL0 hc).embW w)).trans
      (map_one (algebraMap (D.ntw.Ok ((nchEmbOf D hLL0 hc).twI w) 1)
        (FractionRing (D.ntw.Ok ((nchEmbOf D hLL0 hc).twI w) 1)))).symm, fun a => isEmptyElim a⟩
  embedding_baseField_condition := fun w x y z _ h => nchEmbOf_frac D hLL0 hc w x y z h

end Formalism.MainNotions.Inhab

end
