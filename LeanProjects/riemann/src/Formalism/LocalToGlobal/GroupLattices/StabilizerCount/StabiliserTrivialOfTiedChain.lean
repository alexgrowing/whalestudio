import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite
import Formalism.LocalToGlobal.HermitianColumns.TiedQC

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.G.StabilizerCardinality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Stab0Used (D : D7) : Prop :=
  (∀ u c, Nat.card ((D.mem u).C.stab 0 c) = 1) ∧
    ∀ u μ, DV.Used D μ → ∀ c, Nat.card ((D.chTw u μ).stab 0 c) = 1

def TwStab0Tie (D : D7) : Prop :=
  ∀ u μ, DV.Used D μ → μ ≠ D.what₂.mu0 → ∃ e : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0,
    ∀ c, Nonempty ((D.mem u).C.stab 0 c ≃* (D.chTw u μ).stab 0 (e c))

theorem card_stab0_mem (D : D7) (lev : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    Nat.card ((D.mem u).C.stab 0 c) = 1 := by
  have := Formalism.L2.G.Triv.stabZero_rec D lev u c
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩

theorem card_stabiliser_reference_tuple (D : D7) (lev : LevelData D) (u : D.what₂.Word) :
    ∀ c : (D.chTw u D.what₂.mu0).cls 0, Nat.card ((D.chTw u D.what₂.mu0).stab 0 c) = 1 := by
  rw [D.memberColumns_twistedChain_base u]
  exact card_stab0_mem D lev u

theorem card_stab0_of_equiv (D : D7) (lev : LevelData D) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (e : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0) (s : ∀ c, Nonempty ((D.mem u).C.stab 0 c ≃* (D.chTw u μ).stab 0 (e c)))
    (c : (D.chTw u μ).cls 0) : Nat.card ((D.chTw u μ).stab 0 c) = 1 := by
  obtain ⟨c', rfl⟩ := e.surjective c
  obtain ⟨f⟩ := s c'
  rw [← Nat.card_congr f.toEquiv]
  exact card_stab0_mem D lev u c'

theorem stab0Used_of_tie (D : D7) (lev : LevelData D) (hT : TwStab0Tie D) : Stab0Used D := by
  refine ⟨card_stab0_mem D lev, fun u μ hU c => ?_⟩
  by_cases h0 : μ = D.what₂.mu0
  · subst h0
    exact card_stabiliser_reference_tuple D lev u c
  · obtain ⟨e, s⟩ := hT u μ hU h0
    exact card_stab0_of_equiv D lev u μ e s c

theorem twStab0Tie_of_tied (D : D7) {inQ : D.what₂.Tup → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F) → Prop}
    (T : Formalism.L2.Herm.TwChTied D inQ) : TwStab0Tie D :=
  fun u μ _ _ => ⟨T.eCls0 u μ, fun c => ⟨T.eStab0 u μ c⟩⟩

theorem stabiliser_trivial_of_tied_chain (D : D7) (lev : LevelData D)
    {inQ : D.what₂.Tup → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F) → Prop}
    (T : Formalism.L2.Herm.TwChTied D inQ) : Formalism.MainNotions.OrbitPlaces.Stab0 D :=
  ⟨card_stab0_mem D lev, fun u μ _ c => card_stab0_of_equiv D lev u μ (T.eCls0 u μ) (fun c => ⟨T.eStab0 u μ c⟩) c⟩

theorem stab0Used_iff (D : D7) : Stab0Used D ↔ Formalism.MainNotions.OrbitPlaces.Stab0 D := Iff.rfl

theorem stab0Used_of_stab0 (D : D7) (h : Formalism.MainNotions.OrbitPlaces.Stab0 D) : Stab0Used D := h

theorem stabiliser_trivial_of_tie (D : D7) (lev : LevelData D) (hT : TwStab0Tie D) : Formalism.MainNotions.OrbitPlaces.Stab0 D :=
  stab0Used_of_tie D lev hT

end Formalism.L2.G.StabilizerCardinality

end
