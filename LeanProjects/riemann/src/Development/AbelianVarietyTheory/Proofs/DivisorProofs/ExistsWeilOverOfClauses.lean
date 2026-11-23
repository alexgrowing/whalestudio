import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyGridDataIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver

noncomputable section

section WeilOver

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.WeilOver

open GlobalTheory.LatVac GlobalTheory.PlaceDatum GlobalTheory.PlaceModel Formalism.IndefR.Mult

variable {D : D7}

theorem exists_weil_over_of_clauses (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) {Γ : Type} [Group Γ] [Fintype Γ]
    {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hlev : R.toLevCh.Is A.μ0) (hch : R.IsChain) (hmod : R.IsModels)
    (sc : Consts) (G : GridData R.toLevCh sc) : ∃ W : G.Weil, W.Over R := by
  have hψ := (hch.ωX A.μ0).std
  obtain ⟨W, hWψ⟩ := GlobalTheory.T.exists_weilRepresentation_vacuum_cosetVectors_grid hW D T R.toLevCh A.μ0 hlev sc G R.ψ hψ
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have lt : ∀ j, j < D.R.m → G.V (.grid 0 j) = Yc D j := fun j h => congrArg LSp.sp (colY_lt R.toLevCh h)
  have top : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m R.toLevCh)
  have h1 : ∀ X : Node, ∃ s B, (X.InRange D.R.m → IsMaj (G.V X) s B) ∧
      (∀ j, j < D.R.m → X = .grid 0 j → HEq s (cart (R.MY j)) ∧ HEq B (onb (R.MY j))) ∧
      (X = .grid 0 D.R.m → HEq s (cart R.MX) ∧ HEq B (onb R.MX)) := fun X => by
    by_cases h : ∃ j, j < D.R.m ∧ X = .grid 0 j
    · obtain ⟨j, hj, rfl⟩ := h
      obtain ⟨s, B, a, b⟩ := exists_maj_heq (lt j hj) (R.MY j)
      refine ⟨s, B, fun _ => a, fun k _ hk => ?_, fun hk => ?_⟩
      · cases hk; exact b
      · exact absurd (Node.grid.inj hk).2 hj.ne
    by_cases h' : X = .grid 0 D.R.m
    · subst h'
      obtain ⟨s, B, a, b⟩ := exists_maj_heq top R.MX
      exact ⟨s, B, fun _ => a, fun k hk e => absurd ⟨k, hk, e⟩ h, fun _ => b⟩
    exact ⟨W.cart X, W.onb X, fun hX τ => ⟨W.cart_is X hX τ, W.onb_is X hX τ⟩, fun k hk e => absurd ⟨k, hk, e⟩ h,
      fun e => absurd e h'⟩
  have h2 : ∀ p : Pair T, ∃ ω, (p.InRange D.R.m → IsWeilDatumO R.ψ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) ω) ∧
      (∀ t k, k + 1 < D.R.m → p = .mu t 0 k → HEq ω (R.ωY t k)) ∧
      (∀ t k, k + 1 = D.R.m → p = .mu t 0 k → HEq ω (R.ωX t)) := fun p => by
    by_cases h : ∃ t k, k + 1 < D.R.m ∧ p = .mu t 0 k
    · obtain ⟨t, k, hk, rfl⟩ := h
      have := hch.ωY t k hk
      rw [← G.chr_mu_zero t hk.le] at this
      obtain ⟨ω, a, b⟩ := exists_om_heq (lt k (by omega)) (lt (k + 1) hk) this
      refine ⟨ω, fun _ => a, fun t' k' _ e => ?_, fun t' k' hk' e => ?_⟩
      · cases e; exact b
      · cases e; omega
    by_cases h' : ∃ t k, k + 1 = D.R.m ∧ p = .mu t 0 k
    · obtain ⟨t, k, hk, rfl⟩ := h'
      have e0 := G.chr_mu_zero t hk.le
      rw [hk] at e0
      have := hch.ωX t
      rw [← e0] at this
      obtain ⟨ω, a, b⟩ := exists_om_heq (S' := G.V (.grid 0 k)) (T' := G.V (.grid 0 (k + 1)))
        ((lt k (by omega)).trans (congrArg (Yc D) (by omega))) (hk ▸ top) this
      refine ⟨ω, fun _ => a, fun t' k' hk' e => ?_, fun t' k' _ e => ?_⟩
      · cases e; omega
      · cases e; exact b
    exact ⟨W.om p, fun hp => hWψ ▸ W.om_is p hp, fun t k hk e => absurd ⟨t, k, hk, e⟩ h,
      fun t k hk e => absurd ⟨t, k, hk, e⟩ h'⟩
  choose s B hs sY sX using h1
  choose om hom oY oX using h2
  obtain ⟨W', a1, a2, a3, a4, a5⟩ := exists_weil G (fun i hi => by
    have : (G.node (.grid i 0)).IsV (rankV D i 0) ((D.R.m - 0) / 2) := by
      cases i with
      | zero => exact GlobalTheory.T.gridFirstColumnSpace_rank_signature_selfDual D T R.toLevCh A.μ0 hlev 0 hi
      | succ i => exact G.sp.V_is (i + 1) 0 (by omega) hi (Nat.zero_le _)
    exact ⟨this.sigOK, this.sd⟩) he hψ hmod.inf s B hs om hom
  exact ⟨W', a1, a2, fun j hj => a3 ▸ (sY _ j hj rfl).1, a3 ▸ (sX _ rfl).1, fun j hj => a4 ▸ (sY _ j hj rfl).2,
    a4 ▸ (sX _ rfl).2, fun t k hk => a5 ▸ oY _ t k hk rfl, fun t k hk => a5 ▸ oX _ t k hk rfl⟩

end GlobalTheory.ChiGrid.WeilOver

end WeilOver

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

end GlobalTheory.BigTop.Fun

end
