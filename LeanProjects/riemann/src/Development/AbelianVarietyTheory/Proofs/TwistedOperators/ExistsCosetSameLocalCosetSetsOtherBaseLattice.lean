import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomApproxIntegralMatrixMod

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section

open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.CosFlip

open Matrix GlobalTheory.FunObj.Comparison₂ GlobalTheory.SplitFlip GlobalTheory.StdFrames ValuativeRel Formalism.L2.DIV

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem v_le_cosExp (G : GridData L sc) {s : OA D} (hs : s ∈ idS D.host.F G.modul) (w : Pl D.host.E) :
    Valued.v (cpt (D := D) w s.1) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  by_cases hw : w ∈ G.pl.W0
  · exact (mem_idS_modul G s).1 hs w hw
  · rw [(depthAt_of_notMem G hw).1, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact (mem_OA_iff _).1 s.2 w

theorem coord_sub_mem (G : GridData L sc) (B : Frames G) (t : T) (w : Pl D.host.E) (h : 0 < D.R.m)
    (h0 : IsFrame (B.β 0 0) (G.Λ (.grid 0 0))) (h1 : IsFrame (B.β 1 0) (G.Λ (.grid 1 0)))
    {y y₀ : homLat (G.Λ (.grid 1 0)) (G.Λ (.grid 0 0))} (hy : Cos.mk G.modul y = Cos.mk G.modul y₀) :
    B.coord t w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩ ⟨h, Nat.zero_le _⟩
        (y.1.map (algebraMap D.host.E (Kw w))) -
      B.coord t w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩ ⟨h, Nat.zero_le _⟩
        (y₀.1.map (algebraMap D.host.E (Kw w))) ∈ matLat (Fin ((locGrid G t w).rank (1, 0))) (unifAt w ^ cosExp G w • SplitFlip.stdLat (Kw w) (Fin ((locGrid G t w).rank (0, 0)))) := by
  rw [mem_matLat_pow, map_algebraMap, map_algebraMap, coord_map, coord_map]
  intro a b
  obtain ⟨s, hs, e⟩ := fr_mem_idS h1 h0 (sub_mem_of_mk_eq hy)
    (Fin.cast (rank_vertex G t w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
    (Fin.cast (rank_vertex G t w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a)
  simp only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rw [← RingHom.map_sub, ← Matrix.sub_apply, ← fr_sub, ← Matrix.map_sub _ (map_sub (eToEAf D)), ← e]
  exact v_le_cosExp G hs w

theorem cosetSet_mk (G : GridData L sc) (B : Frames G) (t : T) (w : Pl D.host.E) (h : 0 < D.R.m)
    (h0 : IsFrame (B.β 0 0) (G.Λ (.grid 0 0))) (h1 : IsFrame (B.β 1 0) (G.Λ (.grid 1 0)))
    (y₀ : homLat (G.Λ (.grid 1 0)) (G.Λ (.grid 0 0))) :
    cosetSet t w B h (Cos.mk G.modul y₀) = {x | x - B.coord t w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩
      ⟨h, Nat.zero_le _⟩ (y₀.1.map (algebraMap D.host.E (Kw w))) ∈
        matLat (Fin ((locGrid G t w).rank (1, 0))) (unifAt w ^ cosExp G w • SplitFlip.stdLat (Kw w) (Fin ((locGrid G t w).rank (0, 0))))} := by
  ext x
  constructor
  · rintro ⟨y, hy, hx⟩
    have := add_mem hx (coord_sub_mem G B t w h h0 h1 hy)
    rwa [sub_add_sub_cancel] at this
  · intro hx
    exact ⟨y₀, rfl, hx⟩

end GlobalTheory.FunObj.CosFlip

namespace GlobalTheory.FunObj.CosFlip

open Matrix GlobalTheory.FunObj.Comparison₂ GlobalTheory.SplitFlip GlobalTheory.StdFrames ValuativeRel Formalism.L2.DIV

theorem sub_mem_iff_of_sub_mem {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (S : Submodule R M) {a b : M}
    (h : a - b ∈ S) (x : M) : x - a ∈ S ↔ x - b ∈ S := by
  constructor
  · intro hx
    have := add_mem hx h
    rwa [sub_add_sub_cancel] at this
  · intro hx
    have := sub_mem hx h
    rwa [sub_sub_sub_cancel_right] at this

theorem exists_cos_cosetSet_eq : ∀ {D : D7} {T T' : Type} {L : LevCh D T} {L' : LevCh D T'} {sc : Consts} (G : GridData L sc) (G' : GridData L' sc)
    (B : GlobalTheory.FunObj.Frames G) (B' : GlobalTheory.FunObj.Frames G'),
    IsSDFrame (Yc D 0) (L.βY 0) (L.ΛY 0) (D.host.g 0 * D.host.g 1) →
    IsSDFrame (Yc D 0) (L'.βY 0) (L'.ΛY 0) (D.host.g 0 * D.host.g 1) →
    G'.pl.v0 = G.pl.v0 → G'.pl.w = G.pl.w → G'.sp.Vs 1 0 = G.sp.Vs 1 0 → HEq (B'.βs 1 0) (B.βs 1 0) →
    ∀ (h : 0 < D.R.m) (κ' : G'.CosAt 0), ∃ κ : G.CosAt 0, ∀ (t : T') (t₀ : T) (w : Pl D.host.E),
      GlobalTheory.FunObj.cosetSet t w B' h κ' = GlobalTheory.FunObj.cosetSet t₀ w B h κ := by
  intro D T T' L L' sc G G' B B' hY hY' hv0 hw _ _ h κ'
  have h0 : IsFrame (B.β 0 0) (G.Λ (.grid 0 0)) := hY.choose_spec.1
  have h0' : IsFrame (B'.β 0 0) (G'.Λ (.grid 0 0)) := hY'.choose_spec.1
  have h1 : IsFrame (B.β 1 0) (G.Λ (.grid 1 0)) := B.isFrame 1 0 le_rfl h (Nat.zero_le _)
  have h1' : IsFrame (B'.β 1 0) (G'.Λ (.grid 1 0)) := B'.isFrame 1 0 le_rfl h (Nat.zero_le _)
  have hW0 : G'.pl.W0 = G.pl.W0 := by
    unfold Places.W0 Places.S0
    rw [hv0, hw]
  have hdep : ∀ v, G'.pl.depth sc v = G.pl.depth sc v := fun v => by
    unfold Places.depth
    rw [hv0]
  have hexp : ∀ w, cosExp G' w = cosExp G w := fun w => by
    by_cases hm : w ∈ G.pl.W0
    · rw [cosExp, cosExp, if_pos (by rw [hW0]; exact hm), if_pos hm, hdep]
    · rw [cosExp, cosExp, if_neg (by rw [hW0]; exact hm), if_neg hm]
  obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective _ κ'
  have hint : ∀ i j, ∃ s ∈ idS D.host.F ⊤, s.1 = fr (B'.β 0 0) (B'.β 1 0) (y'.1.map (eToEAf D)) i j :=
    fr_mem_idS h1' h0' (by rw [Submodule.top_smul]; exact y'.2)
  choose N _ hN using hint
  have hr : (G.V (.grid 1 0)).rank = (G'.V (.grid 1 0)).rank := by
    show (G.sp.Vs 1 0).sp.rank = (G'.sp.Vs 1 0).sp.rank
    rw [‹G'.sp.Vs 1 0 = G.sp.Vs 1 0›]
  obtain ⟨x₀, hx₀, hs⟩ := HatFrame.homLat_approx_mod (G.Λ (.grid 1 0)) (G.Λ (.grid 0 0)) (B.β 1 0) (B.β 0 0) h1 h0
    G.modul (G.pl.modul_ne_bot sc) (fun i j => N i (Fin.cast hr j))
  refine ⟨Cos.mk G.modul ⟨x₀, hx₀⟩, fun t t₀ w => ?_⟩
  have hk : Cos.mk G'.modul y' = κ' := hy'
  rw [← hk, cosetSet_mk G' B' t w h h0' h1' y', cosetSet_mk G B t₀ w h h0 h1 ⟨x₀, hx₀⟩, hexp]
  have key : @id (Matrix (Fin ((locGrid G t₀ w).rank (1, 0))) (Fin ((locGrid G t₀ w).rank (0, 0))) (Kw w))
        (B'.coord t w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩ ⟨h, Nat.zero_le _⟩
          (y'.1.map (algebraMap D.host.E (Kw w)))) -
      B.coord t₀ w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩ ⟨h, Nat.zero_le _⟩
        (x₀.map (algebraMap D.host.E (Kw w))) ∈ matLat (Fin ((locGrid G t₀ w).rank (1, 0)))
        (unifAt w ^ cosExp G w • SplitFlip.stdLat (Kw w) (Fin ((locGrid G t₀ w).rank (0, 0)))) := by
    rw [mem_matLat_pow]
    dsimp only [id]
    rw [Comparison₂.map_algebraMap, Comparison₂.map_algebraMap, coord_map, coord_map]
    intro a b
    obtain ⟨s, hs1, hs2⟩ := hs (Fin.cast (rank_vertex G t₀ w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
      (Fin.cast (rank_vertex G t₀ w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a)
    have e1 : (N (Fin.cast (rank_vertex G t₀ w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
        (Fin.cast hr (Fin.cast (rank_vertex G t₀ w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a)) : EAf D) =
        fr (B'.β 0 0) (B'.β 1 0) (y'.1.map (eToEAf D))
          (Fin.cast (rank_vertex G' t w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G' t w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a) := hN _ _
    have e2 : fr (B'.β 0 0) (B'.β 1 0) (y'.1.map (eToEAf D))
          (Fin.cast (rank_vertex G' t w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G' t w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a) -
        fr (B.β 0 0) (B.β 1 0) (x₀.map (eToEAf D))
          (Fin.cast (rank_vertex G t₀ w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G t₀ w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a) = -(s : EAf D) := by
      rw [hs2, ← e1]
      exact (neg_sub _ _).symm
    show Valued.v (cpt (D := D) w (fr (B'.β 0 0) (B'.β 1 0) (y'.1.map (eToEAf D))
          (Fin.cast (rank_vertex G' t w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G' t w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a)) -
        cpt (D := D) w (fr (B.β 0 0) (B.β 1 0) (x₀.map (eToEAf D))
          (Fin.cast (rank_vertex G t₀ w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G t₀ w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a))) ≤ _
    rw [← RingHom.map_sub, e2, RingHom.map_neg, Valuation.map_neg]
    exact v_le_cosExp G hs1 w
  ext x
  exact sub_mem_iff_of_sub_mem _ key x

end GlobalTheory.FunObj.CosFlip
