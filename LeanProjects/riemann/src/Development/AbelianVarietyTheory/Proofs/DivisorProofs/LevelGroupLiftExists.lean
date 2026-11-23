import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevelStatement
import Formalism.LocalToGlobal.HermitianColumns.CoordinateLatticeSelfDual
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem isBaseFrame_of_isLatBasis {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (h : IsLatBasis V rfl β) :
    IsBaseFrame V β (GlobalTheory.Member.latC V) 1 := by
  refine ⟨fun x => ?_, Formalism.L2.Herm.coordinate_lattice_self_dual D.sp.cm V, Nat.one_pos, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := GlobalTheory.LiftLevel.swap_surj x
    refine Iff.trans ?_ (h z)
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1]
    exact (GlobalTheory.LevSplit.latHat_iff _ z).symm
  · rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq] at hx
    simpa using hx
  · rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
    simpa using hx

theorem not_isConjPl_of_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H)
    {w w' : Formalism.L2.DIV.Pl D.host.E} (hw : l.Mb ≤ w.asIdeal) (hw' : l.Mb ≤ w'.asIdeal) : ¬ IsConjPl w w' := by
  intro h
  apply w'.isPrime.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le hw' (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
  obtain ⟨c', hc', e⟩ := h a (hw ha)
  have : H.bar a = c' := by
    apply RingOfIntegers.coe_injective
    exact (H.bar_eq a).trans e.symm
  show H.bar a ∈ w'.asIdeal
  rw [this]; exact hc'

theorem finR_rfl {D : D7} (V : HSp D) (κ : GA D V) : finR V rfl κ = finE V κ := by
  apply Units.ext
  ext i j
  rfl

theorem exists_isLift : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsLatBasis V hr β → (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → ∀ g : Formalism.L2.DIV.G0 Pg r, ∃ κ, IsLift V hr β Pg g κ := by
  intro D H l V r hr β Pg hβ hPg g
  subst hr
  obtain ⟨κ, h1, h2, h3⟩ := GlobalTheory.T.finite_group_lifts_to_parahoric_level V β (datW V.rank Pg (Formalism.L2.DIV.LevelP.triv Pg V.rank ℂ) Frm.B)
    (GlobalTheory.Member.latC V) 1 (isBaseFrame_of_isLatBasis V β hβ) rfl
    (fun w hw w' hw' => not_isConjPl_of_le l ((hPg w).1 hw) ((hPg w').1 hw')) g
  have hs : finR V rfl κ ∈ Formalism.L2.DIV.St β := by
    rw [finR_rfl]; exact Formalism.L2.DIV.parLev_St h2
  refine ⟨κ, h1, hs, fun w => ?_⟩
  have h4 : Formalism.L2.DIV.upperLeftBlock le_rfl (Formalism.L2.DIV.redFn β w.1 (finE V κ)) = g w := congrFun h3 w
  have h5 := Formalism.L2.DIV.upper_block_val_submatrix (r := V.rank) le_rfl
    (Formalism.L2.DIV.blockTri_blkOf_le _ _ (Formalism.L2.DIV.parLev_g h2 w.2))
  rw [h4, ← finR_rfl, Formalism.L2.DIV.redFn, Formalism.L2.DIV.extendOne_of_mem _ hs] at h5
  apply Units.ext
  rw [h5]
  rfl

end GlobalTheory.GeoLevel
