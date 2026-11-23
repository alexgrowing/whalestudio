import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPointCarryingFrameLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleAdmissibleLocalComponentFiniteA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsConjPlOfUnderEqOfNe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedFnConjLocFinEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFrameInvMul

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
namespace GlobalTheory.TrPtFrame

theorem finLoc_locFin_ne {D : D7} (V : HSp D) {u v : HeightOneSpectrum (𝓞 D.host.F)} (h : u ≠ v) (x : Gv V v) :
    finLoc V u (locFin V v x) = 1 := by
  show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram u ((locFin V v x : GfC V) : GA D V) = 1
  rw [coe_locFin]
  exact GlobalTheory.AdelicU.proj_emb_ne _ _ h x

theorem mem_parLev {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank) (hQ : L.Q = ∅) {x : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    (hU : x ∈ UA D.sp.cm V.gram) (hS : x ∈ St β) : x ∈ parLev D.sp.cm V.gram β L := by
  rw [Formalism.L2.DIV.mem_parLev]
  refine ⟨hU, hS, fun PP _ => ?_, fun PP hP => ?_⟩
  · rw [Formalism.L2.DIV.mem_blockTri]
    intro i j hij
    exfalso
    simp [Formalism.L2.DIV.blkOf, h] at hij
  · exfalso
    simp [hQ] at hP

theorem upperLeftBlock_apply_of_eq {D : D7} {n r : ℕ} (hr : r ≤ n) (h : r = n) (PP : Pl D.host.E) (g : GL (Fin n) (kP PP)) (i j : Fin r) :
    ((upperLeftBlock hr g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) i j = (g : Matrix (Fin n) (Fin n) (kP PP)) (i.cast h) (j.cast h) := by
  subst h
  have hm : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
    rw [Formalism.L2.DIV.mem_blockTri]
    intro a b hab
    exfalso
    simp [Formalism.L2.DIV.blk2] at hab
  rw [Formalism.L2.DIV.upper_block_val_submatrix hr hm, Matrix.submatrix_apply]
  rfl

private theorem finLoc_locFin' {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Gv V v) :
    finLoc V v (locFin V v x) = x := by
  show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v ((locFin V v x : GfC V) : GA D V) = x
  rw [coe_locFin]
  exact GlobalTheory.AdelicU.proj_emb_self _ _ v x

private theorem upperLeftBlock_one {D : D7} {n r : ℕ} (hr : r ≤ n) (PP : Pl D.host.E) :
    (upperLeftBlock hr (1 : GL (Fin n) (kP PP)) : GL (Fin r) (kP PP)) = 1 :=
  Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (Formalism.L2.DIV.blkR hr)

theorem exists_splitFrame_levG : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → ∃ (a : GfC V) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ L.Pg) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ∀ v : S, ResF v.1 ≃+* kP (pl v).1), (∀ v ∉ S, ∀ k ∈ Kv V v, ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ levG V β (flag1L L)) ∧ ∀ (v : S) (k : Kv V v), ∃ g0 : G0 L.Pg L.r, IsLevelLift V β L g0 ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∧ (∀ PP, PP ≠ pl v → g0 PP = 1) ∧ ∀ i j : Fin L.r, (g0 (pl v)).1 i j = ρ v (((s v).red k).1 (i.cast h) (j.cast h)) := by
  intro D V β Λ N L h hB hQ hPg
  classical
  obtain ⟨a, hLat, hSt⟩ := GlobalTheory.FramePointMove.exists_point_carrying_frameLat D V β Λ N hB

  have hStk : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (k : Gv V v), k ∈ Kv V v →
      finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β := by
    intro v k hk
    refine (hSt (locFin V v k)).2 fun u => ?_
    by_cases huv : u = v
    · subst huv
      rw [finLoc_locFin']
      exact hk
    · rw [finLoc_locFin_ne V huv k]
      exact Subgroup.one_mem _

  have hinj : ∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F) → PP = PP' := by
    intro PP hP PP' hP' he
    by_contra hne
    exact hPg PP hP PP' hP' (GlobalTheory.UnderConj.isConjPl_of_under_eq_of_ne D PP PP' he hne)
  let S : Finset (HeightOneSpectrum (𝓞 D.host.F)) := L.Pg.image fun PP => PP.under (𝓞 D.host.F)
  let f : L.Pg → S := fun PP => ⟨PP.1.under (𝓞 D.host.F), Finset.mem_image_of_mem _ PP.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro PP PP' he
      exact Subtype.ext (hinj _ PP.2 _ PP'.2 (congrArg Subtype.val he))
    · intro v
      obtain ⟨PP, hP, he⟩ := Finset.mem_image.1 v.2
      exact ⟨⟨PP, hP⟩, Subtype.ext he⟩
  let pl : S ≃ L.Pg := (Equiv.ofBijective f hf).symm
  have hunder : ∀ v : S, (pl v).1.under (𝓞 D.host.F) = v.1 := fun v =>
    congrArg Subtype.val ((Equiv.ofBijective f hf).apply_symm_apply v)
  choose s ρ hsρ using fun v : S =>
    GlobalTheory.SplitPlaceRed.splitRed_frame D V β Λ N a hB hLat v.1 (pl v).1 (hunder v)
      (hPg _ (pl v).2 _ (pl v).2) (fun k => hStk v.1 k.1 k.2)
  refine ⟨a, S, pl, s, ρ, ?_, ?_⟩
  · intro v hv k hk
    have hx := hStk v k hk
    rw [Formalism.IndefR.Lev.levG, Formalism.IndefR.Lev.mem_levA]
    refine ⟨(a * locFin V v k * a⁻¹ : GfC V).2, ?_⟩
    rw [Formalism.L2.DIV.mem_lev]
    refine ⟨mem_parLev (flag1L L) h hQ (GlobalTheory.LevSplit.finE_mem_UA V _) hx, ?_⟩
    have hone : ∀ PP ∈ L.Pg, redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = 1 := by
      intro PP hP
      refine GlobalTheory.PlaceAwayRed.redFn_conj_locFin_eq_one D V β a v PP (fun he => hv ?_) k hx
      rw [← he]
      exact Finset.mem_image_of_mem _ hP
    have hrt : rTup β (flag1L L) (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = rTup β (flag1L L) 1 := by
      funext PP
      simp only [Formalism.L2.DIV.rTup]
      rw [hone PP.1 PP.2, Formalism.L2.DIV.redFn_one]
    rw [hrt, Formalism.L2.DIV.rTup_one]
    exact Subgroup.one_mem _
  · intro v k
    have hx := hStk v.1 k.1 k.2
    refine ⟨rTup β L (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)),
      ⟨(a * locFin V v k * a⁻¹ : GfC V).2, mem_parLev L h hQ (GlobalTheory.LevSplit.finE_mem_UA V _) hx, rfl⟩, ?_, ?_⟩
    · intro PP hne
      have hu : PP.1.under (𝓞 D.host.F) ≠ v.1 := by
        intro he
        exact hne (Subtype.ext (hinj _ PP.2 _ (pl v).2 (he.trans (hunder v).symm)))
      show upperLeftBlock L.hr (redFn β PP.1 (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V))) = 1
      rw [GlobalTheory.PlaceAwayRed.redFn_conj_locFin_eq_one D V β a v.1 PP.1 hu k.1 hx]
      exact upperLeftBlock_one L.hr PP.1
    · intro i j
      show ((upperLeftBlock L.hr (redFn β (pl v).1 (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V))) :
        GL (Fin L.r) (kP (pl v).1)) : Matrix (Fin L.r) (Fin L.r) (kP (pl v).1)) i j = _
      rw [upperLeftBlock_apply_of_eq L.hr h]
      exact hsρ v k (i.cast h) (j.cast h)

end GlobalTheory.TrPtFrame
