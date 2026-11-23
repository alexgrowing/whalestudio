import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothBaseAndNormalCoordinateRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellIsClosedInLeadingMinorOpenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImmersionOfClosedPieces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RangeInterCellOpenSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLESpMapFromSpec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.FlagEmb.cells_glue : ∀ (O K : Type) [CommRing O] [IsNoetherianRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover β s V α c D → IsPlk β s V α c p0 p h → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), IsImmersion f ∧ (∀ b w, IsOpenImmersion (i b w)) ∧ (∀ b w, i b w ≫ f = h b w) ∧ ∀ x : F, ∃ b w, x ∈ Set.range (i b w) := by
  intro O K _ _ _ β X s T _ m M B _ V α c D P p0 p h hs hX hC hP
  have hLN : ∀ {Y : Scheme.{0}} (g : Y ⟶ Sp O), IsProjOver g → IsLocallyNoetherian Y := by
    intro Y g hg
    obtain ⟨N, ι, _, rfl⟩ := hg
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str O N)
  haveI : IsLocallyNoetherian X := hLN s hs
  haveI : IsLocallyNoetherian P := hLN _ hP.proj
  have hW : ∀ b w, ∃ W, IsCellOpen p0 p (V b) (D b) w W := fun b w =>
    GlobalTheory.FlagEmb.CellOpen.exists_isCellOpen O X P T m M p0 p (V b) (D b) w
  choose W hW using hW
  have hcl := fun b w => GlobalTheory.T.flagCell_isClosed_in_leadingMinor_open O K β X s T m M B V α c D P p0 p h hC hP inferInstance hs b w (W b w) (hW b w)
  choose h' hh' hci using hcl
  have hred : ∀ b, AlgebraicGeometry.IsReduced (Sp (CR m (V b))) := by
    intro b
    have hn := (GlobalTheory.FlagEmb.cell_smooth_normal X T m (V b) hX).2
    haveI := fun x => (hn x).1
    exact isReduced_of_isReduced_stalk _
  let ι := B × Pm m
  haveI : Finite (Pm m) := Pi.finite
  haveI : ∀ a : ι, IsAffine (Sp (CR m (V a.1))) := fun a => inferInstance
  haveI : ∀ a : ι, AlgebraicGeometry.IsReduced (Sp (CR m (V a.1))) := fun a => hred a.1
  obtain ⟨F, f, i, hf, hio, hcomp, hcov⟩ := GlobalTheory.MemberGlue.exists_immersion_of_closed_pieces P ι
    (fun a => Sp (CR m (V a.1))) (fun a => h a.1 a.2) (fun a => W a.1 a.2) (fun a => h' a.1 a.2) inferInstance
    (fun a => hh' a.1 a.2) (fun a => hci a.1 a.2)
    (fun a a' => GlobalTheory.FlagEmb.Overlap.range_inter_cellOpen_subset O K β X s T m M B V α c D P p0 p h hC hP a.1 a.2
      (W a.1 a.2) (hW a.1 a.2) a'.1 a'.2)
  refine ⟨F, f, fun b w => i (b, w), hf, fun b w => hio (b, w), fun b w => hcomp (b, w), fun x => ?_⟩
  obtain ⟨a, ha⟩ := hcov x
  exact ⟨a.1, a.2, ha⟩
