import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSectionsFormFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitSectionOfLocalValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.Twist (resM resM_resM)
open GlobalTheory.GroupBplus (AffOp Kbar genPt)
open GlobalTheory.OmegaHT (crd ToOpen)

namespace GlobalTheory.ChainPts.SysB.FormRes

attribute [local instance] Over.cartesianMonoidalCategory

open MonObj CategoryTheory.Obj in

theorem exists_comb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
    (Z : LocM.Mdl Y i₀) {r : ℕ} {x : Fin r → Letter Dw} (hx : Function.Bijective x) (a : Fin Z.m) {k : Type} [CommRing k]
    (φ : Γ(Z.X, (Z.U a).1) →+* k) {y : Sp k ⟶ (Y Z.i).X} (hy : spMap φ ≫ Z.chart a ≫ Z.π = y)
    {v : Sp (DualNumber k) ⟶ (Y Z.i).t.G.left} (hv : IsTanAtG (Y Z.i).t y v) :
    ∃ cf : Fin r → k, IsCombAtG (Y Z.i).t y (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf v := by
  subst hy
  have hu : LocM.IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ) :=
    isFrame_bc E H Dw _ _ _ _ _ _ _ φ _ _ (Z.frame a)
  obtain ⟨c, hc, -⟩ := GlobalTheory.TanSec.Frame.exists_unique_coords hu (LieMet.tanOf hv)
  refine ⟨fun i => c (x i), (LieMet.isComb_iff (fun i => LieMet.tanOf (hu.1 (x i).1 (x i).2).1) _ (LieMet.tanOf hv)).2 ?_⟩
  exact hc.trans (Function.Bijective.sum_comp hx fun j => c j • LieMet.tanOf (hu.1 j.1 j.2).1).symm

theorem valF_crd_resM {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {V V' T : X.Opens} {s : Fin r → Γ(F, T)}
    (hs : GlobalTheory.VB.IsFrame s) (hle : V' ≤ V) (σ : Γ(F, V)) {k : Type} [Field k] {w : Sp k ⟶ X}
    (hw : ⊤ ≤ w ⁻¹ᵁ (V' ⊓ T)) (i : Fin r) : valF w _ (crd hs (resM F hle σ) i) = valF w _ (crd hs σ i) := by
  rw [← FieldPtGlue.valF_restrict (inf_le_inf_right T hle) hw, crd, crd]
  refine congrArg (valF w _) ?_
  exact ((congrArg (fun m => (hs.basis inf_le_right).repr m i)
    ((resM_resM _ _ _).trans (resM_resM _ _ _).symm))).trans (hs.repr_resM inf_le_right (inf_le_inf_right T hle) _ i)

theorem genPt_apply (X : Scheme.{0}) [IsIntegral X] (q : Sp (Kbar X)) : genPt X q = genericPoint X := by
  have h : genericPoint X ∈ Set.range (X.fromSpecStalk (genericPoint X)) := ⟨_, Scheme.fromSpecStalk_closedPoint⟩
  obtain ⟨q', hq'⟩ := h
  have : Subsingleton (Spec (X.presheaf.stalk (genericPoint X))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  exact (congrArg (X.fromSpecStalk (genericPoint X)) (Subsingleton.elim _ q')).trans hq'

theorem formResSt : GlobalTheory.ChainPts.SysB.FormResSt := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z X _ h r x hx hopn F s hs U U' hle t t' φt φt' hφt lam lam' hl hl' σ v v' hv
  let κ' : U'.Bp →+* Kbar X := algebraMap _ _
  let κ : U.Bp →+* Kbar X := algebraMap _ _
  have e : κ'.comp (AffOp.res hle) = κ := RingHom.ext fun _ => rfl
  have g : spMap κ ≫ U.toX = genPt X := U.val_toX
  have g' : spMap κ' ≫ U'.toX = genPt X := U'.val_toX
  have hη : h (genericPoint X) ∈ Z.opn := hopn _ fun y hy => (hy.antisymm (genericPoint_specializes y)).eq
  rw [← Z.cover] at hη
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hη
  have hT : ⊤ ≤ (genPt X ≫ h) ⁻¹ᵁ (Z.U a).1 := fun q _ => by
    show h (genPt X q) ∈ (Z.U a).1
    rw [genPt_apply]
    exact ha
  have hU' : ⊤ ≤ genPt X ⁻¹ᵁ U'.1 := fun q _ => by
    show genPt X q ∈ U'.1
    rw [genPt_apply]
    exact ((genericPoint_spec X).mem_open_set_iff U'.1.isOpen).2 (by simpa using U'.2.2)
  obtain ⟨φ, hφ⟩ := Pull.exists_fromSpec (Z.U a).2 (genPt X ≫ h) hT
  have hφ₀ : spMap φ ≫ Z.chart a = genPt X ≫ h := hφ
  have hφ₁ : spMap φ ≫ Z.chart a = spMap κ ≫ U.toX ≫ h := by rw [hφ₀, ← g, Category.assoc]
  have hφ₂ : spMap φ ≫ Z.chart a = spMap κ' ≫ U'.toX ≫ h := by rw [hφ₀, ← g', Category.assoc]
  have hy : spMap κ' ≫ U'.toX ≫ h ≫ Z.π = spMap κ ≫ U.toX ≫ h ≫ Z.π := by
    rw [← Category.assoc, g', ← g, Category.assoc]
  have hw : spMap (Formalism.L2.Pj.dualMap κ') ≫ v'.1.left ≫ φt' = spMap (Formalism.L2.Pj.dualMap κ) ≫ v.1.left ≫ φt := by
    rw [hv, ← Category.assoc, ← Cris.spMap_comp, ← e]
    congr 2
    refine RingHom.ext fun z => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap]
  obtain ⟨cf, hcf⟩ := exists_comb Z hx a φ (y := spMap κ ≫ U.toX ≫ h ≫ Z.π)
    (by rw [← Category.assoc, hφ₁, Category.assoc, Category.assoc])
    (LieMet.isTan_map κ rfl (TanPair.isTanAtG_lieG hφt v))
  have h₁ := hl σ v _ κ a φ hφ₁ cf hcf
  have h₂ := hl' (resM F hle σ) v' _ κ' a φ hφ₂ cf (by rw [hy, hw]; exact hcf)
  refine Subtype.ext (h₂.trans (Eq.trans ?_ h₁.symm))
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g, g', valF_crd_resM (hs a) hle σ fun q hq => ⟨hU' hq, hT hq⟩]

end GlobalTheory.ChainPts.SysB.FormRes

end
