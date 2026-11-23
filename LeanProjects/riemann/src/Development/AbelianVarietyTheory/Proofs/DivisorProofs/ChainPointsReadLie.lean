import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistPullback

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.VB GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Pad.Pull GlobalTheory.FieldPtGlue GlobalTheory.ChainPts
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TriFrame

theorem valF_inv {X : Scheme.{0}} {U : X.Opens} (u : Γ(X, U)ˣ) {F : Type} [Field F] {w : Sp F ⟶ X} (hw : ⊤ ≤ w ⁻¹ᵁ U) :
    valF w U (u⁻¹).val = (valF w U u.val)⁻¹ := eq_inv_of_mul_eq_one_right (valF_mul_inv hw u)

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) {Z : LocM.Mdl Y i₀} [IsDiscreteValuationRing (Z.i.c.V W)]
  {r : ℕ} {st : Fin r → ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Fin r → Letter Dw} (M : ∀ i, LineModel Z false (st i) (x i))
  (M' : ∀ i, LineModel Z true (st i) (x i)) (u : ∀ i, GenIso Z (M i).L (M' i).L) (hu : ∀ i, IsGenId (M i) (M' i) (u i))
  (c : (nmodel Z).Comp) {B : Vert.Model (Z.i.c.V W)} (f : Vert.Model.Hom B ((nmodel Z).comp c))
  (hB : GlobalTheory.IsNormalScheme B.X) {F F' : B.X.Modules} (hF : IsVB F r) (hF' : IsVB F' r) (ψ : F' ⟶ F)
  [IsIso (B.genRes.map ψ)] {s : ∀ a : Fin Z.m, Fin r → Γ(F', (f.f ≫ (nmodel Z).compι c) ⁻¹ᵁ (Z.U a).1)}

omit [IsDiscreteValuationRing (Z.i.c.V W)] in

theorem trans_dual {b : Bool} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (M : LineModel Z b st x) (a : Fin Z.m) (k : Type)
    [Field k] (w : Sp k ⟶ Z.X) (i i' : Fin M.L.n) (hw : ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (M.L.U i ⊓ M.L.U i'))) :
    valF w _ (M.r a i')⁻¹.val = valF w _ (M.L.g i i')⁻¹.val * valF w _ (M.r a i)⁻¹.val := by
  rw [valF_inv (M.r a i') fun q hq => ⟨(hw hq).1, (hw hq).2.2⟩, valF_inv (M.L.g i i') fun q hq => (hw hq).2,
    valF_inv (M.r a i) fun q hq => ⟨(hw hq).1, (hw hq).2.1⟩, M.trans k w a i i' hw, mul_inv]

include hp hW hu hB hF hF'

theorem exists_pair_lie (hN : StepNorms Dw p st x) (h' : IsLat Z (f.f ≫ (nmodel Z).compι c) x false false F' s)
    (h : IsLat Z (f.f ≫ (nmodel Z).compι c) x false true F fun a i => ψ.app _ (s a i)) :
    ∃ Q : Vert.Model.FlagPair (Vert.Model.GenIso.ofHom ψ).symm r, ∀ i,
      picSymPull f.f (picSymPull ((nmodel Z).compι c) (M i).L.c1) = c1 _ (Q.fl.isLB_root i) ∧
      Vert.Model.vPull f.comp_str ((nmodel Z).vRes c (NModel.GenIso.div (u i) (M i).L.isLB (M' i).L.isLB)) =
        (Q.div i).cls := by
  refine (exists_chart c f).elim fun a ha => ?_
  refine (exists_flagPair ha ψ (h'.frame a) (h.frame a) (fun i => (pullLB _ _).isLB)
    (fun i => (pullLB _ _).isLB) (fun i => isGenOn_pullFn _ fun k _ w => (M' i).trans k w a)
    (fun i => isGenOn_pullFn _ fun k _ w => (M i).trans k w a)
    (tri_lie hp hW hB M' ha hF h hN) (tri_lie hp hW hB M ha hF' h' hN)).elim fun Q hQ => ?_
  refine ⟨symmPair Q, fun i => ⟨firstChernClassTateTwist_pullback c f _ _ (hQ i).2.1, ?_⟩⟩
  have e := (hQ i).2.2 _ (isRatio_pull (Z := nmodel Z) c f (NModel.GenIso.symm (u i))
    ((M' i).r a) ((M i).r a) fun k _ w j j' h₁ h₂ => by
      have e₁ := hu i k w a j' j fun q hq => ⟨(h₂ hq).1, (h₂ hq).2.2, (h₂ hq).2.1⟩
      have h₃ : ⊤ ≤ w ⁻¹ᵁ ((nmodel Z).gen ⊓ ((M i).L.U j' ⊓ (M' i).L.U j)) :=
        fun q hq => ⟨h₁ hq, (h₂ hq).2.2, (h₂ hq).2.1⟩
      have h₄ : ⊤ ≤ w ⁻¹ᵁ ((nmodel Z).gen ⊓ ((M' i).L.U j ⊓ (M i).L.U j')) := fun q hq => ⟨h₁ hq, (h₂ hq).2⟩
      have e₂ := valF_mul_inv h₃ ((u i).u j' j)
      refine (congrArg (· * _) (valF_restrict _ h₄ _)).trans ?_
      rw [← e₁, ← _root_.mul_assoc]
      exact (congrArg (· * _) ((_root_.mul_comm _ _).trans e₂)).trans (_root_.one_mul _))
  rw [VertDiv.cls_pull, ← NModel.vRes_cls] at e
  rw [cls_div_symmPair, e, ← map_neg, ← map_neg]
  exact congrArg _ (congrArg _ (neg_eq_iff_eq_neg.1 (NModel.GenIso.div_symm _ _ _).symm))

theorem exists_pair_dual (hN : StepNorms Dw p (fun i => st i.rev) fun i => x i.rev)
    (h' : IsLat Z (f.f ≫ (nmodel Z).compι c) x true true F' s)
    (h : IsLat Z (f.f ≫ (nmodel Z).compι c) x true false F fun a i => ψ.app _ (s a i)) :
    ∃ Q : Vert.Model.FlagPair (Vert.Model.GenIso.ofHom ψ) r, ∀ i,
      picSymPull f.f (picSymPull ((nmodel Z).compι c) (M i).L.dual.c1) = c1 _ (Q.fl.isLB_root i) ∧
      Vert.Model.vPull f.comp_str ((nmodel Z).vRes c
        (NModel.GenIso.div (NModel.GenIso.dual (u i)) (M i).L.dual.isLB (M' i).L.dual.isLB)) = (Q.div i).cls := by
  refine (exists_chart c f).elim fun a ha => ?_
  refine (exists_flagPair ha ψ (h'.frame a) (h.frame a) (fun i => (pullLB _ _).isLB)
    (fun i => (pullLB _ _).isLB) (fun i => isGenOn_pullFn (L := (M i).L.dual) _ (trans_dual (M i) a))
    (fun i => isGenOn_pullFn (L := (M' i).L.dual) _ (trans_dual (M' i) a))
    (tri_dual hp hW hB M ha hF h hN) (tri_dual hp hW hB M' ha hF' h' hN)).elim fun Q hQ => ?_
  refine ⟨Q, fun i => ⟨firstChernClassTateTwist_pullback c f _ _ (hQ i).1, ?_⟩⟩
  have e := (hQ i).2.2 _ (isRatio_pull (Z := nmodel Z) c f (L := (M i).L.dual) (L' := (M' i).L.dual)
    (NModel.GenIso.dual (u i)) (fun k => ((M i).r a k)⁻¹) (fun k => ((M' i).r a k)⁻¹) fun k _ w j j' h₁ h₂ => by
      have e₁ := hu i k w a j j' h₂
      have e₂ := valF_inv ((u i).u j j') (w := w) fun q hq => ⟨h₁ hq, (h₂ hq).2⟩
      have e₃ := valF_inv ((M i).r a j) (w := w) fun q hq => ⟨(h₂ hq).1, (h₂ hq).2.1⟩
      have e₄ := valF_inv ((M' i).r a j') (w := w) fun q hq => ⟨(h₂ hq).1, (h₂ hq).2.2⟩
      refine (congrArg₂ (· * ·) e₂ e₃).trans (Eq.trans ?_ e₄.symm)
      rw [← e₁, mul_inv])
  rw [VertDiv.cls_pull, ← NModel.vRes_cls] at e
  exact e.symm

end Pair

section admitted

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW)

theorem readsLie : ReadsLie z := fun _ _ _ _ h _ hN c _ f hB _ P hP =>
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := P.iso
  hP.2.elim fun _ hs => (exists_pair_lie hp hW _ _ _ (fun i => z.isGenId_genId hp hW (h i)) c f hB (hP.1 ▸ P.vb)
    (hP.1 ▸ P.vb') P.ψ hN hs.1 hs.2).imp fun _ hQ i => ⟨(hQ i).1, congrArg Vert.Model.toQ (hQ i).2⟩

theorem readsOm : ReadsOm z := fun _ _ _ _ h _ hN c _ f hB _ P hP =>
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := P.iso
  hP.2.elim fun _ hs => (exists_pair_dual hp hW _ _ _ (fun i => z.isGenId_genId hp hW (h i)) c f hB (hP.1 ▸ P.vb)
    (hP.1 ▸ P.vb') P.ψ hN hs.1 hs.2).imp fun _ hQ i => ⟨(hQ i).1, congrArg Vert.Model.toQ (hQ i).2⟩

end admitted

theorem readsLieSt : ReadsLieSt := fun _ _ _ _ _ _ _ _ _ z => readsLie z

theorem readsOmSt : ReadsOmSt := fun _ _ _ _ _ _ _ _ _ z => readsOm z

end GlobalTheory.TriFrame

end
