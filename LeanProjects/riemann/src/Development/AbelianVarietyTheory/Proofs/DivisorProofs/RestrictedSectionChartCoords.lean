import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRegularSequenceOfCommonZerosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalCombinationOfLocalRegularIdealStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSKerRes

section Dictionary

variable {Y : Scheme.{0}} {M N : LB Y} {O W : Y.Opens}

theorem coord_resM (h : W ≤ O) (s : Γ(LB.toMod M, O)) (i : M.ι) :
    LB.coord (Twist.resM (LB.toMod M) h s) i = resG Y (inf_le_inf_right _ h) (LB.coord s i) :=
  LB.coord_map h s i

theorem le_tens (O : Y.Opens) (q : (tens M N).ι) : O ⊓ (tens M N).U q ≤ O ⊓ N.U q.2 ⊓ M.U q.1 :=
  fun _ hy => ⟨⟨hy.1, hy.2.2⟩, hy.2.1⟩

def ofTwistFun (s : Γ(twist (LB.toMod M) N, O)) : Γ(LB.toMod (tens M N), O) :=
  LB.mkSec (fun q => resG Y (le_tens O q) (LB.coord (Twist.coord s q.2) q.1)) fun p q => by
    have h₁ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ O ⊓ N.U p.2 := fun _ hy => ⟨hy.1.1, hy.1.2.2⟩
    have h₂ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ O ⊓ N.U q.2 := fun _ hy => ⟨hy.1.1, hy.2.2⟩
    have h₃ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ M.U p.1 := fun _ hy => hy.1.2.1
    have h₄ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ M.U q.1 := fun _ hy => hy.2.1
    have e₁ := congrArg (fun r => resG Y (le_inf le_rfl h₄) (LB.coord r q.1))
      (Twist.coord_rel s p.2 q.2 h₁ h₂ (le_inf (h₁.trans inf_le_right) (h₂.trans inf_le_right)))
    have e₂ := LB.coord_rel (Twist.coord s p.2) p.1 q.1 (le_inf h₁ h₃) (le_inf h₁ h₄) (le_inf h₃ h₄)
    simp only [coord_resM, LB.coord_smul, map_mul, LB.resG_resG] at e₁
    simp only [LB.resG_resG]
    refine e₂.trans ?_
    rw [e₁, ← mul_assoc]
    refine congrArg (· * _) ?_
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (LB.resG_resG _ _ _) (LB.resG_resG _ _ _))).symm

theorem coord_ofTwistFun (s : Γ(twist (LB.toMod M) N, O)) (q : (tens M N).ι) :
    LB.coord (ofTwistFun s) q = resG Y (le_tens O q) (LB.coord (Twist.coord s q.2) q.1) := rfl

def ofTwist : Γ(twist (LB.toMod M) N, O) →+ Γ(LB.toMod (tens M N), O) where
  toFun := ofTwistFun
  map_zero' := LB.sec_ext fun q => by
    rw [coord_ofTwistFun, Twist.coord_zero, LB.coord_zero, map_zero, LB.coord_zero]
  map_add' s t := LB.sec_ext fun q => by
    rw [LB.coord_add, coord_ofTwistFun, coord_ofTwistFun, coord_ofTwistFun, Twist.coord_add, LB.coord_add, map_add]

theorem tens_le (O : Y.Opens) (i : M.ι) (j : N.ι) : O ⊓ N.U j ⊓ M.U i ≤ O ⊓ (tens M N).U (i, j) :=
  fun _ hy => ⟨hy.1.1, hy.2, hy.1.2⟩

theorem tens_rel (f : Γ(LB.toMod (tens M N), O)) (i i' : M.ι) (j j' : N.ι) (h : W ≤ O ⊓ (tens M N).U (i, j))
    (h' : W ≤ O ⊓ (tens M N).U (i', j')) (hM : W ≤ M.U i ⊓ M.U i') (hN : W ≤ N.U j ⊓ N.U j') :
    resG Y h (LB.coord f (i, j)) = resG Y hM (M.g i i' : Γ(Y, M.U i ⊓ M.U i')) *
      resG Y hN (N.g j j' : Γ(Y, N.U j ⊓ N.U j')) * resG Y h' (LB.coord f (i', j')) := by
  refine (LB.coord_rel f (i, j) (i', j') h h' (le_inf (h.trans inf_le_right) (h'.trans inf_le_right))).trans ?_
  refine congrArg (· * _) ?_
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (LB.resG_resG _ _ _) (LB.resG_resG _ _ _))

theorem surjective_ofTwist (hM : M.IsLB) (hN : N.IsLB) :
    Function.Surjective (ofTwist : Γ(twist (LB.toMod M) N, O) → Γ(LB.toMod (tens M N), O)) := fun f => by
  let a : ∀ j : N.ι, Γ(LB.toMod M, O ⊓ N.U j) := fun j =>
    LB.mkSec (fun i => resG Y (tens_le O i j) (LB.coord f (i, j))) fun i i' => by
      simp only [LB.resG_resG]
      refine (tens_rel f i i' j j _ (by exact fun _ hy => ⟨hy.1.1.1, hy.2, hy.1.1.2⟩)
        (by exact fun _ hy => ⟨hy.1.2, hy.2⟩) (by exact fun _ hy => ⟨hy.1.1.2, hy.1.1.2⟩)).trans ?_
      exact congrArg (· * _) ((congrArg (_ * ·) (LB.resG_g_self hN _ _)).trans (mul_one _))
  have ha : ∀ j i, LB.coord (a j) i = resG Y (tens_le O i j) (LB.coord f (i, j)) := fun _ _ => rfl
  refine ⟨Twist.mkSec a fun j j' => LB.sec_ext fun i => ?_, LB.sec_ext fun q => ?_⟩
  · simp only [coord_resM, LB.coord_smul, ha, LB.resG_resG]
    refine (tens_rel f i i j j' _ (by exact fun _ hy => ⟨hy.1.1.1, hy.2, hy.1.2⟩)
      (by exact fun _ hy => ⟨hy.2, hy.2⟩) (by exact fun _ hy => ⟨hy.1.1.2, hy.1.2⟩)).trans ?_
    exact congrArg (· * _) ((congrArg (· * _) (LB.resG_g_self hM _ _)).trans (one_mul _))
  · refine (coord_ofTwistFun _ q).trans ?_
    exact (LB.resG_resG (tens_le O q.1 q.2) (le_tens O q) (LB.coord f q)).trans (LB.resG_self _ _)

variable {k : Type} [CommRing k] (p : Y ⟶ Sp k) {L : LB Y} {n l : ℤ}

def toH0 : Γ(twistZ (LB.toMod M) L n, O) →+ Vanishing.H0 p (tw M L n) O := ofTwist

theorem restricted_section_chart_coords (s : Γ(twistZ (LB.toMod M) L n, O)) (i : M.ι) (j : L.ι)
    (h : W ≤ O ⊓ (tw M L n).U (twIdx n i j)) (h' : W ≤ O ⊓ L.U j ⊓ M.U i) :
    resG Y h ((toH0 p s).loc (twIdx n i j)) = resG Y h' (LB.coord (Twist.zcoord s j) i) := by
  rw [Twist.zcoord, coord_resM, LB.resG_resG]
  exact LB.resG_resG _ _ _

theorem germ_of_global_section (s : Γ(twistZ (LB.toMod M) L n, O)) (i : M.ι) (j : L.ι) (y : Y) (hy : y ∈ O)
    (hi : y ∈ M.U i) (hj : y ∈ L.U j) :
    H0.germ (twIdx n i j) y hy (mem_tw_U.2 ⟨hi, hj⟩) (toH0 p s) =
      ger y (memInf (memInf hy hj) hi) (LB.coord (Twist.zcoord s j) i) := by
  have h : O ⊓ L.U j ⊓ M.U i ≤ O ⊓ (tw M L n).U (twIdx n i j) := fun _ hz => ⟨hz.1.1, mem_tw_U.2 ⟨hz.2, hz.1.2⟩⟩
  have e := congrArg (ger y (memInf (memInf hy hj) hi)) (restricted_section_chart_coords p s i j h le_rfl)
  rwa [ger_resG, ger_resG] at e

theorem global_section_mul (hM : M.IsLB) (hL : L.IsLB) (w : L.Sec) (h : n + 1 = l) (s : Γ(twistZ (LB.toMod M) L n, O)) :
    toH0 p ((Twist.mulSecOfEq (LB.toMod M) (Twist.zofSec w) h).app O s) = mulSec hM hL w h (toH0 p s) :=
  tw_ext hM hL fun i j y hy hi hj => by
    rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hj, germ_of_global_section p _ i j y hy hi hj, germ_of_global_section p _ i j y hy hi hj,
      Twist.zcoord_mulSecOfEq_app, LB.coord_smul, map_mul, ger_resG, ger_resG, Twist.zfun_zofSec]

theorem exists_local (hM : M.IsLB) (hL : L.IsLB) {d : ℕ} (t : Fin d → L.Sec) (h : n + 1 = l)
    (s : Γ(twistZ (LB.toMod M) L l, ⊤)) (hs : VanishesTo (cutIdeal hL t) 1 (toH0 p s)) (y : Y) :
    ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin d → Γ(twistZ (LB.toMod M) L n, W)),
      (twistZ (LB.toMod M) L l).presheaf.map (homOfLE le_top).op s =
        ∑ i, (Twist.mulSecOfEq (LB.toMod M) (Twist.zofSec (t i)) h).app W (m i) := by
  obtain ⟨i, hi⟩ := exists_chart hM y
  obtain ⟨j, hj⟩ := exists_chart hL y
  obtain ⟨V, hV, e⟩ := exists_affine (memInf hi hj)
  have hVi : V.1 ≤ M.U i := e.trans inf_le_left
  have hVj : V.1 ≤ L.U j := e.trans inf_le_right
  have h₁ : V.1 ≤ ⊤ ⊓ (tw M L l).U (twIdx l i j) := fun _ hz => ⟨trivial, mem_tw_U.2 ⟨hVi hz, hVj hz⟩⟩
  have h₂ := vanishesTo_iff_affine.1 hs V _ h₁
  rw [pow_one, ideal_cutIdeal hL t V j hVj, restricted_section_chart_coords p s i j h₁ (le_inf (le_inf le_top hVj) hVi)] at h₂
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h₂
  refine ⟨V.1, hV, fun a => (Twist.zchartEquiv hL n j hVj).symm ((LB.chartEquiv hM i hVi).symm (c a)), ?_⟩
  refine (Twist.zchartEquiv hL l j hVj).injective ((LB.chartEquiv hM i hVi).injective ?_)
  simp only [map_sum, Twist.zchartEquiv_mulSecOfEq_app, map_smul, LinearEquiv.apply_symm_apply, Twist.zfun_zofSec,
    smul_eq_mul]
  rw [LB.chartEquiv_apply, Twist.zchartEquiv_apply]
  refine Eq.trans ?_ (hc.symm.trans (Finset.sum_congr rfl fun a _ => mul_comm _ _))
  rw [coord_resM]
  erw [Twist.zcoord_resM]
  rw [coord_resM, LB.resG_resG, LB.resG_resG]

end Dictionary

section Main

variable {K : Type} [Field K] [NumberField K] (G : Geo K)

theorem ger_comb_sum {ι : Type} [Fintype ι] (a : ι → K) (u : ι → Fin G.N → K) (j : G.L.ι) (y : G.Y) (hj : y ∈ G.L.U j) :
    ger y hj ((G.comb (∑ i, a i • u i)).f j) = ∑ i, H0.const G.str y (a i) * ger y hj ((G.comb (u i)).f j) := by
  have key (v : Fin G.N → K) : H0.ofSec G.str ⊤ (G.comb v) =
      Fintype.linearCombination K (fun c => H0.ofSec G.str ⊤ (G.b c)) v := G.ofSec_comb ⊤ v
  rw [← H0.germ_ofSec (p := G.str) j y (TopologicalSpace.Opens.mem_top y) hj, key, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, H0.germ_smul, ← key, H0.germ_ofSec]

theorem vanishesTo_of_isUnit (s : Fin G.D → Fin G.N → K) (g : Matrix (Fin G.D) (Fin G.D) K) (hg : IsUnit g.det)
    {B : LB G.Y} {O : G.Y.Opens} {f : Vanishing.H0 G.str B O} (hf : VanishesTo (G.ideal s) 1 f) :
    VanishesTo (G.ideal fun i => ∑ j, g i j • s j) 1 f := fun y _ hy c hc => by
  have h := vanishesTo_iff_forall.1 hf y hy c hc
  obtain ⟨j, hj⟩ := exists_chart G.isLB y
  rw [pow_one, stalkId_cutIdeal G.isLB _ j y hj] at h ⊢
  refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_) h
  have e : s a = ∑ i, g⁻¹ a i • ∑ j, g i j • s j := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change ger y hj ((G.comb (s a)).f j) ∈ Ideal.span _
  rw [e, ger_comb_sum]
  exact sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Main

theorem exists_global {k : Type} [Field k] {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)] (hY : IsProjOver (GlobalTheory.strHom k Y))
    (p : Y ⟶ Sp k) {M L : LB Y} (hM : M.IsLB) (hL : L.IsLB) {d : ℕ} (t : Fin d → L.Sec) {n l : ℤ} (h : n + 1 = l)
    (hreg : RegSeq hL (LB.toMod M) (List.ofFn t)) (hvan : VanishFrom L (LB.toMod M) 0) (hd : (d : ℤ) ≤ n + 1)
    (f : Vanishing.H0 p (tw M L l) ⊤) (hf : VanishesTo (cutIdeal hL t) 1 f) :
    ∃ μ : Fin d → Vanishing.H0 p (tw M L n) ⊤, f = ∑ i, mulSec hM hL (t i) h (μ i) := by
  subst h
  obtain ⟨σ, rfl⟩ : ∃ σ : Γ(twistZ (LB.toMod M) L (n + 1), ⊤), toH0 p σ = f :=
    surjective_ofTwist hM (Twist.isLB_lbZPow hL _) f
  have := (VB.isVB_toMod hM).isFiniteQC
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_global_combination_of_local_regular_ideal k Y hY L hL d t (LB.toMod M) 0 n hreg hvan ((zero_add _).trans_le hd) σ
    (exists_local p hM hL t rfl σ hf)
  refine ⟨fun i => toH0 p (m i), (congrArg (toH0 p) hm).trans ?_⟩
  exact (map_sum (toH0 p) _ _).trans (Finset.sum_congr rfl fun i _ => global_section_mul p hM hL _ rfl (m i))

theorem kerRes : Quoted → KerRes := by
  intro Q K _ _ G hnef hbig s hs l hl f hf
  obtain ⟨⟨f, rfl⟩, hv⟩ := mem_Fil.1 hf
  have hB : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  obtain ⟨g, hg, hreg⟩ := GlobalTheory.T.exists_basis_regular_sequence_of_common_zeros K G s hs _ hB
  have hv' := vanishesTo_of_isUnit G s g hg ((vanishesTo_restr_iff hs.inU le_top).1 hv)
  have hproj : IsProjOver (GlobalTheory.strHom K G.Y) := by
    rw [GlobalTheory.strHom_eq (f := G.str) fun _ => rfl]
    exact G.geom.alg.variety.proj
  obtain ⟨μ, e⟩ := exists_global hproj G.str hB G.isLB _ (Nat.cast_succ l).symm hreg (GlobalTheory.T.kawamataViehweg_vanishing_numberField_twist Q K G hnef hbig)
    (by exact_mod_cast hl) f hv'
  refine ⟨fun j => H0.restr le_top (∑ i, g i j • μ i), fun j => ⟨_, rfl⟩, ?_⟩
  have e' (i) : H0.restr (le_top : G.U ≤ ⊤) (mulSec hB G.isLB (G.comb (∑ j, g i j • s j)) (Nat.cast_succ l).symm (μ i)) =
      G.mulW l (∑ j, g i j • s j) (H0.restr le_top (μ i)) := by
    rw [G.mulW_apply, mulSec, mulSec, ProdChart.restr_mul, H0.restr_ofSec]
  rw [e, map_sum]
  simp only [e', map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_comm

end GlobalTheory.HSKerRes
