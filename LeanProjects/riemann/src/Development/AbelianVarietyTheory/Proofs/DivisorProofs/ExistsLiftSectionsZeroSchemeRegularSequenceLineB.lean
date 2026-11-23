import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedSectionChartCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalCombinationOfLocalRegularIdeal
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.RegSeqGlue

open GlobalTheory.Twist

variable {Y : Scheme.{0}} {L : LB Y}

def LocSpan (F : Y.Modules) {d : ℕ} (t : Fin d → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (x : Γ(twistZ F L m, O)) : Prop :=
  ∀ y ∈ O, ∃ (V : Y.Opens) (hV : V ≤ O), y ∈ V ∧ ∃ c : Fin d → Γ(twistZ F L l, V),
    (twistZ F L m).presheaf.map (homOfLE hV).op x = ∑ i, (mulSecOfEq F (zofSec (t i)) h).app V (c i)

theorem res_res (G : Y.Modules) {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(G, U)) :
    G.presheaf.map (homOfLE h₁).op (G.presheaf.map (homOfLE h₂).op x) =
      G.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem eq_zero_of_locSpan (F : Y.Modules) (t : Fin 0 → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (x : Γ(twistZ F L m, O)) (hx : LocSpan F t h x) : x = 0 :=
  section_eq_zero_of_germ x fun y hy => by
    obtain ⟨V, hV, hyV, c, e⟩ := hx y hy
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hV) y hyV, e, Finset.univ_eq_empty, Finset.sum_empty, map_zero]

variable (hL : L.IsLB)

theorem π_mul (F : Y.Modules) (s a : L.Sec) {l m : ℤ} (h : l + 1 = m) (V : Y.Opens) (u : Γ(twistZ F L l, V)) :
    (Twist.map (lbZPow L m) (cutπ F hL s)).app V ((mulSecOfEq F (zofSec a) h).app V u) =
      (mulSecOfEq (cut F hL s) (zofSec a) h).app V ((Twist.map (lbZPow L l) (cutπ F hL s)).app V u) := by
  rw [app_app, app_app, mulSecOfEq_naturality]

theorem map_locSpan (F : Y.Modules) {d : ℕ} (t : Fin (d + 1) → L.Sec) [Mono (cutHom F hL (t 0))] {l m : ℤ}
    (h : l + 1 = m) {O : Y.Opens} {x : Γ(twistZ F L m, O)} (hx : LocSpan F t h x) :
    LocSpan (cut F hL (t 0)) (fun i => t i.succ) h ((Twist.map (lbZPow L m) (cutπ F hL (t 0))).app O x) :=
  fun y hy => by
    obtain ⟨V, hV, hyV, c, e⟩ := hx y hy
    refine ⟨V, hV, hyV, fun i => (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app V (c i.succ), ?_⟩
    have := (RegSeqKer.shortExact_twistComplex hL F (t 0) h).mono_f
    have hex : Function.Exact ((mulSecOfEq F (zofSec (t 0)) h).app V)
        ((Twist.map (lbZPow L m) (cutπ F hL (t 0))).app V) :=
      exact_app_of_exact_of_mono (RegSeqKer.shortExact_twistComplex hL F (t 0) h).exact V
    rw [← app_res, e, Fin.sum_univ_succ, map_add, hex.apply_apply_eq_zero, zero_add, map_sum]
    exact Finset.sum_congr rfl fun i _ => π_mul hL F _ _ h V _

theorem exists_glue (d : ℕ) : ∀ (t : Fin d → L.Sec) (F : Y.Modules) [F.IsQuasicoherent] (j₀ l m : ℤ)
    (h : l + 1 = m), RegSeq hL F (List.ofFn t) → VanishFrom L F j₀ → j₀ + d ≤ m →
    ∀ (W : Y → Y.Opens) (b : ∀ y, Γ(twistZ F L m, W y)), (∀ y, y ∈ W y) →
    (∀ y z, LocSpan F t h ((twistZ F L m).presheaf.map (homOfLE (inf_le_left : W y ⊓ W z ≤ W y)).op (b y) -
      (twistZ F L m).presheaf.map (homOfLE (inf_le_right : W y ⊓ W z ≤ W z)).op (b z))) →
    ∃ σ : Γ(twistZ F L m, ⊤), ∀ y, LocSpan F t h ((twistZ F L m).presheaf.map (homOfLE le_top).op σ - b y) := by
  induction d with
  | zero =>
    intro t F _ j₀ l m h _ _ _ W b hW hb
    have hc : ∀ y z, (twistZ F L m).presheaf.map (homOfLE (inf_le_left : W y ⊓ W z ≤ W y)).op (b y) =
        (twistZ F L m).presheaf.map (homOfLE (inf_le_right : W y ⊓ W z ≤ W z)).op (b z) := fun y z =>
      sub_eq_zero.1 (eq_zero_of_locSpan F t h _ (hb y z))
    obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨(twistZ F L m).presheaf, (twistZ F L m).isSheaf⟩ W ⊤
      (fun y => homOfLE le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) b (fun y z => hc y z)
    refine ⟨σ, fun y z hz => ⟨W y, le_rfl, hz, fun i => i.elim0, ?_⟩⟩
    rw [hσ y, sub_self, map_zero, Finset.univ_eq_empty, Finset.sum_empty]
  | succ d ih =>
    intro t F _ j₀ l m h hr hv hj W b hW hb
    rw [List.ofFn_succ, regSeq_cons] at hr
    obtain ⟨hm0, hr⟩ := hr
    have hS := RegSeqKer.shortExact_twistComplex hL F (t 0) h
    have := hS.mono_f
    have hex : ∀ V : Y.Opens, Function.Exact ((mulSecOfEq F (zofSec (t 0)) h).app V)
        ((Twist.map (lbZPow L m) (cutπ F hL (t 0))).app V) := fun V =>
      exact_app_of_exact_of_mono hS.exact V
    obtain ⟨σ', hσ'⟩ := ih (fun i => t i.succ) (cut F hL (t 0)) (j₀ + 1) l m h hr
      (RegSeqKer.vanishFrom_cut hL F (t 0) hv) (by push_cast at hj; omega) W
      (fun y => (Twist.map (lbZPow L m) (cutπ F hL (t 0))).app (W y) (b y)) hW fun y z => by
        have := map_locSpan hL F t h (hb y z)
        rwa [map_sub, app_res, app_res] at this
    obtain ⟨σ, hσ⟩ := cohOn.app_surjective hS ⊤ (hv l (by push_cast at hj; omega) 1 one_pos) σ'
    change (Twist.map (lbZPow L m) (cutπ F hL (t 0))).app ⊤ σ = σ' at hσ
    have hEpi : Epi (Twist.map (lbZPow L l) (cutπ F hL (t 0))) :=
      (RegSeqKer.shortExact_twistComplex hL F (t 0) (l := l - 1) (m := l) (by omega)).epi_g
    have := isQuasicoherent_twist (F := F) (isLB_lbZPow hL l)
    have := isQuasicoherent_twist (F := cut F hL (t 0)) (isLB_lbZPow hL l)
    refine ⟨σ, fun y z hz => ?_⟩
    obtain ⟨V, hV, hzV, c', e⟩ := hσ' y z hz
    obtain ⟨A, hzA, hAV⟩ := exists_affine hzV
    have hlift : ∀ i, ∃ u : Γ(twistZ F L l, A.1), (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app A.1 u =
        (twistZ (cut F hL (t 0)) L l).presheaf.map (homOfLE hAV).op (c' i) := fun i =>
      surjective_app_of_epi _ A.2 _
    choose u hu using hlift
    obtain ⟨v, hv'⟩ := (hex A.1 ((twistZ F L m).presheaf.map (homOfLE (hAV.trans hV)).op
        ((twistZ F L m).presheaf.map (homOfLE le_top).op σ - b y) -
        ∑ i, (mulSecOfEq F (zofSec (t i.succ)) h).app A.1 (u i))).1 (by
      rw [map_sub, map_sum, sub_eq_zero]
      erw [app_res, map_sub, app_res, hσ]
      rw [← res_res _ hAV hV]
      erw [e]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [π_mul, hu]
      exact (app_res _ _ _).symm)
    refine ⟨A.1, hAV.trans hV, hzA, Fin.cons v u, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hv', sub_add_cancel]

end GlobalTheory.HSCore.RegSeqGlue

namespace GlobalTheory.HSCore.RegSeqGlue

open GlobalTheory.Twist GlobalTheory.HSKerRes

variable {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) {M L : LB Y} (hM : M.IsLB) (hL : L.IsLB)

include hM hL in

theorem toH0_res {n : ℤ} {O O' : Y.Opens} (h : O' ≤ O) (s : Γ(twistZ (LB.toMod M) L n, O)) :
    toH0 p ((twistZ (LB.toMod M) L n).presheaf.map (homOfLE h).op s) = H0.restr h (toH0 p s) :=
  tw_ext hM hL fun i j y hy hi hj => by
    rw [H0.germ_restr, germ_of_global_section p _ i j y _ hi hj, germ_of_global_section p _ i j y _ hi hj]
    erw [Twist.zcoord_resM]
    rw [HSKerRes.coord_resM, ger_resG]

include hM in

theorem vanishesTo_mulSec {d : ℕ} (t : Fin d → L.Sec) (a : Fin d) {n l : ℤ} (h : n + 1 = l) {O : Y.Opens}
    (f : Vanishing.H0 p (tw M L n) O) : VanishesTo (cutIdeal hL t) 1 (mulSec hM hL (t a) h f) :=
  vanishesTo_of_exists fun y _ hy => by
    obtain ⟨i, hi⟩ := exists_chart hM y
    obtain ⟨j, hj⟩ := exists_chart hL y
    refine ⟨twIdx l i j, mem_tw_U.2 ⟨hi, hj⟩, ?_⟩
    rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hj, pow_one, stalkId_cutIdeal hL t j y hj]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, rfl⟩)

include hM in

theorem vanishesTo_of_locSpan {d : ℕ} (t : Fin d → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (x : Γ(twistZ (LB.toMod M) L m, O)) (hx : LocSpan (LB.toMod M) t h x) :
    VanishesTo (cutIdeal hL t) 1 (toH0 p x) := fun y hs hy i hi => by
  obtain ⟨V, hV, hyV, c, e⟩ := hx y hy
  have hv : VanishesTo (cutIdeal hL t) 1 (H0.restr hV (toH0 p x)) := by
    rw [← toH0_res p hM hL, e, map_sum]
    show _ ∈ filTop p _ V (cutIdeal hL t) 1
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [mem_filTop, global_section_mul p hM hL (t a) h]
    exact vanishesTo_mulSec p hM hL t a h _
  have := hv y hs hyV i hi
  rwa [H0.germ_restr] at this

include hM in

theorem locSpan_of_vanishesTo {d : ℕ} (t : Fin d → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (s : Γ(twistZ (LB.toMod M) L m, O)) (hs : VanishesTo (cutIdeal hL t) 1 (toH0 p s)) :
    LocSpan (LB.toMod M) t h s := fun y hy => by
  obtain ⟨i, hi⟩ := exists_chart hM y
  obtain ⟨j, hj⟩ := exists_chart hL y
  obtain ⟨V, hV, e⟩ := exists_affine (memInf (memInf hy hi) hj)
  have hVO : V.1 ≤ O := e.trans (inf_le_left.trans inf_le_left)
  have hVi : V.1 ≤ M.U i := e.trans (inf_le_left.trans inf_le_right)
  have hVj : V.1 ≤ L.U j := e.trans inf_le_right
  have h₁ : V.1 ≤ O ⊓ (tw M L m).U (twIdx m i j) := fun _ hz => ⟨hVO hz, mem_tw_U.2 ⟨hVi hz, hVj hz⟩⟩
  have h₂ := vanishesTo_iff_affine.1 hs V _ h₁
  rw [pow_one, ideal_cutIdeal hL t V j hVj, restricted_section_chart_coords p s i j h₁ (le_inf (le_inf hVO hVj) hVi)] at h₂
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h₂
  refine ⟨V.1, hVO, hV, fun a => (Twist.zchartEquiv hL l j hVj).symm ((LB.chartEquiv hM i hVi).symm (c a)), ?_⟩
  refine (Twist.zchartEquiv hL m j hVj).injective ((LB.chartEquiv hM i hVi).injective ?_)
  simp only [map_sum, Twist.zchartEquiv_mulSecOfEq_app, map_smul, LinearEquiv.apply_symm_apply, Twist.zfun_zofSec,
    smul_eq_mul]
  rw [LB.chartEquiv_apply, Twist.zchartEquiv_apply]
  refine Eq.trans ?_ (hc.symm.trans (Finset.sum_congr rfl fun a _ => mul_comm _ _))
  rw [HSKerRes.coord_resM]
  erw [Twist.zcoord_resM]
  rw [HSKerRes.coord_resM, LB.resG_resG, LB.resG_resG]

end GlobalTheory.HSCore.RegSeqGlue

theorem GlobalTheory.HSCore.exists_glue_mod_regSeq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k Y) → ∀ (p : Y ⟶ Sp k) (M L : LB Y), M.IsLB → ∀ (hL : L.IsLB) (d : ℕ) (t : Fin d → L.Sec) (l : ℤ), RegSeq hL (GlobalTheory.LB.toMod M) (List.ofFn t) → VanishFrom L (GlobalTheory.LB.toMod M) 0 → (d : ℤ) ≤ l → ∀ (W : Y → Y.Opens) (b : ∀ y, Vanishing.H0 p (tw M L l) (W y)), (∀ y, y ∈ W y) → (∀ y z, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr inf_le_left (b y) - Vanishing.H0.restr inf_le_right (b z) : Vanishing.H0 p (tw M L l) (W y ⊓ W z))) → ∃ σ : Vanishing.H0 p (tw M L l) ⊤, ∀ y, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr le_top σ - b y) := by
  intro k _ Y _ _ p M L hM hL d t l hreg hvan hd W b hW hb
  have hl : l - 1 + 1 = l := by omega
  have := (VB.isVB_toMod hM).isFiniteQC
  have hs : ∀ y, ∃ β : Γ(twistZ (LB.toMod M) L l, W y), HSKerRes.toH0 p β = b y := fun y =>
    HSKerRes.surjective_ofTwist hM (Twist.isLB_lbZPow hL _) (b y)
  choose β hβ using hs
  obtain ⟨σ, hσ⟩ := RegSeqGlue.exists_glue hL d t (LB.toMod M) 0 (l - 1) l hl hreg hvan (by omega) W β hW
    fun y z => RegSeqGlue.locSpan_of_vanishesTo p hM hL t hl _ (by
      rw [map_sub, RegSeqGlue.toH0_res p hM hL, RegSeqGlue.toH0_res p hM hL, hβ, hβ]
      exact hb y z)
  refine ⟨HSKerRes.toH0 p σ, fun y => ?_⟩
  have := RegSeqGlue.vanishesTo_of_locSpan p hM hL t hl _ (hσ y)
  rwa [map_sub, RegSeqGlue.toH0_res p hM hL, hβ] at this
