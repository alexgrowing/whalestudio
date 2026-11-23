import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPointNormPowEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.HermCover

variable {F : Type} [Field F] [NumberField F]

theorem injective_emb (σ : 𝓞 F →+* ℂ) : Function.Injective σ :=
  (RingHom.injective_iff_ker_eq_bot _).2
    (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))

def extEmb (σ : 𝓞 F →+* ℂ) : F →+* ℂ := IsFractionRing.lift (K := F) (injective_emb σ)

theorem extEmb_comp (σ : 𝓞 F →+* ℂ) : (extEmb σ).comp (algebraMap (𝓞 F) F) = σ :=
  RingHom.ext fun x => by rw [RingHom.comp_apply, extEmb, IsFractionRing.lift_algebraMap]

theorem extEmb_restrict (τ : F →+* ℂ) : extEmb (τ.comp (algebraMap (𝓞 F) F)) = τ :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (extEmb_comp _)

theorem spMap_extEmb (σ : 𝓞 F →+* ℂ) : spMap σ = spMap (extEmb σ) ≫ spMap (algebraMap (𝓞 F) F) :=
  (congrArg spMap (extEmb_comp σ).symm).trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _))

variable {C : CxSt F} {Y : Var F} (V : Cover Y)

def liftPt (σ : 𝓞 F →+* ℂ) (y : CxPts V.p σ) : CxPts (V.π ≫ Y.str) (extEmb σ) :=
  ⟨V.pb.lift y.1 (spMap (extEmb σ)) (y.2.trans (spMap_extEmb σ)), V.pb.lift_snd _ _ _⟩

theorem liftPt_j (σ : 𝓞 F →+* ℂ) (y : CxPts V.p σ) : (liftPt V σ y).1 ≫ V.j = y.1 := V.pb.lift_fst _ _ _

abbrev down (τ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) τ) : Pts Y τ := Points.PtsOver.map V.π rfl _ z

variable {V} {B : LB V.X}

def wgt (A : Adl C Y) (r : (B.pull V.j).ι → V.G.functionFieldˣ) (τ : F →+* ℂ) (i : B.ι)
    (z : CxPts (V.π ≫ Y.str) τ) : ℝ :=
  Real.log (‖ratVal (V.φ (genAt A.D (under (down V τ z))) * (r (fun _ => i) : V.G.functionField)) z‖ ^ 2) -
    Real.log (Real.exp (-(2 * (A.n : ℕ) * A.ci (InfinitePlace.mk τ))) *
      C.pn Y τ A.D (A.m τ) (C.cx Y τ (genAt A.D (under (down V τ z)))) (down V τ z))

theorem wgt_congr (A : Adl C Y) (r : (B.pull V.j).ι → V.G.functionFieldˣ) (i : B.ι) {τ τ' : F →+* ℂ} (h : τ = τ')
    (z : CxPts (V.π ≫ Y.str) τ) (z' : CxPts (V.π ≫ Y.str) τ') (hz : z.1 = z'.1) : wgt A r τ i z = wgt A r τ' i z' := by
  subst h
  obtain rfl : z = z' := Subtype.ext hz
  rfl

theorem liftPt_mem {σ : 𝓞 F →+* ℂ} {y : CxPts V.p σ} {i : B.ι} (h : y ∈ ptsIn V.p σ (B.U i)) :
    liftPt V σ y ∈ ptsIn (V.π ≫ Y.str) (extEmb σ) ((B.pull V.j).U (fun _ => i)) := by
  rw [mem_ptsIn]
  refine Set.mem_iInter.2 fun _ => ?_
  show V.j.base _ ∈ B.U i
  have := mem_ptsIn.1 h
  rw [← liftPt_j V σ y] at this
  exact this

theorem wgt_trans (A : Adl C Y) {r : (B.pull V.j).ι → V.G.functionFieldˣ} (h : V.FinInd A B r) (σ : 𝓞 F →+* ℂ)
    (i j : B.ι) (y : CxPts V.p σ) (hi : y ∈ ptsIn V.p σ (B.U i)) (hj : y ∈ ptsIn V.p σ (B.U j)) :
    wgt A r (extEmb σ) j (liftPt V σ y) =
      wgt A r (extEmb σ) i (liftPt V σ y) - Real.log (‖gv V.p σ B i j y‖ ^ 2) := by
  set z := liftPt V σ y
  have hzi := liftPt_mem hi
  have hzj := liftPt_mem hj
  have hz := mem_ptsIn_inf.2 ⟨hzi, hzj⟩
  have hg := gen_mem (mem_ptsIn.1 hz)
  set g := genAt A.D (under (down V (extEmb σ) z))
  have hu : UnitAt (under z) (V.φ g * (r (fun _ => j) : V.G.functionField)) := h.2.1 _ _ (mem_ptsIn.1 hzj)
  have e₁ : V.φ g * (r (fun _ => i) : V.G.functionField) =
      fnOf _ hg ((B.pull V.j).g (fun _ => i) (fun _ => j) : Γ(V.G, _)) * (V.φ g * r (fun _ => j)) := by
    rw [h.1 _ _ hg]; ring
  have e₂ : ratVal (fnOf _ hg ((B.pull V.j).g (fun _ => i) (fun _ => j) : Γ(V.G, _))) z = gv V.p σ B i j y := by
    rw [ratVal_fnOf hz]
    exact (gv_linComb (m := fun _ => y) (fun _ => (liftPt_j V σ y).symm) hzi hzj).trans (by simp)
  have hgv : gv V.p σ B i j y ≠ 0 := gv_ne_zero hi hj
  have hne : ratVal (V.φ g * (r (fun _ => j) : V.G.functionField)) z ≠ 0 := ratVal_ne_zero hu
  simp only [wgt]
  rw [e₁, ratVal_mul (regAt_fnOf (mem_ptsIn.1 hz) hg _) hu.regAt, e₂, log_normSq_mul hgv hne]
  ring

def wt (A : Adl C Y) {r : (B.pull V.j).ι → V.G.functionFieldˣ} (hB : B.IsLB) (h : V.FinInd A B r) (σ : 𝓞 F →+* ℂ) :
    Weight V.p σ B where
  isLB := hB
  φ i y := wgt A r (extEmb σ) i (liftPt V σ y)
  trans i j y hi hj := wgt_trans A h σ i j y hi hj

theorem wt_φ (A : Adl C Y) {r : (B.pull V.j).ι → V.G.functionFieldˣ} (hB : B.IsLB) (h : V.FinInd A B r)
    (σ : 𝓞 F →+* ℂ) (i : B.ι) (y : CxPts V.p σ) : (wt A hB h σ).φ i y = wgt A r (extEmb σ) i (liftPt V σ y) := rfl

end GlobalTheory.Mean4O.HermCover

namespace GlobalTheory.Mean4O.HermCover
variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {V : Cover Y} {B : LB V.X}

theorem wt_conj (A : Adl C Y) {r : (B.pull V.j).ι → V.G.functionFieldˣ} (hB : B.IsLB) (h : V.FinInd A B r)
    (hc : ConjInv A) (σ σ' : 𝓞 F →+* ℂ) : (wt A hB h σ).IsConj (wt A hB h σ') := by
  intro i y y' hy _
  have hσ : σ' = (starRingEnd ℂ).comp σ := CxPts.eq_conj_of_conj hy
  have hext : extEmb σ' = (starRingEnd ℂ).comp (extEmb σ) := by
    rw [hσ, ← extEmb_restrict ((starRingEnd ℂ).comp (extEmb σ)), RingHom.comp_assoc, extEmb_comp]
  have hz : (liftPt V σ' y').1 = spMap (starRingEnd ℂ) ≫ (liftPt V σ y).1 := by
    refine V.pb.hom_ext ?_ ?_
    · rw [liftPt_j, Category.assoc, liftPt_j, hy]
    · rw [(liftPt V σ' y').2, Category.assoc, (liftPt V σ y).2, hext]
      exact Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)
  have hd : (down V _ (liftPt V σ' y')).1 = spMap (starRingEnd ℂ) ≫ (down V _ (liftPt V σ y)).1 := by
    show (liftPt V σ' y').1 ≫ V.π = spMap (starRingEnd ℂ) ≫ (liftPt V σ y).1 ≫ V.π
    rw [hz, Category.assoc]
  have hu : under (down V _ (liftPt V σ' y')) = under (down V _ (liftPt V σ y)) := by
    show below (down V _ (liftPt V σ' y')).1 = below (down V _ (liftPt V σ y)).1
    rw [hd]
    exact HtIndep.below_spMap_comp _ _
  have hmk : InfinitePlace.mk (extEmb σ') = InfinitePlace.mk (extEmb σ) := by
    rw [hext]
    exact InfinitePlace.mk_conjugate_eq _
  show wgt A r (extEmb σ') i (liftPt V σ' y') = wgt A r (extEmb σ) i (liftPt V σ y)
  simp only [wgt]
  rw [hc (extEmb σ) (extEmb σ') _ _ hd, hu, hmk, norm_ratVal_of_conj hz]
end GlobalTheory.Mean4O.HermCover

namespace GlobalTheory.Mean4O.HermCover
open scoped ContDiff
variable {F : Type} [Field F] [NumberField F] {Y : Var F} {V : Cover Y} {B : LB V.X}

theorem cInfAt_log_ev {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {W : X.Opens}
    (a : Γ(X, W)ˣ) {z : CxPts p σ} (hz : z ∈ ptsIn p σ W) :
    CInfAt (fun w => Real.log (‖ev p σ W a.val w‖ ^ 2)) z := by
  have hc : ContDiff ℝ ∞ fun v : Unit → ℂ => ‖v ()‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ ())
  refine ⟨W, Unit, inferInstance, fun _ => a.val, fun v => Real.log (‖v ()‖ ^ 2), {v | v () ≠ 0}, hz,
    isOpen_ne_fun (continuous_apply ()) continuous_const, ev_ne_zero hz a.isUnit,
    hc.contDiffOn.log fun v hv => pow_ne_zero 2 (norm_ne_zero_iff.2 hv), Filter.EventuallyEq.rfl⟩

theorem cInfAt_wgt (A : Adl (cxSt F) Y) {r : (B.pull V.j).ι → V.G.functionFieldˣ} (h : V.FinInd A B r)
    (hm : ∀ σ, (cxSt F).mSmooth Y σ A.D (A.m σ)) (τ : F →+* ℂ) (i : B.ι) (z : CxPts (V.π ≫ Y.str) τ)
    (hz : z ∈ ptsIn (V.π ≫ Y.str) τ ((B.pull V.j).U (fun _ => i))) : CInfAt (wgt A r τ i) z := by
  have hp := presents_toLB A.D
  have hpos := Var.mSmooth.posSet_eq (hm τ)
  set ψ := Var.Met.toWeight (A.m τ) hpos hp
  have hψ : ψ.IsCInf := (Weight.isCInf_iff_isSmooth (Y.an τ)).2 (Var.mSmooth.isSmooth_toWeight (hm τ) hp)
  have hpn := Var.pn_ofWeight_toWeight hpos hp
  obtain ⟨c, hc⟩ := exists_chart (isLB_toLB A.D) (under (down V τ z))
  set W : V.G.Opens := (B.pull V.j).U (fun _ => i) ⊓ V.π ⁻¹ᵁ (toLB A.D).U c
  have hzW : z ∈ ptsIn _ τ W := mem_ptsIn_inf.2 ⟨hz, mem_ptsIn.2 hc⟩
  have hunit : ∀ x ∈ W, UnitAt x ((r (fun _ => i) : V.G.functionField) * (V.φ ((c.1.2 : Y.Fn)))⁻¹) := by
    intro x hx
    have h1 : UnitAt x (V.φ (genAt A.D (V.π x)) * (r (fun _ => i) : V.G.functionField)) := h.2.1 _ x hx.1
    have h2 : UnitAt (V.π x) (genAt A.D (V.π x) * (c.1.2 : Y.Fn)) :=
      (hp.isEqn c (V.π x) hx.2).generatesAt_iff.1 (generatesAt_genAt _ _)
    have h3 := (V.unitAt_φ h2).inv
    have h0 : V.φ (genAt A.D (V.π x)) ≠ 0 := (map_ne_zero V.φ).2 (Units.ne_zero _)
    have e : (r (fun _ => i) : V.G.functionField) * (V.φ ((c.1.2 : Y.Fn)))⁻¹ =
        (V.φ (genAt A.D (V.π x)) * (r (fun _ => i) : V.G.functionField)) * (V.φ (genAt A.D (V.π x) * (c.1.2 : Y.Fn)))⁻¹ := by
      rw [map_mul]
      field_simp
    rw [e]
    exact h1.mul h3
  obtain ⟨a, ha⟩ := exists_unit_fnOf_eq hunit
  have hloc : ∀ w ∈ ptsIn _ τ W, wgt A r τ i w = Real.log (‖ev _ τ W a.val w‖ ^ 2) +
      2 * ((A.n : ℕ) : ℝ) * A.ci (InfinitePlace.mk τ) + ψ.φ c (down V τ w) := by
    intro w hw
    have hw2 : w ∈ ptsIn _ τ (V.π ⁻¹ᵁ (toLB A.D).U c) := (mem_ptsIn_inf.1 hw).2
    have hyc : under (down V τ w) ∈ (toLB A.D).U c := mem_ptsIn.1 hw2
    have hgen : A.D.GeneratesAt (under (down V τ w)) (genAt A.D (under (down V τ w))) := generatesAt_genAt _ _
    have hu2 : UnitAt (under (down V τ w)) (genAt A.D (under (down V τ w)) * (c.1.2 : Y.Fn)) :=
      (hp.isEqn c _ hyc).generatesAt_iff.1 hgen
    have eP : (cxSt F).pn Y τ A.D (A.m τ) ((cxSt F).cx Y τ (genAt A.D (under (down V τ w)))) (down V τ w) =
        ‖ratVal (genAt A.D (under (down V τ w)) * (c.1.2 : Y.Fn)) (down V τ w)‖ ^ 2 * Real.exp (-ψ.φ c (down V τ w)) :=
      (congrFun (congrFun hpn _) _).symm.trans
        ((cxSt F).pn_ofWeight Y τ A.D _ _ hp ψ _ (down V τ w) c hyc hgen.regularAt)
    have eR : ratVal (genAt A.D (under (down V τ w)) * (c.1.2 : Y.Fn)) (down V τ w) =
        ratVal (V.φ (genAt A.D (under (down V τ w)) * (c.1.2 : Y.Fn))) w := (V.ratVal_φ w _ rfl hu2.regAt).symm
    have hφu : UnitAt (under w) (V.φ (genAt A.D (under (down V τ w)) * (c.1.2 : Y.Fn))) := V.unitAt_φ hu2
    have hUu : UnitAt (under w) ((r (fun _ => i) : V.G.functionField) * (V.φ ((c.1.2 : Y.Fn)))⁻¹) :=
      hunit _ (mem_ptsIn.1 hw)
    have eU : ratVal ((r (fun _ => i) : V.G.functionField) * (V.φ ((c.1.2 : Y.Fn)))⁻¹) w = ev _ τ W a.val w := by
      rw [← ha (gen_mem (mem_ptsIn.1 hw)), ratVal_fnOf hw]
    have hc0 : V.φ ((c.1.2 : Y.Fn)) ≠ 0 := (map_ne_zero V.φ).2 (Units.ne_zero _)
    have e1 : V.φ (genAt A.D (under (down V τ w))) * (r (fun _ => i) : V.G.functionField) =
        V.φ (genAt A.D (under (down V τ w)) * (c.1.2 : Y.Fn)) *
          ((r (fun _ => i) : V.G.functionField) * (V.φ ((c.1.2 : Y.Fn)))⁻¹) := by
      rw [map_mul]
      field_simp
    have hA : ratVal (V.φ (genAt A.D (under (down V τ w)) * (c.1.2 : Y.Fn))) w ≠ 0 := ratVal_ne_zero hφu
    have hE : ev _ τ W a.val w ≠ 0 := ev_ne_zero hw a.isUnit
    simp only [wgt]
    rw [e1, ratVal_mul hφu.regAt hUu.regAt, eU, eP, eR, log_normSq_mul hA hE,
      Real.log_mul (Real.exp_pos _).ne' (mul_pos (pow_pos (norm_pos_iff.2 hA) 2) (Real.exp_pos _)).ne',
      Real.log_exp, Real.log_mul (pow_pos (norm_pos_iff.2 hA) 2).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hψc : CInfAt (ψ.φ c) (down V τ z) := hψ c _ (mem_ptsIn.2 hc)
  refine (((cInfAt_log_ev a hzW).add (cInfAt_const (2 * ((A.n : ℕ) : ℝ) * A.ci (InfinitePlace.mk τ)) z)).add
    (CInfAt.pull V.π rfl hψc)).congr ?_
  filter_upwards [(isOpen_ptsIn W).mem_nhds hzW] with w hw using hloc w hw
end GlobalTheory.Mean4O.HermCover

namespace GlobalTheory.Mean4O.HermCover
variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {V : Cover Y} {B : LB V.X}

theorem wt_cInf (A : Adl C Y) {r : (B.pull V.j).ι → V.G.functionFieldˣ} (hB : B.IsLB) (h : V.FinInd A B r)
    (hm : ∀ σ, C.mSmooth Y σ A.D (A.m σ)) (σ : 𝓞 F →+* ℂ) : (wt A hB h σ).IsCInf := by
  obtain rfl : C = cxSt F := Subsingleton.elim _ _
  intro i y hy
  let m : CxPts (V.π ≫ Y.str) (extEmb σ) → CxPts V.p σ := fun w =>
    ⟨w.1 ≫ V.j, by rw [Category.assoc, V.pb.w, ← Category.assoc, w.2, ← spMap_extEmb]⟩
  have hlm : ∀ w, liftPt V σ (m w) = w := fun w =>
    Subtype.ext (V.pb.hom_ext (liftPt_j V σ (m w)) (by rw [(liftPt V σ (m w)).2, w.2]))
  have hmz : m (liftPt V σ y) = y := Subtype.ext (liftPt_j V σ y)
  rw [← hmz]
  refine OnModelCInf.baseChange_cInfAt F V.X V.G V.p (V.π ≫ Y.str) V.j V.pb (extEmb σ) σ m (fun _ => rfl) _ _ ?_
  refine (cInfAt_wgt A h hm (extEmb σ) i _ (liftPt_mem hy)).congr (Filter.Eventually.of_forall fun w => ?_)
  show wgt A r (extEmb σ) i (liftPt V σ (m w)) = wgt A r (extEmb σ) i w
  rw [hlm]
end GlobalTheory.Mean4O.HermCover

namespace GlobalTheory.Mean4O.HermCover

theorem exists_hermLB_induces : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y) (A : Adl C Y) (B : LB V.X) (r : (B.pull V.j).ι → V.G.functionFieldˣ), B.IsLB → V.FinInd A B r → (∀ σ, C.mSmooth Y σ A.D (A.m σ)) → ConjInv A → ∃ L : HermLB V.p, V.Induces A L 1 := by
  intro F _ _ C Y V A B r hB h hm hc
  have hcinf : ∀ σ, (wt A hB h σ).IsCInf := wt_cInf A hB h hm
  have hconj : ∀ σ σ', (wt A hB h σ).IsConj (wt A hB h σ') := wt_conj A hB h hc
  have hpos : ∀ σ (y : Pts Y σ), 0 < C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y := by
    obtain rfl : C = cxSt F := Subsingleton.elim _ _
    intro σ y
    exact CombForm.pn_pos_of_generatesAt (generatesAt_genAt _ _) (posAt_of_posSet (Var.mSmooth.posSet_eq (hm σ)) y)
  refine ⟨⟨B, hB, wt A hB h, hcinf, hconj⟩, r, h.1, fun i x hx => by simpa using h.2.1 i x hx, ?_, ?_⟩
  · intro σ z y y' i e₁ e₂ hi
    have hi' : i = fun _ => i PUnit.unit := funext fun _ => rfl
    have hz : (liftPt V _ y').1 = z.1 := V.pb.hom_ext ((liftPt_j V _ y').trans e₂) (by
      rw [(liftPt V _ y').2, z.2, extEmb_restrict])
    have hy : y = down V σ z := Subtype.ext e₁
    show _ = _ * Real.exp (-(wgt A r (extEmb (σ.comp (algebraMap (𝓞 F) F))) (i PUnit.unit) (liftPt V _ y')))
    rw [wgt_congr A r _ (extEmb_restrict σ) _ z hz, wgt, hy, pow_one, pow_one, ← hi']
    have hu : UnitAt (under z) (V.φ (genAt A.D (under (down V σ z))) * (r i : V.G.functionField)) := h.2.1 i _ hi
    have hR : 0 < ‖ratVal (V.φ (genAt A.D (under (down V σ z))) * (r i : V.G.functionField)) z‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2
    have hQ := mul_pos (Real.exp_pos (-(2 * ((A.n : ℕ) : ℝ) * A.ci (InfinitePlace.mk σ)))) (hpos σ (down V σ z))
    rw [neg_sub, Real.exp_sub, Real.exp_log hQ, Real.exp_log hR, ← mul_div_assoc, mul_div_cancel_left₀ _ hR.ne']
  · intro v e y z yt i e₁ e₂ hi
    have := h.2.2 v e y z yt i e₁ e₂ hi
    rw [pow_one, Nat.cast_one, one_mul]
    exact this
end GlobalTheory.Mean4O.HermCover
