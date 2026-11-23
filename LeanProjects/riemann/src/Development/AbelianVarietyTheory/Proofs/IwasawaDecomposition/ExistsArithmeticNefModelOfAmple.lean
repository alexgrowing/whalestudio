import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullWIsConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartDirectionalDerivativeRegularCoordinate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.AmpleKaehler
open GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.Points

namespace GlobalTheory.AmpleModelPos

theorem isGenerated_tens {X : Scheme.{0}} {A B : LB X} (hA : IsGenerated A) (hB : IsGenerated B) :
    IsGenerated (tens A B) := by
  obtain ⟨a, s, hs⟩ := hA
  obtain ⟨b, t, ht⟩ := hB
  refine isGenerated_of_finite (fun q : Fin a × Fin b => EndOnTorsion.tensSec (s q.1) (t q.2))
    (top_le_iff.1 fun y _ => ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), (EndOnTorsion.nonzeroLocus_tensSec (s i) (t j)).ge ⟨hi, hj⟩⟩

section Pull

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D N : ℕ}

theorem semiPos_pull_fsO1 (f : Y ⟶ PSpace k N) (hf : f ≫ PSpace.str k N = p) (R : AnRead p σ D) :
    ((ProjAn.fsO1 k σ N).pull f hf).SemiPos R := by
  intro i c y hy ξ
  obtain ⟨j, rfl⟩ : ∃ j : Fin (N + 1), i = fun _ => j := ⟨i PUnit.unit, rfl⟩
  have hW : y ∈ ptsIn p σ (f ⁻¹ᵁ chart k N j) := mem_ptsIn.2 (Set.mem_iInter.1 (mem_ptsIn.1 hy.2) PUnit.unit)
  have ho := ChartGlue.isOpen_over (R.chart c).e (isOpen_ptsIn (p := p) (σ := σ) (f ⁻¹ᵁ chart k N j))
  have hn := ho.mem_nhds (ChartGlue.mem_over (R.chart c).e hy.1 hW)
  let g (a : Fin (N + 1)) : ReciprocityTheory.L2DbarEstimates.V D → ℂ :=
    ev p σ (f ⁻¹ᵁ chart k N j) (f.app _ (ratio k N j a)) ∘ (R.chart c).e.symm
  have hg (a) : ContDiffAt ℂ 2 (g a) ((R.chart c).e y) :=
    ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho ((R.chart c).holo _ _)).contDiffAt hn).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hj : g j ((R.chart c).e y) = 1 := by
    simp only [g, Function.comp_apply, (R.chart c).e.left_inv hy.1]
    have h1 : ratio k N j j = 1 := ratioOn_self
    rw [h1, map_one, ev_eq hW, map_one]
  have hpos : 0 < ∑ a, Complex.normSq (g a ((R.chart c).e y)) :=
    Finset.sum_pos' (fun a _ => Complex.normSq_nonneg _) ⟨j, Finset.mem_univ _, by rw [hj, map_one]; exact one_pos⟩
  have := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg (u := fun a v => Complex.normSq (g a v))
    (fun a => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hg a)) (fun a => ReciprocityTheory.L2DbarEstimates.logPshAt_normSq (hg a)) hpos ξ
  have e : (fun v => (((ProjAn.fsO1 k σ N).pull f hf).φ (fun _ => j) ((R.chart c).e.symm v) : ℂ)) =
      fun v => ((Real.log (∑ a, Complex.normSq (g a v)) : ℝ) : ℂ) := by
    funext v
    rw [ProjPos.fubiniStudy_weight_pullback_chart_formula]
    simp only [g, Function.comp_apply, Complex.normSq_eq_norm_sq]
  rw [e]
  exact this

end Pull

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

omit [NumberField F] in

theorem valR_ratio_baseChange {n : ℕ} (x : Sp ℂ ⟶ PSpace F n) (j a : Fin (n + 1)) :
    valR (x ≫ baseChange n (algebraMap (𝓞 F) F)) (chart (𝓞 F) n j) (ratio (𝓞 F) n j a) =
      valR x (chart F n j) (ratio F n j a) := by
  rw [valR_comp, ratio, baseChange_app_ratioOn]
  have key : ∀ (U : (PSpace F n).Opens) (hU : U = chart F n j) (hi : U ≤ chart F n j),
      valR x U (ratioOn U j hi a) = valR x (chart F n j) (ratio F n j a) := by
    rintro _ rfl _
    rfl
  exact key _ (baseChange_preimage_chart n _ j) _

omit [NumberField F] in

theorem pull_fsO1_ptMap (Z : TrueGeo.Model Y) (σ : F →+* ℂ) {n : ℕ} (f : Y.X ⟶ PSpace F n)
    (hf : f ≫ PSpace.str F n = Y.str) (g : Z.X ⟶ PSpace (𝓞 F) n) (hg : g ≫ PSpace.str (𝓞 F) n = Z.p)
    (h : Z.j ≫ g = f ≫ baseChange n (algebraMap (𝓞 F) F)) (j : PUnit → Fin (n + 1)) (y : Pts Y σ) :
    ((ProjAn.fsO1 (𝓞 F) (σ.comp (algebraMap (𝓞 F) F)) n).pull g hg).φ j (OfModel.ptMap Z σ y) =
      ((ProjAn.fsO1 F σ n).pull f hf).φ j y := by
  rw [show j = fun _ => j PUnit.unit from rfl, ProjPos.fubiniStudy_weight_pullback_chart_formula, ProjPos.fubiniStudy_weight_pullback_chart_formula]
  refine congrArg Real.log (Finset.sum_congr rfl fun a _ => ?_)
  change ‖valR ((y : Sp ℂ ⟶ Y.X) ≫ Z.j) _ _‖ ^ 2 = ‖valR (y : Sp ℂ ⟶ Y.X) _ _‖ ^ 2
  rw [← valR_comp, ← valR_comp, Category.assoc, h, ← Category.assoc, valR_ratio_baseChange]

theorem exists_model_strictPos : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ : Y.Dv), Y.ample Δ →
    ∃ (q : ℕ+) (Z : TrueGeo.Model Y) (L : HermLB Z.p) (r : (L.B.pull Z.j).ι → Y.Fnˣ),
      Presents ((q : ℕ) • Δ) (L.B.pull Z.j) r ∧ ArInt.NefFib L ∧
        ∀ σ : F →+* ℂ, (pullW Z L σ).IsSmooth (Y.an σ) ∧ (pullW Z L σ).StrictPos (Y.an σ) := by
  intro F _ _ Y Δ hΔ
  have := CommonModel.isProper_of_isProjOver Y.isProjOver
  obtain ⟨e, he, he1⟩ := ((AmpleDominates.eventually_isGenerated Y.str hΔ Y.isAmple_projective_O_one.isLB).and
    (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨b, sb, hsb⟩ := he.exists_fin_succ
  let α := algebraMap (𝓞 F) F
  let c := Y.str ≫ spMap α
  have hfa : (Y.ι ≫ baseChange Y.N α) ≫ PSpace.str (𝓞 F) Y.N = Y.str ≫ spMap α := by
    rw [Category.assoc, baseChange_str, ← Category.assoc]
    rfl
  obtain ⟨X, π, j, hX, hπ, hfl, H, ⟨ga, ha₁, ha₂⟩, gb, hb₁, hb₂⟩ :=
    IntModel.exists_flat_model_two (O := 𝓞 F) Y.str Y.isProjOver ⟨Y.N, 𝟙 _, inferInstance, Category.id_comp _⟩
      ⟨b, 𝟙 _, inferInstance, Category.id_comp _⟩ hfa (toProj_str c sb hsb)
  have := CommonModel.isProper_of_isProjOver hπ
  have hZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 F)).2 inferInstance
  have har : IsArithVar π Y.dim := ⟨inferInstance, inferInstance, hX, hπ, inferInstance,
    IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField F) H Y.topologicalKrullDim_eq⟩
  let Z : TrueGeo.Model Y := ⟨X, π, har, j, H⟩
  let La : HermLB Z.p := (hermitianTwistingSheaf (𝓞 F) Y.N).pull ga ha₂
  let Lb : HermLB Z.p := (hermitianTwistingSheaf (𝓞 F) b).pull gb hb₂
  let L : HermLB Z.p := La.tens Lb
  let fb := toProj Y.str sb hsb
  have hfb : fb ≫ PSpace.str F b = Y.str := toProj_str _ _ _
  have hb₁' : Z.j ≫ gb = fb ≫ baseChange b α := hb₁.trans (toProj_baseChange α Y.str sb hsb).symm
  have hL : (L.B.pull Z.j).IsLB := LB.isLB_pull L.isLB Z.j
  have ea : pull Z.j (cls La.B La.isLB) = cls Y.O1 (LB.isLB_pull (O1_isLB F Y.N) Y.ι) := by
    have e₀ : cls La.B La.isLB = pull ga (cls _ (O1_isLB (𝓞 F) Y.N)) := cls_pull (O1_isLB (𝓞 F) Y.N) ga La.isLB
    rw [e₀, ← pull_comp, show Z.j ≫ ga = Y.ι ≫ baseChange Y.N α from ha₁,
      pull_comp, ← cls_pull (O1_isLB (𝓞 F) Y.N) _ (LB.isLB_pull (O1_isLB (𝓞 F) Y.N) _),
      (cls_eq_iff _ (O1_isLB F Y.N)).2 (lbIso_pull_O1 Y.N α), cls_pull (O1_isLB F Y.N)]
  have eb : pull Z.j (cls Lb.B Lb.isLB) = cls _ he.isLB := IntModel.pull_cls_O1 Z.j c he.isLB sb hsb gb hb₁ Lb.isLB
  obtain ⟨r, hr⟩ := IntModel.exists_presents (((⟨e, he1⟩ : ℕ+) : ℕ) • Δ) hL (by
    change toPic (e • Δ) = _
    have e₁ : cls L.B L.isLB = cls La.B La.isLB + cls Lb.B Lb.isLB := cls_tens La.isLB Lb.isLB L.isLB
    rw [cls_pull L.isLB Z.j hL, e₁, map_add, ea, eb,
      cls_div (isLB_lbPow (isLB_toLB Δ) e) (LB.isLB_pull (O1_isLB F Y.N) Y.ι), cls_lbPow (isLB_toLB Δ),
      map_nsmul, toPic_apply]
    abel)
  refine ⟨⟨e, he1⟩, Z, L, r, hr, OfLattice.nefFib_of_isGenerated har L
    (isGenerated_tens ((isGenerated_O1 _ _).pull ga) ((isGenerated_O1 _ _).pull gb)), fun σ => ?_⟩
  let ψa := (ProjAn.fsO1 F σ Y.N).pull Y.ι rfl
  let ψb := (ProjAn.fsO1 F σ b).pull fb hfb
  have sa : ψa.IsSmooth (Y.an σ) := ProjPos.fubiniStudy_weight_pullback_isSmooth _ _ _
  have pa : ψa.StrictPos (Y.an σ) := ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos _ _ _
  have sb' : ψb.IsSmooth (Y.an σ) := ProjPos.fubiniStudy_weight_pullback_isSmooth _ _ _
  have pb : ψb.SemiPos (Y.an σ) := semiPos_pull_fsO1 _ _ _
  have eq (i : (L.B.pull Z.j).ι) (y : Pts Y σ) :
      (pullW Z L σ).φ i y = ψa.φ (i PUnit.unit).1 y + ψb.φ (i PUnit.unit).2 y := by
    rw [pullW_φ]
    exact congrArg₂ (· + ·) (pull_fsO1_ptMap Z σ Y.ι rfl ga ha₂ ha₁ _ y)
      (pull_fsO1_ptMap Z σ fb hfb gb hb₂ hb₁' _ y)
  have mem (i : (L.B.pull Z.j).ι) (y : Pts Y σ) (hy : y ∈ ptsIn Y.str σ ((L.B.pull Z.j).U i)) :
      y ∈ ptsIn Y.str σ (((O1 F Y.N).pull Y.ι).U (i PUnit.unit).1) ∧
        y ∈ ptsIn Y.str σ (((O1 F b).pull fb).U (i PUnit.unit).2) := by
    have h1 := mem_ptsIn_inf.1 (mem_of_mem_linComb (m := fun _ => OfModel.ptMap Z σ y) (fun _ => rfl) hy PUnit.unit)
    have ha := mem_ptsIn.1 (mem_of_mem_linComb (m := fun _ => PtsOver.map ga ha₂ _ (OfModel.ptMap Z σ y))
      (fun _ => rfl) h1.1 PUnit.unit)
    have hb := mem_ptsIn.1 (mem_of_mem_linComb (m := fun _ => PtsOver.map gb hb₂ _ (OfModel.ptMap Z σ y))
      (fun _ => rfl) h1.2 PUnit.unit)
    refine ⟨mem_ptsIn.2 (Set.mem_iInter.2 fun _ => ?_), mem_ptsIn.2 (Set.mem_iInter.2 fun _ => ?_)⟩
    · have e : ((y : Sp ℂ ⟶ Y.X) ≫ Z.j) ≫ ga = ((y : Sp ℂ ⟶ Y.X) ≫ Y.ι) ≫ baseChange Y.N α := by
        rw [Category.assoc, Category.assoc]
        exact congrArg _ ha₁
      have ha' := ha
      change (((y : Sp ℂ ⟶ Y.X) ≫ Z.j) ≫ ga).base (IsLocalRing.closedPoint ℂ) ∈
        chart (𝓞 F) Y.N ((i PUnit.unit).1 PUnit.unit) at ha'
      rw [e] at ha'
      have hm : ((y : Sp ℂ ⟶ Y.X) ≫ Y.ι).base (IsLocalRing.closedPoint ℂ) ∈
          chart F Y.N ((i PUnit.unit).1 PUnit.unit) := by
        exact (SetLike.ext_iff.1 (baseChange_preimage_chart Y.N α ((i PUnit.unit).1 PUnit.unit)) _).1 ha'
      exact hm
    · have e : ((y : Sp ℂ ⟶ Y.X) ≫ Z.j) ≫ gb = ((y : Sp ℂ ⟶ Y.X) ≫ fb) ≫ baseChange b α := by
        rw [Category.assoc, Category.assoc]
        exact congrArg _ hb₁'
      have hb' := hb
      change (((y : Sp ℂ ⟶ Y.X) ≫ Z.j) ≫ gb).base (IsLocalRing.closedPoint ℂ) ∈
        chart (𝓞 F) b ((i PUnit.unit).2 PUnit.unit) at hb'
      rw [e] at hb'
      have hm : ((y : Sp ℂ ⟶ Y.X) ≫ fb).base (IsLocalRing.closedPoint ℂ) ∈
          chart F b ((i PUnit.unit).2 PUnit.unit) := by
        exact (SetLike.ext_iff.1 (baseChange_preimage_chart b α ((i PUnit.unit).2 PUnit.unit)) _).1 hb'
      exact hm
  have hs : (pullW Z L σ).IsSmooth (Y.an σ) := by
    refine (Weight.isCInf_iff_isSmooth (Y.an σ)).1 fun i y hy => ?_
    obtain ⟨m1, m2⟩ := mem i y hy
    exact (((Weight.isCInf_iff_isSmooth (Y.an σ)).2 sa _ y m1).add
      ((Weight.isCInf_iff_isSmooth (Y.an σ)).2 sb' _ y m2)).congr (.of_forall fun z => eq i z)
  refine ⟨hs, fun i c y hy ξ hξ => ?_⟩
  obtain ⟨m1, m2⟩ := mem i y hy.2
  have e' : (pullW Z L σ).φ i = fun z => ψa.φ (i PUnit.unit).1 z + ψb.φ (i PUnit.unit).2 z := funext (eq i)
  show 0 < ((Y.an σ).chart c).levi ((pullW Z L σ).φ i) y ξ
  rw [e']
  refine lt_of_lt_of_eq ?_ (AlgChart.levi_add (sa.contDiffAt_two hy.1 m1) (sb'.contDiffAt_two hy.1 m2) ξ).symm
  exact add_pos_of_pos_of_nonneg (pa _ c y ⟨hy.1, m1⟩ ξ hξ) (pb _ c y ⟨hy.1, m2⟩ ξ)

end GlobalTheory.AmpleModelPos
