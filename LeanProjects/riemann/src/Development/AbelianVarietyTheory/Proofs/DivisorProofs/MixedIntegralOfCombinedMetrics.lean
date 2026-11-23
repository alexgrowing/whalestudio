import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassPotential
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetWeightIsCInfOfPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfMetWeightEqPotentialHolo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereIntegralInvariantHomeomorphTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialTransportHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CombChern

section Bundle

variable {X : Scheme.{0}} [IsIntegral X]

theorem presents_zpow {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) (n : ℤ) :
    Presents (n • D) (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n) fun j => r (j PUnit.unit) ^ n := by
  have mem : ∀ (j : PUnit → L.ι) {x : X}, x ∈ (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j →
      x ∈ L.U (j PUnit.unit) := fun j x hx => by simpa using Set.mem_iInter.1 hx PUnit.unit
  refine ⟨LB.isLB_linComb h.isLB _ _, fun j j' hjj => ?_, fun j x hx => (h.isEqn _ x (mem j hx)).zsmul n⟩
  have l : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j ⊓
      (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j' ≤ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) :=
    fun x hx => ⟨mem j hx.1, mem j' hx.2⟩
  have hg : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).g j j' = res l (L.g (j PUnit.unit) (j' PUnit.unit)) ^ n := by
    change ∏ _k : PUnit, _ = _
    exact Fintype.prod_unique _
  have key : ∀ {U : X.Opens} (hU : genericPoint X ∈ U) (u : Γ(X, U)ˣ) (m : ℤ),
      fnOf U hU ((u ^ m : Γ(X, U)ˣ) : Γ(X, U)) = fnOf U hU (u : Γ(X, U)) ^ m := fun hU u m => by
    have e := congrArg Units.val (map_zpow (Units.map (fnOf _ hU).toMonoidHom) u m)
    rw [Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map] at e
    exact e
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, h.isRatSec _ _ (l hjj), mul_zpow, hg, key]
  congr 2
  exact (fnOf_resG l hjj _).symm

end Bundle

section Comb

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} (T : ι → LB X) (b : ι → ℤ)

noncomputable def cBun : List ι → LB X
  | [] => LB.triv X
  | i :: l => CechPic.tens (LB.LinComb (T i) (K := PUnit) (fun _ => 𝟙 X) fun _ => b i) (cBun l)

noncomputable def cEq (r : ∀ i, (T i).ι → X.functionFieldˣ) : ∀ l, (cBun T b l).ι → X.functionFieldˣ
  | [] => fun _ => 1
  | i :: l => fun q => r i (q.1 PUnit.unit) ^ b i * cEq r l q.2

theorem presents_cBun {D : ι → CartierDiv X} {r : ∀ i, (T i).ι → X.functionFieldˣ}
    (hr : ∀ i, Presents (D i) (T i) (r i)) :
    ∀ l, Presents ((l.map fun i => b i • D i).sum) (cBun T b l) (cEq T b r l)
  | [] => presents_zero
  | i :: l => by
    rw [List.map_cons, List.sum_cons]
    exact (presents_zpow (hr i) (b i)).tens (presents_cBun hr l)

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ}

noncomputable def cWt (ψ : ∀ i, Weight p σ (T i)) : ∀ l, Weight p σ (cBun T b l)
  | [] => Weight.ofFun 0
  | i :: l => ((ψ i).zpow (b i)).tens (cWt ψ l)

theorem isCInf_cWt {ψ : ∀ i, Weight p σ (T i)} (h : ∀ i, (ψ i).IsCInf) : ∀ l, (cWt T b ψ l).IsCInf
  | [] => Weight.isCInf_ofFun fun y => cInfAt_const 0 y
  | i :: l => ((h i).zpow (b i)).tens (isCInf_cWt h l)

noncomputable def cIdx (ψ : ∀ i, Weight p σ (T i)) (x : CxPts p σ) : ∀ l, (cBun T b l).ι
  | [] => PUnit.unit
  | i :: l => (fun _ => pick (ψ i).isLB x, cIdx ψ x l)

theorem mem_cIdx (ψ : ∀ i, Weight p σ (T i)) (x : CxPts p σ) :
    ∀ l, x ∈ ptsIn p σ ((cBun T b l).U (cIdx T b ψ x l))
  | [] => mem_ptsIn_top
  | i :: l => mem_ptsIn_inf.2 ⟨mem_pow_iff.2 (mem_pick (ψ i).isLB x), mem_cIdx ψ x l⟩

theorem cWt_φ (ψ : ∀ i, Weight p σ (T i)) (x z : CxPts p σ) :
    ∀ l, (cWt T b ψ l).φ (cIdx T b ψ x l) z = (l.map fun i => (b i : ℝ) * (ψ i).φ (pick (ψ i).isLB x) z).sum
  | [] => rfl
  | i :: l => by
    rw [List.map_cons, List.sum_cons, ← cWt_φ ψ x z l]
    exact congrArg (· + _) ((ψ i).zpow_φ (b i) _ z)

end Comb

section Met

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

theorem metWeight_isCInf_at {e : ℕ} {M : Man e} (I : ManIs M Y) (a : Fin (M.n + 1)) {Δ : Y.Dv}
    {m : C.Met Y (I.ε a) Δ} (hm : ∀ y, PosAt m y) {Q : LocPot (M.X a)}
    (hQ : IsPot (I.pt a) m Q ∧ IsPotential (M.A a) Q) : (metWeight Δ m hm).IsCInf := by
  intro c y hy
  obtain ⟨x, rfl⟩ := (I.pt a).surjective y
  have hxU : (I.pt a).symm (I.pt a x) ∈ Q.U x := by simpa using Q.mem_U x
  obtain ⟨f, hf⟩ := hQ.1 x
  have key : ∀ z : Pts Y (I.ε a), (I.pt a).symm z ∈ Q.U x → z ∈ ptsIn Y.str (I.ε a) ((toLB Δ).U c) →
      UnitAt (under z) (f * (c.1.2 : Y.Fn)) ∧ (metWeight Δ m hm).φ c z =
        2 * Q.φ x ((I.pt a).symm z) + Real.log (‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2) := by
    intro z hz hzc
    have hzc' : under z ∈ c.1.1 := mem_ptsIn.1 hzc
    obtain ⟨h₁, h₂, h₃⟩ := hf _ hz
    rw [Homeomorph.apply_symm_apply] at h₁ h₂ h₃
    have he : Δ.IsEqn (under z) c.1.2 := c.2.2 _ hzc'
    have hu := he.generatesAt_iff.1 h₁
    have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 he
    have hp := pn_pos_of_generatesAt (C := C) hgen (hm z)
    have hr : 0 < ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2 := pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2
    have e₁ : (f * (c.1.2 : Y.Fn)) * (c.1.2 : Y.Fn)⁻¹ = f := by
      rw [mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
    have e₂ := C.pn_mul Y _ Δ m _ _ z hu.regAt hgen.regularAt
    rw [e₁] at e₂
    refine ⟨hu, ?_⟩
    rw [metWeight_φ, h₃, lnN, e₂, Real.log_mul hr.ne' hp.ne']
    ring
  have hS : IsOpen ((I.pt a).symm ⁻¹' Q.U x) := (Q.isOpen_U x).preimage (I.pt a).symm.continuous
  refine (((MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.cInfAt_of_smoothOn_tAtlas (isAlgAtlas_tAtlas I a) (Q.isOpen_U x)
    (hQ.2.1 x) hxU).const_mul 2).add
    (MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.cInfAt_log_normSq_ratVal (key _ hxU hy).1)).congr ?_
  filter_upwards [hS.mem_nhds hxU, (isOpen_ptsIn _).mem_nhds hy] with z hz hzc
  exact (key z hz hzc).2

end Met

theorem mInt_combPot_eq_inter : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] [NumberField F] (Y : GlobalTheory.ProjVar.Var F)
    (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (ι : Type) [Fintype ι] (Δ : ι → Y.Dv)
    (m : ∀ i (σ : F →+* ℂ), (cxSt F).Met Y σ (Δ i)) (b : ι → ℤ) (Q : ι → LocPot (M.X a)), Y.dim = e →
    (∀ i σ, (cxSt F).mSmooth Y σ (Δ i) (m i σ)) →
    (∀ i, IsPot (I.pt a) (m i (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i)) →
    mInt (M.A a) (fun _ => InhabCalc.combPot Q (fun i => (b i : ℝ)) (fun _ => 0)) (fun _ => 1) =
      (Y.inter (fun _ => ∑ i, b i • Δ i) : ℝ) := by
  intro hCD F _ _ Y e M I a ι _ Δ m b Q hdim _ hQ
  subst hdim
  have hm : ∀ i y, PosAt (m i (I.ε a)) y := by
    intro i y
    obtain ⟨x, rfl⟩ := (I.pt a).surjective y
    obtain ⟨f, hf⟩ := (hQ i).1 x
    exact (hf x ((Q i).mem_U x)).2.1
  let ψ : ∀ i, Weight Y.str (I.ε a) (toLB (Δ i)) := fun i => metWeight (Δ i) (m i (I.ε a)) (hm i)
  have hψ : ∀ i, (ψ i).IsCInf := fun i => metWeight_isCInf_at I a (hm i) (hQ i)
  let l := (Finset.univ : Finset ι).toList
  have hp := presents_cBun (fun i => toLB (Δ i)) b (fun i => presents_toLB (Δ i)) l
  have hD : (l.map fun i => b i • Δ i).sum = ∑ i, b i • Δ i := Finset.sum_map_toList _ _
  rw [hD] at hp
  let φ := cWt (fun i => toLB (Δ i)) b ψ l
  have hφ : φ.IsCInf := isCInf_cWt _ b hψ l
  obtain ⟨-, hc⟩ := hCD F Y (I.ε a) _ _ _ hp φ hφ
  have := CxPts.secondCountableTopology_of_isProjOver (I.ε a) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (I.ε a) Y.isProjOver
  have hA := isAlgAtlas_tAtlas I a
  rw [← hc, ChernMA.chernInt_eq_mInt hφ hA continuous_const]
  let TM : LocPot (M.X a) := InhabCalc.combPot Q (fun i => (b i : ℝ)) (fun _ => 0)
  have hTM : IsPotential (M.A a) TM :=
    InhabCalc.isPotential_combPot _ _ (fun i => (hQ i).2) _ _ (fun _ => contDiffOn_const)
  let T : LocPot (Pts Y (I.ε a)) := TM.pullback (I.pt a).symm (I.pt a).symm.continuous
  have hT : IsPotential (tAtlas (M.A a) (I.pt a)) T :=
    PotentialityTransport.GlobalTheory.CompanionTheory.CarriedPot.isPotential_tAtlas_pullback _ _ _ _ _ _ hTM
  have hsf : SameForm (tAtlas (M.A a) (I.pt a)) φ.locPot T := by
    refine Weight.sameForm_of_re (R := hA.anRead) _ hA hT fun x => ?_
    have h6 := fun i => HalfMetricWeight.GlobalTheory.CompanionTheory.Dblock.HalfWeight.half_metWeight_eq F (cxSt F) Y (I.ε a) _ _ hA (Δ i)
      (m i (I.ε a)) (hm i) _ (IsPot.pullback_symm (hQ i).1) x (pick (ψ i).isLB x) (mem_pick _ x)
    choose W hW hxW G hG hGe using h6
    refine ⟨cIdx _ b ψ x l, mem_cIdx _ b ψ x l, ⋂ i, W i, isOpen_iInter_of_finite hW, Set.mem_iInter.2 hxW,
      fun z => ∑ i, (b i : ℂ) * G i z, (hA.holoOn_iff hA.anRead (isOpen_iInter_of_finite hW)).1 ?_, fun z hz => ?_⟩
    · intro j t ht
      exact Finset.analyticAt_fun_sum _ fun i _ =>
        analyticAt_const.mul (hG i j t ⟨ht.1, Set.mem_iInter.1 ht.2 i⟩)
    · have e1 : ∀ i, (ψ i).φ (pick (ψ i).isLB x) z =
          2 * ((Q i).φ ((I.pt a).symm x) ((I.pt a).symm z) + (G i z).re) := fun i => by
        have := hGe i z (Set.mem_iInter.1 hz i)
        simp only [LocPot.pullback] at this
        linarith
      have e3 : T.φ x z = ∑ i, (b i : ℝ) * (Q i).φ ((I.pt a).symm x) ((I.pt a).symm z) + 0 := rfl
      have e4 : ∀ i, ((b i : ℂ) * G i z).re = (b i : ℝ) * (G i z).re := fun i => by simp
      rw [cWt_φ, Finset.sum_map_toList, e3, Complex.re_sum]
      simp only [e1, e4]
      rw [Finset.sum_div, add_zero, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  rw [SameForm.mInt_eq (fun _ => hsf), MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas _ _ _ _ _ _ _ (fun _ => hT)
    continuous_const]
  refine InhabCalc.mInt_congr_φ (M.A a) (fun _ => ?_) _
  funext x z
  simp [T, TM, LocPot.pullback]

end GlobalTheory.CombChern
