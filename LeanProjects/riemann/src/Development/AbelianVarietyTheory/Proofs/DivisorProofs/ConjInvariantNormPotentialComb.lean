import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetWeightIsCInfOfPotentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetWeightIsConjOfConjNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadFnCInfAtOfSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereIntegralInvariantHomeomorphTransportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfMetWeightEqPotentialHoloStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialTransportHomeomorphStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtLinearCombinationPotentialStatement

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.CombForm

open ReadsProj in

theorem combForm : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (ι : Type) [Fintype ι] (Δ : ι → Y.Dv) (m : ∀ i σ, C.Met Y σ (Δ i)) (n : ι → ℤ) (u : M.Fun) (P : M.Pot), (∀ i (σ σ' : F →+* ℂ) (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → C.pn Y σ' (Δ i) (m i σ') (C.cx Y σ' (genAt (Δ i) (under y'))) y' = C.pn Y σ (Δ i) (m i σ) (C.cx Y σ (genAt (Δ i) (under y))) y) → M.Smooth u → (∀ a a' x x', (I.pt a' x').1 = spMap (starRingEnd ℂ) ≫ (I.pt a x).1 → u a' x' = u a x) → (∀ a, IsPotential (M.A a) (P a)) → (∀ a, ∃ Q : ι → LocPot (M.X a), (∀ i, IsPot (I.pt a) (m i _) (Q i) ∧ IsPotential (M.A a) (Q i)) ∧ ∀ j, ∀ y ∈ ((M.A a).chart j).target, ∀ w, leviAt (M.A a) (P a) j y w = ∑ i, (n i : ℝ) * leviAt (M.A a) (Q i) j y w + leviAt (M.A a) (LocPot.ofFun (u a)) j y w) → ∃ N : HermLB Y.str, ∀ (f : M.Fun) (g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), M.Smooth f → (∀ a x, g (I.ε a) (I.pt a x) = f a x) → chInt N e g = ∑ a, mInt (M.A a) (fun _ => P a) (f a) := by
  intro F _ _ C Y e M I ι _ Δ m n u P hcj hu huc hP hQ
  choose Q hQp hQl using hQ
  have hm : ∀ i σ y, PosAt (m i σ) y := by
    intro i σ y
    obtain ⟨a, rfl⟩ := I.ε.surjective σ
    obtain ⟨x, rfl⟩ := (I.pt a).surjective y
    obtain ⟨f, hf⟩ := (hQp a i).1 x
    exact (hf x ((Q a i).mem_U x)).2.1
  let H : ι → HermLB Y.str := fun i =>
    ⟨toLB (Δ i), isLB_toLB _, fun σ => metWeight (Δ i) (m i σ) (hm i σ),
      GlobalTheory.T.metWeight_isCInf_of_potential F C Y e M I (Δ i) (m i) (hm i) (fun a => Q a i) (fun a => hQp a i),
      GlobalTheory.T.metWeight_isConj_of_conj_norms F C Y (Δ i) (m i) (hm i) (hcj i)⟩
  have h2u : M.Smooth ((2 : ℝ) • u) := (InhabCalc.smSub M).smul_mem 2 hu
  let v : ∀ σ : F →+* ℂ, Pts Y σ → ℝ := readFn I ((2 : ℝ) • u)
  have hv : ∀ σ y, CInfAt (v σ) y := GlobalTheory.T.readFn_cInfAt_of_smooth F Y e M I _ h2u
  have hvc : ∀ σ σ', (Weight.ofFun (v σ)).IsConj (Weight.ofFun (v σ')) := by
    intro σ σ' _ y y' h _
    obtain ⟨a, rfl⟩ := I.ε.surjective σ
    obtain ⟨a', rfl⟩ := I.ε.surjective σ'
    obtain ⟨x, rfl⟩ := (I.pt a).surjective y
    obtain ⟨x', rfl⟩ := (I.pt a').surjective y'
    show v _ _ = v _ _
    simp only [v, readFn_apply, Pi.smul_apply, smul_eq_mul]
    rw [huc a a' x x' h]
  let L : Option ι → HermLB Y.str := fun o => o.elim (fnB v hv hvc) H
  let k : Option ι → ℤ := fun o => o.elim 1 n
  refine ⟨ArInt.comb L k, fun f g hf hg => ?_⟩
  have hw (σ : F →+* ℂ) := halfWeight_comb (σ := σ) (L := L)
    (g := fun o => o.elim (fun _ z => v σ z / 2) fun i => ((H i).φ σ).locPot.φ) (fun o => by
      cases o with
      | none => exact halfWeight_fnB _ hv hvc
      | some i => exact halfWeight_locPot _) k
  rw [chInt, finsum_eq_sum_of_fintype, ← I.ε.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := CxPts.secondCountableTopology_of_isProjOver (I.ε a) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (I.ε a) Y.isProjOver
  have hA := isAlgAtlas_tAtlas I a
  have hga : g (I.ε a) = f a ∘ (I.pt a).symm := funext fun y => by
    rw [Function.comp_apply, ← hg a ((I.pt a).symm y), Homeomorph.apply_symm_apply]
  have gcont : Continuous (g (I.ε a)) := hga ▸ (projLine_continuous_of_smooth _ (hf a)).comp (I.pt a).symm.continuous
  let TM : LocPot (M.X a) := InhabCalc.combPot (Q a) (fun i => (n i : ℝ)) (u a)
  have hTM : IsPotential (M.A a) TM := InhabCalc.isPotential_combPot _ _ (fun i => (hQp a i).2) _ _ (hu a)
  let T : LocPot (Pts Y (I.ε a)) := TM.pullback (I.pt a).symm (I.pt a).symm.continuous
  have hT : IsPotential (tAtlas (M.A a) (I.pt a)) T := GlobalTheory.T.isPotential_transport_homeomorph _ _ _ _ _ _ hTM
  have hsf : SameForm (tAtlas (M.A a) (I.pt a)) ((ArInt.comb L k).φ (I.ε a)).locPot T := by
    refine Weight.sameForm_of_re (R := hA.anRead) _ hA hT fun x => ?_
    obtain ⟨i0, hi0, he⟩ := hw (I.ε a) x
    have h6 := fun i => GlobalTheory.T.half_metWeight_eq_potential_holo F C Y (I.ε a) e _ hA (Δ i) (m i (I.ε a)) (hm i (I.ε a)) _ (IsPot.pullback_symm (hQp a i).1) x
      (pick ((H i).φ (I.ε a)).isLB x) (mem_pick _ x)
    choose W hW hxW G hG hGe using h6
    refine ⟨i0, hi0, ⋂ i, W i, isOpen_iInter_of_finite hW, Set.mem_iInter.2 hxW, fun z => ∑ i, (n i : ℂ) * G i z,
      (hA.holoOn_iff hA.anRead (isOpen_iInter_of_finite hW)).1 ?_, fun z hz => ?_⟩
    · intro j t ht
      exact Finset.analyticAt_fun_sum _ fun i _ =>
        analyticAt_const.mul (hG i j t ⟨ht.1, Set.mem_iInter.1 ht.2 i⟩)
    · have e1 : ∀ i, ((H i).φ (I.ε a)).locPot.φ x z =
          (Q a i).φ ((I.pt a).symm x) ((I.pt a).symm z) + (G i z).re := fun i => hGe i z (Set.mem_iInter.1 hz i)
      have e2 : v (I.ε a) z / 2 = u a ((I.pt a).symm z) := by
        simp only [v, readFn_apply', Pi.smul_apply, smul_eq_mul]; ring
      have e3 : T.φ x z = ∑ i, (n i : ℝ) * (Q a i).φ ((I.pt a).symm x) ((I.pt a).symm z) + u a ((I.pt a).symm z) := rfl
      have e4 : ∀ i, ((n i : ℂ) * G i z).re = (n i : ℝ) * (G i z).re := fun i => by simp
      rw [he z]
      simp only [Fintype.sum_option, k, Option.elim, Int.cast_one, one_mul, e1, e2, e3, Complex.re_sum, e4, mul_add,
        Finset.sum_add_distrib]
      ring
  have hs := ChernMA.chernInt_eq_mInt ((ArInt.comb L k).cInf (I.ε a)) hA gcont
  rw [hs, SameForm.mInt_eq (fun _ => hsf), GlobalTheory.T.mongeAmpereIntegral_invariant_homeomorph_transport _ _ _ _ _ _ _ (fun _ => hT) gcont, show g (I.ε a) ∘ I.pt a = f a from funext (hg a)]
  rw [InhabCalc.mInt_congr_φ (M.A a) (Ψ := fun _ => TM) (fun _ => ?_)]
  · refine (LeviOnly.mInt_eq_of_leviEq e _ (M.A a) _ _ _ (fun _ => hTM) (fun _ => hP a) fun _ j y hy w => ?_).1
    rw [GlobalTheory.T.leviAt_linear_combination_potential _ _ _ _ _ _ _ (fun i => (hQp a i).2) (hu a) j y hy w, hQl a j y hy w]
  · funext x z
    simp [T, LocPot.pullback]

end GlobalTheory.Mean4O.CombForm
