import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeesawSmall

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.MixModel

variable {D : D7}

def decNN (A B : HSp D) : OrthDec (GlobalTheory.Doubling.hsum A B) A (negSp (negSp B)) where
  iA := (GlobalTheory.BiTransfer.sumDec A B).iA
  iB := (GlobalTheory.BiTransfer.sumDec A B).iB
  isoA := (GlobalTheory.BiTransfer.sumDec A B).isoA
  isoB := by
    rw [negSp_gram, negSp_gram, neg_neg]
    exact (GlobalTheory.BiTransfer.sumDec A B).isoB
  orth := (GlobalTheory.BiTransfer.sumDec A B).orth
  rank_add := (GlobalTheory.BiTransfer.sumDec A B).rank_add

theorem pB_decNN (A B : HSp D) : (decNN A B).pB = (GlobalTheory.BiTransfer.sumDec A B).pB := by
  simp only [OrthDec.pB, OrthDec.qB, negSp_gram, neg_neg]
  rfl

theorem boxT_decNN (S A B : HSp D) (φ : WO S A → ℂ) (φ' : WO S B → ℂ) :
    (decNN A B).boxT S φ φ' = box2 φ φ' := by
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
  funext x
  simp only [OrthDec.boxT, OrthDec.resT_apply, pB_decNN]
  rfl

theorem emb_decNN (A B : HSp D) (g : GA D A) (g₁ : GA D B) :
    (decNN A B).emb (g, negGA _ (negGA B g₁)) = GlobalTheory.SquareComm.blk A B (g, g₁) := by
  rw [← GlobalTheory.SeesawSumTarget.emb_sumDec]
  apply mt_injective
  rw [OrthDec.mt_emb, OrthDec.mt_emb, pB_decNN]
  rfl

section Chars

variable {C : Type*} [CommGroup C]

theorem attChr_inv_mul (μ η : C) (n : ℕ) :
    (Formalism.IndefR.Lift.attChr μ η n)⁻¹ * (μ * η ^ (n % 2)) = η ^ (2 * (n % 2)) := by
  unfold Formalism.IndefR.Lift.attChr
  rcases Nat.even_or_odd n with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]
    simp
  · rw [if_pos h, Nat.odd_iff.1 h, pow_one, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
      show 2 * 1 = 2 from rfl, pow_two]

theorem attChr_mul (μ χ η : C) (n : ℕ) :
    Formalism.IndefR.Lift.attChr χ η n * (μ * η ^ (n % 2)) = μ * χ := by
  unfold Formalism.IndefR.Lift.attChr
  rcases Nat.even_or_odd n with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]
    simp [mul_comm]
  · rw [if_pos h, Nat.odd_iff.1 h, pow_one, mul_comm μ η, ← mul_assoc, mul_assoc χ, inv_mul_cancel, mul_one, mul_comm]

theorem attChr_div (μ χ η : C) {a b : ℕ} (hab : Odd a ↔ Odd b) (k : ℕ) :
    Formalism.IndefR.Lift.attChr μ η a * (Formalism.IndefR.Lift.attChr χ η b)⁻¹ = μ * η ^ k / (χ * η ^ k) := by
  unfold Formalism.IndefR.Lift.attChr
  rw [mul_div_mul_right_eq_div]
  by_cases h : Odd a
  · rw [if_pos h, if_pos (hab.1 h), _root_.mul_inv_rev, inv_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc η⁻¹, inv_mul_cancel,
      one_mul]
  · rw [if_neg h, if_neg (fun h' => h (hab.2 h')), div_eq_mul_inv]

end Chars

end GlobalTheory.SeesawSmall

namespace GlobalTheory.SeesawSmall

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

variable {D : D7}

def adjFn (S B : HSp D) (f : WO (negSp B) S → ℂ) : WO S B → ℂ := fun y => f (dagger S (negSp B) y)

theorem trivOnF_of_resEta {χ χ' : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (h' : ResEta D χ' n) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.TrivOnF D (χ⁻¹ * χ') := by
  obtain ⟨η, hη⟩ := h.1
  intro a
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, h.2 η hη a, h'.2 η hη a, inv_mul_cancel]

theorem trivOnF_one : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.TrivOnF D 1 := fun _ => rfl

theorem tildeDet_one {V : HSp D} {g : GA D V} {a : Circle} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.IsTildeDet V 1 g a) : a = 1 := by
  obtain ⟨x, hx⟩ := h.1
  rw [← h.2 x hx]
  rfl

theorem dagger_zero (S T : HSp D) : dagger S T 0 = 0 := by
  have e : adj (0 : WO S T) = 0 := by ext a b; simp [adj]
  simp only [dagger, e, Matrix.zero_mul, Matrix.mul_zero]

theorem dag_eq_cj (S T : HSp D) (f : WO S T → ℂ) : GlobalTheory.PairLift.dag S T f = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f := by
  funext y
  simp only [GlobalTheory.PairLift.dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.PairLift.adjO, dagger, giA, gA, adj, rat, Matrix.mul_assoc]

end GlobalTheory.SeesawSmall

namespace GlobalTheory.SeesawSmall

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem seesaw_small {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) {i j : ℕ} (hi : i + 1 ≤ D.R.m) (hj : j + 1 ≤ D.R.m)
    (ω : GA D (spW₁ G i j) × GA D (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) →*
      Module.End ℂ (WO (spW₁ G i j) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) → ℂ))
    (hω : IsWeilDatumO W.ψ (spW₁ G i j) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) (alpha G t i j)
      (alpha G t i j / beta G i j) ω)
    (f₁ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ) (f₂ : WO (G.pS (.chi i j)) (G.pT (.chi i j)) → ℂ)
    (hf₁ : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) f₁)
    (hf₂ : IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) f₂) :
    IsThetaFunO W.ψ (spW₁ G i j) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j))
        (box2 f₁ (adjFn (spW₁ G i j) (spV₁ G i j) f₂)) ∧
      ∀ (g : GA D (spV G i j)) (u : GA D (spW₁ G i j)) (g₁ : GA D (spV₁ G i j)),
        W.kerA (.down t i j) f₁ g u * W.kerA (.right i j) f₂ u g₁ =
          xiV G i j g * xiV₁ G t i j g₁ *
            thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (box2 f₁ (adjFn (spW₁ G i j) (spV₁ G i j) f₂)) := by
  have hψ := W.ψ_std
  have rg : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (GlobalTheory.FunObj.node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hpar : Odd (spV G i j).rank ↔ Odd (spV₁ G i j).rank := by
    rw [spV, spV₁, rg i (j + 1) (by omega) hj, rg (i + 1) j hi (by omega)]
    unfold rankV
    rw [show D.R.r + (j + 1) * D.R.t + i * sLen D = (D.R.r + j * D.R.t + i * sLen D) + D.R.t by ring,
      show D.R.r + j * D.R.t + (i + 1) * sLen D = (D.R.r + j * D.R.t + i * sLen D) + sLen D by ring]
    have key : ∀ X a b : ℕ, Odd a → Odd b → (Odd (X + a) ↔ Odd (X + b)) := by
      intro X a b ha hb
      rw [Nat.odd_add, Nat.odd_add]
      simp only [Nat.not_even_iff_odd.2 ha, Nat.not_even_iff_odd.2 hb]
    exact key _ _ _ D.R.t_odd (odd_sLen D)
  have H₁ := W.om_is (.mu t i j) ⟨by omega, hj⟩
  have H₂ := W.om_is (.chi i j) ⟨hi, by omega⟩
  have H₂a := GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D W.ψ _ _ _ _ (W.om (.chi i j)) H₂
  have H₂b := (GlobalTheory.ConjWeil.conj_isWeilDatumO D W.ψ _ _ _ _ _ H₂a).1
  have hB : G.chrT (.mu t i j) * (G.chrS (.chi i j))⁻¹ = alpha G t i j / beta G i j :=
    attChr_div _ _ _ hpar _
  have hω' : IsWeilDatumO W.ψ (spW₁ G i j) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) (alpha G t i j)
      (G.chrT (.mu t i j) * (G.chrS (.chi i j))⁻¹) ω := by rw [hB]; exact hω
  obtain ⟨ωA, HA⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D W.ψ hψ (spW₁ G i j) (spV G i j) (alpha G t i j)
    (G.chrT (.mu t i j)) (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecS H₁.hecT hω.resS H₁.resT
  obtain ⟨ωB, HB⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D W.ψ hψ (spW₁ G i j) (negSp (negSp (spV₁ G i j)))
    (alpha G t i j) (G.chrS (.chi i j))⁻¹ (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecS H₂b.hecT hω.resS
    H₂b.resT

  set A1 := G.chrS (.mu t i j) with hA1
  set B1 := G.chrT (.mu t i j) with hB1
  set A2 := (G.chrT (.chi i j))⁻¹ with hA2
  set B2 := (G.chrS (.chi i j))⁻¹ with hB2
  set α := alpha G t i j with hα
  have hξ₁ : A1⁻¹ * α = L.eta ^ (2 * eps G i j) := attChr_inv_mul _ _ _
  have hξ₂ : A2⁻¹ * α = L.mu t (j + 1) * G.ch.chi (D.R.m - i) := by
    rw [hA2, inv_inv]
    exact attChr_mul _ _ _ _
  have tr₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.TrivOnF D (A1⁻¹ * α) := trivOnF_of_resEta H₁.resS hω.resS
  have tr₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.TrivOnF D (A2⁻¹ * α) := trivOnF_of_resEta H₂b.resS hω.resS
  have HA' : IsWeilDatumO W.ψ (spW₁ G i j) (spV G i j) (A1 * (A1⁻¹ * α)) (B1 * 1) ωA := by
    rwa [mul_inv_cancel_left, mul_one]
  have HB' : IsWeilDatumO W.ψ (spW₁ G i j) (negSp (negSp (spV₁ G i j))) (A2 * (A2⁻¹ * α)) (B2 * 1) ωB := by
    rwa [mul_inv_cancel_left, mul_one]

  set F₂ : WO (spW₁ G i j) (negSp (negSp (spV₁ G i j))) → ℂ :=
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger (spW₁ G i j) (negSp (spV₁ G i j))) f₂) with hF₂def
  have hF₂adj : F₂ = adjFn (spW₁ G i j) (spV₁ G i j) f₂ := by
    funext y
    simp only [hF₂def, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, Complex.conj_conj, adjFn]
  have hF₂ : IsThetaFunO W.ψ (spW₁ G i j) (negSp (negSp (spV₁ G i j))) F₂ := by
    have h1 := (GlobalTheory.AdjLawPf.adjLaw D W.ψ hψ (negSp (spV₁ G i j)) (spW₁ G i j)).theta f₂ hf₂
    rw [dag_eq_cj] at h1
    exact ((GlobalTheory.CjNeg.theta_heis_neg D W.ψ hψ (spW₁ G i j) (negSp (spV₁ G i j))).1 _).1.2 h1
  have TT := GlobalTheory.TensorTargetRule.tensorTarget D W.ψ hψ _ _ _ (decNN (spV G i j) (spV₁ G i j)) (spW₁ G i j)
  refine ⟨?_, fun g u g₁ => ?_⟩
  · rw [← hF₂adj, ← boxT_decNN]
    exact TT.box_theta f₁ F₂ hf₁ hF₂

  obtain ⟨a₁, b₁, ha₁, hb₁, e₁⟩ := GlobalTheory.WeilDetermined.weilDatumTwist D W.ψ _ _ A1 B1 (A1⁻¹ * α) 1
    (W.om (.mu t i j)) ωA tr₁ trivOnF_one H₁ HA' u g
  obtain ⟨a₂, b₂, ha₂, hb₂, e₂⟩ := GlobalTheory.WeilDetermined.weilDatumTwist D W.ψ _ _ A2 B2 (A2⁻¹ * α) 1
    (conjTarget (conjAdjoint (W.om (.chi i j)))) ωB tr₂ trivOnF_one H₂b HB' u (negGA _ (negGA _ g₁))
  rw [tildeDet_one ha₁] at e₁
  rw [tildeDet_one ha₂] at e₂
  have key := congrFun (TT.om_box α B1 B2 ω ωA ωB hω' HA HB u g (negGA _ (negGA _ g₁)) f₁ F₂ hf₁ hF₂) 0
  rw [OrthDec.boxT_zero, e₁ f₁ hf₁, e₂ F₂ hF₂, emb_decNN, boxT_decNN] at key
  have k₂ : conjTarget (conjAdjoint (W.om (.chi i j))) (u, negGA _ (negGA _ g₁)) F₂ 0 = W.kerA (.right i j) f₂ u g₁ := by
    rw [GlobalTheory.ConjWeil.conjTarget_apply, MulEquiv.symm_apply_apply, hF₂def, GlobalTheory.ConjWeil.cj_id_cj_id]
    show GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (cjEnd (daggerEquiv _ _) (W.om (.chi i j) (negGA _ g₁, u))
      (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (daggerEquiv _ _) f₂)) 0 = _
    rw [cjEnd_cj]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, Complex.conj_conj]
    show W.om (.chi i j) (negGA _ g₁, u) f₂ (dagger _ _ 0) = W.om (.chi i j) (negGA _ g₁, u) f₂ 0
    rw [dagger_zero]
  have k₁ : W.om (.mu t i j) (u, g) f₁ 0 = W.kerA (.down t i j) f₁ g u := rfl
  have x1 : xiV G i j g = ((b₁ : ℂ))⁻¹ := by
    unfold xiV flatDet
    rw [← hξ₁, MonoidHom.inv_apply, hb₁.2 _ (GlobalTheory.RecDict.exists_isDetRoot D (spV G i j) g).choose_spec, Circle.coe_inv]
  have x2 : xiV₁ G t i j g₁ = ((b₂ : ℂ))⁻¹ := by
    unfold xiV₁ flatDet
    rw [← hξ₂, MonoidHom.inv_apply, hb₂.2 _ (GlobalTheory.RecDict.exists_isDetRoot D (spV₁ G i j) g₁).choose_spec, Circle.coe_inv]
  have n1 : (b₁ : ℂ) ≠ 0 := Circle.coe_ne_zero b₁
  have n2 : (b₂ : ℂ) ≠ 0 := Circle.coe_ne_zero b₂
  rw [x1, x2, ← hF₂adj]
  unfold thetaKO
  rw [key, Pi.smul_apply, Pi.smul_apply, k₂, k₁, smul_eq_mul, smul_eq_mul, inv_one, one_mul, one_mul]
  field_simp

end GlobalTheory.SeesawSmall

namespace GlobalTheory.SeesawSmall

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

def toOr (e : Num G i j) (x : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    WO (spW₁ G i j) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) :=
  HMul.hMul (x.submatrix id fun k => e (finSumFinEquiv.symm k))ᵀ ((spW₁ G i j).gram.map (incA D))

theorem topR_toOr (e : Num G i j) (x : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    topR (A := spV G i j) (B := spV₁ G i j) (toOr e x) = mulG (spW₁ G i j) (colV e x)ᵀ := by
  ext a b
  simp [topR, toOr, mulG, colV, Matrix.mul_apply, incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]

theorem botR_toOr (e : Num G i j) (x : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    botR (A := spV G i j) (B := spV₁ G i j) (toOr e x) =
      HMul.hMul (x.submatrix id fun k => e (.inr k))ᵀ ((spW₁ G i j).gram.map (incA D)) := by
  ext a b
  simp [botR, toOr, Matrix.mul_apply]

theorem dagger_botR_toOr (e : Num G i j)
    (x : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    dagger (spW₁ G i j) (negSp (spV₁ G i j)) (botR (A := spV G i j) (B := spV₁ G i j) (toOr e x)) = adjV₁ e x := by
  rw [botR_toOr]
  set y := x.submatrix id fun k => e (.inr k)
  have h1 : adj (HMul.hMul yᵀ ((spW₁ G i j).gram.map (incA D)) : WO (spW₁ G i j) (negSp (spV₁ G i j))) =
      HMul.hMul ((spW₁ G i j).gram.map (incA D)) (y.map (cA D)) := by
    unfold adj
    rw [Matrix.map_mul, transpose_mul, GlobalTheory.RouteCoords.gram_conj_transpose, transpose_map, transpose_transpose]
  unfold dagger
  rw [h1, gA, giA, rat, rat, negSp_gram, Matrix.map_neg _ (map_neg _)]
  have h2 := GlobalTheory.RouteCoords.inv_mul_gram (spW₁ G i j)
  calc _ = HMul.hMul (HMul.hMul (HMul.hMul ((spW₁ G i j).gram⁻¹.map (incA D)) ((spW₁ G i j).gram.map (incA D)))
        (y.map (cA D))) (-(spV₁ G i j).gram.map (incA D)) := by simp only [Matrix.mul_assoc]
    _ = adjV₁ e x := by
      rw [h2, Matrix.one_mul, adjV₁, mulG, Matrix.mul_neg]
      rfl

theorem thetaSquareProductRouteB_eq_externalProduct {t : T} (e : Num G i j) (d : GlobalTheory.FunObj.PureT G (routeB t i j))
    (x : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    boxB e d x = box2 (d.1.2 : GlobalTheory.FunObj.Sch G (.down t i j))
      (adjFn (spW₁ G i j) (spV₁ G i j) (d.2 : GlobalTheory.FunObj.Sch G (.right i j))) (toOr e x) := by
  unfold boxB box2 adjFn
  rw [topR_toOr, dagger_botR_toOr]

end GlobalTheory.SeesawSmall
