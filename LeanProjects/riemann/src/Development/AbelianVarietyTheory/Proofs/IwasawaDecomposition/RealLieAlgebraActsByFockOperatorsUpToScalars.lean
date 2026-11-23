import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulNonsingInvCancelRightGram

noncomputable section

namespace GlobalTheory.LieFock

section Abstract

open Formalism.IndefR.Datum in

theorem exists_lift_on {ι X : Type} [DecidableEq ι] (M : Submodule ℂ (X → ℂ)) (A : ι → (X → ℂ) → (X → ℂ))
    (a b : ι → Module.End ℂ M) (hA : ∀ i (g : M), A i g = a i g) (haa : ∀ i j, a i * a j = a j * a i)
    (hba : ∀ i j, b i * a j = a j * b i + (if i = j then (1 : ℂ) else 0) • 1) (f : M) (S : Set ι)
    (hf : ∀ i ∈ S, b i f = 0) :
    ∃ E : MvPolynomial ι ℂ →ₗ[ℂ] M, (∀ Q, pureTensorL A (f : X → ℂ) Q = E Q) ∧
      (∀ v Q, E (MvPolynomial.X v * Q) = a v (E Q)) ∧ ∀ v ∈ S, ∀ Q, E (MvPolynomial.pderiv v Q) = b v (E Q) := by
  have h1 : ∀ i g, g ∈ M → A i g ∈ M := fun i g hg => by rw [hA i ⟨g, hg⟩]; exact Subtype.prop _
  have hm := GlobalTheory.FockIndep.pure_mem (P := (· ∈ M)) (fun _ _ => add_mem) (fun c _ => M.smul_mem c) h1 f.2
  have hX := GlobalTheory.FockIndep.pure_X_mul (P := (· ∈ M)) (fun _ _ => add_mem) (fun c _ => M.smul_mem c) h1
    (fun i j g hg => by
      rw [hA j ⟨g, hg⟩, hA i ⟨g, hg⟩, hA, hA]
      exact congrArg Subtype.val (LinearMap.congr_fun (haa i j) ⟨g, hg⟩))
    (fun i g g' hg hg' => by
      rw [hA i ⟨g, hg⟩, hA i ⟨g', hg'⟩, ← Submodule.coe_add, ← map_add, ← hA]; rfl)
    (fun i c g hg => by rw [hA i ⟨g, hg⟩, ← Submodule.coe_smul, ← map_smul, ← hA]; rfl) f.2
  let E : MvPolynomial ι ℂ →ₗ[ℂ] M := (pureTensorL A (f : X → ℂ)).codRestrict M hm
  have hE : ∀ v Q, E (MvPolynomial.X v * Q) = a v (E Q) := fun v Q => Subtype.ext ((hX Q v).trans (hA v (E Q)))
  have h0 : E 1 = f := Subtype.ext (GlobalTheory.FockIndep.pure_one _)
  refine ⟨E, fun _ => rfl, hE, fun i hi Q => Eq.symm ?_⟩
  clear_value E
  induction Q using MvPolynomial.induction_on with
  | C r => rw [MvPolynomial.pderiv_C, map_zero, MvPolynomial.C_eq_smul_one, map_smul, map_smul, h0, hf i hi, smul_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    rw [mul_comm, hE, ← Module.End.mul_apply, hba, LinearMap.add_apply, Module.End.mul_apply, hp,
      MvPolynomial.pderiv_mul, map_add, hE, add_comm]
    congr 1
    split_ifs with h
    · rw [h, MvPolynomial.pderiv_X_self, one_mul, one_smul, Module.End.one_apply]
    · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm h), zero_mul, map_zero, zero_smul, LinearMap.zero_apply]

end Abstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators Complex
open scoped Classical Real ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V W : HSp D} (A : Fr V) (B : Fr W)

variable {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D}

theorem exists_raise_lower_at (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau) :
    ∃ (R L : Fin W.rank → Fin V.rank → Module.End ℂ (thetaSub ψ V W))
      (w : Ix V W → Ix V W → Module.End ℂ (thetaSub ψ V W)),
      (∀ f, IsThetaFunO ψ V W f → IsFockVacAt (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) f → ∃ E : PolF D W.rank V.rank →ₗ[ℂ] thetaSub ψ V W, (∀ P, ptF ψ θ A B f P = E P) ∧
        (∀ i j P, E (raiO τ (A.ε τ) (B.ε τ) i j P) = R i j (E P)) ∧
        ∀ i j P, E (lowO τ (A.ε τ) (B.ε τ) i j P) = L i j (E P)) ∧
      (∀ i j l k, w ((i, j), τ) ((l, k), τ) = (sgn (A.ε τ j) * sgn (A.ε τ k)) • (R i j * L l k)) ∧
      ∀ X X' : Matrix (Ix V W) (Ix V W) ℂ, X * uM A B = uM A B * X' → ∀ g : thetaSub ψ V W,
        ((nOp (rhoV hψ σ V W) (HM V W) X (toB hψ g.1 g.2)).1 : WO V W → ℂ) = ((∑ k, ∑ l, X' k l • w k l) g).1 := by
  let J : thetaSub ψ V W →ₗ[ℂ] BB ψ V W :=
    { toFun := fun f => toB hψ f.1 f.2
      map_add' := fun f g => QB_ext fun x => rfl
      map_smul' := fun a f => QB_ext fun x => rfl }
  have hc : ∀ f, ((J f).1 : WO V W → ℂ) = f.1 := fun f => coe_toB hψ f.1 f.2
  have hJ : Function.Injective J := fun f g e => Subtype.ext (by rw [← hc, ← hc, e])
  have ht : ∀ f, IsThetaFunO ψ V W (J f).1 := fun f => (hc f).symm ▸ f.2
  obtain ⟨d, x, y, hd, hn, hx, hy, c1, c2, c3, hN⟩ := exists_der (HM V W) HM_herm (rhoV hψ σ V W) (isHeis_rhoB h hψ)
    J hJ (fun f => sm_of_theta h hψ _ (ht f))
    fun v f => ⟨⟨_, GlobalTheory.DefLift.Gen.theta_dH h hψ (J f) (ht f) v⟩, QB_ext fun w => congrFun (hc _) w⟩
  have hD : ∀ τ z (g : thetaSub ψ V W), Datum.dRho (heisO ψ V W) θ τ z g =
      d (vecL (Pi.single τ z : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ)) g := fun τ z g => by
    rw [← hc (d _ g), hd, GlobalTheory.DefLift.Gen.coe_dH h hψ _ (ht g), hc]
  let u : FVar D W.rank V.rank → Ix V W → ℂ := fun k => uM A B *ᵥ Pi.single (k.2, k.1) 1
  let p : FVar D W.rank V.rank → Prop := fun k => B.ε k.1 k.2.1 = A.ε k.1 k.2.2
  have s2 : ∀ τ, (fockScale D τ : ℂ) * fockScale D τ = 4 * π * cc D τ := fun τ => by
    rw [GlobalTheory.VacuumFockLaws.fockScale_sq, cc]
    push_cast
    ring
  have sn := GlobalTheory.VacuumFockLaws.fockScale_ne (D := D)
  have cs : ∀ τ, starRingEnd ℂ (cc D τ) = cc D τ := fun τ => conj_ofReal _
  let a : FVar D W.rank V.rank → Module.End ℂ (thetaSub ψ V W) := fun k =>
    (fockScale D k.1 : ℂ)⁻¹ • if p k then x (u k) else y (u k)
  let b : FVar D W.rank V.rank → Module.End ℂ (thetaSub ψ V W) := fun k =>
    -(fockScale D k.1 : ℂ)⁻¹ • if p k then y (u k) else x (u k)
  obtain ⟨haa, hba⟩ := ccr_of_sign (fun k => x (u k)) (fun k => y (u k)) p (fun k => (fockScale D k.1 : ℂ))
    (fun k => sn _) (fun _ _ => c1 _ _) (fun _ _ => c2 _ _) (fun k l => by
      rw [c3]
      congr 2
      have e : star (u l) ⬝ᵥ HM V W *ᵥ u k = ((uM A B)ᴴ * HM V W * uM A B) (l.2, l.1) (k.2, k.1) := by
        simp only [u]
        rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
        simp [← Pi.single_star]
      rw [e, uM_gram, diagonal_apply]
      by_cases hkl : k = l
      · subst hkl
        rw [if_pos rfl, if_pos rfl, s2, map_mul, map_mul, cs, conj_sgn, conj_sgn, mul_assoc (cc D _), sgn_mul]
        ring
      · rw [if_neg hkl, if_neg fun e : (l.2, l.1) = (k.2, k.1) => hkl (Prod.swap_injective e).symm, map_zero, mul_zero])
    (a := a) (b := b) (fun _ => rfl) fun _ => rfl
  have hdJ : ∀ (k : FVar D W.rank V.rank) (g : thetaSub ψ V W),
      Datum.dRho (heisO ψ V W) θ k.1 (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2) g = d (u k) g ∧
      Datum.dRho (heisO ψ V W) θ k.1 (cplxO (A.cart k.1) (B.cart k.1) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)) g =
        (if p k then (1 : ℂ) else -1) • (d (I • u k) g).1 := fun k g => by
    have e := uM_single A B k.1 k.2.1 k.2.2
    rw [hD, hD, cplxO_unit, vecL_smul, vecL_smul, ← e]
    refine ⟨rfl, ?_⟩
    simp only [p]
    split_ifs
    · rw [one_smul, one_smul]
    · rw [neg_one_smul, neg_one_smul, hn]
      rfl
  refine ⟨fun i j => (sgn (A.ε τ j) * (fockScale D τ : ℂ)⁻¹) • x (u (τ, i, j)),
    fun i j => (-sgn (B.ε τ i) * (fockScale D τ : ℂ)⁻¹) • y (u (τ, i, j)),
    fun k l => x (uM A B *ᵥ Pi.single k 1) * (-(1 / (4 * π)) : ℂ) • y ((uM A B * diagonal fun k =>
      (cc D k.2)⁻¹ * sgn (B.ε k.2 k.1.1) * sgn (A.ε k.2 k.1.2)) *ᵥ Pi.single l 1),
    fun f hf hv => ?_, fun i j l k => ?_, fun X X' hX g => ?_⟩
  · obtain ⟨E, h1, h2, h3'⟩ := exists_lift_on (thetaSub ψ V W)
      (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) a b (fun k g => by
        rw [aPlusAll, aPlus, crea, (hdJ k g).1, (hdJ k g).2]
        simp only [a]
        split_ifs
        · rw [hx, one_smul]
          rfl
        · rw [hy, neg_one_smul, smul_neg, sub_neg_eq_add]
          rfl) haa hba ⟨f, hf⟩ {k | k.1 = τ} (fun k hk => by
        have e := (show IsFockVacAt (heisO ψ V W) θ k.1 (cplxO (A.cart k.1) (B.cart k.1)) f from
          (show k.1 = τ from hk) ▸ hv) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)
        rw [annih, (hdJ k ⟨f, hf⟩).1, (hdJ k ⟨f, hf⟩).2] at e
        simp only [b, LinearMap.smul_apply]
        rw [smul_eq_zero]
        refine Or.inr (Subtype.ext ?_)
        split_ifs at e ⊢
        · rw [one_smul] at e
          rw [hy]
          exact e
        · rw [neg_one_smul, smul_neg, ← sub_eq_add_neg] at e
          rw [hx]
          exact e)
    have h3 : ∀ i j P, E (MvPolynomial.pderiv ((τ, i, j) : FVar D W.rank V.rank) P) = b (τ, i, j) (E P) :=
      fun i j P => h3' (τ, i, j) rfl P
    refine ⟨E, h1, fun i j P => ?_, fun i j P => ?_⟩
    · unfold raiO
      by_cases hp : B.ε τ i = A.ε τ j
      · simp only [if_pos hp, LinearMap.smul_apply, map_smul, LinearMap.mulLeft_apply, h2, a, p, smul_smul]
      · simp only [if_neg hp, LinearMap.smul_apply, map_smul, LinearMap.neg_apply, map_neg, Derivation.coeFn_coe, h3,
          b, p, smul_smul, neg_smul, neg_neg]
    · unfold lowO
      by_cases hp : B.ε τ i = A.ε τ j
      · simp only [if_pos hp, LinearMap.smul_apply, map_smul, Derivation.coeFn_coe, h3, b, p, smul_smul]
        rw [hp, neg_mul, mul_neg]
      · have e : sgn (A.ε τ j) = -sgn (B.ε τ i) := by
          revert hp
          cases B.ε τ i <;> cases A.ε τ j <;> simp [sgn]
        simp only [if_neg hp, LinearMap.smul_apply, map_smul, LinearMap.mulLeft_apply, h2, a, p, smul_smul, e]
  · beta_reduce
    rw [← mulVec_mulVec, diagonal_mulVec_single, ← smul_eq_mul _ (1 : ℂ), Pi.single_smul',
      mulVec_smul, map_smulₛₗ, map_mul, map_mul, map_inv₀, cs, conj_sgn, conj_sgn]
    simp only [u, smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    have h1 := sn τ
    have h2 : cc D τ = fockScale D τ * fockScale D τ / (4 * π) := by
      rw [s2]
      field_simp
    have h3 : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    rw [h2]
    field_simp
    linear_combination (sgn (B.ε τ l) * sgn (A.ε τ k)) * sgn_mul_self (A.ε τ j)
  · beta_reduce
    rw [← quad_basis x y _ hX, ← HM_inv]
    exact (congrArg (fun F : BB ψ V W => (F.1 : WO V W → ℂ)) (hN X g)).trans (hc _)

theorem lieFockUpTo_at : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω →
    ∃ (κS : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) (κT : Matrix (Fin W.rank) (Fin W.rank) ℂ → ℂ), ∀ f,
      IsThetaFunO ψ V W f → IsFockVacAt (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) f →
        GlobalTheory.ChainFr.LieFockWith ψ θ A B ω f τ κS κT := by
  intro D V W A B θ ψ χS χT ω τ hθ hω
  have hψ := hω.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨R, L, w, hE, hw, hN⟩ := exists_raise_lower_at A B h hψ τ
  have key : ∀ γ : ℝ → GA D V × GA D W, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) →
      (∀ t, (γ t).1 ∈ GinfC V ∧ (γ t).2 ∈ GinfC W) → ∀ X X' : Matrix (Ix V W) (Ix V W) ℂ,
      (∀ k l, HasDerivAt (fun t => mM θ V W (γ t) k l) (X k l) 0) → X * uM A B = uM A B * X' →
      ∃ lam : ℂ, ∀ (g : thetaSub ψ V W) z,
        HasDerivAt (fun t => ω (γ t) g.1 z) (((∑ k, ∑ l, X' k l • w k l) g + lam • g).1 z) 0 := by
    intro γ h1 h2 h3 X X' h4 h5
    obtain ⟨lam, hl⟩ := GlobalTheory.Mem.LiftGen.hasDerivAt_om D θ σ h ψ hψ V W ω (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
      γ h1 h2 h3 X h4
    refine ⟨lam, fun g z => ?_⟩
    have e := coe_toB hψ g.1 g.2
    have h6 := hl (toB hψ g.1 g.2) (e.symm ▸ g.2) 1 z
    simp only [one_mul, map_one, Module.End.one_apply] at h6
    rw [← GlobalTheory.DefLift.Gen.coe_add_smul, hN X X' h5, e] at h6
    exact h6
  have hS : ∀ X, ∃ κ : ℂ, X ∈ lieAt V τ → ∀ f, IsThetaFunO ψ V W f →
      IsFockVacAt (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) f → ∀ (P : PolF D W.rank V.rank) (z : WO V W),
      HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (ptF ψ θ A B f P) z)
        (ptF ψ θ A B f (fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + κ • P) z) 0 := by
    intro X
    by_cases hX : X ∈ lieAt V τ
    swap
    · exact ⟨0, fun h => absurd h hX⟩
    obtain ⟨lam, hl⟩ := key (fun t => (oneP θ V τ X t, 1)) ((continuous_oneP hθ hX).prodMk continuous_const)
      (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨(isAtTau_oneP hθ hX t).1, one_mem _⟩) (blk (fun _ => 1) (Pi.single τ (-X)))
      (blk (fun _ => 1) (Pi.single τ (-(A.fr τ * X * (A.fr τ)⁻¹)))) (fun k l => by
        simp only [mM_apply, WeylAction.oneP_inv hθ hX, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one,
          WeylAction.blk_apply]
        split_ifs
        · exact (WeylAction.hasDerivAt_comp hθ (WeylAction.neg_mem_lieAt hX) _ _ _).const_mul _
        · exact hasDerivAt_const _ _) (by
        rw [uM, blk_mul, blk_mul]
        congr 1 <;> funext t
        · rw [Matrix.one_mul, Matrix.mul_one]
        · rw [blk_single_congr A.fr (fr_det A), Matrix.mul_neg, Matrix.neg_mul])
    refine ⟨lam - ∑ i, ∑ k, (A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ) i k *
      ∑ _j : Fin W.rank, if i = k then (1 / 2 : ℂ) else 0, fun _ f hf hv P z => ?_⟩
    obtain ⟨E, h1, h2, h3⟩ := hE f hf hv
    have e : ∑ k, ∑ l, blk (fun _ => 1) (Pi.single τ (-(A.fr τ * X * (A.fr τ)⁻¹))) k l • w k l =
        ∑ j, ∑ k, (A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ) j k • ∑ i, R i j * L i k := by
      rw [WeylAction.sum_right, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.map_apply, lie_entry (fr_det A τ) (A.fr_gram τ) hX]
      simp only [hw, ← Finset.smul_sum]
      module
    rw [h1, h1, map_add, map_smul, fockS, lift_quad E (fun j i => raiO τ (A.ε τ) (B.ε τ) i j)
      (fun j i => lowO τ (A.ε τ) (B.ε τ) i j) (fun j i => R i j) (fun j i => L i j) (fun j i => h2 i j)
      (fun j i => h3 i j), add_assoc, ← add_smul, add_sub_cancel, ← e]
    exact hl (E P) z
  have hT : ∀ Y, ∃ κ : ℂ, Y ∈ lieAt W τ → ∀ f, IsThetaFunO ψ V W f →
      IsFockVacAt (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) f → ∀ (P : PolF D W.rank V.rank) (z : WO V W),
      HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptF ψ θ A B f P) z)
        (ptF ψ θ A B f (fockT τ (A.ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P + κ • P) z) 0 := by
    intro Y
    by_cases hY : Y ∈ lieAt W τ
    swap
    · exact ⟨0, fun h => absurd h hY⟩
    obtain ⟨lam, hl⟩ := key (fun t => (1, oneP θ W τ Y t)) (continuous_const.prodMk (continuous_oneP hθ hY))
      (fun s t => by rw [oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨one_mem _, (isAtTau_oneP hθ hY t).1⟩) (blk (Pi.single τ Y) fun _ => 1)
      (blk (Pi.single τ (B.fr τ * Y * (B.fr τ)⁻¹)) fun _ => 1) (fun k l => by
        simp only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, WeylAction.blk_apply]
        split_ifs
        · exact (WeylAction.hasDerivAt_comp hθ hY _ _ _).mul_const _
        · exact hasDerivAt_const _ _) (by
        rw [uM, blk_mul, blk_mul]
        congr 1 <;> funext t
        · rw [← nonsing_inv_mul_cancel_left _ (_ * (B.fr t)⁻¹) (fr_det B t), ← Matrix.mul_assoc (B.fr t),
            blk_single_congr B.fr (fr_det B), mul_nonsing_inv_cancel_right _ _ (fr_det B t)]
        · rw [Matrix.one_mul, Matrix.mul_one])
    refine ⟨lam - ∑ i, ∑ k, (B.fr τ * Y * (B.fr τ)⁻¹) i k *
      ∑ _j : Fin V.rank, if i = k then (1 / 2 : ℂ) else 0, fun _ f hf hv P z => ?_⟩
    obtain ⟨E, h1, h2, h3⟩ := hE f hf hv
    have e : ∑ k, ∑ l, blk (Pi.single τ (B.fr τ * Y * (B.fr τ)⁻¹)) (fun _ => 1) k l • w k l =
        ∑ i, ∑ k, (B.fr τ * Y * (B.fr τ)⁻¹) i k • ∑ j, R i j * L k j := by
      rw [WeylAction.sum_left]
      simp only [hw, sgn_mul_self, one_smul]
    rw [h1, h1, map_add, map_smul, fockT, lift_quad E _ _ R L h2 h3, add_assoc, ← add_smul, add_sub_cancel, ← e]
    exact hl (E P) z
  choose κS hS using hS
  choose κT hT using hT
  exact ⟨κS, κT, fun f hf hv => ⟨fun X hX => hS X hX f hf hv, fun Y hY => hT Y hY f hf hv⟩⟩

end GlobalTheory.LieFock

end
