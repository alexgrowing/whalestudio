import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RapidDecayLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtWeilRepRealOneParamAdelicPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift
open scoped ENNReal NNReal Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.LiftReg

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

section Tame

variable {X : Type} [AddCommGroup X] [Module ℂ X] {j : X →ₗ[ℂ] (WO V W → ℂ)} {r r' : ℕ} {S S' : X → X}

variable (ψ θ j r S) in

def Tame : Prop :=
  (∀ U x, j x ∈ thetaLevel ψ V W U → j (S x) ∈ thetaLevel ψ V W U) ∧
    ∃ c : ℝ≥0, ∀ μ 𝓕 d x, IsThetaFunO ψ V W (j x) → sobO ψ θ μ 𝓕 d (j (S x)) ≤ c * sobO ψ θ μ 𝓕 (d + r) (j x)

theorem Tame.theta (h : Tame ψ θ j r S) {x : X} (hx : IsThetaFunO ψ V W (j x)) : IsThetaFunO ψ V W (j (S x)) := by
  obtain ⟨U, -, hU⟩ := isTheta_iff_level.mp hx
  exact (h.1 U x hU).1

theorem Tame.congr (h : Tame ψ θ j r S) (e : ∀ x, IsThetaFunO ψ V W (j x) → j (S' x) = j (S x)) : Tame ψ θ j r S' := by
  obtain ⟨hlev, c, hc⟩ := h
  refine ⟨fun U x hx => ?_, c, fun μ 𝓕 d x hx => ?_⟩
  · rw [e x hx.1]
    exact hlev U x hx
  · rw [e x hx]
    exact hc μ 𝓕 d x hx

theorem tame_id : Tame ψ θ j r fun x => x := by
  refine ⟨fun U x hx => hx, 1, fun μ 𝓕 d x _ => ?_⟩
  rw [ENNReal.coe_one, one_mul]
  exact sobO_mono (Nat.le_add_right d r)

theorem Tame.mono (h : Tame ψ θ j r S) (hr : r ≤ r') : Tame ψ θ j r' S := by
  obtain ⟨hlev, c, hc⟩ := h
  refine ⟨hlev, c, fun μ 𝓕 d x hx => (hc μ 𝓕 d x hx).trans ?_⟩
  gcongr
  exact sobO_mono (Nat.add_le_add_left hr d)

theorem Tame.smul (a : ℂ) (h : Tame ψ θ j r S) : Tame ψ θ j r fun x => a • S x := by
  obtain ⟨hlev, c, hc⟩ := h
  refine ⟨fun U x hx => ?_, ‖a‖₊ * c, fun μ 𝓕 d x hx => ?_⟩
  · rw [map_smul]
    exact Submodule.smul_mem _ a (hlev U x hx)
  · rw [map_smul, sobO_smul, ENNReal.coe_mul, mul_assoc, enorm_eq_nnnorm]
    gcongr
    exact hc μ 𝓕 d x hx

theorem Tame.add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (h : Tame ψ θ j r S) (h' : Tame ψ θ j r S') :
    Tame ψ θ j r fun x => S x + S' x := by
  refine ⟨fun U x hx => ?_, h.2.choose + h'.2.choose, fun μ 𝓕 d x hx => ?_⟩
  · rw [map_add]
    exact Submodule.add_mem _ (h.1 U x hx) (h'.1 U x hx)
  · rw [map_add, ENNReal.coe_add, add_mul]
    exact (sobO_add_le hψ hθ (h.theta hx) (h'.theta hx) d).trans
      (add_le_add (h.2.choose_spec μ 𝓕 d x hx) (h'.2.choose_spec μ 𝓕 d x hx))

theorem Tame.comp (h : Tame ψ θ j r S) (h' : Tame ψ θ j r' S') : Tame ψ θ j (r + r') fun x => S (S' x) := by
  obtain ⟨c, hc⟩ := h.2
  obtain ⟨c', hc'⟩ := h'.2
  refine ⟨fun U x hx => h.1 U _ (h'.1 U x hx), c * c', fun μ 𝓕 d x hx => ?_⟩
  calc sobO ψ θ μ 𝓕 d (j (S (S' x))) ≤ c * sobO ψ θ μ 𝓕 (d + r) (j (S' x)) := hc μ 𝓕 d _ (h'.theta hx)
    _ ≤ c * (c' * sobO ψ θ μ 𝓕 (d + r + r') (j x)) := by gcongr; exact hc' μ 𝓕 (d + r) x hx
    _ = ((c * c' : ℝ≥0) : ℝ≥0∞) * sobO ψ θ μ 𝓕 (d + (r + r')) (j x) := by
      rw [ENNReal.coe_mul, mul_assoc, Nat.add_assoc]

theorem tame_sum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {ι : Type} (s : Finset ι) {T : ι → X → X}
    (h : ∀ i, Tame ψ θ j r (T i)) : Tame ψ θ j r fun x => ∑ i ∈ s, T i x := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 : Tame ψ θ j r fun x : X => x := tame_id
    refine (h0.smul (0 : ℂ)).congr fun x _ => ?_
    simp
  | insert a s ha ih =>
    refine ((h a).add hψ hθ ih).congr fun x _ => ?_
    rw [Finset.sum_insert ha]

theorem tame_word {ι : Type} {T : ι → X → X} (h : ∀ i, Tame ψ θ j r (T i)) (l : List ι) :
    Tame ψ θ j (l.length * r) (wordAct T l) := by
  induction l with
  | nil =>
    have h0 : Tame ψ θ j 0 fun x : X => x := tame_id
    rw [List.length_nil, Nat.zero_mul]
    exact h0.congr fun x _ => by rw [wordAct_nil]
  | cons i l ih =>
    have key := ((h i).comp ih).congr (S' := wordAct T (i :: l)) fun x _ => by rw [wordAct_cons]
    have e : (i :: l).length * r = r + l.length * r := by
      rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
    rw [e]
    exact key

theorem tame_of_heisDer (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (a : D.what₂.Tau × Fin W.rank × Fin V.rank × Bool)
    (e : ∀ x, IsThetaFunO ψ V W (j x) → j (S x) = heisDer ψ θ a (j x)) : Tame ψ θ j 1 S := by
  refine ⟨fun U x hx => ?_, 1, fun μ 𝓕 d x hx => ?_⟩
  · rw [e x hx.1]
    exact dRho_mem_thetaLevel hψ hθ hx a.1 _
  · rw [e x hx, ENNReal.coe_one, one_mul]
    exact sobO_heisDer_le d a

private theorem dH_eq_sum_re_im_single {ι B : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup B] [NormedSpace ℂ B]
    (ρ : (ι → ℂ) → B →L[ℂ] B) (v : ι → ℂ) (F : B) :
    dH ρ v F = ∑ k, ((((v k).re : ℝ) : ℂ) • dH ρ (Pi.single k 1) F +
      (((v k).im : ℝ) : ℂ) • dH ρ (Pi.single k Complex.I) F) := by
  have hv : v = ∑ k, ((v k).re • (Pi.single k (1 : ℂ) : ι → ℂ) + (v k).im • (Pi.single k Complex.I : ι → ℂ)) := by
    funext x
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Complex.real_smul, mul_one]
    exact (Complex.re_add_im (v x)).symm
  conv_lhs => rw [hv]
  unfold dH
  simp only [map_sum, map_add, map_smul, Complex.coe_smul]

private theorem single_eq_vecL_single (i : Fin W.rank) (j : Fin V.rank) (τ : D.what₂.Tau) (c : ℂ) :
    (Pi.single ((i, j), τ) c : Ix V W → ℂ) =
      vecL (Pi.single τ (Matrix.single i j c) : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) := by
  funext p
  obtain ⟨⟨i', j'⟩, τ'⟩ := p
  show _ = (Pi.single τ (Matrix.single i j c) : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) τ' i' j'
  by_cases hτ : τ' = τ
  · subst hτ
    by_cases hi : i' = i
    · subst hi
      by_cases hj : j' = j
      · subst hj
        simp
      · simp [hj, Ne.symm hj]
    · simp [hi, Ne.symm hi]
  · simp [hτ]

end Tame

variable (ψ V W) in

def coeB : BB ψ V W →ₗ[ℂ] (WO V W → ℂ) where
  toFun F := F.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D}

theorem tame_dH (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (v : Ix V W → ℂ) :
    Tame ψ θ (coeB ψ V W) 1 (dH (rhoV hψ σ V W) v) := by
  have hθ : IsInfFam θ := h.inf
  have h1 : ∀ k : Ix V W, Tame ψ θ (coeB ψ V W) 1 (dH (rhoV hψ σ V W) (Pi.single k 1)) := fun k =>
    tame_of_heisDer hψ hθ (k.2, k.1.1, k.1.2, false) fun F hF => by
      rw [show k = ((k.1.1, k.1.2), k.2) from rfl, single_eq_vecL_single]
      exact GlobalTheory.DefLift.Gen.coe_dH h hψ F hF _ _
  have hI : ∀ k : Ix V W, Tame ψ θ (coeB ψ V W) 1 (dH (rhoV hψ σ V W) (Pi.single k Complex.I)) := fun k =>
    tame_of_heisDer hψ hθ (k.2, k.1.1, k.1.2, true) fun F hF => by
      rw [show k = ((k.1.1, k.1.2), k.2) from rfl, single_eq_vecL_single]
      exact GlobalTheory.DefLift.Gen.coe_dH h hψ F hF _ _
  refine (tame_sum hψ hθ Finset.univ (T := fun k F => (((v k).re : ℝ) : ℂ) • dH (rhoV hψ σ V W) (Pi.single k 1) F +
      (((v k).im : ℝ) : ℂ) • dH (rhoV hψ σ V W) (Pi.single k Complex.I) F)
    fun k => ((h1 k).smul _).add hψ hθ ((hI k).smul _)).congr fun F _ => ?_
  rw [dH_eq_sum_re_im_single]

theorem tame_nOp (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (Y : Matrix (Ix V W) (Ix V W) ℂ) :
    Tame ψ θ (coeB ψ V W) 2 (nOp (rhoV hψ σ V W) (HM V W) Y) := by
  have hθ : IsInfFam θ := h.inf
  have hx : ∀ k, Tame ψ θ (coeB ψ V W) 1 (xOp (rhoV hψ σ V W) k) := fun k =>
    ((tame_dH h hψ (Pi.single k 1)).add hψ hθ
      ((tame_dH h hψ (Complex.I • Pi.single k 1)).smul (-Complex.I))).congr fun F _ => by
        simp only [xOp, sub_eq_add_neg, neg_smul]
  have hd : ∀ l, Tame ψ θ (coeB ψ V W) 1 (dOp (rhoV hψ σ V W) (HM V W) l) := fun l =>
    (((tame_dH h hψ (Matrix.mulVec (HM V W)⁻¹ (Pi.single l 1))).add hψ hθ
      ((tame_dH h hψ (Complex.I • Matrix.mulVec (HM V W)⁻¹ (Pi.single l 1))).smul Complex.I)).smul
        (-(1 / (4 * (Real.pi : ℂ))))).congr fun F _ => by
      simp only [dOp]
  refine (tame_sum hψ hθ Finset.univ (T := fun k F => ∑ l, Y k l • xOp (rhoV hψ σ V W) k (dOp (rhoV hψ σ V W) (HM V W) l F))
    fun k => tame_sum hψ hθ Finset.univ (T := fun l F => Y k l • xOp (rhoV hψ σ V W) k (dOp (rhoV hψ σ V W) (HM V W) l F))
      fun l => ((hx k).comp (hd l)).smul (Y k l)).congr fun F _ => ?_
  simp only [nOp]

private theorem tame_id_of_tame_coeB (hψ : IsStdChar D ψ (-1)) {r : ℕ} {G : BB ψ V W → BB ψ V W}
    (hG : Tame ψ θ (coeB ψ V W) r G) {S : (WO V W → ℂ) → WO V W → ℂ}
    (e : ∀ f (hf : IsThetaFunO ψ V W f), S f = ((G (toB hψ f hf)).1 : WO V W → ℂ)) :
    Tame ψ θ LinearMap.id r S := by
  obtain ⟨hlev, c, hc⟩ := hG
  refine ⟨fun U f hf => ?_, c, fun μ 𝓕 d f hf => ?_⟩
  · have hf' : IsThetaFunO ψ V W f := hf.1
    have hB : coeB ψ V W (toB hψ f hf') ∈ thetaLevel ψ V W U := by
      show ((toB hψ f hf').1 : WO V W → ℂ) ∈ _
      rw [coe_toB]
      exact hf
    rw [LinearMap.id_apply, e f hf']
    exact hlev U _ hB
  · rw [LinearMap.id_apply] at hf
    have h1 : coeB ψ V W (toB hψ f hf) = f := coe_toB hψ f hf
    have h0 := hc μ 𝓕 d (toB hψ f hf) (by rw [h1]; exact hf)
    rw [h1] at h0
    rw [LinearMap.id_apply, LinearMap.id_apply, e f hf]
    exact h0

variable {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem tame_deriv (h : GlobalTheory.FockCompare.Chart θ σ) (hω : IsWeilDatumO ψ V W χS χT ω) (γ : ℝ → GA D V × GA D W)
    (h1 : Continuous γ) (h2 : ∀ s t, γ (s + t) = γ s * γ t) (h3 : ∀ t, (γ t).1 ∈ GinfC V ∧ (γ t).2 ∈ GinfC W)
    (Y : Matrix (Ix V W) (Ix V W) ℂ) (h4 : ∀ k l, HasDerivAt (fun t => mM θ V W (γ t) k l) (Y k l) 0) :
    Tame ψ θ LinearMap.id 2 (fun f z => deriv (fun t : ℝ => ω (γ t) f z) 0) ∧
      ∀ f, IsThetaFunO ψ V W f → ∀ p w, HasDerivAt (fun t => ω (p * γ t) f w)
        (ω p (fun z => deriv (fun t : ℝ => ω (γ t) f z) 0) w) 0 := by
  have hψ : IsStdChar D ψ (-1) := hω.std
  obtain ⟨lam, hlam⟩ := GlobalTheory.Mem.LiftGen.hasDerivAt_om D θ σ h ψ hψ V W ω (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
    γ h1 h2 h3 Y h4
  have key : ∀ f (hf : IsThetaFunO ψ V W f) (p : GA D V × GA D W) (w : WO V W), HasDerivAt (fun t => ω (p * γ t) f w)
      (ω p (nOp (rhoV hψ σ V W) (HM V W) Y (toB hψ f hf) + lam • toB hψ f hf).1 w) 0 := fun f hf p w => by
    have := hlam (toB hψ f hf) (by rw [coe_toB]; exact hf) p w
    rwa [coe_toB] at this
  have hd : ∀ f (hf : IsThetaFunO ψ V W f), (fun z => deriv (fun t : ℝ => ω (γ t) f z) 0) =
      ((nOp (rhoV hψ σ V W) (HM V W) Y (toB hψ f hf) + lam • toB hψ f hf).1 : WO V W → ℂ) := fun f hf => by
    funext z
    have := (key f hf 1 z).deriv
    simp only [one_mul, map_one] at this
    exact this
  have hid : Tame ψ θ (coeB ψ V W) 2 fun F : BB ψ V W => F := tame_id
  refine ⟨tame_id_of_tame_coeB hψ (G := fun F => nOp (rhoV hψ σ V W) (HM V W) Y F + lam • F)
    ((tame_nOp h hψ Y).add hψ h.inf (hid.smul lam)) hd, fun f hf p w => ?_⟩
  rw [hd f hf]
  exact key f hf p w

theorem tame_dOmS (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Tame ψ θ LinearMap.id 2 (dOmS θ ω τ X) ∧ ∀ f, IsThetaFunO ψ V W f → ∀ p w,
      HasDerivAt (fun t => ω (p * (oneP θ V τ X t, 1)) f w) (ω p (dOmS θ ω τ X f) w) 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hd : ∀ k l : Ix V W, HasDerivAt (fun t => mM θ V W ((oneP θ V τ X t, 1) : GA D V × GA D W) k l)
      (blk (fun _ => 1) (Pi.single τ (-X)) k l) 0 := by
    intro k l
    have e : (fun t : ℝ => mM θ V W ((oneP θ V τ X t, 1) : GA D V × GA D W) k l) = fun t =>
        if k.2 = l.2 then (1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) k.1.1 l.1.1 *
          compAt θ k.2 (Formalism.L2.Theta.mt V (oneP θ V τ (-X) t)) l.1.2 k.1.2 else 0 := by
      funext t
      simp only [mM_apply, GlobalTheory.Mem.Lift.WeylAction.blk_apply, GlobalTheory.Mem.Lift.WeylAction.oneP_inv hθ hX,
        compAt_fin (one_mem _)]
    rw [e, GlobalTheory.Mem.Lift.WeylAction.blk_apply]
    split_ifs
    · exact (GlobalTheory.Mem.Lift.WeylAction.hasDerivAt_comp hθ (GlobalTheory.Mem.Lift.WeylAction.neg_mem_lieAt hX) k.2 l.1.2
        k.1.2).const_mul _
    · exact hasDerivAt_const _ _
  exact tame_deriv hσ hω (fun t => (oneP θ V τ X t, 1)) ((continuous_oneP hθ hX).prodMk continuous_const)
    (fun s t => Prod.ext (by simp [oneP_add hθ hX]) (by simp)) (fun t => ⟨(isAtTau_oneP hθ hX t).1, one_mem _⟩) _ hd

theorem tame_dOmT (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) {τ : D.what₂.Tau}
    {Y : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hY : Y ∈ lieAt W τ) :
    Tame ψ θ LinearMap.id 2 (dOmT θ ω τ Y) ∧ ∀ f, IsThetaFunO ψ V W f → ∀ p w,
      HasDerivAt (fun t => ω (p * (1, oneP θ W τ Y t)) f w) (ω p (dOmT θ ω τ Y f) w) 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hd : ∀ k l : Ix V W, HasDerivAt (fun t => mM θ V W ((1, oneP θ W τ Y t) : GA D V × GA D W) k l)
      (blk (Pi.single τ Y) (fun _ => 1) k l) 0 := by
    intro k l
    have e : (fun t : ℝ => mM θ V W ((1, oneP θ W τ Y t) : GA D V × GA D W) k l) = fun t =>
        if k.2 = l.2 then compAt θ k.2 (Formalism.L2.Theta.mt W (oneP θ W τ Y t)) k.1.1 l.1.1 *
          (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) l.1.2 k.1.2 else 0 := by
      funext t
      simp only [mM_apply, GlobalTheory.Mem.Lift.WeylAction.blk_apply, inv_one, compAt_fin (one_mem _)]
    rw [e, GlobalTheory.Mem.Lift.WeylAction.blk_apply]
    split_ifs
    · exact (GlobalTheory.Mem.Lift.WeylAction.hasDerivAt_comp hθ hY k.2 k.1.1 l.1.1).mul_const _
    · exact hasDerivAt_const _ _
  exact tame_deriv hσ hω (fun t => (1, oneP θ W τ Y t)) (continuous_const.prodMk (continuous_oneP hθ hY))
    (fun s t => Prod.ext (by simp) (by simp [oneP_add hθ hY])) (fun t => ⟨one_mem _, (isAtTau_oneP hθ hY t).1⟩) _ hd

end GlobalTheory.Chain.LiftReg

end
