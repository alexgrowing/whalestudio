import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictio
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdMapMulSingleApply

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.RealMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Eqv

variable {D : D7}

theorem norm_sub_three {G : Type*} (φ : G → ℂ) (a b c d : G) :
    ‖φ d - φ a‖ ≤ ‖φ d - φ c‖ + ‖φ c - φ b‖ + ‖φ b - φ a‖ := by
  have e : φ d - φ a = (φ d - φ c) + (φ c - φ b) + (φ b - φ a) := by ring
  rw [e]
  exact norm_add₃_le

theorem lip_list {ι : Type*} (θ : InfFam D) {V : HSp D} (A : Fr V) (φ : GA D V → ℂ) (c : ℝ) (hL : Lip θ A φ c)
    (τf : ι → D.what₂.Tau) (Xf Yf : ι → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hX : ∀ i, Xf i ∈ lieAt V (τf i)) (hY : ∀ i, Yf i ∈ lieAt V (τf i)) (l : List ι) (y : GA D V) :
    ‖φ (y * (l.map fun i => oneP θ V (τf i) (Xf i) 1 * oneP θ V (τf i) (Yf i) 1).prod) - φ y‖ ≤
      c * (l.map fun i => hsn (A.fr (τf i) * Xf i * (A.fr (τf i))⁻¹) +
        hsn (A.fr (τf i) * Yf i * (A.fr (τf i))⁻¹)).sum := by
  induction l generalizing y with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have h1 := hL y (τf i) (Xf i) (hX i) 1
    have h2 := hL (y * oneP θ V (τf i) (Xf i) 1) (τf i) (Yf i) (hY i) 1
    have h3 := ih (y * oneP θ V (τf i) (Xf i) 1 * oneP θ V (τf i) (Yf i) 1)
    rw [abs_one, mul_one] at h1 h2
    rw [← mul_assoc, ← mul_assoc]
    refine (norm_sub_three φ y (y * oneP θ V (τf i) (Xf i) 1)
      (y * oneP θ V (τf i) (Xf i) 1 * oneP θ V (τf i) (Yf i) 1) _).trans ?_
    rw [show ∀ a b s : ℝ, c * (a + b + s) = c * s + c * b + c * a from fun a b s => by ring]
    linarith

theorem list_prod_mulSingle {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Monoid (M i)] (x : ∀ i, M i)
    (l : List ι) (hl : l.Nodup) (w : ι) :
    (l.map fun i => Pi.mulSingle i (x i)).prod w = if w ∈ l then x w else 1 := by
  first
  | exact @_root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply
  | exact _root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply
  | (apply _root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply ..)

theorem conj_cancel {n : ℕ} {P M N : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : P * M * P⁻¹ = P * N * P⁻¹) :
    M = N := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have e := congrArg (fun Q => P⁻¹ * Q * P) h
  simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul _ hd,
    Matrix.mul_one] using e

theorem conj_back {n : ℕ} (Q M : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) : Q * (Q⁻¹ * M * Q⁻¹⁻¹) * Q⁻¹ = M := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hQ
  rw [Matrix.nonsing_inv_nonsing_inv Q hd]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

def expUJ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) : Formalism.REAL.UJ ε :=
  ⟨(Matrix.isUnit_exp X).unit, by
    have h := Formalism.REAL.exp_indefinite_unitary_holds n ε X hX 1
    show Formalism.REAL.inUJ ε (NormedSpace.exp X)
    simpa using h⟩

theorem isAtTau_unique (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (fr : UI.Frames D V) {τ : D.what₂.Tau}
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} {h h' : GA D V} (hh : IsAtTau θ V τ g h) (hh' : IsAtTau θ V τ g h') :
    h = h' := by
  obtain ⟨-, h2, -⟩ := GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr
  have he : ∀ τ', infMat D.sp.cm.sig V.gram (θ τ') h = infMat D.sp.cm.sig V.gram (θ τ') h' := fun τ' => by
    by_cases e : τ' = τ
    · subst e; rw [hh.2.1, hh'.2.1]
    · rw [hh.2.2 τ' e, hh'.2.2 τ' e]
  have hx : UI.brg fr ((UI.brg fr).symm h) = h := (UI.brg fr).apply_symm_apply h
  have hx' : UI.brg fr ((UI.brg fr).symm h') = h' := (UI.brg fr).apply_symm_apply h'
  have hxx : (UI.brg fr).symm h = (UI.brg fr).symm h' := by
    refine Prod.ext (funext fun (v : InfinitePlace D.host.F) => ?_) ?_
    · have a := h2 ((UI.brg fr).symm h) ((Formalism.L2.Host.tauPl D).symm v) _ rfl
      have a' := h2 ((UI.brg fr).symm h') ((Formalism.L2.Host.tauPl D).symm v) _ rfl
      rw [Equiv.apply_symm_apply] at a a'
      rw [hx] at a
      rw [hx'] at a'
      have e2 := a.symm.trans ((he _).trans a')
      exact Subtype.ext (Units.ext (conj_cancel (fr.unit v) e2))
    · rw [(brg_mem_GinfC fr _).1 (by rw [hx]; exact hh.1), (brg_mem_GinfC fr _).1 (by rw [hx']; exact hh'.1)]
  rw [← hx, ← hx', hxx]

open Classical in

theorem isAtTau_brg (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (fr : UI.Frames D V) (v : InfinitePlace D.host.F)
    (a : Formalism.REAL.UJ (fr.ε v)) :
    IsAtTau θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Formalism.MainNotions.S.uMat a * (fr.P v)⁻¹)
      (UI.brg fr ((Pi.mulSingle v a : (UI.instV fr).Ginf), 1)) := by
  classical
  obtain ⟨-, h2, -⟩ := GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr
  have hs : ∀ w : InfinitePlace (UI.instV fr).F, w = v → Formalism.MainNotions.S.uMat ((Pi.mulSingle v a : (UI.instV fr).Ginf) w) = Formalism.MainNotions.S.uMat a := by
    rintro w rfl
    exact congrArg Formalism.MainNotions.S.uMat
      (Pi.mulSingle_eq_same (M := fun w : InfinitePlace (UI.instV fr).F => Formalism.REAL.UJ ((UI.instV fr).ε w)) w a)
  have hn : ∀ w : InfinitePlace (UI.instV fr).F, w ≠ v → Formalism.MainNotions.S.uMat ((Pi.mulSingle v a : (UI.instV fr).Ginf) w) = 1 := by
    intro w hw
    exact (congrArg Formalism.MainNotions.S.uMat
      (Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace (UI.instV fr).F => Formalism.REAL.UJ ((UI.instV fr).ε w)) hw a)).trans rfl
  refine ⟨(brg_mem_GinfC fr _).2 rfl, ?_, fun τ' hτ' => ?_⟩
  · have e := h2 ((Pi.mulSingle v a : (UI.instV fr).Ginf), 1) ((Formalism.L2.Host.tauPl D).symm v) (Formalism.MainNotions.S.uMat a)
      (hs _ (Equiv.apply_symm_apply _ _)).symm
    rw [e]
    simp only [Equiv.apply_symm_apply]
  · have hw : Formalism.L2.Host.tauPl D τ' ≠ v := fun hv => hτ' (by rw [← hv, Equiv.symm_apply_apply])
    have e := h2 ((Pi.mulSingle v a : (UI.instV fr).Ginf), 1) τ' 1 (hn _ hw).symm
    rw [e]
    have hd := (Matrix.isUnit_iff_isUnit_det _).1 (fr.unit (Formalism.L2.Host.tauPl D τ'))
    rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]

open Classical in

theorem oneP_eq_brg (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (fr : UI.Frames D V) (v : InfinitePlace D.host.F)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (a : Formalism.REAL.UJ (fr.ε v))
    (ha : NormedSpace.exp X = fr.P v * Formalism.MainNotions.S.uMat a * (fr.P v)⁻¹) :
    oneP θ V ((Formalism.L2.Host.tauPl D).symm v) X 1 = UI.brg fr ((Pi.mulSingle v a : (UI.instV fr).Ginf), 1) := by
  have hc := isAtTau_brg θ hθ fr v a
  rw [← ha, ← one_smul ℝ X] at hc
  have hex : ∃ x, IsAtTau θ V ((Formalism.L2.Host.tauPl D).symm v) (NormedSpace.exp ((1 : ℝ) • X)) x := ⟨_, hc⟩
  unfold oneP atTau
  rw [dif_pos hex]
  exact isAtTau_unique θ hθ fr hex.choose_spec hc

theorem map_prod_pairs {ι G H : Type*} [Monoid G] [Monoid H] (f : G →* H) (l : List ι) (a b : ι → G) :
    f (l.map fun i => a i * b i).prod = (l.map fun i => f (a i) * f (b i)).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

theorem conj_mem_lieAt {V : HSp D} (fr : UI.Frames D V) (v : InfinitePlace D.host.F)
    {M : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hM : Formalism.REAL.inG (fr.ε v) M) :
    fr.P v * M * (fr.P v)⁻¹ ∈ lieAt V ((Formalism.L2.Host.tauPl D).symm v) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (fr.unit v)
  have e1 : ((fr.P v)⁻¹)ᴴ * (fr.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  have hG : gramAt D V ((Formalism.L2.Host.tauPl D).symm v) =
      ((fr.P v)⁻¹)ᴴ * Formalism.REAL.Jm (fr.ε v) * (fr.P v)⁻¹ := by
    rw [← fr.spec v]
    calc gramAt D V ((Formalism.L2.Host.tauPl D).symm v) = V.gram.map (UI.phiV D v) := rfl
      _ = ((fr.P v)⁻¹)ᴴ * (fr.P v)ᴴ * V.gram.map (UI.phiV D v) * (fr.P v * (fr.P v)⁻¹) := by
        rw [e1, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e2 : ∀ W : Matrix (Fin V.rank) (Fin V.rank) ℂ, (fr.P v)ᴴ * (((fr.P v)⁻¹)ᴴ * W) = W := fun W => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have e3 : ∀ W : Matrix (Fin V.rank) (Fin V.rank) ℂ, (fr.P v)⁻¹ * (fr.P v * W) = W := fun W =>
    Matrix.nonsing_inv_mul_cancel_left _ _ hd
  show _ * _ + _ * _ = 0
  rw [hG]
  have key : (fr.P v * M * (fr.P v)⁻¹)ᴴ * (((fr.P v)⁻¹)ᴴ * Formalism.REAL.Jm (fr.ε v) * (fr.P v)⁻¹) +
      ((fr.P v)⁻¹)ᴴ * Formalism.REAL.Jm (fr.ε v) * (fr.P v)⁻¹ * (fr.P v * M * (fr.P v)⁻¹) =
      ((fr.P v)⁻¹)ᴴ * (Mᴴ * Formalism.REAL.Jm (fr.ε v) + Formalism.REAL.Jm (fr.ε v) * M) * (fr.P v)⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e2, e3, Matrix.mul_add, Matrix.add_mul]
  rw [key, show Mᴴ * Formalism.REAL.Jm (fr.ε v) + Formalism.REAL.Jm (fr.ε v) * M = 0 from hM, Matrix.mul_zero, Matrix.zero_mul]

open Classical in

theorem lip_move_real : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (φ : GA D V → ℂ) (c : ℝ), 0 ≤ c → Lip θ A φ c → ∀ (u : (Formalism.IndefR.Eqv.UI.instV fr).Ginf) (Av Z : InfinitePlace D.host.F → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ v, Formalism.REAL.inG (fr.ε v) (Av v) ∧ Formalism.REAL.inG (fr.ε v) (Z v)) → (∀ v, Formalism.MainNotions.S.uMat (u v) = NormedSpace.exp (Av v) * NormedSpace.exp (Z v)) → ∀ y : GA D V, ‖φ (y * Formalism.IndefR.Eqv.UI.brg fr (u, 1)) - φ y‖ ≤ c * ∑ v, (Real.sqrt (Formalism.REAL.hs (Av v)) + Real.sqrt (Formalism.REAL.hs (Z v))) := by
  intro D θ hθ V A fr hP φ c hc hL u Av Z hAZ hu y
  have hX : ∀ v, fr.P v * Av v * (fr.P v)⁻¹ ∈ lieAt V ((Formalism.L2.Host.tauPl D).symm v) :=
    fun v => conj_mem_lieAt fr v (hAZ v).1
  have hY : ∀ v, fr.P v * Z v * (fr.P v)⁻¹ ∈ lieAt V ((Formalism.L2.Host.tauPl D).symm v) :=
    fun v => conj_mem_lieAt fr v (hAZ v).2
  have hXe : ∀ v, oneP θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Av v * (fr.P v)⁻¹) 1 =
      UI.brg fr ((Pi.mulSingle v (expUJ (hAZ v).1) : (UI.instV fr).Ginf), 1) :=
    fun v => oneP_eq_brg θ hθ fr v _ _ (Matrix.exp_conj _ _ (fr.unit v))
  have hYe : ∀ v, oneP θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Z v * (fr.P v)⁻¹) 1 =
      UI.brg fr ((Pi.mulSingle v (expUJ (hAZ v).2) : (UI.instV fr).Ginf), 1) :=
    fun v => oneP_eq_brg θ hθ fr v _ _ (Matrix.exp_conj _ _ (fr.unit v))
  have hu' : u = ((Finset.univ : Finset (InfinitePlace D.host.F)).toList.map fun v =>
      (Pi.mulSingle v (expUJ (hAZ v).1) : (UI.instV fr).Ginf) * (Pi.mulSingle v (expUJ (hAZ v).2) : (UI.instV fr).Ginf)).prod := by
    have e : ∀ v : InfinitePlace D.host.F, ((Pi.mulSingle v (expUJ (hAZ v).1) : (UI.instV fr).Ginf) *
        (Pi.mulSingle v (expUJ (hAZ v).2) : (UI.instV fr).Ginf)) = (Pi.mulSingle v (expUJ (hAZ v).1 * expUJ (hAZ v).2) : (UI.instV fr).Ginf) :=
      fun v => (Pi.mulSingle_mul _ _ _).symm
    refine Eq.trans ?_ (congrArg List.prod (List.map_congr_left fun v _ => e v)).symm
    funext w
    refine Eq.trans ?_ (list_prod_mulSingle (M := fun w : InfinitePlace (UI.instV fr).F => Formalism.REAL.UJ ((UI.instV fr).ε w))
      (fun v => expUJ (hAZ v).1 * expUJ (hAZ v).2) _ (Finset.nodup_toList _) w).symm
    refine Eq.trans ?_ (if_pos (Finset.mem_toList.2 (Finset.mem_univ _))).symm
    exact Subtype.ext (Units.ext (hu w))
  have hfac : UI.brg fr (u, 1) = ((Finset.univ : Finset (InfinitePlace D.host.F)).toList.map fun v =>
      oneP θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Av v * (fr.P v)⁻¹) 1 *
        oneP θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Z v * (fr.P v)⁻¹) 1).prod := by
    have e1 : ((u, 1) : (UI.instV fr).GA) = MonoidHom.inl (UI.instV fr).Ginf (UI.instV fr).Gf u := rfl
    rw [e1, hu']
    refine (map_prod_pairs ((UI.brg fr : (UI.instV fr).GA →* GA D V).comp (MonoidHom.inl _ _)) _
      (fun v => (Pi.mulSingle v (expUJ (hAZ v).1) : (UI.instV fr).Ginf))
      (fun v => (Pi.mulSingle v (expUJ (hAZ v).2) : (UI.instV fr).Ginf))).trans ?_
    refine congrArg List.prod (List.map_congr_left fun v _ => ?_)
    rw [hXe v, hYe v]
    rfl
  rw [hfac]
  refine (lip_list θ A φ c hL (fun v => (Formalism.L2.Host.tauPl D).symm v) (fun v => fr.P v * Av v * (fr.P v)⁻¹)
    (fun v => fr.P v * Z v * (fr.P v)⁻¹) hX hY _ y).trans (le_of_eq ?_)
  rw [Finset.sum_map_toList]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  have hPv : fr.P v = (A.fr ((Formalism.L2.Host.tauPl D).symm v))⁻¹ := by
    have h := hP ((Formalism.L2.Host.tauPl D).symm v)
    rwa [Equiv.apply_symm_apply] at h
  simp only [hPv, conj_back _ _ (A.fr_unit _)]
  rfl

end GlobalTheory.RealMove

end
