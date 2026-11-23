import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStru
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FockPlace

open GlobalTheory.FinTranslate GlobalTheory.FockCompare

variable {D : D7}

theorem finPart_eInf_smul (a : AE D) : finPart D (eInf D • a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add a b ha hb => rw [smul_add, RingHom.map_add, ha, hb, add_zero]
  | tmul a x =>
    rw [TensorProduct.smul_tmul']
    show (sndA D.host.F (eInf D • a)) ⊗ₜ[D.host.F] x = 0
    rw [show sndA D.host.F (eInf D • a) = 0 from zero_mul _, TensorProduct.zero_tmul]

theorem infPart_eInf_smul (a : AE D) : infPart D (eInf D • a) = infPart D a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [smul_zero]
  | add a b ha hb => rw [smul_add, RingHom.map_add, ha, hb, RingHom.map_add]
  | tmul a x =>
    rw [TensorProduct.smul_tmul']
    show (fstA D.host.F (eInf D • a)) ⊗ₜ[D.host.F] x = (fstA D.host.F a) ⊗ₜ[D.host.F] x
    rw [show fstA D.host.F (eInf D • a) = fstA D.host.F a from one_mul _]

theorem infPart_eq_zero {θ : InfFam D} (hθ : IsInfFam θ) {a : AE D} (h : ∀ τ, θ τ (infPart D a) = 0) :
    infPart D a = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have := hσ.ext (eInf D • a) (finPart_eInf_smul a) fun τ => by rw [infPart_eInf_smul, h]
  rw [← infPart_eInf_smul, this, map_zero]

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem exists_extension (hψ : IsStdChar D ψ (-1)) (F₀ : (WO S T → ℂ) → (WO S T → ℂ))
    (hlin : ∀ (c : ℂ) f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → F₀ (c • f + g) = c • F₀ f + F₀ g)
    (hcomm : ∀ u : WO S T, u.map (infPart D) = 0 → ∀ f, IsThetaFunO ψ S T f →
      F₀ (heisO ψ S T u f) = heisO ψ S T u (F₀ f)) :
    ∃ F : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → F f = F₀ f) ∧
      ∀ u : WO S T, u.map (infPart D) = 0 → ∀ f, F (heisO ψ S T u f) = heisO ψ S T u (F f) := by
  let U : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
      zero_mem' := GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
  have h0 : F₀ 0 = 0 := by
    have := hlin 1 0 0 GlobalTheory.OrientedHeis.theta_zero GlobalTheory.OrientedHeis.theta_zero
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  let L₀ : U →ₗ[ℂ] (WO S T → ℂ) :=
    { toFun := fun g => F₀ g
      map_add' := fun a b => by
        have := hlin 1 a b a.2 b.2
        rwa [one_smul, one_smul] at this
      map_smul' := fun c a => by
        have := hlin c a 0 a.2 GlobalTheory.OrientedHeis.theta_zero
        rwa [add_zero, h0, add_zero] at this }
  obtain ⟨L, hL⟩ := L₀.exists_extend
  have hL' : ∀ g, IsThetaFunO ψ S T g → L g = F₀ g := fun g hg => LinearMap.congr_fun hL ⟨g, hg⟩
  have hr : ∀ w : WO S T, (eInf D • w).map (finPart D) = 0 := fun w =>
    Matrix.ext fun i j => finPart_eInf_smul (w i j)
  have hf : ∀ w : WO S T, (w - eInf D • w).map (infPart D) = 0 := fun w => Matrix.ext fun i j => by
    show infPart D (w i j - eInf D • w i j) = 0
    rw [RingHom.map_sub, infPart_eInf_smul, sub_self]
  let F : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    LinearMap.pi fun w => (LinearMap.proj (eInf D • w) : (WO S T → ℂ) →ₗ[ℂ] ℂ) ∘ₗ L ∘ₗ heisL S T ψ (w - eInf D • w)
  have hF : ∀ g w, F g w = L (heisO ψ S T (w - eInf D • w) g) (eInf D • w) := fun _ _ => rfl
  refine ⟨F, fun f h => funext fun w => ?_, fun u hu f => funext fun w => ?_⟩
  · rw [hF, hL' _ (isThetaFunO_heisO hψ.1.1 hψ.1.2.1 h (hf w)), hcomm _ (hf w) f h, heisO,
      symplOH_real_fin (hf w) (hr w), ψ.map_zero_eq_one, one_mul, add_sub_cancel]
  · have e : symplOH S T w u = symplOH S T (w - eInf D • w) u := by
      conv_lhs => rw [← sub_add_cancel w (eInf D • w)]
      rw [symplOH_add_left, symplOH_real_fin hu (hr w), add_zero]
    rw [hF, heisO_heisO, map_smul, heisO, hF, smul_add, smul_fin hu, add_zero, e, add_sub_right_comm]
    rfl

theorem eq_zero_of_fixed (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) {g : WO S T → ℂ}
    (hg : ∀ y : WO S T, y.map (finPart D) = 0 → (∀ τ', τ' ≠ τ → ∀ a b, θ τ' (infPart D (y a b)) = 0) →
      heisO ψ S T y g = g) : g = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨om, J, h1, h2, -, -, -, h3⟩ := GlobalTheory.OrientedRealForm.exists_real_form D ψ θ S T sS sT hψ hθ hS hT
  let z : RW T S := fun τ' _ _ => if τ' = τ then 1 else 0
  have hz : z ≠ 0 := fun h => by simpa [z] using congrFun (congrFun (congrFun h τ) i) j
  have hz' : ∀ τ', τ' ≠ τ → z τ' = 0 := fun τ' h => by
    funext a b
    simp [z, h]
  have hp := h3 z hz
  have key : ∀ x : RW T S, (∀ τ', τ' ≠ τ → x τ' = 0) → heisO ψ S T (iotaW σ T S x) g = g := fun x hx =>
    hg _ (hσ.real_iota T S x) fun τ' h a b =>
      (congrFun (congrFun (congrFun (hσ.pi_iota T S x) τ') a) b).trans (by rw [hx τ' h]; rfl)
  have a1 : ∀ τ', τ' ≠ τ → ((om z (J z))⁻¹ • z) τ' = 0 := fun τ' h => by rw [Pi.smul_apply, hz' τ' h, smul_zero]
  have a2 : ∀ τ', τ' ≠ τ → (J z) τ' = 0 := fun τ' h => by
    rw [h2, hz' τ' h]
    show Complex.I • (sT τ' * (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ) * sS τ') = 0
    rw [Matrix.mul_zero, Matrix.zero_mul, smul_zero]
  have a3 := key ((om z (J z))⁻¹ • z + J z) fun τ' h => by rw [Pi.add_apply, a1 τ' h, a2 τ' h, add_zero]
  have e := heisO_heisO S T ψ (iotaW σ T S ((om z (J z))⁻¹ • z)) (iotaW σ T S (J z)) g
  rw [map_add] at a3
  rw [key _ a2, key _ a1, h1 _ _ (hσ.real_iota T S _), hσ.pi_iota, hσ.pi_iota, map_smul, LinearMap.smul_apply,
    smul_eq_mul, inv_mul_cancel₀ hp.ne', Complex.ofReal_one, mul_one, Complex.exp_neg, Complex.exp_pi_mul_I] at e
  erw [a3] at e
  funext w
  have := congrFun e w
  rw [Pi.smul_apply, smul_eq_mul] at this
  show g w = 0
  linear_combination (1 / 2 : ℂ) * this

theorem isSBHalf_halfInd (e : AE D) (Λ : AddSubgroup (WO S T)) : IsSBHalf e Λ (halfInd e Λ) := by
  have h : ∀ t, halfInd e Λ t ≠ 0 → t ∈ Λ ∧ IsHalf e t := fun t ht => by
    by_contra hn
    exact ht (if_neg hn)
  refine ⟨fun t ht => (h t ht).2, 1, one_pos, fun u hu hu' t => ?_, fun t ht => by rw [one_smul]; exact (h t ht).1⟩
  rw [one_smul]
  unfold halfInd
  refine if_congr (and_congr (Λ.add_mem_cancel_right hu) (forall₂_congr fun i j => ?_)) rfl rfl
  rw [Matrix.add_apply, mul_add, hu' i j, add_left_inj]

theorem placeModel_eq_zero (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {e : AE D} {Λ : AddSubgroup (WO S T)} (hΛ : ∀ u ∈ Λ, (u : WO S T).map (infPart D) = 0) {c : ℂ} {f₀ : WO S T → ℂ}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm)
    {x : WO S T} (hx : IsHalf e x ∨ IsHalf (cA D e) x) (hx' : x.map (infPart D) ≠ 0)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) : Tm Φ = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have h1 : ∃ i j τ, θ τ (infPart D (x i j)) ≠ 0 := by
    by_contra! h
    exact hx' (Matrix.ext fun i j => infPart_eq_zero hθ (h i j))
  obtain ⟨i, j, τ, h1⟩ := h1
  have hc : θ τ (infPart D (cA D e)) = starRingEnd ℂ (θ τ (infPart D e)) := comp_cA hθ τ e
  have h2 : θ τ (infPart D (cA D e)) = 1 := by
    rcases hx with hx | hx
    · have := congrArg (fun a => θ τ (infPart D a)) (hx i j)
      simp only [RingHom.map_mul] at this
      rw [hc, (mul_eq_right₀ h1).1 this, map_one]
    · have := congrArg (fun a => θ τ (infPart D a)) (hx i j)
      simp only [RingHom.map_mul] at this
      exact (mul_eq_right₀ h1).1 this
  refine eq_zero_of_fixed hψ hθ hS hT τ i j fun y hy hy' => ?_
  have h3 : IsHalf (cA D e) y := fun a b => by
    have hf : finPart D (y a b) = 0 := congrFun (congrFun hy a) b
    rw [← sub_eq_zero]
    refine hσ.ext _ (by rw [RingHom.map_sub, RingHom.map_mul, hf, mul_zero, sub_zero]) fun τ' => ?_
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_mul]
    by_cases h : τ' = τ
    · rw [h, h2, one_mul, sub_self]
    · rw [hy' τ' h, mul_zero, sub_zero]
  rw [← hTm.modul Φ hΦ y h3]
  congr 1
  funext t
  by_cases ht : Φ t = 0
  · rw [ht, mul_zero]
  obtain ⟨-, k, hk, -, h4⟩ := hΦ
  have h5 : t.map (infPart D) = 0 := Matrix.ext fun a b => infPart_eq_zero hθ fun τ' => by
    have h6 : infPart D (k • t a b) = 0 := congrFun (congrFun (hΛ _ (h4 t ht)) a) b
    have h7 := congrArg (θ τ') h6
    have h9 : θ τ' (infPart D (k • t a b)) = k • θ τ' (infPart D (t a b)) :=
      ((θ τ').comp (infPart D)).toAddMonoidHom.map_nsmul k (t a b)
    rw [h9, RingHom.map_zero, nsmul_eq_mul] at h7
    exact (mul_eq_zero.1 h7).resolve_left (Nat.cast_ne_zero.2 hk.ne')
  have h8 : symplO S T t y = 0 :=
    Prod.ext (GlobalTheory.OrientedHeis.fst_symplO (Or.inl h5)) (GlobalTheory.OrientedHeis.snd_symplO (Or.inr hy))
  rw [h8, ψ.map_zero_eq_one, one_mul]

theorem isThetaAt_map {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}
    (F : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hF : ∀ x, IsHalf e x ∨ IsHalf (cA D e) x → ∀ g, F (heisO ψ S T x g) = heisO ψ S T x (F g))
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (F f₀) Φ (F f) := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c (F f₀) (F ∘ₗ Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hT.trans Φ hΦ x hx, hF x (Or.inl hx)]
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hT.modul Φ hΦ y hy, hF y (Or.inr hy)]
      vac := by rw [LinearMap.comp_apply, hT.vac] }
  refine ⟨⟨_, hT'⟩, fun T₁ h₁ => ?_⟩
  have hh : ∀ x a b d, heisO ψ S T x (a + (b - d)) = heisO ψ S T x a + (heisO ψ S T x b - heisO ψ S T x d) :=
    fun x a b d => ((heisL S T ψ x).map_add _ _).trans (congrArg _ ((heisL S T ψ x).map_sub _ _))
  have h₂ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + (T₁ - F ∘ₗ Tm)) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sub_apply, hT.trans Φ hΦ x hx,
          h₁.trans Φ hΦ x hx, hT'.trans Φ hΦ x hx, hh]
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sub_apply, hT.modul Φ hΦ y hy,
          h₁.modul Φ hΦ y hy, hT'.modul Φ hΦ y hy, hh]
      vac := by rw [LinearMap.add_apply, LinearMap.sub_apply, hT.vac, h₁.vac, hT'.vac, sub_self, add_zero] }
  have e1 : f = Tm Φ := hall Tm hT
  have e2 : f = (Tm + (T₁ - F ∘ₗ Tm)) Φ := hall _ h₂
  rw [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, ← e1] at e2
  exact (sub_eq_zero.1 (left_eq_add.1 e2)).symm

theorem isThetaAt_pureTensorO (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {e : AE D} {Λ : AddSubgroup (WO S T)} (hΛ : ∀ u ∈ Λ, (u : WO S T).map (infPart D) = 0) {f₀ Φ f : WO S T → ℂ}
    (h₀ : IsThetaFunO ψ S T f₀) (hΦ : IsSBHalf e Λ Φ) (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 (pureTensorO ψ θ S T sS sT BS BT f₀ P) Φ
      (pureTensorO ψ θ S T sS sT BS BT f P) := by
  obtain ⟨F, hF, hF'⟩ := exists_extension hψ (fun g => pureTensorO ψ θ S T sS sT BS BT g P)
    (fun c f g hf hg => GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT c hf hg P)
    (fun u hu f hf => ((finite_translate D ψ θ S T hψ hθ f hf).2 u hu).2 sS BS sT BT P)
  have hf := GlobalTheory.GalLift.Vec.theta_of_thetaAt hψ hθ h h₀
  have e₀ : F f₀ = pureTensorO ψ θ S T sS sT BS BT f₀ P := hF f₀ h₀
  have e₁ : F f = pureTensorO ψ θ S T sS sT BS BT f P := hF f hf
  rw [← e₀, ← e₁]
  by_cases hx : ∀ x : WO S T, IsHalf e x ∨ IsHalf (cA D e) x → x.map (infPart D) = 0
  · exact isThetaAt_map F (fun x h => hF' x (hx x h)) h
  · push_neg at hx
    obtain ⟨x, hx, hx'⟩ := hx
    obtain ⟨Tm, hTm⟩ := h.1
    have a : f₀ = 0 := by
      rw [← hTm.vac, one_smul]
      exact placeModel_eq_zero hψ hθ hS hT hΛ hTm hx hx' (isSBHalf_halfInd e Λ)
    have b : f = 0 := (h.2 Tm hTm).trans (placeModel_eq_zero hψ hθ hS hT hΛ hTm hx hx' hΦ)
    subst a b
    rwa [map_zero]

theorem main : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D) (v f : SchDown ch.G t) (P : PolDown ch.G) (j : Fin D.R.m) (φ : WO (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j)) → ℂ), IsThetaFunO ch.W.ψ _ _ (v j) → IsLocVec ch.W (.mu t D.R.m j) e (v j) φ (f j) → IsThetaFunO ch.W.ψ _ _ (fockD ch.W t v P j) ∧ IsLocVec ch.W (.mu t D.R.m j) e (fockD ch.W t v P j) φ (fockD ch.W t f P j) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ t e v f P j φ hv h => ?_⟩⟩
  exact ⟨GlobalTheory.GalLift.Vec.theta_pureTensorO ch.W.ψ_std ch.W.θ_is _ _ _ _ hv (P j), h.1,
    isThetaAt_pureTensorO ch.W.ψ_std ch.W.θ_is (ch.W.cart_is (.grid D.R.m j) ⟨le_rfl, j.2.le⟩)
      (ch.W.cart_is (.grid D.R.m (j + 1)) ⟨le_rfl, j.2⟩) _ _ (fun _ hu => GlobalTheory.VacGood.infPart_latO hu) hv h.1 h.2 (P j)⟩

end GlobalTheory.FockPlace

end
