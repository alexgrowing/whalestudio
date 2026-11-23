import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MiStar2OfAnchored
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateVectorCentralTwistStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomRelationOfPinStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCrdHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomHypothesisMatchingCentral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateVectorPairFormStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PostOnMemEEatOfCenter
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodBoundIff
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.AtReal

open Formalism.IndefR.Links

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}

theorem cols_heq {Df Df' : DefSide Bs} (hDf : Df = Df') {Dc : DefCols Df} {Dc' : DefCols Df'} (hD : HEq Dc Dc')
    {m : Dc.Mem} {m' : Dc'.Mem} (hm : HEq m m') :
    Dc.a m = Dc'.a m' ∧ (∀ v, HEq (Dc.Xc m v) (Dc'.Xc m' v)) ∧
      ∀ t (x : Fin (Dc.a m) → K) (x' : Fin (Dc'.a m') → K) (F : Fin (Df.nV t) → K) (F' : Fin (Df'.nV t) → K),
        HEq x x' → HEq F F' → Dc.Pt m t x F = Dc'.Pt m' t x' F' := by
  subst hDf
  obtain rfl := eq_of_heq hD
  obtain rfl := eq_of_heq hm
  refine ⟨rfl, fun v => HEq.rfl, fun t x x' F F' hx hF => ?_⟩
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hF
  rfl

theorem cols_mem {Df Df' : DefSide Bs} (hDf : Df = Df') {Dc : DefCols Df} {Dc' : DefCols Df'} (hD : HEq Dc Dc')
    (m : Dc.Mem) : ∃ m' : Dc'.Mem, HEq m m' := by
  subst hDf
  obtain rfl := eq_of_heq hD
  exact ⟨m, HEq.rfl⟩

end Gen

theorem heq_fin {α : Type} {n n' : ℕ} (h : n = n') (x : Fin n → α) : ∃ x' : Fin n' → α, HEq x x' := by
  subst h; exact ⟨x, HEq.rfl⟩

theorem heq_fin' {α : Type} {n n' : ℕ} (h : n = n') (x' : Fin n' → α) : ∃ x : Fin n → α, HEq x x' := by
  subst h; exact ⟨x', HEq.rfl⟩

theorem heq_mat {n n' : ℕ} (h : n = n') (M' : Matrix (Fin n') (Fin n') ℂ) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, HEq M M' := by
  subst h; exact ⟨M', HEq.rfl⟩

theorem heq_mulVec {n n' : ℕ} (h : n = n') {M : Matrix (Fin n) (Fin n) ℂ} {M' : Matrix (Fin n') (Fin n') ℂ}
    (hM : HEq M M') {x : Fin n → ℂ} {x' : Fin n' → ℂ} (hx : HEq x x') : HEq (M.mulVec x) (M'.mulVec x') := by
  subst h; obtain rfl := eq_of_heq hM; obtain rfl := eq_of_heq hx; rfl

theorem heq_fnorm {n n' : ℕ} (h : n = n') {Y : Matrix (Fin n) (Fin n) ℂ} {Y' : Matrix (Fin n') (Fin n') ℂ}
    (hY : HEq Y Y') {x : Fin n → ℂ} {x' : Fin n' → ℂ} (hx : HEq x x') : fnorm Y x = fnorm Y' x' := by
  subst h; obtain rfl := eq_of_heq hY; obtain rfl := eq_of_heq hx; rfl

theorem heq_cpt {K : Type} [Field K] (σ : K →+* ℂ) {n n' : ℕ} (h : n = n') {x : Fin n → K} {x' : Fin n' → K}
    (hx : HEq x x') : HEq (cpt σ x) (cpt σ x') := by
  subst h; obtain rfl := eq_of_heq hx; rfl

theorem heq_cjv (s : Bool) {n n' : ℕ} (h : n = n') {x : Fin n → ℂ} {x' : Fin n' → ℂ}
    (hx : HEq x x') : HEq (Formalism.L2.SG.JoinSI.cjv s x) (Formalism.L2.SG.JoinSI.cjv s x') := by
  subst h; obtain rfl := eq_of_heq hx; rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem dc_heq (W : RealPack ex) : HEq (W.Q.F.fc (cxW W).zs).Dc W.P.Dc :=
  (congr_arg_heq W.Dcf W.Q.zs).trans (heq_of_eq W.Q.dc)

theorem df_eq (W : RealPack ex) : (W.Q.F.fc (cxW W).zs).Df1 = W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs :=
  congrArg (W.P.A3.side3 W.P.Ps W.P.ψs) W.Q.zs

theorem mem_word (W : RealPack ex) (m : (W.Q.F.fc (cxW W).zs).Dc.Mem) : ∃ u, HEq m (W.P.I.wU u) := by
  obtain ⟨m', hm⟩ := cols_mem (df_eq W) (dc_heq W) m
  refine ⟨W.Q.wdD m', ?_⟩
  rw [W.Q.wU_wdD]; exact hm

end GlobalTheory.MiTop.AtReal

namespace GlobalTheory.MiTop.AtReal

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem anchor_word (W : RealPack ex) (z : GA D (D.sp.Y 0)) (u : D.what₂.Word) (d : BotDat W u) (v : (W.Q.Rl.MY 0).Vec)
    (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (c : W.P.T → ℂ) (hR : BotRel W z d)
    (hA : (∀ φ, ∃ C, IsCol W u C φ) ∧ (∀ T ∈ ThetaLiftSpaceZero W, ∀ C, ∃ b, IsPair W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b) ∧ ∃ (φ : D.what₂.Mu u) (C : _) (b : ℂ), ∃ T ∈ ThetaLiftSpaceZero W, IsCol W u C φ ∧ IsPair W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b ∧ b ≠ 0)
    (hr : 0 < r) (hU : ∀ φ, ‖U φ‖ = r * ‖φ‖) (hRel : d.Rel U c)
    (hrow : ∀ t (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL), rowAt W t F ∈ ThetaLiftSpaceZero W) :
    ∃ (R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u) (p b₀ : ℂ), p ≠ 0 ∧ b₀ ≠ 0 ∧
      ∀ t (φ : D.what₂.Mu u) (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL)
        (F' : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL), HEq F F' → ∀ C b, IsCol W u C (R (U φ)) →
        IsPair W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (rowAt W t F' (PiTensorProduct.tprod ℂ v)) C b →
        c t * D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F)) * b₀ = p * b := by
  obtain ⟨R, hR⟩ := hR
  obtain ⟨-, -, φ₁, C₀, b₀, T₀, hT₀, hC₀, hP₀, hb₀⟩ := hA
  have hinj : Function.Injective U := by
    rw [injective_iff_map_eq_zero]
    intro φ h
    have h1 := hU φ
    rw [h, norm_zero] at h1
    exact norm_eq_zero.1 ((mul_eq_zero.1 h1.symm).resolve_left hr.ne')
  obtain ⟨φ₀, hφ₀⟩ := LinearMap.injective_iff_surjective.1 hinj (R.symm φ₁)
  have hC₁ : IsCol W u C₀ (R (U φ₀)) := by rw [hφ₀, LinearIsometryEquiv.apply_symm_apply]; exact hC₀
  obtain ⟨p, hp⟩ := hRel T₀ hT₀
  refine ⟨R, p φ₀, b₀, fun h0 => hb₀ ?_, hb₀, fun t φ F F' hF C b hC hb => ?_⟩
  · obtain ⟨F, hF⟩ := heq_fin' (α := D.what₂.LL)
      (congrArg (fun Df => DefSide.nV Df W.P.A3.A.μ0) (df_eq W)).symm (fun _ => 0)
    have h1 := hp φ₀ φ₀ W.P.A3.A.μ0 F _ hF 1 0 (by rw [h0, mul_zero, zero_mul, add_zero])
    have h2 := hR (U φ₀) (U φ₀) T₀ hT₀ T₀ hT₀ 1 0
      (fun y w => by have h3 := h1 y w; rw [zero_mul] at h3 ⊢; exact h3) _ C₀ C₀ b₀ b₀ hC₁ hC₁ hP₀ hP₀
    rwa [one_mul, zero_mul, add_zero] at h2
  · have h1 := hp φ₀ φ t F F' hF
      (c t * D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F))) (-p φ₀) (by ring)
    have h2 := hR (U φ₀) (U φ) T₀ hT₀ _ (hrow t F') _ _ h1 _ C₀ C b₀ b hC₁ hC hP₀ hb
    linear_combination h2

end GlobalTheory.MiTop.AtReal

namespace GlobalTheory.MiTop

open Formalism.IndefR.Links GlobalTheory.MiTop.AtReal

set_option maxHeartbeats 1000000 in

theorem miStar2_at_realisation : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → (∀ t F, (cxW W).Θ t ((cxW W).jR t (W.Q.F.eV (cxW W).zs t F)) ∈ (cxW W).EEl true) → Joint W → PuNZ D → (cxW W).MIstar2 (W.Q.F.eV (cxW W).zs) W.Q.sEE := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB hΘ hJ hPu
  classical
  obtain ⟨z, hzf, hzc, hw⟩ := hJ
  choose d U r c hpin hr hUn hUC hRel using hw
  obtain ⟨V₀, hV₀⟩ := GlobalTheory.MiTop.exists_isShift_of_center W hB z hzf hzc
  have hMt := GlobalTheory.MiTop.botHyp_match W hB
  have hS : parB (Ptw D) (min 0 D.R.m) = parB (Ptw D) 0 := by simp
  obtain ⟨v, hv⟩ := GlobalTheory.Core.Mi.exists_conjVec hDS D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) hS hMt.2.1 hB.gap hB.idE
  obtain ⟨κ, hκ, hPF⟩ := GlobalTheory.T.conjugate_vector_pair_form hDS hCR W hB v hv
  have hCC := GlobalTheory.MiTop.colCrd_holds W
  have hrow : ∀ t (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL), rowAt W t F ∈ ThetaLiftSpaceZero W :=
    fun t F => hMt.2.2.2.2.2 _ (hΘ t F)
  have hanc := fun u => GlobalTheory.T.conjugate_vector_central_twist hDS hCR W hB hPu z hzf hzc v hv u
  have hword := fun u => anchor_word W z u (d u) v (U u) (r u) (c u)
    (GlobalTheory.T.bottom_relation_of_pin hDS hCR W hB z hzf hzc u (d u) (hpin u)) (hanc u) (hr u) (hUn u) (hRel u) hrow
  choose R p b₀ hp hb₀ hid using hword
  have key : ∀ m : (W.Q.F.fc (cxW W).zs).Dc.Mem, ∃ (Um : Matrix (Fin ((W.Q.F.fc (cxW W).zs).Dc.a m)) (Fin ((W.Q.F.fc (cxW W).zs).Dc.a m)) ℂ) (cm : W.P.A3.fam3.base3.Tup → ℂ),
      (∀ x, fnorm ((W.Q.F.fc (cxW W).zs).Dc.Xc m W.P.A3.fam3.base3.v0) (Um.mulVec x) = fnorm ((W.Q.F.fc (cxW W).zs).Dc.Xc m W.P.A3.fam3.base3.v0) x) ∧
      (∀ t, cm t ≠ 0) ∧ (∀ w (k : D.what₂.LL), W.P.A3.fam3.base3.v0.embedding k = cm ((cxW W).μ w) / cm W.P.A3.fam3.base3.μ0 → vw w k = 0) ∧
      ∃ pp bb : ℂ, pp ≠ 0 ∧ bb ≠ 0 ∧ ∀ t (φ : Fin ((W.Q.F.fc (cxW W).zs).Dc.a m) → D.what₂.LL) (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL),
        cm t * W.P.A3.fam3.base3.v0.embedding ((W.Q.F.fc (cxW W).zs).Dc.Pt m t φ F) * bb =
          pp * ⟪W.Q.sEE (Tw.map (Formalism.L2.SG.JoinSI.twQ W.P) V₀ ((cxW W).Θ t ((cxW W).jR t (W.Q.F.eV (cxW W).zs t F)))), (W.Q.F.fc (cxW W).zs).Sp.Pu m (Um.mulVec (cpt W.P.A3.fam3.base3.v0.embedding φ))⟫_ℂ := by
    intro m
    obtain ⟨u, hm⟩ := mem_word W m
    obtain ⟨ha, hXc, hPt⟩ := cols_heq (df_eq W) (dc_heq W) hm
    obtain ⟨hbij, hrat, r', hr', hnorm⟩ := hCC u
    let s := Formalism.L2.SG.JoinSI.twQ W.P
    let cL : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) →ₗ[ℂ] D.what₂.Mu u :=
      { toFun := colC W u
        map_add' := fun x y => by simp only [colC, Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun a x => by simp only [colC, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply] }
    let eC : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) ≃ₗ[ℂ] D.what₂.Mu u := LinearEquiv.ofBijective cL hbij
    have heC : ∀ x, eC x = colC W u x := fun x => rfl
    let A : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u := ((r u : ℂ))⁻¹ • (((R u).toLinearEquiv : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) ∘ₗ U u)
    have hAap : ∀ φ, A φ = R u (U u (((r u : ℂ))⁻¹ • φ)) := fun φ => by
      show ((r u : ℂ))⁻¹ • R u (U u φ) = _
      rw [map_smul, map_smul]
    have hA : ∀ φ, ‖A φ‖ = ‖φ‖ := fun φ => by
      show ‖((r u : ℂ))⁻¹ • R u (U u φ)‖ = ‖φ‖
      rw [norm_smul, LinearIsometryEquiv.norm_map, hUn u, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hr u).le,
        ← mul_assoc, inv_mul_cancel₀ (hr u).ne', one_mul]
    let f' : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) →ₗ[ℂ] (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) :=
      { toFun := fun y => Formalism.L2.SG.JoinSI.cjv s (eC.symm (A (eC (Formalism.L2.SG.JoinSI.cjv s y))))
        map_add' := fun x y => by simp only [Formalism.L2.SG.JoinSI.cjv_add, map_add]
        map_smul' := fun a x => by
          simp only [Formalism.L2.SG.JoinSI.cjv_smul, map_smul, Formalism.IndefR.Links.cj_cj, RingHom.id_apply] }
    obtain ⟨M, hM⟩ := heq_mat ha (LinearMap.toMatrix' f')
    have hcj : ∀ a : D.what₂.LL, W.P.A3.fam3.base3.v0.embedding a = Formalism.IndefR.Links.cj s (D.what₂.embLL a) :=
      Formalism.L2.SG.JoinSI.twist_of_realT W.Q
    have hr0 : ((r u : ℂ))⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 (hr u).ne')
    refine ⟨M, fun t => Formalism.IndefR.Links.cj s (c u t), ?_, fun t => (map_ne_zero _).2 ((hUC u).1 t), ?_,
      Formalism.IndefR.Links.cj s (p u), Formalism.IndefR.Links.cj s (κ * ((r u : ℂ))⁻¹ * b₀ u), (map_ne_zero _).2 (hp u),
      (map_ne_zero _).2 (mul_ne_zero (mul_ne_zero hκ hr0) (hb₀ u)), ?_⟩
    · intro x
      obtain ⟨x', hx⟩ := heq_fin ha x
      rw [heq_fnorm ha (hXc _) (heq_mulVec ha hM hx), heq_fnorm ha (hXc _) hx, LinearMap.toMatrix'_mulVec]
      show fnorm _ (Formalism.L2.SG.JoinSI.cjv s (eC.symm (A (eC (Formalism.L2.SG.JoinSI.cjv s x'))))) = _
      conv_rhs => rw [← Formalism.L2.SG.JoinSI.cjv_cjv s x']
      rw [hnorm, hnorm, ← heC, ← heC, LinearEquiv.apply_symm_apply, hA]
    · intro w k hk
      apply (hUC u).2 w k
      rw [hcj, ← map_div₀] at hk
      exact (Formalism.IndefR.Links.cj s).injective hk
    · intro t φ F
      obtain ⟨φ', hφ⟩ := heq_fin ha φ
      have hnV : (W.Q.F.fc (cxW W).zs).Df1.nV t = (W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t :=
        congrArg (fun Df => DefSide.nV Df t) (df_eq W)
      obtain ⟨F'', hF⟩ := heq_fin hnV F
      rw [hPt t φ φ' F F'' hφ hF, hcj, hB.hyp.2.2.1 u t (hB.used t) φ' F'']
      set ψ := D.jN u (W.P.I.eNu u φ') with hψ
      have hvec : HEq (M.mulVec (cpt W.P.A3.fam3.base3.v0.embedding φ)) (Formalism.L2.SG.JoinSI.cjv s (eC.symm (A ψ))) := by
        refine (heq_mulVec ha hM (heq_cpt _ ha hφ)).trans (heq_of_eq ?_)
        rw [LinearMap.toMatrix'_mulVec]
        show Formalism.L2.SG.JoinSI.cjv s (eC.symm (A (eC (Formalism.L2.SG.JoinSI.cjv s (cpt W.P.A3.fam3.base3.v0.embedding φ'))))) = _
        have e1 : Formalism.L2.SG.JoinSI.cjv s (cpt W.P.A3.fam3.base3.v0.embedding φ') = cpt D.what₂.embLL φ' := by
          funext i
          show Formalism.IndefR.Links.cj s (W.P.A3.fam3.base3.v0.embedding (φ' i)) = D.what₂.embLL (φ' i)
          rw [hcj, Formalism.IndefR.Links.cj_cj]
        rw [e1, heC, hrat]
      have hx' : HEq (eC.symm (A ψ)) (Formalism.L2.SG.JoinSI.cjv s (M.mulVec (cpt W.P.A3.fam3.base3.v0.embedding φ))) := by
        have h2 := heq_cjv s ha hvec
        rw [Formalism.L2.SG.JoinSI.cjv_cjv] at h2
        exact h2.symm
      rw [← Formalism.L2.SG.JoinSI.cjv_cjv s (M.mulVec _)]
      obtain ⟨T, hTc⟩ := (hanc u).1 (colC W u (eC.symm (A ψ)))
      obtain ⟨b, hb⟩ := (hanc u).2.1 (rowAt W t F) (hrow t F) T
      have hE := (hV₀.2.2 _ (hΘ t F))
      have hPair : IsPair W u (show GA D (D.sp.Y 0) from W.Q.tS)
          (rowOf W (Tw.out (s := Formalism.L2.SG.JoinSI.twQ W.P) (E := W.Q.Rl.HE.H) (Tw.map (E := W.Q.Rl.HE.H) (F := W.Q.Rl.HE.H) s V₀ ((cxW W).Θ t ((cxW W).jR t (W.Q.F.eV (cxW W).zs t F))))) (PiTensorProduct.tprod ℂ v)) T b := by
        obtain ⟨φL, hφL, hbL⟩ := hb
        refine ⟨φL, hφL.trans (Filter.EventuallyEq.of_eq ?_), hbL⟩
        funext x
        refine Eq.trans ?_ (congrFun (hV₀.1 (W.Q.Rl.Th t (W.Q.Rl.jX t (W.Q.F.eV (cxW W).zs t F))) (PiTensorProduct.tprod ℂ v))
          ((iotaX W.S.X W.Q.instEq).symm x * (show GA D (D.sp.Y 0) from W.Q.tS))).symm
        refine congrArg (rowAt W t F (PiTensorProduct.tprod ℂ v)) ?_
        show (iotaX W.S.X W.Q.instEq).symm x * (z * (show GA D (D.sp.Y 0) from W.Q.tS)) =
          (iotaX W.S.X W.Q.instEq).symm x * (show GA D (D.sp.Y 0) from W.Q.tS) * z
        rw [mul_assoc, Subgroup.mem_center_iff.1 hzc]
      have hpair := hPF (Tw.map (E := W.Q.Rl.HE.H) (F := W.Q.Rl.HE.H) s V₀ ((cxW W).Θ t ((cxW W).jR t (W.Q.F.eV (cxW W).zs t F))))
        hE u m hm _ _ hx' T b hTc hPair
      refine Eq.trans ?_ (congrArg (fun a => Formalism.IndefR.Links.cj s (p u) * a) hpair.symm)
      show Formalism.IndefR.Links.cj s (c u t) * _ * _ = Formalism.IndefR.Links.cj s (p u) * Formalism.IndefR.Links.cj s (κ * b)
      have hcolR : IsCol W u T (R u (U u (((r u : ℂ))⁻¹ • ψ))) := by
        rw [← hAap]; unfold IsCol at hTc ⊢; rw [hTc, ← heC, LinearEquiv.apply_symm_apply]
      have hid' := hid u t (((r u : ℂ))⁻¹ • ψ) F'' F hF.symm T b hcolR hb
      rw [GlobalTheory.ExpAtTypePrimes.perCol_smul] at hid'
      rw [← map_mul, ← map_mul, ← map_mul]
      congr 1
      linear_combination κ * hid'
  choose Um cm hUm hc0 hcU hAn using key
  exact GlobalTheory.MiTop.miStar2_of_anchored (cxW W) (W.Q.F.eV (cxW W).zs) W.Q.sEE (Tw.map (E := W.Q.Rl.HE.H) (F := W.Q.Rl.HE.H) (Formalism.L2.SG.JoinSI.twQ W.P) V₀) Um cm
    ⟨fun e he => ⟨hV₀.2.2 (Tw.out (s := Formalism.L2.SG.JoinSI.twQ W.P) (E := W.Q.Rl.HE.H) e) he, hV₀.2.1 (Tw.out (s := Formalism.L2.SG.JoinSI.twQ W.P) (E := W.Q.Rl.HE.H) e)⟩, hUm⟩ hAn ⟨hc0, hcU⟩

end GlobalTheory.MiTop

end
