import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.Imports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionAutomorphySourceGroup
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatH

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace PositivityTheory.ThKW.Sw

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem symp_congr {ξ ξ' : E} {J J' : Matrix α α E} (h : ξ • J = ξ' • J') (K : Matrix β β E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.symp c ξ J K x y = GlobalTheory.WeilM.symp c ξ' J' K x y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  have h1 : ξ * J i k = ξ' * J' i k := congrFun (congrFun h i) k
  linear_combination (x i j * K j l * c (y k l)) * h1

theorem ug_le {ξ ξ' : E} {J J' : Matrix α α E} (h : ξ • J = ξ' • J') (hξ : IsUnit ξ') (hJ : IsUnit J'.det) :
    GlobalTheory.WeilM.UG c J' ≤ GlobalTheory.WeilM.UG c J := by
  intro g hg
  have hg' : (g : Matrix α α E)ᵀ * J' * (g : Matrix α α E).map c = J' := hg
  show (g : Matrix α α E)ᵀ * J * (g : Matrix α α E).map c = J
  rcases isEmpty_or_nonempty α with hα | hα
  · exact Subsingleton.elim _ _
  have hu : IsUnit ξ := by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_smul, Matrix.det_smul] at h1
    have h2 : IsUnit (ξ ^ Fintype.card α * J.det) := h1 ▸ (hξ.pow _).mul hJ
    exact (isUnit_pow_iff Fintype.card_ne_zero).1 (isUnit_of_mul_isUnit_left h2)
  refine hu.smul_left_cancel.1 ?_
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_smul, Matrix.smul_mul, hg']

theorem invT_of_inv {H : Subgroup (GL α E)} (u : GL α E) (b : H) (h : u.1 = (b⁻¹).1.1ᵀ) :
    (GlobalTheory.DualSwap.invT u).1 = b.1.1 := by
  have h1 : u = GlobalTheory.DualSwap.invT b.1 := Units.ext h
  rw [h1, GlobalTheory.DualSwap.invT_invT]

theorem invT_incl {H K : Subgroup (GL α E)} (hle : H ≤ K) (u : GL α E) (a : H) (h : u.1 = a.1.1) :
    (GlobalTheory.DualSwap.invT u).1 = ((Subgroup.inclusion hle a)⁻¹).1.1ᵀ := by
  have h1 : u = a.1 := Units.ext h
  rw [h1]
  rfl

def swapHom {G M : Type} [Group G] [Monoid M] {H K : Subgroup (GL α E)} (hle : H ≤ K) (om : G × K →* M) : H × G →* M :=
  om.comp ((MonoidHom.snd _ _).prod ((Subgroup.inclusion hle).comp (MonoidHom.fst _ _)))

theorem swapHom_apply {G M : Type} [Group G] [Monoid M] {H K : Subgroup (GL α E)} (hle : H ≤ K) (om : G × K →* M)
    (a : H) (g : G) : swapHom hle om (a, g) = om (g, Subgroup.inclusion hle a) := rfl

variable [Invertible (2 : R)]

def castD {ξ ξ' : E} {J J' : Matrix α α E} (h : ξ • J = ξ' • J') {K : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ J K) κ) : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ' J' K) κ where
  e := d.e
  form w w' := by rw [← symp_congr c h, d.form]

theorem castD_transD_e {ξ ξ' : E} {J J' : Matrix α α E} (h : ξ • J = ξ' • J') {K : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ K J) κ) (x : Matrix α β E) :
    (castD c h (GlobalTheory.WeilSchrodinger.transD c d)).e x = d.e xᵀ := rfl

theorem castD_transD_rho {ξ ξ' : E} {J J' : Matrix α α E} (h : ξ • J = ξ' • J') {K : Matrix β β E} {κ : Type}
    [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ K J) κ) (ψ : AddChar R ℂ) (x : Matrix α β E) :
    (castD c h (GlobalTheory.WeilSchrodinger.transD c d)).rho ψ x = d.rho ψ xᵀ := rfl

omit [Invertible (2 : R)] in
theorem symp_congr₂ {ξ ξ' : E} {J J' : Matrix β β E} (h : ξ • J = ξ' • J') (K : Matrix α α E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.symp c ξ K J x y = GlobalTheory.WeilM.symp c ξ' K J' x y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  have h1 : ξ * J j l = ξ' * J' j l := congrFun (congrFun h j) l
  linear_combination (x i j * K i k * c (y k l)) * h1

omit [Invertible (2 : R)] in
theorem ug_ge {ξ ξ' : E} {J J' : Matrix α α E} (h : ξ • J = ξ' • J') (hξ : IsUnit ξ') :
    GlobalTheory.WeilM.UG c J ≤ GlobalTheory.WeilM.UG c J' := by
  intro g hg
  have hg' : (g : Matrix α α E)ᵀ * J * (g : Matrix α α E).map c = J := hg
  show (g : Matrix α α E)ᵀ * J' * (g : Matrix α α E).map c = J'
  refine hξ.smul_left_cancel.1 ?_
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← h, Matrix.mul_smul, Matrix.smul_mul, hg']

omit [Invertible (2 : R)] [Fintype α] [DecidableEq α] in
theorem smul_dbl {ξ ξ' : E} {J J' : Matrix α α E} (h : ξ • J = ξ' • J') :
    ξ • GlobalTheory.WeilM.dbl J = ξ' • GlobalTheory.WeilM.dbl J' := by
  simp only [GlobalTheory.WeilM.dbl, Matrix.fromBlocks_smul, smul_zero, smul_neg, h]

def castD₂ {ξ ξ' : E} {J J' : Matrix β β E} (h : ξ • J = ξ' • J') {K : Matrix α α E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ' K J') κ) : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ K J) κ where
  e := d.e
  form w w' := by rw [symp_congr₂ c h, d.form]

theorem isUWeilSplit_cast₂ [TopologicalSpace R] [TopologicalSpace E] [IsModuleTopology R E] {C : GlobalTheory.WeilM.TestClass R}
    {ψ : AddChar R ℂ} {ξ ξ' : E} {J J' : Matrix β β E} (h : ξ • J = ξ' • J') {K : Matrix α α E} {κ : Type} [Fintype κ]
    {d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ' K J') κ} {χ : Eˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν]
    {Cy : Matrix β ν E} {om : GlobalTheory.WeilM.UG c J' →* Module.End ℂ ((κ → R) → ℂ)}
    (hle : GlobalTheory.WeilM.UG c J ≤ GlobalTheory.WeilM.UG c J') (hL : GlobalTheory.WeilM.IsLagr c J Cy)
    (H : GlobalTheory.WeilM.IsUWeilSplit c C ψ ξ' K J' d χ Cy om) :
    GlobalTheory.WeilM.IsUWeilSplit c C ψ ξ K J (castD₂ c h d) χ Cy (om.comp (Subgroup.inclusion hle)) :=
  ⟨hL, ⟨⟨fun g => H.2.1.pres (Subgroup.inclusion hle g), fun g => H.2.1.impl (Subgroup.inclusion hle g),
    fun g => H.2.1.adm (Subgroup.inclusion hle g)⟩, H.2.1.unit.comp _,
    H.2.1.cont.comp (continuous_subtype_val.subtype_mk _)⟩,
    fun l hl hinv p t hp => H.2.2 l hl hinv (Subgroup.inclusion hle p) t hp⟩

end Gen

section Swap

open Formalism.IndefR.DatumF GlobalTheory.DualSwap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def trW {m n : ℕ} : (WOF F E m n → ℂ) ≃ₗ[ℂ] (WOF F E n m → ℂ) where
  toFun f x := f xᵀ
  invFun f x := f xᵀ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem trW_trW {m n : ℕ} (f : WOF F E m n → ℂ) : trW (trW f) = f := rfl

def trAW {m n : ℕ} : WOF F E m n →+ WOF F E n m where
  toFun x := xᵀ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_trW {m n : ℕ} : Continuous (fun x : WOF F E m n => (xᵀ : WOF F E n m)) :=
  continuous_id.matrix_transpose

variable (σ : E →ₐ[F] E)

def dualG {n : ℕ} {J J' : Matrix (Fin n) (Fin n) E} (h : J'ᵀ * J = 1) : GAF σ J' →* GAF σ J :=
  (invT.comp (matHomF σ J')).codRestrict (HR (AF F) σ J) fun g =>
    invT_mem _ (J' := JR (AF F) J') (by
      rw [JR, JR, ← Matrix.transpose_map, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]) g.2

theorem matHom_dualG {n : ℕ} {J J' : Matrix (Fin n) (Fin n) E} (h : J'ᵀ * J = 1) (g : GAF σ J') :
    matHomF σ J (dualG σ h g) = invT (matHomF σ J' g) := rfl

theorem mt_dualG {n : ℕ} {J J' : Matrix (Fin n) (Fin n) E} (h : J'ᵀ * J = 1) (g : GAF σ J') :
    mtF σ J (dualG σ h g) = (mtF σ J' g⁻¹)ᵀ := rfl

theorem mt_dualG_inv {n : ℕ} {J J' : Matrix (Fin n) (Fin n) E} (h : J'ᵀ * J = 1) (g : GAF σ J') :
    mtF σ J (dualG σ h g)⁻¹ = (mtF σ J' g)ᵀ := rfl

theorem continuous_dualG {n : ℕ} {J J' : Matrix (Fin n) (Fin n) E} (h : J'ᵀ * J = 1) : Continuous (dualG σ h) :=
  (continuous_invT.comp continuous_subtype_val).subtype_mk _

theorem dualG_mem_GQ {n : ℕ} {J J' : Matrix (Fin n) (Fin n) E} (h : J'ᵀ * J = 1) {γ : GAF σ J'} (hγ : γ ∈ GQF σ J') :
    dualG σ h γ ∈ GQF σ J := by
  have hγ' : matHomF σ J' γ ∈ HFin (AF F) σ J' := hγ
  obtain ⟨g, hg, hgγ⟩ := hγ'
  have h2 : invT (matHomF σ J' γ) ∈ HFin (AF F) σ J := ⟨invT g, invT_mem _ h hg, by rw [bc_invT, hgγ]⟩
  exact h2

variable {nS nT : ℕ} {JS JS' : Matrix (Fin nS) (Fin nS) E} {JT JT' : Matrix (Fin nT) (Fin nT) E}
  (hS : JS'ᵀ * JS = 1) (hT : JT'ᵀ * JT = 1) (ξ₀ : E) (ψ : AddChar (AF F) ℂ)

omit [NumberField E] in
theorem dual_inv {n : ℕ} {J J' : Matrix (Fin n) (Fin n) E} (h : J'ᵀ * J = 1) : J⁻¹ = J'ᵀ ∧ J'⁻¹ = Jᵀ :=
  ⟨Matrix.inv_eq_left_inv h, Matrix.inv_eq_left_inv (by
    have := congrArg Matrix.transpose h
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this)⟩

include hS hT

theorem hO_tr (x y : WOF F E nS nT) : hOF σ JT' JS' xᵀ yᵀ = hOF σ JS JT x y := by
  unfold hOF
  rw [(dual_inv hT).2, (dual_inv hS).1, sum_sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  simp only [Matrix.transpose_apply]
  ring

theorem symplOH_tr (x y : WOF F E nS nT) : symplOHF σ JT' JS' ξ₀ xᵀ yᵀ = symplOHF σ JS JT ξ₀ x y := by
  unfold symplOHF symplOF
  rw [hO_tr σ hS hT]

theorem trW_heis (w : WOF F E nT nS) (f : WOF F E nT nS → ℂ) :
    trW (heisOF σ JT' JS' ξ₀ ψ w f) = heisOF σ JS JT ξ₀ ψ wᵀ (trW f) := by
  funext x
  change ψ (symplOHF σ JT' JS' ξ₀ xᵀ wᵀᵀ) * f (xᵀ + w) = ψ (symplOHF σ JS JT ξ₀ x wᵀ) * f (xᵀ + w)
  rw [symplOH_tr σ hS hT]

theorem trW_heis' (w : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    trW (heisOF σ JS JT ξ₀ ψ w f) = heisOF σ JT' JS' ξ₀ ψ wᵀ (trW f) := by
  funext x
  change ψ (symplOHF σ JS JT ξ₀ xᵀ w) * f (xᵀ + w) = ψ (symplOHF σ JT' JS' ξ₀ xᵀᵀ wᵀ) * f (xᵀ + w)
  rw [symplOH_tr σ hS hT]

theorem theta_trW {f : WOF F E nT nS → ℂ} (h : IsThetaFunOF σ JT' JS' ξ₀ ψ f) : IsThetaFunOF σ JS JT ξ₀ ψ (trW f) where
  quasi γ w := by
    have := h.quasi γᵀ wᵀ
    rw [← symplOH_tr σ hS hT]
    exact this
  level := by
    obtain ⟨U, hU, hU'⟩ := h.level
    refine ⟨U.comap trAW, hU.preimage continuous_trW, fun u hu hu' => ?_⟩
    have := congrArg trW (hU' uᵀ hu (congrArg Matrix.transpose hu'))
    rwa [trW_heis σ hS hT] at this
  cont := h.cont.comp continuous_trW
  smooth k L hL hL' w :=
    h.smooth k (trAW.comp L) (continuous_trW.comp hL) (fun t => congrArg Matrix.transpose (hL' t)) wᵀ

theorem theta_trW' {f : WOF F E nS nT → ℂ} (h : IsThetaFunOF σ JS JT ξ₀ ψ f) : IsThetaFunOF σ JT' JS' ξ₀ ψ (trW f) where
  quasi γ w := by
    have := h.quasi γᵀ wᵀ
    rw [← symplOH_tr σ hS hT] at this
    exact this
  level := by
    obtain ⟨U, hU, hU'⟩ := h.level
    refine ⟨U.comap trAW, hU.preimage continuous_trW, fun u hu hu' => ?_⟩
    have := congrArg trW (hU' uᵀ hu (congrArg Matrix.transpose hu'))
    rwa [trW_heis' σ hS hT] at this
  cont := h.cont.comp continuous_trW
  smooth k L hL hL' w :=
    h.smooth k (trAW.comp L) (continuous_trW.comp hL) (fun t => congrArg Matrix.transpose (hL' t)) wᵀ

theorem actO_tr (g : GAF σ JT') (h : GAF σ JS') (x : WOF F E nT nS) :
    actOF σ JS JT (dualG σ hS h) (dualG σ hT g) xᵀ = (actOF σ JT' JS' g h x)ᵀ := by
  unfold actOF
  rw [mt_dualG, mt_dualG_inv, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]

def swapOm (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) :
    GAF σ JT' × GAF σ JS' →* Module.End ℂ (WOF F E nT nS → ℂ) where
  toFun p := (trW : (WOF F E nS nT → ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ om (dualG σ hS p.2, dualG σ hT p.1) ∘ₗ
    (trW : _ ≃ₗ[ℂ] (WOF F E nS nT → ℂ)).toLinearMap
  map_one' := by
    refine LinearMap.ext fun f => ?_
    have : ((dualG σ hS 1, dualG σ hT 1) : GAF σ JS × GAF σ JT) = 1 := by rw [map_one, map_one]; rfl
    change trW (om (dualG σ hS 1, dualG σ hT 1) (trW f)) = f
    rw [this, map_one]; rfl
  map_mul' p q := by
    refine LinearMap.ext fun f => ?_
    have : ((dualG σ hS (p.2 * q.2), dualG σ hT (p.1 * q.1)) : GAF σ JS × GAF σ JT) =
      (dualG σ hS p.2, dualG σ hT p.1) * (dualG σ hS q.2, dualG σ hT q.1) := by rw [map_mul, map_mul]; rfl
    change trW (om (dualG σ hS (p.2 * q.2), dualG σ hT (p.1 * q.1)) (trW f)) =
      trW (om (dualG σ hS p.2, dualG σ hT p.1) (om (dualG σ hS q.2, dualG σ hT q.1) (trW f)))
    rw [this, map_mul]; rfl

theorem swapOm_apply (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) (g : GAF σ JT') (h : GAF σ JS')
    (f : WOF F E nT nS → ℂ) :
    swapOm σ hS hT om (g, h) f = trW (om (dualG σ hS h, dualG σ hT g) (trW f)) := rfl

theorem swap_datum {Tau : Type} [Fintype Tau] {tauE : Tau → (E →+* ℂ)} {χS χT : (AEF F E)ˣ →* Circle}
    {om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}
    (h : IsWeilDatumOF σ JS JT tauE ξ₀ ψ χS χT om) :
    IsWeilDatumOF σ JT' JS' tauE ξ₀ ψ χT χS (swapOm σ hS hT om) := by
  refine ⟨h.std, h.hecT, h.hecS, h.resT, h.resS,
    fun p f hf => theta_trW' σ hS hT ξ₀ ψ (h.om_pres _ _ (theta_trW σ hS hT ξ₀ ψ hf)),
    fun g k w f hf => ?_, fun g hg k hk f hf => ?_,
    fun f hf w => (h.om_cont _ (theta_trW σ hS hT ξ₀ ψ hf) wᵀ).comp
      (((continuous_dualG σ hS).comp continuous_snd).prodMk ((continuous_dualG σ hT).comp continuous_fst)),
    fun μ 𝓕 hμ h𝓕 p f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩
  · rw [swapOm_apply, swapOm_apply, trW_heis σ hS hT, h.om_heis _ _ _ _
      (theta_trW σ hS hT ξ₀ ψ hf), trW_heis' σ hS hT, actO_tr, Matrix.transpose_transpose]
  · exact h.om_aut _ (dualG_mem_GQ σ hS hk) _ (dualG_mem_GQ σ hT hg) _ (theta_trW σ hS hT ξ₀ ψ hf)
  · have : IsTopologicalRing (AEF F E) := IsModuleTopology.isTopologicalRing (AF F) (AEF F E)
    have : IsTopologicalAddGroup (AEF F E) := IsTopologicalRing.to_topologicalAddGroup
    have : IsTopologicalAddGroup (WOF F E nS nT) := Pi.topologicalAddGroup
    have : IsTopologicalAddGroup (WOF F E nT nS) := Pi.topologicalAddGroup
    have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
    have : BorelSpace (WOF F E nT nS) := ⟨rfl⟩
    let e : WOF F E nT nS ≃ₜ+ WOF F E nS nT :=
      { toFun := fun x => xᵀ, invFun := fun x => xᵀ, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
        map_add' := fun _ _ => rfl, continuous_toFun := continuous_trW, continuous_invFun := continuous_trW }
    let m : WOF F E nT nS ≃ᵐ WOF F E nS nT := e.toHomeomorph.toMeasurableEquiv
    have hH : (μ.map m).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
    have hp : MeasurePreserving m.symm (μ.map m) μ := (m.measurable.measurePreserving μ).symm m
    have hF : IsAddFundamentalDomain (ratLF F E nS nT) (m.symm ⁻¹' 𝓕) (μ.map m) := by
      refine h𝓕.preimage_of_equiv hp.quasiMeasurePreserving
        (e := fun γ => (⟨γ.1ᵀ, by obtain ⟨γ, δ, rfl⟩ := γ; exact ⟨δᵀ, rfl⟩⟩ : ratLF F E nS nT)) ?_ fun γ x => rfl
      constructor
      · intro a b hab
        exact Subtype.ext (congrArg Matrix.transpose (congrArg Subtype.val hab))
      · rintro ⟨_, δ, rfl⟩
        exact ⟨⟨_, δᵀ, rfl⟩, rfl⟩
    have key := h.om_unit (μ.map m) _ hH hF (dualG σ hS p.2, dualG σ hT p.1) _ (theta_trW σ hS hT ξ₀ ψ hf)
    have e1 := hp.setLIntegral_comp_preimage_emb m.symm.measurableEmbedding
      (fun w => ‖swapOm σ hS hT om p f w‖ₑ ^ 2) 𝓕
    have e2 := hp.setLIntegral_comp_preimage_emb m.symm.measurableEmbedding (fun w => ‖f w‖ₑ ^ 2) 𝓕
    exact e1.symm.trans (key.trans e2)
  · obtain ⟨r, hr, H⟩ := h.om_split e he (dualG σ hS k) (dualG σ hT g)
      (supp_inv _ (matHomF σ JS' k) hk) (supp_inv _ (matHomF σ JT' g) hg) y⁻¹ x⁻¹
      (det_inv_at he.1 (matHomF σ JS' k) y hy) (det_inv_at he.1 (matHomF σ JT' g) x hx)
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have := H (ℓ ∘ₗ (trW : (WOF F E nS nT → ℂ) ≃ₗ[ℂ] _).toLinearMap) (fun u hu f hf => by
      change ℓ (trW (heisOF σ JS JT ξ₀ ψ u f)) = ℓ (trW f)
      rw [trW_heis' σ hS hT]
      exact hℓ _ (fun i j => hu j i) _ (theta_trW' σ hS hT ξ₀ ψ hf)) _ (theta_trW σ hS hT ξ₀ ψ hf)
    have e1 : splitFacOF χS χT y⁻¹ x⁻¹ = splitFacOF χT χS x y := by
      rw [splitFacOF, splitFacOF, map_inv, map_inv, inv_inv, mul_comm]
    rw [e1] at this
    exact this

set_option maxHeartbeats 400000 in
theorem swap_transport {ξ ξ' : AF F ⊗[F] E} {JA : Matrix (Fin nT) (Fin nT) E} {JB JB' : Matrix (Fin nS) (Fin nS) E}
    (hle : GlobalTheory.WeilM.UG (cA σ) (incM F JB') ≤ GlobalTheory.WeilM.UG (cA σ) (incM F JB)) {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
    (co' : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (cA σ) ξ' (incM F JB') (incM F JA)) κ)
    (hco : ∀ x, co'.rho ψ x = co.rho ψ xᵀ)
    {ω : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}
    {om : GlobalTheory.WeilM.UG (cA σ) (incM F JA) × GlobalTheory.WeilM.UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)}
    (hom : GlobalTheory.WeilSchrodinger.IsTransportF σ ψ co ω om)
    (om' : GlobalTheory.WeilM.UG (cA σ) (incM F JB') × GlobalTheory.WeilM.UG (cA σ) (incM F JA) →* Module.End ℂ ((κ → AF F) → ℂ))
    (hom' : ∀ a g, om' (a, g) = om (g, Subgroup.inclusion hle a)) :
    GlobalTheory.WeilSchrodinger.IsTransportF σ ψ co' (swapOm σ hS hT ω) om' := by
  intro a b g h hh hg Φ hΦ
  have e1 : mtF σ JT (dualG σ hT g) = b.1.1 :=
    (congrArg Units.val (matHom_dualG σ hT g)).trans (invT_of_inv (matHomF σ JT' g) b hg)
  have e2 : mtF σ JS (dualG σ hS h) = ((Subgroup.inclusion hle a)⁻¹).1.1ᵀ :=
    (congrArg Units.val (matHom_dualG σ hS h)).trans (invT_incl hle (matHomF σ JS' h) a hh)
  have H := hom b (Subgroup.inclusion hle a) (dualG σ hS h) (dualG σ hT g) e1 e2 Φ hΦ
  have th : ∀ (Φ : (κ → AF F) → ℂ), GlobalTheory.WeilSchrodinger.thetaTr F co' ψ Φ =
      trW (m := nS) (n := nT) (GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ) := fun Φ => funext fun w =>
    congrArg (GlobalTheory.WeilM.thetaSum F) (congrFun (hco w) Φ)
  have e3 : om' (a, b) Φ = om (b, Subgroup.inclusion hle a) Φ := LinearMap.congr_fun (hom' a b) Φ
  refine ⟨e3 ▸ H.1, ?_⟩
  rw [th, th, e3, H.2, swapOm_apply, trW_trW]

omit [NumberField E] in
theorem hRat_tr (x y : Matrix (Fin nT) (Fin nS) E) : hRatF σ JT' JS' xᵀ yᵀ = hRatF σ JS JT x y := by
  unfold hRatF
  rw [(dual_inv hT).2, (dual_inv hS).1, sum_sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  simp only [Matrix.transpose_apply]
  ring

theorem latH_swap (h : LatH σ JS JT ξ₀) : LatH σ JT' JS' ξ₀ := by
  obtain ⟨Λ, h1, h2⟩ := h
  let t : Matrix (Fin nT) (Fin nS) E ≃ₗ[𝓞 E] Matrix (Fin nS) (Fin nT) E := Matrix.transposeLinearEquiv _ _ _ _
  have hm : ∀ M, M ∈ Λ.map t.toLinearMap ↔ Mᵀ ∈ Λ := fun M =>
    ⟨by rintro ⟨x, hx, rfl⟩; exact hx, fun hx => ⟨Mᵀ, hx, rfl⟩⟩
  refine ⟨Λ.map t.toLinearMap, ⟨h1.fg.map _, fun M => ?_⟩, fun M => ?_⟩
  · obtain ⟨N, hN, hM⟩ := h1.den Mᵀ
    exact ⟨N, hN, (hm _).2 hM⟩
  · rw [hm, h2]
    constructor
    · intro H M' hM'
      have := H M'ᵀ ((hm _).1 hM')
      rwa [← hRat_tr σ hS hT] at this
    · intro H M' hM'
      have := H M'ᵀ ((hm _).2 hM')
      rwa [← Matrix.transpose_transpose M, hRat_tr σ hS hT] at this

end Swap

end PositivityTheory.ThKW.Sw

end
