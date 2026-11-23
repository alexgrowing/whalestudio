import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpC
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupCLeISupGeneric
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnHolomorphicFramedFamily
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIdempotentWeightZeroSectionOfComponent
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IdemMulMemCusp
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FnFGFnTrdeg
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair

noncomputable section

namespace GlobalTheory.CompModel

section Free

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm GlobalTheory.Reg
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_open_same_model (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {A : Type} [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) {m : ℕ}
    {B : Set (Fin m → ℂ)} (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ))
    (hB : IsOpen B) (hφ : ∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B)
    (hy : ∀ b ∈ B, FrMap (φ b) yA (y b)) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) {k₀ : U.Comp} {x₁ : (U.X k₀).dom}
    {t₁ : Ix Dw → (CAt σ)ˣ} (ht₁ : FrBor t₁ (U.un k₀ x₁) (y b₀)) :
    ∃ B₁, IsOpen B₁ ∧ b₀ ∈ B₁ ∧ ∀ b ∈ B₁, ∃ (x : (U.X k₀).dom) (t : Ix Dw → (CAt σ)ˣ),
      FrBor t (U.un k₀ x) (y b) := by
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, ψ, hef, hun⟩ := hU
  obtain ⟨B₁, k, P, hB₁, hb₁, hs₁, hP, hyP⟩ := GlobalTheory.T.exists_holomorphic_periods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨P₁, hP₁, hP₁', hx₁, -⟩ := hun k₀ x₁
  obtain rfl : ik k₀ = k := F.disj _ _ _ _ hP₁' (hP.1 b₀ hb₁) (hx₁.symm.trans (ht₁.1.symm.trans (hyP b₀ hb₁).1))
  obtain ⟨d, hd, horth⟩ := GlobalTheory.T.period_eq_triangular_orthonormal_alt E H Dw l c σ g e _ r (U.X k₀) (ψ k₀) hσ (F.sig _).1 (F.sig _).2 hr
    (hty k₀).1 (hty k₀).2 (hef k₀)
    (GlobalTheory.T.im_neg_of_frame_period_vector E H Dw l c σ g e _ r (U.X k₀) (ψ k₀) hσ hr (hty k₀).1 (hty k₀).2 (hef k₀) x₁.1 x₁.2 P₁ hP₁ hP₁')
  refine ⟨B₁, hB₁, hb₁, fun b hb => ?_⟩
  have hp := hP.1 b hb
  obtain ⟨x₀, hx₀, -, S, -, hsupp, hper, -⟩ := horth _ hp
  obtain ⟨P₀, hP₀, hP₀', hux, hud, -⟩ := hun k₀ ⟨x₀, hx₀⟩
  have hPS : ∀ a, P₀ a = S *ᵥ P b a := fun a => funext fun j => (hP₀ a j).trans (hper a j).symm
  obtain ⟨t, ht, -⟩ := GlobalTheory.T.triangular_frame_change_of_triangular_period E H Dw l Xo c σ g e F _ (P b) P₀ S (y b) (U.un k₀ ⟨x₀, hx₀⟩) hp hP₀' hPS hsupp
    (hyP b hb).1 hux (hyP b hb).2 hud
  exact ⟨⟨x₀, hx₀⟩, t, ht⟩

def CarriesGeneric (U : Formalism.L2.PjFree.Unf Xo c σ r) (h : GenFrEx Xo c) (k : U.Comp) (Z : Comp Xo c) : Prop :=
  ∃ (P : Om Z →ₐ[c.F] CAt σ) (w : FrPt Xo c (CAt σ)) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ),
    FrMap P (genFr h Z) w ∧ FrBor t (U.un k x) w

def algOf {Z : Comp Xo c} (P : Om Z →+* ℂ) (hP : P ∈ T0.PT (Ω := Om Z) σ) : Om Z →ₐ[c.F] CAt σ :=
  { (show Om Z →+* CAt σ from P) with commutes' := fun a => RingHom.congr_fun hP a }

theorem exists_model (U : Formalism.L2.PjFree.Unf Xo c σ r) (hU : Formalism.L2.PjFree.IsUnf U) (h : GenFrEx Xo c)
    (Z : Comp Xo c) : ∃ k, CarriesGeneric U h k Z := by
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨P, hP⟩ := T0.exists_embedding_over ((GlobalTheory.FlagDim.fnFG_fnTrdeg E H Dw l Xo c).1 Z) σ
  obtain ⟨w, hw⟩ := hL.bc _ _ (algOf P hP) (genFr h Z)
  obtain ⟨k, x, t, ht⟩ := hU.2.2.1 w
  exact ⟨k, algOf P hP, w, x, t, hw, ht⟩

theorem exists_comp (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (h : GenFrEx Xo c) (k : U.Comp) : ∃ Z, CarriesGeneric U h k Z := by
  classical
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨x₁, hx₁⟩ := (GlobalTheory.frames_isConnected E r (U.X k)).nonempty
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C, ψ₀, z₀, t₀, hz₀, hb₀⟩ := hA h (CAt σ) (U.un k ⟨x₁, hx₁⟩)
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  have huniq := fun φ : C.R →ₐ[c.F] CAt σ =>
    (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c C.R (CAt σ) φ C.y).1
  haveI := C.sm
  haveI := GlobalTheory.SupGeneric.isFractionRing_chart C
  let φ₀ : C.R →+* ℂ := ψ₀.toRingHom
  have hφ₀ : φ₀.comp (algebraMap c.F C.R) = σ := RingHom.ext fun a => ψ₀.commutes a
  obtain ⟨m, s, B, ψ, S, ε, hB, hε, hψ, hd, hnear⟩ :=
    GlobalTheory.SmoothPointFamily.exists_holomorphic_family c.F C.R σ φ₀ hφ₀
  let ψ' : (Fin m → ℂ) → (C.R →ₐ[c.F] CAt σ) := fun b =>
    if hb : b ∈ B then
      { (show C.R →+* CAt σ from ψ b) with commutes' := fun a => RingHom.congr_fun (hψ b hb).1 a }
    else ψ₀
  have hψ' : ∀ b ∈ B, ∀ a, Formalism.L2.PjFree.toC (ψ' b a) = ψ b a := by
    intro b hb a
    simp only [ψ', dif_pos hb]
    rfl
  choose z hz using fun b => hL.bc _ _ (ψ' b) C.y
  obtain ⟨h1, h2⟩ := hnear φ₀ hφ₀ (fun a _ => by simpa using hε)
  have e₀ : ψ' (fun i => φ₀ (s i)) = ψ₀ := AlgHom.ext fun a => by
    have := hψ' _ h1 a
    rw [h2] at this
    exact this
  have hz₀' : z₀ = z fun i => φ₀ (s i) := huniq ψ₀ _ _ hz₀ (e₀ ▸ hz _)
  obtain ⟨B₁, hB₁, hb₁, hloc⟩ := exists_open_same_model U hσ hU C.y ψ' z hB
    (fun a => (hd a).congr fun b hb => hψ' b hb a) (fun b _ => hz b) h1 (hz₀' ▸ hinv _ _ _ hb₀)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hB₁ _ hb₁
  obtain ⟨P, hP, hPε⟩ := GlobalTheory.generic_points_dense GlobalTheory.exists_algIndep_tuple_near c.F C.R (Om C.Z) σ φ₀ hφ₀
    (S ∪ Finset.univ.image s) (min ε δ) (lt_min hε hδ)
  let ρ : C.R →+* ℂ := P.comp (algebraMap C.R (Om C.Z))
  have hρ : ρ.comp (algebraMap c.F C.R) = σ := RingHom.ext fun a => RingHom.congr_fun hP a
  obtain ⟨h3, h4⟩ := hnear ρ hρ fun a ha =>
    (hPε a (Finset.mem_union_left _ ha)).trans_le (min_le_left _ _)
  have h5 : (fun i => ρ (s i)) ∈ B₁ := hball (by
    rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    intro i
    rw [dist_eq_norm]
    exact (hPε (s i) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))).trans_le
      (min_le_right _ _))
  obtain ⟨x, t, ht⟩ := hloc _ h5
  have e₁ : ψ' (fun i => ρ (s i)) = (algOf P hP).comp C.R.val := AlgHom.ext fun a => by
    have := hψ' _ h3 a
    rw [h4] at this
    exact this
  obtain ⟨w, hw⟩ := hL.bc _ _ (algOf P hP) (genFr h C.Z)
  obtain ⟨w', hw'⟩ := hL.bc _ _ (algOf P hP) C.yg
  have e₂ : w' = z fun i => ρ (s i) := huniq _ _ _ (PullbackSections.frMap_trans _ _ C.gen hw') (e₁ ▸ hz _)
  have hbw := GlobalTheory.SupGeneric.frBor_of_frMap _ C.bor hw hw'
  rw [e₂] at hbw
  exact ⟨C.Z, algOf P hP, w, x, _, hw, hmul _ _ _ _ _ ht (hinv _ _ _ hbw)⟩

theorem rdU_apply (U : Formalism.L2.PjFree.Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) (x : (U.X k).dom) :
    Formalism.L2.PjFree.rdU U f k x.1 = Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) := by
  simp only [Formalism.L2.PjFree.rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2]

theorem exists_frame_iff {U : Formalism.L2.PjFree.Unf Xo c σ r} {h : GenFrEx Xo c} {k : U.Comp} {Z : Comp Xo c}
    (hk : CarriesGeneric U h k Z) : ∃ x ∈ (U.X k).dom, ∀ a n, ∀ f ∈ sec Xo c a n,
      (evC h Z f = 0 ↔ Formalism.L2.PjFree.rdU U f k x = 0) := by
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨P, w, x, t, hw, ht⟩ := hk
  obtain ⟨-, -, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  refine ⟨x.1, x.2, fun a n f hf => ?_⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have e1 := GlobalTheory.SupGeneric.evR_of_frMap hL hf P hw
  have e2 := hL.wt a n f hf _ t _ _ (hL.test _ _) (hL.test _ _) ht
  have e3 := hL.wt a n f hf _ _ _ _ (hL.test _ _) (hL.test _ _) (hinv _ _ _ ht)
  rw [rdU_apply]
  change evR Xo c f (genFr h Z) = 0 ↔ evR Xo c f (U.un k x) = 0
  constructor
  · intro h0
    rw [e3, e1, h0, map_zero, mul_zero]
  · intro h0
    rw [h0, mul_zero, e1] at e2
    exact (map_eq_zero_iff P.toRingHom P.toRingHom.injective).1 e2

theorem evC_eq_zero_iff {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) {h : GenFrEx Xo c}
    {k : U.Comp} {Z : Comp Xo c} (hk : CarriesGeneric U h k Z) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) : evC h Z f = 0 ↔ ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f k x = 0 := by
  obtain ⟨x₀, hx₀, hiff⟩ := exists_frame_iff hk
  refine ⟨fun h0 x hx => ?_, fun h0 => (hiff a n f hf).2 (h0 x₀ hx₀)⟩
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨χ, hχ, hi, h1, hz⟩ := exists_idem_section E H Dw l Xo c hL h (hA h) Z
  have hmul : ∀ Z' : Comp Xo c, evC h Z' (χ * f) = evC h Z' χ * evC h Z' f := fun Z' => by
    simp only [evC, evR, evalAt_mul]
  have hχf : χ * f = 0 := by
    refine sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) _ _ _ (sec_mul Xo c 0 a 0 n hχ hf) fun Z' => ?_
    rw [hmul]
    by_cases hZ : Z' = Z
    · rw [hZ, h0, mul_zero]
    · rw [hz Z' hZ, zero_mul]
  have hD : Dom (E := E) 0 0 := ⟨fun τ _ _ _ => le_rfl, Even.zero⟩
  have hs := hU.2.2.2.2.1 0 0 hD χ hχ k
  rw [IdemCusp.laU_zero] at hs
  have hid : IdemCusp.IsIdemFn (U.X k) (Formalism.L2.PjFree.rdU U χ k) := by
    refine IdemCusp.isIdemFn_of_isSec _ hs ?_
    have := congrFun (IdemCusp.rdU_mul U χ χ) k
    rw [hi] at this
    exact this.symm
  have hT : Set.MapsTo (Formalism.L2.PjFree.rdU U χ k) (U.X k).dom ({0, 1} : Set ℂ) := by
    intro s hs
    rcases hid.1 _ hs with h | h <;> simp [h]
  have hc := (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected.constant_of_mapsTo
    (Set.toFinite ({0, 1} : Set ℂ)).isDiscrete hid.2.1.continuousOn hT hx hx₀
  have hne : Formalism.L2.PjFree.rdU U χ k x ≠ 0 := by
    rw [hc]
    intro h2
    rw [← hiff 0 0 χ hχ, h1] at h2
    exact one_ne_zero h2
  have hp := congrFun (congrFun (IdemCusp.rdU_mul U χ f) k) x
  rw [hχf, map_zero] at hp
  exact (mul_eq_zero.1 hp.symm).resolve_left hne

end Free

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem comp_read_on_model : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → (∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k : (T.U j σ).Comp, ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u), evC hG Z F.1 = 0 ↔ ∀ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) F.1 k x = 0) ∧ ∀ k : (T.U j σ).Comp, ∃ Z : Comp (T.Q.Xo j) T.Q.c, ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u), evC hG Z F.1 = 0 ↔ ∀ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) F.1 k x = 0 := by
  intro D T h j hj hG σ hσ
  have hU : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := h.unf j hj σ hσ
  have hs : ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u),
      (F.1 : T.R j) ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n := fun u F =>
    cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA u) u.n (cutR_le T.C j u F.2)
  refine ⟨fun Z => ?_, fun k => ?_⟩
  · obtain ⟨k, hk⟩ := exists_model _ hU hG Z
    exact ⟨k, fun u F => evC_eq_zero_iff hU hk (hs u F)⟩
  · obtain ⟨Z, hk⟩ := exists_comp _ hσ hU hG k
    exact ⟨Z, fun u F => evC_eq_zero_iff hU hk (hs u F)⟩

end GlobalTheory.CompModel
