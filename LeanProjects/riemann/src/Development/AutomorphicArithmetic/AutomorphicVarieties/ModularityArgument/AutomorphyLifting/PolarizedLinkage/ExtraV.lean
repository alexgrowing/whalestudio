import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationDetCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistRecCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterRecCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LFactorRecCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotientStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SumTrWEqZeroOfFrobCoset

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Extra

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (w.adicCompletion E) → WD h}

private theorem cz : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective

private theorem geo : GlobalTheory.Published.GeometricLemma := PositivityTheory.Exh.geometricLemmaGL

private theorem eq_of_support_singleton {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {y z : IrrGL k} (h : HasSupport y.rep {z}) : y = z := by
  obtain ⟨r, u, hu, hi, hc, e, hsub⟩ := h
  obtain rfl : r = 1 := by simpa using congrArg Multiset.card hu
  obtain rfl : u = fun _ => z := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hu
  obtain ⟨d, c⟩ := y
  obtain rfl : z.1 = d := by simpa using Fintype.card_congr e
  have hd : ∑ _ : Fin 1, z.1 = z.1 := by simp
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks (fun _ : Fin 1 => z.1) hd) _).1
    (piTensor fun _ => z.rep)
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one z hd
  let χ := φ.trans ψ.symm
  obtain ⟨θ⟩ := SupportUnique.nonempty_equiv_of_isSubquotient hi z.2.rep.irr
    (hsub.trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective))
  exact ((IrrGL.of_rep z).symm.trans ((IrrGL.of_eq_of.2 ⟨θ⟩).trans (IrrGL.of_rep ⟨_, c⟩))).symm

private theorem det_law (H : LawsT a ha rc) (t : ℕ) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    rc (cls (IrrRep.det (Fin t) χ hχ)) =
      sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j)) := by
  haveI := cz (E := E) (w := w)
  have hL := GlobalTheory.T.isLanglandsClassification_detCharacter Pr.cos (w.adicCompletion E) t χ hχ
  obtain ⟨φ⟩ := (IrrRep.det (Fin t) χ hχ).nonempty_equiv_rep
  rw [H.langlands _ (cls (IrrRep.det (Fin t) χ hχ)) (hL.of_equiv φ.symm), segSum, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  show ((rc ((IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ))).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar
      (WD.lpSp h 1) = _
  have h0 : ((((1 : ℕ) : ℝ) - 1) / 2) = 0 := by norm_num
  rw [h0, (GlobalTheory.T.weilDeligne_charpoly_twist_special E Ω A w h _).1, H.nu]

private theorem prod_law (H : LawsT a ha rc) (r t : ℕ) (σ : IrrRep (GL (Fin r) (w.adicCompletion E)))
    (τ : IrrRep (GL (Fin t) (w.adicCompletion E))) (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E)))
    (hπ : Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ))) : rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ)) := by
  haveI := cz (E := E) (w := w)
  obtain ⟨𝔪, h𝔪⟩ := Pr.exh _ (cls σ)
  obtain ⟨𝔫, h𝔫⟩ := Pr.exh _ (cls τ)
  have hp := GlobalTheory.T.isLanglandsClassification_add_of_irreducible_product Pr.multi Pr.cos _ r t σ τ π 𝔪 𝔫 (h𝔪.of_equiv (equivRep σ).symm)
    (h𝔫.of_equiv (equivRep τ).symm) hπ
  rw [H.langlands 𝔪.toList (cls σ) (by rwa [Multiset.coe_toList]),
    H.langlands 𝔫.toList (cls τ) (by rwa [Multiset.coe_toList]),
    H.langlands (𝔪.toList ++ 𝔫.toList) (cls π) (by
      rw [← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList]
      exact hp.of_equiv (equivRep π)), segSum_append_lpSum]

private theorem charPol_seg (H : LawsT a ha rc) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).charPol σ
      = (Δ.ms.map fun y => (rc y).charPol σ).prod := by
  rw [(GlobalTheory.T.weilDeligne_charpoly_twist_special E Ω A w h (rc Δ.first)).2 Δ.len σ, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (rc (Δ.term j)).charPol σ = ((rc Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, H.nu]
  change _ = ∏ j : Fin Δ.len, (fun y => (rc y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((rc Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

private theorem supp_law (H : LawsT a ha rc) (x : IrrGL (w.adicCompletion E)) (s : Multiset (IrrGL (w.adicCompletion E)))
    (hs : HasSupport x.rep s) (σ : Weil h) : (rc x).charPol σ = (s.map fun y => (rc y).charPol σ).prod := by
  haveI := cz (E := E) (w := w)
  obtain ⟨𝔪, hm⟩ := Pr.exh (w.adicCompletion E) x
  have h1 := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment Pr.zel _ 𝔪 x hm
  obtain rfl : s = msupp 𝔪 := GlobalTheory.T.supercuspidalSupport_unique_GL geo Pr.bz Pr.zel _ x s _ hs h1
  rw [H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, SuppLaw.charPol_sumList, List.map_map,
    msupp, Multiset.map_bind, Multiset.prod_bind]
  have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
      (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
  rw [hl, Multiset.coe_toList]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => charPol_seg H Δ σ)

private theorem sat_law (H : LawsT a ha rc) (x : IrrGL (w.adicCompletion E)) (α : Fin x.1 → ℂˣ)
    (hα : HasSatake x.rep α) : rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  haveI := cz (E := E) (w := w)
  have hL := GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified Pr.exh Pr.multi Pr.cos Pr.zel geo Pr.bz (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← SatakeLaw.sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _

private theorem good_of_hasSatake (x : IrrGL (w.adicCompletion E)) (α : Fin x.1 → ℂˣ) (hα : HasSatake x.rep α) :
    Good x := by
  haveI := cz (E := E) (w := w)
  refine ⟨_, GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient (w.adicCompletion E) x.1 (fun i => GlobalTheory.SmGL.unrChar _ (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ (α i))) x.2.rep hα.2.2, fun y hy => ?_⟩
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  exact Or.inl rfl

private theorem sph_law (H : LawsT a ha rc) (x : IrrGL (w.adicCompletion E)) : IsSpherical x.rep ↔ (rc x).unr := by
  constructor
  · intro hs
    obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main Pr.bz (w.adicCompletion E) x.1
      ⟨x.2.rep.V, x.2.rep.ρ, x.2.rep.smooth, x.2.rep.irr⟩ hs
    rw [sat_law H x α hα]
    exact (WD.unr_mk _).2 (WDRep.unr_diag _)
  · intro hu
    obtain ⟨α, hα⟩ := GlobalTheory.T.unramified_weilDeligne_eq_diagonal_inv E Ω A w h (rc x) hu
    obtain ⟨π, hπ⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := w.adicCompletion E) α
    have φ := equivRep π
    have hπ' : HasSatake (cls π).rep α := ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hπ.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hπ.2.2⟩
    have e1 := sat_law H (cls π) α hπ'
    have e2 : x = cls π := H.inj _ _ (good_of_hasSatake _ α hπ') (hα.trans e1.symm)
    rw [e2]
    exact hπ'.2.1

private theorem dim_zero_of_irr_sum {x y : WD h} (hi : IsIrrWD (x.lpSum y)) : x.lpDim = 0 ∨ y.lpDim = 0 := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  obtain ⟨m, c, rfl⟩ := y.exists_rep
  rw [WD.lpSum_mk, GlobalTheory.VWeil.isIrrWD_mk] at hi
  let S : Subrepresentation (b.sum c).ρ := ⟨LinearMap.ker (LinearMap.snd ℂ _ _), fun σ v hv => by
    have hv' : v.2 = 0 := hv
    show c.ρ σ v.2 = 0
    rw [hv', map_zero]⟩
  rw [WD.lpDim_mk, WD.lpDim_mk, Module.finrank_zero_iff, Module.finrank_zero_iff]
  rcases hi.eq_bot_or_eq_top S with hS | hS
  · refine Or.inl (subsingleton_of_forall_eq 0 fun v => ?_)
    have hv : ((v, 0) : (Fin n → ℂ) × (Fin m → ℂ)) ∈ S.toSubmodule := rfl
    rw [hS] at hv
    exact congrArg Prod.fst (show ((v, 0) : (Fin n → ℂ) × (Fin m → ℂ)) = 0 from hv)
  · refine Or.inr (subsingleton_of_forall_eq 0 fun v => ?_)
    have hv : ((0, v) : (Fin n → ℂ) × (Fin m → ℂ)) ∈ S.toSubmodule := by
      rw [hS]; trivial
    exact hv

private theorem not_mono0_sp {x : WD h} (h0 : x.mono0) (hd : 0 < x.lpDim) {n : ℕ} (hn : 2 ≤ n) :
    ¬ (x.lpChar (WD.lpSp h n)).mono0 := by
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hd
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
  rw [WD.lpSp, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, WDRep.sp_N, LinearMap.rTensor_zero, zero_add]
  intro hN
  refine shiftEnd_ne_zero hn (LinearMap.ext fun u => ?_)
  have h1 := congrArg ((TensorProduct.lid ℂ (Fin n → ℂ)).toLinearMap ∘ₗ
    LinearMap.rTensor (Fin n → ℂ) (LinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) ⟨0, hd⟩))
    (LinearMap.congr_fun hN ((fun _ => 1) ⊗ₜ u))
  simpa using h1

private theorem seg_dim_pos (H : LawsT a ha rc) (Δ : Segment (w.adicCompletion E)) :
    0 < (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).lpDim := by
  rw [WD.lpDim_tensor, WD.lpDim_tw, H.dim, WD.lpSp, WD.lpDim_mk, Module.finrank_fin_fun]
  exact Nat.mul_pos Δ.isCusp_first.1 Δ.len_pos

private theorem cusp_law (H : LawsT a ha rc) (x : IrrGL (w.adicCompletion E)) (hx : IsIrrWD (rc x)) : x.IsCusp := by
  haveI := cz (E := E) (w := w)
  obtain ⟨𝔪, hm⟩ := Pr.exh (w.adicCompletion E) x
  obtain ⟨l, rfl⟩ : ∃ l : List (Segment (w.adicCompletion E)), (l : Multiset _) = 𝔪 := ⟨_, 𝔪.coe_toList⟩
  have hs := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment Pr.zel _ _ x hm
  rw [H.langlands l x hm] at hx
  have key : ∀ (Δ : Segment (w.adicCompletion E)) (m : List (Segment (w.adicCompletion E))), segSum rc (Δ :: m) =
      (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).lpSum (segSum rc m) := fun _ _ => rfl
  match l, hs, hx with
  | [], _, hx =>
    exact absurd (GlobalTheory.VWeil.IrrW.lpDim_pos ⟨_, hx⟩) (by
      show ¬ 0 < (WD.lpZero h).lpDim
      rw [WD.lpDim_zero]
      exact lt_irrefl 0)
  | [Δ], hs, hx =>
    have e : segSum rc [Δ] = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len) := WD.lpSum_zero _
    rw [e] at hx
    have hf := H.cusp _ Δ.isCusp_first
    have hlen : Δ.len = 1 := by
      have hpos := Δ.len_pos
      by_contra hne
      refine not_mono0_sp ?_ ?_ (by omega) (GlobalTheory.VWeil.IrrW.mono0 ⟨_, hx⟩)
      · exact (WD.monomial_twist_iff _ _).2 (GlobalTheory.VWeil.IrrW.mono0 ⟨_, hf⟩)
      · rw [WD.lpDim_tw]
        exact GlobalTheory.VWeil.IrrW.lpDim_pos ⟨_, hf⟩
    have e' : Δ = Segment.single Δ.first Δ.isCusp_first := Segment.ext_first rfl (by rw [hlen]; rfl)
    have hms : msupp (([Δ] : List (Segment (w.adicCompletion E))) : Multiset _) = {Δ.first} := by
      rw [msupp, Multiset.coe_singleton, Multiset.singleton_bind]
      exact (congrArg Segment.ms e').trans (Segment.ms_single _ _)
    rw [hms] at hs
    rw [eq_of_support_singleton hs]
    exact Δ.isCusp_first
  | Δ :: Δ' :: m, _, hx =>
    rw [key] at hx
    rcases dim_zero_of_irr_sum hx with h0 | h0
    · exact absurd h0 (seg_dim_pos H Δ).ne'
    · rw [key, WD.lpDim_sum] at h0
      have := seg_dim_pos H Δ'
      omega

end UpperTheory.V.Z.Win.Extra

open UpperTheory.V.Z.Win.Extra in
theorem UpperTheory.V.Z.Win.extraV :
    UpperTheory.V.Z.Win.ExtraV := by
  rintro E Ω _ _ _ _ _ A w h rc ⟨a, ha, H⟩
  exact ⟨a, ha, fun _ _ _ _ _ _ _ _ _ => 1, H.dim, H.one, H.langlands, det_law H, prod_law H, supp_law H,
    sph_law H, sat_law H, fun x => ⟨H.cusp x, cusp_law H x⟩, H.nu, H.absCentral, H.twist, H.central, H.dual, H.inj⟩

theorem UpperTheory.V.Z.Win.toV' {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRecT h rc) : UpperTheory.V.Z.Win.IsRecV h rc :=
  UpperTheory.V.Z.Win.extraV E Ω A w h rc H

end
