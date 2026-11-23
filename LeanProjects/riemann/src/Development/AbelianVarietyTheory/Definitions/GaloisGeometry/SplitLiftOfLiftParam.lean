import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne

noncomputable section

namespace GlobalTheory.ThetaExh.Check

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.ThetaExh

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem upInj_of_lamPos (i : N.Loc) (h : LamPos N i) : UpInj N i := by
  intro σ f hf h0
  obtain ⟨hscal, hpos⟩ := h σ
  have key := hscal f hf
  rw [h0, map_zero] at key
  by_cases hb : what₂.isot (N.j i) σ = ⊥
  · rw [hb] at hf
    exact (Submodule.mem_bot ℂ).1 hf
  · have hne : ((what₂.lamP (N.mu i) (N.j i) σ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (hpos hb).ne'
    exact (smul_eq_zero.1 key.symm).resolve_left hne

theorem locOfPt_of_repOfPt (i : N.Loc) (h : RepOfPt N A i) : LocOfPt N A i := by
  intro P P' x hP hP' w _
  rw [h P P' x hP hP']

theorem count_of_down (i : N.Loc) (h1 : TypeNZ N A i) (h2 : DownMem N A i) : Count N A i := by
  intro x hx Sig hS
  let g : ↥(eigC N A i x) →ₗ[ℂ] ↥(MjSig N A i Sig) :=
    ((what₂.thetaP (N.mu i) (N.j i)).domRestrict (eigC N A i x)).codRestrict (MjSig N A i Sig)
      (fun v => h2 x hx Sig hS (Submodule.mem_map_of_mem v.2))
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : what₂.thetaP (N.mu i) (N.j i) (v : what₂.Mt (N.mu i) (N.j i)) = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.1 hv)
    exact Subtype.ext (h1 x hx v v.2 hv')
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem pairs_of_thetaOf (i : N.Loc) (σ : what₂.FT) (P : A.AV i) (h : thetaOf N A i σ P) :
    Pairs N A i σ P := by
  obtain ⟨hne, hle⟩ := h
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨f, hf, hfy⟩ := Submodule.mem_map.1 hy
  refine ⟨f, hf, y, hle hy, ?_⟩
  rw [hfy]
  exact inner_self_ne_zero.2 hy0

private theorem foldr_lpSum_lpChar_comm {ι : Type} (hL : ParamLaws N A) (χ : A.CG 1) (w : PlE H)
    (c : ι → ℝ) (b : A.LP w) (L : List ι) :
    L.foldr (fun k acc => A.lpSum (A.lpTw (A.lpChar b (A.locG χ w)) (c k)) acc) (A.lpZero w) =
      A.lpChar (L.foldr (fun k acc => A.lpSum (A.lpTw b (c k)) acc) (A.lpZero w)) (A.locG χ w) := by
  have hd : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction L with
  | nil => exact ((hL w).2.1 _ hd).symm
  | cons k L ih =>
    simp only [List.foldr_cons]
    rw [ih, (hL w).1 _ _ _ hd, (hL w).2.2.1 _ _ _ hd]

theorem speh_char (hL : ParamLaws N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  unfold spehLoc
  simp only [A.locG_tw]
  exact foldr_lpSum_lpChar_comm N A hL χ w (fun k : ℝ => ((p.d : ℝ) - 1) / 2 - k) (A.locG p.π w) _

theorem iso_char (hL : ParamLaws N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hd : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction S with
  | nil => exact ((hL w).2.1 _ hd).symm
  | cons p S ih =>
    show A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [ih, speh_char N A hL p χ w, (hL w).1 _ _ _ hd]

theorem iso_append (S : List (Part A.CG)) (p : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [p]) w = A.lpSum (isoLoc N A S w) (spehLoc N A p w) := by
  induction S with
  | nil => exact A.lpSum_comm _ _
  | cons q S ih =>
    show A.lpSum (spehLoc N A q w) (isoLoc N A (S ++ [p]) w) =
      A.lpSum (A.lpSum (spehLoc N A q w) (isoLoc N A S w)) (spehLoc N A p w)
    rw [ih, A.lpSum_assoc]

theorem splitLift_of_liftParam (hL : ParamLaws N A) (i : N.Loc) (h : LiftParam N A i) :
    SplitLift N A i := by
  intro σ P hθ w hw
  obtain ⟨Sig, hSig, hBC⟩ := h σ P hθ
  show A.locV i P w =
    A.lpChar (A.lpSum (A.locW i σ w) (spehLoc N A (muPart N A i) w)) (A.locG A.etaTinv w)
  rw [← hBC.2.2.2.1 w hw, iso_char N A hL _ _ w, iso_append N A, hSig.2.2 w hw]

private theorem pairs_of_starProjection_ne_zero (i : N.Loc) (σ : what₂.FT) (P : A.AV i) (f : what₂.Mj (N.j i))
    (hf : f ∈ what₂.isot (N.j i) σ)
    (hne : (A.typeV i P).starProjection (what₂.thetaT (N.mu i) (N.j i) f) ≠ 0) :
    Pairs N A i σ P := by
  refine ⟨f, hf, (A.typeV i P).starProjection (what₂.thetaT (N.mu i) (N.j i) f),
    Submodule.starProjection_apply_mem _ _, ?_⟩
  have e1 := Submodule.starProjection_inner_eq_zero (K := A.typeV i P)
    (what₂.thetaT (N.mu i) (N.j i) f) _
    (Submodule.starProjection_apply_mem (A.typeV i P) (what₂.thetaT (N.mu i) (N.j i) f))
  rw [inner_sub_left, sub_eq_zero] at e1
  rw [Submodule.inner_starProjection_left_eq_right, e1]
  exact inner_self_ne_zero.2 hne

theorem thetaOne_of (h1 : ∀ i, UpInj N i) (h2 : ∀ i, HoweUp N A i) (h3 : ∀ i, TypeOrth N A i) :
    ThetaOne N A := by
  intro i σ hσ
  classical
  letI : Fintype (A.AV i) := Fintype.ofFinite _
  have hO : OrthogonalFamily ℂ (fun P => A.typeV i P) (fun P => (A.typeV i P).subtypeₗᵢ) :=
    orthogonalFamily_iff_pairwise.2 (by intro P P' hP; exact h3 i P P' hP)
  have hsum : ∀ u, (∑ Q, (A.typeV i Q).starProjection u) = u := fun u =>
    hO.sum_projection_of_mem_iSup u (by rw [A.typeV_top i]; exact Submodule.mem_top)
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have hu0 : what₂.thetaT (N.mu i) (N.j i) f ≠ 0 := fun h => hf0 (h1 i σ f hf h)
  obtain ⟨P, hP⟩ : ∃ P, (A.typeV i P).starProjection (what₂.thetaT (N.mu i) (N.j i) f) ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    apply hu0
    rw [← hsum (what₂.thetaT (N.mu i) (N.j i) f)]
    exact Finset.sum_eq_zero (fun Q _ => hc Q)
  have hPair := pairs_of_starProjection_ne_zero N A i σ P f hf hP
  refine ⟨P, ?_, ?_⟩
  · intro hbot
    apply hu0
    have hm : what₂.thetaT (N.mu i) (N.j i) f ∈
        (what₂.isot (N.j i) σ).map (what₂.thetaT (N.mu i) (N.j i)) := Submodule.mem_map_of_mem hf
    rw [hbot] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · intro u hu
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hu
    have hz : ∀ Q, Q ≠ P → (A.typeV i Q).starProjection (what₂.thetaT (N.mu i) (N.j i) g) = 0 := by
      intro Q hQ
      by_contra hc
      exact hQ (h2 i σ Q P (pairs_of_starProjection_ne_zero N A i σ Q g hg hc) hPair)
    rw [← hsum (what₂.thetaT (N.mu i) (N.j i) g),
      Finset.sum_eq_single P (fun Q _ hQ => hz Q hQ) (by simp)]
    exact Submodule.starProjection_apply_mem _ _

theorem iotaO_inj (i : N.Loc) : Function.Injective (iotaO N A i) := by
  intro a b hab
  simp only [iotaO, RingHom.coe_comp, Function.comp_apply] at hab
  exact IsFractionRing.injective (N.O i) (FractionRing (N.O i))
    ((A.iotaQ i).injective ((A.iotaQC i).injective hab))

theorem exists_pt_of_loc (i : N.Loc) (h : PtLocal N A i) (P P' : A.AV i) (x : N.X i)
    (hx : A.ptV i P' = some x) (hl : ∀ w, SplitOut N i w → A.locV i P w = A.locV i P' w) :
    ∃ y, A.ptV i P = some y ∧ ∀ w, SplitOut N i w → heckePol N i y w = heckePol N i x w := by
  have hpol : ∀ w, SplitOut N i w → (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) := by
    intro w hw
    rw [hl w hw]
    exact A.pt_loc i P' x hx w hw
  obtain ⟨y, hy⟩ := h P x (fun w hw => ⟨heckePol N i x w, hpol w hw, rfl⟩)
  refine ⟨y, hy, fun w hw => ?_⟩
  apply Polynomial.map_injective (iotaO N A i) (iotaO_inj N A i)
  rw [hpol w hw]
  exact A.pt_loc i P y hy w hw

theorem rowSize_of_le (hq : ∀ w : PlE H, 1 < (normV w : ℕ)) (h : RowSizeLe N A) : RowSize N A := by
  intro i σ hσ w hw hu α hα
  refine lt_of_le_of_lt (h i σ hσ w hw hu α hα) ?_
  apply Real.rpow_lt_rpow_of_exponent_lt
  · exact_mod_cast hq w
  · have hrt : R.r < R.t := by
      have h5 := R.rank_add_five_le
      simp only [Ranks.r]
      omega
    have hrt' : (R.r : ℝ) < R.t := by exact_mod_cast hrt
    linarith

end GlobalTheory.ThetaExh.Check
