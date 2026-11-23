import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLnRatioMetLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedComplexPointsOpenVariety
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionEqHorizontalGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmooth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotIsBettiZero

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ComplexOrder Classical

namespace GlobalTheory.DetHodgeExt

theorem prod_grSq {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.PosDef) : ∏ i, grSq M i = M.det.re := by
  have hp := fun k => (GlobalTheory.GradedCompare.lminor_re_pos h k).1
  have h0 : lminor M 0 = 1 := by
    unfold lminor
    exact Matrix.det_isEmpty (n := Fin 0)
  have hl : lminor M (Fin.last m) = M.det := rfl
  have h1 := (Fin.prod_univ_succ fun k => (lminor M k).re).symm.trans (Fin.prod_univ_castSucc fun k => (lminor M k).re)
  rw [h0, Complex.one_re, one_mul, hl] at h1
  simp only [GlobalTheory.GradedCompare.grSq_eq h]
  rw [Finset.prod_div_distrib, h1, mul_div_cancel_left₀ _ (Finset.prod_ne_zero_iff.2 fun i _ => (hp _).ne')]

theorem det_smul_gram {m : ℕ} (b : ℝ) (T : Matrix (Fin m) (Fin m) ℂ) :
    ((b : ℂ) • (Tᴴ * T)).det.re = b ^ m * ‖T.det‖ ^ 2 := by
  rw [det_smul, det_mul, det_conjTranspose, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    RCLike.star_def, mul_comm (starRingEnd ℂ _), Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem per_cx {Z : Model Xo c β} {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} (Fu : Fam Xo c σ e)
    (P : FrPt Xo c (CAt σ)) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm) (hx : P.x = Fu.u i Pm)
    (hd : ∀ τ (a : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (Fu.ex i Pm z).left) (Pi.single (e.symm ⟨τ, a⟩) 1) (P.u τ a))
    (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (hQ : ∀ v z, Q v z = Pm v (e.symm z)) :
    Per Fu (⟨cxPt Z P, cxFrame Z P⟩ : CxFr Z σ) i Q := by
  refine ⟨Pm, fun z => Pi.single (e.symm z) 1, GlobalTheory.AllWt.ptF (S := CAt σ) P, hP, ?_, rfl, ?_, ?_⟩
  · exact (GlobalTheory.ShFam.Descent.ptF_fst P).trans hx
  · intro z
    obtain ⟨w, h1, h2, h3⟩ := EigFrame.ofFrPt_v (S := CAt σ) Z P
      (Category.assoc (GlobalTheory.AllWt.ptF (S := CAt σ) P) Z.jQ (genι Z)).symm z.1 z.2
    refine ⟨w, h1.1, h3, ?_⟩
    have := hd z.1 z.2
    rw [← h2] at this
    exact this
  · intro v
    simp only [hQ]
    rw [Fintype.sum_equiv e.symm (fun z => Pm v (e.symm z) • (Pi.single (e.symm z) 1 : Fin g → ℂ))
      (fun j => Pm v j • (Pi.single j 1 : Fin g → ℂ)) (fun _ => rfl)]
    funext j
    simp [Finset.sum_apply, Pi.single_apply]

theorem exists_horFn {Y : Model Xo c β} (T : TorModel Y) {σ : c.F →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb c σ) {r : ℕ}
    {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ Dw.p + Dw.q)
    (hl : ∀ p : ℕ, p.Prime → l.GoodAt p) {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) :
    ∃ h : CxFr T.Z σ → ℂ, HorFn τ h ∧ ∃ b : U.Comp → ℝ, ∀ k (y : (U.X k).dom), IsOrth (U.X k) y.1 →
      ‖h ⟨cxPt T.Z (U.un k y), cxFrame T.Z (U.un k y)⟩‖ ^ 2 = b k := by
  obtain ⟨g, e, Fu, ik, φ, hEF, hun⟩ := hU.2.2.2.2.2
  choose x hm hx using fun i : Fin Fu.n => GlobalTheory.T.exists_hermitianPeriodLatticeBasis_same_signature _ H Dw (Fu.Di i) τ (Fu.sig i)
  refine ⟨_, GlobalTheory.ShFam.Hor.horFn_horOf (Fu := Fu) (τ := τ) (x := x) (hm := hm) T hσ hr hl hx, ?_⟩
  have hΨ : ∀ k (ρ : E →+* ℂ), Formalism.L2.PjFree.relab c σ ρ ∈ (U.X k).Ψ ↔ ρ (H.rt : E) = H.rt0 :=
    fun k ρ => ((hU.2.1 k).2 _).trans (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_rt c σ hσ ρ)
  choose c₀ hc₀ hper using fun k => GlobalTheory.T.period_relabel_matrix _ H Dw l c σ r (U.X k) (Fu.Di (ik k)) τ ((hΨ k τ).2 hτ) (φ k)
    (x (ik k)) (hm (ik k)) hU.1 (hU.2.1 k).1 hτ (hΨ k) (hEF k) (hx (ik k))
  refine ⟨fun k => ‖c₀ k‖ ^ 2 * ‖Formalism.L2.PjFree.relab c σ τ (U.X k).Gm.det‖, fun k y hy => ?_⟩
  obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hun k y
  let Q : (Fu.Di (ik k)).La →+ (Letter Dw → ℂ) :=
    { toFun := fun v z => Pm v (e.symm z)
      map_zero' := by funext z; simp
      map_add' := fun a b => by funext z; simp }
  have hQ : ∀ v z, Q v z = Formalism.L2.PjFree.perFr (U.X k) y (φ k v : Fin r → E) (Formalism.L2.PjFree.relab c σ z.1) z.2 :=
    fun v z => by
      have := h1 v (e.symm z)
      rw [Equiv.apply_symm_apply] at this
      exact this
  have hP := per_cx (Z := T.Z) Fu (U.un k y) (ik k) Pm h2 h3 h4 Q (fun _ _ => rfl)
  rw [GlobalTheory.ShFam.Hor.horOf_eq hl hx _ (ik k) Q hP, hper k y.1 y.2 Q hQ, norm_mul, mul_pow]
  congr 1
  have h5 := GlobalTheory.FlatLine.det_gram (Formalism.L2.PjFree.relab c σ τ) (U.X k).Gm (mat y.1 ⟨_, (hΨ k τ).2 hτ⟩)
  rw [hy ⟨_, (hΨ k τ).2 hτ⟩, Matrix.det_diagonal, norm_prod,
    Finset.prod_eq_one fun i _ => by unfold sgn; split_ifs <;> simp] at h5
  rw [GlobalTheory.FlatLine.horizGen, norm_inv, inv_pow]
  exact (eq_inv_of_mul_eq_one_left h5.symm).symm

variable {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {σ : F →+* ℂ}

omit [NumberField F] in

theorem genSq_det (G : EigMet Z (embOf e σ)) {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) {p : Y.Y.pts σ} (g : Y.FrameAt p) :
    Y.genSq G (expo Dw (detSym Dw (fun _ => false) none τ)) g =
      (G.gram _ g τ).det.re / (G.gram _ g (conjEmb τ)).det.re := by
  have hne : conjEmb τ ≠ τ := fun e => GlobalTheory.AllWt.conj_not_mem ⟨τ, hτ⟩ (e.symm ▸ hτ)
  have hE := GlobalTheory.ShFam.Pad.expo_detSym Dw ⟨τ, hτ⟩ (fun _ => false) none
  rw [FlagCpt.genSq, Fintype.prod_sigma, Finset.prod_eq_mul τ (conjEmb τ) hne.symm, ← prod_grSq (G.pos _ _ _),
    ← prod_grSq (G.pos _ _ _), div_eq_mul_inv, ← Finset.prod_inv_distrib]
  · congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [hE]; simp
    · exact Finset.prod_congr rfl fun i _ => by rw [hE]; simp [hne]
  · intro ρ _ h
    exact Finset.prod_eq_one fun i _ => by rw [hE]; simp [h.1, h.2]
  · simp
  · simp

theorem exists_isCoord (n : Letter Dw → ℤ) {s : Y.Y.Fn} (p : Y.Y.pts σ) (hs : (divOf Y n).GeneratesAt (Var.base p) s) :
    ∃ (g : Y.FrameAt p) (v : ℂ), IsCoord Y p.1 g n s v := by
  obtain ⟨q, h1, φ, f, h2, h3⟩ := Y.exists_adapted p
  obtain ⟨r, -, hr⟩ := (CartierDiv.IsEqn.generatesAt_iff (FlagCpt.prodPow_mem n h1)).1 hs
  exact ⟨q.2, _, _, _, φ, f, _, _, r, (Y.spMap_evStalk p).symm, h2, h3, hr, rfl⟩

theorem lnRatio_sum (G G₀ : EigMet Z (embOf e σ)) {ι : Type} (S : Finset ι) (n : ι → Letter Dw → ℤ) (p : Y.Y.pts σ) :
    ∑ i ∈ S, lnRatio (C := cxSt F) (Y.met G (n i)) (Y.met G₀ (n i)) p =
      lnRatio (C := cxSt F) (Y.met G (∑ i ∈ S, n i)) (Y.met G₀ (∑ i ∈ S, n i)) p := by
  obtain ⟨q, h1, h2⟩ := Y.exists_adapted p
  have key : ∀ m : Letter Dw → ℤ, lnRatio (C := cxSt F) (Y.met G m) (Y.met G₀ m) p =
      ∑ z : Letter Dw, (m z : ℝ) * ((Real.log (grSq (G.gram _ q.2 z.1) z.2) - Real.log (grSq (G₀.gram _ q.2 z.1) z.2)) / 2) :=
    fun m => by
    have hm := FlagCpt.prodPow_mem m h1
    have hg : (divOf Y m).GeneratesAt (under p) (((prodPow q.1 m)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
      rw [Units.val_inv_eq_inv_val]
      exact CartierDiv.isEqn_iff_generatesAt_inv.1 hm
    rw [lnRatio_eq hg (posAt_of_posSet (FlagCpt.posSet_met _ _) p) (posAt_of_posSet (FlagCpt.posSet_met _ _) p)]
    show Real.log (Y.Y.pn σ _ (Y.met G m) (Y.Y.cx σ _) p) / 2 - Real.log (Y.Y.pn σ _ (Y.met G₀ m) (Y.Y.cx σ _) p) / 2 = _
    have hone : ‖((prodPow (1 : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℂˣ) m : ℂˣ) : ℂ)‖ ^ 2 = 1 := by simp [prodPow]
    rw [Var.pn_frame hm, Var.pn_frame hm, FlagCpt.met_h G m h2, FlagCpt.met_h G₀ m h2, hone, div_one, div_one,
      GlobalTheory.GradedCompare.log_genSq, GlobalTheory.GradedCompare.log_genSq, ← sub_div, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun z _ => by ring
  simp only [key, Finset.sum_apply, Int.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

end Free

section FinalTheorems

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp)
  (τ : D.what₂.Tau) {φ : (Φ.C k).Y.Fn} (hφ : IsFlat (Φ.C k) (DV.tauEmb D τ) φ)
include hφ

set_option maxHeartbeats 1600000 in

theorem finite_good {σ : D.what₂.LL →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb κ.c (embOf κ.e σ)) :
    ∃ V : Set ℝ, V.Finite ∧ ∀ p : (Φ.C k).Y.pts σ, ¬ LiesIn ((Φ.C k).down p) (genBd s.T.Z) →
      (Φ.C k).Y.pn σ _ (metsOf x Φ k none σ (detEx S τ)) ((Φ.C k).Y.cx σ φ) p ∈ V := by
  have hr : 1 ≤ S.Dw.p + S.Dw.q := by have := S.two_le; have := S.rank_eq; omega
  obtain ⟨h, hh, b, hb⟩ := exists_horFn s.T hσ (s.unf _ hσ).1 hr κ.good (A.cm τ)
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.ShFam.Horiz.rigid (Φ.C k) (A.cm τ) hh hφ
  refine ⟨Set.range fun k' => (2 * Real.pi * xiR D) ^ S.Dw.mult (DV.tauEmb D τ) /
    (2 * Real.pi * xiR D) ^ S.Dw.mult (conjEmb (DV.tauEmb D τ)) * b k' / ‖b₀‖ ^ 2, Set.finite_range _, fun p hp => ?_⟩
  obtain ⟨f, hf⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 hp
  obtain ⟨g, v, hv⟩ := exists_isCoord (Φ.C k) (detEx S τ) p (hφ _)
  obtain ⟨ψ, σ', k', y, rfl | rfl, h2, h3, h4, h5, h6⟩ := id hf
  swap
  · exact (not_good_conj κ.c (σ := embOf κ.e σ) hσ (h2 ▸ h3)).elim
  obtain rfl : σ' = embOf κ.e σ := h2
  have e0 : cxPt s.T.Z ((s.U _).un k' y) = (Φ.C k).down p :=
    Subtype.ext (h5.trans ((congrArg (· ≫ ((Φ.C k).down p).1) (Spec.map_id _)).trans (Category.id_comp _)))
  have hv' : ∀ ρ, (cxFrame s.T.Z ((s.U _).un k' y)).v ρ = f.v ρ := fun ρ => funext fun i => by
    rw [h6, spMap_dualMap_id, Category.id_comp]
  have hC : ∀ ρ, Chg (⟨_, cxFrame s.T.Z ((s.U _).un k' y)⟩ : CxFr s.T.Z _) ⟨(Φ.C k).down p, g⟩ ρ (f.co g ρ)ᵀ :=
    fun ρ => ⟨e0, fun i => by
      show IsCombAtG _ _ ((cxFrame s.T.Z ((s.U _).un k' y)).v ρ) _ _
      rw [hv']
      exact f.co_spec g ρ i⟩
  have hin : Hor.Inner (cxPt s.T.Z ((s.U _).un k' y)) := not_liesIn_cxPt (Z := s.T.Z) ((s.U _).un k' y)
  have hin' : Hor.Inner ((Φ.C k).down p) := hp
  have e1 := hh.2.1 _ _ _ _ hin (hC (DV.tauEmb D τ)) (hC (conjEmb (DV.tauEmb D τ)))
  have hstr : p.1 ≫ (Φ.C k).Y.str = spMap ((embOf κ.e σ).comp κ.e.toRingHom) :=
    p.2.trans (congrArg spMap (RingHom.ext fun a => congrArg σ (κ.e.symm_apply_apply a).symm))
  have e2 := hb₀ ⟨(Φ.C k).down p, g⟩ ⟨p.1, hstr⟩ v hin' rfl hv
  have e3 := hh.1 ⟨(Φ.C k).down p, g⟩ hin'
  have e4 := hb k' y h4
  refine ⟨k', ?_⟩
  have e5 := FlagCpt.pn_met (x.hodge (embOf κ.e σ)) (detEx S τ) hv
  rw [genSq_det (Φ.C k) _ (A.cm τ), x.hodge_gram hf, x.hodge_gram hf, det_smul_gram, det_smul_gram] at e5
  refine Eq.trans ?_ e5.symm
  rw [det_transpose, det_transpose, e2] at e1
  rw [e2] at e3
  have e6 := congrArg (fun z : ℂ => ‖z‖ ^ 2) e1
  simp only [norm_mul, mul_pow] at e6
  rw [e4] at e6
  have n1 : ‖b₀‖ ≠ 0 := norm_ne_zero_iff.2 (left_ne_zero_of_mul e3)
  have n2 : ‖(f.co g (conjEmb (DV.tauEmb D τ))).det‖ ≠ 0 := norm_ne_zero_iff.2 (f.isUnit_det_co g _).ne_zero
  have n3 : 2 * Real.pi * xiR D ≠ 0 := (mul_pos Real.two_pi_pos (xiR_pos D)).ne'
  generalize 2 * Real.pi * xiR D = t at n3 ⊢
  field_simp
  linear_combination -e6

omit hφ in

theorem finite_all {u : (Φ.C k).Y.Fnˣ} (hu : ∀ y, (divOf (Φ.C k) (detEx S τ)).IsEqn y u) (σ : D.what₂.LL →+* ℂ) :
    ∃ V : Set ℝ, V.Finite ∧ ∀ p : (Φ.C k).Y.pts σ, ¬ LiesIn ((Φ.C k).down p) (genBd s.T.Z) →
      Var.Met.h (metsOf x Φ k none σ (detEx S τ)) u p ∈ V := by
  have hφ : IsFlat (Φ.C k) (DV.tauEmb D τ) ((u⁻¹ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) := fun y => by
    rw [Units.val_inv_eq_inv_val]
    exact CartierDiv.isEqn_iff_generatesAt_inv.1 (hu y)
  have good : ∀ σ : D.what₂.LL →+* ℂ, Formalism.L2.PjFree.GoodEmb κ.c (embOf κ.e σ) →
      ∃ V : Set ℝ, V.Finite ∧ ∀ p : (Φ.C k).Y.pts σ, ¬ LiesIn ((Φ.C k).down p) (genBd s.T.Z) →
        Var.Met.h (metsOf x Φ k none σ (detEx S τ)) u p ∈ V := fun σ hσ => by
    obtain ⟨V, h1, h2⟩ := finite_good x Φ k τ hφ hσ
    exact ⟨V, h1, fun p hp => Var.pn_frame (m := metsOf x Φ k none σ (detEx S τ)) (y := p) (hu _) ▸ h2 p hp⟩
  by_cases hσ : GoodEmb κ.c (embOf κ.e σ)
  · exact good σ hσ
  have h1 : GoodEmb κ.c ((starRingEnd ℂ).comp (embOf κ.e σ)) := by
    simpa only [goodOf, if_neg hσ] using goodEmb_goodOf κ.c (embOf κ.e σ)
  obtain ⟨V, h2, h3⟩ := good ((starRingEnd ℂ).comp σ) h1
  refine ⟨V, h2, fun p hp => ?_⟩
  let p' : (Φ.C k).Y.pts ((starRingEnd ℂ).comp σ) :=
    ⟨spMap (starRingEnd ℂ) ≫ p.1, by rw [Category.assoc, p.2, ← Spec.map_comp]; rfl⟩
  rw [← (GlobalTheory.ShFam.mets_conj D A N j S κ s x Φ k σ _ (detEx S τ) p p' u rfl (hu _)).1 none]
  exact h3 p' fun h => hp ((liesIn_iff_of_comp (y := (Φ.C k).down p) (y' := (Φ.C k).down p') (ψ := starRingEnd ℂ)
    (Category.assoc _ _ _) _).1 h)

omit hφ in

theorem exists_wt_const {u : (Φ.C k).Y.Fnˣ} (hu : ∀ y, (divOf (Φ.C k) (detEx S τ)).IsEqn y u) (σ : D.what₂.LL →+* ℂ) :
    ∃ a : ℝ, ∀ p : (Φ.C k).Y.pts σ, (Φ.C k).π (Var.base p) ∉ genBd s.T.Z →
      Var.Met.wt (metsOf x Φ k none σ (detEx S τ)) u p = a := by
  obtain ⟨V, hV, h⟩ := finite_all x Φ k τ hu σ
  set B := ptsIn (Φ.C k).Y.str σ ((Φ.C k).π ⁻¹ᵁ (genBd s.T.Z).compl) with hB
  have hm : ∀ p, p ∈ B ↔ (Φ.C k).π (Var.base p) ∉ genBd s.T.Z := fun p => mem_ptsIn
  have hc : ContinuousOn (Var.Met.wt (metsOf x Φ k none σ (detEx S τ)) u) B :=
    (((GlobalTheory.metsOf_smooth D A N j S κ s x Φ k σ (detEx S τ)).2.2.2 u).mono
      fun p hp => ⟨(hm p).1 hp, hu _⟩).continuousOn (isOpen_ptsIn _)
  have hs : (Var.Met.wt (metsOf x Φ k none σ (detEx S τ)) u '' B).Subsingleton := by
    have h1 := (GlobalTheory.CxConn.isPreconnected_ptsIn _ (Φ.C k).Y σ _).image _ hc
    have h2 : (Var.Met.wt (metsOf x Φ k none σ (detEx S τ)) u '' B).Finite :=
      (hV.image fun t => -Real.log t).subset (by
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨_, h p ((hm p).1 hp), rfl⟩)
    intro a ha b hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (Set.Icc_infinite hlt) (h2.subset (h1.Icc_subset ha hb))
    · exact (Set.Icc_infinite hlt) (h2.subset (h1.Icc_subset hb ha))
  by_cases hne : B.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    exact ⟨_, fun p hp => hs ⟨p, (hm p).2 hp, rfl⟩ ⟨p₀, hp₀, rfl⟩⟩
  · exact ⟨0, fun p hp => (hne ⟨p, (hm p).2 hp⟩).elim⟩

omit hφ in

theorem exists_smooth (σ : D.what₂.LL →+* ℂ) : ∃ g : (Φ.C k).Y.pts σ → ℝ, ((Φ.C k).Y.an σ).SmoothOn Set.univ g ∧
    ∀ p, (Φ.C k).π (Var.base p) ∉ genBd s.T.Z →
      g p = -lnRatio (metsOf x Φ k none σ (detEx S τ)) (refMet x Φ k σ (detEx S τ)) p := by
  have hφ := GlobalTheory.ShFam.Hor.isFlat_flatSec D A N j S κ s Φ k τ
  generalize flatSec s Φ k τ = φ at hφ
  have h0 : φ ≠ 0 := have ⟨_, _, hu⟩ := hφ (genericPoint _); left_ne_zero_of_mul hu.ne_zero
  have hu : ∀ y, (divOf (Φ.C k) (detEx S τ)).IsEqn y (Units.mk0 φ h0)⁻¹ := fun y =>
    CartierDiv.isEqn_iff_generatesAt_inv.2 (by simpa using hφ y)
  obtain ⟨a, ha⟩ := exists_wt_const x Φ k τ hu σ
  have hs := ((GlobalTheory.metsOf_smooth D A N j S κ s x Φ k σ (detEx S τ)).2.1.2 (Units.mk0 φ h0)⁻¹).mono
    (T := Set.univ) fun p _ => ⟨trivial, hu _⟩
  refine ⟨fun p => (a - Var.Met.wt (refMet x Φ k σ (detEx S τ)) (Units.mk0 φ h0)⁻¹ p) / 2,
    fun i => (contDiffOn_const.sub (hs i)).div_const 2, fun p hp => ?_⟩
  rw [lnRatio_eq (f := φ) (hφ _) (posAt_of_posSet (posSet_metsOf x Φ k none σ _) p)
    (posAt_of_posSet (posSet_refMet x Φ k σ _) p), ← ha p hp]
  have e₁ := Var.pn_frame (m := metsOf x Φ k none σ (detEx S τ)) (y := p) (hu _)
  have e₂ := Var.pn_frame (m := refMet x Φ k σ (detEx S τ)) (y := p) (hu _)
  rw [inv_inv, Units.val_mk0] at e₁ e₂
  show _ = -(Real.log ((Φ.C k).Y.pn σ _ _ ((Φ.C k).Y.cx σ φ) p) / 2 - Real.log ((Φ.C k).Y.pn σ _ _ ((Φ.C k).Y.cx σ φ) p) / 2)
  rw [e₁, e₂]
  unfold Var.Met.wt
  ring

end FinalTheorems

end GlobalTheory.DetHodgeExt

open IsDedekindDomain Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 ReciprocityTheory.AnForm
  ReciprocityTheory.AnForm.M in

theorem GlobalTheory.DetHodgeExt.exists_smooth_ext : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ _ => ∀ (τ : D.what₂.Tau) c,
    ∃ g : (T.M c).Fun, (T.M c).Smooth g ∧
      ∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x := by
  intro _ _ D O hO _ A T H h τ c
  obtain ⟨x, P, hc⟩ := hO
  let I := h.man c
  choose g hg he using fun σ => GlobalTheory.DetHodgeExt.exists_smooth x O.Φ c τ σ
  refine ⟨fun a z => g (I.ε a) (I.pt a z), fun a j => ?_, fun a z hz => ?_⟩
  · simpa using GlobalTheory.HodgeChgSmooth.smoothOn_of_manIs I (O.dim_eq c) a isOpen_univ (hg (I.ε a))
      (f := fun z => g (I.ε a) (I.pt a z)) (fun _ _ => rfl) j
  · have hz' := ((h.an c).Z a z).not.1 hz
    refine ((he _ _ hz').trans ?_).trans ((h.an c).ph _ a z hz).symm
    have hn : detEx O.S τ = ∑ i : Fin O.N, O.ex (τ, i) := by
      funext w
      have e : expo O.S.Dw (detSym O.S.Dw (fun _ => false) none (DV.tauEmb D τ)) w =
          ∑ k ∈ Finset.range (O.S.Dw.p + O.S.Dw.q), expo O.S.Dw (rootSym O.S.Dw (fun _ => false) none (DV.tauEmb D τ) k) w :=
        (Finsupp.sum_finsetSum_index (fun _ => by simp) fun _ _ _ => by split_ifs <;> simp).symm
      refine e.trans ?_
      rw [O.S.rank_eq, Finset.sum_apply, Finset.sum_range]
      rfl
    unfold Setup.chg
    rw [hc.hm_eq, hc.h0_eq, Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp), hn]
    simp only [if_true, neg_one_mul, Finset.sum_neg_distrib]
    exact congrArg Neg.neg (GlobalTheory.DetHodgeExt.lnRatio_sum (O.Φ.C c) (x.hodge _) (x.eigMet _) Finset.univ
      (fun i => O.ex (τ, i)) _).symm

end
