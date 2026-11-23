import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.JacquetSubsetSums.SeparationTR
import Formalism.DivisorInequality.StatementObj
import Formalism.QuotientMetricDivisors.DivIntoDualShift

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.L2.Indef

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem dim_of_bij {F : Type} [Field F] {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) F)
    (h : Function.Bijective φ.mulVec) : d = d' := by
  have hb : Function.Bijective φ.mulVecLin := h
  have := (LinearEquiv.ofBijective φ.mulVecLin hb).finrank_eq
  simpa using this

theorem isUnit_det_of_bij {F : Type} [Field F] {d : ℕ} (φ : Matrix (Fin d) (Fin d) F)
    (h : Function.Bijective φ.mulVec) : IsUnit φ.det := by
  first
  | exact (Matrix.isUnit_iff_isUnit_det φ).mp (Matrix.mulVec_injective_iff_isUnit.mp h.1)
  | exact (Matrix.isUnit_iff_isUnit_det φ).mp (Matrix.mulVec_surjective_iff_isUnit.mp h.2)
  | (have hb : Function.Bijective (Matrix.toLin' φ) := h
     have := LinearEquiv.isUnit_det' (LinearEquiv.ofBijective (Matrix.toLin' φ) hb)
     rwa [LinearEquiv.coe_ofBijective, LinearMap.det_toLin'] at this)

theorem finrank_map_bij {F : Type} [Field F] {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) F)
    (h : Function.Bijective φ.mulVec) (A : Submodule F (Fin d → F)) :
    finrank F (A.map φ.mulVecLin) = finrank F A := by
  have hb : Function.Bijective φ.mulVecLin := h
  exact (Submodule.equivMapOfInjective φ.mulVecLin hb.1 A).finrank_eq.symm

theorem sum_finrank {F V Ix : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Fintype Ix] (A : Ix → Submodule F V) (hi : iSupIndep A) (ht : (⨆ p, A p) = ⊤) :
    ∑ p, finrank F (A p) = finrank F V := by
  classical
  have hint : DirectSum.IsInternal A := by
    first
    | exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi ht
    | exact DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top hi ht
  rw [Module.finrank_eq_card_basis (hint.collectedBasis fun p => Module.finBasis F (A p)),
    Fintype.card_sigma]
  simp

theorem finrank_comap_bij {F : Type} [Field F] {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) F)
    (h : Function.Bijective φ.mulVec) (A : Submodule F (Fin d' → F)) :
    finrank F (A.comap φ.mulVecLin) = finrank F A := by
  have hb : Function.Bijective φ.mulVecLin := h
  rw [← finrank_map_bij φ h (A.comap φ.mulVecLin), Submodule.map_comap_eq_of_surjective hb.2]

theorem map_indep {F : Type} [Field F] {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) F)
    (h : Function.Bijective φ.mulVec) {Ix : Type} (A : Ix → Submodule F (Fin d → F)) (hi : iSupIndep A) :
    iSupIndep fun p => (A p).map φ.mulVecLin := by
  have hb : Function.Bijective φ.mulVecLin := h
  intro i
  have hle : (⨆ (j) (_ : j ≠ i), (A j).map φ.mulVecLin) ≤ (⨆ (j) (_ : j ≠ i), A j).map φ.mulVecLin :=
    iSup₂_le fun j hj => Submodule.map_mono (le_iSup₂_of_le j hj le_rfl)
  refine Disjoint.mono_right hle ?_
  rw [Submodule.disjoint_def]
  rintro x ⟨a, ha, rfl⟩ ⟨b, hbB, hab⟩
  have hba : b = a := hb.1 hab
  rw [hba] at hbB
  rw [Submodule.disjoint_def.mp (hi i) a ha hbB, map_zero]

theorem map_iSup_top {F : Type} [Field F] {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) F)
    (h : Function.Bijective φ.mulVec) {Ix : Type} (A : Ix → Submodule F (Fin d → F)) (ht : (⨆ p, A p) = ⊤) :
    (⨆ p, (A p).map φ.mulVecLin) = ⊤ := by
  have hb : Function.Bijective φ.mulVecLin := h
  rw [← Submodule.map_iSup, ht, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hb.2

theorem comap_indep {F : Type} [Field F] {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) F)
    (h : Function.Bijective φ.mulVec) {Ix : Type} (A : Ix → Submodule F (Fin d' → F)) (hi : iSupIndep A) :
    iSupIndep fun p => (A p).comap φ.mulVecLin := by
  have hb : Function.Bijective φ.mulVecLin := h
  intro i
  have hle : (⨆ (j) (_ : j ≠ i), (A j).comap φ.mulVecLin) ≤ (⨆ (j) (_ : j ≠ i), A j).comap φ.mulVecLin :=
    iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂_of_le j hj le_rfl)
  refine Disjoint.mono_right hle ?_
  rw [Submodule.disjoint_def]
  intro x hx1 hx2
  apply hb.1
  rw [map_zero]
  exact Submodule.disjoint_def.mp (hi i) _ hx1 hx2

theorem comap_iSup_top {F : Type} [Field F] {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) F)
    (h : Function.Bijective φ.mulVec) {Ix : Type} (A : Ix → Submodule F (Fin d' → F)) (ht : (⨆ p, A p) = ⊤) :
    (⨆ p, (A p).comap φ.mulVecLin) = ⊤ := by
  have hb : Function.Bijective φ.mulVecLin := h
  have e1 : (⨆ p, (A p).comap φ.mulVecLin).map φ.mulVecLin = ⊤ := by
    rw [Submodule.map_iSup]
    simp only [Submodule.map_comap_eq_of_surjective hb.2]
    exact ht
  have e2 := congrArg (Submodule.comap φ.mulVecLin) e1
  rwa [Submodule.comap_map_eq_of_injective hb.1, Submodule.comap_top] at e2

namespace IndefRows

variable {Bs : DefBase K} {Df : DefSide Bs} (S : IndefRows Df)

include S

theorem dQ_eq (t : Bs.Tup) : Df.dQ t = S.D := dim_of_bij (S.ι t) (S.l1c.1 t)

theorem dZ_eq (j : Bs.J) (t : Bs.Tup) : Df.dZ j t = S.dW j := dim_of_bij (S.θ j t) (S.l1c.2.1 j t)

theorem Qpart_base (p : Bs.Ix) : S.Qpart Bs.μ0 p = Df.Qp Bs.μ0 p := by
  have hb : Function.Bijective (S.ι Bs.μ0).mulVecLin := S.l1c.1 Bs.μ0
  show (S.Ep p).comap (S.ι Bs.μ0).mulVecLin = _
  rw [← S.l1a.1 p, Submodule.comap_map_eq_of_injective hb.1]

theorem part_dim (j : Bs.J) (t : Bs.Tup) (p : Bs.Ix) :
    finrank K (S.Qpart t p) = finrank K (S.Zpart j t p) := by
  show finrank K ((S.Ep p).comap (S.ι t).mulVecLin) = finrank K ((S.Wp j p).comap (S.θ j t).mulVecLin)
  rw [finrank_comap_bij _ (S.l1c.1 t), finrank_comap_bij _ (S.l1c.2.1 j t), S.l1d j p]

theorem dW_eq (wf : Df.WF) (j : Bs.J) : S.dW j = S.D := by
  have hb0 := S.l1c.1 Bs.μ0
  have hθ0 := S.l1c.2.1 j Bs.μ0
  have he : S.Ep = fun p => (Df.Qp Bs.μ0 p).map (S.ι Bs.μ0).mulVecLin :=
    funext fun p => (S.l1a.1 p).symm
  have hw : S.Wp j = fun p => (Df.Zp j Bs.μ0 p).map (S.θ j Bs.μ0).mulVecLin :=
    funext fun p => (S.l1a.2 j p).symm
  have a := sum_finrank (S.Wp j) (by rw [hw]; exact map_indep _ hθ0 _ (wf.Zp_indep j))
    (by rw [hw]; exact map_iSup_top _ hθ0 _ (S.4 j))
  have b := sum_finrank S.Ep (by rw [he]; exact map_indep _ hb0 _ wf.Qp_indep)
    (by rw [he]; exact map_iSup_top _ hb0 _ wf.Qp_top)
  first
  | simp only [Module.finrank_fin_fun] at a b
  | simp at a b
  calc S.dW j = ∑ p, finrank K (S.Wp j p) := a.symm
    _ = ∑ p, finrank K (S.Ep p) := Finset.sum_congr rfl fun p _ => S.l1d j p
    _ = S.D := b

theorem rankZ (wf : Df.WF) (j : Bs.J) (t : Bs.Tup) : Df.dZ j t = S.D := by
  rw [S.dZ_eq j t, S.dW_eq wf j]

theorem D_pos : 0 < S.D := by
  rw [← S.dQ_eq Bs.μ0]
  exact S.2

theorem Ep_decomp (wf : Df.WF) : iSupIndep S.Ep ∧ (⨆ p, S.Ep p) = ⊤ := by
  have hb0 := S.l1c.1 Bs.μ0
  have he : S.Ep = fun p => (Df.Qp Bs.μ0 p).map (S.ι Bs.μ0).mulVecLin :=
    funext fun p => (S.l1a.1 p).symm
  rw [he]
  exact ⟨map_indep _ hb0 _ wf.Qp_indep, map_iSup_top _ hb0 _ wf.Qp_top⟩

theorem Wp_decomp (wf : Df.WF) (j : Bs.J) : iSupIndep (S.Wp j) ∧ (⨆ p, S.Wp j p) = ⊤ := by
  have hθ0 := S.l1c.2.1 j Bs.μ0
  have hw : S.Wp j = fun p => (Df.Zp j Bs.μ0 p).map (S.θ j Bs.μ0).mulVecLin :=
    funext fun p => (S.l1a.2 j p).symm
  rw [hw]
  exact ⟨map_indep _ hθ0 _ (wf.Zp_indep j), map_iSup_top _ hθ0 _ (S.4 j)⟩

theorem Qpart_decomp (wf : Df.WF) (t : Bs.Tup) : iSupIndep (S.Qpart t) ∧ (⨆ p, S.Qpart t p) = ⊤ := by
  obtain ⟨h1, h2⟩ := S.Ep_decomp wf
  exact ⟨comap_indep (S.ι t) (S.l1c.1 t) S.Ep h1, comap_iSup_top (S.ι t) (S.l1c.1 t) S.Ep h2⟩

theorem Zpart_decomp (wf : Df.WF) (j : Bs.J) (t : Bs.Tup) :
    iSupIndep (S.Zpart j t) ∧ (⨆ p, S.Zpart j t p) = ⊤ := by
  obtain ⟨h1, h2⟩ := S.Wp_decomp wf j
  exact ⟨comap_indep (S.θ j t) (S.l1c.2.1 j t) (S.Wp j) h1,
    comap_iSup_top (S.θ j t) (S.l1c.2.1 j t) (S.Wp j) h2⟩

end IndefRows

theorem specDet_rect (hS : SpecDet) (v : InfinitePlace K) {D dQ : ℕ}
    (XQ : InfinitePlace K → Matrix (Fin dQ) (Fin dQ) ℂ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hXQ : ∀ u, IsUnit (XQ u).det) (hXE : ∀ u, IsUnit (XE u).det)
    (ι : Matrix (Fin D) (Fin dQ) K) (hι : Function.Bijective ι.mulVec)
    (J : Type) [Fintype J] (dZ dW : J → ℕ)
    (XT : ∀ j, InfinitePlace K → Matrix (Fin (dZ j)) (Fin (dZ j)) ℂ)
    (XW : ∀ j, InfinitePlace K → Matrix (Fin (dW j)) (Fin (dW j)) ℂ)
    (hXT : ∀ j u, IsUnit (XT j u).det) (hXW : ∀ j u, IsUnit (XW j u).det)
    (θ : ∀ j, Matrix (Fin (dW j)) (Fin (dZ j)) K) (hθ : ∀ j, Function.Bijective (θ j).mulVec)
    (Ix : Type) [Fintype Ix] (Qp : Ix → Submodule K (Fin dQ → K))
    (Tq : ∀ j, Ix → Submodule K (Fin (dZ j) → K))
    (h1 : iSupIndep Qp) (h2 : (⨆ p, Qp p) = ⊤) (h3 : ∀ j, iSupIndep (Tq j)) (h4 : ∀ j, (⨆ p, Tq j p) = ⊤)
    (h5 : ∀ j p, finrank K (Qp p) = finrank K (Tq j p)) (s : ℝ) (lam : J → Ix → ℝ)
    (h6 : ∀ p, IsScalarOn XQ XE v ι (Qp p) (s * ∏ j, lam j p))
    (h7 : ∀ j p, IsScalarOn (XT j) (XW j) v (θ j) (Tq j p) (lam j p)) :
    detRatio XQ XE ι v = s ^ D * ∏ j, detRatio (XT j) (XW j) (θ j) v := by
  obtain rfl : dQ = D := dim_of_bij ι hι
  have hd : dZ = dW := funext fun j => dim_of_bij (θ j) (hθ j)
  subst hd
  exact hS K v _ XQ XE hXQ hXE ι (isUnit_det_of_bij ι hι) J _ XT XW hXT hXW θ
    (fun j => isUnit_det_of_bij (θ j) (hθ j)) Ix Qp Tq h1 h2 h3 h4 h5 s lam h6 h7

theorem IndefRows.detId (hS : SpecDet) {Bs : DefBase K} {Df : DefSide Bs} (wf : Df.WF)
    (S : IndefRows Df) (t : Bs.Tup) (v : InfinitePlace K) (h : t = Bs.μ0 ∨ v = Bs.v0) :
    detRatio (Df.XQ t) S.XE (S.ι t) v =
      S.κ v ^ S.D * ∏ j, detRatio (Df.XT j t) (S.XW j) (S.θ j t) v :=
  specDet_rect hS v (Df.XQ t) S.XE (fun u => (wf.XQ_quot t u).1) S.frames.1 (S.ι t) (S.l1c.1 t) Bs.J
    (fun j => Df.dZ j t) S.dW (fun j => Df.XT j t) S.XW (fun j => (wf.XT_herm j t).1) S.frames.2.1
    (fun j => S.θ j t) (fun j => S.l1c.2.1 j t) Bs.Ix (S.Qpart t) (fun j => S.Zpart j t) (S.Qpart_decomp wf t).1
    (S.Qpart_decomp wf t).2 (fun j => (S.Zpart_decomp wf j t).1) (fun j => (S.Zpart_decomp wf j t).2)
    (fun j p => S.part_dim j t p)
    (S.κ v) (fun j p => S.lam j t p v) (S.l1c.2.2.2.2.1 t v h) (fun j => S.l1c.2.2.2.2.2 j t v h)

theorem matLat_lattice {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) K) (h : Function.Surjective φ.mulVec)
    (L : Submodule (𝓞 K) (Fin d → K)) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (matLat φ L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have h1 : ((matLat φ L : Submodule (𝓞 K) (Fin d' → K)) : Set (Fin d' → K)) =
      φ.mulVecLin '' (L : Set (Fin d → K)) := by
    ext x; simp [matLat]
  rw [h1, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact h

theorem twisted_finite {Bs : DefBase K} {Df : DefSide Bs} (S : IndefRows Df) : {w | S.μ w ≠ Bs.μ0}.Finite := (S.Tw.finite_toSet).subset fun w hw => (S.5.2 w).mpr hw

theorem IndefRows.RR_spec (hG : LatticeGlue) {Bs : DefBase K} {Df : DefSide Bs} (wf : Df.WF)
    (S : IndefRows Df) :
    Submodule.IsLattice K S.RR ∧ ∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal S.RR =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))) := by
  refine hG K S.D (matLat (S.ι Bs.μ0) (Df.abelian₂ Bs.μ0)) (fun w => matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w)))
    (matLat_lattice _ (S.l1c.1 _).2 _ (wf.Lam_lat _)) (fun w => matLat_lattice _ (S.l1c.1 _).2 _ (wf.Lam_lat _))
    ((twisted_finite S).subset fun w hw => ?_)
  intro h
  apply hw
  show Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))) = _
  rw [h]

theorem vw_one (w : HeightOneSpectrum (𝓞 K)) : vw w (1 : K) = 0 := by
  first
  | simp only [vw, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  | simp [vw]

theorem IndefRows.stepB [IsTotallyComplex K] (hB : StepBW) (hS : SpecDet) (hR0 : GramDeterminantQuotientMetric) (hRb : LemmaRb)
    (hG : LatticeGlue) {Bs : DefBase K} {Df : DefSide Bs} (wf : Df.WF) (S : IndefRows Df)
    (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df.dQ t) → Fin (Df.dQ t) → K)
    (heb : ∀ t w, IsLocBasis (Df.abelian₂ t) w (eb t w)) :
    (Function.support fun w => lw w * ((vw w (Df.Gm eb (S.μ w) w) : ℝ) + ∑ j, S.Aw j w)).Finite ∧
    lcv S.XE S.RR ≤ (S.D : ℝ) * meanLog S.κ + ∑ j, lcv (S.XW j) (S.M j) +
      ∑ᶠ w, lw w * ((vw w (Df.Gm eb (S.μ w) w) : ℝ) + ∑ j, S.Aw j w) := by
  have hdet0 := fun v => S.detId hS wf Bs.μ0 v (Or.inl rfl)
  have hdet1 := fun t => S.detId hS wf t Bs.v0 (Or.inr rfl)
  have hRR := S.RR_spec hG wf
  have hQ := S.dQ_eq
  have hZ := S.dZ_eq
  have hfr := S.frames
  have hc := S.l1c
  have h0 := S.h0
  have htw := twisted_finite S
  have hprov := S.proviso
  obtain ⟨⟨μ, Tw, D, XE, Ep, ι, dW, XW, Wp, M, θ, κ, lam, err0⟩, _p1, _p2, _p3, _g0, _g1, _g2, _g3, _g4⟩ := S
  obtain ⟨nV, HV, Mt, dQ, Pq, XQ, Qp, dZ, HT, XT, Tl, Zp⟩ := Df
  dsimp only [DefSide.Proviso] at hdet0 hdet1 hRR hQ hZ hfr hc h0 htw hprov eb heb
  obtain rfl : dQ = fun _ => D := funext hQ
  obtain rfl : dZ = fun j _ => dW j := funext fun j => funext fun t => hZ j t
  exact hB K Bs.K0 wf.cm Bs.v0 wf.conj D XE hfr.1 Bs.Tup Bs.μ0 μ h0.1 htw XQ
    (fun t v => (wf.XQ_quot t v).1) (fun t => matLat (Pq t) (Mt t)) wf.Lam_lat ι
    (fun t => isUnit_det_of_bij _ (hc.1 t)) Bs.J dW XW hfr.2.1 M hfr.2.2 HT XT hprov wf.XT_herm Tl
    wf.Tl_lat θ (fun j t => isUnit_det_of_bij _ (hc.2.1 j t)) κ hc.2.2.1 (fun _ => 1) (fun _ => 1)
    (fun _ => by simp) rfl (fun _ => one_pos) (fun w => vw_one w) hdet0
    (fun t => by simpa only [mul_one] using hdet1 t)
    (fun t w => gramR (quotGram (Pq t) (HV t)) (eb t w)) eb heb
    (fun t w => (hR0 K Bs.K0 wf.cm Bs.v0 wf.conj (nV t) D (HV t) (wf.HV_rat t) (wf.HV_pos t) (Pq t)
      (wf.Pq_surj t) (XQ t) (wf.XQ_quot t) (eb t w)).2)
    (hRb K Bs.K0 wf.cm Bs.v0 wf.conj (nV Bs.μ0) D (HV Bs.μ0) (wf.HV_rat _) (wf.HV_pos _) (Pq Bs.μ0)
      (wf.Pq_surj _) (XQ Bs.μ0) (wf.XQ_quot _) (Mt Bs.μ0) (wf.Mt_lat _) (eb Bs.μ0) (heb Bs.μ0)).2
    _ hRR.1 hRR.2

theorem IndefSide.boundsMu [IsTotallyComplex K] (hM : Formalism.DivisorInequality.BoundsMu) (hS : SpecDet) (hR0 : GramDeterminantQuotientMetric)
    (hG : LatticeGlue) (hRam : RamBasic) {Bs : DefBase K} {Df : DefSide Bs} {N : IndefNum Bs} (wf : Df.WF)
    (S : IndefSide Df N) (hU : S.toIndefData.Untwisted N)
    (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df.dQ t) → Fin (Df.dQ t) → K)
    (heb : ∀ t w, IsLocBasis (Df.abelian₂ t) w (eb t w))
    (Sy : Finset (HeightOneSpectrum (𝓞 K))) (hSy : S.Tw ⊆ Sy)
    (hG0 : ∀ y, y ∉ Sy → vw y (Df.Gm eb (S.μ y) y) = 0)
    (LG E3 : ℝ) (E2 : Bs.J → ℝ) (gy : HeightOneSpectrum (𝓞 K) → ℝ) (ηy : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ)
    (hi : ∀ y ∈ Sy, (vw y (Df.Gm eb (S.μ y) y) : ℝ) ≤ (S.D : ℝ) * gy y)
    (hLG : ∑ y ∈ Sy, lw y * gy y ≤ LG)
    (hiv : ∀ y ∈ S.Tw, ∀ j, (jw (Df.HT j (S.μ y)) y (Df.Tl j (S.μ y)) : ℝ) ≤
      ((ramw y : ℝ) * N.J0 (S.μ y) y j) * (S.D : ℝ) + ηy y j)
    (hE2 : ∀ j, ∑ y ∈ S.Tw, lw y * ηy y j / (S.D : ℝ) ≤ E2 j)
    (hE3 : ∑ y ∈ Sy, lw y * (2 / ellw y ^ 2) ≤ E3) :
    Formalism.HN.muDef (Pi.basisFun K (Fin S.D)).dualBasis (Formalism.HN.dualFrame S.XE) (Formalism.HN.dualLat S.RR) ≤
      meanLog S.κ + (∑ j, N.l3 j) + 2 * (∑ j, ∑ y ∈ S.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)) + LG +
        (∑ j, (N.E1 j + E2 j)) + E3 := by
  have hdet0 := fun v => S.toIndefRows.detId hS wf Bs.μ0 v (Or.inl rfl)
  have hdet1 := fun t => S.toIndefRows.detId hS wf t Bs.v0 (Or.inr rfl)
  have hRR := S.toIndefRows.RR_spec hG wf
  have hQ := S.toIndefRows.dQ_eq
  have hZ := S.toIndefRows.dZ_eq
  have hW := S.toIndefRows.dW_eq wf
  have hD := S.toIndefRows.D_pos
  have hfr := S.frames
  have hc := S.l1c
  have hl3 := S.l3
  have hon := S.on
  have h0 := S.h0
  have htw := twisted_finite S.toIndefRows
  have hprov := S.proviso
  have hout : ∀ y, y ∉ Sy → lw y * ((vw y (Df.Gm eb (S.μ y) y) : ℝ) + ∑ j, S.Aw j y) = 0 := by
    intro y hy
    rw [hG0 y hy, Finset.sum_eq_zero fun j _ => (hU y (fun h => hy (hSy h)) j).1]
    simp
  have hmid : ∀ y ∈ Sy, y ∉ S.Tw → ∀ j, S.Aw j y = 0 := fun y _ hy j => (hU y hy j).1
  have hF : ∀ y ∈ Sy, y ∉ S.Tw → ∀ j, (ramw y : ℝ) * N.F0 y j = 0 := fun y _ hy j => by
    rw [(hU y hy j).2, mul_zero]
  have hiii : ∀ y ∈ S.Tw, ∑ j, ((S.Iw j (S.μ y) y : ℝ) + (S.Iw j (S.μ y) (conjPl y) : ℝ)) ≤
      (∑ j, (2 * ((ramw y : ℝ) * N.F0 y j) + (ramw y : ℝ) * S.err0 y j) + 2 / ellw y ^ 2) * (S.D : ℝ) := by
    intro y hy
    rw [(hRam K y).2.2.2.2]
    exact hon.1 y hy
  obtain ⟨⟨⟨μ, Tw, D, XE, Ep, ι, dW, XW, Wp, M, θ, κ, lam, err0⟩, _p1, _p2, _p3, _g0, _g1, _g2, _g3, _g4⟩, _g6, _g7⟩ := S
  obtain ⟨nV, HV, Mt, dQ, Pq, XQ, Qp, dZ, HT, XT, Tl, Zp⟩ := Df
  dsimp only [DefSide.Proviso] at hdet0 hdet1 hRR hQ hZ hW hD hfr hc hl3 hon h0 htw hprov hout hmid hF hiii eb heb hi hiv hE2 hG0 hSy hLG hE3
  obtain rfl : dW = fun _ => D := funext hW
  obtain rfl : dQ = fun _ => D := funext hQ
  obtain rfl : dZ = fun _ _ => D := funext fun j => funext fun t => hZ j t
  have H := (hM K Bs.K0 wf.cm Bs.v0 wf.conj D XE hD hfr.1 Bs.Tup Bs.μ0 μ h0.1 htw XQ
    (fun t v => (wf.XQ_quot t v).1) (fun t => matLat (Pq t) (Mt t)) wf.Lam_lat ι
    (fun t => isUnit_det_of_bij _ (hc.1 t)) Bs.J XW hfr.2.1 M hfr.2.2 HT XT hprov wf.XT_herm Tl
    wf.Tl_lat θ (fun j t => isUnit_det_of_bij _ (hc.2.1 j t)) κ hc.2.2.1 (fun _ => 1) (fun _ => 1)
    (fun _ => by simp) rfl (fun _ => one_pos) (fun w => vw_one w) hdet0
    (fun t => by simpa only [mul_one] using hdet1 t)
    (fun t w => gramR (quotGram (Pq t) (HV t)) (eb t w)) eb heb
    (fun t w => (hR0 K Bs.K0 wf.cm Bs.v0 wf.conj (nV t) D (HV t) (wf.HV_rat t) (wf.HV_pos t) (Pq t)
      (wf.Pq_surj t) (XQ t) (wf.XQ_quot t) (eb t w)).2)
    (nV Bs.μ0) (HV Bs.μ0) (wf.HV_rat _) (wf.HV_pos _) (Pq Bs.μ0) (wf.Pq_surj _) (wf.XQ_quot _) (Mt Bs.μ0)
    (wf.Mt_lat _) rfl (fun _ => rfl) _ hRR.1 hRR.2 Sy Tw hSy hout hmid LG E3 N.E1 E2 ellw gy
    (fun y j => (ramw y : ℝ) * N.F0 y j) (fun y j => (ramw y : ℝ) * err0 y j)
    (fun y j => (ramw y : ℝ) * N.J0 (μ y) y j) ηy hF hi hLG hiii hiv hon.2.2 hE2 hE3).1
  have h3 : ∑ j, lcv (XW j) (M j) / (D : ℝ) ≤ ∑ j, N.l3 j := Finset.sum_le_sum fun j _ => hl3 j
  linarith [H, h3]

theorem IndefCols.log_eigenvalue_sum_le_min {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
    [Nonempty Bs.Ix] (S : IndefCols Df Dc Sp N) (v : InfinitePlace K) :
    ∑ j, N.l6 j ≤ minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) :=
  Finset.le_inf' _ _ fun p _ => Finset.sum_le_sum fun j _ => S.l6 j p v

theorem IndefCols.height (hH : HeightBoundConstant) {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc}
    {N : IndefNum Bs} [Nonempty Bs.Ix] (wf : Df.WF) (S : IndefCols Df Dc Sp N) (u : Dc.Mem) (hXc : ∀ v, IsUnit (Dc.Xc u v).det)
    (hne : S.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding)
    (pU : InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u)
      (Pi.basisFun K (Fin (Df.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v (Dc.Pt u Bs.μ0) ≤ pU v) :
    Formalism.HN.htMap (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin S.D)).dualBasis
              (Formalism.HN.dualFrame S.XE) (S.col.B u) ≤
      (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (pU v ^ 2) - ∑ j, N.l6 j - meanLog S.κ := by
  have hQ := S.toIndefRows.dQ_eq
  have hfr := S.frames
  have hc := S.l1c
  have hb := S.l1b
  have hmin := S.log_eigenvalue_sum_le_min
  have hsc : ∀ v p, IsScalarOn (Df.XQ Bs.μ0) S.XE v (S.ι Bs.μ0) (Df.Qp Bs.μ0 p)
      (S.κ v * ∏ j, S.lam j Bs.μ0 p v) := fun v p => by
    rw [← S.toIndefRows.Qpart_base p]; exact hc.2.2.2.2.1 Bs.μ0 v (Or.inl rfl) p
  obtain ⟨⟨⟨μ, Tw, D, XE, Ep, ι, dW, XW, Wp, M, θ, κ, lam, err0⟩, _p1, _p2, _p3, _g0, _g1, _g2, _g3, _g4⟩, _g5, ⟨B, ζ, sE⟩, _g6, _g7⟩ := S
  obtain ⟨HH, nHH, iHH, Pu, Rw⟩ := Sp
  obtain ⟨Mem, a, Xc, Pt⟩ := Dc
  obtain ⟨nV, HV, Mt, dQ, Pq, XQ, Qp, dZ, HT, XT, Tl, Zp⟩ := Df
  dsimp only at hQ hfr hc hb hmin hsc hXc hne X0 hX0 hpU u
  obtain rfl : dQ = fun _ => D := funext hQ
  have H := (hH K (nV Bs.μ0) D 0 (fun _ => a u) (fun _ => Xc u) (fun _ => hXc) (fun j => j.elim0) (HV Bs.μ0) X0 hX0
    (Pq Bs.μ0) (wf.Pq_surj _) (XQ Bs.μ0) (wf.XQ_quot _) XE hfr.1 (ι Bs.μ0) (isUnit_det_of_bij _ (hc.1 _))
    Bs.Ix Bs.J (Qp Bs.μ0) wf.Qp_top κ (fun j p v => lam j Bs.μ0 p v) (fun j p v => lam j Bs.μ0 p v)
    hc.2.2.1 (fun j p v => hc.2.2.2.1 j _ p v) (fun _ _ _ => le_rfl)
    hsc (Pt u Bs.μ0) (B u)
    (fun φ F => by
      have h1 := hb.1 u Bs.μ0 φ F
      rw [hb.2.1 u, one_mul] at h1
      rw [← h1]
      show _ = Pt u Bs.μ0 ((1 : Matrix (Fin (a u)) (Fin (a u)) K).mulVec φ) F
      rw [Matrix.one_mulVec])
    hne pU (fun j => j.elim0) hpU (fun j => j.elim0)).2
  have hn : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    exact_mod_cast this
  have h2 : ∑ j, N.l6 j ≤ (1 / (Formalism.HN.nPl K : ℝ)) *
      ∑ v, minOver (fun p => ∑ j, Real.log (lam j Bs.μ0 p v)) := by
    have h3 : ∑ _v : InfinitePlace K, ∑ j, N.l6 j ≤
        ∑ v, minOver (fun p => ∑ j, Real.log (lam j Bs.μ0 p v)) := Finset.sum_le_sum fun v _ => hmin v
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
    rw [one_div, le_inv_mul_iff₀ hn]
    exact h3
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at H
  linarith [H, h2]

theorem matLat_mul {d d' d'' : ℕ} (A : Matrix (Fin d'') (Fin d') K) (B : Matrix (Fin d') (Fin d) K)
    (L : Submodule (𝓞 K) (Fin d → K)) : matLat (A * B) L = matLat A (matLat B L) := by
  first
  | (ext x
     simp only [matLat, Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
     constructor
     · rintro ⟨y, hy, rfl⟩
       exact ⟨B.mulVec y, ⟨y, hy, rfl⟩, Matrix.mulVec_mulVec y A B⟩
     · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
       exact ⟨y, hy, (Matrix.mulVec_mulVec y A B).symm⟩)
  | (ext x
     simp [matLat, Submodule.mem_map, Matrix.mulVec_mulVec])

theorem matLat_one {d : ℕ} (L : Submodule (𝓞 K) (Fin d → K)) : matLat (1 : Matrix (Fin d) (Fin d) K) L = L := by
  ext x
  simp [matLat]

theorem IndefCols.intoDual (hD : DivIntoDualShift) (hG : LatticeGlue) {Bs : DefBase K} {Df : DefSide Bs}
    {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs} (wf : Df.WF) (S : IndefCols Df Dc Sp N) (u : Dc.Mem)
    (Nu Nu' : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (σ : HeightOneSpectrum (𝓞 K) → ℝ)
    (τ : HeightOneSpectrum (𝓞 K) → ℤ)
    (hL2 : ∀ w, ∀ φ ∈ Nu, ∀ F ∈ Df.Mt (S.μ w),
      Dc.Pt u (S.μ w) φ F = 0 ∨ σ w ≤ (vw w (Dc.Pt u (S.μ w) φ F) : ℝ))
    (hτ : ∀ w, τ w ≤ ⌈σ w⌉) (hsh : IsShift Nu Nu' τ) :
    ∀ φ ∈ Nu', S.col.B u φ ∈ Formalism.HN.dualLat S.RR := by
  intro φ hφ x hx
  refine hD K (Dc.a u) S.D S.RR (S.col.B u) (fun w => Df.nV (S.μ w)) (fun w => Df.Mt (S.μ w))
    (fun w => S.ι (S.μ w) * Df.Pq (S.μ w)) (fun _ => 1) (fun w => Dc.Pt u (S.μ w))
    (fun w => S.col.ζ u (S.μ w)) (fun w => S.l1b.2.2.1 u _) (fun w => S.l1b.2.2.2 u w)
    (fun w φ F => ?_) Nu Nu' σ τ hL2 hτ hsh (fun w => ?_) φ hφ x hx
  · rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    exact S.l1b.1 u _ φ F
  · rw [matLat_one, matLat_mul]
    exact (S.toIndefRows.RR_spec hG wf).2 w

theorem LevelLink.Tw_eq {Bs : DefBase K} {Df Df' : DefSide Bs} {S : IndefData Df} {S' : IndefData Df'}
    (h : LevelLink S S') (h0 : S.H0) (h0' : S'.H0) : S.Tw = S'.Tw := by
  ext w
  rw [h0.2 w, h0'.2 w, h.1]

namespace IndefCore

variable {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
  (P : IndefCore Df0 Df1 Dc Sp N)

include P

theorem base_level_log_eigenvalue_bound : P.base.toIndefData.L6 N := fun j p v => by
  rw [P.extra.level.2.2]; exact P.cols.l6 j p v

theorem fun1 (hde : 0 ≤ N.de) (hde3 : N.de ≤ 1 / 3) :
    P.cols.muMaxRR ≤ N.hh - meanLog P.cols.κ + 14 * N.la := by
  rw [← P.extra.level.2.1]; exact (P.extra.passage hde hde3 _ P.extra.fun0).1

end IndefCore

namespace ColData

variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {S : IndefData Df} (C : ColData Dc Sp S)

theorem fnorm_eq_zero {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y.det) (y : Fin n → ℂ) (h : fnorm Y y = 0) : y = 0 := by
  have h1 : ∑ i, ‖(Y⁻¹.mulVec y) i‖ ^ 2 = 0 := by
    have h' : Real.sqrt (∑ i, ‖(Y⁻¹.mulVec y) i‖ ^ 2) = 0 := h
    rwa [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => by positivity)] at h'
  have h2 : Y⁻¹.mulVec y = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp h1 i (Finset.mem_univ i)
    simpa using this
  calc y = (Y * Y⁻¹).mulVec y := by rw [Matrix.mul_nonsing_inv Y hY, Matrix.one_mulVec]
    _ = Y.mulVec (Y⁻¹.mulVec y) := (Matrix.mulVec_mulVec y Y Y⁻¹).symm
    _ = 0 := by rw [h2, Matrix.mulVec_zero]

theorem period_images_surjective (h : C.L1e) (hX : IsUnit (S.XE Bs.v0).det) (hD : 0 < S.D) (z : Sp.HH) (hz : z ∈ Sp.Rw) : ∃ y, C.sE y = z := by
  obtain ⟨hs, hm, hr, -⟩ := h
  have hinj : Function.Injective C.sE := by
    intro y1 y2 h12
    have h0 : C.sE (y1 - y2) = 0 := by rw [map_sub, h12, sub_self]
    have := hs (y1 - y2)
    rw [h0, norm_zero] at this
    exact sub_eq_zero.mp (fnorm_eq_zero _ hX _ this.symm)
  have hfin : FiniteDimensional ℂ Sp.Rw := Module.finite_of_finrank_pos (by rw [hr]; exact hD)
  let g : (Fin S.D → ℂ) →ₗ[ℂ] Sp.HH :=
    { toFun := fun y => C.sE (star y)
      map_add' := fun a b => by simp only [star_add, map_add]
      map_smul' := fun c a => by
        first
        | simp only [star_smul, map_smulₛₗ, starRingEnd_apply, star_star, RingHom.id_apply]
        | (simp only [RingHom.id_apply]
           rw [star_smul, map_smulₛₗ, starRingEnd_apply, star_star]) }
  have hinjg : Function.Injective g := fun a b hab => star_injective (hinj hab)
  have hle : LinearMap.range g ≤ Sp.Rw := by
    rintro _ ⟨y, rfl⟩
    exact hm _
  have hrank : finrank ℂ (LinearMap.range g) = finrank ℂ Sp.Rw := by
    rw [LinearMap.finrank_range_of_inj hinjg, hr]
    simp
  have heq : LinearMap.range g = Sp.Rw := by
    by_contra hne
    exact (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)).ne hrank
  rw [← heq] at hz
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hz
  exact ⟨star y, hy⟩

end ColData

theorem IndefCore.divCore [IsTotallyComplex K] (hM : Formalism.DivisorInequality.BoundsMu) (hS : SpecDet) (hR0 : GramDeterminantQuotientMetric)
    (hG : LatticeGlue) (hRam : RamBasic) (hH : HeightBoundConstant) {Bs : DefBase K} {Df0 Df1 : DefSide Bs}
    {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs} [Nonempty Bs.Ix] (wf0 : Df0.WF) (wf1 : Df1.WF)
    (P : IndefCore Df0 Df1 Dc Sp N) (hde : 0 ≤ N.de) (hde3 : N.de ≤ 1 / 3)
    (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df0.dQ t) → Fin (Df0.dQ t) → K)
    (heb : ∀ t w, IsLocBasis (Df0.abelian₂ t) w (eb t w))
    (Sy : Finset (HeightOneSpectrum (𝓞 K))) (hSy : P.base.Tw ⊆ Sy)
    (hG0 : ∀ y, y ∉ Sy → vw y (Df0.Gm eb (P.base.μ y) y) = 0)
    (LG E3 : ℝ) (E2 : Bs.J → ℝ) (gy : HeightOneSpectrum (𝓞 K) → ℝ) (ηy : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ)
    (hi : ∀ y ∈ Sy, (vw y (Df0.Gm eb (P.base.μ y) y) : ℝ) ≤ (P.base.D : ℝ) * gy y)
    (hLG : ∑ y ∈ Sy, lw y * gy y ≤ LG)
    (hiv : ∀ y ∈ P.base.Tw, ∀ j, (jw (Df0.HT j (P.base.μ y)) y (Df0.Tl j (P.base.μ y)) : ℝ) ≤
      ((ramw y : ℝ) * N.J0 (P.base.μ y) y j) * (P.base.D : ℝ) + ηy y j)
    (hE2 : ∀ j, ∑ y ∈ P.base.Tw, lw y * ηy y j / (P.base.D : ℝ) ≤ E2 j)
    (hE3 : ∑ y ∈ Sy, lw y * (2 / ellw y ^ 2) ≤ E3)
    (u : Dc.Mem) (hXc : ∀ v, IsUnit (Dc.Xc u v).det) (hne : P.cols.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin (Df1.nV Bs.μ0)) (Fin (Df1.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df1.HV Bs.μ0).map v.embedding)
    (pU : InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u)
      (Pi.basisFun K (Fin (Df1.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v (Dc.Pt u Bs.μ0) ≤ pU v)
    (X : ℝ)
    (hX : X = (∑ j, N.l3 j) + 2 * (∑ j, ∑ y ∈ P.base.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)) + LG +
      (∑ j, (N.E1 j + E2 j)) + E3) :
    P.cols.muCC + Formalism.HN.htMap (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin P.cols.D)).dualBasis
        (Formalism.HN.dualFrame P.cols.XE) (P.cols.col.B u) ≤
      X + 3 * N.de * (X + N.hh + 28 * N.la) + 28 * N.la +
        ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (pU v ^ 2) - ∑ j, N.l6 j) := by
  have h0 : P.base.muCC ≤ _ :=
    P.base.boundsMu hM hS hR0 hG hRam wf0 P.extra.untw eb heb Sy hSy hG0 LG E3 E2 gy ηy hi hLG hiv hE2 hE3
  have hp := (P.extra.passage hde hde3 _ P.extra.fun0).2
  have hh := P.cols.height hH wf1 u hXc hne X0 hX0 pU hpU
  have hκ : meanLog P.cols.κ = meanLog P.base.κ := by rw [P.extra.level.2.1]
  rw [hκ] at hh
  have h1 : P.base.muCC - meanLog P.base.κ ≤ X := by rw [hX]; linarith [h0]
  have h2 : 3 * N.de * (P.base.muCC + (N.hh - meanLog P.base.κ) + 28 * N.la) ≤
      3 * N.de * (X + N.hh + 28 * N.la) :=
    mul_le_mul_of_nonneg_left (by linarith [h1]) (by linarith [hde])
  linarith [hp, hh, h1, h2]

end Formalism.L2.Indef
