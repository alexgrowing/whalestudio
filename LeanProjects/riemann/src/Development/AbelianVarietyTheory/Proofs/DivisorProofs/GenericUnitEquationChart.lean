import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorDecompositionFlagSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartAffineNeighbourhoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameChartOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameChartOffBoundarySecond
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open Filter Topology
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Mean4O GlobalTheory.Mean4 ReciprocityTheory.AnForm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.HodgeLocGeo.RootModel

open GlobalTheory.GradedNorm in
theorem grSq_transpose' {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) : grSq Mᵀ i = grSq M i := by
  have e (k : Fin (m + 1)) : ReciprocityTheory.ChartRestriction.G.FD.lminor Mᵀ k = ReciprocityTheory.ChartRestriction.G.FD.lminor M k := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
    rw [← transpose_submatrix, det_transpose]
  rw [grSq, grSq, e, e]

theorem conj_gram_transpose {m n : ℕ} (c : ℝ) (B : Matrix (Fin m) (Fin m) ℂ) (Gm : Matrix (Fin m) (Fin n) ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (Gr : Matrix (Fin m) (Fin m) ℂ) (h : Grᵀ = (c : ℂ) • (Gm * P * Gmᴴ)) :
    (Bᴴ * Gr * B)ᵀ = (c : ℂ) • ((Bᵀ * Gm) * P * (Bᵀ * Gm)ᴴ) := by
  have e : (Bᴴ)ᵀ = (Bᵀ)ᴴ := by ext; simp
  rw [transpose_mul, transpose_mul, h, conjTranspose_mul, e]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

open GlobalTheory.GradedNorm in
theorem grSq_wLine_of {m p q p' q' : ℕ} (hm : m = p) (hp : p = p') (hq : q = q') (c : ℝ)
    (B Gm Gr : Matrix (Fin m) (Fin m) ℂ) (zz : Matrix (Fin p) (Fin q) ℂ)
    (h : Grᵀ = (c : ℂ) • (Gm * reindex (finCongr hm.symm) (finCongr hm.symm)
      (1 - zz.map (starRingEnd ℂ) * zzᵀ)⁻¹ * Gmᴴ)) (i : Fin m) :
    grSq (Bᴴ * Gr * B) i = grSq (wLine c ((Bᵀ * Gm).submatrix (Fin.cast (hm.trans hp).symm)
      (Fin.cast (hm.trans hp).symm)) (zz.submatrix (Fin.cast hp.symm) (Fin.cast hq.symm))) (Fin.cast (hm.trans hp) i) := by
  subst hm hp hq
  rw [← grSq_transpose', conj_gram_transpose c B Gm _ Gr h]
  simp [wLine]

open GlobalTheory.GradedNorm in
theorem grSq_oLine_of {m p q p' q' : ℕ} (hm : m = q) (hp : p = p') (hq : q = q') (c : ℝ)
    (B Gm Gr : Matrix (Fin m) (Fin m) ℂ) (zz : Matrix (Fin p) (Fin q) ℂ)
    (h : Grᵀ = (c : ℂ) • (Gm * reindex (finCongr hm.symm) (finCongr hm.symm) (1 - zzᴴ * zz)⁻¹ * Gmᴴ)) (i : Fin m) :
    grSq (Bᴴ * Gr * B) i = grSq (oLine c ((Bᵀ * Gm).submatrix (Fin.cast (hm.trans hq).symm)
      (Fin.cast (hm.trans hq).symm)) (zz.submatrix (Fin.cast hp.symm) (Fin.cast hq.symm))) (Fin.cast (hm.trans hq) i) := by
  subst hm hp hq
  rw [← grSq_transpose', conj_gram_transpose c B Gm _ Gr h]
  simp [oLine]

open GlobalTheory.GradedNorm in
theorem hodge_root_norm_model : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag)
    (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (e : ℕ) (c' : AlgChart (Φ.C k).Y.str σ e) (p0 : (Φ.C k).Y.pts σ),
    p0 ∈ c'.finChart.source → (Φ.C k).π (under p0) ∉ genBd s.T.Z →
    ∃ (t : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Φ.C k).Y.Fnˣ) (U : (Φ.C k).Y.X.Opens)
      (Zm : D.what₂.Tau → (Fin e → ℂ) → Matrix (Fin j) (Fin (N - j)) ℂ)
      (GW : D.what₂.Tau → (Fin e → ℂ) → Matrix (Fin j) (Fin j) ℂ)
      (GΩ : D.what₂.Tau → (Fin e → ℂ) → Matrix (Fin (N - j)) (Fin (N - j)) ℂ) (cW cΩ : D.what₂.Tau → ℝ),
      under p0 ∈ U ∧ (∀ y' ∈ U, ∀ τ i, ((Φ.C k).gr τ i).IsEqn y' (t τ i)) ∧ (∀ τ, 0 < cW τ) ∧ (∀ τ, 0 < cΩ τ) ∧
      ∀ᶠ v in 𝓝 (c'.finChart p0), (∀ τ a b, AnalyticAt ℂ (fun w => Zm τ w a b) v) ∧
        (∀ τ a b, AnalyticAt ℂ (fun w => GW τ w a b) v) ∧ (∀ τ a b, AnalyticAt ℂ (fun w => GΩ τ w a b) v) ∧
        (∀ τ, (1 - (Zm τ v)ᴴ * Zm τ v).PosDef) ∧ (∀ τ, IsUnit (GW τ v).det) ∧ (∀ τ, IsUnit (GΩ τ v).det) ∧
        ∀ r : DV.Rt D.what₂.Tau N, (metsOf x Φ k none σ (rootEx S.Dw (DV.tauEmb D r.1) r.2)).h
            (prodPow t (rootEx S.Dw (DV.tauEmb D r.1) r.2)) (c'.finChart.symm v) =
          rootNorm N j (cW r.1) (cΩ r.1) (GW r.1 v) (GΩ r.1 v) (Zm r.1 v) r.2 := by
  intro D A N j S κ s x Φ k σ e c' p0 hp0 hbd
  classical
  obtain ⟨U, t, V, φ, Fr, Am, hU, hφ, hV, ht, hev⟩ := GlobalTheory.T.algebraic_chart_affine_neighbourhood _ _ _ _ _ _ _ _ _ _ _ (Φ.C k) σ e c' p0 hp0
  obtain ⟨G, z, cc, hcc, hmod⟩ := (em (Formalism.L2.PjFree.GoodEmb κ.c (embOf κ.e σ))).elim
    (fun hg => GlobalTheory.T.eigen_frame_chart_off_boundary D A N j S κ s x Φ k σ hg e c' p0 hp0 hbd V φ Fr hφ hV)
    (fun hg => GlobalTheory.T.eigen_frame_chart_off_boundary_second D A N j S κ s x Φ k σ hg e c' p0 hp0 hbd V φ Fr hφ hV)
  have hp : S.Dw.p = j := S.p_eq
  have hq : S.Dw.q = N - j := by have := S.rank_eq; omega
  have hin : ∀ r : D.what₂.Tau, DV.tauEmb D r (A.H.rt : D.host.E) = A.H.rt0 := A.cm
  have hout : ∀ r : D.what₂.Tau, ¬ conjEmb (DV.tauEmb D r) (A.H.rt : D.host.E) = A.H.rt0 :=
    GlobalTheory.FlagAmple.BorelWeil.conjEmb_tauEmb_rt A
  have hmW : ∀ r : D.what₂.Tau, S.Dw.mult (DV.tauEmb D r) = S.Dw.p := fun r => GlobalTheory.PointChern.mult_of_mem S.Dw (hin r)
  have hmO : ∀ r : D.what₂.Tau, S.Dw.mult (conjEmb (DV.tauEmb D r)) = S.Dw.q := fun r => GlobalTheory.PointChern.mult_of_not_mem S.Dw (hout r)
  refine ⟨t, U, fun r w => (z w ⟨DV.tauEmb D r, hin r⟩).submatrix (Fin.cast hp.symm) (Fin.cast hq.symm),
    fun r w => ((Am (DV.tauEmb D r) w)ᵀ * G w (DV.tauEmb D r)).submatrix (Fin.cast ((hmW r).trans hp).symm)
      (Fin.cast ((hmW r).trans hp).symm),
    fun r w => ((Am (conjEmb (DV.tauEmb D r)) w)ᵀ * G w (conjEmb (DV.tauEmb D r))).submatrix
      (Fin.cast ((hmO r).trans hq).symm) (Fin.cast ((hmO r).trans hq).symm),
    fun r => cc (DV.tauEmb D r), fun r => cc (conjEmb (DV.tauEmb D r)), hU, ht, fun r => hcc _, fun r => hcc _, ?_⟩
  filter_upwards [hev, hmod] with v hv1 hv2
  obtain ⟨hAm, hv, g, f, had, hmap, hco⟩ := hv1
  obtain ⟨hG, hz, hGu, hzd, hv', hgr⟩ := hv2
  have hunit : ∀ τ, IsUnit (Am τ v).det := fun τ => hco τ ▸ EigFrame.isUnit_det_co f g τ
  refine ⟨fun r a b => hz _ _ _, fun r a b => ?_, fun r a b => ?_, fun r => ?_, fun r => ?_, fun r => ?_, ?_⟩
  · exact GlobalTheory.HodgeGramGen.an_mul (A := fun w => (Am (DV.tauEmb D r) w)ᵀ) (fun i k => hAm _ k i) (fun i k => hG _ i k) _ _
  · exact GlobalTheory.HodgeGramGen.an_mul (A := fun w => (Am (conjEmb (DV.tauEmb D r)) w)ᵀ) (fun i k => hAm _ k i)
      (fun i k => hG _ i k) _ _
  · have e : (1 - ((z v ⟨DV.tauEmb D r, hin r⟩).submatrix (Fin.cast hp.symm) (Fin.cast hq.symm))ᴴ *
        (z v ⟨DV.tauEmb D r, hin r⟩).submatrix (Fin.cast hp.symm) (Fin.cast hq.symm)) =
        (1 - (z v ⟨DV.tauEmb D r, hin r⟩)ᴴ * z v ⟨DV.tauEmb D r, hin r⟩).submatrix (finCongr hq.symm) (finCongr hq.symm) := by
      ext a b
      simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, submatrix_apply, one_apply, finCongr_apply]
      congr 1
      · simp [Fin.ext_iff]
      · exact Fintype.sum_equiv (finCongr hp.symm) _ _ fun _ => rfl
    rw [e]
    exact (hzd _).submatrix (finCongr hq.symm).injective
  · rw [show (Fin.cast ((hmW r).trans hp).symm : Fin j → Fin (S.Dw.mult (DV.tauEmb D r))) =
      ⇑(finCongr ((hmW r).trans hp).symm) from rfl, det_submatrix_equiv_self, det_mul, det_transpose]
    exact (hunit _).mul (hGu _)
  · rw [show (Fin.cast ((hmO r).trans hq).symm : Fin (N - j) → Fin (S.Dw.mult (conjEmb (DV.tauEmb D r)))) =
      ⇑(finCongr ((hmO r).trans hq).symm) from rfl, det_submatrix_equiv_self, det_mul, det_transpose]
    exact (hunit _).mul (hGu _)
  rintro ⟨τr, i⟩
  have hgram : ∀ τ, (x.hodge (embOf κ.e σ)).gram ((Φ.C k).down (c'.finChart.symm v)) g τ =
      (Am τ v)ᴴ * (x.hodge (embOf κ.e σ)).gram ((Φ.C k).down (c'.finChart.symm v)) f τ * Am τ v := fun τ => by
    rw [(x.hodge (embOf κ.e σ)).change _ f g τ, hco τ]
  show ((Φ.C k).met (x.hodge (embOf κ.e σ)) _).h _ _ = _
  rw [FlagCpt.met_h _ _ had]
  simp only [prodPow, Pi.one_apply, _root_.one_zpow, Finset.prod_const_one, Units.val_one, norm_one, one_pow, div_one]
  rw [FlagCpt.genSq, rootNorm]
  set τ := DV.tauEmb D τr with hτ
  split_ifs with hi
  · have hi' : (i : ℕ) < S.Dw.p := by omega
    let L : Letter S.Dw := ⟨τ, ⟨i, by rw [hmW]; exact hi'⟩⟩
    rw [Finset.prod_eq_single L ?_ (by simp)]
    · rw [GlobalTheory.FlagAmple.BorelWeil.rootEx_apply, if_pos hi', if_pos ⟨rfl, rfl⟩, zpow_one, hgram]
      have hmg : GlobalTheory.PointChern.modelGram A.H S.Dw (z v) τ = reindex (finCongr (hmW τr).symm) (finCongr (hmW τr).symm)
          (1 - (z v ⟨τ, hin τr⟩).map (starRingEnd ℂ) * (z v ⟨τ, hin τr⟩)ᵀ)⁻¹ := by
        unfold GlobalTheory.PointChern.modelGram
        rw [dif_pos (show τ (A.H.rt : D.host.E) = A.H.rt0 from hin τr)]
      have h := hgr f hmap τ
      rw [hmg] at h
      exact grSq_wLine_of (hmW τr) hp hq _ _ _ _ _ h L.2
    · intro b _ hb
      rw [GlobalTheory.FlagAmple.BorelWeil.rootEx_apply, if_pos hi', if_neg, zpow_zero]
      rintro ⟨h1, h2⟩
      apply hb
      obtain ⟨ρ, a⟩ := b
      obtain rfl : τ = ρ := h1
      exact Sigma.ext rfl (heq_of_eq (Fin.ext h2.symm))
  · have hi' : ¬ (i : ℕ) < S.Dw.p := by omega
    have hiN : (i : ℕ) < S.Dw.p + S.Dw.q := by have := S.rank_eq; have := i.isLt; omega
    let L : Letter S.Dw := ⟨conjEmb τ, ⟨S.Dw.p + S.Dw.q - 1 - i, by rw [hmO]; omega⟩⟩
    rw [Finset.prod_eq_single L ?_ (by simp)]
    · rw [GlobalTheory.FlagAmple.BorelWeil.rootEx_apply, if_neg hi', if_pos ⟨rfl, rfl⟩, _root_.zpow_neg_one, hgram]
      have h' : conjEmb (conjEmb τ) (A.H.rt : D.host.E) = A.H.rt0 := by
        rw [show conjEmb (conjEmb τ) = τ from RingHom.ext fun a => Complex.conj_conj _]
        exact hin τr
      have hψ : (⟨conjEmb (conjEmb τ), h'⟩ : GlobalTheory.AllWt.Psi A.H) = ⟨τ, hin τr⟩ :=
        Subtype.ext (RingHom.ext fun a => Complex.conj_conj _)
      have hmg : GlobalTheory.PointChern.modelGram A.H S.Dw (z v) (conjEmb τ) =
          reindex (finCongr (hmO τr).symm) (finCongr (hmO τr).symm)
            (1 - (z v ⟨τ, hin τr⟩)ᴴ * z v ⟨τ, hin τr⟩)⁻¹ := by
        unfold GlobalTheory.PointChern.modelGram
        rw [dif_neg (show ¬ conjEmb τ (A.H.rt : D.host.E) = A.H.rt0 from hout τr), dif_pos h', hψ]
      have h := hgr f hmap (conjEmb τ)
      rw [hmg] at h
      congr 1
      rw [grSq_oLine_of (hmO τr) hp hq _ _ _ _ _ h L.2]
      congr 1
      ext
      simp only [Fin.coe_cast, L]
      omega
    · intro b _ hb
      rw [GlobalTheory.FlagAmple.BorelWeil.rootEx_apply, if_neg hi', if_neg, neg_zero, zpow_zero]
      rintro ⟨h1, h2⟩
      apply hb
      obtain ⟨ρ, a⟩ := b
      obtain rfl : conjEmb τ = ρ := h1
      exact Sigma.ext rfl (heq_of_eq (Fin.ext h2.symm))

end GlobalTheory.HodgeLocGeo.RootModel
