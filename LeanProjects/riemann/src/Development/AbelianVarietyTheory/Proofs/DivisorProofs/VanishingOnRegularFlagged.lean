import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSectionLiftsMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineBundleInducedArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleMetricSetupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalFlagGradedIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantMetricIsometric

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.VBExt (AdaptedChart)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.TwoLat

section Isometry

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem form_app_of_gram {E E' : X.Modules} {r r' : ℕ} {h : Met p σ E r} {h' : Met p σ E' r'} {u : E ⟶ E'}
    (c : Chart E r) {y : CxPts p σ} (hc : y ∈ ptsIn p σ c.U) (e : h'.gram (fun a => u.app c.U (c.e a)) y = h.G c y)
    {V : X.Opens} (s t : Γ(E, V)) (hy : y ∈ ptsIn p σ V) : h'.form (u.app V s) (u.app V t) y = h.form s t y := by
  have h₀ := h'.isVB.mem_pick y
  rw [h.form_eq c hc _ _ hy, h'.form_eq _ h₀ _ _ hy, Chart.crd_app _ c u s hy hc, Chart.crd_app _ c u t hy hc,
    ← form_chg, ← h'.gram_eq _ h₀ _ hc, e]

theorem IsoHom.pull {E E' : X.Modules} {r : ℕ} {h : VMetric p E r} {h' : VMetric p E' r} {u : E ⟶ E'}
    (hu : IsoHom h h' u) {Y : Scheme.{0}} {q : Y ⟶ Sp k} (π : Y ⟶ X) (w : π ≫ p = q) :
    IsoHom (h.pull π w) (h'.pull π w) ((Scheme.Modules.pullback π).map u) := fun σ V s t z hz => by
  have hc := (h.met σ).isVB.mem_pick (PtsOver.map π w _ z)
  refine form_app_of_gram (Chart.pull _ (h.met σ).isVB π) hc ?_ s t hz
  refine Eq.trans ?_ ((h.met σ).pull_G π w _ hc).symm
  ext a b
  rw [← (h.met σ).form_frame _ hc, ← hu σ _ _ _ _ hc, ← (h'.met σ).form_pull π w _ _ le_rfl hc,
    ← QCoh.pullback_map_app_pullbackSections, ← QCoh.pullback_map_app_pullbackSections]
  rfl

theorem bcForm_eq_of_isometry {S S' : ShortComplex X.Modules} {r s : ℕ} {h : Met p σ S.X₂ (r + s)}
    {h' : Met p σ S'.X₂ (r + s)} (hS : S.ShortExact) (hS' : S'.ShortExact) (H' : h'.IsCInf) (f₁ : S.X₁ ⟶ S'.X₁)
    (f₂ : S.X₂ ⟶ S'.X₂) (hf : f₁ ≫ S'.f = S.f ≫ f₂)
    (hu : ∀ (V : X.Opens) (s t : Γ(S.X₂, V)), ∀ y ∈ ptsIn p σ V, h'.form (f₂.app V s) (f₂.app V t) y = h.form s t y)
    (a : AdaptedChart S r s) (a' : AdaptedChart S' r s) {D : ℕ} (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) (ha : y ∈ ptsIn p σ a.U) (ha' : y ∈ ptsIn p σ a'.U) :
    h.bcForm a c y = h'.bcForm a' c y := by
  have hm := (ChartGlue.isOpen_over c.e (isOpen_ptsIn (a.U ⊓ a'.U))).mem_nhds
    (ChartGlue.mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, ha'⟩))
  let A : CxPts p σ → Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := fun z =>
    Matrix.of fun i j => (a'.mid hS').crd p σ (f₂.app a.U (a.frame j)) z (finSumFinEquiv i)
  have hA : MInfAt A y := fun i j => (a'.mid hS').vInfAt_crd _ ha ha' _
  have hG (z : CxPts p σ) (hz : z ∈ ptsIn p σ a.U) (hz' : z ∈ ptsIn p σ a'.U) :
      h.gram a.frame z = chg (A z) (h'.gram a'.frame z) := by
    have e₁ : h.gram a.frame z = h'.gram (fun j => f₂.app a.U (a.frame j)) z := by
      ext i j
      exact (hu _ _ _ z hz).symm
    rw [e₁, h'.gram_eq (a'.mid hS') hz' _ hz, h'.gram_frame hS' a' hz']
    exact (chg_submatrix (Matrix.of fun i j => (a'.mid hS').crd p σ (f₂.app a.U (a.frame j)) z i) _
      finSumFinEquiv id).symm
  rw [Met.bcForm, extTrace_congr (K' := fun v => chg (A (c.e.symm v)) (h'.gram a'.frame (c.e.symm v)))
    (eventually_of_mem hm fun v hv => hG _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2)]
  refine extTrace_chg (((H'.gram _ ha').mContDiffAt c hy).of_le (by norm_cast))
    (h'.eventually_posDef hS' a' c hy ha') ((hA.mContDiffAt c hy).of_le (by norm_cast)) ?_
    (fun η => Matrix.ext fun i j => ?_) (eventually_of_mem hm fun v hv => ?_)
  · rw [c.e.left_inv hy]
    have hd := (h.posDef_gram_frame hS a ha).det_pos.ne'
    rw [hG y ha ha', det_chg] at hd
    refine Ne.isUnit fun e => hd ?_
    simp [e]
  · exact congr($(dbar_eq_zero (c.differentiableAt_ev _ hy (mem_ptsIn_inf.2 ⟨ha, ha'⟩))) η)
  · obtain ⟨hz, hz'⟩ := mem_ptsIn_inf.1 hv.2
    ext i j
    have e : f₂.app a.U (a.frame (.inl j)) = S'.f.app a.U (f₁.app a.U (a.e j)) := congr(($hf.symm).app a.U (a.e j))
    change (a'.mid hS').crd p σ (f₂.app a.U (a.frame (.inl j))) _ (finSumFinEquiv (.inr i)) = 0
    rw [e, (a'.mid hS').crd_app a'.sub S'.f _ hz hz']
    simp only [mulVec, dotProduct, of_apply]
    refine Finset.sum_eq_zero fun b _ => mul_eq_zero_of_left ?_ _
    exact (a'.crd_frame hS' hz' (.inr i) (.inl b)).trans (by simp)

theorem bcMat_eq_of_isometry {S S' : ShortComplex X.Modules} {r s : ℕ} {h : Met p σ S.X₂ (r + s)}
    {h' : Met p σ S'.X₂ (r + s)} (hS : S.ShortExact) (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s)
    (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (H' : h'.IsCInf) (f₁ : S.X₁ ⟶ S'.X₁)
    (f₂ : S.X₂ ⟶ S'.X₂) (hf : f₁ ≫ S'.f = S.f ≫ f₂)
    (hu : ∀ (V : X.Opens) (s t : Γ(S.X₂, V)), ∀ y ∈ ptsIn p σ V, h'.form (f₂.app V s) (f₂.app V t) y = h.form s t y)
    {D : ℕ} (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    bcMat h hS h₁ h₃ c y = bcMat h' hS' h₁' h₃' c y :=
  congrArg formMat (bcForm_eq_of_isometry hS hS' H' f₁ f₂ hf hu _ _ c hy (Met.exists_adapted hS h₁ h₃ y).choose_spec
    (Met.exists_adapted hS' h₁' h₃' y).choose_spec)

theorem bcPair_eq_of_compat {E E' : X.Modules} {r : ℕ} {h : VMetric p E r} {h' : VMetric p E' r} (H' : h'.IsCInf)
    {u : E ⟶ E'} (hu : IsoHom h h' u) {fl : Vert.Flag E r} {fl' : Vert.Flag E' r} (hc : Compat u fl fl')
    (N : HermLB p) (d : ℕ) : bcPair h fl N d = bcPair h' fl' N d := by
  refine finsum_congr fun σ => total_congr fun c y hy => ?_
  refine congrArg (mix d _) (Finset.sum_congr rfl fun i _ => ?_)
  obtain ⟨t₁, h₁⟩ := hc i.castSucc
  obtain ⟨t₂, h₂⟩ := hc i.succ
  refine bcMat_eq_of_isometry (S := VMetric.stepSeq fl i) (S' := VMetric.stepSeq fl' i) (r := i) (s := 1)
    (h := (h.stepMet fl i).met σ) (h' := (h'.stepMet fl' i).met σ) _ _ _ _ _ _
    (H'.restrict (fl'.isSubbundle i.succ) (fl'.isVB i.succ) σ) t₁ t₂ ?_ (fun V s t z hz => ?_) c hy
  · change t₁ ≫ fl'.step i = fl.step i ≫ t₂
    rw [← cancel_mono (fl'.ι i.succ), Category.assoc, Category.assoc, fl'.step_ι, h₁, h₂, fl.step_ι_assoc]
  · have e (s : Γ(fl.F i.succ, V)) : (fl'.ι i.succ).app V (t₂.app V s) = u.app V ((fl.ι i.succ).app V s) :=
      congr(($h₂).app V s)
    refine ((h'.met σ).form_restrict (fl'.isSubbundle i.succ) (fl'.isVB i.succ) _ _ hz).trans ?_
    rw [e, e, hu σ V _ _ z hz]
    exact ((h.met σ).form_restrict (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ hz).symm

theorem icls_det_rank_zero {E : X.Modules} {h : VMetric p E 0} (H : h.IsCInf) : (VMetric.det H).icls = 0 := by
  refine HermLB.icls_eq_iff.2 (HermLB.isometric_of_chart (M := .triv p) (fun _ => PUnit.unit) (fun _ => le_top)
    (fun x j j' _ _ => ?_) fun σ j y _ => ?_)
  · have : (VMetric.det H).B.g j j' = 1 := Units.ext (by
      change (IsFrame.detUnit _ _ _ _).val = _
      simp [IsFrame.detUnit]; rfl)
    rw [this, map_one]; exact (map_one _).symm
  · change (0 : ℝ) = -Real.log ((h.met σ).G j y).det.re
    simp

theorem sum_icls_grLB {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) :
    ∑ i, (VMetric.grLB fl i H).icls = (VMetric.det H).icls := by
  let t : Fin (r + 1) → HermLB.IsomClass p := fun j => (VMetric.det (H.restrict (fl.isSubbundle j) (fl.isVB j))).icls
  have h₀ : t 0 = 0 := icls_det_rank_zero _
  have h₁ : t (Fin.last r) = (VMetric.det H).icls :=
    HermLB.icls_eq_iff.2 (VMetric.isometric_det_of_isIsometry k X p _ E r _ h (asIso (fl.ι (Fin.last r))) _ H
      fun σ V s t y hy => ((h.met σ).form_restrict (fl.isSubbundle _) (fl.isVB _) s t hy).symm)
  have h₂ (i : Fin r) : (VMetric.grLB fl i H).icls = t i.succ - t i.castSucc :=
    eq_sub_of_add_eq' (HermLB.icls_eq_iff.2 (VMetric.isometric_det_tens_grLB p E r h H fl i))
  simp only [h₂, Finset.sum_sub_distrib]
  have e := (Fin.sum_univ_succ t).symm.trans (Fin.sum_univ_castSucc t)
  rw [h₀, zero_add] at e
  rw [e, h₁, add_sub_cancel_left]

end Isometry

section Assembly

open MvPolynomial

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem apply_aeval (hI : Published.ArIso) (hX : IsArithVar p D) {κ J : Type} [Fintype κ] [Fintype J] {L : κ → HermLB p}
    {M : J → HermLB p} {Ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ} {Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ} (hΨ : IsArFun L D Ψ)
    (hΦ : IsArFun M D Φ) (f : J → MvPolynomial κ ℝ)
    (hf : ∀ j, ∃ n : κ → ℤ, f j = lin (fun i => (n i : ℝ)) ∧ ∑ i, n i • (L i).icls = (M j).icls)
    (P : MvPolynomial J ℝ) : Ψ (aeval f P) = Φ P := by
  choose n hn hn' using hf
  obtain rfl := funext hn
  rw [GlobalTheory.ArInt.Model.isArFun_unique hX hΦ (((hI k X p D hX).2 κ L Ψ hΨ).2.2 J M n fun j =>
    HermLB.icls_eq_iff.1 ((icls_comb _ _).trans (hn' j)))]
  rfl

theorem apply_sq_sub_eq (hC : Published.ArCalc) (hP : Published.Principalisation) {d : ℕ} (hD : D = d + 1) (hX : IsArithVar p D)
    {E E' : X.Modules} {r : ℕ} {h : VMetric p E r} {h' : VMetric p E' r} (H : h.IsCInf) (H' : h'.IsCInf) {u : E ⟶ E'}
    (hu : IsoHom h h' u) {fl m : Vert.Flag E r} {fl' m' : Vert.Flag E' r} (hfl : Compat u fl fl') (hm : Compat u m m')
    {κ : Type} [Fintype κ] {L : κ → HermLB p} {Ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ} (hΨ : IsArFun L D Ψ)
    (x x' y y' : Fin r → κ) (hx : ∀ i, (L (x i)).Isometric (VMetric.grLB fl i H))
    (hx' : ∀ i, (L (x' i)).Isometric (VMetric.grLB fl' i H')) (hy : ∀ i, (L (y i)).Isometric (VMetric.grLB m i H))
    (hy' : ∀ i, (L (y' i)).Isometric (VMetric.grLB m' i H')) {R : MvPolynomial κ ℝ} (hR : R.IsHomogeneous d) :
    Ψ ((∑ i, MvPolynomial.X (x' i) ^ 2 - ∑ i, MvPolynomial.X (x i) ^ 2) * R) =
      Ψ ((∑ i, MvPolynomial.X (y' i) ^ 2 - ∑ i, MvPolynomial.X (y i) ^ 2) * R) := by
  subst hD
  obtain ⟨I, _, c, n, rfl⟩ := FlagCmp.exists_sum_pow hR
  simp only [Finset.mul_sum _ (fun j => c j • _), mul_smul_comm, map_sum Ψ (fun j => c j • _), map_smul]
  refine Finset.sum_congr rfl fun j _ => congrArg (c j • ·) ?_
  have e₁ := FlagCmp.compare hC hP hX H fl m κ L Ψ hΨ x y hx hy (n j)
  have e₂ := FlagCmp.compare hC hP hX H' fl' m' κ L Ψ hΨ x' y' hx' hy' (n j)
  rw [bcPair_eq_of_compat H' hu hfl, bcPair_eq_of_compat H' hu hm, ← e₂] at e₁
  simp only [sub_mul, map_sub] at e₁ ⊢
  linarith

end Assembly

open MvPolynomial in

theorem vanishOn_regFlagged : GlobalTheory.CovTop.Hypotheses2 → VanishOn RegFlagged := by
  intro HP k _ B Y X _ _ _ q π ρ p w n e hB hY hc ι _ E E' r h h' H H' u hu ⟨hreg, hm⟩ fl hfl fl' hcf Φ hΦ Q hQ hQ0
  subst w
  choose m m' hm using hm
  have hX := hc.1
  let g : (Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a)) → HermLB q :=
    Sum.elim (fun z => VMetric.grLB (m z.1) z.2 (H z.1)) fun z => VMetric.grLB (m' z.1) z.2 (H' z.1)
  let A : Option ((Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a))) → HermLB q :=
    fun o => o.elim (comb (fun z => g (.inl z)) fun _ => 1) g
  obtain ⟨Ψ, hΨ⟩ := ((HP.p4.arExists k X _ _ hX).2 _ (Sum.elim (Sum.elim
    (fun z : Σ a, Fin (r a) => (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π rfl)).pull ρ rfl)
    fun z : Σ a, Fin (r a) => VMetric.grLB (fl' z.1) z.2 (((H' z.1).pull π rfl).pull ρ rfl))
    fun z => ((g z).pull π rfl).pull ρ rfl)).1
  obtain ⟨ΦB, hΦB⟩ := ((HP.p4.arExists k B _ _ hB).2 _ A).1
  obtain ⟨ΨY, hΨY⟩ := ((HP.p4.arExists k Y _ _ hY).2 _ (Sum.elim
    (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π rfl)) fun a => (A a).pull π rfl)).1
  have hsq {κ : Type} (f : (Σ a, Fin (r a)) → κ) :
      (∑ z, MvPolynomial.X (f z) ^ 2 : MvPolynomial κ ℝ).IsHomogeneous 2 :=
    IsHomogeneous.sum _ _ _ fun z _ => by simpa using (isHomogeneous_X ℝ (f z)).pow 2
  have e₁ := T.flag_bundle_metric_setup HP k B Y q _ _ _ hB hreg hY π rfl ι E r h H fl hfl _ A ΦB ΨY hΦB hΨY
    ((∑ z, MvPolynomial.X (some (.inr z)) ^ 2 - ∑ z, MvPolynomial.X (some (.inl z)) ^ 2) * MvPolynomial.X none ^ n) Q 0
    (by
      rw [show n + 1 + 1 = 2 + 1 * n by omega]
      exact ((hsq _).sub (hsq _)).mul ((isHomogeneous_X ℝ none).pow n))
    (by rwa [Nat.add_sub_cancel_left]) (by rw [hQ0, zero_smul])
  have hpull {F : B.Modules} {s : ℕ} {b : VMetric q F s} (Hb : b.IsCInf) (l : Vert.Flag F s) (i : Fin s) :
      (((VMetric.grLB l i Hb).pull π rfl).pull ρ rfl).Isometric
        (VMetric.grLB ((l.pull π).pull ρ) i ((Hb.pull π rfl).pull ρ rfl)) :=
    ((VMetric.isometric_grLB_pull _ _ _ _ _ _ _ _ _ _ ρ rfl i).trans
      ((VMetric.isometric_grLB_pull _ _ _ _ _ _ _ _ _ _ π rfl i).pull ρ rfl)).symm
  have e₂ := apply_aeval HP.p4.arIso hX hΨ ((HP.p4.arProj k Y X _ _ _ hY hX ρ rfl hc.2.1 hc.2.2).2 _ _ ΨY hΨY)
    (Sum.elim (fun z => MvPolynomial.X (.inl (.inl z)))
      fun o => o.elim (∑ z, MvPolynomial.X (.inl (.inl z))) fun z => MvPolynomial.X (.inr z)) (by
      rintro (z | _ | z)
      · exact ⟨Pi.single (.inl (.inl z)) 1, by simp [lin, Pi.single_apply, apply_ite], by simp [Pi.single_apply]⟩
      · refine ⟨Sum.elim (Sum.elim (fun _ => 1) 0) 0, by simp [lin], ?_⟩
        have e (a : ι) : ∑ i, (VMetric.grLB (fl a) i ((H a).pull π rfl)).icls =
            ∑ i, ((VMetric.grLB (m a) i (H a)).pull π rfl).icls := by
          rw [sum_icls_grLB, ← sum_icls_grLB _ ((m a).pull π)]
          exact Finset.sum_congr rfl fun i _ =>
            HermLB.icls_eq_iff.2 (VMetric.isometric_grLB_pull _ _ _ _ _ _ _ _ _ _ π rfl i)
        simp only [HermLB.icls_pull] at e
        simp [A, g, HermLB.icls_pull, icls_comb, Fintype.sum_sigma, ← map_sum, e]
      · exact ⟨Pi.single (.inr z) 1, by simp [lin, Pi.single_apply, apply_ite], by simp [Pi.single_apply, A]⟩)
  have hR : (rename Sum.inl (rename Sum.inl ((∑ z, MvPolynomial.X z) ^ n * Q)) : MvPolynomial
      (((Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a))) ⊕ ((Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a)))) ℝ).IsHomogeneous (n + e) := by
    simpa using ((((IsHomogeneous.sum _ _ _ fun z _ => isHomogeneous_X ℝ z).pow n).mul hQ).rename_isHomogeneous
      (f := Sum.inl)).rename_isHomogeneous (f := Sum.inl)
  have e₃ (a : ι) := apply_sq_sub_eq HP.p4 HP.q16 (show n + 1 + e = n + e + 1 by omega) hX
    (((H a).pull π rfl).pull ρ rfl) (((H' a).pull π rfl).pull ρ rfl) (((hu a).pull π rfl).pull ρ rfl) (hcf a)
    (((hm a).pull π).pull ρ) hΨ (fun i => .inl (.inl ⟨a, i⟩)) (fun i => .inl (.inr ⟨a, i⟩))
    (fun i => .inr (.inl ⟨a, i⟩)) (fun i => .inr (.inr ⟨a, i⟩))
    (fun i => (VMetric.isometric_grLB_pull _ _ _ _ _ _ _ _ _ _ ρ rfl i).symm) (fun _ => .refl _)
    (fun i => hpull (H a) _ i) (fun i => hpull (H' a) _ i) hR
  have e₄ := Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => e₃ a
  rw [← map_sum, ← map_sum, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at e₄
  have e₅ := e₂ (rename Sum.inl Q * rename Sum.inr
    ((∑ z, MvPolynomial.X (some (.inr z)) ^ 2 - ∑ z, MvPolynomial.X (some (.inl z)) ^ 2) * MvPolynomial.X none ^ n))
  rw [LinearMap.smul_apply, e₁, zero_mul, smul_zero] at e₅
  rw [← FlagCmp.isArFun_restrict_inl HP.p4.arIso hX _ _ hΦ hΨ, map_mul]
  refine Eq.trans ?_ (e₄.trans (Eq.trans ?_ e₅))
  · simp only [map_sub, map_sum, map_pow, rename_X, Fintype.sum_sigma]
  · congr 1
    have eQ : aeval (fun z => MvPolynomial.X (.inl (.inl z))) Q = (rename Sum.inl (rename Sum.inl Q) : MvPolynomial
      (((Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a))) ⊕ ((Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a)))) ℝ) := by
      rw [rename_rename, rename_eq_aeval]; rfl
    simp only [map_mul, aeval_rename, Sum.elim_comp_inl, eQ, map_sub, map_sum, map_pow, rename_X, aeval_X, Sum.elim_inr,
      Option.elim, Fintype.sum_sigma]
    ring

end GlobalTheory.TwoLat
