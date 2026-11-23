import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open GlobalTheory.Points GlobalTheory.ProjFrac

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.TwistEmb

private theorem valR_ne_zero_of_mem_basicOpen {A : Type} [CommRing A] {X : Scheme.{0}} (w : Sp A ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ w ⁻¹ᵁ V) (s : Γ(X, V)) (z : Sp A) (hs : w z ∈ X.basicOpen s) : valR w V s ≠ 0 := by
  intro h0
  unfold valR at h0
  rw [dif_pos h] at h0
  have h1 : (w.appLE V ⊤ h).hom s = 0 := by
    have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom h0
    rw [map_zero] at h3
    rw [← h3]
    first
      | exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of A)) _).symm
      | simp
  have h4 : z ∈ w ⁻¹ᵁ X.basicOpen s := hs
  rw [Scheme.preimage_basicOpen] at h4
  have e1 : (Sp A).basicOpen ((w.appLE V ⊤ h).hom s) = ⊤ ⊓ (Sp A).basicOpen ((w.app V).hom s) := by
    show (Sp A).basicOpen ((Sp A).presheaf.map (homOfLE h).op ((w.app V).hom s)) = _
    first
      | exact Scheme.basicOpen_res _ _ _
      | rw [Scheme.basicOpen_res]
      | simp only [Scheme.basicOpen_res]
  have h2 : z ∈ (Sp A).basicOpen ((w.appLE V ⊤ h).hom s) := by
    rw [e1, top_inf_eq]
    exact h4
  rw [h1, Scheme.basicOpen_zero] at h2
  exact h2

private theorem valR_sub_iwasawa_decomposition {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (s t : Γ(X, V)) : valR x V (s - t) = valR x V s - valR x V t := by
  unfold valR
  rw [dif_pos h, dif_pos h, dif_pos h, map_sub, map_sub]

theorem eq_of_valR {Y : Scheme.{0}} [IsReduced Y] {V : Y.Opens} {f g : Γ(Y, V)}
    (H : ∀ (k : Type) [Field k] (w : Sp k ⟶ Y), ⊤ ≤ w ⁻¹ᵁ V → valR w V f = valR w V g) : f = g := by
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro y hy
  have hyV : y ∈ V := Y.basicOpen_le (f - g) hy
  have hw : ⊤ ≤ Y.fromSpecResidueField y ⁻¹ᵁ V := by
    intro z _
    show Y.fromSpecResidueField y z ∈ V
    rw [Scheme.fromSpecResidueField_apply]
    exact hyV
  have hfg := H (Y.residueField y) (Y.fromSpecResidueField y) hw
  have hsub : valR (Y.fromSpecResidueField y) V (f - g) = 0 :=
    (valR_sub_iwasawa_decomposition (Y.fromSpecResidueField y) V hw f g).trans (sub_eq_zero.mpr hfg)
  have hz := Scheme.fromSpecResidueField_apply y (IsLocalRing.closedPoint (Y.residueField y))
  rw [← hz] at hy
  exact absurd hsub (valR_ne_zero_of_mem_basicOpen (Y.fromSpecResidueField y) V hw (f - g) _ hy)

theorem le_inf' {C : Type} [CommRing C] {Y : Scheme.{0}} (w : Sp C ⟶ Y) {U V : Y.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U)
    (h' : ⊤ ≤ w ⁻¹ᵁ V) : ⊤ ≤ w ⁻¹ᵁ (U ⊓ V) := by
  rw [Scheme.Hom.preimage_inf]
  exact le_inf h h'

private theorem valR_resG_iwasawa_decomposition {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens}
    (e : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(X, U)) : valR x V (resG X e s) = valR x U s := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (fun z hz => e hz)
  unfold valR
  rw [dif_pos h, dif_pos hU]
  congr 1
  show (X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom s = _
  rw [Scheme.Hom.map_appLE]

private theorem valR_mul_degeneration {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (s t : Γ(X, V)) : valR x V (s * t) = valR x V s * valR x V t := by
  unfold valR
  rw [dif_pos h, dif_pos h, dif_pos h, map_mul, map_mul]

theorem valR_frac_mul {A τ : Type} [CommRing A] [SetLike τ A] [AddSubgroupClass τ A] (𝒜 : ℕ → τ) [GradedRing 𝒜]
    {C : Type} [CommRing C] (y : Sp C ⟶ Proj 𝒜) {U₁ U₂ U₃ : (Proj 𝒜).Opens} {d : ℕ} {a b c : A}
    (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d) (hc : c ∈ 𝒜 d) (h₁ : U₁ ≤ Proj.basicOpen 𝒜 c) (h₂ : U₂ ≤ Proj.basicOpen 𝒜 c)
    (h₃ : U₃ ≤ Proj.basicOpen 𝒜 b) (y₁ : ⊤ ≤ y ⁻¹ᵁ U₁) (y₂ : ⊤ ≤ y ⁻¹ᵁ U₂) (y₃ : ⊤ ≤ y ⁻¹ᵁ U₃) :
    valR y U₁ (frac 𝒜 U₁ a c ha hc h₁) =
      valR y U₂ (frac 𝒜 U₂ b c hb hc h₂) * valR y U₃ (frac 𝒜 U₃ a b ha hb h₃) := by
  have hW : ⊤ ≤ y ⁻¹ᵁ (U₁ ⊓ U₂ ⊓ U₃) := GlobalTheory.TwistEmb.le_inf' y (GlobalTheory.TwistEmb.le_inf' y y₁ y₂) y₃
  have e1 : U₁ ⊓ U₂ ⊓ U₃ ≤ U₁ := inf_le_left.trans inf_le_left
  have e2 : U₁ ⊓ U₂ ⊓ U₃ ≤ U₂ := inf_le_left.trans inf_le_right
  have e3 : U₁ ⊓ U₂ ⊓ U₃ ≤ U₃ := inf_le_right
  rw [← valR_resG_iwasawa_decomposition y e1 hW, ← valR_resG_iwasawa_decomposition y e2 hW, ← valR_resG_iwasawa_decomposition y e3 hW, ← valR_mul_degeneration y _ hW,
    resG_frac, resG_frac, resG_frac]
  congr 1
  exact (frac_mul_eq (by ring)).symm

theorem exists_form {O : Type} [CommRing O] {N : ℕ} {U : (PSpace O N).Opens} {q : PSpace O N} (hq : q ∈ U) :
    ∃ n, 0 < n ∧ ∃ F ∈ grading O N n, q ∈ Proj.basicOpen (grading O N) F ∧ Proj.basicOpen (grading O N) F ≤ U := by
  classical
  obtain ⟨_, ⟨r, rfl⟩, hqr, hrU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Proj.isBasis_basicOpen (grading O N)) hq
  have hqr' : q ∈ ⨆ i : ℕ, Proj.basicOpen (grading O N) (GradedRing.proj (grading O N) i r) := by
    rw [← Proj.basicOpen_eq_iSup_proj]
    exact hqr
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hqr'
  obtain ⟨j, hj⟩ := exists_mem_chart O N q
  have hle : Proj.basicOpen (grading O N) (GradedRing.proj (grading O N) i r) ≤ U := by
    refine le_trans ?_ hrU
    rw [Proj.basicOpen_eq_iSup_proj (grading O N) r]
    exact le_iSup (fun k => Proj.basicOpen (grading O N) (GradedRing.proj (grading O N) k r)) i
  have hmem : GradedRing.proj (grading O N) i r ∈ grading O N i := by
    rw [GradedRing.proj_apply]
    exact SetLike.coe_mem _
  refine ⟨i + 1, Nat.succ_pos i, GradedRing.proj (grading O N) i r * MvPolynomial.X j,
    SetLike.mul_mem_graded hmem (X_mem O N j), ?_, ?_⟩
  · rw [Proj.basicOpen_mul]
    exact TopologicalSpace.Opens.mem_inf.mpr ⟨hi, hj⟩
  · rw [Proj.basicOpen_mul]
    exact inf_le_left.trans hle

theorem exists_forms {O : Type} [CommRing O] {N : ℕ} {X : Scheme.{0}} (e : X ⟶ PSpace O N) [IsClosedImmersion e]
    {J : Type} (U : J → X.Opens) (hU : ∀ x : X, ∃ j, x ∈ U j) :
    ∃ (m d : ℕ) (F : Fin m → MvPolynomial (Fin (N + 1)) O) (σ : Fin m → J), 0 < d ∧ (∀ i, F i ∈ grading O N d) ∧
      (∀ i, e ⁻¹ᵁ Proj.basicOpen (grading O N) (F i) ≤ U (σ i)) ∧
      ∀ x : X, ∃ i, x ∈ e ⁻¹ᵁ Proj.basicOpen (grading O N) (F i) := by
  classical
  have hemb := e.isClosedEmbedding
  have step : ∀ x : X, ∃ (n : ℕ) (F : MvPolynomial (Fin (N + 1)) O) (j : J), 0 < n ∧ F ∈ grading O N n ∧
      x ∈ e ⁻¹ᵁ Proj.basicOpen (grading O N) F ∧ e ⁻¹ᵁ Proj.basicOpen (grading O N) F ≤ U j := by
    intro x
    obtain ⟨j, hj⟩ := hU x
    obtain ⟨W, hWo, hW⟩ := hemb.isInducing.isOpen_iff.mp (U j).isOpen
    have hj' : x ∈ (U j : Set X) := hj
    rw [← hW] at hj'
    obtain ⟨n, hn, F, hF, hxF, hFW⟩ := exists_form (U := (⟨W, hWo⟩ : (PSpace O N).Opens)) (q := e x) hj'
    refine ⟨n, F, j, hn, hF, hxF, fun y hy => ?_⟩
    have hyW : y ∈ e ⁻¹' W := hFW hy
    rw [hW] at hyW
    exact hyW
  choose n F j hn hF hxF hFU using step
  have hcpt : IsCompact (Set.univ : Set (PSpace O N)) := by
    have h1 : (Set.univ : Set (PSpace O N)) = ⋃ i, (chart O N i : Set (PSpace O N)) := by
      rw [← TopologicalSpace.Opens.coe_iSup, iSup_chart, TopologicalSpace.Opens.coe_top]
    rw [h1]
    exact isCompact_iUnion fun i => (isAffineOpen_chart O N i).isCompact
  haveI : CompactSpace (PSpace O N) := ⟨hcpt⟩
  haveI : CompactSpace X := hemb.compactSpace
  obtain ⟨t, ht⟩ := (isCompact_univ (X := X)).elim_finite_subcover
    (fun x => ((e ⁻¹ᵁ Proj.basicOpen (grading O N) (F x) : X.Opens) : Set X))
    (fun x => (e ⁻¹ᵁ Proj.basicOpen (grading O N) (F x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxF x⟩)
  set d := ∏ x ∈ t, n x with hd_def
  have hd : 0 < d := Finset.prod_pos fun x _ => hn x
  have hdvd : ∀ x ∈ t, n x ∣ d := fun x hx => Finset.dvd_prod_of_mem n hx
  have hk : ∀ x ∈ t, 0 < d / n x := fun x hx => Nat.div_pos (Nat.le_of_dvd hd (hdvd x hx)) (hn x)
  have hbo : ∀ (i : Fin t.card), Proj.basicOpen (grading O N) (F (t.equivFin.symm i) ^ (d / n (t.equivFin.symm i))) =
      Proj.basicOpen (grading O N) (F (t.equivFin.symm i)) := fun i =>
    Proj.basicOpen_pow (grading O N) _ _ (hk _ (t.equivFin.symm i).2)
  refine ⟨t.card, d, fun i => F (t.equivFin.symm i) ^ (d / n (t.equivFin.symm i)), fun i => j (t.equivFin.symm i),
    hd, fun i => ?_, fun i => ?_, fun x => ?_⟩
  · have h1 := SetLike.pow_mem_graded (d / n (t.equivFin.symm i)) (hF (t.equivFin.symm i))
    rwa [smul_eq_mul, Nat.div_mul_cancel (hdvd _ (t.equivFin.symm i).2)] at h1
  · rw [hbo i]
    exact hFU _
  · have hx : x ∈ ⋃ y ∈ t, ((e ⁻¹ᵁ Proj.basicOpen (grading O N) (F y) : X.Opens) : Set X) := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    rw [hbo, Equiv.symm_apply_apply]
    exact hxy

private theorem valR_app_eq_valR_comp {A : Type} [CommRing A] {X Y : Scheme.{0}} (w : Sp A ⟶ X) (e : X ⟶ Y) (D : Y.Opens)
    (h : ⊤ ≤ w ⁻¹ᵁ (e ⁻¹ᵁ D)) (r : Γ(Y, D)) : valR w (e ⁻¹ᵁ D) ((e.app D).hom r) = valR (w ≫ e) D r := by
  have h' : ⊤ ≤ (w ≫ e) ⁻¹ᵁ D := h
  unfold valR
  rw [dif_pos h, dif_pos h']
  congr 1

theorem exists_cover {O : Type} [CommRing O] {X : Scheme.{0}} {s : X ⟶ Sp O} (hs : IsProjOver s)
    {J : Type} (U : J → X.Opens) (hU : ∀ x : X, ∃ j, x ∈ U j) :
    ∃ (m : ℕ) (V : Fin m → X.Opens) (σ : Fin m → J) (g : ∀ i i', Γ(X, V i ⊓ V i')ˣ) (t : ∀ i, Fin m → Γ(X, V i)),
      (∀ i, IsAffineOpen (V i)) ∧ (∀ i, V i ≤ U (σ i)) ∧ ⨆ i, V i = ⊤ ∧
      (∀ i i', X.basicOpen (t i i') = V i ⊓ V i') ∧ (∀ i, t i i = 1) ∧
      ∀ (k : Type) [Field k] (w : Sp k ⟶ X) i i' i₀, ⊤ ≤ w ⁻¹ᵁ V i → ⊤ ≤ w ⁻¹ᵁ V i' →
        valR w _ (t i i₀) = valR w _ (g i i').val * valR w _ (t i' i₀) := by
  obtain ⟨N, e, he, -⟩ := hs
  obtain ⟨m, d, F, σ, hd, hF, hle, hcov⟩ := exists_forms e U hU
  refine ⟨m, fun i => e ⁻¹ᵁ Proj.basicOpen (grading O N) (F i), σ,
    fun i i' => Units.map (e.app (Proj.basicOpen (grading O N) (F i) ⊓ Proj.basicOpen (grading O N) (F i'))).hom.toMonoidHom
      (fracUnit (grading O N) (Proj.basicOpen (grading O N) (F i) ⊓ Proj.basicOpen (grading O N) (F i')) (F i') (F i)
        (hF i') (hF i) inf_le_right inf_le_left),
    fun i i' => (e.app (Proj.basicOpen (grading O N) (F i))).hom
      (frac (grading O N) (Proj.basicOpen (grading O N) (F i)) (F i') (F i) (hF i') (hF i) le_rfl),
    fun i => ?_, hle, ?_, fun i i' => ?_, fun i => ?_, ?_⟩
  · have ha : IsAffineOpen (Proj.basicOpen (grading O N) (F i)) := by
      first
        | exact Proj.isAffineOpen_basicOpen (grading O N) (F i) (hF i) hd
        | exact Proj.isAffineOpen_basicOpen (grading O N) (F i) (f_deg := hF i) (hm := hd)
    exact ha.preimage e
  · exact eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr (hcov x)
  · have h6 := Scheme.preimage_basicOpen e
      (frac (grading O N) (Proj.basicOpen (grading O N) (F i)) (F i') (F i) (hF i') (hF i) le_rfl)
    have h7 : (Proj (grading O N)).basicOpen
        (frac (grading O N) (Proj.basicOpen (grading O N) (F i)) (F i') (F i) (hF i') (hF i) le_rfl) =
        Proj.basicOpen (grading O N) (F i) ⊓ Proj.basicOpen (grading O N) (F i') := basicOpen_frac
    exact h6.symm.trans (congrArg (fun W : (PSpace O N).Opens => e ⁻¹ᵁ W) h7)
  · show (e.app (Proj.basicOpen (grading O N) (F i))).hom
      (frac (grading O N) (Proj.basicOpen (grading O N) (F i)) (F i) (F i) (hF i) (hF i) le_rfl) = 1
    rw [frac_self, map_one]
  · intro k _ w i i' i₀ hi hi'
    have hii' : ⊤ ≤ w ⁻¹ᵁ (e ⁻¹ᵁ (Proj.basicOpen (grading O N) (F i) ⊓ Proj.basicOpen (grading O N) (F i'))) :=
      GlobalTheory.TwistEmb.le_inf' w hi hi'
    have a1 := valR_app_eq_valR_comp w e (Proj.basicOpen (grading O N) (F i)) hi
      (frac (grading O N) (Proj.basicOpen (grading O N) (F i)) (F i₀) (F i) (hF i₀) (hF i) le_rfl)
    have a2 := valR_app_eq_valR_comp w e (Proj.basicOpen (grading O N) (F i) ⊓ Proj.basicOpen (grading O N) (F i')) hii'
      (frac (grading O N) (Proj.basicOpen (grading O N) (F i) ⊓ Proj.basicOpen (grading O N) (F i')) (F i') (F i)
        (hF i') (hF i) inf_le_left)
    have a3 := valR_app_eq_valR_comp w e (Proj.basicOpen (grading O N) (F i')) hi'
      (frac (grading O N) (Proj.basicOpen (grading O N) (F i')) (F i₀) (F i') (hF i₀) (hF i') le_rfl)
    have a4 := valR_frac_mul (grading O N) (w ≫ e) (U₁ := Proj.basicOpen (grading O N) (F i))
      (U₂ := Proj.basicOpen (grading O N) (F i) ⊓ Proj.basicOpen (grading O N) (F i'))
      (U₃ := Proj.basicOpen (grading O N) (F i')) (hF i₀) (hF i') (hF i) le_rfl inf_le_left le_rfl hi hii' hi'
    exact a1.trans (a4.trans (congrArg₂ (· * ·) a2.symm a3.symm))

private theorem valR_pow_iwasawa_decomposition {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(X, V)) (m : ℕ) : valR x V (s ^ m) = valR x V s ^ m := by
  unfold valR
  rw [dif_pos h, dif_pos h, map_pow, map_pow]

private theorem le_preimage_basicOpen_of_valR_ne_zero {k : Type} [Field k] {X : Scheme.{0}} (w : Sp k ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ w ⁻¹ᵁ V) (s : Γ(X, V)) (hs : valR w V s ≠ 0) : ⊤ ≤ w ⁻¹ᵁ X.basicOpen s := by
  unfold valR at hs
  rw [dif_pos h] at hs
  have hu : IsUnit ((w.appLE V ⊤ h).hom s) := by
    have h3 := (Ne.isUnit hs).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    have e : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((w.appLE V ⊤ h).hom s)) = (w.appLE V ⊤ h).hom s := by
      first
        | exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) _
        | simp
    rwa [e] at h3
  have h5 : (Sp k).basicOpen ((w.appLE V ⊤ h).hom s) = ⊤ := by
    first
      | exact Scheme.basicOpen_of_isUnit _ hu
      | exact Scheme.basicOpen_of_isUnit hu
  have e1 : (Sp k).basicOpen ((w.appLE V ⊤ h).hom s) = ⊤ ⊓ (Sp k).basicOpen ((w.app V).hom s) := by
    show (Sp k).basicOpen ((Sp k).presheaf.map (homOfLE h).op ((w.app V).hom s)) = _
    first
      | exact Scheme.basicOpen_res _ _ _
      | rw [Scheme.basicOpen_res]
      | simp only [Scheme.basicOpen_res]
  rw [e1, top_inf_eq] at h5
  have h6 : w ⁻¹ᵁ X.basicOpen s = (Sp k).basicOpen ((w.app V).hom s) := Scheme.preimage_basicOpen w s
  exact (h6.trans h5).ge

theorem exists_ext {X : Scheme.{0}} {V W : X.Opens} (hV : IsAffineOpen V) (t : Γ(X, V)) (hW : X.basicOpen t ≤ W)
    (f : Γ(X, W)) : ∃ N : ℕ, ∀ N', N < N' → ∃ a : Γ(X, V), ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ V →
      valR w V a = valR w V t ^ N' * valR w W f := by
  have hloc := hV.isLocalization_basicOpen t
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj t (resG X hW f)
  refine ⟨n, fun N' hN' => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, N' = m + 1 + n := ⟨N' - n - 1, by omega⟩
  refine ⟨t ^ (m + 1) * b, fun k _ w hw => ?_⟩
  have hD : X.basicOpen t ≤ V := X.basicOpen_le t
  by_cases hwD : ⊤ ≤ w ⁻¹ᵁ X.basicOpen t
  · have hb' : valR w V b = valR w W f * valR w V t ^ n := by
      rw [← valR_resG_iwasawa_decomposition w hD hwD b, ← valR_resG_iwasawa_decomposition w hW hwD f, ← valR_resG_iwasawa_decomposition w hD hwD t,
        ← valR_pow_iwasawa_decomposition w _ hwD, ← valR_mul_degeneration w _ hwD]
      congr 1
      exact hb.symm
    rw [valR_mul_degeneration w V hw, valR_pow_iwasawa_decomposition w V hw, hb']
    ring
  · have ht : valR w V t = 0 := by
      by_contra hne
      exact hwD (le_preimage_basicOpen_of_valR_ne_zero w V hw t hne)
    rw [valR_mul_degeneration w V hw, valR_pow_iwasawa_decomposition w V hw, ht]
    simp [pow_add, pow_succ]

private theorem valF_eq_valR_iwasawa_decomposition {k : Type} [Field k] {X : Scheme.{0}} (w : Sp k ⟶ X) (V : X.Opens) (f : Γ(X, V)) :
    valF w V f = valR w V f := by
  unfold valF valR
  first
    | rfl
    | (split_ifs <;> rfl)

private theorem valR_one_iwasawa_decomposition {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ V) : valR x V 1 = 1 := by
  unfold valR
  rw [dif_pos h, map_one, map_one]

private theorem valR_zero_iwasawa_decomposition {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ V) : valR x V 0 = 0 := by
  unfold valR
  rw [dif_pos h, map_zero, map_zero]

private theorem valR_res_units_coe {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (u : Γ(X, U)ˣ) : valR x V ((res e u : Γ(X, V)ˣ) : Γ(X, V)) = valR x U u :=
  valR_resG_iwasawa_decomposition x e h u

private theorem res_mul_res_eq_res_of_valR_cocycle {X : Scheme.{0}} [IsReduced X] {m : ℕ} (V : Fin m → X.Opens)
    (g : ∀ i i', Γ(X, V i ⊓ V i')ˣ) (t : ∀ i, Fin m → Γ(X, V i)) (htt : ∀ i, t i i = 1)
    (hcoc : ∀ (k : Type) [Field k] (w : Sp k ⟶ X) i i' i₀, ⊤ ≤ w ⁻¹ᵁ V i → ⊤ ≤ w ⁻¹ᵁ V i' →
        valR w _ (t i i₀) = valR w _ (g i i').val * valR w _ (t i' i₀))
    (i j l : Fin m) (W : X.Opens) (e1 : W ≤ V i ⊓ V j) (e2 : W ≤ V j ⊓ V l) (e3 : W ≤ V i ⊓ V l) :
    res e1 (g i j) * res e2 (g j l) = res e3 (g i l) := by
  apply Units.ext
  rw [Units.val_mul]
  apply eq_of_valR
  intro k _ w hw
  have hi : ⊤ ≤ w ⁻¹ᵁ V i := fun z hz => (TopologicalSpace.Opens.mem_inf.mp (e1 (hw hz))).1
  have hj : ⊤ ≤ w ⁻¹ᵁ V j := fun z hz => (TopologicalSpace.Opens.mem_inf.mp (e1 (hw hz))).2
  have hl : ⊤ ≤ w ⁻¹ᵁ V l := fun z hz => (TopologicalSpace.Opens.mem_inf.mp (e2 (hw hz))).2
  rw [valR_mul_degeneration w W hw, valR_res_units_coe w e1 hw, valR_res_units_coe w e2 hw, valR_res_units_coe w e3 hw]
  have c1 := hcoc k w i j l hi hj
  have c2 := hcoc k w j l l hj hl
  have c3 := hcoc k w i l l hi hl
  rw [htt l, valR_one_iwasawa_decomposition w _ hl, mul_one] at c2 c3
  rw [← c2, ← c3, c1]

private theorem transition_self_eq_one_of_valR_cocycle {X : Scheme.{0}} [IsReduced X] {m : ℕ} (V : Fin m → X.Opens)
    (g : ∀ i i', Γ(X, V i ⊓ V i')ˣ) (t : ∀ i, Fin m → Γ(X, V i)) (htt : ∀ i, t i i = 1)
    (hcoc : ∀ (k : Type) [Field k] (w : Sp k ⟶ X) i i' i₀, ⊤ ≤ w ⁻¹ᵁ V i → ⊤ ≤ w ⁻¹ᵁ V i' →
        valR w _ (t i i₀) = valR w _ (g i i').val * valR w _ (t i' i₀))
    (i : Fin m) : g i i = 1 := by
  apply Units.ext
  rw [Units.val_one]
  apply eq_of_valR
  intro k _ w hw
  have hi : ⊤ ≤ w ⁻¹ᵁ V i := fun z hz => (TopologicalSpace.Opens.mem_inf.mp (hw hz)).1
  have c := hcoc k w i i i hi hi
  rw [htt i, valR_one_iwasawa_decomposition w _ hi, mul_one] at c
  rw [valR_one_iwasawa_decomposition w _ hw]
  exact c.symm

theorem exists_twist_embedding : ∀ (O : Type) [CommRing O] (X : Scheme.{0}) [IsReduced X] (s : X ⟶ Sp O) (J : Type) (U : J → X.Opens) (n : J → ℕ) (G : ∀ j j', Matrix (Fin (n j)) (Fin (n j')) Γ(X, U j ⊓ U j')), IsProjOver s → (∀ x : X, ∃ j, x ∈ U j) → (∀ (k : Type) [Field k] (w : Sp k ⟶ X) j, ⊤ ≤ w ⁻¹ᵁ U j → (G j j).map (valF w _) = 1) → (∀ (k : Type) [Field k] (w : Sp k ⟶ X) j j' j'', ⊤ ≤ w ⁻¹ᵁ U j → ⊤ ≤ w ⁻¹ᵁ U j' → ⊤ ≤ w ⁻¹ᵁ U j'' → (G j j').map (valF w _) * (G j' j'').map (valF w _) = (G j j'').map (valF w _)) → ∃ (L : FinLB X) (M : ℕ) (σ : Fin L.n → J) (A : ∀ i, Matrix (Fin (M + 1)) (Fin (n (σ i))) Γ(X, L.U i)) (B : ∀ i, Matrix (Fin (n (σ i))) (Fin (M + 1)) Γ(X, L.U i)), (∀ i, IsAffineOpen (L.U i)) ∧ (∀ i, L.U i ≤ U (σ i)) ∧ (∀ i, B i * A i = 1) ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ X) i i', ⊤ ≤ w ⁻¹ᵁ L.U i → ⊤ ≤ w ⁻¹ᵁ L.U i' → (A i).map (valF w _) = valF w _ (L.g i i').val • ((A i').map (valF w _) * (G (σ i') (σ i)).map (valF w _)) := by
  intro O _ X _ s J U n G hs hU hG1 hG2
  classical
  obtain ⟨m, V, σ, g, t, haff, hVU, hVtop, hbt, htt, hcoc⟩ := exists_cover hs U hU
  have hext : ∀ (i₁ : Fin m) (a : Fin (n (σ i₁))) (i : Fin m) (b : Fin (n (σ i))), ∃ N : ℕ, ∀ N', N < N' →
      ∃ x : Γ(X, V i), ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ V i →
        valR w (V i) x = valR w (V i) (t i i₁) ^ N' * valR w (U (σ i₁) ⊓ U (σ i)) (G (σ i₁) (σ i) a b) := by
    intro i₁ a i b
    have hW : X.basicOpen (t i i₁) ≤ U (σ i₁) ⊓ U (σ i) := by
      rw [hbt]
      exact le_inf (inf_le_right.trans (hVU i₁)) (inf_le_left.trans (hVU i))
    exact exists_ext (haff i) (t i i₁) hW (G (σ i₁) (σ i) a b)
  choose Nf hNf using hext
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℕ, 0 < K ∧ ∀ i₁ a i b, Nf i₁ a i b < K :=
    ⟨Finset.univ.sup (fun q : (Σ i₁ : Fin m, Fin (n (σ i₁))) × (Σ i : Fin m, Fin (n (σ i))) =>
        Nf q.1.1 q.1.2 q.2.1 q.2.2) + 1, Nat.succ_pos _, fun i₁ a i b => Nat.lt_succ_of_le
      (Finset.le_sup (f := fun q : (Σ i₁ : Fin m, Fin (n (σ i₁))) × (Σ i : Fin m, Fin (n (σ i))) =>
        Nf q.1.1 q.1.2 q.2.1 q.2.2) (Finset.mem_univ (⟨i₁, a⟩, ⟨i, b⟩)))⟩
  choose x hx using fun i₁ a i b => hNf i₁ a i b K (hK i₁ a i b)
  let ε : Option (Σ i₁ : Fin m, Fin (n (σ i₁))) ≃ Fin (Fintype.card (Σ i₁ : Fin m, Fin (n (σ i₁))) + 1) :=
    Fintype.equivFinOfCardEq (Fintype.card_option)
  obtain ⟨A, hA⟩ : ∃ A : ∀ i, Matrix (Fin (Fintype.card (Σ i₁ : Fin m, Fin (n (σ i₁))) + 1)) (Fin (n (σ i))) Γ(X, V i),
      ∀ i r b, A i r b = Option.elim (ε.symm r) 0 (fun p => x p.1 p.2 i b) := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ∀ i, Matrix (Fin (n (σ i))) (Fin (Fintype.card (Σ i₁ : Fin m, Fin (n (σ i₁))) + 1)) Γ(X, V i),
      ∀ i b r, B i b r = if ε.symm r = some ⟨i, b⟩ then 1 else 0 := ⟨_, fun _ _ _ => rfl⟩
  have hBA : ∀ i, B i * A i = 1 := by
    intro i
    ext b b'
    have hsum : (B i * A i) b b' = x i b i b' := by
      rw [Matrix.mul_apply, ← ε.sum_comp, Fintype.sum_option]
      simp [hA, hB]
    rw [hsum]
    apply eq_of_valR
    intro k _ w hw
    have hwU : ⊤ ≤ w ⁻¹ᵁ U (σ i) := hw.trans (fun z hz => hVU i hz)
    have e1 := congrArg (fun M => M b b') (hG1 k w (σ i) hwU)
    simp only [Matrix.map_apply, valF_eq_valR_iwasawa_decomposition] at e1
    rw [hx i b i b' k w hw, htt i, valR_one_iwasawa_decomposition w _ hw, one_pow, one_mul, e1, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact (valR_one_iwasawa_decomposition w _ hw).symm
    · exact (valR_zero_iwasawa_decomposition w _ hw).symm
  have hlaw : ∀ (k : Type) [Field k] (w : Sp k ⟶ X) (i i' : Fin m), ⊤ ≤ w ⁻¹ᵁ V i → ⊤ ≤ w ⁻¹ᵁ V i' →
      (A i).map (valF w (V i)) = valF w (V i ⊓ V i') (g i i' ^ K).val •
        ((A i').map (valF w (V i')) * (G (σ i') (σ i)).map (valF w (U (σ i') ⊓ U (σ i)))) := by
    intro k _ w i i' hi hi'
    have hii' : ⊤ ≤ w ⁻¹ᵁ (V i ⊓ V i') := GlobalTheory.TwistEmb.le_inf' w hi hi'
    have hUi : ⊤ ≤ w ⁻¹ᵁ U (σ i) := hi.trans (fun z hz => hVU i hz)
    have hUi' : ⊤ ≤ w ⁻¹ᵁ U (σ i') := hi'.trans (fun z hz => hVU i' hz)
    ext r b
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, valF_eq_valR_iwasawa_decomposition, hA]
    rw [Units.val_pow_eq_pow_val, valR_pow_iwasawa_decomposition w _ hii']
    cases ε.symm r with
    | none =>
      simp only [Option.elim_none, valR_zero_iwasawa_decomposition w _ hi, valR_zero_iwasawa_decomposition w _ hi', zero_mul, Finset.sum_const_zero,
        mul_zero]
    | some p =>
      obtain ⟨i₁, a⟩ := p
      simp only [Option.elim_some]
      rw [hx i₁ a i b k w hi]
      simp only [fun c => hx i₁ a i' c k w hi']
      by_cases hw1 : ⊤ ≤ w ⁻¹ᵁ V i₁
      · have hU1 : ⊤ ≤ w ⁻¹ᵁ U (σ i₁) := hw1.trans (fun z hz => hVU i₁ hz)
        have c1 := hcoc k w i i' i₁ hi hi'
        have eG := congrArg (fun M => M a b) (hG2 k w (σ i₁) (σ i') (σ i) hU1 hUi' hUi)
        simp only [Matrix.mul_apply, Matrix.map_apply, valF_eq_valR_iwasawa_decomposition] at eG
        rw [c1, mul_pow, ← eG, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
      · have h0 : ∀ j (hj : ⊤ ≤ w ⁻¹ᵁ V j), valR w (V j) (t j i₁) = 0 := by
          intro j hj
          by_contra hne
          apply hw1
          have h5 := le_preimage_basicOpen_of_valR_ne_zero w (V j) hj (t j i₁) hne
          rw [hbt] at h5
          exact fun z hz => (TopologicalSpace.Opens.mem_inf.mp (h5 hz)).2
        rw [h0 i hi, h0 i' hi']
        simp [zero_pow hK0.ne']
  have hself : ∀ i, g i i ^ K = 1 := fun i => by rw [transition_self_eq_one_of_valR_cocycle V g t htt hcoc i, one_pow]
  refine ⟨⟨m, V, fun i i' => g i i' ^ K, ⟨hVtop, fun i => ?_, fun i j l => ?_⟩⟩,
    Fintype.card (Σ i₁ : Fin m, Fin (n (σ i₁))), σ, A, B, haff, hVU, hBA, hlaw⟩
  · dsimp only
    rw [hself i, map_one]
  · dsimp only
    rw [map_pow, map_pow, map_pow, ← mul_pow]
    congr 1
    exact res_mul_res_eq_res_of_valR_cocycle V g t htt hcoc i j l _ _ _ _

end GlobalTheory.TwistEmb
