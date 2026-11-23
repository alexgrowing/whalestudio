import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFramesOfHolPeriods
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrueCx.TorHolo

section Hol

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {X Z : Scheme.{0}}

theorem isHolTo_of_openImmersion (i : X ⟶ Z) [IsOpenImmersion i] {B : Set W} {y : W → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ i) : IsHolTo B y := by
  intro U f
  have hU : i ⁻¹ᵁ (i ''ᵁ U) = U := i.preimage_image_eq U
  have key : ∀ (U' : X.Opens) (_ : i ⁻¹ᵁ (i ''ᵁ U) = U') (f : Γ(X, U')), IsOpen {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} ∧
      DifferentiableOn ℂ (fun b => valAt' (y b) U' f) {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} := by
    rintro _ rfl f
    have : IsIso (i.app (i ''ᵁ U)) := i.isIso_app _ (i.image_le_opensRange U)
    obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso (i.app (i ''ᵁ U))).2 f
    have := h (i ''ᵁ U) g
    simp only [← ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_comp] at this
    exact this
  exact key U hU f

theorem isHolTo_const {B : Set W} (hB : IsOpen B) (x : Sp ℂ ⟶ X) : IsHolTo B fun _ => x := by
  intro U f
  refine ⟨?_, differentiableOn_const _⟩
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simpa only [h, and_true, Set.ofPred_mem_eq] using hB
  · simpa only [h, and_false, Set.ofPred_false] using isOpen_empty

theorem isHolTo_of_fst {S : Scheme.{0}} (p : X ⟶ Z) (q : S ⟶ Z) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    {y : (Fin n → ℂ) → (Sp ℂ ⟶ pullback p q)} (s : Sp ℂ ⟶ S) (hs : ∀ b, y b ≫ pullback.snd _ _ = s)
    (h : IsHolTo B fun b => y b ≫ pullback.fst _ _) : IsHolTo B y := by
  have he : ∀ b, (y b ≫ pullback.fst p q) ≫ p = s ≫ q := fun b => by
    rw [← hs b, Category.assoc, Category.assoc, pullback.condition]
  refine LocLift.isHolTo_congr (holPair _ _ _ p q n B _ (fun _ => s) he hB h (isHolTo_const hB s)) fun b _ => ?_
  exact pullback.hom_ext (pullback.lift_fst _ _ _).symm ((hs b).trans (pullback.lift_snd _ _ _).symm)

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem continuousOn_of_isHolTo {B : Set W} {y : W → CxPts p σ} (h : IsHolTo B fun b => (y b).1) :
    ContinuousOn y B := by
  rw [continuousOn_iff_continuous_domRestrict, CxPts.continuous_iff]
  intro U
  refine ⟨?_, fun f => ?_⟩
  · convert (h U 0).1.preimage (continuous_subtype_val (p := (· ∈ B))) using 1
    ext b
    exact ⟨fun hb => ⟨b.2, hb⟩, fun hb => hb.2⟩
  · exact (h U f).2.continuousOn.comp continuous_subtype_val.continuousOn fun b hb => ⟨b.2, hb⟩

theorem differentiableAt_chart {B : Set W} (hB : IsOpen B) {y : W → CxPts p σ} (h : IsHolTo B fun b => (y b).1)
    (ch : AlgChart p σ D) {b : W} (hb : b ∈ B) (hy : y b ∈ ch.e.source) :
    DifferentiableAt ℂ (fun v => ch.e (y v)) b := by
  refine (differentiableAt_piLp 2).2 fun a => ?_
  have h1 := ((h ch.U (ch.x a)).2).differentiableAt ((h ch.U (ch.x a)).1.mem_nhds ⟨hb, ch.source_subset hy⟩)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [((continuousOn_of_isHolTo h).continuousAt (hB.mem_nhds hb)).preimage_mem_nhds
    (ch.e.open_source.mem_nhds hy)] with v hv
  exact ch.apply_eq _ hv a

theorem isHolTo_symm (ch : AlgChart p σ D) : IsHolTo ch.e.target fun v => (ch.e.symm v).1 := fun U f =>
  ⟨ChartGlue.isOpen_over ch.e (isOpen_ptsIn U), ch.holo U f⟩

end Hol

section Frames

open GlobalTheory.TorsionHolomorphic ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (X : Data E r) {B : Set W}

theorem differentiableOn_perFr {x : W → Frame X.Ψ r} (hx : ∀ b ∈ B, x b ∈ X.dom)
    (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b) τ a c) B) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    DifferentiableOn ℂ (fun b => perFr X (x b) v τ i) B := by
  unfold perFr
  split_ifs with h1 h2 h3 h4
  · simp only [mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun a _ =>
      (differentiableOn_matrix_inv _ B (hd _) (fun b hb => (hx b hb _).1) _ _).mul_const _
  · exact differentiableOn_const _
  · simp only [hermC]
    exact DifferentiableOn.fun_sum fun a _ => DifferentiableOn.fun_sum fun c _ =>
      ((hd _ _ _).mul_const _).mul_const _
  · exact differentiableOn_const _
  · exact differentiableOn_const _

theorem differentiableOn_domPt (hj : j ≤ r) (κ : Tau → X.Ψ) (hp : X.p0 = r - j) {x : W → Frame X.Ψ r}
    (hx : ∀ b ∈ B, x b ∈ X.dom) (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b) τ a c) B) (t : Tau)
    (a : Fin j) (c : Fin (r - j)) : DifferentiableOn ℂ (fun b => domPt X hj κ (x b) t a c) B := by
  have h1 : ∀ a c, DifferentiableOn ℂ (fun b => frameCo X hj (x b) (κ t) a c) B := fun a c =>
    differentiableOn_matrix_mul (fun _ => (mat (x0F X) (κ t))⁻¹) (fun b => mat (x b) (κ t)) B
      (fun _ _ => differentiableOn_const _) (hd _) _ _
  simp only [domPt, moeb_zero, mul_apply]
  exact DifferentiableOn.fun_sum fun d _ => (h1 _ _).mul
    (differentiableOn_matrix_inv (fun b => (frameCo X hj (x b) (κ t)).toBlocks₂₂) B (fun _ _ => h1 _ _)
      (fun b hb => (frameCo_isUnit₂₂ X hj hp (hx b hb) _).ne_zero) _ _)

theorem differentiable_stdMat [Fintype Tau] (hj : j ≤ r) (κ : Tau ≃ X.Ψ) (τ : X.Ψ) (a c : Fin r) :
    Differentiable ℂ fun v => mat (stdMat X hj κ (unflat v)) τ a c := by
  refine differentiableOn_univ.1 (differentiableOn_matrix_mul (fun _ => mat (x0F X) τ)
    (fun v => reindex (idx hj).symm (idx hj).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) _
    (fun _ _ => differentiableOn_const _) (fun a c => ?_) a c)
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm]
  rcases idx hj a with a | a <;> rcases idx hj c with c | c
  · exact differentiableOn_const _
  · exact differentiableOn_apply (κ.symm τ, a, c) _
  · exact differentiableOn_const _
  · exact differentiableOn_const _

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ} {U : Unf Xo c σ r}

theorem isHolTo_torPt (hU : IsUnf U) (k : U.Comp) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (x : (Fin n → ℂ) → (U.X k).dom) (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B) :
    IsHolTo B fun b => (torPt Y (U.un k (x b))).1 := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hx _ using hun k
  have h1 := (F.hol (ik k) n B (fun b => P (x b)) hB ⟨fun b _ => hP' _, fun a => differentiableOn_pi.2 fun i => by
    simp only [hP]
    exact differentiableOn_perFr _ (fun b _ => (x b).2) hd _ _ _⟩).1
  refine isHolTo_of_fst _ _ hB _ (fun b => (torPt Y (U.un k (x b))).2) ?_
  simp only [torPt_pr]
  refine isHolTo_comp (isHolTo_of_fst _ _ hB _ (fun b => ptC_snd _) ?_) _
  simp only [ptC_fst]
  exact LocLift.isHolTo_congr h1 fun b _ => hx _

theorem isHolTo_domTor [Fintype Tau] (hU : IsUnf U) (e : Dw.p = j) (T : Tau ≃ Psi H) (k : U.Comp) :
    IsHolTo (DomFlat Tau j (r - j)) fun v => (domTor Y U hU e T k (unflat v)).1 := by
  classical
  let L : (Tau × Fin j × Fin (r - j) → ℂ) ≃L[ℂ] (Fin (Fintype.card (Tau × Fin j × Fin (r - j))) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin _).symm).toContinuousLinearEquiv
  have ho : IsOpen (DomFlat Tau j (r - j)) := ActionDeriv.isOpen_domFlat
  have h := isHolTo_torPt Y hU k (ho.preimage L.symm.continuous)
    (fun b => stdFrame (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) (first_index_eq_of_unfolded U hU e k) (unflat (L.symm b)))
    fun τ a c => ((differentiable_stdMat (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) τ a c).comp
      L.symm.differentiable).differentiableOn.congr fun b hb => by rw [stdFrame_val _ _ _ _ hb]; rfl
  refine LocLift.isHolTo_congr (LocLift.isHolTo_comp h ho L.differentiableOn fun v hv => ?_) fun v _ => ?_
  · rwa [Set.mem_preimage, L.symm_apply_apply]
  · rw [L.symm_apply_apply]
    rfl

theorem snd_eq_of_comp_j {w : TorPts Y σ} {y : Sp ℂ ⟶ Xo.XF c} (h : y ≫ Y.j = w.1 ≫ torPr Y σ) :
    y ≫ pullback.snd _ _ = spMap σ := by
  have e1 : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have e2 : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id _
  have h1 : Y.j ≫ Y.s = pullback.snd _ _ := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, e1, Category.comp_id]
  rw [← h1, ← Category.assoc, h, Category.assoc, pullback.condition, ← Category.assoc, w.2, e2, Category.id_comp]

theorem exists_frames (hU : IsUnf U) (hσ : GoodEmb c σ) (k : U.Comp) {n : ℕ} {B : Set (Fin n → ℂ)}
    {w : (Fin n → ℂ) → TorPts Y σ} (hw : IsHolTo B fun b => (w b).1) {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B)
    (x₀ : (U.X k).dom) (h0 : w b₀ = torPt Y (U.un k x₀)) :
    ∃ (B₁ : Set (Fin n → ℂ)) (x : (Fin n → ℂ) → Frame (U.X k).Ψ r), IsOpen B₁ ∧ b₀ ∈ B₁ ∧ DifferentiableOn ℂ x B₁ ∧
      ∀ b ∈ B₁, ∃ h : x b ∈ (U.X k).dom, torPt Y (U.un k ⟨_, h⟩) = w b := by
  obtain ⟨hr, hty, -, hfib, -, g, e, F, ik, ψ, hef, hun⟩ := hU
  have hw' := isHolTo_comp hw (torPr Y σ)
  have hB' := (hw' Y.j.opensRange 0).1
  have hb' : b₀ ∈ {b ∈ B | ⊤ ≤ ((w b).1 ≫ torPr Y σ) ⁻¹ᵁ Y.j.opensRange} := by
    refine ⟨hb₀, fun s _ => ⟨ptC (U.un k x₀) s, ?_⟩⟩
    rw [h0, torPt_pr, Scheme.Hom.comp_apply]
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨ptC (U.un k x₀)⟩
  have hy : ∀ b ∈ {b ∈ B | ⊤ ≤ ((w b).1 ≫ torPr Y σ) ⁻¹ᵁ Y.j.opensRange}, ∃ y : Sp ℂ ⟶ Xo.XF c,
      y ≫ Y.j = (w b).1 ≫ torPr Y σ := fun b hb =>
    ⟨IsOpenImmersion.lift Y.j _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  replace hw' := LocLift.isHolTo_mono hw' hB' fun b hb => hb.1
  generalize {b ∈ B | ⊤ ≤ ((w b).1 ≫ torPr Y σ) ⁻¹ᵁ Y.j.opensRange} = B' at hB' hb' hy hw'
  choose! y hy using hy
  have hyh : IsHolTo B' y := isHolTo_of_openImmersion Y.j (LocLift.isHolTo_congr hw' hy)
  have hpt : ∀ b ∈ B', ∀ z : Formalism.L2.Pj.FrPt Xo c (Formalism.L2.Pj.CAt σ), xC z = y b ≫ pullback.fst _ _ →
      torPt Y z = w b := fun b hb z hz => by
    have h1 : ptC z = y b :=
      pullback.hom_ext ((ptC_fst z).trans hz) ((ptC_snd z).trans (snd_eq_of_comp_j Y (hy b hb)).symm)
    exact Subtype.ext (pullback.hom_ext ((torPt_pr Y z).trans (h1 ▸ hy b hb)) ((torPt Y z).2.trans (w b).2.symm))
  obtain ⟨B₁, i, P, hB₁, hb₁, hs₁, hP, hyP⟩ := F.lift n B' (fun b => y b ≫ pullback.fst _ _) hB' (fun b hb => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, snd_eq_of_comp_j Y (hy b hb), ← Spec.map_comp]
    rfl) (isHolTo_comp hyh _) b₀ hb'
  obtain ⟨P₁, hP₁, hP₁', hx₁, -⟩ := hun k x₀
  have h1 : y b₀ = ptC (U.un k x₀) := (cancel_mono Y.j).1 (by rw [hy b₀ hb', h0, torPt_pr])
  obtain rfl : ik k = i := F.disj _ _ _ _ hP₁' (hP.1 b₀ hb₁)
    (hx₁.symm.trans ((ptC_fst _).symm.trans (h1 ▸ (hyP b₀ hb₁).symm)))
  obtain ⟨B₂, x', hB₂, hb₂, hs₂, hx'd, hx'⟩ := HolChartLift.exists_frames_of_holPeriods c σ e _ (U.X k) (ψ k) hσ
    (F.sig _).1 (F.sig _).2 hr (hty k).1 (hty k).2 (hef k)
    (FrameSign.im_neg_of_isPeriod E H Dw l c σ g e _ r (U.X k) (ψ k) hσ hr (hty k).1 (hty k).2 (hef k)
      x₀.1 x₀.2 P₁ hP₁ hP₁') hB₁ P hP hb₁
  refine ⟨B₂, x', hB₂, hb₂, hx'd, fun b hb => ?_⟩
  obtain ⟨x, hx, hper, β, hβ, hxβ⟩ := hx' b hb
  have hd : x' b ∈ (U.X k).dom := hxβ ▸ OrthogonalFrameDomain.rmul_mem_dom _ hx hβ
  obtain ⟨t, ht⟩ := (hfib k k ⟨x, hx⟩ ⟨_, hd⟩).2 ⟨1, one_mem _, β, hβ, by rw [KU.lact_one]; exact congrArg _ hxβ⟩
  obtain ⟨P₀, hP₀, -, hux, -⟩ := hun k ⟨x, hx⟩
  obtain rfl : P₀ = P b := AddMonoidHom.ext fun a => funext fun i => (hP₀ a i).trans (hper a i).symm
  exact ⟨hd, hpt b (hs₁ (hs₂ hb)) _ (ht.1.trans (hux.trans (hyP b (hs₂ hb))))⟩

theorem exists_lift [Fintype Tau] (hU : IsUnf U) (e : Dw.p = j) (hσ : GoodEmb c σ) (T : Tau ≃ Psi H) (k : U.Comp)
    {n : ℕ} {B : Set (Fin n → ℂ)} {w : (Fin n → ℂ) → TorPts Y σ} (hw : IsHolTo B fun b => (w b).1) {b₀ : Fin n → ℂ}
    (hb₀ : b₀ ∈ B) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) (h0 : w b₀ = domTor Y U hU e T k z) :
    ∃ s : (Fin n → ℂ) → (Tau × Fin j × Fin (r - j) → ℂ), DifferentiableAt ℂ s b₀ ∧ s b₀ = flat z ∧
      ∀ᶠ b in nhds b₀, domTor Y U hU e T k (unflat (s b)) = w b := by
  have hp := first_index_eq_of_unfolded U hU e k
  obtain ⟨B₁, x, hB₁, hb₁, hxd, hx⟩ := exists_frames Y hU hσ k hw hb₀ _ h0
  choose hx hxw using hx
  obtain ⟨m, hm, hm0, hmd, ht⟩ := PointOfFrames.exists_frBor U hU hσ k ⟨_, hx b₀ hb₁⟩ (domFr U hU e T k z)
    ((torPt_eq_iff Y).1 ((hxw b₀ hb₁).trans h0))
  obtain ⟨g, hg, β, hβ, h1⟩ := (hU.2.2.2.1 k k _ _).1 ht
  have h2 := eq_of_heq (Sigma.mk.inj h1).2
  have hl : ∀ b ∈ B₁, lact g (x b) ∈ (U.X k).dom := fun b hb => KU.lact_dom _ hg (hx b hb)
  refine ⟨fun b => flat (domPt (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) (lact g (x b))), ?_, ?_, ?_⟩
  · refine differentiableAt_pi.2 fun i => (differentiableOn_domPt _ _ _ hp hl (fun τ a c => ?_) _ _ _).differentiableAt
      (hB₁.mem_nhds hb₁)
    exact differentiableOn_matrix_mul (fun _ => (g : Matrix (Fin r) (Fin r) E).map τ.1) (fun b => mat (x b) τ) B₁
      (fun _ _ => differentiableOn_const _)
      (fun p q => differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hxd τ) p) q) a c
  · refine congrArg flat ?_
    rw [← domPt_stdFrame (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) hp hz, h2, domPt_rmul _ _ _ hβ,
      KU.lact_rmul', PointOfFrames.domPt_rmul_block _ _ _ _ m hm (hp ▸ hm0)]
  · filter_upwards [hB₁.mem_nhds hb₁] with b hb
    exact (domTor_domPt Y U hU e hσ T k ⟨_, hl b hb⟩).trans
      (((torPt_eq_iff Y).2 (PointWell.pt_lact hU k ⟨_, hx b hb⟩ hg)).trans (hxw b hb))

end Frames

theorem domTor_holo_immersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (σ : c.F →+* ℂ) (r j : ℕ) (U : Unf Xo c σ r) (hU : IsUnf U) (e : Dw.p = j) (hσ : GoodEmb c σ) (Tau : Type) [Fintype Tau] (T : Tau ≃ Psi H) (k : U.Comp), ContinuousOn (domTor Y U hU e T k) (DomI Tau j (r - j)) ∧ ∀ (ch : AlgChart (torStr Y σ) (RingHom.id ℂ) Dw.dim) (z : Pt Tau j (r - j)), z ∈ DomI Tau j (r - j) → domTor Y U hU e T k z ∈ ch.e.source → DifferentiableAt ℂ (fun v => ch.e (domTor Y U hU e T k (unflat v))) (flat z) ∧ Function.Injective (fderiv ℂ (fun v => ch.e (domTor Y U hU e T k (unflat v))) (flat z)) := by
  intro E _ _ _ H Dw l Xo c Y σ r j U hU e hσ Tau _ T k
  have hh := isHolTo_domTor Y hU e T k
  refine ⟨(continuousOn_of_isHolTo (y := fun v => domTor Y U hU e T k (unflat v)) hh).comp (f := flat)
    (continuous_pi fun i => by unfold flat; fun_prop).continuousOn fun z hz => hz, fun ch z hz hs => ?_⟩
  have hd := differentiableAt_chart (y := fun v => domTor Y U hU e T k (unflat v)) ActionDeriv.isOpen_domFlat hh ch
    (b := flat z) hz hs
  refine ⟨hd, ?_⟩
  let L := (EuclideanSpace.equiv (Fin Dw.dim) ℂ).symm
  have ht := ch.e.map_source hs
  obtain ⟨s, hsd, hs0, hsw⟩ := exists_lift Y hU e hσ T k (w := fun b => ch.e.symm (L b))
    (LocLift.isHolTo_comp (isHolTo_symm ch) (ch.e.open_target.preimage L.continuous) L.differentiableOn fun _ h => h)
    (b₀ := L.symm (ch.e (domTor Y U hU e T k z))) ht hz (ch.e.left_inv hs)
  have h1 : (fun v => ch.e (domTor Y U hU e T k (unflat v))) ∘ s =ᶠ[nhds (L.symm (ch.e (domTor Y U hU e T k z)))] L := by
    filter_upwards [hsw, (ch.e.open_target.preimage L.continuous).mem_nhds
      (show L.symm (ch.e (domTor Y U hU e T k z)) ∈ _ from ht)] with b hb hb'
    exact (congrArg ch.e hb).trans (ch.e.right_inv hb')
  have h2 := h1.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_comp _ (hs0 ▸ hd) hsd, hs0, L.fderiv] at h2
  have h3 : Function.Surjective (fderiv ℂ (fun v => ch.e (domTor Y U hU e T k (unflat v))) (flat z)) := fun v =>
    ⟨_, (DFunLike.congr_fun h2 (L.symm v)).trans (L.apply_symm_apply v)⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (fderiv ℂ (fun v => ch.e (domTor Y U hU e T k (unflat v))) (flat z)).toLinearMap) ?_).2 h3
  have h4 := (U.X k).card_Psi
  rw [← Fintype.card_congr (cmEquiv U hU T k)] at h4
  rw [finrank_euclideanSpace_fin, Module.finrank_fintype_fun_eq_card, Datum.dim, e, q_of_isUnf U hU e, ← h4]
  simp [_root_.mul_assoc]

end GlobalTheory.TrueCx.TorHolo
