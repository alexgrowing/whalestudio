import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open GlobalTheory.GradedPieces GlobalTheory.Points GlobalTheory.LieMet

namespace GlobalTheory.LocM.LatGr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B}

theorem tan_of_flagAt {k : Type} [Field k] {x : Sp k ⟶ Z.X} {u : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u) :
    ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u σ i) := by
  obtain ⟨a, φ, -, hf, -⟩ := h
  exact fun σ i => (hf.1 σ i).1

theorem linInd_of_flagAt {k : Type} [Field k] {x : Sp k ⟶ Z.X} {u : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u)
    (σ : E →+* ℂ) : LinearIndependent k fun i => tanOf (tan_of_flagAt h σ i) := by
  obtain ⟨a, φ, -, hf, -⟩ := id h
  have e : GlobalTheory.DRFlag.up (Dw := Dw) (fun σ i => tanOf (tan_of_flagAt h σ i)) = u :=
    funext fun σ => funext fun i => left_tanOf _
  have hf' : LocM.IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (x ≫ Z.π)
      (GlobalTheory.DRFlag.up (Dw := Dw) (fun σ i => tanOf (tan_of_flagAt h σ i))) := by
    rw [e]
    exact hf
  exact ((GlobalTheory.DRFlag.isFrame_up_iff (φ.comp (Z.alg a)) _).1 hf' σ).1

theorem exists_diag_frames (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {k : Type} [Field k]
    {x : Sp k ⟶ Z.X} {u u' : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u) (h' : Z.FlagAt x u') :
    ∃ d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k, ∀ σ,
      Diag (fun i => tanOf (tan_of_flagAt h' σ i)) (fun i => tanOf (tan_of_flagAt h σ i)) (d σ) := by
  choose d hd using fun σ => exists_diag_of_flagAt Z hty h h' σ (tan_of_flagAt h σ) (tan_of_flagAt h' σ)
    (linInd_of_flagAt h' σ)
  exact ⟨d, hd⟩

theorem diag_ne_zero {k M : Type} [Field k] [AddCommGroup M] [Module k M] {m : ℕ} {p q : Fin m → M}
    {d : Fin m → k} (hd : Diag p q d) (hp : LinearIndependent k p) (hq : LinearIndependent k q) (a : Fin m) :
    d a ≠ 0 := by
  obtain ⟨d', h'⟩ := hd.symm hq
  have e := congrFun ((hd.trans h').unique hp (Diag.refl p)) a
  intro h0
  simp only [h0, mul_zero] at e
  exact zero_ne_one e

variable (hex : ∀ (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ),
  ∃ a : Γ(Z.X, q.U ⊓ q'.U)ˣ, q.IsTr q' e a.val)
include hex

theorem valR_tr (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) {k : Type} [Field k]
    (x : Sp k ⟶ Z.X) {u u' : Vecs Dw (Y Z.i).t k} (hu : q.FrameAt x u) (hu' : q'.FrameAt x u')
    (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k)
    (hd : ∀ σ, Diag (fun i => tanOf (tan_of_flagAt hu'.2.1 σ i)) (fun i => tanOf (tan_of_flagAt hu.2.1 σ i)) (d σ)) :
    valR x _ (q.tr q' e).val = ∏ σ, ∏ i, d σ i ^ e σ i :=
  LatChart.isTr_tr (hex q q' e) k x u u' d hu hu' fun σ => (diagAt_iff _ _ _).2 (hd σ)

theorem valR_res_tr (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) {k : Type} [Field k]
    (x : Sp k ⟶ Z.X) {V : Z.X.Opens} (hV : V ≤ q.U ⊓ q'.U) (h : ⊤ ≤ x ⁻¹ᵁ V) {u u' : Vecs Dw (Y Z.i).t k}
    (hu : q.FrameAt x u) (hu' : q'.FrameAt x u') (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k)
    (hd : ∀ σ, Diag (fun i => tanOf (tan_of_flagAt hu'.2.1 σ i)) (fun i => tanOf (tan_of_flagAt hu.2.1 σ i)) (d σ)) :
    valR x V (res hV (q.tr q' e)).val = ∏ σ, ∏ i, d σ i ^ e σ i :=
  (valR_res x hV h _).trans (valR_tr hex q q' e x hu hu' d hd)

variable (hL : HasLatFlags Z L)
include hL

theorem isLB_latLB (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : (latLB Z L e).IsLB := by
  refine ⟨top_unique fun z _ => Opens.mem_iSup.2 (hL.2 z), fun q => ?_, fun q q' q'' => ?_⟩
  · refine Units.ext (fn_ext Z fun k _ x h ho => ?_)
    obtain ⟨u, hu⟩ := q.exists_frameAt h ho
    refine (valR_res_tr hex q q e x _ h hu hu (fun _ _ => 1) fun σ => Diag.refl _).trans ?_
    simp only [one_zpow, Finset.prod_const_one]
    exact (valR_one x _ h).symm
  · refine Units.ext (fn_ext Z fun k _ x h ho => (valR_mul x _ h _ _).trans ?_)
    obtain ⟨u, hu⟩ := q.exists_frameAt (le_preimage_mono x (inf_le_left.trans inf_le_left) h) ho
    obtain ⟨u', hu'⟩ := q'.exists_frameAt (le_preimage_mono x (inf_le_left.trans inf_le_right) h) ho
    obtain ⟨u'', hu''⟩ := q''.exists_frameAt (le_preimage_mono x inf_le_right h) ho
    obtain ⟨d₁, hd₁⟩ := exists_diag_frames hL.1 hu.2.1 hu'.2.1
    obtain ⟨d₂, hd₂⟩ := exists_diag_frames hL.1 hu'.2.1 hu''.2.1
    refine (congrArg₂ (· * ·) (valR_res_tr hex q q' e x _ h hu hu' d₁ hd₁)
      (valR_res_tr hex q' q'' e x _ h hu' hu'' d₂ hd₂)).trans
      (.trans ?_ (valR_res_tr hex q q'' e x _ h hu hu'' _ fun σ => (hd₂ σ).trans (hd₁ σ)).symm)
    simp only [mul_zpow, Finset.prod_mul_distrib]

theorem tr_add (q q' : LatChart Z L) (e e' : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) :
    q.tr q' (e + e') = q.tr q' e * q.tr q' e' := by
  refine Units.ext (fn_ext Z fun k _ x h ho => ?_)
  obtain ⟨u, hu⟩ := q.exists_frameAt (le_preimage_mono x inf_le_left h) ho
  obtain ⟨u', hu'⟩ := q'.exists_frameAt (le_preimage_mono x inf_le_right h) ho
  obtain ⟨d, hd⟩ := exists_diag_frames hL.1 hu.2.1 hu'.2.1
  rw [Units.val_mul, valR_mul x _ h, valR_tr hex q q' _ x hu hu' d hd, valR_tr hex q q' e x hu hu' d hd,
    valR_tr hex q q' e' x hu hu' d hd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact zpow_add₀ (diag_ne_zero (hd σ) (linInd_of_flagAt hu'.2.1 σ) (linInd_of_flagAt hu.2.1 σ) i) _ _

end GlobalTheory.LocM.LatGr

open GlobalTheory.LocM.LatGr in

theorem GlobalTheory.LocM.LatGr.isLB_latLB_and_tr_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ),
    p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z B : Mdl Y i₀) (L : Lat B),
    HasLatFlags Z L → (∀ (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ),
      ∃ a : Γ(Z.X, q.U ⊓ q'.U)ˣ, q.IsTr q' e a.val) →
    (∀ e, (latLB Z L e).IsLB) ∧ ∀ (q q' : LatChart Z L) (e e' : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ),
      q.tr q' (e + e') = q.tr q' e * q.tr q' e' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL hex => ⟨fun e => isLB_latLB hex hL e, fun q q' e e' => tr_add hex hL q q' e e'⟩
