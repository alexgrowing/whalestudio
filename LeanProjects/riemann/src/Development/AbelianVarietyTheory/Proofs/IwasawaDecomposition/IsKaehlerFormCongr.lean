import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMulFderivOfTsupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjCompatibleKaehlerForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullWIsConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleNsmulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArithmeticNefModelOfAmpleStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

namespace GlobalTheory.AmpleKaehler

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem isPotential_congr {σ : F →+* ℂ} {a b : ChartForm Y.str σ Y.dim}
    (h : ∀ (c : AlgChart Y.str σ Y.dim), ∀ y ∈ c.e.source, ∀ ξ, a c y ξ = b c y ξ) {W : Set (Pts Y σ)}
    {φ : Pts Y σ → ℝ} : IsPotential (Y.an σ) a W φ ↔ IsPotential (Y.an σ) b W φ := by
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun c => forall₂_congr fun y hy =>
    forall_congr' fun _ => forall_congr' fun ξ => ?_
  rw [h c y hy ξ]

theorem isKaehlerForm_congr {σ : F →+* ℂ} {a b : ChartForm Y.str σ Y.dim}
    (h : ∀ (c : AlgChart Y.str σ Y.dim), ∀ y ∈ c.e.source, ∀ ξ, a c y ξ = b c y ξ) :
    IsKaehlerForm (Y.an σ) a ↔ IsKaehlerForm (Y.an σ) b := by
  refine and_congr (forall_congr' fun y => exists₂_congr fun W φ => and_congr_right fun _ => isPotential_congr h)
    (forall_congr' fun c => forall₂_congr fun y hy => forall₂_congr fun ξ _ => ?_)
  rw [h c y hy ξ]

variable {σ : F →+* ℂ} {Δ : Y.Dv} {m : Var.Met Y σ Δ} {L : LB Y.X} {r : L.ι → Y.Fnˣ} {ψ : Weight Y.str σ L}

theorem mSmooth_of_wt (hp : Presents Δ L r) (hs : ψ.IsSmooth (Y.an σ))
    (he : ∀ i, ∀ y ∈ ptsIn Y.str σ (L.U i), m.h (r i) y = Real.exp (-ψ.φ i y)) : Y.mSmooth σ Δ m := by
  have e (i) (y) (hi : y ∈ ptsIn Y.str σ (L.U i)) : m.wt (r i) y = ψ.φ i y := by
    rw [Var.Met.wt, he i y hi, Real.log_exp, neg_neg]
  refine Var.Met.smoothOn_of_cover isOpen_univ (fun y _ => ?_) (fun i => isOpen_ptsIn (L.U i))
    (fun y => ⟨_, mem_pick ψ.isLB y⟩) (Var.ptsIn_subset_eqnSet hp)
    fun i => ((hs i).mono Set.inter_subset_right).congr fun y hy => e i y hy.2
  have hi := mem_pick ψ.isLB y
  rw [Var.Met.mem_posSet_iff (Var.ptsIn_subset_eqnSet hp _ hi), he _ _ hi]
  exact Real.exp_pos _

theorem curvMet_eq (hp : Presents Δ L r) (hs : ψ.IsSmooth (Y.an σ))
    (he : ∀ i, ∀ y ∈ ptsIn Y.str σ (L.U i), m.h (r i) y = Real.exp (-ψ.φ i y))
    (c : AlgChart Y.str σ Y.dim) (y : Pts Y σ) (hy : y ∈ c.e.source) (ξ : Fin Y.dim → ℂ) :
    curvMet m c y ξ = curvForm ψ c y ξ := by
  have hm := mSmooth_of_wt hp hs he
  have hi := mem_pick ψ.isLB y
  have e₁ := hm.levi_frame Var.smoothOn_zero hy (Var.ptsIn_subset_eqnSet hp _ hi) (Var.mem_eqnSet Δ y) ξ
  simp only [Pi.zero_apply, add_zero] at e₁
  change c.levi _ y ξ / Real.pi = c.levi _ y ξ / Real.pi
  rw [e₁]
  refine congrArg (· / Real.pi) (AlgChart.levi_congr (isOpen_ptsIn _) hy hi (fun z hz => ?_) ξ)
  rw [Var.Met.wt, he _ _ hz, Real.log_exp, neg_neg]

end GlobalTheory.AmpleKaehler

namespace GlobalTheory.AmpleKaehler

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem h_of_induced {A : Adl (cxSt F) Y} {Z : TrueGeo.Model Y} {L : HermLB Z.p} {cf : HeightOneSpectrum (𝓞 F) → ℝ}
    (hA : A.Induced Z L 1 cf) (hci : ∀ v, A.ci v = 0) (σ : F →+* ℂ) :
    ∃ r : (L.B.pull Z.j).ι → Y.Fnˣ, Presents A.D (L.B.pull Z.j) r ∧
      ∀ i, ∀ y ∈ ptsIn Y.str σ ((L.B.pull Z.j).U i), (A.m σ).h (r i) y = Real.exp (-(pullW Z L σ).φ i y) := by
  obtain ⟨-, r, hr, h₂, -⟩ := hA
  have hr₁ : Presents A.D (L.B.pull Z.j) r := by simpa using hr
  refine ⟨r, hr₁, fun i y hy => ?_⟩
  have hi : under y ∈ (L.B.pull Z.j).U i := Var.mem_ptsIn_iff.1 hy
  have h₁ : A.D.IsEqn (under y) (r i) := hr₁.isEqn i _ hi
  have hf : (1 • A.D).RegularAt (under y) ((r i : Y.Fn)⁻¹) := by
    rw [one_nsmul]; exact (CartierDiv.isEqn_iff_generatesAt_inv.1 h₁).regularAt
  have e := h₂ σ y (OfModel.ptMap Z σ y) i ((r i : Y.Fn)⁻¹) rfl hi (by simpa using hf)
  have h₈ : ratVal (1 : Y.Fn) y = 1 := by
    have e' := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
    rwa [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e'
  simp only [hci, mul_zero, neg_zero, Real.exp_zero, one_mul, PNat.val_ofNat] at e
  rw [OfLattice.pn_mPow_one (cxSt F) σ (A.m σ) y h₁ hf, inv_mul_cancel₀ (r i).ne_zero, h₈] at e
  simp only [norm_one, one_pow, one_mul] at e
  rw [pullW_φ, ← e, ← Units.val_inv_eq_inv_val]
  exact (Var.pn_frame (Var.ptsIn_subset_eqnSet hr₁ i hy)).symm

theorem exists_ample_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ : Y.Dv), Y.ample Δ → ∃ M : Adl (cxSt F) Y, qDiv M = 1 ⊗ₜ Δ ∧ Y.ample M.D ∧ (∃ (Z : TrueGeo.Model Y) (L : HermLB Z.p) (q : ℕ+), M.Induced Z L q 0 ∧ ArInt.NefFib L) ∧ (∀ σ, (cxSt F).mSmooth Y σ _ (M.m σ) ∧ IsKaehlerForm (Y.an σ) (curvMet (M.m σ))) ∧ ∀ σ σ' (ι : Pts Y σ' → Pts Y σ), IsConjMap ι → (∀ W φ, IsPotential (Y.an σ) (curvMet (M.m σ)) W φ → IsPotential (Y.an σ') (curvMet (M.m σ')) (ι ⁻¹' W) (φ ∘ ι)) := by
  intro F _ _ Y Δ hΔ
  obtain ⟨q, Z, L, r, hr, hnef, hw⟩ := GlobalTheory.T.exists_arithmetic_nef_model_of_ample F Y Δ hΔ
  obtain ⟨A, hD, hn, hci, hA⟩ := OfModel.exists_induced F (cxSt F) Y Z L ((q : ℕ) • Δ) r hr
  have hci' : ∀ v, A.ci v = 0 := fun v => by rw [hci]; rfl
  have key (σ : F →+* ℂ) : (cxSt F).mSmooth Y σ _ (A.m σ) ∧
      ∀ (c : AlgChart Y.str σ Y.dim), ∀ y ∈ c.e.source, ∀ ξ, curvMet (A.m σ) c y ξ = curvForm (pullW Z L σ) c y ξ := by
    obtain ⟨r', hr', he⟩ := h_of_induced hA hci' σ
    exact ⟨mSmooth_of_wt hr' (hw σ).1 he, curvMet_eq hr' (hw σ).1 he⟩
  refine ⟨A.divide q, ?_, ?_, ⟨Z, L, 1, ?_, hnef⟩, fun σ => ⟨(key σ).1, ?_⟩, fun σ σ' ι hι W φ hφ => ?_⟩
  · simp only [qDiv, Adl.divide, hn, hD, one_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    rw [nsmul_eq_mul]
    field_simp
  · change Y.ample A.D
    rw [hD]
    exact GlobalTheory.T.ample_nsmul_of_pos F Y Δ q q.pos hΔ
  · have := hA.divide q
    convert this using 1
    funext v
    simp
  · exact (isKaehlerForm_congr (key σ).2).2 (isKaehlerForm_curvForm (hw σ).1 (hw σ).2)
  · have h₁ := (isPotential_congr (key σ).2).1 hφ
    exact (isPotential_congr (key σ').2).2
      (KaehlerFamily.isPotential_conj (hw σ).1 (pullW_isConj Z L σ σ') hι h₁)

end GlobalTheory.AmpleKaehler
