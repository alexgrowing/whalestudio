import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqConstMulOfNormOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.La1sqEqOfUnXEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalDecayHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealFlowPeriodsSpanEqTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CompactEntryBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoverHol
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X₂.Gm u w := by
  have h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1 := Matrix.map_one τ τ.map_zero τ.map_one
  conv_rhs => rw [← Matrix.one_mulVec u, ← Matrix.one_mulVec w, ← h1]
  rw [CompactEntryBounds.hermC_expand X, CompactEntryBounds.hermC_expand X₂]
  simp only [hγ, Matrix.one_mulVec]

theorem col_mul (A Y : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col (A * Y) c = A *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col Y c := by
  funext i; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem gram_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (γ.map τ * Y) = ReciprocityTheory.ChartRestriction.G.FD.gram τ X₂.Gm Y := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply]
  rw [col_mul, col_mul, hermC_move X X₂ hγ]

def majM (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p : ℕ) (hp : p ≤ r) (M : Matrix (Fin r) (Fin r) ℂ)
    (v : Fin r → ℂ) : ℝ :=
  2 * (∑ a : Fin p, ∑ b : Fin p,
    hermC τ G v (ReciprocityTheory.ChartRestriction.G.FD.col M (Fin.castLE hp a)) *
      ((ReciprocityTheory.ChartRestriction.G.FD.gram τ G M).submatrix (Fin.castLE hp) (Fin.castLE hp))⁻¹ a b *
      conj (hermC τ G v (ReciprocityTheory.ChartRestriction.G.FD.col M (Fin.castLE hp b)))).re - (hermC τ G v v).re

theorem maj_eq (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj x τ v = majM τ.1 X.Gm X.p0 X.p0_le (mat x τ) v := rfl

omit [NumberField E] [IsCMField E] in
theorem majM_congr (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {p q : ℕ} (hp : p ≤ r) (hq : q ≤ r) (h : p = q)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) : majM τ G p hp M v = majM τ G q hq M v := by
  subst h; rfl

theorem majM_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (τ : E →+* ℂ) {p : ℕ} (hp : p ≤ r)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    majM τ X.Gm p hp (γ.map τ * M) (γ.map τ *ᵥ v) = majM τ X₂.Gm p hp M v := by
  unfold majM
  simp only [col_mul, hermC_move X X₂ hγ, gram_move X X₂ hγ]

theorem maj_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (hp : X.p0 = X₂.p0)
    (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ)
    (hrel : mat x' ⟨τ, h₁⟩ = γ.map τ * mat x ⟨τ, h₂⟩) (v : Fin r → E) :
    X.maj x' ⟨τ, h₁⟩ (Data.emb τ (γ *ᵥ v)) = X₂.maj x ⟨τ, h₂⟩ (Data.emb τ v) := by
  rw [maj_eq, maj_eq, hrel, ← ReciprocityTheory.ChartRestriction.G.AR.Inst.emb_mulVec, majM_move X X₂ hγ]
  exact majM_congr _ _ _ _ hp _ _

theorem dmin_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w)
    (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ)
    (hrel : mat x' ⟨τ, h₁⟩ = γ.map τ * mat x ⟨τ, h₂⟩) (i : Fin (r + 1)) :
    dmin X.Gm x' ⟨τ, h₁⟩ i = dmin X₂.Gm x ⟨τ, h₂⟩ i := by
  unfold dmin
  rw [hrel, gram_move X X₂ hγ]

theorem pnorm_move (X X₂ : Data E r) (hΨ : ∀ τ, τ ∈ X₂.Ψ ↔ τ ∈ X.Ψ) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (la : Wt X.Ψ r) (la₂ : Wt X₂.Ψ r)
    (hla : ∀ τ (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ) i, la₂ ⟨τ, h₂⟩ i = la ⟨τ, h₁⟩ i)
    (P : Frame X.Ψ r → ℂ) (P₂ : Frame X₂.Ψ r → ℂ) (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r)
    (hrel : ∀ τ (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = γ.map τ * mat x ⟨τ, h₂⟩)
    (u : ℂ) (hu : ‖u‖ = 1) (hP : P₂ x = u * P x') :
    X₂.pnorm la₂ P₂ x = X.pnorm la P x' := by
  unfold Data.pnorm
  rw [hP, norm_mul, hu, one_mul]
  congr 1
  refine Fintype.prod_equiv (Equiv.subtypeEquivRight hΨ) _ _ (fun τ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h₁ : τ.1 ∈ X.Ψ := (hΨ τ.1).1 τ.2
  show _ = ‖dmin X.Gm x' ⟨τ.1, h₁⟩ i.succ / dmin X.Gm x' ⟨τ.1, h₁⟩ i.castSucc‖ ^ (-(la ⟨τ.1, h₁⟩ i : ℝ) / 2)
  rw [dmin_move X X₂ hγ x x' τ.1 τ.2 h₁ (hrel τ.1 τ.2 h₁), dmin_move X X₂ hγ x x' τ.1 τ.2 h₁ (hrel τ.1 τ.2 h₁),
    ← hla τ.1 τ.2 h₁ i]

theorem exists_firstMinimumSq_bound_of_rationalIsometry (X X₂ : Data E r) (hr : 0 < r) (hΨ : ∀ τ, τ ∈ X₂.Ψ ↔ τ ∈ X.Ψ) (γ : GL (Fin r) E)
    (hΛ : (X.Λ : Set (Fin r → E)) = (γ : Matrix (Fin r) (Fin r) E).mulVec '' (X₂.Λ : Set (Fin r → E)))
    (hγ : ∀ v w, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) =
      herm X₂.Gm v w) (hp : X.p0 = X₂.p0) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ X₂.dom, ∀ x' ∈ X.dom,
      (∀ τ (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩) →
      X.firstMinimumSq x' ≤ K * X₂.firstMinimumSq x := by
  set K : ℝ := 1 + ∑ τ : X₂.Ψ, X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ / X₂.c τ with hKdef
  have hc2 : ∀ τ : X₂.Ψ, 0 < X₂.c τ := fun τ => IsotropicThreshold.c_pos X₂ τ
  have hKτ : ∀ τ : X₂.Ψ, X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ ≤ K * X₂.c τ := by
    intro τ
    have h1 : X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ / X₂.c τ ≤ K := by
      have := Finset.single_le_sum (f := fun τ : X₂.Ψ => X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ / X₂.c τ)
        (fun τ _ => (div_pos (IsotropicThreshold.c_pos X _) (hc2 τ)).le) (Finset.mem_univ τ)
      linarith
    rwa [div_le_iff₀ (hc2 τ)] at h1
  have hK : 0 < K := by
    have := Finset.sum_nonneg (fun τ (_ : τ ∈ (Finset.univ : Finset X₂.Ψ)) =>
      (div_pos (IsotropicThreshold.c_pos X ⟨τ.1, (hΨ τ.1).1 τ.2⟩) (hc2 τ)).le)
    linarith
  refine ⟨K, hK, fun x hx x' hx' hrel => ?_⟩
  obtain ⟨w₀, hw₀, hw₀0⟩ := ReciprocityTheory.ChartRestriction.G.AR.Inst.lam_ne X₂ hr
  unfold Data.firstMinimumSq
  set S := {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x' τ (Data.emb τ.1 v)} with hS
  set S₂ := {t | ∃ v ∈ X₂.Λ, v ≠ 0 ∧ t = ∑ τ, X₂.c τ * X₂.maj x τ (Data.emb τ.1 v)} with hS₂
  have hSb : BddBelow S := ⟨0, by
    rintro _ ⟨v, -, hv0, rfl⟩
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (IsotropicThreshold.c_pos X τ).le
      (X.maj_pos hx' τ (emb_ne_zero τ.1 hv0)).le⟩
  have hS₂ne : S₂.Nonempty := ⟨_, w₀, hw₀, hw₀0, rfl⟩
  have key : sInf S / K ≤ sInf S₂ := by
    refine le_csInf hS₂ne ?_
    rintro _ ⟨w, hw, hw0, rfl⟩
    rw [div_le_iff₀ hK]
    have hγw : (γ : Matrix (Fin r) (Fin r) E) *ᵥ w ∈ X.Λ := by
      have : (γ : Matrix (Fin r) (Fin r) E) *ᵥ w ∈ (X.Λ : Set (Fin r → E)) := by
        rw [hΛ]; exact ⟨w, hw, rfl⟩
      exact this
    have hγw0 : (γ : Matrix (Fin r) (Fin r) E) *ᵥ w ≠ 0 := by
      intro h0
      apply hw0
      have e : (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) = w := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← e, h0, Matrix.mulVec_zero]
    refine (csInf_le hSb ⟨_, hγw, hγw0, rfl⟩).trans ?_
    have hre : ∑ τ : X.Ψ, X.c τ * X.maj x' τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) =
        ∑ τ : X₂.Ψ, X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ * X₂.maj x τ (Data.emb τ.1 w) := by
      refine (Fintype.sum_equiv (Equiv.subtypeEquivRight hΨ) _ _ (fun τ => ?_)).symm
      show X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ * X₂.maj x τ (Data.emb τ.1 w) = X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ *
        X.maj x' ⟨τ.1, (hΨ τ.1).1 τ.2⟩ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w))
      rw [maj_move X X₂ hγ hp x x' τ.1 τ.2 ((hΨ τ.1).1 τ.2) (hrel τ.1 τ.2 _)]
    rw [hre, Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => ?_
    have hm := (X₂.maj_pos hx τ (emb_ne_zero τ.1 hw0)).le
    calc _ ≤ (K * X₂.c τ) * X₂.maj x τ (Data.emb τ.1 w) := mul_le_mul_of_nonneg_right (hKτ τ) hm
      _ = _ := by ring
  rwa [div_le_iff₀ hK, mul_comm] at key

theorem cover_pull_holSub0 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ ∈ holSub0 C.U₂.X (laU C.U₂ a n) := by
  intro D T hL j hj σ hσ C hC a n hDom f hf hfh f₂ hf₂ hP
  refine Submodule.mem_inf.2 ⟨holCusp_mem_holSub _ _ (fun k₂ => ?_), rdU_mem_offZero _ _⟩
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ
  have hS := Formalism.L2.Pj.abelian₂.holSub_SS ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _ _ (Submodule.mem_inf.1 hfh).1
  obtain ⟨k, γ, hΛ, hh, -, u, hu1, hx⟩ := GlobalTheory.CoverConst.cover_scalar_const D T hL j hj σ hσ C hC n k₂
  obtain ⟨hΨ, hla⟩ := GlobalTheory.CoverConst.psi_and_weight_eq D T hL j hj σ hσ C hC k₂ k
  have hp : ((T.U j σ).X k).p0 = (C.U₂.X k₂).p0 := ((hU₁.2.1 k).1).trans ((hU₂.2.1 k₂).1).symm
  let G : Frame (C.U₂.X k₂).Ψ D.R.r → Frame ((T.U j σ).X k).Ψ D.R.r := fun x τ =>
    ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩ :
      Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hGrel : ∀ x (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ),
      mat (G x) ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩ :=
    fun _ _ _ _ => rfl
  have hG : ∀ x ∈ (C.U₂.X k₂).dom, G x ∈ ((T.U j σ).X k).dom ∧
      rdU C.U₂ f₂ k₂ x = u * rdU (T.U j σ) f k (G x) := fun x hxd =>
    ⟨(hx x (G x) hxd (hGrel x)).1, (hx x (G x) hxd (hGrel x)).2 a hDom f hf f₂ hf₂ hP⟩
  have hpn : ∀ x ∈ (C.U₂.X k₂).dom, (C.U₂.X k₂).pnorm (laU C.U₂ a n k₂) (rdU C.U₂ f₂ k₂) x =
      ((T.U j σ).X k).pnorm (laU (T.U j σ) a n k) (rdU (T.U j σ) f k) (G x) := fun x hxd =>
    pnorm_move _ _ hΨ hh _ _ (fun τ h₂ h₁ i => hla a n τ h₂ h₁ i) _ _ x (G x) (hGrel x) u hu1 (hG x hxd).2
  have hsec := hU₂.2.2.2.2.1 a n hDom f₂ hf₂ k₂
  obtain ⟨B, hB⟩ := (hS k).1.2
  have hbdd : (C.U₂.X k₂).IsBddSec (laU C.U₂ a n k₂) (rdU C.U₂ f₂ k₂) :=
    ⟨hsec, B, fun x hxd => (hpn x hxd).trans_le (hB _ (hG x hxd).1)⟩
  by_cases hr : 0 < D.R.r
  · obtain ⟨c₀, hc₀, hgt⟩ := ReciprocityTheory.ChartRestriction.G.FD.spectralGap_holds D.R.r _ _ _ (hS k)
    obtain ⟨C₁, hC₁⟩ := ReciprocityTheory.ChartRestriction.G.FD.cuspidalDecay_holds D.R.r _ _ _ c₀ hc₀.le hgt
    obtain ⟨K, hK, hle⟩ := exists_firstMinimumSq_bound_of_rationalIsometry _ _ hr hΨ γ hΛ hh hp
    refine GlobalTheory.CuspUnif.mem_SS_of_decay _ hr _ _ hbdd (C := |C₁|) (c := 2 * Real.pi * c₀ / K) (by positivity)
      fun x hxd => ?_
    have hGd := (hG x hxd).1
    have hl : 0 < ((T.U j σ).X k).firstMinimumSq (G x) := Real.sqrt_pos.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom _ hr hGd)
    have hl₂ : 0 < (C.U₂.X k₂).firstMinimumSq x := Real.sqrt_pos.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom _ hr hxd)
    have hle' := hle x hxd (G x) hGd (hGrel x)
    rw [hpn x hxd]
    refine (hC₁ (G x) hGd).trans ?_
    refine mul_le_mul (le_abs_self _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (abs_nonneg _)
    have hq : 2 * Real.pi * c₀ / K / (C.U₂.X k₂).firstMinimumSq x ≤ 2 * Real.pi * c₀ / ((T.U j σ).X k).firstMinimumSq (G x) := by
      rw [div_div, div_le_div_iff₀ (by positivity) hl]
      exact mul_le_mul_of_nonneg_left hle' (by positivity)
    have e1 : -2 * Real.pi * c₀ / ((T.U j σ).X k).firstMinimumSq (G x) =
        -(2 * Real.pi * c₀ / ((T.U j σ).X k).firstMinimumSq (G x)) := by ring
    rw [e1, neg_div]
    exact neg_le_neg hq
  · refine ⟨hbdd, fun ξ hξ x _ => ?_⟩
    exfalso
    apply hξ.2.2
    funext i
    exact absurd i.2 (by omega)

end GlobalTheory.CoverHol
