import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedFrameCMUnitaryProofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormNonzeroAtOneLiftStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix

namespace GlobalTheory.TranslatesDet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermMat {G γ : Matrix (Fin r) (Fin r) E}
    (h : ∀ v w, herm G (Matrix.mulVec γ v) (Matrix.mulVec γ w) = herm G v w) :
    γᵀ * G * γ.map cc = G := by
  ext c d
  have h1 := h (Pi.single c 1) (Pi.single d 1)
  simp only [herm, Matrix.mulVec_single_one] at h1
  have h2 : (∑ a, ∑ b, (Pi.single c (1 : E) : Fin r → E) a * G a b *
      cc ((Pi.single d (1 : E) : Fin r → E) b)) = G c d := by simp [Pi.single_apply, cc]
  rw [← h2, ← h1]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem gramLact {G : Matrix (Fin r) (Fin r) E} {γ : GL (Fin r) E}
    (h : ∀ v w, herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v)
      (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) w) = herm G v w)
    (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G ((γ : Matrix (Fin r) (Fin r) E).map τ * M) = gram τ G M := by
  have hc : ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ := by
    ext a b; simp [cc, NumberField.IsCMField.complexEmbedding_complexConj]
  have key : ((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ *
      ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) = G.map τ := by
    rw [hc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hermMat h]
  rw [FrameDegreeData.gram_eq, FrameDegreeData.gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  calc Mᵀ * ((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ *
        (((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) * M.map (starRingEnd ℂ))
      = Mᵀ * (((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ *
        ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key]

theorem lactGG {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {p0 : ℕ} {γ : GL (Fin r) E}
    (h : ∀ v w, herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v)
      (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) w) = herm G v w)
    {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : lact γ x ∈ GG Ψ G p0 := by
  intro τ
  have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    refine mul_ne_zero ?_ (hx τ).1
    have hd : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det := by
      rw [RingHom.map_det]; rfl
    rw [hd]
    exact (map_ne_zero τ.1).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)
  · have e : dmin G (lact γ x) τ i = dmin G x τ i := by
      unfold dmin; rw [hm, gramLact h]
    rw [e]; exact (hx τ).2 i

theorem lactMul {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = ((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem castGG {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {G : Matrix (Fin r) (Fin r) E} {p0 : ℕ}
    {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : castFrame h x ∈ GG Ψ' G p0 := by
  subst h; exact hx

section Two

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem domOfComp (c : C) {x : Frame (M.comp c).Ψ r} (hx : x ∈ (M.comp c).dom) :
    castFrame (M.comp_Ψ c) x ∈ M.dom := by
  have h := castGG (M.comp_Ψ c) hx
  rw [M.comp_Gm c, M.comp_basePoint c] at h
  exact h

theorem domToComp (c : C) {x : Frame M.Ψ r} (hx : x ∈ M.dom) :
    castFrame (M.comp_Ψ c).symm x ∈ (M.comp c).dom := by
  have hx' : x ∈ GG M.Ψ (M.comp c).Gm (M.comp c).p0 := by
    rw [M.comp_Gm c, M.comp_basePoint c]; exact hx
  exact castGG (M.comp_Ψ c).symm hx'

theorem trDom (u : U) (c : C) {x : Frame M.Ψ r} (hx : x ∈ M.dom) : lact (M.tr u c) x ∈ M.dom :=
  lactGG (M.tr_herm u c) hx

theorem ssLact {la : Wt M.Ψ r} {F : C → Frame M.Ψ r → ℂ} (hF : F ∈ M.SS la) (c : C)
    {γ : GL (Fin r) E} (hγ : γ ∈ (M.comp c).Γ) {x : Frame M.Ψ r} (hx : x ∈ M.dom) :
    F c (lact γ x) = F c x := by
  have h1 := (hF c).1.1.2.2 γ hγ (castFrame (M.comp_Ψ c).symm x) (domToComp M c hx)
  rw [M.χ_one c _ γ hγ, one_mul] at h1
  exact h1

theorem ssZero (la : Wt M.Ψ r) : (0 : C → Frame M.Ψ r → ℂ) ∈ M.SS la := by
  intro c
  exact ⟨BoundedSectionAlgebra.bdd_zero _ _, fun ξ _ x _ => BoundedSectionAlgebra.fj_zero _ _ ξ x 0⟩

theorem ssAdd {la : Wt M.Ψ r} {F G : C → Frame M.Ψ r → ℂ} (hF : F ∈ M.SS la) (hG : G ∈ M.SS la) :
    F + G ∈ M.SS la := by
  intro c
  have h := hF c
  have h' := hG c
  have e : (fun y => (F + G) c (castFrame (M.comp_Ψ c) y)) =
      (fun y => F c (castFrame (M.comp_Ψ c) y)) + (fun y => G c (castFrame (M.comp_Ψ c) y)) := rfl
  rw [e]
  exact ⟨BoundedSectionAlgebra.bdd_add _ h.1 h'.1, fun ξ hξ x hx => by
    rw [BoundedSectionAlgebra.fj_add _ h.1 h'.1 hξ hx, h.2 ξ hξ x hx, h'.2 ξ hξ x hx, add_zero]⟩

theorem ssSum {la : Wt M.Ψ r} {ι : Type} (s : Finset ι) (f : ι → C → Frame M.Ψ r → ℂ)
    (h : ∀ i ∈ s, f i ∈ M.SS la) : ∑ i ∈ s, f i ∈ M.SS la :=
  Finset.sum_induction f (fun F => F ∈ M.SS la) (fun _ _ ha hb => ssAdd M ha hb) (ssZero M la) h

end Two

end GlobalTheory.TranslatesDet

namespace GlobalTheory.TranslatesDet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem detNeAt [Fintype U] [DecidableEq U] {la : Wt M.Ψ r} {u u0 : C → Frame M.Ψ r → ℂ}
    (hu : u ∈ M.SS la) {c0 : C} {x0 : Frame M.Ψ r} (hx0 : x0 ∈ M.dom) (hne : u c0 x0 ≠ 0)
    (hz : ∀ h : U, h ≠ 1 → M.pull h u c0 x0 = 0)
    (hrep : ∀ (g : U) (y : Frame M.Ψ r), u0 (g • c0) y = u (g • c0) y) (k : U) :
    ∃ x ∈ M.dom, M.detTr u0 (k • c0) x ≠ 0 := by
  refine ⟨lact (M.tr k c0) x0, trDom M k c0 hx0, ?_⟩
  have ht1 : M.tr 1 c0 ∈ (M.comp c0).Γ := by
    have h := M.tr_mul 1 1 c0
    simp only [mul_one, one_smul] at h
    have e : M.tr 1 c0 * (M.tr 1 c0 * M.tr 1 c0)⁻¹ = (M.tr 1 c0)⁻¹ := by group
    rw [e] at h
    exact inv_mem_iff.mp h
  have ha : M.pull 1 u c0 x0 ≠ 0 := by
    simp only [TwoLevels.pull, one_smul]
    rw [ssLact M hu c0 ht1 hx0]
    exact hne
  have entry : ∀ g : U, M.pull g u0 (k • c0) (lact (M.tr k c0) x0) = M.pull (g * k) u c0 x0 := by
    intro g
    have hzd : lact (M.tr g (k • c0)) (lact (M.tr k c0) x0) ∈ M.dom :=
      trDom M g (k • c0) (trDom M k c0 hx0)
    have e1 : lact (M.tr (g * k) c0) x0 =
        lact (M.tr (g * k) c0 * (M.tr g (k • c0) * M.tr k c0)⁻¹)
          (lact (M.tr g (k • c0)) (lact (M.tr k c0) x0)) := by
      rw [lactMul (M.tr g (k • c0)) (M.tr k c0) x0, lactMul, inv_mul_cancel_right]
    simp only [TwoLevels.pull]
    rw [e1, ← mul_smul, hrep (g * k)]
    exact (ssLact M hu ((g * k) • c0) (M.tr_mul g k c0) hzd).symm
  let σ : Equiv.Perm U := (Equiv.inv U).trans (Equiv.mulRight k⁻¹)
  have key : ∀ h h' : U, h * h' * k = 1 ↔ σ h = h' := by
    intro h h'
    show h * h' * k = 1 ↔ h⁻¹ * k⁻¹ = h'
    constructor
    · intro e
      have e2 : h⁻¹ * (h * h' * k) * k⁻¹ = h' := by group
      rw [e] at e2
      simpa using e2
    · intro e
      rw [← e]
      group
  have hmat : (Matrix.of fun h h' : U => M.pull (h * h') u0 (k • c0) (lact (M.tr k c0) x0)) =
      (M.pull 1 u c0 x0 • (1 : Matrix U U ℂ)).submatrix σ id := by
    ext h h'
    rw [Matrix.of_apply, entry, Matrix.submatrix_apply, id, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases e : h * h' * k = 1
    · rw [if_pos ((key h h').1 e), e, mul_one]
    · rw [if_neg (fun e' => e ((key h h').2 e')), mul_zero]
      exact hz _ e
  unfold TwoLevels.detTr
  rw [hmat, Matrix.det_permute, Matrix.det_smul, Matrix.det_one, mul_one]
  refine mul_ne_zero ?_ (pow_ne_zero _ ha)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem independentTranslates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    IndependentTranslates E := by
  intro E _ _ _ r U C _ _ _ _ _ M hL s hs hsle
  classical
  have hB : ∀ c : C, ∃ x ∈ (M.comp c).dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction (M.comp c) x := fun c => by
    obtain ⟨x, hx, h1, -⟩ := GlobalTheory.T.existsBalancedFrameCMUnitary_proof E r (M.comp c)
    exact ⟨x, hx, h1⟩
  choose xb hxb hnc using hB
  have hI : ∀ c : C, ∃ u ∈ M.SS (deMul M.Ψ r M.p0 s), u c (castFrame (M.comp_Ψ c) (xb c)) ≠ 0 ∧
      (∀ h : U, h ≠ 1 → M.pull h u c (castFrame (M.comp_Ψ c) (xb c)) = 0) ∧
      ∀ c', (∀ h : U, h • c ≠ c') → ∀ y, u c' y = 0 := fun c =>
    GlobalTheory.T.exists_cuspForm_nonzero_at_one_lift E r U C M hL s hs hsle c _ (hnc c) (domOfComp M c (hxb c))
  choose uc huS hu0 hu1 hu2 using hI
  haveI : Fintype (Quotient (MulAction.orbitRel U C)) := Fintype.ofFinite _
  have hsum : ∀ c' y, (∑ q : Quotient (MulAction.orbitRel U C), uc q.out) c' y =
      uc (Quotient.mk (MulAction.orbitRel U C) c').out c' y := by
    intro c' y
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_eq_single (Quotient.mk (MulAction.orbitRel U C) c') (fun q _ hq => ?_)
      (fun h => absurd (Finset.mem_univ _) h)
    refine hu2 q.out c' (fun h hh => hq ?_) y
    have e : (Quotient.mk (MulAction.orbitRel U C) q.out) = Quotient.mk (MulAction.orbitRel U C) c' :=
      Quotient.sound (MulAction.orbitRel_apply.2 ⟨h⁻¹, by show h⁻¹ • c' = q.out; rw [← hh, inv_smul_smul]⟩)
    rwa [Quotient.out_eq] at e
  have hrep : ∀ (q : Quotient (MulAction.orbitRel U C)) (g : U) (y : Frame M.Ψ r),
      (∑ q' : Quotient (MulAction.orbitRel U C), uc q'.out) (g • q.out) y = uc q.out (g • q.out) y := by
    intro q g y
    rw [hsum]
    have e : Quotient.mk (MulAction.orbitRel U C) (g • q.out) = q :=
      (Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, rfl⟩)).trans (Quotient.out_eq q)
    rw [e]
  refine ⟨∑ q : Quotient (MulAction.orbitRel U C), uc q.out,
    ssSum M _ _ (fun q _ => huS q.out), fun c => ?_⟩
  obtain ⟨m, hm⟩ : (Quotient.mk (MulAction.orbitRel U C) c).out ∈ MulAction.orbit U c :=
    MulAction.orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel U C) c)))
  have hk : m⁻¹ • (Quotient.mk (MulAction.orbitRel U C) c).out = c := by
    rw [← hm, inv_smul_smul]
  rw [← hk]
  exact detNeAt M (huS _) (domOfComp M _ (hxb _)) (hu0 _) (hu1 _) (hrep _) m⁻¹

end GlobalTheory.TranslatesDet
