import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormExistsFreeDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormRingActionSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSeparatesEmbeddingsAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodsAlgebraicNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodTranscendenceRelationStatement

set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMEigen

theorem polForm_bc {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply Limits.pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

theorem corr_inj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} (hσ : Function.Injective σ)
    {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {b : Sp R' ⟶ Sp R} {q : A'.left ⟶ A.left}
    {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b q} {x y : HdR A} {x' : HdR A'}
    (hx : m.Corr x x') (hy : m.Corr y x') : x = y :=
  LinearMap.ext fun c ↦ hσ ((hx c).symm.trans (hy c))

theorem corr_smul {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {b : Sp R' ⟶ Sp R} {q : A'.left ⟶ A.left}
    {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b q} {x : HdR A} {x' : HdR A'}
    (hx : m.Corr x x') (r : R) : m.Corr (r • x) (σ r • x') := fun c ↦ by
  simp only [LinearMap.smul_apply, smul_eq_mul, hx c, map_mul]

theorem isAlg_emb {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) (x : E) : τ x ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic x).algHom τ.toRatAlgHom

set_option maxHeartbeats 1000000 in

theorem eigen_ops : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (U : Unif φ L 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ), IsCMType φ →
    X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧ a i ≠ 0) →
    (∀ b : E, (∀ x ∈ L, b * x ∈ L) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
      ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
    (∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left) →
    ∃ (N : I → Module.End Qb (HdR X₀.A))
      (m : GrpMor (dp0 Qb) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap Qb ℂ) (spMap (algebraMap Qb ℂ)) p)
      (ψ : LinearMap.BilinForm ℂ (HdR X.A)) (yv : I → HdR X.A) (w : I → ℂ),
      IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ ∧ admitted X₀ N ∧
      ∀ i, U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧ IsAlgebraic ℚ (w i / a i) ∧
        ∀ x₀ x, m.Corr x₀ x → m.Corr (N i x₀) ((ψ.flip (yv i)).smulRight (yv i) x) := by
  intro hPC hDR hDC E _ _ _ I _ φ L 𝔠 X₀ X p U v₀ v a hφ hp hv hex hdesc
  obtain ⟨y₀, yv, w, hy⟩ := GlobalTheory.T.cm_period_transcendence_relation hPC hDR hDC E I φ L 𝔠 X₀ X p U v₀ v a hp hφ hv hex hdesc
  have m := GlobalTheory.Published.AbelianDeRham.bcMor hp.grp
  have hne : ∀ i, y₀ i ≠ 0 := fun i ↦ (hy i).1
  replace hy : ∀ i, m.Corr (y₀ i) (yv i) ∧ U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧ IsAlgebraic ℚ (w i / a i) :=
    fun i ↦ (hy i).2
  have hσ : Function.Injective (algebraMap Qb ℂ) := Subtype.val_injective
  obtain ⟨ψ₀, hψ₀⟩ := GlobalTheory.T.polarization_form_exists_free_de_rham hDR.1 X₀ U.c
  obtain ⟨ψ, hψ, hψc⟩ := polForm_bc (algebraMap Qb ℂ) hp m U.c hψ₀

  have eig : ∀ i (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
      act (dp0 Qb) (𝟙 _) X₀.rm b (y₀ i) = β • y₀ i := by
    intro i b β hβ
    haveI := X₀.rm.hom b
    haveI := X.rm.hom b
    have h1 : m.Corr (act (dp0 Qb) (𝟙 _) X₀.rm b (y₀ i)) (push (dp0 ℂ) (𝟙 _) (X.rm.act b) (yv i)) := by
      rw [act_apply]
      exact GrpMor.Corr.push (m := m) m (X₀.rm.act b) (X.rm.act b) (hp.act b).symm (hy i).1
    have h2 : push (dp0 ℂ) (𝟙 _) (X.rm.act b) (yv i) = algebraMap Qb ℂ β • yv i := by
      rw [hβ]
      exact (hy i).2.1.1 _ (X.rm.act b) fun w' ↦ U.act b w'
    rw [h2] at h1
    exact corr_inj hσ h1 (corr_smul (hy i).1 β)
  have eigβ : ∀ i (b : 𝓞 (FR E)), ∃ β : Qb, algebraMap Qb ℂ β = φ i ((b : FR E) : E) := fun i b ↦
    ⟨⟨_, isAlg_emb (φ i) _⟩, rfl⟩

  have orth : ∀ (c : 𝔠.elt) (ψ' : LinearMap.BilinForm Qb (HdR X₀.A)),
      IsPolForm (dp0 Qb) (𝟙 _) X₀.A (X₀.diag c) ψ' → ∀ i j, ψ' (y₀ i) (y₀ j) = 0 := by
    intro c ψ' hψ' i j
    by_cases hij : i = j
    · subst hij; exact hψ'.isAlt _
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_ne_of_isCMType_of_ne φ hφ i j hij
    obtain ⟨βi, hβi⟩ := eigβ i b
    obtain ⟨βj, hβj⟩ := eigβ j b
    have := GlobalTheory.T.polarization_form_ring_action_symmetric hDR hDC X₀ c ψ' hψ' b (y₀ i) (y₀ j)
    rw [eig i b βi hβi, eig j b βj hβj, LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul] at this
    have hne' : βi ≠ βj := fun e ↦ hb (by rw [← hβi, ← hβj, e])
    have : (βi - βj) * ψ' (y₀ i) (y₀ j) = 0 := by rw [sub_mul, this, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')
  let N : I → Module.End Qb (HdR X₀.A) := fun i ↦ (ψ₀.flip (y₀ i)).smulRight (y₀ i)
  have hN : ∀ i x, N i x = ψ₀ x (y₀ i) • y₀ i := fun _ _ ↦ rfl
  refine ⟨N, m, ψ, yv, w, hψ, ⟨?_, ?_, ?_⟩, fun i ↦ ⟨(hy i).2.1, (hy i).2.2.1, (hy i).2.2.2, ?_⟩⟩
  · intro i b
    obtain ⟨β, hβ⟩ := eigβ i b
    refine LinearMap.ext fun x ↦ ?_
    change N i (act (dp0 Qb) (𝟙 _) X₀.rm b x) = act (dp0 Qb) (𝟙 _) X₀.rm b (N i x)
    rw [hN, hN, GlobalTheory.T.polarization_form_ring_action_symmetric hDR hDC X₀ U.c ψ₀ hψ₀, eig i b β hβ, LinearMap.map_smul, map_smul, eig i b β hβ, smul_smul,
      smul_eq_mul, mul_comm]
  · intro i j
    refine LinearMap.ext fun x ↦ ?_
    change N i (N j x) = 0
    rw [hN, hN, LinearMap.map_smul₂, orth U.c ψ₀ hψ₀ j i, smul_zero, zero_smul]
  · intro c ψ' hψ'
    refine ⟨fun i x y ↦ ?_, fun i j x y ↦ ?_⟩
    · rw [hN, hN, LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
      have h0 : (ψ₀ (y₀ i)) (y₀ i) = 0 := hψ₀.isAlt (y₀ i)
      have h0' : (ψ' (y₀ i)) (y₀ i) = 0 := hψ'.isAlt (y₀ i)
      have hr := GlobalTheory.T.cm_periods_algebraic_nonzero hPC hDR E I φ L 𝔠 X₀ X p U hφ hp i (y₀ i) (hne i) (eig i) (ψ₀ (y₀ i)) (ψ' (y₀ i))
        h0 h0' (fun b β hβ z ↦ ⟨by
          rw [← GlobalTheory.T.polarization_form_ring_action_symmetric hDR hDC X₀ U.c ψ₀ hψ₀, eig i b β hβ, LinearMap.map_smul₂, smul_eq_mul], by
          rw [← GlobalTheory.T.polarization_form_ring_action_symmetric hDR hDC X₀ c ψ' hψ', eig i b β hβ, LinearMap.map_smul₂, smul_eq_mul]⟩) x y
      have a1 : ψ₀ x (y₀ i) = - ψ₀ (y₀ i) x := (LinearMap.IsAlt.neg hψ₀.isAlt (y₀ i) x).symm
      have a2 : ψ₀ y (y₀ i) = - ψ₀ (y₀ i) y := (LinearMap.IsAlt.neg hψ₀.isAlt (y₀ i) y).symm
      have a3 : ψ' x (y₀ i) = - ψ' (y₀ i) x := (LinearMap.IsAlt.neg hψ'.isAlt (y₀ i) x).symm
      rw [a1, a2, a3]
      linear_combination -hr
    · rw [hN, hN, LinearMap.map_smul₂, LinearMap.map_smul, orth c ψ' hψ' i j]
      simp
  · intro x₀ x hx
    have h1 := corr_smul (m := m) (hy i).1 (ψ₀ x₀ (y₀ i))
    rw [← hψc x₀ x (y₀ i) (yv i) hx (hy i).1] at h1
    exact h1

end GlobalTheory.CMEigen
