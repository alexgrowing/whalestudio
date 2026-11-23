import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedProjectionPreservesSchwartzAdmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartialEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxProductDiagonalFunctionalNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormUnramifiedFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MixedForm

section Abstract

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem siegel_conj {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    {d : Darboux (symp c ξ JA JB) κ} {χ : Eˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν] {Cy : Matrix β ν E}
    {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)} (hs : IsSplitting C ψ d (actB c) om)
    (h : SiegelRule c C ψ ξ JA JB d χ Cy om) (γ : UG c JB) :
    SiegelRule c C ψ ξ JA JB d χ (((γ : GL β E) : Matrix β β E) * Cy) om := by
  intro l hl hinv p t hp φ hφ
  have h1 := h (l ∘ₗ om γ) (hs.adm γ l hl) (fun z φ hφ => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs.impl γ _ φ hφ, ← hinv z _ (hs.pres γ φ hφ)]
    simp only [actB, Matrix.transpose_mul, Matrix.mul_assoc]) (γ⁻¹ * p * γ) t (by
      have e : (((γ⁻¹ : UG c JB) : GL β E) : Matrix β β E) * ((γ : GL β E) : Matrix β β E) = 1 := Units.inv_mul _
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
      rw [hp, Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.one_mul]) (om γ⁻¹ φ) (hs.pres _ φ hφ)
  simp only [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul] at h1
  simpa [mul_assoc] using h1

theorem schr_add (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (w w' : (κ → R) × (κ → R)) (h1 : w.1 ⬝ᵥ w'.2 = 0)
    (h2 : w'.1 ⬝ᵥ w.2 = 0) (Φ : (κ → R) → ℂ) : schr ψ (w + w') Φ = schr ψ w (schr ψ w' Φ) := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add, h1, h2, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  ring

theorem tensForm_schr [TopologicalSpace R] [T2Space R] (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ] [Fintype κ']
    (l₁ : ((κ → R) → ℂ) →ₗ[ℂ] ℂ) (l₂ : ((κ' → R) → ℂ) →ₗ[ℂ] ℂ) (p₁ q₁ : κ → R) (p₂ q₂ : κ' → R)
    (h₁ : ∀ φ ∈ SB (κ → R), l₁ (schr ψ (p₁, q₁) φ) = l₁ φ) (h₂ : ∀ φ ∈ SB (κ' → R), l₂ (schr ψ (p₂, q₂) φ) = l₂ φ)
    (f : (κ ⊕ κ' → R) → ℂ) (hf : f ∈ SB (κ ⊕ κ' → R)) :
    tensForm l₁ l₂ (schr ψ (Sum.elim p₁ p₂, Sum.elim q₁ q₂) f) = tensForm l₁ l₂ f := by
  obtain ⟨s1, s2⟩ := GlobalTheory.T.schwartz_bruhat_partial_evaluation R κ κ' f hf
  change l₁ _ = l₁ _
  rw [← h₁ _ (s2 l₂)]
  congr 1
  funext x₁
  have e : (fun x₂ => schr ψ (Sum.elim p₁ p₂, Sum.elim q₁ q₂) f (Sum.elim x₁ x₂)) =
      ψ (x₁ ⬝ᵥ q₁ + ⅟(2 : R) * (p₁ ⬝ᵥ q₁)) • schr ψ (p₂, q₂) (fun x₂ => f (Sum.elim (x₁ + p₁) x₂)) := by
    funext x₂
    have e1 : Sum.elim x₁ x₂ + Sum.elim p₁ p₂ = Sum.elim (x₁ + p₁) (x₂ + p₂) := by funext i; cases i <;> rfl
    simp only [schr, Pi.smul_apply, smul_eq_mul, e1, sumElim_dotProduct_sumElim, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [e, map_smul, h₂ _ (s1 _)]
  rfl

end Abstract

section Proj

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem liftV_mul (v : Pl F) (a : Fv F v) (y : AF F) : liftV v a * y = liftV v (a * evFin F v y) :=
  GlobalTheory.EmbChart.atPlace_mul_right v a y

theorem mul_liftV (v : Pl F) (a : Fv F v) (y : AF F) : y * liftV v a = liftV v (evFin F v y * a) := by
  rw [mul_comm, liftV_mul, mul_comm]

theorem proj_schr_off (ψ : AddChar (AF F) ℂ) (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (p q : κ → AF F) (hp : ∀ i, evFin F v (p i) = 0) (hq : ∀ i, evFin F v (q i) = 0) (Φ : (κ → AF F) → ℂ) :
    proj v φ₀ l (schr ψ (p, q) Φ) = schr ψ (p, q) (proj v φ₀ l Φ) := by
  funext y
  have e : (fun x => schr ψ (p, q) Φ (repl v y x)) =
      ψ (y ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q)) • fun x => Φ (repl v (y + p) x) := by
    funext x
    have e1 : repl v y x ⬝ᵥ q = y ⬝ᵥ q := by
      simp only [dotProduct, repl, add_mul, sub_mul, liftV_mul, hq, mul_zero, map_zero, sub_zero, add_zero]
    have e2 : repl v y x + p = repl v (y + p) x := by
      funext i; simp only [repl, Pi.add_apply, map_add, hp, add_zero]; ring
    simp only [schr, e1, e2, Pi.smul_apply, smul_eq_mul]
  rw [proj_apply, e, map_smul]
  simp only [schr, proj_apply, Pi.add_apply, map_add, hp, add_zero, smul_eq_mul]
  ring

theorem proj_schr_at (ψ : AddChar (AF F) ℂ) (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (p q : κ → Fv F v) (h : ∀ φ ∈ SB (κ → Fv F v), l (schr (psiAt ψ v) (p, q) φ) = l φ) (Φ : (κ → AF F) → ℂ)
    (hΦ : Φ ∈ schA F κ) :
    proj v φ₀ l (schr ψ (fun i => liftV v (p i), fun i => liftV v (q i)) Φ) = proj v φ₀ l Φ := by
  funext y
  have hs : (fun x => Φ (repl v y x)) ∈ SB (κ → Fv F v) := by
    have := restrict_liftV_mem_SB v _ (GlobalTheory.SchwartzTranslation.schA_add_const (fun i => y i - liftV v (evFin F v (y i))) Φ hΦ)
    convert this using 3
    funext i
    simp only [repl, Pi.add_apply]; ring
  have e : (fun x => schr ψ (fun i => liftV v (p i), fun i => liftV v (q i)) Φ (repl v y x)) =
      schr (psiAt ψ v) (p, q) fun x => Φ (repl v y x) := by
    funext x
    have e2 : (repl v y x + fun i => liftV v (p i)) = repl v y (x + p) := by
      funext i; simp only [repl, Pi.add_apply, map_add]; ring
    have e1 : (repl v y x ⬝ᵥ fun i => liftV v (q i)) +
        ⅟(2 : AF F) * ((fun i => liftV v (p i)) ⬝ᵥ fun i => liftV v (q i)) =
        liftV v (x ⬝ᵥ q + ⅟(2 : Fv F v) * (p ⬝ᵥ q)) := by
      simp only [dotProduct, mul_liftV, evFin_repl, evFin_liftV, ← map_sum, GlobalTheory.VacAny.evFin_invOf_two, map_add]
    simp only [schr, e1, e2]
    rfl
  rw [proj_apply, proj_apply, e, h _ hs]

theorem mixed_inv (ψ : AddChar (AF F) ℂ) (v : Pl F) (φ₀ : (κ ⊕ κ → Fv F v) → ℂ) (hφ₀ : φ₀ ∈ SB (κ ⊕ κ → Fv F v))
    (l₁ l₂ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (p₁ q₁ p₂ q₂ : κ → AF F)
    (hp : (1 - liftV v 1) • p₁ = (1 - liftV v 1) • p₂) (hq : (1 - liftV v 1) • q₁ = (1 - liftV v 1) • q₂)
    (h₁ : ∀ φ ∈ SB (κ → Fv F v), l₁ (schr (psiAt ψ v) (fun i => evFin F v (p₁ i), fun i => evFin F v (q₁ i)) φ) = l₁ φ)
    (h₂ : ∀ φ ∈ SB (κ → Fv F v), l₂ (schr (psiAt ψ v) (fun i => evFin F v (p₂ i), -fun i => evFin F v (q₂ i)) φ) = l₂ φ)
    (Φ : (κ ⊕ κ → AF F) → ℂ) (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    (GlobalTheory.DiagForm.lDiag F κ ∘ₗ proj v φ₀ (tensForm l₁ l₂)) (schr ψ (Sum.elim p₁ p₂, Sum.elim q₁ (-q₂)) Φ) =
      (GlobalTheory.DiagForm.lDiag F κ ∘ₗ proj v φ₀ (tensForm l₁ l₂)) Φ := by
  set u : AF F := 1 - liftV v 1 with hu
  have hu0 : evFin F v u = 0 := by simp [hu, evFin_liftV]
  have hd : ∀ a : AF F, a = u * a + liftV v (evFin F v a) := fun a => by
    rw [hu, sub_mul, liftV_mul, one_mul, one_mul, sub_add_cancel]
  set P : κ ⊕ κ → Fv F v := Sum.elim (fun i => evFin F v (p₁ i)) (fun i => evFin F v (p₂ i))
  set Q : κ ⊕ κ → Fv F v := Sum.elim (fun i => evFin F v (q₁ i)) (-fun i => evFin F v (q₂ i))
  have e : ((Sum.elim p₁ p₂, Sum.elim q₁ (-q₂)) : (κ ⊕ κ → AF F) × (κ ⊕ κ → AF F)) =
      (Sum.elim (u • p₁) (u • p₁), Sum.elim (u • q₁) (-(u • q₁))) + (fun i => liftV v (P i), fun i => liftV v (Q i)) := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · cases i with
      | inl i => exact hd _
      | inr i => rw [hp]; exact hd _
    · cases i with
      | inl i => exact hd _
      | inr i =>
        rw [hq]
        change -q₂ i = -(u * q₂ i) + liftV v (-evFin F v (q₂ i))
        rw [map_neg, ← neg_add, ← hd]
  have o1 : ∀ i, evFin F v (Sum.elim (u • p₁) (u • p₁) i) = 0 := fun i => by cases i <;> simp [hu0]
  have o2 : ∀ i, evFin F v (Sum.elim (u • q₁) (-(u • q₁)) i) = 0 := fun i => by cases i <;> simp [hu0]
  rw [e, schr_add ψ _ _ (by simp only [dotProduct, mul_liftV, o1, zero_mul, map_zero, Finset.sum_const_zero])
    (by simp only [dotProduct, liftV_mul, o2, mul_zero, map_zero, Finset.sum_const_zero]),
    LinearMap.comp_apply, LinearMap.comp_apply, proj_schr_off ψ v _ _ _ _ o1 o2,
    proj_schr_at ψ v _ _ P Q (tensForm_schr _ l₁ l₂ _ _ _ _ h₁ h₂) Φ hΦ]
  exact GlobalTheory.DiagForm.lDiag_schr ψ _ _ ((GlobalTheory.T.mixed_projection_preserves_schwartz_adm F _ v φ₀ hφ₀ _).1 Φ hΦ)

end Proj

section Mixed

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Invertible (2 : R)] [Fintype β] in
theorem smul_one_map (a : E) : (a • (1 : Matrix β β E)).map c = c a • 1 := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

omit [Invertible (2 : R)] in

theorem exists_shear (J : Matrix β β E) (ε : E) (h2 : ε * c ε = 0) (h3 : c (c ε) = ε) : ∃ γ : UG c (dbl J),
    ((γ : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks 1 ((-ε) • 1) ((-c ε) • 1) 1 := by
  have h2' : c ε * ε = 0 := by rw [mul_comm, h2]
  refine ⟨⟨⟨Matrix.fromBlocks 1 ((-ε) • 1) ((-c ε) • 1) 1, Matrix.fromBlocks 1 (ε • 1) (c ε • 1) 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · simp [Matrix.fromBlocks_multiply, smul_smul, h2, h2']
  · simp [Matrix.fromBlocks_multiply, smul_smul, h2, h2']
  · change (Matrix.fromBlocks 1 ((-ε) • 1) ((-c ε) • 1) 1)ᵀ * dbl J *
      (Matrix.fromBlocks 1 ((-ε) • 1) ((-c ε) • 1) 1).map c = dbl J
    rw [Matrix.fromBlocks_map, smul_one_map, smul_one_map, Matrix.map_one _ (map_zero c) (map_one c), map_neg, map_neg, h3]
    simp [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, smul_smul, h2, h2']

omit [Invertible (2 : R)] in

theorem exists_inl (J : Matrix β β E) (g : UG c J) : ∃ gd : UG c (dbl J),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  refine ⟨⟨⟨Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1,
    Matrix.fromBlocks (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · simp [Matrix.fromBlocks_multiply]
  · simp [Matrix.fromBlocks_multiply]
  · have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
    change (Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J *
      (Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1).map c = dbl J
    rw [Matrix.fromBlocks_map, Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_zero _ (map_zero c)]
    simp [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hg]

theorem exists_part (e : E) (he : e * e = e) (g : GL β E) : ∃ t : GL β E, (t : Matrix β β E) = 1 + e • ((g : Matrix β β E) - 1) := by
  have key : ∀ a b : Matrix β β E, a * b = 1 → (1 + e • (a - 1)) * (1 + e • (b - 1)) = 1 := fun a b hab => by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      he, Matrix.sub_mul, Matrix.mul_sub, hab, smul_add, smul_sub]
    abel
  exact ⟨⟨_, _, key _ _ g.mul_inv, key _ _ g.inv_mul⟩, rfl⟩

theorem siegel_mixed {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    {d : Darboux (symp c ξ JA JB) κ} {χ : Eˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsWeilB c C ψ ξ JA JB d χ om) (ε : E) (h1 : ε * ε = ε) (h2 : ε * c ε = 0) (h3 : c (c ε) = ε)
    (l : ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ C.adm (κ ⊕ κ))
    (hinv : ∀ z : Matrix α β E, ∀ Φ ∈ C.sp (κ ⊕ κ), l (schr ψ (Sum.elim (d.e ((1 - ε) • z)).1 (d.e ((1 - c ε) • z)).1,
      Sum.elim (d.e ((1 - ε) • z)).2 (-(d.e ((1 - c ε) • z)).2)) Φ) = l Φ)
    (g : UG c JB) (hg : (1 - ε - c ε) • (((g : GL β E) : Matrix β β E) - 1) = 0) (t : GL β E)
    (ht : (t : Matrix β β E) = 1 + c ε • (((g : GL β E) : Matrix β β E) - 1))
    (φ₁ φ₂ : (κ → R) → ℂ) (hφ₁ : φ₁ ∈ C.sp κ) (hφ₂ : φ₂ ∈ C.sp κ) (hb : boxFun φ₁ φ₂ ∈ C.sp (κ ⊕ κ)) :
    l (boxFun (om g φ₁) φ₂) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        (((C.modu (Units.map (Algebra.norm R : E →* R) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^
          ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) * l (boxFun φ₁ φ₂) := by
  obtain ⟨-, dd, omd, hdd, hs, hS, hres⟩ := h
  obtain ⟨γ, hγ⟩ := exists_shear JB ε h2 h3
  obtain ⟨gd, hgd⟩ := exists_inl JB g
  have h4 : c ε * c ε = c ε := by rw [← map_mul, h1]
  have hC : ((γ : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) * (diagCols β : Matrix (β ⊕ β) β E) =
      Matrix.fromRows ((1 - ε) • (1 : Matrix β β E)) ((1 - c ε) • (1 : Matrix β β E)) := by
    rw [hγ, diagCols, Matrix.fromBlocks_mul_fromRows]
    congr 1
    · simp [sub_smul, sub_eq_add_neg, add_smul]
    · simp [sub_smul, sub_eq_add_neg, add_smul, add_comm]
  rw [← hres g gd hgd φ₁ hφ₁ φ₂ hφ₂]
  refine siegel_conj hs hS γ l hl (fun z Φ hΦ => ?_) gd t ?_ _ hb
  · rw [← hinv z Φ hΦ, hC, Matrix.transpose_fromRows, Matrix.mul_fromCols, Darboux.rho, hdd]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one]
  · rw [hC, hgd, ht, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
    set G : Matrix β β E := ((g : GL β E) : Matrix β β E)
    congr 1
    · simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, smul_zero, add_zero,
        smul_add, smul_smul]
      have e : (1 - ε) * c ε = c ε := by rw [sub_mul, one_mul, h2, sub_zero]
      rw [e, ← sub_eq_zero, ← hg]
      module
    · simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, smul_zero, zero_add,
        smul_add, smul_smul]
      have e : (1 - c ε) * c ε = 0 := by rw [sub_mul, one_mul, h4, sub_self]
      rw [e, zero_smul, add_zero]

end Mixed

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

omit [NumberField E] in
theorem piW_algebraMap (τ : E →ₐ[F] Fv F v) (a : AF F) : piW τ (algebraMap (AF F) (AE F E) a) = evFin F v a := by
  change evFin F v a * τ 1 = _
  rw [map_one, mul_one]

theorem exists_idem (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) : ∃ ε : AE F E, ε * ε = ε ∧ ε * cA σ ε = 0 ∧
    cA σ (cA σ ε) = ε ∧ ε + cA σ ε = algebraMap (AF F) (AE F E) (liftV v 1) ∧ piW t ε = 1 ∧ piW t (cA σ ε) = 0 ∧
    piW (t.comp σ) (cA σ ε) = 1 := by
  have hc : cA σ (GlobalTheory.EmbChart.tensAt E v (splitIdem h t)) = GlobalTheory.EmbChart.tensAt E v (1 - splitIdem h t) :=
    (GlobalTheory.EmbChart.sigR_tensAt v σ _).trans (congrArg _ (sigR_splitIdem h t))
  have hp : ∀ (τ : E →ₐ[F] Fv F v) y, piW τ (GlobalTheory.EmbChart.tensAt E v y) = splitProj τ y := fun τ y =>
    congrArg (splitProj τ) (GlobalTheory.EmbChart.compFin_tensAt v y)
  refine ⟨GlobalTheory.EmbChart.tensAt E v (splitIdem h t), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [GlobalTheory.EmbChart.tensAt_mul_right, GlobalTheory.EmbChart.compFin_tensAt, splitIdem_mul_self]
  · rw [hc, GlobalTheory.EmbChart.tensAt_mul_right, GlobalTheory.EmbChart.compFin_tensAt, mul_sub, mul_one, splitIdem_mul_self, sub_self,
      map_zero]
  · rw [hc]
    refine (GlobalTheory.EmbChart.sigR_tensAt v σ _).trans (congrArg _ ?_)
    rw [map_sub, map_one, sigR_splitIdem, sub_sub_cancel]
  · rw [hc, ← map_add, add_sub_cancel]; rfl
  · rw [hp, splitProj_splitIdem]
  · rw [hc, hp, map_sub, map_one, splitProj_splitIdem, sub_self]
  · rw [hc, hp, map_sub, map_one, splitProj_comp_splitIdem, sub_zero]

omit [NumberField E] in

theorem at_det {n : ℕ} (T : Matrix (Fin n) (Fin n) (AE F E)) (hT : At (evFin F v) (T - 1)) : At (evFin F v) (T.det - 1) := by
  intro u hu
  let I : Ideal (AE F E) := LinearMap.ker (LinearMap.lsmul (AE F E) (AE F E) (algebraMap (AF F) (AE F E) u))
  have hI : ∀ x, x ∈ I ↔ u • x = 0 := fun x => by
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply, algebraMap_smul]
  have h1 : (Ideal.Quotient.mk I).mapMatrix T = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 ((hI _).2 (congrFun (congrFun (hT u hu) i) j))
  rw [← hI, ← Ideal.Quotient.eq, RingHom.map_det, h1, map_one, map_one, Matrix.det_one]

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem form_scalar (h : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W)
    (hW : M.IsWeil ψ χX χW om) (t : E →ₐ[F] Fv F v) (l₁ l₂ : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (h₁ : ∀ w : Matrix (Fin n) (Fin d) (AE F E), w.map (piW t) = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      l₁ (schr (psiAt ψ v) (locCo M.co v w) φ) = l₁ φ)
    (h₂ : ∀ w : Matrix (Fin n) (Fin d) (AE F E), w.map (piW (t.comp σ)) = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      l₂ (schr (psiAt ψ v) ((locCo M.co v w).1, -(locCo M.co v w).2) φ) = l₂ φ)
    (φ₂ : (Fin n × Fin d → Fv F v) → ℂ) (hφ₂ : φ₂ ∈ SB (Fin n × Fin d → Fv F v)) (hne : l₂ φ₂ ≠ 0)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) (y : (Fv F v)ˣ) (hy : (y : Fv F v) = ((mat g).map (piW (t.comp σ))).det)
    (φ φ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hA : Acts (evFin F v) (om (g, 1)) φ φ₁) :
    l₁ φ₁ = (chrW χW (t.comp σ) y : ℂ) * ((GlobalTheory.SplitWeil.nabs (Fv F v) y ^ ((d : ℝ) / 2) : ℝ) : ℂ) * l₁ φ := by
  obtain ⟨-, ⟨d', hd', hB⟩, -⟩ := hW
  obtain ⟨ε, e1, e2, e3, e4, e5, e6, e7⟩ := exists_idem h t
  have e8 : piW (t.comp σ) ε = 0 := by simpa [e7] using congrArg (piW (t.comp σ)) e2
  obtain ⟨φ₀, hφ₀, hb₀, R, R', hR, hL⟩ := GlobalTheory.T.box_product_diagonal_functional_ne_zero F (Fin n × Fin d) v
  set u : AF F := 1 - liftV v 1 with hu
  have hu0 : evFin F v u = 0 := by simp [hu, evFin_liftV]
  have huA : algebraMap (AF F) (AE F E) u = 1 - ε - cA σ ε := by rw [hu, map_sub, map_one, ← e4]; ring
  have h4 : cA σ ε * cA σ ε = cA σ ε := by rw [← map_mul, e1]
  obtain ⟨T, hT⟩ := exists_part (cA σ ε) h4 (g : GL (Fin n) (AE F E))
  have hgu : (1 - ε - cA σ ε) • (mat g - 1) = 0 := by rw [← huA, algebraMap_smul]; exact hg u hu0
  have hbox : ∀ a b : (Fin n × Fin d → Fv F v) → ℂ, boxFun (tens (evFin F v) a R) (tens (evFin F v) b R') =
      tens (evFin F v) (boxFun a b) (boxFun R R') := fun a b => by
    funext x; simp only [boxFun, tens, Function.comp_def]; ring
  have hRR : ∀ x z, At (evFin F v) z → boxFun R R' (x + z) = boxFun R R' x := fun x z hz => by
    have a1 := (hR φ hφ).1.1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
    have a2 := (hR φ hφ).2.1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
    exact congrArg₂ (· * ·) a1 a2
  have key := siegel_mixed hB.isWeilB ε e1 e2 e3
    (GlobalTheory.DiagForm.lDiag F (Fin n × Fin d) ∘ₗ proj v (boxFun φ₀ φ₀) (tensForm l₁ l₂))
    ((GlobalTheory.T.mixed_projection_preserves_schwartz_adm F _ v _ hb₀ _).2 _ GlobalTheory.DiagForm.lDiag_adm) (fun z Φ hΦ => by
      have hz : u • ((1 - ε) • z) = u • ((1 - cA σ ε) • z) := by
        rw [← algebraMap_smul (AE F E) u, ← algebraMap_smul (AE F E) u, smul_smul, smul_smul, huA]
        congr 1
        linear_combination e1 - h4
      have hz' : u • d'.e ((1 - ε) • z) = u • d'.e ((1 - cA σ ε) • z) :=
        (d'.e.map_smul u _).symm.trans ((congrArg d'.e hz).trans (d'.e.map_smul u _))
      have hz1 : u • (d'.e ((1 - ε) • z)).1 = u • (d'.e ((1 - cA σ ε) • z)).1 := congrArg Prod.fst hz'
      have hz2 : u • (d'.e ((1 - ε) • z)).2 = u • (d'.e ((1 - cA σ ε) • z)).2 := congrArg Prod.snd hz'
      refine mixed_inv ψ v _ hb₀ l₁ l₂ _ _ _ _ hz1 hz2 ?_ ?_ Φ hΦ
      · rw [← Matrix.transpose_transpose ((1 - ε) • z), hd']
        refine h₁ _ ?_
        ext i j; simp [e5]
      · rw [← Matrix.transpose_transpose ((1 - cA σ ε) • z), hd']
        refine h₂ _ ?_
        ext i j; simp [e7])
    g hgu T hT _ _ (hR φ hφ).1.2 (hR φ₂ hφ₂).2.2 (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ (hR φ hφ).1.2 _ (hR φ₂ hφ₂).2.2)
  have hom : (om.comp (MonoidHom.inl _ _)) g (tens (evFin F v) φ R) = tens (evFin F v) φ₁ R := hA R (hR φ hφ).1
  rw [hom, hbox, hbox, LinearMap.comp_apply, LinearMap.comp_apply, proj_tens _ _ _ _ _ hRR, proj_tens _ _ _ _ _ hRR,
    tensForm_box, tensForm_box, map_smul, map_smul, ← hbox, smul_eq_mul, smul_eq_mul] at key
  set z : (AE F E)ˣ := Matrix.GeneralLinearGroup.det T with hzdef
  have hz : (z : AE F E) = (T : Matrix (Fin n) (Fin n) (AE F E)).det := rfl
  have z1 : At (evFin F v) ((z : AE F E) - 1) := at_det _ fun u hu => by
    rw [hT, add_sub_cancel_left, smul_comm]
    rw [show u • (((g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0 from hg u hu, smul_zero]
  have z2 : piW t (z : AE F E) = 1 := by
    have : (piW t).mapMatrix (T : Matrix (Fin n) (Fin n) (AE F E)) = (piW t).mapMatrix 1 := by
      rw [hT]; ext i j; simp [e6]
    rw [hz, RingHom.map_det, this, map_one, Matrix.det_one]
  have z3 : piW (t.comp σ) (z : AE F E) = y := by
    have : (piW (t.comp σ)).mapMatrix (T : Matrix (Fin n) (Fin n) (AE F E)) = (mat g).map (piW (t.comp σ)) := by
      rw [hT]; ext i j; simp [e7, mat]
    rw [hz, RingHom.map_det, this, hy]
  have c1 := GlobalTheory.T.local_character_norm_one_unit F E σ h χW v (t.comp σ) z z1 (by rw [comp_conj_conj h]; exact z2)
  rw [show Units.map (piW (t.comp σ)).toMonoidHom z = y from Units.ext z3] at c1
  obtain ⟨n1, n2⟩ := GlobalTheory.T.local_norm_unramified_factorization F E σ h v t z z1
  have c2 := GlobalTheory.T.distribHaarChar_supportedIdele_eq_localAbsValue F v (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) n1
  rw [show Units.map (evFin F v : AF F →* Fv F v) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) = y from
    Units.ext (by rw [← z3, ← one_mul (piW (t.comp σ) _), ← z2]; exact n2)] at c2
  rw [c1, ← c2]
  apply mul_right_cancel₀ hne
  apply mul_right_cancel₀ hL
  rw [key, Fintype.card_fin]
  simp only [mul_assoc]
  rfl

end Place

section Linear

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem exists_at (M : Model σ X W) (w : Matrix (Fin n) (Fin d) (AE F E)) : ∃ u : Matrix (Fin n) (Fin d) (AE F E),
    At (evFin F v) u ∧ locCo M.co v u = locCo M.co v w ∧ ∀ τ : E →ₐ[F] Fv F v, u.map (piW τ) = w.map (piW τ) := by
  refine ⟨liftV v 1 • w, fun a ha => ?_, ?_, fun τ => ?_⟩
  · rw [smul_smul, show a * liftV v 1 = 0 from at_liftV v 1 a ha, zero_smul]
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · change evFin F v ((M.co.e (liftV v 1 • w)).1 k) = evFin F v ((M.co.e w).1 k)
      rw [M.co.e.map_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, map_mul, evFin_liftV, one_mul]
    · change evFin F v ((M.co.e (liftV v 1 • w)).2 k) = evFin F v ((M.co.e w).2 k)
      rw [M.co.e.map_smul, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, evFin_liftV, one_mul]
  · ext i j
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.smul_apply, Algebra.smul_def, map_mul, piW_algebraMap, evFin_liftV, one_mul]

theorem star_mem_SB {Y : Type} [TopologicalSpace Y] {f : Y → ℂ} (hf : f ∈ SB Y) : star f ∈ SB Y :=
  ⟨hf.1.comp star, hf.2.comp_left (g := star) (star_zero ℂ)⟩

def conjForm {Y : Type} (l : (Y → ℂ) →ₗ[ℂ] ℂ) : (Y → ℂ) →ₗ[ℂ] ℂ where
  toFun f := star (l (star f))
  map_add' f g := by rw [star_add, map_add, star_add]
  map_smul' c f := by rw [star_smul, map_smul, star_smul, star_star]; rfl

theorem star_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) : star (schr ψ (w.1, -w.2) φ) = schr ψ w (star φ) := by
  funext x
  simp only [schr, Pi.star_apply, star_mul', dotProduct_neg, mul_neg, ← neg_add, AddChar.map_neg_eq_inv]
  rw [Complex.inv_eq_conj (hψ _), Complex.star_def, Complex.conj_conj]

theorem lin_zero (h : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (χX χW : Chr F E) (om : Rep σ X W)
    (hW : M.IsWeil ψ χX χW om) (t : E →ₐ[F] Fv F v)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW ψ t 1 1 ι)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) (y : (Fv F v)ˣ) (hy : (y : Fv F v) = ((mat g).map (piW (t.comp σ))).det)
    (φ φ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hA : Acts (evFin F v) (om (g, 1)) φ φ₁) :
    ι φ₁ 0 = (chrW χW (t.comp σ) y : ℂ) * ((GlobalTheory.SplitWeil.nabs (Fv F v) y ^ ((d : ℝ) / 2) : ℝ) : ℂ) * ι φ 0 := by
  obtain ⟨Λ, hΛ, f, hf, hne⟩ := GlobalTheory.T.exists_translation_invariant_functional F v n d
  obtain ⟨φ₂, hφ₂, rfl⟩ := hι.bij.surjOn hf
  refine form_scalar h M ψ χX χW om hW t (LinearMap.proj 0 ∘ₗ ι) (conjForm (Λ ∘ₗ ι)) (fun w hw φ hφ => ?_)
    (fun w hw φ hφ => ?_) (star φ₂) (star_mem_SB hφ₂) ?_ g hg y hy φ φ₁ hφ hA
  · obtain ⟨u, hu, e1, e2⟩ := exists_at (v := v) M w
    have := hι.mult u hu ((e2 t).trans hw) φ hφ _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ φ hφ)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu φ) 0 (fun a _ => smul_zero a) (Matrix.map_zero _ (map_zero _))
    rw [e1] at this
    simpa [symp, hTens] using this
  · obtain ⟨u, hu, e1, e2⟩ := exists_at (v := v) M w
    have := hι.trans u hu ((e2 _).trans hw) _ (star_mem_SB hφ) _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ _ (star_mem_SB hφ))
      (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu _)
    rw [e1] at this
    change star (Λ (ι _)) = star (Λ (ι _))
    rw [star_schr (psiAt ψ v) (fun x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _), funext this,
      hΛ _ (hι.bij.mapsTo (star_mem_SB hφ))]
  · change star (Λ (ι (star (star φ₂)))) ≠ 0
    rwa [star_star, star_ne_zero]

theorem chrW_div (α β : Chr F E) (τ : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : chrW (β / α) τ x = (chrW (α / β) τ x)⁻¹ := by
  rw [← inv_div α β]
  exact map_inv Circle.toUnits _

end Linear

theorem char_eq_local : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) →
    ∃ t' : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t' ∨ ν₀ = (chrW X.ν t')⁻¹ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v _ t ι hι ν₀ hν
  have h := hT.base.cm
  have hJ : IsUnit (G.V.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hT.geo.hV.sig (InfinitePlace.mk φ))
    have h1 : G.V.J.det ≠ 0 := fun e => h0 (by
      rw [show G.V.J.map _ = RingHom.mapMatrix _ G.V.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show G.V.J.map t = (t : E →+* Fv F v).mapMatrix G.V.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  haveI : Nonempty (Fin a) := ⟨⟨0, lt_of_le_of_lt (Nat.zero_le _) hT.geo.lt⟩⟩
  obtain ⟨φ, hφ, hφ0⟩ : ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ 0 ≠ 0 := by
    obtain ⟨Λ, -, f, hf, hne⟩ := GlobalTheory.T.exists_translation_invariant_functional F v a (a + a')
    obtain ⟨Y₀, hY⟩ : ∃ Y₀, f Y₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (by rw [show f = 0 from funext hc, map_zero])
    have hf' : (fun Y => f (Y + Y₀)) ∈ SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) :=
      ⟨hf.1.comp_continuous (continuous_add_const Y₀), hf.2.comp_homeomorph (Homeomorph.addRight Y₀)⟩
    obtain ⟨φ, hφ, e⟩ := hι.bij.surjOn hf'
    exact ⟨φ, hφ, by rw [e]; simpa using hY⟩
  refine ⟨t.comp σ, Or.inr (MonoidHom.ext fun x => ?_)⟩
  obtain ⟨g', rfl⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin a) x
  set g := GlobalTheory.LeviAtPlace.leviHom h t G.V.J hJ hT.geo.hV.herm g' with hgdef
  have hg : g ∈ UAt σ G.V (evFin F v) := GlobalTheory.LeviAtPlace.lift_sub_one_at v _
  have g1 : (mat g).map (piW t) = g'.1 := by
    rw [hgdef, GlobalTheory.LeviAtPlace.leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, GlobalTheory.LeviAtPlace.pairMat_fst]
  have g2 : (((Matrix.GeneralLinearGroup.det g')⁻¹ : (Fv F v)ˣ) : Fv F v) = ((mat g).map (piW (t.comp σ))).det := by
    rw [hgdef, GlobalTheory.LeviAtPlace.leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, GlobalTheory.LeviAtPlace.pairMat_snd,
      GlobalTheory.LeviAtPlace.conjComp, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
      Matrix.nonsing_inv_mul _ hJ, Matrix.det_one, one_mul, Matrix.det_transpose, ← map_inv]
    rfl
  obtain ⟨g'', e, hact⟩ := hν g hg
  obtain rfl : g' = g'' := Units.ext (g1.symm.trans e)
  obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B _ _ _ _ G.M _ _ om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 v).1 g hg 1 (fun u _ => by
      rw [show mat (1 : UA σ G.W.J) = 1 from rfl, sub_self, smul_zero]) φ hφ
  have k1 := lin_zero h G.M B.ψ hT.base.std _ _ om hT.weil t ι hι g hg _ g2 φ φ₁ hφ hA
  rw [hact φ hφ φ₁ hφ₁ hA, chrW_div, map_inv, inv_inv] at k1
  have k2 : ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g')⁻¹ ^ (((a + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ) =
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g') (-(Fintype.card (Fin (a + a')) : ℂ) / 2) := by
    rw [neg_div, ← GlobalTheory.SplitFlip.apow_inv, GlobalTheory.SplitFlip.apow,
      Complex.ofReal_cpow (show 0 ≤ GlobalTheory.SplitWeil.nabs _ _ from NNReal.coe_nonneg _), Fintype.card_fin]
    push_cast
    rfl
  rw [k2] at k1
  simp only [GlobalTheory.SplitFlip.omA, map_one, GlobalTheory.SplitFlip.apow_one, MonoidHom.one_apply, Units.val_one, mul_one,
    Matrix.mul_zero, Matrix.zero_mul] at k1
  have k3 := mul_right_cancel₀ (GlobalTheory.SplitFlip.apow_ne_zero _ _) (mul_right_cancel₀ hφ0 k1)
  rw [MonoidHom.inv_apply, ← inv_eq_iff_eq_inv]
  exact Units.ext k3

end GlobalTheory.MixedForm

end
