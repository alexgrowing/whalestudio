import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorLeftPartialPureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorRightPartialPureStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblEval

section Alg

variable {A : Type} {κ κ₁ κ₂ κ' κ₁' κ₂' : Type}

theorem partL_partL (T : ((κ₁ → A) → ℂ) → (κ₂ → A) → ℂ) (U : ((κ → A) → ℂ) → (κ₁ → A) → ℂ)
    (Φ : (κ ⊕ κ' → A) → ℂ) : partL T (partL U Φ) = partL (fun φ => T (U φ)) Φ := by
  funext y; simp only [partL, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem partR_partR (T : ((κ₁' → A) → ℂ) → (κ₂' → A) → ℂ) (U : ((κ' → A) → ℂ) → (κ₁' → A) → ℂ)
    (Φ : (κ ⊕ κ' → A) → ℂ) : partR T (partR U Φ) = partR (fun φ => T (U φ)) Φ := by
  funext y; simp only [partR, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem partL_congr {T T' : ((κ → A) → ℂ) → (κ₁ → A) → ℂ} {Φ : (κ ⊕ κ' → A) → ℂ}
    (h : ∀ b : κ' → A, T (fun x => Φ (Sum.elim x b)) = T' (fun x => Φ (Sum.elim x b))) : partL T Φ = partL T' Φ := by
  funext y; simp only [partL, h]

theorem partR_congr {T T' : ((κ' → A) → ℂ) → (κ₁' → A) → ℂ} {Φ : (κ ⊕ κ' → A) → ℂ}
    (h : ∀ a : κ → A, T (fun x => Φ (Sum.elim a x)) = T' (fun x => Φ (Sum.elim a x))) : partR T Φ = partR T' Φ := by
  funext y; simp only [partR, h]

theorem partL_partR_mt [Add A] (e : ((κ → A) → ℂ) →ₗ[ℂ] (κ₁ → A) → ℂ) (c : (κ' → A) → ℂ) (a : κ' → A)
    (Φ : (κ ⊕ κ' → A) → ℂ) :
    partL e (partR (fun φ x => c x * φ (x + a)) Φ) = partR (fun φ x => c x * φ (x + a)) (partL e Φ) := by
  funext y
  simp only [partL, partR, Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [show (fun x => c (y ∘ Sum.inr) * Φ (Sum.elim x (y ∘ Sum.inr + a))) =
    c (y ∘ Sum.inr) • fun x => Φ (Sum.elim x (y ∘ Sum.inr + a)) from rfl, map_smul]
  rfl

theorem partR_partL_mt [Add A] (e : ((κ' → A) → ℂ) →ₗ[ℂ] (κ₁' → A) → ℂ) (c : (κ → A) → ℂ) (a : κ → A)
    (Φ : (κ ⊕ κ' → A) → ℂ) :
    partR e (partL (fun φ x => c x * φ (x + a)) Φ) = partL (fun φ x => c x * φ (x + a)) (partR e Φ) := by
  funext y
  simp only [partL, partR, Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [show (fun x => c (y ∘ Sum.inl) * Φ (Sum.elim (y ∘ Sum.inl + a) x)) =
    c (y ∘ Sum.inl) • fun x => Φ (Sum.elim (y ∘ Sum.inl + a) x) from rfl, map_smul]
  rfl

end Alg

section Heis

variable {R : Type} [CommRing R] [Invertible (2 : R)]

theorem rho_dbl {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (ξ : E) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (d : Darboux (symp c ξ JA JB) κ) (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)) (h : IsDblCoord c ξ JA JB d dd)
    (ψ : AddChar R ℂ) (w₁ w₂ : Matrix α β E) (Φ : (κ ⊕ κ → R) → ℂ) :
    dd.rho ψ (Matrix.fromCols w₁ w₂) Φ = partL (d.rho ψ w₁) (partR (d.rho ψ⁻¹ w₂) Φ) := by
  funext y
  obtain ⟨u, v, rfl⟩ : ∃ u v, y = Sum.elim u v := ⟨_, _, (Sum.elim_comp_inl_inr y).symm⟩
  have h' := h w₁ w₂
  simp only [Darboux.rho, partL, partR, h', schr, Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim,
    Sum.elim_add_add, AddChar.inv_apply, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [dotProduct_neg]
  ring

variable {κ : Type} [Fintype κ] (ψ : AddChar R ℂ) (hψ : ∀ t, ‖ψ t‖ = 1)
include hψ

theorem conj_psi (t : R) : starRingEnd ℂ (ψ t) = ψ⁻¹ t := by
  rw [AddChar.inv_apply, AddChar.map_neg_eq_inv]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ t]
  norm_num

theorem conj_schr (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) (x : κ → R) :
    starRingEnd ℂ (schr ψ w φ x) = schr ψ⁻¹ w (fun x => starRingEnd ℂ (φ x)) x := by
  simp only [schr, map_mul, conj_psi ψ hψ]

theorem conj_schr_inv (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) (x : κ → R) :
    starRingEnd ℂ (schr ψ⁻¹ w φ x) = schr ψ w (fun x => starRingEnd ℂ (φ x)) x := by
  simp only [schr, map_mul, AddChar.inv_apply, conj_psi ψ hψ, inv_inv, neg_neg]

end Heis

section Glue

variable {A : Type} {κ κ₁ κ' κ₁' : Type}

theorem partL_id (Φ : (κ ⊕ κ' → A) → ℂ) : partL (fun φ => φ) Φ = Φ := by
  funext y; simp only [partL, Sum.elim_comp_inl_inr]

theorem partR_id (Φ : (κ ⊕ κ' → A) → ℂ) : partR (fun φ => φ) Φ = Φ := by
  funext y; simp only [partR, Sum.elim_comp_inl_inr]

theorem partL_intertwine {κa κb κc κd : Type} (T : ((κb → A) → ℂ) → (κd → A) → ℂ)
    (U : ((κa → A) → ℂ) → (κb → A) → ℂ) (U' : ((κc → A) → ℂ) → (κd → A) → ℂ) (T₀ : ((κa → A) → ℂ) → (κc → A) → ℂ)
    (S : Set ((κa → A) → ℂ)) (h : ∀ φ ∈ S, T (U φ) = U' (T₀ φ)) {Φ : (κa ⊕ κ' → A) → ℂ}
    (hΦ : ∀ b, (fun x => Φ (Sum.elim x b)) ∈ S) : partL T (partL U Φ) = partL U' (partL T₀ Φ) := by
  rw [partL_partL, partL_partL]
  exact partL_congr fun b => h _ (hΦ b)

theorem partR_intertwine {κa κb κc κd : Type} (T : ((κb → A) → ℂ) → (κd → A) → ℂ)
    (U : ((κa → A) → ℂ) → (κb → A) → ℂ) (U' : ((κc → A) → ℂ) → (κd → A) → ℂ) (T₀ : ((κa → A) → ℂ) → (κc → A) → ℂ)
    (S : Set ((κa → A) → ℂ)) (h : ∀ φ ∈ S, T (U φ) = U' (T₀ φ)) {Φ : (κ ⊕ κa → A) → ℂ}
    (hΦ : ∀ a, (fun x => Φ (Sum.elim a x)) ∈ S) : partR T (partR U Φ) = partR U' (partR T₀ Φ) := by
  rw [partR_partR, partR_partR]
  exact partR_congr fun a => h _ (hΦ a)

end Glue

section Rho

variable {R : Type} [CommRing R] [Invertible (2 : R)] {Wt : Type} [AddCommGroup Wt] [Module R Wt] {Bf : Wt → Wt → R}
  {κ κ₁ κ' κ₁' : Type} [Fintype κ] [Fintype κ']

theorem partL_partR_rho (e : ((κ → R) → ℂ) →ₗ[ℂ] (κ₁ → R) → ℂ) (D : Darboux Bf κ') (ψ : AddChar R ℂ) (w : Wt)
    (Φ : (κ ⊕ κ' → R) → ℂ) : partL e (partR (D.rho ψ w) Φ) = partR (D.rho ψ w) (partL e Φ) :=
  partL_partR_mt e (fun x => ψ (x ⬝ᵥ (D.e w).2 + ⅟(2 : R) * ((D.e w).1 ⬝ᵥ (D.e w).2))) (D.e w).1 Φ

theorem partR_partL_rho (e : ((κ' → R) → ℂ) →ₗ[ℂ] (κ₁' → R) → ℂ) (D : Darboux Bf κ) (ψ : AddChar R ℂ) (w : Wt)
    (Φ : (κ ⊕ κ' → R) → ℂ) : partR e (partL (D.rho ψ w) Φ) = partL (D.rho ψ w) (partR e Φ) :=
  partR_partL_mt e (fun x => ψ (x ⬝ᵥ (D.e w).2 + ⅟(2 : R) * ((D.e w).1 ⬝ᵥ (D.e w).2))) (D.e w).1 Φ

theorem sliceL_partR_rho (D : Darboux Bf κ') (ψ : AddChar R ℂ) (w : Wt) (Φ : (κ ⊕ κ' → R) → ℂ) (b : κ' → R) :
    (fun x => partR (D.rho ψ w) Φ (Sum.elim x b)) =
      ψ (b ⬝ᵥ (D.e w).2 + ⅟(2 : R) * ((D.e w).1 ⬝ᵥ (D.e w).2)) • fun x => Φ (Sum.elim x (b + (D.e w).1)) := by
  funext x; simp [partR, Darboux.rho, schr]

end Rho

section Main

variable {F : Type} [Field F] [NumberField F]

theorem sliceL_mem {κ κ' : Type} [Fintype κ] [Fintype κ'] {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ'))
    (b : κ' → AF F) : (fun x => Φ (Sum.elim x b)) ∈ schA F κ := by
  have e1 : (fun x => Φ (Sum.elim x b)) = fun x => Φ (GlobalTheory.ThK.Adapt.glue (Equiv.sumComm κ κ') b x) :=
    funext fun x => congrArg Φ (funext fun k => by cases k <;> rfl)
  rw [e1]
  exact GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.sumComm κ κ') b hΦ

theorem sliceR_mem {κ κ' : Type} [Fintype κ] [Fintype κ'] {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ'))
    (a : κ → AF F) : (fun x => Φ (Sum.elim a x)) ∈ schA F κ' :=
  GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.refl (κ ⊕ κ')) a hΦ

variable {κ κ₁ κ' κ₁' : Type} [Fintype κ] [Fintype κ₁] [Fintype κ'] [Fintype κ₁']

theorem partL_mem (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ) (he : IsLocOp e) :
    ∀ Φ ∈ schA F (κ ⊕ κ'), partL e Φ ∈ schA F (κ₁ ⊕ κ') := by
  obtain ⟨P, hP⟩ := GlobalTheory.T.local_operator_left_partial_pure (κ' := κ') e he
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨g₁, hg₁, h1⟩ := hP g hg
    rw [h1 f]
    exact Submodule.subset_span ⟨P f, g₁, hg₁, rfl⟩
  | zero => show partLₗ e 0 ∈ _; rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => show partLₗ e (x + y) ∈ _; rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => show partLₗ e (c • x) ∈ _; rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem partR_mem (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ) (he : IsLocOp e) :
    ∀ Φ ∈ schA F (κ ⊕ κ'), partR e Φ ∈ schA F (κ ⊕ κ₁') := by
  obtain ⟨P, hP⟩ := GlobalTheory.T.local_operator_right_partial_pure (κ := κ) e he
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨g₁, hg₁, h1⟩ := hP g hg
    rw [h1 f]
    exact Submodule.subset_span ⟨P f, g₁, hg₁, rfl⟩
  | zero => show partRₗ e 0 ∈ _; rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => show partRₗ e (x + y) ∈ _; rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => show partRₗ e (c • x) ∈ _; rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem partL_adm (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ) (he : IsLocOp e) :
    ∀ l ∈ (adeleClass F).adm (κ₁ ⊕ κ'), l ∘ₗ partLₗ e ∈ (adeleClass F).adm (κ ⊕ κ') := by
  obtain ⟨P, hP⟩ := GlobalTheory.T.local_operator_left_partial_pure (κ' := κ') e he
  intro l hl g hg
  obtain ⟨g₁, hg₁, h1⟩ := hP g hg
  obtain ⟨T, hT⟩ := hl g₁ hg₁
  exact ⟨T.comp P, fun f => by rw [LinearMap.comp_apply, partLₗ_apply, h1 f, hT, ContinuousLinearMap.comp_apply]⟩

theorem partR_adm (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ) (he : IsLocOp e) :
    ∀ l ∈ (adeleClass F).adm (κ ⊕ κ₁'), l ∘ₗ partRₗ e ∈ (adeleClass F).adm (κ ⊕ κ') := by
  obtain ⟨P, hP⟩ := GlobalTheory.T.local_operator_right_partial_pure (κ := κ) e he
  intro l hl g hg
  obtain ⟨g₁, hg₁, h1⟩ := hP g hg
  obtain ⟨T, hT⟩ := hl g₁ hg₁
  exact ⟨T.comp P, fun f => by rw [LinearMap.comp_apply, partRₗ_apply, h1 f, hT, ContinuousLinearMap.comp_apply]⟩

end Main

section Ev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isLocOp_of_isEv {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁}
    {W₁ : Spc F E d₁} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E}
    {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
    (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e) : IsLocOp e := by
  obtain ⟨ei, ev, -, hev, hloc⟩ := he.loc
  refine ⟨ei, ev, fun v φ hφ => (hev v).2 ▸ Submodule.mem_map_of_mem hφ, (hM.std.and hM₁.std).mono fun v h => ?_,
    fun f φ hφ hstd => hloc f φ hφ ((hstd.and hM.std).mono fun v h => h.1.trans h.2.symm)⟩
  show ev v (Set.indicator _ 1) = Set.indicator _ 1
  rw [← h.1, (hev v).1, h.2]

end Ev

section Thm

theorem exists_dblEv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (cA σ) (-1) (incM F X₁.J) (dbl (incM F W.J))) (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X₁.J) (incM F W.J) M₁.co dd₁ →
      ∃ (ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ)) (e₂ : Fn F n d →ₗ[ℂ] Fn F n₁ d),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)) ∧
        (∀ (z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (incM F H.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) ∧
        (∀ z : Fin d ⊕ Fin d → AE F E, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) Φ) = ed Φ) ∧
        (∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d), l ∘ₗ ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) ∧
        (∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), ed (boxFun φ₁ φ₂) = boxFun (e φ₁) (e₂ φ₂)) ∧
        (∀ φ ∈ schA F (Fin n × Fin d), e₂ φ ∈ schA F (Fin n₁ × Fin d)) ∧
        ∃ φ ∈ schA F (Fin n × Fin d), e₂ φ ≠ 0 := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ _ hpair₁ e he hne dd dd₁ hdd hdd₁
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hpair.base.std
  have hL : IsLocOp e := isLocOp_of_isEv hpair.good hpair₁.good he
  have hL₂ : IsLocOp (conjLin e) := GlobalTheory.T.conj_local_operator e hL
  have hone : (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ = 1 := by
    rw [incM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have Heisenberg₂ : ∀ (z : Matrix (Fin n₁) (Fin d) (AE F E)), ∀ φ ∈ schA F (Fin n × Fin d),
      e (M.co.rho B.ψ (incM F H.ι * z) φ) = M₁.co.rho B.ψ z (e φ) := fun z φ hφ => by
    have := he.Heisenberg₂ z φ hφ
    rwa [hone, Matrix.mul_one] at this
  have heis₂ : ∀ (z : Matrix (Fin n₁) (Fin d) (AE F E)), ∀ φ ∈ schA F (Fin n × Fin d),
      conjLin e (M.co.rho B.ψ⁻¹ (incM F H.ι * z) φ) = M₁.co.rho B.ψ⁻¹ z (conjLin e φ) := fun z φ hφ => by
    funext y
    rw [conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (M.co.rho B.ψ⁻¹ (incM F H.ι * z) φ x)) =
        M.co.rho B.ψ (incM F H.ι * z) (fun x => starRingEnd ℂ (φ x)) :=
      funext fun x => conj_schr_inv B.ψ hψ _ _ _
    rw [h1, Heisenberg₂ z _ (GlobalTheory.T.adelic_schwartz_conj_mem φ hφ)]
    exact conj_schr B.ψ hψ _ _ _
  have inv₁ : ∀ (z : Fin d → AE F E), ∀ φ ∈ schA F (Fin n × Fin d),
      e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) φ) = e φ := fun z φ hφ => he.inv _ ⟨z, rfl⟩ φ hφ
  have inv₂ : ∀ (z : Fin d → AE F E), ∀ φ ∈ schA F (Fin n × Fin d),
      conjLin e (M.co.rho B.ψ⁻¹ (Matrix.vecMulVec (incV F H.x) z) φ) = conjLin e φ := fun z φ hφ => by
    funext y
    rw [conjLin_apply, conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (M.co.rho B.ψ⁻¹ (Matrix.vecMulVec (incV F H.x) z) φ x)) =
        M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) (fun x => starRingEnd ℂ (φ x)) :=
      funext fun x => conj_schr_inv B.ψ hψ _ _ _
    rw [h1, inv₁ z _ (GlobalTheory.T.adelic_schwartz_conj_mem φ hφ)]
  refine ⟨partRₗ (conjLin e) ∘ₗ partLₗ e, conjLin e, fun Φ hΦ => ?_, fun z Φ hΦ => ?_, fun z Φ hΦ => ?_,
    fun l hl => ?_, fun φ₁ _ φ₂ _ => ?_, fun φ hφ => ?_, ?_⟩
  · exact partR_mem (conjLin e) hL₂ _ (partL_mem e hL Φ hΦ)
  · rw [← Matrix.fromCols_toCols z, Matrix.mul_fromCols, rho_dbl _ _ _ _ _ _ hdd, rho_dbl _ _ _ _ _ _ hdd₁]
    simp only [LinearMap.comp_apply, partLₗ_apply, partRₗ_apply]
    rw [partL_intertwine e (M.co.rho B.ψ (incM F H.ι * z.toCols₁)) (M₁.co.rho B.ψ z.toCols₁) e _ (fun φ hφ => Heisenberg₂ _ φ hφ)
        (fun b => by rw [sliceL_partR_rho]; exact Submodule.smul_mem _ _ (sliceL_mem hΦ _)),
      partL_partR_rho, partR_partL_rho,
      partR_intertwine (conjLin e) (M.co.rho B.ψ⁻¹ (incM F H.ι * z.toCols₂)) (M₁.co.rho B.ψ⁻¹ z.toCols₂) (conjLin e) _
        (fun φ hφ => heis₂ _ φ hφ) (fun a => sliceR_mem (partL_mem e hL Φ hΦ) a)]
  · have hv : Matrix.vecMulVec (incV F H.x) z = Matrix.fromCols (Matrix.vecMulVec (incV F H.x) (z ∘ Sum.inl))
        (Matrix.vecMulVec (incV F H.x) (z ∘ Sum.inr)) := by
      ext i j; cases j <;> rfl
    rw [hv, rho_dbl _ _ _ _ _ _ hdd]
    simp only [LinearMap.comp_apply, partLₗ_apply, partRₗ_apply]
    rw [partL_intertwine e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (z ∘ Sum.inl))) (fun φ => φ) e _
        (fun φ hφ => inv₁ _ φ hφ) (fun b => by rw [sliceL_partR_rho]; exact Submodule.smul_mem _ _ (sliceL_mem hΦ _)),
      partL_id, partL_partR_rho,
      partR_intertwine (conjLin e) (M.co.rho B.ψ⁻¹ (Matrix.vecMulVec (incV F H.x) (z ∘ Sum.inr))) (fun φ => φ) (conjLin e) _
        (fun φ hφ => inv₂ _ φ hφ) (fun a => sliceR_mem (partL_mem e hL Φ hΦ) a), partR_id]
  · rw [← LinearMap.comp_assoc]
    exact partL_adm e hL _ (partR_adm (conjLin e) hL₂ l hl)
  · funext y
    simp only [LinearMap.comp_apply, partLₗ_apply, partRₗ_apply, partR, partL, boxFun, Sum.elim_comp_inl,
      Sum.elim_comp_inr]
    have h1 : (fun x => e (fun x' => φ₁ x' * φ₂ x) (y ∘ Sum.inl)) = e φ₁ (y ∘ Sum.inl) • φ₂ := funext fun x => by
      rw [show (fun x' => φ₁ x' * φ₂ x) = φ₂ x • φ₁ from funext fun x' => by simp [mul_comm], map_smul]
      simp [mul_comm]
    rw [h1, map_smul]
    rfl
  · exact GlobalTheory.T.adelic_schwartz_conj_mem _ (he.maps _ (GlobalTheory.T.adelic_schwartz_conj_mem φ hφ))
  · obtain ⟨Φ₀, h₀, hne⟩ := hne
    refine ⟨fun x => starRingEnd ℂ (Φ₀ x), GlobalTheory.T.adelic_schwartz_conj_mem _ h₀, fun h => hne (funext fun y => ?_)⟩
    have := congrFun h y
    simpa [conjLin_apply] using this

end Thm

end GlobalTheory.DblEval
