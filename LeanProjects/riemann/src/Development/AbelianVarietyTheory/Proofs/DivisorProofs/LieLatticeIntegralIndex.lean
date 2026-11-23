import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMultipleInLieLattice
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published

noncomputable section
namespace GlobalTheory.TamPos
open ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_eq' (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem herm_pair (G X : Matrix (Fin r) (Fin r) E) (u w : Fin r → E) :
    herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = u ⬝ᵥ ((Xᵀ * G + G * X.map cc) *ᵥ fun b => cc (w b)) := by
  have hc : ∀ (P : Matrix (Fin r) (Fin r) E) (y : Fin r → E),
      (fun b => cc ((P *ᵥ y) b)) = P.map cc *ᵥ fun b => cc (y b) := by
    intro P y; ext a; simp [mulVec, dotProduct, cc, map_sum, map_mul]
  rw [herm_eq', herm_eq', hc, add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec u Xᵀ, vecMul_transpose]

theorem skew_iff (G X : Matrix (Fin r) (Fin r) E) :
    (∀ x y, herm G (X *ᵥ x) y + herm G x (X *ᵥ y) = 0) ↔ Xᵀ * G + G * X.map cc = 0 := by
  constructor
  · intro h
    ext a b
    have h1 := h (Pi.single a 1) (Pi.single b 1)
    rw [herm_pair] at h1
    have e : (fun c => cc ((Pi.single b (1 : E) : Fin r → E) c)) = Pi.single b 1 := by
      ext c; by_cases hcb : c = b <;> simp [hcb, cc]
    rw [e] at h1
    simpa [mulVec_single_one, Matrix.mul_assoc] using h1
  · intro h u w
    rw [herm_pair, h, zero_mulVec, dotProduct_zero]

theorem lieInt_eq (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    lieInt (IsCMField.complexConj E).toAlgHom Gᵀ Λ = lieLat G Λ := by
  ext X
  change (X.trace = 0 ∧ _ ∧ _) ↔ (X.trace = 0 ∧ _ ∧ _)
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  rw [skew_iff, ← transpose_eq_zero (M := Xᵀ * G + G * X.map cc)]
  rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, add_comm]
  rfl

theorem resOrder_pos (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) : 0 < resOrder E r v := by
  unfold resOrder
  split_ifs with h
  · have hI : v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≠ ⊥ := by
      rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
      exact v.ne_bot
    haveI := Ideal.finiteQuotientOfFreeOfNeBot _ hI
    refine (Set.ncard_pos (Set.toFinite _)).2 ⟨_, 1, ⟨by simp, fun a b => by simp⟩, rfl⟩
  · haveI := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    exact Nat.card_pos

theorem locFactor_pos (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) : 0 < locFactor E r v := by
  unfold locFactor
  refine div_pos (by exact_mod_cast resOrder_pos v) (pow_pos ?_ _)
  exact_mod_cast Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

section Dim
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
local notation "F" => maximalRealSubfield E

theorem map_cc_smul (c : F) (X : Matrix (Fin r) (Fin r) E) : (c • X).map cc = c • X.map cc := by
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, cc]
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def]

def skewSp (G : Matrix (Fin r) (Fin r) E) : Submodule F (Matrix (Fin r) (Fin r) E) where
  carrier := {X | Xᵀ * G + G * X.map cc = 0}
  zero_mem' := by
    have e : (0 : Matrix (Fin r) (Fin r) E).map cc = 0 := by ext; simp [cc]
    simp [e]
  add_mem' {X Y} hX hY := by
    have e : (X + Y).map cc = X.map cc + Y.map cc := by ext; simp [cc]
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [e, transpose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  smul_mem' c X hX := by
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [map_cc_smul, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

def slSp (G : Matrix (Fin r) (Fin r) E) : Submodule F (Matrix (Fin r) (Fin r) E) where
  carrier := {X | X.trace = 0 ∧ Xᵀ * G + G * X.map cc = 0}
  zero_mem' := ⟨by simp, (skewSp G).zero_mem⟩
  add_mem' {X Y} hX hY := ⟨by rw [trace_add, hX.1, hY.1, add_zero], (skewSp G).add_mem hX.2 hY.2⟩
  smul_mem' c X hX := ⟨by rw [trace_smul, hX.1, smul_zero], (skewSp G).smul_mem c hX.2⟩

theorem slSp_le (G : Matrix (Fin r) (Fin r) E) : slSp G ≤ skewSp G := fun _ h => h.2

theorem exists_imag : ∃ δ : E, δ ≠ 0 ∧ IsCMField.complexConj E δ = -δ := by
  obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  refine ⟨x - IsCMField.complexConj E x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub, IsCMField.complexConj_apply_apply]
  ring

theorem finrank_skewSp_le (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) :
    Module.finrank F (skewSp G) ≤ r ^ 2 := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_imag (E := E)
  let f : (skewSp G × skewSp G) →ₗ[F] Matrix (Fin r) (Fin r) E :=
    { toFun := fun p => (p.1 : Matrix (Fin r) (Fin r) E) + δ • (p.2 : Matrix (Fin r) (Fin r) E)
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, RingHom.id_apply,
          smul_comm δ c] }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ h
    change X + δ • Y = 0 at h
    change Xᵀ * G + G * X.map cc = 0 at hX
    change Yᵀ * G + G * Y.map cc = 0 at hY
    have hXe : X = -(δ • Y) := eq_neg_of_add_eq_zero_left h
    have hXc : X.map cc = δ • Y.map cc := by
      rw [hXe]; ext a b; simp [cc, hδ]
    rw [hXc, hXe, transpose_neg, transpose_smul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul,
      eq_neg_of_add_eq_zero_left hY, smul_neg, neg_neg, ← two_smul E (δ • (G * Y.map cc)), smul_smul] at hX
    have h2 : G * Y.map cc = 0 := by
      rcases smul_eq_zero.1 hX with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hδ0)
      · exact h
    have h3 : Y.map cc = 0 := by
      have := congrArg (fun M => G⁻¹ * M) h2
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hG)] using this
    have hY0 : Y = 0 := by
      ext a b
      have := congrFun (congrFun h3 a) b
      simpa [cc] using this
    have hX0 : X = 0 := by rw [hXe, hY0, smul_zero, neg_zero]
    subst hX0 hY0
    rfl
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, Module.finrank_matrix, Fintype.card_fin,
    Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
  rw [sq]
  omega

theorem finrank_slSp_le (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) :
    Module.finrank F (slSp G) ≤ r ^ 2 - 1 := by
  have hle := finrank_skewSp_le G hG
  rcases Nat.eq_zero_or_pos r with hr | hr
  · have := Submodule.finrank_mono (slSp_le G)
    subst hr; exact this.trans hle
  obtain ⟨δ, hδ0, hδ⟩ := exists_imag (E := E)
  have hmem : δ • (1 : Matrix (Fin r) (Fin r) E) ∈ skewSp G := by
    change (δ • (1 : Matrix (Fin r) (Fin r) E))ᵀ * G + G * (δ • (1 : Matrix (Fin r) (Fin r) E)).map cc = 0
    have e : (δ • (1 : Matrix (Fin r) (Fin r) E)).map cc = (-δ) • 1 := by
      ext a b; by_cases h : a = b <;> simp [h, cc, hδ, Matrix.one_apply]
    rw [e, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
      neg_smul, add_neg_cancel]
  have hnot : δ • (1 : Matrix (Fin r) (Fin r) E) ∉ slSp G := by
    intro h
    have := h.1
    rw [trace_smul, trace_one, Fintype.card_fin, smul_eq_mul] at this
    exact mul_ne_zero hδ0 (Nat.cast_ne_zero.2 hr.ne') this
  have hlt : slSp G < skewSp G := lt_of_le_of_ne (slSp_le G) fun h => hnot (h ▸ hmem)
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

end Dim

section Index
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
local notation "F" => maximalRealSubfield E

theorem lieLat_le_slSp (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) {X : Matrix (Fin r) (Fin r) E}
    (hX : X ∈ lieLat G Λ) : X ∈ slSp G :=
  ⟨hX.1, (skew_iff G X).1 hX.2.1⟩

theorem span_eq_slSp (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (Λ : Submodule (𝓞 E) (Fin r → E))
    (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E) (he : ∀ i, e i ∈ lieLat G Λ)
    (hli : LinearIndependent F e) : Submodule.span F (Set.range e) = slSp G := by
  refine Submodule.eq_of_le_of_finrank_le ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact lieLat_le_slSp G Λ (he i)
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact finrank_slSp_le G hG

theorem exists_nsmul_mem_span {n : ℕ} (e : Fin n → Matrix (Fin r) (Fin r) E) {X : Matrix (Fin r) (Fin r) E}
    (hX : X ∈ Submodule.span F (Set.range e)) :
    ∃ m : ℕ, 0 < m ∧ m • X ∈ Submodule.span (𝓞 F) (Set.range e) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hX
  have hc : ∀ i, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : F) * c i) := fun i => GlobalTheory.DenClear.exists_natMul_isIntegral (c i)
  choose m hm hint using hc
  refine ⟨∏ i, m i, Finset.prod_pos fun i _ => hm i, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have hI : IsIntegral ℤ (((∏ j, m j : ℕ) : F) * c i) := by
    rw [hk, Nat.cast_mul, mul_comm (m i : F), mul_assoc]
    have h1 := (isIntegral_algebraMap (R := ℤ) (A := F) (x := (k : ℤ))).mul (hint i)
    simpa using h1
  let a : 𝓞 F := ⟨_, (mem_integralClosure_iff ℤ F).2 hI⟩
  have e1 : (∏ j, m j) • c i • e i = a • e i := by
    rw [← algebraMap_smul F a (e i), ← Nat.cast_smul_eq_nsmul F, smul_smul]
    rfl
  rw [e1]
  exact Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)

theorem fg_lieLat (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) : AddGroup.FG (lieLat G Λ) := by
  have hv : ∀ j : Fin r, ∃ n : ℕ, 0 < n ∧ (n : E) • (Pi.single j 1 : Fin r → E) ∈ Λ := fun j =>
    GlobalTheory.DenClear.exists_natSmul_mem Λ _ (by rw [hspan]; trivial)
  choose n hn hnΛ using hv
  set N := ∏ j, n j with hN
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 (Finset.prod_pos fun j _ => hn j).ne'
  have hNΛ : ∀ j, (N : E) • (Pi.single j 1 : Fin r → E) ∈ Λ := by
    intro j
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ j)
    rw [hN, hk, Nat.cast_mul, mul_comm, ← smul_smul, Nat.cast_smul_eq_nsmul]
    exact Λ.nsmul_mem (hnΛ j) k
  let φ : lieLat G Λ →+ (Fin r → Λ) :=
    { toFun := fun X j => ⟨X.1 *ᵥ ((N : E) • Pi.single j 1), X.2.2.2 _ (hNΛ j)⟩
      map_zero' := by ext j; simp
      map_add' := by intro X Y; ext j; simp [add_mulVec] }
  have hinj : Function.Injective φ := by
    intro X Y h
    apply Subtype.ext
    ext a j
    have := congrArg (fun f : Fin r → Λ => ((f j : Λ) : Fin r → E) a) h
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mulVec_smul, mulVec_single_one, Pi.smul_apply,
      smul_eq_mul] at this
    exact mul_left_cancel₀ hN0 this
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  haveI : Module.Finite ℤ (lieLat G Λ) := Module.Finite.of_injective φ.toIntLinearMap hinj
  exact Module.Finite.iff_addGroup_fg.1 inferInstance

theorem relIndex_ne_zero (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E) (hS : SelfDualLat G Λ) (he : ∀ i, e i ∈ lieLat G Λ)
    (hli : LinearIndependent F e) :
    (Submodule.span (𝓞 F) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) ≠ 0 := by
  haveI := fg_lieLat G Λ hS.2.2.1 hS.2.2.2.1
  have hsp := span_eq_slSp G hS.2.1 Λ e he hli
  haveI : Finite (lieLat G Λ ⧸ (Submodule.span (𝓞 F) (Set.range e)).toAddSubgroup.addSubgroupOf (lieLat G Λ)) := by
    refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
    induction x using QuotientAddGroup.induction_on with
    | H b =>
      obtain ⟨m, hm, hmem⟩ := exists_nsmul_mem_span e (hsp ▸ lieLat_le_slSp G Λ b.2)
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact hmem
  exact AddSubgroup.index_ne_zero_of_finite

end Index

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → (∀ i, e i ∈ lieLat G Λ) → LinearIndependent (maximalRealSubfield E) e → lieInt (IsCMField.complexConj E).toAlgHom Gᵀ Λ = lieLat G Λ ∧ (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) ≠ 0 ∧ ∀ v, 0 < locFactor E r v := by
  intro E _ _ _ r G Λ e hS he hli
  exact ⟨lieInt_eq G Λ, relIndex_ne_zero G Λ e hS he hli, fun v => locFactor_pos v⟩
end GlobalTheory.TamPos
