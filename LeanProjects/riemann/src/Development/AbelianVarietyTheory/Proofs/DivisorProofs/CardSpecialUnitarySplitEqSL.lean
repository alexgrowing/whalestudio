import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped Pointwise

namespace GlobalTheory.TamOne

theorem card_suMat_of_swap {A B : Type} [CommRing A] [CommRing B] (c : A →+* A) (e : A ≃+* B × B)
    (he : ∀ x, e (c x) = (e x).swap) (r : ℕ) :
    Nat.card (suMat A c r) = Nat.card (Matrix.SpecialLinearGroup (Fin r) B) := by
  let p1 : A →+* B := (RingHom.fst B B).comp (e : A →+* B × B)
  let p2 : A →+* B := (RingHom.snd B B).comp (e : A →+* B × B)
  have h1 : ∀ x, p1 (c x) = p2 x := fun x => congrArg Prod.fst (he x)
  have h2 : ∀ x, p2 (c x) = p1 x := fun x => congrArg Prod.snd (he x)
  have hext : ∀ M N : Matrix (Fin r) (Fin r) A, M.map p1 = N.map p1 → M.map p2 = N.map p2 → M = N := by
    intro M N hM hN
    ext i j
    exact e.injective (Prod.ext (congrFun (congrFun hM i) j) (congrFun (congrFun hN i) j))
  have hc1 : ∀ M : Matrix (Fin r) (Fin r) A, (M.map c).map p1 = M.map p2 := fun M => by
    ext i j; exact h1 _
  have hc2 : ∀ M : Matrix (Fin r) (Fin r) A, (M.map c).map p2 = M.map p1 := fun M => by
    ext i j; exact h2 _
  have hmap : ∀ (f : A →+* B) (M : Matrix (Fin r) (Fin r) A),
      ((M.map c)ᵀ * M).map f = ((M.map c).map f)ᵀ * M.map f := fun f M => by
    rw [Matrix.map_mul, Matrix.transpose_map]
  have hone : ∀ f : A →+* B, (1 : Matrix (Fin r) (Fin r) A).map f = 1 := fun f => Matrix.map_one _ f.map_zero f.map_one
  have key : ∀ g ∈ suMat A c r, (g.map p2)ᵀ * g.map p1 = 1 ∧ (g.map p1)ᵀ * g.map p2 = 1 ∧ (g.map p1).det = 1 := by
    rintro g ⟨hg, hd⟩
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg (fun M => M.map p1) hg
      simpa only [hmap, hc1, hone] using this
    · have := congrArg (fun M => M.map p2) hg
      simpa only [hmap, hc2, hone] using this
    · rw [show g.map p1 = p1.mapMatrix g from rfl, ← RingHom.map_det, hd, map_one]
  have hcancel : ∀ X Y Y' : Matrix (Fin r) (Fin r) B, X * Y = 1 → X * Y' = 1 → Y = Y' := fun X Y Y' h h' => by
    rw [← Matrix.mul_one Y, ← h', ← Matrix.mul_assoc, (mul_eq_one_comm.1 h), Matrix.one_mul]
  let φ : suMat A c r → Matrix.SpecialLinearGroup (Fin r) B := fun g => ⟨g.1.map p1, (key g.1 g.2).2.2⟩
  refine Nat.card_congr (Equiv.ofBijective φ ⟨fun g g' hgg => ?_, fun h => ?_⟩)
  · have e1 : g.1.map p1 = g'.1.map p1 := congrArg Subtype.val hgg
    apply Subtype.ext
    refine hext _ _ e1 ?_
    have k := (key g.1 g.2).2.1
    have k' := (key g'.1 g'.2).2.1
    rw [← e1] at k'
    exact hcancel _ _ _ k k'
  · let k : Matrix (Fin r) (Fin r) B := ((h⁻¹ : Matrix.SpecialLinearGroup (Fin r) B) : Matrix (Fin r) (Fin r) B)ᵀ
    let g : Matrix (Fin r) (Fin r) A := Matrix.of fun i j => e.symm ((h : Matrix (Fin r) (Fin r) B) i j, k i j)
    have g1 : g.map p1 = (h : Matrix (Fin r) (Fin r) B) := by
      ext i j; simp [g, p1]
    have g2 : g.map p2 = k := by
      ext i j; simp [g, p2]
    have hinv : ((h⁻¹ : Matrix.SpecialLinearGroup (Fin r) B) : Matrix (Fin r) (Fin r) B) *
        (h : Matrix (Fin r) (Fin r) B) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hg : g ∈ suMat A c r := by
      refine ⟨hext _ _ ?_ ?_, ?_⟩
      · rw [hmap, hc1, g1, g2, hone, Matrix.transpose_transpose, hinv]
      · rw [hmap, hc2, g1, g2, hone, ← Matrix.transpose_mul, hinv, Matrix.transpose_one]
      · apply e.injective
        refine Prod.ext ?_ ?_
        · change p1 g.det = p1 1
          rw [RingHom.map_det, RingHom.mapMatrix_apply, g1, map_one, Matrix.SpecialLinearGroup.det_coe]
        · change p2 g.det = p2 1
          rw [RingHom.map_det, RingHom.mapMatrix_apply, g2, map_one, Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe]
    exact ⟨⟨g, hg⟩, Subtype.ext g1⟩

section SplitPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

local notation3 "K⁺" => maximalRealSubfield E

theorem galGroup_int : IsGaloisGroup (E ≃ₐ[K⁺] E) (𝓞 K⁺) (𝓞 E) :=
  IsGaloisGroup.of_isFractionRing _ _ _ K⁺ E

attribute [local instance] galGroup_int

theorem complexConj_mul_self : IsCMField.complexConj E * IsCMField.complexConj E = 1 :=
  AlgEquiv.ext (IsCMField.complexConj_apply_apply E)

theorem gal_cases (g : E ≃ₐ[K⁺] E) : g = 1 ∨ g = IsCMField.complexConj E := by
  have hg : g ∈ Subgroup.zpowers (IsCMField.complexConj E) := by
    rw [IsCMField.zpowers_complexConj_eq_top]; exact Subgroup.mem_top g
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, IsCMField.orderOf_complexConj]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [Nat.cast_ofNat, h] <;> simp

theorem complexConj_smul_ideal (P : Ideal (𝓞 E)) :
    IsCMField.complexConj E • P = P.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap,
    inv_eq_of_mul_eq_one_right complexConj_mul_self]
  rfl

theorem exists_split_prime (hU : GlobalTheory.UCls.Unr E) (v : HeightOneSpectrum (𝓞 K⁺))
    (hv : ¬ (extIdeal (E := E) v).IsPrime) :
    ∃ P : Ideal (𝓞 E), P.IsMaximal ∧
      P ⊔ P.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) = ⊤ ∧
      extIdeal v = P ⊓ P.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) ∧
      Nonempty ((𝓞 K⁺ ⧸ v.asIdeal) ≃+* (𝓞 E ⧸ P)) := by
  unfold GlobalTheory.UCls.Unr at hU
  haveI := v.isMaximal
  have hI0 : v.asIdeal ≠ ⊥ := v.ne_bot
  obtain ⟨⟨P, hPp, hPo⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver v.asIdeal (𝓞 E)))
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hI0 P
  have hPm : P.IsMaximal := hPp.isMaximal hP0
  have hQ := complexConj_smul_ideal P
  have hs : v.asIdeal.primesOver (𝓞 E) = {P, IsCMField.complexConj E • P} := by
    ext Q'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hQp, hQo⟩
      obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal P Q' (E ≃ₐ[K⁺] E)
      rcases gal_cases g with rfl | rfl
      · rw [one_smul] at hg; exact Or.inl hg.symm
      · exact Or.inr hg.symm
    · rintro (rfl | rfl)
      · exact ⟨inferInstance, inferInstance⟩
      · exact ⟨inferInstance, inferInstance⟩
  have hQm : (IsCMField.complexConj E • P).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (Ideal.ne_bot_of_liesOver_of_ne_bot hI0 _)
  have he : ∀ P' ∈ v.asIdeal.primesOver (𝓞 E), P'.ramificationIdx (𝓞 K⁺) = 1 := by
    rintro P' ⟨hP', -⟩
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hJ := Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 E) (p := v.asIdeal) hI0
  rw [Finset.prod_congr rfl (fun P' hP' => by rw [he P' (Set.mem_toFinset.1 hP'), pow_one])] at hJ
  have hPQ : P ≠ IsCMField.complexConj E • P := by
    intro h
    apply hv
    have h1 : (v.asIdeal.primesOver (𝓞 E)).toFinset = {P} := by
      ext x; simp [hs, ← h]
    change (Ideal.map _ _).IsPrime
    rw [hJ, h1, Finset.prod_singleton]
    exact hPp
  have hcop : P ⊔ IsCMField.complexConj E • P = ⊤ := hPm.coprime_of_ne hQm hPQ
  have hfin : (v.asIdeal.primesOver (𝓞 E)).toFinset = {P, IsCMField.complexConj E • P} := by
    ext x; simp [hs]
  rw [hfin, Finset.prod_pair hPQ, Ideal.mul_eq_inf_of_coprime hcop] at hJ
  have h2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 E) (E ≃ₐ[K⁺] E)
  rw [hs, Set.ncard_pair hPQ, Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P (E ≃ₐ[K⁺] E),
    he P ⟨hPp, hPo⟩, Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P (E ≃ₐ[K⁺] E),
    IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two] at h2
  have hf : P.inertiaDeg (𝓞 K⁺) = 1 := by omega
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal P] at hf
  letI := Ideal.Quotient.field v.asIdeal
  exact ⟨P, hPm, hQ ▸ hcop, hQ ▸ hJ,
    ⟨RingEquiv.ofBijective _ (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hf)⟩⟩

end SplitPlace

theorem card_suMat_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), GlobalTheory.UCls.Unr E →
    ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ¬ (extIdeal (E := E) v).IsPrime →
    Nat.card (suMat (𝓞 E ⧸ extIdeal v) (resConj v) r) =
      Nat.card (Matrix.SpecialLinearGroup (Fin r) (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal)) := by
  intro E _ _ _ r hU v hv
  obtain ⟨P, hPm, hcop, hJ, ⟨α⟩⟩ := exists_split_prime hU v hv
  let f : 𝓞 E ≃+* 𝓞 E := (IsCMField.ringOfIntegersComplexConj E).toRingEquiv
  have hf : ∀ x, f (f x) = x := fun x => by
    apply RingOfIntegers.ext
    change IsCMField.complexConj E (IsCMField.complexConj E (x : E)) = (x : E)
    exact IsCMField.complexConj_apply_apply E _
  let Q : Ideal (𝓞 E) := P.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)
  have hQP : P = Q.map (f : 𝓞 E →+* 𝓞 E) :=
    (Ideal.map_comap_of_surjective (f : 𝓞 E →+* 𝓞 E) f.surjective P).symm
  let τ : (𝓞 E ⧸ Q) ≃+* (𝓞 E ⧸ P) := Ideal.quotientEquiv Q P f hQP
  let e : (𝓞 E ⧸ extIdeal v) ≃+* (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) × (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) :=
    (Ideal.quotEquivOfEq hJ).trans ((Ideal.quotientInfEquivQuotientProd P Q (Ideal.isCoprime_iff_sup_eq.2 hcop)).trans
      (RingEquiv.prodCongr α.symm (τ.trans α.symm)))
  have he : ∀ x, e (resConj v x) = (e x).swap := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [resConj_mk]
    refine Prod.ext ?_ ?_
    · simp [e, τ, Ideal.quotientEquiv_mk]
      rfl
    · simp [e, τ, Ideal.quotientEquiv_mk]
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]
      exact congrArg (Ideal.Quotient.mk P) (hf y)
  exact card_suMat_of_swap _ e he r

end GlobalTheory.TamOne
