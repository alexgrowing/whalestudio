import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open Polynomial
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnitNorm

open PositivityTheory.Rg.Tf.Loc

noncomputable section

section Eval

variable {O O' E : Type} [CommRing O] [CommRing O'] [Algebra O O'] [Field E] [Algebra O E]
  {n : ℕ}

def evalRight (P : O[X]) (M : Matrix (Fin n) (Fin n) E) (hM : aeval M P = 0) :
    AdjoinRoot P →ₐ[O] Matrix (Fin n) (Fin n) E :=
  Ideal.Quotient.liftₐ (Ideal.span {P}) (aeval M) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [hM])

theorem evalRight_mk (P : O[X]) (M : Matrix (Fin n) (Fin n) E) (hM : aeval M P = 0) (f : O[X]) :
    evalRight P M hM (AdjoinRoot.mk P f) = aeval M f := rfl

def evalLeft (j : O' →ₐ[O] E) : O' →ₐ[O] Matrix (Fin n) (Fin n) E :=
  ((Algebra.ofId E (Matrix (Fin n) (Fin n) E)).restrictScalars O).comp j

theorem evalLeft_commute (j : O' →ₐ[O] E) (P : O[X]) (M : Matrix (Fin n) (Fin n) E)
    (hM : aeval M P = 0) (x : O') (y : AdjoinRoot P) :
    Commute (evalLeft j x : Matrix (Fin n) (Fin n) E) (evalRight P M hM y) :=
  Algebra.commutes (j x) (evalRight P M hM y)

def evalT (j : O' →ₐ[O] E) (P : O[X]) (M : Matrix (Fin n) (Fin n) E) (hM : aeval M P = 0) :
    O' ⊗[O] AdjoinRoot P →ₐ[O] Matrix (Fin n) (Fin n) E :=
  Algebra.TensorProduct.lift (evalLeft j) (evalRight P M hM)
    (evalLeft_commute j P M hM)

theorem evalT_tmul (j : O' →ₐ[O] E) (P : O[X]) (M : Matrix (Fin n) (Fin n) E)
    (hM : aeval M P = 0) (x : O') (r : AdjoinRoot P) :
    evalT j P M hM (x ⊗ₜ r) = algebraMap E _ (j x) * evalRight P M hM r := by
  unfold evalT; rw [Algebra.TensorProduct.lift_tmul]; rfl

theorem evalT_poly (j : O' →ₐ[O] E) (P : O[X]) (M : Matrix (Fin n) (Fin n) E)
    (hM : aeval M P = 0) (S : Subring E) (hS : ∀ x, j x ∈ S) (t : O' ⊗[O] AdjoinRoot P) :
    ∃ p : E[X], evalT j P M hM t = aeval M p ∧ ∀ i, p.coeff i ∈ S := by
  have hO : ∀ a : O, algebraMap O E a ∈ S := fun a => by
    rw [← j.commutes a]; exact hS _
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp [S.zero_mem]⟩
  | tmul x r =>
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
    refine ⟨C (j x) * f.map (algebraMap O E), ?_, fun i => ?_⟩
    · rw [evalT_tmul, evalRight_mk, map_mul, aeval_C, aeval_map_algebraMap]
    · rw [coeff_C_mul, coeff_map]; exact S.mul_mem (hS x) (hO _)
  | add a b ha hb =>
    obtain ⟨p, hp, hp'⟩ := ha
    obtain ⟨q, hq, hq'⟩ := hb
    refine ⟨p + q, by rw [map_add, hp, hq, map_add], fun i => ?_⟩
    rw [coeff_add]; exact S.add_mem (hp' i) (hq' i)

theorem evalT_map (j : O' →ₐ[O] E) (P : O[X]) (M : Matrix (Fin n) (Fin n) E)
    (hM : aeval M P = 0) (τ : O' →ₐ[O] O') (s : E →ₐ[O] E) (hs : ∀ x, s (j x) = j (τ x))
    (hMs : M.map s = M) (t : O' ⊗[O] AdjoinRoot P) :
    (evalT j P M hM t).map s =
      evalT j P M hM (Algebra.TensorProduct.map τ (AlgHom.id O (AdjoinRoot P)) t) := by
  have hφ : ∀ A : Matrix (Fin n) (Fin n) E, A.map s = s.mapMatrix A := fun _ => rfl
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x r =>
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
    rw [Algebra.TensorProduct.map_tmul, evalT_tmul, evalT_tmul, evalRight_mk, AlgHom.id_apply,
      evalRight_mk, hφ, map_mul, ← aeval_algHom_apply, ← hφ M, hMs, ← hs]
    congr 1
    ext a b
    simp [Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ← ha, ← hb]
    ext a b
    simp

end Eval

section Norm

variable {k E O O' : Type} [Field k] [Field E] [Algebra k E] [CommRing O] [CommRing O']
  [Algebra O O'] [Algebra O k] [Algebra O E] [IsScalarTower O k E]

theorem pow_compat (j : O' →ₐ[O] E) (σ : E ≃ₐ[k] E) (τ : O' ≃ₐ[O] O')
    (hτ : ∀ x, σ (j x) = j (τ x)) (i : ℕ) (x : O') : (σ ^ i) (j x) = j ((τ ^ i) x) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτ, ih]

theorem exists_norm_eval (j : O' →ₐ[O] E) (σ : E ≃ₐ[k] E) (τ : O' ≃ₐ[O] O')
    (hτ : ∀ x, σ (j x) = j (τ x)) (S : Subring E) (hS : ∀ x, j x ∈ S) {n : ℕ}
    (γ : GL (Fin n) k) (P : O[X])
    (hP : P.map (algebraMap O k) = (γ : Matrix (Fin n) (Fin n) k).charpoly)
    (s : (O' ⊗[O] AdjoinRoot P)ˣ)
    (hs : ∏ i ∈ Finset.range (Module.finrank k E),
        Algebra.TensorProduct.map ((τ ^ i : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O (AdjoinRoot P))
          (s : O' ⊗[O] AdjoinRoot P) =
      Algebra.TensorProduct.includeRight (AdjoinRoot.root P)) :
    ∃ c : GL (Fin n) E,
      (∃ p : E[X], (c : Matrix (Fin n) (Fin n) E) =
          aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p ∧ ∀ i, p.coeff i ∈ S) ∧
      (∃ q : E[X], ((c⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
          aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) q ∧ ∀ i, q.coeff i ∈ S) ∧
      normGL σ c = incl γ := by
  set M : Matrix (Fin n) (Fin n) E := ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hMdef
  have hMk : M = (γ : Matrix (Fin n) (Fin n) k).map (algebraMap k E) := rfl
  have hM : aeval M P = 0 := by
    have h1 : P.map (algebraMap O E) = M.charpoly := by
      rw [hMk, Matrix.charpoly_map, ← hP, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    rw [← aeval_map_algebraMap E, h1, Matrix.aeval_self_charpoly]
  let ev := evalT j P M hM
  let c : GL (Fin n) E := Units.map (ev : _ →* _) s
  have hc : ((c : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = ev s := rfl
  have hci : ((c⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = ev (s⁻¹ : (O' ⊗[O] AdjoinRoot P)ˣ).val := rfl
  have hfix : ∀ i : ℕ, M.map (((σ ^ i : E ≃ₐ[k] E) : E →ₐ[k] E).restrictScalars O) = M := by
    intro i
    rw [hMk]
    ext a b
    exact (σ ^ i).commutes _
  have hmap : ∀ (i : ℕ) (t : O' ⊗[O] AdjoinRoot P),
      ((sigmaGL σ ^ i) (Units.map (ev : _ →* _) s) : GL (Fin n) E).val =
        ev (Algebra.TensorProduct.map ((τ ^ i : O' ≃ₐ[O] O').toAlgHom)
          (AlgHom.id O (AdjoinRoot P)) s.val) := by
    intro i _
    rw [← sigmaGL_pow, sigmaGL_val]
    exact evalT_map j P M hM ((τ ^ i : O' ≃ₐ[O] O').toAlgHom)
      (((σ ^ i : E ≃ₐ[k] E) : E →ₐ[k] E).restrictScalars O)
      (fun x => pow_compat j σ τ hτ i x) (hfix i) s.val
  have key : ∀ m : ℕ, ((twNorm (sigmaGL σ) m c : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      ev (∏ i ∈ Finset.range m, Algebra.TensorProduct.map ((τ ^ i : O' ≃ₐ[O] O').toAlgHom)
        (AlgHom.id O (AdjoinRoot P)) s.val) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [twNorm_succ, Units.val_mul, ih, Finset.prod_range_succ, map_mul, hmap m 0]
  refine ⟨c, ?_, ?_, ?_⟩
  · exact evalT_poly j P M hM S hS s.val
  · exact evalT_poly j P M hM S hS (s⁻¹ : (O' ⊗[O] AdjoinRoot P)ˣ).val
  · apply Units.ext
    show ((twNorm (sigmaGL σ) (Module.finrank k E) c : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = M
    rw [key, hs]
    show evalT j P M hM (1 ⊗ₜ AdjoinRoot.root P) = M
    rw [evalT_tmul, map_one, map_one, one_mul]
    show evalRight P M hM (AdjoinRoot.mk P X) = M
    rw [evalRight_mk, aeval_X]

end Norm

section Unit

variable {O : Type} [CommRing O]

theorem isUnit_root (P : O[X]) (h0 : IsUnit (P.coeff 0)) : IsUnit (AdjoinRoot.root P) := by
  obtain ⟨u, hu⟩ := h0
  have h1 : AdjoinRoot.mk P (P.divX * X + C (P.coeff 0)) = 0 := by
    rw [Polynomial.divX_mul_X_add]; exact AdjoinRoot.mk_self
  rw [map_add, map_mul, ← hu] at h1
  have h2 : AdjoinRoot.root P * (-(AdjoinRoot.of P (u⁻¹ : Oˣ).val * AdjoinRoot.mk P P.divX)) = 1 := by
    have h3 : AdjoinRoot.mk P (C (u : O)) * AdjoinRoot.of P (u⁻¹ : Oˣ).val = 1 := by
      show AdjoinRoot.of P (u : O) * AdjoinRoot.of P (u⁻¹ : Oˣ).val = 1
      rw [← map_mul, Units.mul_inv, map_one]
    have h4 : AdjoinRoot.mk P X = AdjoinRoot.root P := rfl
    rw [h4] at h1
    calc AdjoinRoot.root P * (-(AdjoinRoot.of P (u⁻¹ : Oˣ).val * AdjoinRoot.mk P P.divX))
        = -((AdjoinRoot.mk P P.divX * AdjoinRoot.root P) * AdjoinRoot.of P (u⁻¹ : Oˣ).val) := by ring
      _ = -((-(AdjoinRoot.mk P (C (u : O)))) * AdjoinRoot.of P (u⁻¹ : Oˣ).val) := by
          rw [eq_neg_of_add_eq_zero_left h1]
      _ = 1 := by rw [neg_mul, neg_neg, h3]
  exact IsUnit.of_mul_eq_one _ h2

end Unit

section Final

theorem adicComplete_intO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    IsAdicComplete (IsLocalRing.maximalIdeal (intO k)) (intO k) := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  exact inferInstance

theorem exists_integral_norm_of_unit_norm_surjective : D0a → IntegralBasisUnramified → TraceOneIntegralElement → N3 → N4 := by
  intro h0a h0b h0c h3
  unfold N4
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n γ hγ
  obtain ⟨hval, hint, -, -, -, -⟩ := h0a k E hun σ hgen
  obtain ⟨⟨b, hb, hb'⟩, -, -⟩ := h0b k E hun σ hgen
  obtain ⟨-, x, y, hxy, hdual⟩ := h0c k E hun σ hgen
  haveI := adicComplete_intO k
  haveI : Finite (IsLocalRing.ResidueField (intO k)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (Valuation.integer (ValuativeRel.valuation k))))
  let f : intO k →+* intO E := ((algebraMap k E).comp (intO k).subtype).codRestrict (intO E)
    (fun a => (hint a).2 a.2)
  letI : Algebra (intO k) (intO E) := f.toAlgebra
  haveI : IsScalarTower (intO k) (intO E) E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e : intO E ≃ₗ[intO k] (Fin (Module.finrank k E) → intO k) :=
    { toFun := fun z i => ⟨b.repr z.1 i, (hb' z.1).1 z.2 i⟩
      invFun := fun v => ⟨∑ i, (v i : k) • b i, (hb' _).2 (fun i => by
        rw [b.repr_sum_self]; exact (v i).2)⟩
      left_inv := fun z => Subtype.ext (b.sum_repr z.1)
      right_inv := fun v => by
        funext i
        apply Subtype.ext
        show b.repr (∑ i, (v i : k) • b i) i = v i
        rw [b.repr_sum_self]
      map_add' := fun z w => by
        funext i
        apply Subtype.ext
        show b.repr (z.1 + w.1) i = b.repr z.1 i + b.repr w.1 i
        simp
      map_smul' := fun a z => by
        funext i
        apply Subtype.ext
        show b.repr (algebraMap k E a.1 * z.1) i = a.1 * b.repr z.1 i
        rw [← Algebra.smul_def]
        simp }
  haveI : Module.Finite (intO k) (intO E) := Module.Finite.equiv e.symm
  haveI : Module.Free (intO k) (intO E) := Module.Free.of_equiv e.symm
  have hmem : ∀ (ρ : E ≃ₐ[k] E) (z : E), z ∈ intO E → ρ z ∈ intO E := fun ρ z hz => by
    have h := hval ρ z
    rw [Valuation.mem_integer_iff] at *
    rwa [h]
  let τ : intO E ≃ₐ[intO k] intO E :=
    { toFun := fun z => ⟨σ z.1, hmem σ z.1 z.2⟩
      invFun := fun z => ⟨σ.symm z.1, hmem σ.symm z.1 z.2⟩
      left_inv := fun z => Subtype.ext (σ.symm_apply_apply z.1)
      right_inv := fun z => Subtype.ext (σ.apply_symm_apply z.1)
      map_mul' := fun z w => Subtype.ext (map_mul σ z.1 w.1)
      map_add' := fun z w => Subtype.ext (map_add σ z.1 w.1)
      commutes' := fun a => Subtype.ext (σ.commutes a.1) }
  let j : intO E →ₐ[intO k] E := IsScalarTower.toAlgHom _ _ _
  have hτ : ∀ z, σ (j z) = j (τ z) := fun _ => rfl
  have hσℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hτℓ : τ ^ Module.finrank k E = 1 := by
    refine AlgEquiv.ext fun z => Subtype.ext ?_
    have h := pow_compat j σ τ hτ (Module.finrank k E) z
    rw [hσℓ] at h
    exact h.symm
  have hpos : 0 < Module.finrank k E := Module.finrank_pos
  have hfixed : ∀ z : intO E, τ z = z → z ∈ Set.range (algebraMap (intO k) (intO E)) := by
    intro z hz
    have h1 : σ z.1 = z.1 := congrArg Subtype.val hz
    have hst : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) z.1 := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact h1
    have hall : ∀ ρ : E ≃ₐ[k] E, ρ z.1 = z.1 := by
      intro ρ
      have h2 := (Subgroup.zpowers_le.mpr hst) (hgen ρ)
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at h2
    have h3' := (IsGalois.mem_bot_iff_fixed z.1).mpr hall
    rw [IntermediateField.mem_bot] at h3'
    obtain ⟨a, ha⟩ := h3'
    exact ⟨⟨a, (hint a).1 (ha ▸ z.2)⟩, Subtype.ext ha⟩
  have hdual' : ∃ x' y' : Fin (Module.finrank k E) → intO E, ∀ m < Module.finrank k E,
      ∑ i, x' i * (τ ^ m) (y' i) = if m = 0 then 1 else 0 := by
    refine ⟨fun i => ⟨x i, (hxy i).1⟩, fun i => ⟨y i, (hxy i).2⟩, fun m hm => ?_⟩
    have hjinj : Function.Injective j := Subtype.val_injective
    apply hjinj
    rw [map_sum]
    have e1 : ∀ i, j ((⟨x i, (hxy i).1⟩ : intO E) * (τ ^ m) ⟨y i, (hxy i).2⟩) =
        x i * (σ ^ m) (y i) := fun i => by
      rw [map_mul, ← pow_compat j σ τ hτ m]; rfl
    rw [Finset.sum_congr rfl fun i _ => e1 i, hdual m hm]
    split_ifs <;> simp
  have hlift : (γ : Matrix (Fin n) (Fin n) k).charpoly ∈ Polynomial.lifts (intO k).subtype :=
    (Polynomial.lifts_iff_coeff_lifts _).2 (fun i => ⟨⟨_, hγ.1 i⟩, rfl⟩)
  obtain ⟨P, hPmap, -, hPm⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift (Matrix.charpoly_monic _)
  have hP : P.map (algebraMap (intO k) k) = (γ : Matrix (Fin n) (Fin n) k).charpoly := hPmap
  have hcoef : ((P.coeff 0 : intO k) : k) = (γ : Matrix (Fin n) (Fin n) k).charpoly.coeff 0 := by
    rw [← hPmap, coeff_map]; rfl
  have h0 : IsUnit (P.coeff 0) := by
    refine (Valuation.integer.integers (ValuativeRel.valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    show ValuativeRel.valuation k ((P.coeff 0 : intO k) : k) = 1
    rw [hcoef]
    exact hγ.2
  haveI : Module.Finite (intO k) (AdjoinRoot P) := hPm.finite_adjoinRoot
  obtain ⟨s, hs⟩ := h3 (intO k) (intO E) (AdjoinRoot P) (Module.finrank k E) τ hpos hτℓ hfixed
    hdual' (isUnit_root P h0).unit
  exact exists_norm_eval j σ τ hτ (intO E) (fun z => z.2) γ P hP s hs

end Final

end

end GlobalTheory.CompanionTheory.UnitNorm
