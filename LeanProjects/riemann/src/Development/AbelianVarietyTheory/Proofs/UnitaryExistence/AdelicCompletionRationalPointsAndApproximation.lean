import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNatStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemAdelicCompletionPseudoBasisIffStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNatMulMem
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section RationalPoints

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
theorem cap_fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  funext i
  simp [fv, TensorProduct.tmul_add]

omit [NumberField E] in
theorem cap_fv_neg (x : Fin n → E) : fv F (-x) = - fv F x := by
  funext i
  simp [fv, TensorProduct.tmul_neg]

omit [NumberField E] in
theorem cap_fv_zero : fv F (0 : Fin n → E) = 0 := by
  funext i
  simp [fv]

omit [NumberField E] in
theorem cap_fv_nsmul (d : ℕ) (x : Fin n → E) : fv F (d • x) = d • fv F x := by
  induction d with
  | zero => simp [cap_fv_zero]
  | succ d ih => rw [succ_nsmul, succ_nsmul, cap_fv_add, ih]

omit [NumberField E] in
theorem cap_gen_mem (L : Set (Fin n → E)) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (x : Fin n → E) (hx : x ∈ L) :
    (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) ∈ hat F L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

omit [NumberField E] in
theorem cap_fv_mem (L : Set (Fin n → E)) (x : Fin n → E) (hx : x ∈ L) : fv F x ∈ hat F L :=
  cap_gen_mem F L 1 (fun v => (v.adicCompletionIntegers F).one_mem) x hx

omit [NumberField E] in
theorem cap_split (r : F) (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => (algebraMap F (FiniteAdeleRing (𝓞 F) F) r + d • a) ⊗ₜ[F] x i : Fin n → RA F E)
      = fv F (algebraMap F E r • x) + d • (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) := by
  funext i
  simp only [fv, Pi.add_apply, Pi.smul_apply, TensorProduct.add_tmul, algebraMap_smul]
  congr 1
  · rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

omit [NumberField E] in
theorem cap_tmul_nsmul (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => a ⊗ₜ[F] (d • x) i : Fin n → RA F E)
      = d • (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) := by
  funext i
  simp only [Pi.smul_apply]
  induction d with
  | zero => simp
  | succ d ih => rw [succ_nsmul, succ_nsmul, TensorProduct.tmul_add, ih]

theorem cap_exists_denom (L : Submodule (𝓞 E) (Fin n → E))
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulMemUnitaryExistence.target
  | exact _root_.GlobalTheory.NatMulMemUnitaryExistence.target
  | (apply _root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulMemUnitaryExistence.target ..)

end RationalPoints

theorem hat_rational_points_and_approx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ v, fv F v ∈ (hat F (L : Set (Fin n → E))) ↔ v ∈ L) ∧ (∀ N : ℕ, 0 < N → ∀ z ∈ (hat F (L : Set (Fin n → E))), ∃ x ∈ L, ∃ w ∈ (hat F (L : Set (Fin n → E))), z = fv F x + N • w) ∧ (∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) ∧ ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L hfg hsp
  have h3 : ∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
    have hadd : ∀ z w : Fin n → RA F E, (∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) →
        (∃ x : Fin n → E, w - fv F x ∈ (hat F (L : Set (Fin n → E)))) →
        (∃ x : Fin n → E, z + w - fv F x ∈ (hat F (L : Set (Fin n → E)))) := by
      rintro z w ⟨x, hx⟩ ⟨y, hy⟩
      refine ⟨x + y, ?_⟩
      have := add_mem hx hy
      rw [cap_fv_add]
      convert this using 1
      abel
    have hzero : ∃ x : Fin n → E, (0 : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) :=
      ⟨0, by rw [cap_fv_zero, sub_zero]; exact zero_mem _⟩
    have hgen : ∀ (a : FiniteAdeleRing (𝓞 F) F) (y : Fin n → E), ∃ x : Fin n → E,
        (fun i => a ⊗ₜ[F] y i : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
      intro a y
      obtain ⟨d, hd, hy⟩ := cap_exists_denom L hsp y
      obtain ⟨r, a', ha', rfl⟩ := (GlobalTheory.T.finiteAdele_strong_approximation_mod_nat F d hd).1 a
      refine ⟨algebraMap F E r • y, ?_⟩
      rw [cap_split, add_sub_cancel_left, ← cap_tmul_nsmul]
      exact cap_gen_mem F _ a' ha' _ hy
    have hsingle : ∀ (i : Fin n) (t : RA F E), ∃ x : Fin n → E,
        (Pi.single i t : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
      intro i t
      induction t using TensorProduct.induction_on with
      | zero => simpa using hzero
      | tmul a y =>
        have := hgen a (Pi.single i y)
        convert this using 4
        funext j
        by_cases h : j = i
        · subst h; simp
        · simp [h]
      | add s t hs ht =>
        rw [Pi.single_add]
        exact hadd _ _ hs ht
    intro z
    rw [← Finset.univ_sum_single z]
    exact Finset.sum_induction _ (fun z => ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E))))
      hadd hzero (fun i _ => hsingle i (z i))
  refine ⟨?_, ?_, h3, ?_⟩
  · intro v
    obtain ⟨s, e, c, -, hc, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
    have hv : fv F v = ∑ a, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (e.repr v a) : RA F E) • fv F (e a) := by
      funext i
      have h := congrFun (e.sum_repr v) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      simp only [fv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul]
      rw [← TensorProduct.tmul_sum, h]
    rw [hv, GlobalTheory.T.mem_adelicCompletion_pseudoBasis_iff F E n L e c hc, hc]
    exact forall_congr' fun a => (GlobalTheory.T.adelicCompletion_fractionalIdeal_properties_alt F E).2.1 (c a) _
  · intro N hN z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨r, a', ha', rfl⟩ := (GlobalTheory.T.finiteAdele_strong_approximation_mod_nat F N hN).2 a ha
      refine ⟨algebraMap F E (r : F) • x, ?_, _, cap_gen_mem F _ a' ha' x hx, cap_split F _ _ _ _⟩
      exact L.smul_mem (algebraMap (𝓞 F) (𝓞 E) r) hx
    | zero => exact ⟨0, L.zero_mem, 0, zero_mem _, by simp [cap_fv_zero]⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hz
      obtain ⟨x', hx', w', hw', rfl⟩ := hz'
      refine ⟨x + x', L.add_mem hx hx', w + w', add_mem hw hw', ?_⟩
      rw [cap_fv_add, smul_add]
      abel
    | neg z _ hz =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hz
      refine ⟨-x, L.neg_mem hx, -w, neg_mem hw, ?_⟩
      rw [cap_fv_neg, smul_neg]
      abel
  · intro z
    obtain ⟨x, hx⟩ := h3 z
    obtain ⟨d, hd, hdx⟩ := cap_exists_denom L hsp x
    refine ⟨d, hd, ?_⟩
    have := add_mem (nsmul_mem hx d) (cap_fv_mem F (L : Set (Fin n → E)) _ hdx)
    rw [cap_fv_nsmul, ← smul_add, sub_add_cancel] at this
    exact this

end GlobalTheory.AdLat
