import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.Lv

open IsDedekindDomain.HeightOneSpectrum

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j : Fin m) : B.A := ∑ i, e.symm (Z i j) • b i

theorem repr_col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j i : Fin m) :
    b.repr (col e b Z j) i = e.symm (Z i j) := by
  rw [col, Module.Basis.repr_sum_self]

theorem repr_sum_smul_col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (c : Fin m → K.E) (i : Fin m) :
    b.repr (∑ l, c l • col e b Z l) i = e.symm ((Z *ᵥ fun l => e (c l)) i) := by
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, repr_col,
    smul_eq_mul, Matrix.mulVec, dotProduct, map_mul, RingEquiv.symm_apply_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem mul_col (a : B.A) (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j : Fin m) :
    a * col e b Z j = col e b (GlobalTheory.TwLat.mulMat e b a * Z) j := by
  apply b.repr.injective
  ext i
  rw [repr_col]
  have h2 := congrFun (LinearMap.toMatrix_mulVec_repr b b (LinearMap.mulLeft K.E a) (col e b Z j)) i
  simp only [LinearMap.mulLeft_apply] at h2
  rw [← h2]
  simp only [Matrix.mulVec, dotProduct, GlobalTheory.TwLat.mulMat, Matrix.mul_apply, Matrix.map_apply, repr_col, map_sum,
    map_mul, RingEquiv.symm_apply_apply]

theorem mulMat_one_add (t : K.E) (x : B.A) :
    GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.E B.A t * x) = 1 + e t • GlobalTheory.TwLat.mulMat e b x := by
  ext i j
  simp only [GlobalTheory.TwLat.mulMat, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, add_mul, one_mul,
    mul_assoc, ← Algebra.smul_def, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, map_mul,
    Matrix.add_apply, Matrix.smul_apply, Module.Basis.repr_self, Matrix.one_apply, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem sum_smul_col_inj (g : GLw m w) (c c' : Fin m → K.E)
    (h : ∑ l, c l • col e b g.val l = ∑ l, c' l • col e b g.val l) : c = c' := by
  have h1 : g.val *ᵥ (fun l => e (c l)) = g.val *ᵥ (fun l => e (c' l)) := by
    funext i
    have := congrArg (fun x => b.repr x i) h
    simp only [repr_sum_smul_col] at this
    exact e.symm.injective this
  have h2 := congrArg (fun v => (g⁻¹).val *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h2
  funext l
  exact e.injective (congrFun h2 l)

theorem mul_le_self_iff (a b : WithZero (Multiplicative ℤ)) (ha : a ≠ 0) : a * b ≤ a ↔ b ≤ 1 := by
  constructor
  · intro h
    have : a⁻¹ * (a * b) ≤ a⁻¹ * a := by gcongr
    rwa [← mul_assoc, inv_mul_cancel₀ ha, one_mul] at this
  · intro h
    exact mul_le_of_le_one_right' h

end GlobalTheory.TwLat.Lv

namespace GlobalTheory.TwLat.Lv

open IsDedekindDomain.HeightOneSpectrum

theorem valued_uniformizerPower_completion_eq_exp_neg {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
    (e : K.E ≃+* w.adicCompletion E) (hval : ∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) (t : K.O) (k : ℕ)
    (ht : t ≠ 0) (hk : GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k) :
    Valued.v (e (algebraMap K.O K.E t)) = WithZero.exp (-(k : ℤ)) := by
  have hne : e (algebraMap K.O K.E t) ≠ 0 := by
    intro h
    apply ht
    have h1 : algebraMap K.O K.E t = 0 := e.injective (h.trans (map_zero e).symm)
    exact IsFractionRing.injective K.O K.E (h1.trans (map_zero _).symm)
  have hv : Valued.v (e (algebraMap K.O K.E t)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
  rw [hval, ordL, dif_neg hv] at hk
  rw [← WithZero.coe_unzero hv, WithZero.exp]
  congr 1
  rw [← ofAdd_toAdd (WithZero.unzero hv)]
  congr 1
  omega

theorem level_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (t : K.O) (k : ℕ), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ g N : GLw m w, N.val = GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.O B.A t * B.g) → ((g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e he hint hval B m b t k hs hk g N hN
  have hv := valued_uniformizerPower_completion_eq_exp_neg e hval t k hs.1 hk
  obtain ⟨c, hc⟩ : ∃ c, c = e (algebraMap K.O K.E t) := ⟨_, rfl⟩
  rw [← hc] at hv
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin m) (Fin m) (w.adicCompletion E),
      Y = (g⁻¹).val * GlobalTheory.TwLat.mulMat e b B.g * g.val := ⟨_, rfl⟩
  have hA : (g⁻¹ * N * g).val = 1 + c • Y := by
    rw [Units.val_mul, Units.val_mul, hN, IsScalarTower.algebraMap_apply K.O K.E B.A, mulMat_one_add, ← hc, hY,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hent : ∀ i j, (g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j = c * Y i j := by
    intro i j
    rw [hA]
    simp
  have hexp : WithZero.exp (-(k : ℤ)) ≠ 0 := WithZero.exp_ne_zero
  have hcoef : (∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(k : ℤ))) ↔ ∀ i j, Valued.v (Y i j) ≤ 1 := by
    simp only [hent, map_mul, hv]
    exact forall_congr' fun i => forall_congr' fun j => mul_le_self_iff _ _ hexp

  have hgY : g.val * Y = GlobalTheory.TwLat.mulMat e b B.g * g.val := by
    rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hgcol : ∀ j, B.g * col e b g.val j = ∑ l, e.symm (Y l j) • col e b g.val l := by
    intro j
    rw [mul_col, ← hgY]
    apply b.repr.injective
    ext i
    rw [repr_sum_smul_col, repr_col]
    simp only [RingEquiv.apply_symm_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hlat : (∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) ↔ ∀ i j, Valued.v (Y i j) ≤ 1 := by
    constructor
    · intro hst i j
      have hmem : B.g * col e b g.val j ∈ GlobalTheory.TwLat.lat e b g :=
        hst _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun K.O).mp hmem
      have ho' : ∑ l, algebraMap K.O K.E (o l) • col e b g.val l = ∑ l, e.symm (Y l j) • col e b g.val l := by
        rw [← hgcol j, ← ho]
        exact Finset.sum_congr rfl fun l _ => algebraMap_smul K.E (o l) _
      have := congrFun (sum_smul_col_inj e b g _ _ ho') i
      have hi := (hint (algebraMap K.O K.E (o i))).mp ⟨o i, rfl⟩
      rw [this, RingEquiv.apply_symm_apply] at hi
      exact hi
    · intro hYi y hy
      have hle : GlobalTheory.TwLat.lat e b g ≤ (GlobalTheory.TwLat.lat e b g).comap (LinearMap.mulLeft K.O B.g) := by
        rw [GlobalTheory.TwLat.lat, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        show B.g * col e b g.val j ∈ GlobalTheory.TwLat.lat e b g
        rw [hgcol j]
        refine Submodule.sum_mem _ fun l _ => ?_
        obtain ⟨o, ho⟩ := (hint (e.symm (Y l j))).mpr (by rw [RingEquiv.apply_symm_apply]; exact hYi l j)
        rw [← ho, algebraMap_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
      exact hle hy

  have hK : (∀ i j, Valued.v (Y i j) ≤ 1) → g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w m := by
    intro hYi
    haveI : IsLocalRing (Ov E w) := inferInstanceAs (IsLocalRing (w.adicCompletionIntegers E))
    have hcS : c ∈ Ov E w := by
      show c ∈ w.adicCompletionIntegers E
      rw [mem_adicCompletionIntegers, hv]
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    let c' : Ov E w := ⟨c, hcS⟩
    let Y' : Matrix (Fin m) (Fin m) (Ov E w) := fun i j =>
      ⟨Y i j, by show Y i j ∈ w.adicCompletionIntegers E; rw [mem_adicCompletionIntegers]; exact hYi i j⟩
    let A' : Matrix (Fin m) (Fin m) (Ov E w) := 1 + c' • Y'
    have hmap : A'.map (Ov E w).subtype = (g⁻¹ * N * g).val := by
      rw [hA]
      ext i j
      simp only [A', Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        map_add, map_mul]
      split_ifs <;> simp [c', Y']
    have hc'nu : ¬ IsUnit c' := by
      rintro ⟨u, hu⟩
      have h1 : c * ((u⁻¹ : (Ov E w)ˣ) : Ov E w) = 1 := by
        have := congrArg Subtype.val (Units.mul_inv u)
        rw [hu] at this
        exact this
      obtain ⟨o, ho⟩ := (hint (e.symm ((u⁻¹ : (Ov E w)ˣ) : Ov E w))).mpr (by
        rw [RingEquiv.apply_symm_apply]
        exact (mem_adicCompletionIntegers _ _ _).mp ((u⁻¹ : (Ov E w)ˣ) : Ov E w).2)
      have h2 : algebraMap K.O K.E (t * o) = 1 := by
        apply e.injective
        rw [map_mul, map_mul, ho, RingEquiv.apply_symm_apply, ← hc, h1, map_one]
      have h3 : t * o = 1 := IsFractionRing.injective K.O K.E (h2.trans (map_one _).symm)
      exact (IsLocalRing.mem_maximalIdeal t).mp hs.2.1 ⟨⟨t, o, h3, by rw [mul_comm]; exact h3⟩, rfl⟩
    have hres0 : IsLocalRing.residue (Ov E w) c' = 0 :=
      (IsLocalRing.residue_eq_zero_iff c').mpr ((IsLocalRing.mem_maximalIdeal c').mpr hc'nu)
    have hdet : IsUnit A'.det := by
      apply (isUnit_map_iff (IsLocalRing.residue (Ov E w)) _).mp
      rw [RingHom.map_det]
      have : (IsLocalRing.residue (Ov E w)).mapMatrix A' = 1 := by
        ext i j
        simp [A', hres0, Matrix.one_apply]
      rw [this, Matrix.det_one]
      exact isUnit_one
    have hU : IsUnit A' := (Matrix.isUnit_iff_isUnit_det A').mpr hdet
    refine ⟨hU.unit, ?_⟩
    apply Units.ext
    rw [← hmap]
    rfl
  constructor
  · rintro ⟨-, h⟩
    exact hlat.2 (hcoef.1 h)
  · intro h
    have h' := hlat.1 h
    exact ⟨hK h', hcoef.2 h'⟩

end GlobalTheory.TwLat.Lv
