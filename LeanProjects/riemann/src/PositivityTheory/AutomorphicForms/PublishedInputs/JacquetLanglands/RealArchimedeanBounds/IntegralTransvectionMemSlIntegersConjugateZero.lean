import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import GroundTheory.GlobalFields.Adele.Topology

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.CompactSubgroupMembership

variable {F : Type} [Field F] [NumberField F]

def mP (w : Pl F) (c : ℕ) : AddSubgroup (w.adicCompletion F) :=
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c).toAddSubgroup.map
    (w.adicCompletionIntegers F).subtype.toAddMonoidHom

theorem mem_parahoricTimesPrincipalCongruence_iff {w : Pl F} {c : ℕ} {g : GL (Fin 2) (w.adicCompletion F)} :
    g ∈ K1 w c ↔ (∀ a b, g a b ∈ w.adicCompletionIntegers F) ∧
      (∀ a b, (g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b ∈ w.adicCompletionIntegers F) ∧
      g 1 0 ∈ mP w c ∧ g 1 1 - 1 ∈ mP w c := by
  have key : ∀ k : GL (Fin 2) (w.adicCompletionIntegers F),
      k ∈ ((mirab _).comap (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)))) ↔
      k 1 0 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ∧
        k 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c := fun k => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq, map_one]
    change ![0, 1] ᵥ* _ = ![0, 1] ↔ _
    rw [funext_iff, Fin.forall_fin_two]
    simp [Matrix.vecMul, dotProduct]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h1, h2⟩ := (key k).1 hk
    refine ⟨fun a b => (k a b).2, fun a b => ?_, ⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
    rw [← map_inv]; exact ((k⁻¹ : GL (Fin 2) (w.adicCompletionIntegers F)) a b).2
  · rintro ⟨ha, hb, ⟨y, hy, e⟩, ⟨y', hy', e'⟩⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin 2) (w.adicCompletionIntegers F).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin 2) (w.adicCompletionIntegers F) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    refine ⟨k, (key k).2 ⟨?_, ?_⟩, Units.ext rfl⟩
    · rw [show k 1 0 = y from Subtype.ext e.symm]; exact hy
    · rw [show k 1 1 - 1 = y' from Subtype.ext e'.symm]; exact hy'

theorem mem_mP_zero {w : Pl F} {x : w.adicCompletion F} (hx : x ∈ w.adicCompletionIntegers F) : x ∈ mP w 0 :=
  ⟨⟨x, hx⟩, by simp, rfl⟩

theorem mem_O {x : Af F} : x ∈ Ohat F ↔ ∀ w : Pl F, pLoc F w x ∈ w.adicCompletionIntegers F := by
  simp [Ohat, Subring.mem_iInf]

theorem mem_Ov {x : Af F} : x ∈ Ohat F ↔ ∀ w : Pl F, Valued.v (pLoc F w x) ≤ 1 := by
  rw [mem_O]; simp only [HeightOneSpectrum.mem_adicCompletionIntegers]

theorem v_le {x : Af F} (hx : x ∈ Ohat F) (w : Pl F) : Valued.v (pLoc F w x) ≤ 1 := mem_Ov.1 hx w

theorem integral_transvection_mem_slIntegers_conjugate_zero {g : GF F} :
    g ∈ K0 F ↔ (∀ i j, g.val i j ∈ Ohat F) ∧ ∀ i j, (g⁻¹ : GF F).val i j ∈ Ohat F := by
  simp only [K0, Kc, Subgroup.mem_iInf, Subgroup.mem_comap, mem_parahoricTimesPrincipalCongruence_iff, ← map_inv, mem_O]
  constructor
  · intro h
    exact ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2.1 i j⟩
  · rintro ⟨h1, h2⟩ w
    exact ⟨fun i j => h1 i j w, fun i j => h2 i j w, mem_mP_zero (h1 1 0 w),
      mem_mP_zero (sub_mem (h1 1 1 w) (one_mem _))⟩

theorem Kc_le (c : Pl F → ℕ) : Kc c ≤ K0 F := fun g hg => by
  rw [integral_transvection_mem_slIntegers_conjugate_zero]
  simp only [Kc, Subgroup.mem_iInf, Subgroup.mem_comap, mem_parahoricTimesPrincipalCongruence_iff, ← map_inv] at hg
  exact ⟨fun i j => mem_O.2 fun w => (hg w).1 i j, fun i j => mem_O.2 fun w => (hg w).2.1 i j⟩

theorem zc_normal : ((zc F).range).Normal :=
  ⟨fun n hn g => by
    obtain ⟨z, rfl⟩ := hn
    have := Subgroup.mem_center_iff.1 (zc_center z) g
    exact ⟨z, by rw [this, mul_inv_cancel_right]⟩⟩

theorem mem_Hc (c : Pl F → ℕ) (h : GF F) : h ∈ Hc c ↔ ∃ k ∈ Kc c, ∃ z, h = k * zc F z := by
  have := zc_normal (F := F)
  change h ∈ Kc c ⊔ (zc F).range ↔ _
  rw [Subgroup.mem_sup_of_normal_right]
  constructor
  · rintro ⟨k, hk, _, ⟨z, rfl⟩, rfl⟩
    exact ⟨k, hk, z, rfl⟩
  · rintro ⟨k, hk, z, rfl⟩
    exact ⟨k, hk, _, ⟨z, rfl⟩, rfl⟩

theorem det_mem {g : GF F} (h : ∀ i j, g.val i j ∈ Ohat F) : g.val.det ∈ Ohat F := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (h 0 0) (h 1 1)) (mul_mem (h 0 1) (h 1 0))

theorem k_prop {k : GF F} (hk : k ∈ K0 F) (w : Pl F) :
    Valued.v (pLoc F w ((Matrix.GeneralLinearGroup.det k : (Af F)ˣ) : Af F)) = 1 ∧
      max (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) = 1 := by
  obtain ⟨h1, h2⟩ := integral_transvection_mem_slIntegers_conjugate_zero.1 hk
  refine ⟨?_, ?_⟩
  · have hd2 := v_le (det_mem h2) w
    have hdd : k.val.det * (k⁻¹ : GF F).val.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have e1 : Valued.v (pLoc F w k.val.det) * Valued.v (pLoc F w (k⁻¹ : GF F).val.det) = 1 := by
      rw [← map_mul, ← map_mul, hdd, map_one, map_one]
    change Valued.v (pLoc F w k.val.det) = 1
    exact le_antisymm (v_le (det_mem h1) w) (e1 ▸ mul_le_of_le_one_right' hd2)
  · have e : k.val 1 0 * (k⁻¹ : GF F).val 0 1 + k.val 1 1 * (k⁻¹ : GF F).val 1 1 = 1 := by
      have := congrFun (congrFun (Units.mul_inv k) 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at this
      exact this
    have hv : Valued.v (pLoc F w (k.val 1 0) * pLoc F w ((k⁻¹ : GF F).val 0 1) +
        pLoc F w (k.val 1 1) * pLoc F w ((k⁻¹ : GF F).val 1 1)) = 1 := by
      rw [← map_mul, ← map_mul, ← map_add, e, map_one, map_one]
    refine le_antisymm (max_le (v_le (h1 1 0) w) (v_le (h1 1 1) w)) ?_
    refine hv.ge.trans ((Valuation.map_add _ _ _).trans (max_le_max ?_ ?_))
    · rw [map_mul]; exact mul_le_of_le_one_right' (v_le (h2 0 1) w)
    · rw [map_mul]; exact mul_le_of_le_one_right' (v_le (h2 1 1) w)

theorem val_pLoc (w : Pl F) (x : F) :
    Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem int_iff (t : F) : IsIntegral ℤ t ↔ algebraMap F (Af F) t ∈ Ohat F := by
  rw [mem_Ov]
  simp only [val_pLoc]
  constructor
  · intro h w
    exact HeightOneSpectrum.valuation_le_one w (⟨t, h⟩ : 𝓞 F)
  · intro h
    obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F t h
    exact RingOfIntegers.isIntegral_coe r

theorem af_den (a : Af F) : ∃ n : ℕ, n ≠ 0 ∧ (n : Af F) * a ∈ Ohat F := by
  have hU : IsOpen {z : Af F | a - z ∈ Ohat F} :=
    isOpen_Ohat.preimage (f := fun z : Af F => a - z) (by fun_prop)
  obtain ⟨x, hx⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).exists_mem_open hU
    ⟨a, by simp⟩
  obtain ⟨m, hm0, hm⟩ :=
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, ?_⟩
  have h1 : algebraMap F (Af F) (m • x) ∈ Ohat F :=
    mem_Ohat.2 (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F ⟨_, hm⟩)
  have h2 := add_mem h1 (mul_mem (intCast_mem (Ohat F) m) hx)
  have h3 : (m : Af F) * a ∈ Ohat F := by
    convert h2 using 1
    rw [zsmul_eq_mul, map_mul, map_intCast]; ring
  rcases Int.natAbs_eq m with h | h
  · rw [h] at h3; simpa using h3
  · rw [h] at h3; simpa using neg_mem h3

theorem den_ex (g : GF F) : ∃ N : ℕ, N ≠ 0 ∧ ∀ i j, (N : Af F) * g.val i j ∈ Ohat F := by
  choose n hn0 hn using fun p : Fin 2 × Fin 2 => af_den (g.val p.1 p.2)
  refine ⟨∏ p, n p, Finset.prod_ne_zero_iff.2 fun p _ => hn0 p, fun i j => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (i, j))
  rw [hk, Nat.cast_mul, mul_comm ((n (i, j) : ℕ) : Af F), mul_assoc]
  exact mul_mem (natCast_mem _ k) (hn (i, j))

theorem unit_scalar_mem_maximal_compact {u : (Af F)ˣ} (hu : ∀ w : Pl F, Valued.v (pLoc F w (u : Af F)) = 1) :
    zc F u ∈ K0 F ∧ ∀ t ∈ Ohat F, aff u t ∈ K0 F := by
  have hu1 : (u : Af F) ∈ Ohat F := mem_Ov.2 fun w => (hu w).le
  have hu2 : ((u⁻¹ : (Af F)ˣ) : Af F) ∈ Ohat F := by
    refine mem_Ov.2 fun w => ?_
    have : Valued.v (pLoc F w (u : Af F)) * Valued.v (pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    rw [hu w, one_mul] at this
    exact this.le
  refine ⟨integral_transvection_mem_slIntegers_conjugate_zero.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun t ht => integral_transvection_mem_slIntegers_conjugate_zero.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · fin_cases i <;> fin_cases j <;> simp [zc, hu1]
  · rw [show (zc F u)⁻¹ = zc F u⁻¹ from (map_inv (zc F) u).symm]
    fin_cases i <;> fin_cases j <;> simp [-map_inv, zc, hu2]
  · change (!![(u : Af F), t; 0, 1] : Matrix (Fin 2) (Fin 2) (Af F)) i j ∈ Ohat F
    fin_cases i <;> fin_cases j <;> simp [hu1, ht]
  · change (!![((u⁻¹ : (Af F)ˣ) : Af F), -(((u⁻¹ : (Af F)ˣ) : Af F) * t); 0, 1] : Matrix (Fin 2) (Fin 2) (Af F)) i j ∈
      Ohat F
    fin_cases i <;> fin_cases j <;> simp [hu2, mul_mem hu2 ht]

end UpperTheory.Esk.CompactSubgroupMembership

open UpperTheory.Esk.CompactSubgroupMembership in
theorem UpperTheory.Esk.aMem : UpperTheory.Esk.AMem := by
  intro F _ _
  exact ⟨fun g => integral_transvection_mem_slIntegers_conjugate_zero, fun x => mem_Ov, Kc_le, mem_Hc, fun k hk w => k_prop hk w, int_iff, den_ex,
    fun u hu => unit_scalar_mem_maximal_compact hu⟩
