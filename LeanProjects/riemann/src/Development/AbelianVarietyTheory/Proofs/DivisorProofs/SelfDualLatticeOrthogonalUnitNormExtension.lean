import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory

theorem selfDual_orthogonal_unit_step : ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
    [FiniteDimensional K.E V] (h : V → V → K.E), (∀ y y' z, h (y + y') z = h y z + h y' z) →
    (∀ (a : K.E) y z, h (a • y) z = a * h y z) → (∀ y z, h z y = K.c (h y z)) →
    ∀ L : Submodule K.O V, L.FG → Submodule.span K.E (L : Set V) = ⊤ →
    (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∀ (k : ℕ) (f : Fin k → V), (∀ i, f i ∈ L) → (∀ i j, i ≠ j → h (f i) (f j) = 0) →
    (∀ i, ∃ t : K.O, IsUnit t ∧ h (f i) (f i) = algebraMap K.O K.E t) → k < Module.finrank K.E V →
    ∃ y ∈ L, (∀ i, h y (f i) = 0) ∧ ∃ t : K.O, IsUnit t ∧ h y y = algebraMap K.O K.E t := by
  intro K V _ _ _ _ _ h hadd hsmul hsym L hLfg hLspan hdual k f hfL horth hunit hk
  have alg_inj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
  have hadd2 : ∀ y z z', h y (z + z') = h y z + h y z' := by
    intro y z z'
    rw [hsym (z + z') y, hadd, map_add, ← hsym, ← hsym]
  have hsmul2 : ∀ (a : K.E) y z, h y (a • z) = K.c a * h y z := by
    intro a y z
    rw [hsym (a • z) y, hsmul, map_mul, ← hsym]
  let H1 : V → V →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => h y z, map_add' := fun y y' => hadd y y' z,
      map_smul' := fun a y => by simp [hsmul] }
  let H2 : V → V →+ K.E := fun y => AddMonoidHom.mk' (fun z => h y z) (hadd2 y)
  have h0l : ∀ z, h 0 z = 0 := fun z => (H1 z).map_zero
  have hsub1 : ∀ a b z, h (a - b) z = h a z - h b z := fun a b z => (H1 z).map_sub a b
  have hsub2 : ∀ y a b, h y (a - b) = h y a - h y b := fun y a b => (H2 y).map_sub a b
  have hsum1 : ∀ (g : Fin k → V) z, h (∑ i, g i) z = ∑ i, h (g i) z :=
    fun g z => map_sum (H1 z) g Finset.univ
  have hsum2 : ∀ (g : Fin k → V) y, h y (∑ i, g i) = ∑ i, h y (g i) :=
    fun g y => map_sum (H2 y) g Finset.univ
  have hsmulO : ∀ (o : K.O) (v : V), (algebraMap K.O K.E o) • v = o • v :=
    fun o v => algebraMap_smul K.E o v
  have hint : ∀ y ∈ L, ∀ z ∈ L, ∃ a : K.O, h y z = algebraMap K.O K.E a := by
    intro y hy z hz
    obtain ⟨a, ha⟩ := (hdual y).1 hy z hz
    exact ⟨a, ha.symm⟩
  have hs : ∀ i, h (f i) (f i) ≠ 0 := by
    intro i
    obtain ⟨t, ht, he⟩ := hunit i
    rw [he]
    intro h0
    apply ht.ne_zero
    apply alg_inj
    rw [h0, map_zero]
  let M : Submodule K.O V :=
    { carrier := {y | y ∈ L ∧ ∀ i, h y (f i) = 0}
      add_mem' := fun {a b} ha hb => ⟨L.add_mem ha.1 hb.1, fun i => by rw [hadd, ha.2 i, hb.2 i, add_zero]⟩
      zero_mem' := ⟨L.zero_mem, fun i => h0l (f i)⟩
      smul_mem' := fun o y hy => ⟨L.smul_mem o hy.1, fun i => by rw [← hsmulO, hsmul, hy.2 i, mul_zero]⟩ }
  have memM : ∀ y, y ∈ M ↔ y ∈ L ∧ ∀ i, h y (f i) = 0 := fun y => Iff.rfl

  have hP : ∀ l ∈ L, ∃ p ∈ M, (∀ w, (∀ i, h w (f i) = 0) → h w l = h w p) ∧
      (l ∉ Submodule.span K.E (Set.range f) → p ≠ 0) := by
    intro l hl
    set g : Fin k → V := fun i => (h l (f i) / h (f i) (f i)) • f i with hg
    have hgL : ∀ i, g i ∈ L := by
      intro i
      obtain ⟨a, ha⟩ := hint l hl (f i) (hfL i)
      obtain ⟨t, ht, he⟩ := hunit i
      have hc : h l (f i) / h (f i) (f i) = algebraMap K.O K.E (a * ↑ht.unit⁻¹) := by
        rw [ha, he, map_mul, div_eq_mul_inv]
        congr 1
        exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, IsUnit.mul_val_inv, map_one])
      simp only [hg]
      rw [hc, hsmulO]
      exact L.smul_mem _ (hfL i)
    refine ⟨l - ∑ i, g i, (memM _).2 ⟨L.sub_mem hl (L.sum_mem fun i _ => hgL i), fun j => ?_⟩,
      fun w hw => ?_, fun hn h0 => ?_⟩
    · rw [hsub1, hsum1, Finset.sum_eq_single j]
      · simp only [hg, hsmul]
        rw [div_mul_cancel₀ _ (hs j), sub_self]
      · intro i _ hij
        simp only [hg, hsmul, horth i j hij, mul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    · rw [hsub2, hsum2, Finset.sum_eq_zero, sub_zero]
      intro i _
      simp only [hg, hsmul2, hw i, mul_zero]
    · apply hn
      rw [sub_eq_zero] at h0
      rw [h0]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have hspan : Submodule.span K.E (Set.range f) ≠ ⊤ := by
    intro htop
    have h1 := finrank_range_le_card (R := K.E) f
    rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at h1
    omega
  obtain ⟨l, hl, hlnot⟩ : ∃ l ∈ L, l ∉ Submodule.span K.E (Set.range f) := by
    by_contra hcon
    push_neg at hcon
    apply hspan
    rw [eq_top_iff, ← hLspan]
    exact Submodule.span_le.2 (fun x hx => hcon x hx)
  have hMne : M ≠ ⊥ := by
    obtain ⟨p, hpM, -, hp0⟩ := hP l hl
    intro hb
    rw [hb] at hpM
    exact hp0 hlnot ((Submodule.mem_bot _).1 hpM)

  by_contra hno
  push_neg at hno
  let Q : Submodule K.O K.E := Submodule.map (Algebra.linearMap K.O K.E) (IsLocalRing.maximalIdeal K.O)
  have hQsmul : ∀ (o : K.O) x, x ∈ Q → algebraMap K.O K.E o * x ∈ Q := by
    intro o x hx
    rw [← Algebra.smul_def]
    exact Q.smul_mem o hx
  have hQdiag : ∀ y ∈ M, h y y ∈ Q := by
    intro y hy
    obtain ⟨t, ht⟩ := hint y hy.1 y hy.1
    refine Submodule.mem_map.2 ⟨t, ?_, by rw [Algebra.linearMap_apply, ht]⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hno y hy.1 hy.2 t hu ht
  have hpol : ∀ y ∈ M, ∀ z ∈ M, ∀ o : K.O,
      algebraMap K.O K.E o * h z y + K.c (algebraMap K.O K.E o) * h y z ∈ Q := by
    intro y hy z hz o
    obtain ⟨μ, hμ⟩ := K.c_int o
    have hw : y + (algebraMap K.O K.E o) • z ∈ M := by
      rw [hsmulO]
      exact M.add_mem hy (M.smul_mem o hz)
    have e : algebraMap K.O K.E o * h z y + K.c (algebraMap K.O K.E o) * h y z =
        h (y + (algebraMap K.O K.E o) • z) (y + (algebraMap K.O K.E o) • z) - h y y
          - algebraMap K.O K.E o * (algebraMap K.O K.E μ * h z z) := by
      simp only [hadd, hadd2, hsmul, hsmul2, hμ]
      ring
    rw [e]
    exact Q.sub_mem (Q.sub_mem (hQdiag _ hw) (hQdiag _ hy)) (hQsmul _ _ (hQsmul _ _ (hQdiag _ hz)))
  have hQall : ∀ y ∈ M, ∀ z ∈ M, h y z ∈ Q := by
    intro y hy z hz
    obtain ⟨a, b, hab, hnot⟩ := K.c_res
    have h1 := hpol y hy z hz 1
    have h2 := hpol y hy z hz a
    simp only [map_one, one_mul] at h1
    rw [hab] at h2
    have h3 : algebraMap K.O K.E (a - b) * h y z ∈ Q := by
      have := Q.sub_mem (hQsmul a _ h1) h2
      convert this using 1
      rw [map_sub]
      ring
    obtain ⟨e, he⟩ := hint y hy.1 z hz.1
    rw [he, ← map_mul] at h3
    obtain ⟨m', hm', hm'e⟩ := Submodule.mem_map.1 h3
    rw [Algebra.linearMap_apply] at hm'e
    have hme := alg_inj hm'e
    rw [hme] at hm'
    rw [he]
    exact Submodule.mem_map.2 ⟨e,
      ((IsLocalRing.maximalIdeal.isMaximal K.O).isPrime.mem_or_mem hm').resolve_left hnot, rfl⟩

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hπm : IsLocalRing.maximalIdeal K.O = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hπmem : π ∈ IsLocalRing.maximalIdeal K.O := by
    rw [hπm]; exact Ideal.mem_span_singleton_self π
  have hπ0 : algebraMap K.O K.E π ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    apply alg_inj
    rw [h0, map_zero]
  have hle : M ≤ IsLocalRing.maximalIdeal K.O • M := by
    intro w hw
    have hw' : (algebraMap K.O K.E π)⁻¹ • w ∈ M := by
      refine (memM _).2 ⟨(hdual _).2 fun l hl => ?_, fun i => by rw [hsmul, hw.2 i, mul_zero]⟩
      obtain ⟨p, hp, hpw, -⟩ := hP l hl
      rw [hsmul, hpw w hw.2]
      obtain ⟨b, hb, hbe⟩ := Submodule.mem_map.1 (hQall w hw p hp)
      rw [hπm, Ideal.mem_span_singleton'] at hb
      obtain ⟨d, rfl⟩ := hb
      rw [← hbe, Algebra.linearMap_apply, map_mul]
      exact ⟨d, by field_simp⟩
    have hweq : w = π • ((algebraMap K.O K.E π)⁻¹ • w) := by
      rw [← hsmulO, smul_smul, mul_inv_cancel₀ hπ0, one_smul]
    rw [hweq]
    exact Submodule.smul_mem_smul hπmem hw'
  have hfg : M.FG := Submodule.FG.of_le hLfg (fun y hy => hy.1)
  exact hMne (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle
    (IsLocalRing.maximalIdeal_le_jacobson _))

end GlobalTheory
