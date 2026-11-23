import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemFractionalIdealGeneratorAtPrimesOverStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularLiftOfUnimodularMod
open NumberField IsDedekindDomain

namespace GlobalTheory
open Formalism.L2.SG.Pf.LatEx

theorem fractionalIdeal_restrictScalars_isLattice_of_tower (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hc : c ≠ 0) :
    Submodule.IsLattice F ((c : Submodule (𝓞 E) E).restrictScalars (𝓞 F)) := by
  refine ⟨?_, ?_⟩
  · exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl c).restrictScalars
  · obtain ⟨x, hxc, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := (c : Submodule (𝓞 E) E))
      (by rwa [Ne, FractionalIdeal.coeToSubmodule_eq_bot])
    rw [eq_top_iff]
    intro y _
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) (y / x)
    dsimp only at hrs
    have hs0 : (s : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    have hspan : Ideal.span {(s : 𝓞 E)} ≠ ⊥ := by simpa using hs0
    have hm0 : Ideal.absNorm (Ideal.span {(s : 𝓞 E)}) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {(s : 𝓞 E)}))
    set m := Ideal.absNorm (Ideal.span {(s : 𝓞 E)})
    have hmem : (algebraMap (𝓞 E) E (u * r)) * x ∈ c :=
      (c : Submodule (𝓞 E) E).smul_mem (u * r) hxc
    have hyeq : y = ((m : F)⁻¹) • ((algebraMap (𝓞 E) E (u * r)) * x) := by
      have hu' : algebraMap (𝓞 E) E u * algebraMap (𝓞 E) E s = (m : E) := by
        rw [← map_mul, hu, map_natCast]
      have hmE : (m : E) ≠ 0 := Nat.cast_ne_zero.mpr hm0
      rw [Algebra.smul_def, map_inv₀, map_natCast, map_mul]
      have hyx : y = algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s * x := by
        have hsE : algebraMap (𝓞 E) E s ≠ 0 := by simpa using hs0
        rw [← hrs]; field_simp
      rw [hyx, ← hu']
      have hsE : algebraMap (𝓞 E) E s ≠ 0 := by simpa using hs0
      have huE : algebraMap (𝓞 E) E u ≠ 0 := by
        intro h; rw [h, zero_mul] at hu'; exact hmE hu'.symm
      field_simp
    rw [hyeq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem exists_basis_latSpanV_eq_of_finrank_two (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (hE : Module.finrank F E = 2) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hc : c ≠ 0) :
    ∃ (e : Fin 2 → E) (b : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), LinearIndependent F e ∧ b ≠ 0 ∧
      (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) =
        latSpanV (Fin.snoc (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (fun _ => 1) b) e := by
  have hL := fractionalIdeal_restrictScalars_isLattice_of_tower F E c hc
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hE
  let w := Module.finBasisOfFinrankEq F E hE
  obtain ⟨e, b, he, -, hb, heq⟩ := satBasisV_holds F E _ hL 1 w w.linearIndependent (fun _ => 1)
    (fun _ => one_ne_zero)
  refine ⟨e, b, he, hb, ?_⟩
  rw [← heq, w.span_eq]
  simp

theorem basis_repr_mem_of_mem_latSpanV_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (B : Module.Basis (Fin 2) F E) (C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    {z : E} (hz : z ∈ latSpanV C B) (i : Fin 2) : B.repr z i ∈ C i := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, x, hx, rfl⟩ := hy
    rw [map_smul, B.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; simpa using hx
    · rw [smul_zero]; exact (C i : Submodule (𝓞 F) F).zero_mem
  | zero => rw [map_zero, Finsupp.zero_apply]; exact (C i : Submodule (𝓞 F) F).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add, Finsupp.add_apply]; exact (C i : Submodule (𝓞 F) F).add_mem hx hy
  | smul r x _ hx =>
    rw [← algebraMap_smul F r x, map_smul, Finsupp.smul_apply, algebraMap_smul]
    exact (C i : Submodule (𝓞 F) F).smul_mem r hx

theorem algebraMap_ringOfIntegers_tower_mul_eq_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (π : 𝓞 F) (z : E) :
    algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) * z = (algebraMap (𝓞 F) F π) • z := by
  rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem basis_repr_mem_of_mem_map_mul_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (B : Module.Basis (Fin 2) F E) (C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hc : (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) = latSpanV C B) (p : Ideal (𝓞 F)) {a : E}
    (ha : a ∈ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) (i : Fin 2) :
    B.repr a i ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * C i := by
  let T : Submodule (𝓞 F) F := (↑((p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * C i) : Submodule (𝓞 F) F)
  have hcoord : ∀ z ∈ c, B.repr z i ∈ C i := fun z hz =>
    basis_repr_mem_of_mem_latSpanV_two B C (by rw [← hc]; exact hz) i
  have hgen : ∀ π ∈ p, ∀ z ∈ c,
      B.repr (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) * z) i ∈ T := by
    intro π hπ z hz
    rw [algebraMap_ringOfIntegers_tower_mul_eq_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hπ) (hcoord z hz)
  have hq : ∀ q ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p, ∀ z ∈ c,
      B.repr (algebraMap (𝓞 E) E q * z) i ∈ T := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨π, hπ, rfl⟩ := hy
      exact hgen π hπ
    | zero => intro z _; simp [T.zero_mem]
    | add x y _ _ hx hy =>
      intro z hz; rw [map_add, add_mul, map_add, Finsupp.add_apply]; exact T.add_mem (hx z hz) (hy z hz)
    | smul r x _ hx =>
      intro z hz
      have e1 : algebraMap (𝓞 E) E (r * x) * z = algebraMap (𝓞 E) E x * (algebraMap (𝓞 E) E r * z) := by
        rw [RingHom.map_mul]; ring
      rw [smul_eq_mul, e1]
      exact hx _ ((c : Submodule (𝓞 E) E).smul_mem r hz)
  refine FractionalIdeal.mul_induction_on (C := fun a => B.repr a i ∈ T) ha ?_ ?_
  · intro u hu z hz
    obtain ⟨q, hq', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hu
    exact hq q hq' z hz
  · intro x y hx hy
    simp only [map_add, Finsupp.add_apply]
    exact T.add_mem hx hy

theorem mem_map_mul_of_basis_repr_mem_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (B : Module.Basis (Fin 2) F E) (C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hc : (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) = latSpanV C B) (p : Ideal (𝓞 F)) {a : E}
    (ha : ∀ i, B.repr a i ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * C i) :
    a ∈ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  let M : Submodule (𝓞 E) E := (↑(((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) : Submodule (𝓞 E) E)
  have hterm : ∀ i, B.repr a i • B i ∈ M := by
    intro i
    refine FractionalIdeal.mul_induction_on (C := fun u => u • B i ∈ M) (ha i) ?_ ?_
    · intro u hu x hx
      obtain ⟨π, hπ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hu
      have hxc : x • B i ∈ c := by
        have : x • B i ∈ latSpanV C B := Submodule.subset_span ⟨i, x, hx, rfl⟩
        rw [← hc] at this; exact this
      show (algebraMap (𝓞 F) F π * x) • B i ∈ M
      rw [mul_smul, ← algebraMap_ringOfIntegers_tower_mul_eq_smul]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _
        (Ideal.mem_map_of_mem _ hπ)) hxc
    · intro x y hx hy
      show (x + y) • B i ∈ M
      rw [add_smul]; exact M.add_mem hx hy
  have hsum := B.sum_repr a
  rw [Fin.sum_univ_two] at hsum
  show a ∈ M
  rw [← hsum]
  exact M.add_mem (hterm 0) (hterm 1)

theorem exists_mem_fractionalIdeal_primitive_local_generator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ (∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q → a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) ∧ ∀ p : Ideal (𝓞 F), p.IsMaximal → a ∉ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  intro F E _ _ _ _ _ hE c hc N hN
  obtain ⟨e, b, he, hb, hce⟩ := exists_basis_latSpanV_eq_of_finrank_two F E hE c hc
  let B : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank he (by simp [hE])
  have hBe : ⇑B = e := coe_basisOfLinearIndependentOfCardEqFinrank he _
  let C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F := Fin.snoc (n := 1) (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (fun _ => 1) b
  have hc' : (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) = latSpanV C B := by rw [hBe]; exact hce
  have hC0 : C 0 = 1 := rfl
  have hC1 : C 1 = b := rfl
  have hspanN : Ideal.span {N} ≠ ⊥ := by simpa using hN
  have hm0 : Ideal.absNorm (Ideal.span {N}) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hmN : ((Ideal.absNorm (Ideal.span {N}) : ℕ) : 𝓞 E) ∈ Ideal.span {N} := Ideal.absNorm_mem _
  set m := Ideal.absNorm (Ideal.span {N})
  obtain ⟨a₀, ha₀c, ha₀⟩ := GlobalTheory.T.exists_mem_fractionalIdeal_generator_at_primes_over' E c hc (m : 𝓞 E) (Nat.cast_ne_zero.mpr hm0)
  have hco : ∀ i, B.repr a₀ i ∈ C i := fun i =>
    basis_repr_mem_of_mem_latSpanV_two B C (show a₀ ∈ latSpanV C B by rw [← hc']; exact ha₀c) i
  obtain ⟨x₀, hx₀⟩ := (FractionalIdeal.mem_one_iff _).mp (hC0 ▸ hco 0)
  have hy₀ : B.repr a₀ 1 ∈ b := hC1 ▸ hco 1
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  have hmono : ∀ (I J : Ideal (𝓞 E)), I ≤ J → (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c ≤
      (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
    intro I J hIJ
    have : (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ J := (FractionalIdeal.coeIdeal_le_coeIdeal E).mpr hIJ
    gcongr
  obtain ⟨s, t, ht, hst⟩ := GlobalTheory.exists_unimodular_lift_of_unimodular_mod F b hb (m : 𝓞 F) x₀ (B.repr a₀ 1)
    (Nat.cast_ne_zero.mpr hm0) hy₀ (by
      rintro p hp hnp ⟨hxp, hyp⟩
      have hmem := mem_map_mul_of_basis_repr_mem_two B C c hc' p (a := a₀) (by
        refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · rw [← hx₀, hC0, mul_one]; exact FractionalIdeal.mem_coeIdeal_of_mem _ hxp
        · exact hyp)
      obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) p (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
      have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ Q := Ideal.map_le_iff_le_comap.mpr hQp.ge
      have hmQ : (m : 𝓞 E) ∈ Q := hle (by
        rw [← map_natCast (algebraMap (𝓞 F) (𝓞 E)) m]; exact Ideal.mem_map_of_mem _ hnp)
      exact ha₀ Q hQ hmQ (hmono _ _ hle hmem))
  let w : E := (algebraMap (𝓞 F) F s) • B 0 + t • B 1
  have hw : w ∈ c := by
    have : w ∈ latSpanV C B := Submodule.add_mem _
      (Submodule.subset_span ⟨0, _, (FractionalIdeal.mem_one_iff _).mpr ⟨s, rfl⟩, rfl⟩)
      (Submodule.subset_span ⟨1, t, ht, rfl⟩)
    rw [← hc'] at this; exact this
  have hmw : (m : F) • w = algebraMap (𝓞 E) E (m : 𝓞 E) * w := by
    rw [map_natCast, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  refine ⟨a₀ + (m : F) • w, ?_, ?_, ?_⟩
  · rw [hmw]; exact (c : Submodule (𝓞 E) E).add_mem ha₀c ((c : Submodule (𝓞 E) E).smul_mem _ hw)
  · intro Q hQ hNQ ha
    have hmQ : (m : 𝓞 E) ∈ Q := (Ideal.span_singleton_le_iff_mem Q).mpr hNQ hmN
    have h2 : (m : F) • w ∈ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
      rw [hmw]; exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hmQ) hw
    refine ha₀ Q hQ hmQ ?_
    have e2 : a₀ = (a₀ + (m : F) • w) - (m : F) • w := by abel
    rw [e2]
    exact Submodule.sub_mem (↑((Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) : Submodule (𝓞 E) E) ha h2
  · intro p hp ha
    have h := basis_repr_mem_of_mem_map_mul_two B C c hc' p ha
    have hr : ∀ i, B.repr (a₀ + (m : F) • w) i = B.repr a₀ i + (m : F) * ((algebraMap (𝓞 F) F s) *
        (Finsupp.single 0 1 : Fin 2 →₀ F) i + t * (Finsupp.single 1 1 : Fin 2 →₀ F) i) := by
      intro i
      simp only [w, map_add, map_smul, B.repr_self, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    refine hst p hp ⟨?_, ?_⟩
    · have h0 := h 0
      rw [hC0, mul_one, hr 0] at h0
      obtain ⟨x', hx'p, hx'⟩ := (FractionalIdeal.mem_coeIdeal _).mp h0
      have : x' = x₀ + (m : 𝓞 F) * s := by
        apply IsFractionRing.injective (𝓞 F) F
        rw [hx', map_add, map_mul, map_natCast, hx₀]
        simp
      exact this ▸ hx'p
    · have h1 := h 1
      rw [hC1, hr 1] at h1
      convert h1 using 1
      simp

end GlobalTheory
