import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralIdx
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralRed
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform

noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.UG.P Formalism.BasicNotions Formalism.FrobeniusOrbits
open scoped TensorProduct

section Order

theorem bc_injective {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (f : A →+* B) (hf : Function.Injective f) : Function.Injective (bc (n := n) f) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg (fun u : GL n B => (u : Matrix n n B)) hxy
  ext i j
  exact hf (congrFun (congrFun h i) j)

theorem closure_upperUni_pow {A : Type} [CommRing A] [Nontrivial A] (k g : ℕ) [Fact g.Prime] [CharP A g]
    (x : GL (Fin k) A) (hx : x ∈ Subgroup.closure (upperUni k A)) : x ^ (g ^ k) = 1 := by
  have hg : g.Prime := Fact.out
  have hpow : ∀ x : GL (Fin k) A, Formalism.MainNotions.StandardLattice.IsUnitri (x : Matrix (Fin k) (Fin k) A) → x ^ (g ^ k) = 1 := by
    intro x hx
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact Formalism.MainNotions.Gaps.MI.isUnitri_pow_char g hx
  let U : Subgroup (GL (Fin k) A) :=
    { carrier := {x | Formalism.MainNotions.StandardLattice.IsUnitri (x : Matrix (Fin k) (Fin k) A)}
      mul_mem' := fun {a b} ha hb => by
        show Formalism.MainNotions.StandardLattice.IsUnitri ((a * b : GL (Fin k) A) : Matrix (Fin k) (Fin k) A)
        rw [Units.val_mul]
        exact Formalism.MainNotions.Gaps.MI.isUnitri_mul ha hb
      one_mem' := by
        show Formalism.MainNotions.StandardLattice.IsUnitri ((1 : GL (Fin k) A) : Matrix (Fin k) (Fin k) A)
        rw [Units.val_one]
        exact Formalism.MainNotions.Gaps.MI.isUnitri_one
      inv_mem' := fun {a} ha => by
        show Formalism.MainNotions.StandardLattice.IsUnitri ((a⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A)
        have hpos : 0 < g ^ k := pow_pos hg.pos k
        have h1 : a ^ (g ^ k - 1) * a = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel hpos]
          exact hpow a ha
        have h2 : a⁻¹ = a ^ (g ^ k - 1) := (eq_inv_of_mul_eq_one_left h1).symm
        rw [h2, Units.val_pow_eq_pow_val]
        exact Formalism.MainNotions.Gaps.MI.isUnitri_pow ha _ }
  have hle : Subgroup.closure (upperUni k A) ≤ U := by
    rw [Subgroup.closure_le]
    intro y hy
    exact ⟨fun i j hij => (hy i j).1 hij, fun i => (hy i i).2⟩
  exact hpow x (hle hx)

theorem local_gpow {O : Type} [CommRing O] [IsLocalRing O] (k g : ℕ) (hg : g.Prime)
    (hgm : (g : O) ∈ IsLocalRing.maximalIdeal O) (w : GL (Fin k) O)
    (hw : redGL (IsLocalRing.maximalIdeal O) w ∈ Subgroup.closure (upperUni k _))
    (n : ℕ) (hn : 0 < n) (hwn : w ^ n = 1) : ∃ N : ℕ, w ^ (g ^ N) = 1 := by
  have : Fact g.Prime := ⟨hg⟩
  have hch : CharP (O ⧸ IsLocalRing.maximalIdeal O) g := by
    rw [CharP.charP_iff_prime_eq_zero hg, ← map_natCast (Ideal.Quotient.mk _)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hgm
  have h1 := closure_upperUni_pow k g _ hw
  obtain ⟨s, t, htg, hnt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' g hg.ne_one
  refine ⟨k + s, ?_⟩
  have htu : IsUnit ((t : ℕ) : O) := by
    by_contra hnu
    have h0 : ((t : ℕ) : O ⧸ IsLocalRing.maximalIdeal O) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    exact htg ((CharP.cast_eq_zero_iff _ g t).1 h0)
  apply Units.ext
  rw [Units.val_one]
  apply Formalism.MainNotions.Gaps.MI.mat_eq_one _ t htu
  · rw [← Units.val_pow_eq_pow_val, ← pow_mul, pow_add, mul_assoc, ← hnt, mul_comm, pow_mul, hwn, one_pow,
      Units.val_one]
  · intro i j
    have h2 : redGL (IsLocalRing.maximalIdeal O) (w ^ g ^ (k + s)) = 1 := by
      rw [pow_add, pow_mul, map_pow, map_pow, h1, one_pow]
    have h3 := congrFun (congrFun (congrArg
      (fun u : GL (Fin k) (O ⧸ IsLocalRing.maximalIdeal O) =>
        (u : Matrix (Fin k) (Fin k) (O ⧸ IsLocalRing.maximalIdeal O))) h2) i) j
    have h4 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
        (((w ^ g ^ (k + s) : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) i j) =
        (1 : Matrix (Fin k) (Fin k) (O ⧸ IsLocalRing.maximalIdeal O)) i j := h3
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, ← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply,
      map_sub, h4]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]

variable {F : Type} [Field F] [NumberField F]

theorem iwU_gpow (k g : ℕ) (hg : g.Prime) (v : HeightOneSpectrum (𝓞 F)) (hgv : (g : 𝓞 F) ∈ v.asIdeal)
    (u : GL (Fin k) (v.adicCompletion F)) (hu : u ∈ iwU F k v) (n : ℕ) (hn : 0 < n) (hun : u ^ n = 1) :
    ∃ N : ℕ, u ^ (g ^ N) = 1 := by
  obtain ⟨w, hw, rfl⟩ := hu
  have hinj : Function.Injective
      (bc (n := Fin k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) :=
    bc_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have hwn : w ^ n = 1 := hinj (by rw [map_pow, map_one]; exact hun)
  have hgm : ((g : ℕ) : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have hone := (Valuation.integer.integers (Valued.v (R := v.adicCompletion F))).isUnit_iff_valuation_eq_one.1 hunit
    have h1 : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (g : v.adicCompletionIntegers F)) < 1 := by
      have h2 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (g : v.adicCompletionIntegers F) =
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (g : 𝓞 F)) := by simp
      rw [h2, Formalism.UG.P.levelaf_valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 hgv
    exact h1.ne hone
  obtain ⟨N, hN⟩ := local_gpow k g hg hgm w hw n hn hwn
  exact ⟨N, by rw [← map_pow, hN, map_one]⟩

end Order

section LocInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

variable (E) in

def trV (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] v.adicCompletion F →ₗ[F] v.adicCompletion F :=
  (TensorProduct.lid F _).toLinearMap ∘ₗ (Algebra.trace F E).rTensor _

theorem trV_tmul (v : HeightOneSpectrum (𝓞 F)) (e : E) (a : v.adicCompletion F) :
    trV E v (e ⊗ₜ a) = algebraMap F _ (Algebra.trace F E e) * a := by
  simp [trV, Algebra.smul_def]

theorem trV_prV (v : HeightOneSpectrum (𝓞 F)) (z : 𝒜) :
    trV E v (prV (E := E) v z) = (adelstabT F E z) v := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul e a => rw [afsplit_prV_tmul, trV_tmul, adelstabT_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; rfl

theorem trV_int (v : HeightOneSpectrum (𝓞 F)) (y : E ⊗[F] v.adicCompletion F) (hy : y ∈ intV E v) :
    trV E v y ∈ v.adicCompletionIntegers F := by
  obtain ⟨a, rfl⟩ := levelv_S_le_range v y hy
  show trV E v (∑ i, algebraMap (𝓞 E) E (RingOfIntegers.basis E i) ⊗ₜ[F]
    ((a i : v.adicCompletionIntegers F) : v.adicCompletion F)) ∈ _
  rw [map_sum]
  refine sum_mem fun i _ => ?_
  rw [trV_tmul]
  obtain ⟨t, ht⟩ := adelstab_trace_int (F := F) (RingOfIntegers.basis E i)
  rw [← ht, ← IsScalarTower.algebraMap_apply]
  exact mul_mem (levelaf_int_mem_v v t) (a i).2

theorem adele_expand {ι : Type} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F E) (x : 𝒜) :
    x = ∑ i, ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i) ⊗ₜ[F]
      adelstabT F E (x * (β i ⊗ₜ[F] (1 : 𝔸))) := by
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    have h : ∀ i, β' i ⊗ₜ[F] adelstabT F E ((e ⊗ₜ[F] a) * (β i ⊗ₜ[F] (1 : 𝔸))) =
        (Algebra.trace F E (e * β i) • β' i) ⊗ₜ[F] a := by
      intro i
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, adelstabT_tmul, ← Algebra.smul_def,
        TensorProduct.smul_tmul]
    simp_rw [h]
    rw [← TensorProduct.sum_tmul]
    congr 1
    conv_lhs => rw [← β'.sum_repr e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  | add x y hx hy =>
    simp only [add_mul, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) hx hy

variable (F E) in

theorem loc_int_bound : ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x : 𝒜, (∀ w, prV (E := E) w x ∈ intV E w) →
    levelafC E c * x ∈ 𝒮 := by
  classical
  set β := Module.finBasis F E
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β with hβ'
  obtain ⟨N, hN, hNi⟩ := adelstabL_den (fun i => β i)
  obtain ⟨M, hM, hMi⟩ := adelstabL_den (fun i => β' i)
  refine ⟨((M * N : ℤ) : 𝓞 F), by exact_mod_cast (mul_ne_zero hM hN), fun x hx => ?_⟩
  have key : levelafC E ((M * N : ℤ) : 𝓞 F) * x =
      ∑ i, ((M : E) * β' i) ⊗ₜ[F] adelstabT F E (x * (((N : E) * β i) ⊗ₜ[F] (1 : 𝔸))) := by
    conv_lhs => rw [adele_expand β x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ((N : E) * β i) = (N : F) • β i := by rw [Algebra.smul_def, map_intCast]
    have h2 : ((M : E) * β' i) = (M : F) • β' i := by rw [Algebra.smul_def, map_intCast]
    have h3 : ((N : F) • β i) ⊗ₜ[F] (1 : 𝔸) = (N : F) • (β i ⊗ₜ[F] (1 : 𝔸)) :=
      (TensorProduct.smul_tmul' _ _ _).symm
    rw [h1, h2, h3, mul_smul_comm, map_smul, TensorProduct.smul_tmul, levelafC,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    simp [Algebra.smul_def, mul_assoc]
  rw [key]
  refine sum_mem fun i _ => ?_
  refine levelaf_tmul_mem (⟨(M : E) * β' i, hMi i⟩ : 𝓞 E) ?_
  intro w
  rw [← trV_prV, map_mul]
  refine trV_int w _ (mul_mem (hx w) ?_)
  rw [afsplit_prV_tmul]
  exact Subring.subset_closure (Or.inl ⟨⟨_, ⟨(⟨(N : E) * β i, hNi i⟩ : 𝓞 E), rfl⟩⟩, rfl⟩)

end LocInt

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem bc_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {n : Type} [Fintype n] [DecidableEq n]
    (f : A →+* B) (g : B →+* C) (x : GL n A) : bc (g.comp f) x = bc g (bc f x) := by
  apply Units.ext
  ext i j
  rfl

theorem exists_place (F : Type) [Field F] [NumberField F] (g : ℕ) (hg : g.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 F), (g : 𝓞 F) ∈ v.asIdeal := by
  have hgZ : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  have hpp : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hgZ.ne_zero).mpr hgZ
  obtain ⟨⟨Q, hQp, hQl⟩⟩ := (Ideal.span {(g : ℤ)}).nonempty_primesOver (S := 𝓞 F)
  have hmem : (g : 𝓞 F) ∈ Q := by
    have h1 : (g : ℤ) ∈ Q.under ℤ := by
      rw [← hQl.over]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.under] using h1
  refine ⟨⟨Q, hQp, ?_⟩, hmem⟩
  intro h
  rw [h, Ideal.mem_bot] at hmem
  exact hg.ne_zero (by exact_mod_cast hmem)

namespace Par

variable {k : ℕ} (P : Par F E k)

def Lad : Submodule 𝒮 (Fin k → 𝒜) where
  carrier := {x | ∀ v, (fun i => prV (E := E) v (x i)) ∈ P.LbV v}
  add_mem' := by
    intro x y hx hy v
    have h : (fun i => prV (E := E) v ((x + y) i)) =
        (fun i => prV (E := E) v (x i)) + (fun i => prV (E := E) v (y i)) := by
      ext i; simp
    rw [h]; exact add_mem (hx v) (hy v)
  zero_mem' := by
    intro v
    have h : (fun i => prV (E := E) v ((0 : Fin k → 𝒜) i)) = 0 := by
      ext i; simp
    rw [h]; exact zero_mem _
  smul_mem' := by
    intro s x hx v
    have h : (fun i => prV (E := E) v ((s • x) i)) =
        (⟨prV (E := E) v s, afsplit_prV_int v _ s.2⟩ : intV E v) • (fun i => prV (E := E) v (x i)) := by
      ext i; simp [Subring.smul_def]
    rw [h]; exact Submodule.smul_mem _ _ (hx v)

theorem Uloc_le (hIw : P.IwLe) (S : P.Splits) (v : HeightOneSpectrum (𝓞 F)) :
    P.Uloc S v ≤ stabGL (P.LbV v) := by
  unfold Uloc
  split_ifs with hT h0 h1
  · exact inf_le_left.trans inf_le_right
  · exact (hIw 0 v h0 _).trans inf_le_right
  · exact (hIw 1 v h1 _).trans inf_le_right
  · exact inf_le_right

theorem U_comp (S : P.Splits) (u : GL (Fin k) 𝒜) (hu : u ∈ P.U S) (v : HeightOneSpectrum (𝓞 F)) :
    bc (prV (E := E) v) u ∈ P.Uloc S v := by
  have h : u ∈ ⨅ v : HeightOneSpectrum (𝓞 F), (P.Uloc S v).comap (bc (prV (E := E) v)) := hu.2
  rw [Subgroup.mem_iInf] at h
  exact h v

theorem U_le_stab (hIw : P.IwLe) (S : P.Splits) : P.U S ≤ stabGL P.Lad := by
  intro u hu x
  have hmap : ∀ v, (fun i => prV (E := E) v (((u : Matrix (Fin k) (Fin k) 𝒜) *ᵥ x) i)) =
      ((bc (prV (E := E) v) u : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) *ᵥ
        (fun i => prV (E := E) v (x i)) := by
    intro v; ext i; rw [RingHom.map_mulVec]; rfl
  show (∀ v, _ ∈ P.LbV v) ↔ (∀ v, _ ∈ P.LbV v)
  refine forall_congr' fun v => ?_
  rw [hmap]
  exact P.Uloc_le hIw S v (P.U_comp S u hu v) _

theorem LbV_int (hInt : ∀ x ∈ P.Lb, ∀ i, x i ∈ intOE E) (v : HeightOneSpectrum (𝓞 F))
    (z : Fin k → E ⊗[F] v.adicCompletion F) (hz : z ∈ P.LbV v) : ∀ i, z i ∈ intV E v := by
  refine Submodule.span_induction (p := fun z _ => ∀ i, z i ∈ intV E v) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨a, ha, rfl⟩ i
    exact Subring.subset_closure (Or.inl ⟨⟨a i, hInt a ha i⟩, rfl⟩)
  · intro i; exact zero_mem _
  · intro x y _ _ hx hy i; exact add_mem (hx i) (hy i)
  · intro s x _ hx i; exact mul_mem s.2 (hx i)

theorem finOrder (hτ : ∀ τ : E →+* ℂ, τ.comp (P.σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (P.σ : E →+* E) P.J) (hdet : IsUnit P.J.det) (hdef : IsTotDef P.σ P.J)
    (hIw : P.IwLe) (c₁ : 𝓞 F) (hc₁ : c₁ ≠ 0)
    (hc : ∀ j, (Pi.single j (algebraMap (𝓞 F) E c₁) : Fin k → E) ∈ P.Lb)
    (hInt : ∀ x ∈ P.Lb, ∀ i, x i ∈ intOE E)
    (S : P.Splits) (y : GL (Fin k) 𝒜) (hy : y ∈ P.GA) (γ : GL (Fin k) E)
    (hγ : γ ∈ UJ (P.σ : E →+* E) P.J)
    (hmem : bc ιA γ ∈ (P.U S).map (MulAut.conj y).toMonoidHom) : IsOfFinOrder γ := by
  obtain ⟨c₂, hc₂, hb⟩ := loc_int_bound F E
  have hfin := adelstab_core P.σ P.J hτ hH hdet hdef P.Lad (P.U S) (P.U_le_stab hIw S) c₁ c₂ hc₁ hc₂
    (by
      intro x hx v
      have e : (fun i => prV (E := E) v (levelafC E c₁ * x i)) =
          ∑ j, (⟨prV (E := E) v (x j), afsplit_prV_int v _ (hx j)⟩ : intV E v) •
            (fun i => inclE (F := F) (v.adicCompletion F)
              ((Pi.single j (algebraMap (𝓞 F) E c₁) : Fin k → E) i)) := by
        ext i
        rw [Finset.sum_apply, Finset.sum_eq_single i]
        · rw [map_mul, ← adelstab_incl_C, afsplit_prV_inclE, Pi.smul_apply, Pi.single_eq_same, Subring.smul_def,
            smul_eq_mul, mul_comm]
        · intro j _ hj
          rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), map_zero, smul_zero]
        · intro h; exact absurd (Finset.mem_univ i) h
      show (fun i => prV (E := E) v (levelafC E c₁ * x i)) ∈ P.LbV v
      rw [e]
      exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hc j, rfl⟩))
    (by
      intro x hx i
      exact hb _ fun w => P.LbV_int hInt w _ (hx w) i)
    ⟨y, hy⟩
  obtain ⟨u, hu, hconj⟩ := hmem
  have hu_eq : bc ιA γ = y * u * y⁻¹ := by rw [← hconj]; rfl
  have hGA : bc ιA γ ∈ P.GA := by
    rw [hu_eq]; exact mul_mem (mul_mem hy hu.1) (inv_mem hy)
  have hnt : Nontrivial 𝔸 := by
    obtain ⟨v, -⟩ := exists_place F 2 Nat.prime_two
    exact (evalV F v).toRingHom.domain_nontrivial
  rw [← (UG_inclusion_injective F E (Fin k) 𝔸 hnt).isOfFinOrder_iff]
  by_contra hno
  have hinj := injective_pow_iff_not_isOfFinOrder.2 hno
  let f : ℕ → stabAt ((ratPts P.σ P.J 𝔸).subgroupOf (UPts P.σ P.J 𝔸))
      ((P.U S).subgroupOf (UPts P.σ P.J 𝔸)) ⟨y, hy⟩ := fun n =>
    ⟨⟨⟨bc ιA γ ^ n, pow_mem hGA n⟩, by
      rw [Subgroup.mem_subgroupOf]
      exact pow_mem (⟨γ, hγ, rfl⟩ : bc ιA γ ∈ ratPts P.σ P.J 𝔸) n⟩, by
      show _ ∈ (P.U S).subgroupOf (UPts P.σ P.J 𝔸)
      rw [Subgroup.mem_subgroupOf]
      show y⁻¹ * bc ιA γ ^ n * y ∈ P.U S
      have : y⁻¹ * bc ιA γ ^ n * y = u ^ n := by rw [hu_eq, conj_pow]; group
      rw [this]
      exact pow_mem hu n⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply hinj
    exact congrArg (fun z => ((z.1.1 : UPts P.σ P.J 𝔸) : GL (Fin k) 𝒜)) hab
  have hN : Finite ℕ := Finite.of_injective f hf
  exact not_finite ℕ

theorem gpow (S : P.Splits) (g : ℕ) (hg : g.Prime) (v : HeightOneSpectrum (𝓞 F)) (hv : (g : 𝓞 F) ∈ v.asIdeal)
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (hU : P.Uloc S v = P.iwPre v φ) (y : GL (Fin k) 𝒜) (γ : GL (Fin k) E)
    (hmem : bc ιA γ ∈ (P.U S).map (MulAut.conj y).toMonoidHom) (hfin : IsOfFinOrder γ) :
    ∃ N : ℕ, γ ^ (g ^ N) = 1 := by
  obtain ⟨n, hn, hγn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  obtain ⟨u, hu, hconj⟩ := hmem
  have hu_eq : bc ιA γ = y * u * y⁻¹ := by rw [← hconj]; rfl
  have hpow : ∀ m, bc ιA (γ ^ m) = y * u ^ m * y⁻¹ := by
    intro m; rw [map_pow, hu_eq, conj_pow]
  have hun : u ^ n = 1 := by
    have h : u ^ n = y⁻¹ * (y * u ^ n * y⁻¹) * y := by group
    rw [h, ← hpow n, hγn, map_one]; group
  set p1 : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom with hp1
  have hu' : bc p1 (bc (prV (E := E) v) u) ∈ iwU F k v := by
    have h := P.U_comp S u hu v
    rw [hU] at h
    exact h.2
  obtain ⟨N, hN⟩ := iwU_gpow k g hg v hv _ hu' n hn (by rw [← map_pow, ← map_pow, hun, map_one, map_one])
  refine ⟨N, ?_⟩
  have hψ : Function.Injective (bc (n := Fin k) ((p1.comp (prV (E := E) v)).comp ιA)) :=
    bc_injective _ (RingHom.injective _)
  apply hψ
  rw [bc_comp, bc_comp, hpow, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, hN, mul_one, ← map_mul,
    ← map_mul, mul_inv_cancel, map_one, map_one, map_one]

end Par

theorem not_both {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a b : ℕ)
    (h : Nat.Coprime a b) (ha : (a : 𝓞 F) ∈ v.asIdeal) (hb : (b : 𝓞 F) ∈ v.asIdeal) : False := by
  obtain ⟨r, s, hrs⟩ := Nat.isCoprime_iff_coprime.2 h
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((r : 𝓞 F) * (a : 𝓞 F) + (s : 𝓞 F) * (b : 𝓞 F)) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 F) hrs
  rw [← h1]
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

namespace Par

variable {k : ℕ} (P : Par F E k)

theorem stabTriv_of (hτ : ∀ τ : E →+* ℂ, τ.comp (P.σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (P.σ : E →+* E) P.J) (hdet : IsUnit P.J.det) (hdef : IsTotDef P.σ P.J)
    (hIw : P.IwLe) (c₁ : 𝓞 F) (hc₁ : c₁ ≠ 0)
    (hc : ∀ j, (Pi.single j (algebraMap (𝓞 F) E c₁) : Fin k → E) ∈ P.Lb)
    (hInt : ∀ x ∈ P.Lb, ∀ i, x i ∈ intOE E)
    (hg : ∀ i, (P.gp i).Prime) (hne : P.gp 0 ≠ P.gp 1) (hT : ∀ i, Nat.Coprime P.T (P.gp i)) :
    P.StabTriv := by
  intro S y hy γ hγ hmem
  have hfin := P.finOrder hτ hH hdet hdef hIw c₁ hc₁ hc hInt S y hy γ hγ hmem
  obtain ⟨v0, hv0⟩ := exists_place F (P.gp 0) (hg 0)
  obtain ⟨v1, hv1⟩ := exists_place F (P.gp 1) (hg 1)
  have hU0 : P.Uloc S v0 = P.iwPre v0 (S 0 v0 hv0).φ := by
    unfold Uloc
    rw [if_neg (fun h => not_both v0 _ _ (hT 0) h hv0), dif_pos hv0]
  have hU1 : P.Uloc S v1 = P.iwPre v1 (S 1 v1 hv1).φ := by
    unfold Uloc
    rw [if_neg (fun h => not_both v1 _ _ (hT 1) h hv1),
      dif_neg (fun h => not_both v1 _ _ ((Nat.coprime_primes (hg 0) (hg 1)).2 hne) h hv1), dif_pos hv1]
  obtain ⟨N0, hN0⟩ := P.gpow S _ (hg 0) v0 hv0 _ hU0 y γ hmem hfin
  obtain ⟨N1, hN1⟩ := P.gpow S _ (hg 1) v1 hv1 _ hU1 y γ hmem hfin
  have d0 : orderOf γ ∣ P.gp 0 ^ N0 := orderOf_dvd_of_pow_eq_one hN0
  have d1 : orderOf γ ∣ P.gp 1 ^ N1 := orderOf_dvd_of_pow_eq_one hN1
  have hcop : Nat.Coprime (P.gp 0 ^ N0) (P.gp 1 ^ N1) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes (hg 0) (hg 1)).mpr hne)
  have : orderOf γ = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd d0 d1)
  exact orderOf_eq_one_iff.mp this

end Par

end Fin

section Lb

variable {E : Type} [Field E] [NumberField E]

theorem LbOf_int (k : ℕ) (pz : 𝓞 E) : ∀ x ∈ LbOf k pz, ∀ i, x i ∈ intOE E := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => ∀ i, x i ∈ intOE E) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩ i
    unfold lbVec
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same]
      split_ifs
      · exact ⟨pz, rfl⟩
      · exact one_mem _
    · rw [Pi.single_eq_of_ne hij]; exact zero_mem _
  · intro i; exact zero_mem _
  · intro x y _ _ hx hy i; exact add_mem (hx i) (hy i)
  · intro s x _ hx i
    show s • x i ∈ intOE E
    rw [Algebra.smul_def]
    exact mul_mem ⟨s, rfl⟩ (hx i)

theorem single_mem_LbOf (k : ℕ) (pz c : 𝓞 E) (t : 𝓞 E) (ht : c * pz = t) (j : Fin k) :
    (Pi.single j (t : E) : Fin k → E) ∈ LbOf k pz := by
  by_cases hj : j.1 = 0
  · have h : (Pi.single j (t : E) : Fin k → E) = c • lbVec k pz j := by
      unfold lbVec
      rw [if_pos hj, ← Pi.single_smul, Algebra.smul_def, ← ht]
      rfl
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · have h : (Pi.single j (t : E) : Fin k → E) = t • lbVec k pz j := by
      unfold lbVec
      rw [if_neg hj, ← Pi.single_smul, Algebra.smul_def, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end Lb

theorem factStabTriv_of (h4 : FactIwLe) (h9 : FactTNeG) : FactStabTriv := by
  intro R H T pz piG h
  have hτ : ∀ τ : H.E →+* ℂ,
      τ.comp ((Examples₂.conjF H : H.E →ₐ[H.F] H.E) : H.E →+* H.E) = (starRingEnd ℂ).comp τ :=
    fun τ => RingHom.ext fun x => Examples₂.emb_conj H τ x
  obtain ⟨hH, hdef, -⟩ := standard_hermitian_form_definite H.F H.E (Fin R.k) (Examples₂.conjF H) hτ
    (fun e he => ⟨⟨e, (Examples₂.conj_eq_self_iff H e).1 he⟩, rfl⟩) inferInstance
  refine (hostPar H T pz piG).stabTriv_of hτ hH (by simp [hostPar]) hdef (h4 H T pz piG h) (T : 𝓞 H.F)
    (by exact_mod_cast h.T_prime.ne_zero) ?_ (LbOf_int _ _) H.g_prime H.g_ne
    (fun i => (Nat.coprime_primes h.T_prime (H.g_prime i)).2 (h9 H T pz piG h i))
  intro j
  have hT : algebraMap (𝓞 H.F) H.E (T : 𝓞 H.F) = (((T : ℕ) : 𝓞 H.E) : H.E) := by
    rw [map_natCast]; simp
  rw [hT]
  refine single_mem_LbOf R.k pz (RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E) pz) _ ?_ j
  apply RingOfIntegers.ext
  show H.conj (pz : H.E) * (pz : H.E) = (((T : ℕ) : 𝓞 H.E) : H.E)
  rw [mul_comm, h.pz_norm]; simp

theorem factStabTriv_of_iwLe (h4 : FactIwLe) : FactStabTriv :=
  factStabTriv_of h4 Formalism.MainNotions.Gaps.LevGap.factTNeG

theorem factStabTriv : FactStabTriv := factStabTriv_of_iwLe factIwLe

end Formalism.MainNotions.Gaps.LG

end
