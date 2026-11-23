import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.LevelA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Development
import Lemmata.IntegerMulIntegral.IntMulIntegral

noncomputable section

open NumberField Matrix IsDedekindDomain Formalism.UG Formalism.UG.P PI.InHHClassFin
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem lvB_denom_fam {ι : Type} [Fintype ι] (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ i, levelafC E d * f i ∈
      tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
  classical
  choose d hd0 hd using fun i => levelaf_denom (E := E) (f i)
  refine ⟨∏ k, d k, Finset.prod_ne_zero_iff.2 fun i _ => hd0 i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), levelafC_mul,
    mul_comm (levelafC E (d i)), mul_assoc]
  exact mul_mem (levelafC_mem _) (hd i)

theorem lvB_incl_int (a : 𝓞 E) : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) ∈
    tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
  show algebraMap (𝓞 E) E a ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) ∈ _
  exact levelaf_tmul_mem a (one_mem _)

theorem lvB_C_intCast (M : ℤ) : levelafC E ((M : 𝓞 F)) = ((M : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
  rw [levelafC, map_intCast, ← Algebra.TensorProduct.includeRight_apply, map_intCast]

theorem lvB_C_natCast (M : ℕ) : levelafC E ((M : 𝓞 F)) = ((M : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
  rw [levelafC, map_natCast, ← Algebra.TensorProduct.includeRight_apply, map_natCast]

theorem lvB_lat_up (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ y ∈ Formalism.MainNotions.S.lamAf (F := F) L, ∀ i, levelafC E d * y i ∈
      tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
  classical
  obtain ⟨s, hs⟩ := hL
  obtain ⟨d, hd0, hd⟩ := lvB_denom_fam (F := F) (E := E)
    (fun p : s × Fin n =>
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((p.1 : Fin n → E) p.2))
  refine ⟨d, hd0, ?_⟩
  have hL' : ∀ x ∈ L, ∀ i, levelafC E d * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i) ∈
      tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact fun i => hd ⟨⟨x, Finset.mem_coe.1 hx⟩, i⟩
    | zero => intro i; simp
    | add x y _ _ hx hy =>
      intro i
      simp only [Pi.add_apply, map_add, mul_add]
      exact add_mem (hx i) (hy i)
    | smul a x _ hx =>
      intro i
      simp only [Pi.smul_apply]
      rw [Algebra.smul_def, map_mul, mul_left_comm]
      exact mul_mem (lvB_incl_int a) (hx i)
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact fun i => hL' x x.2 i
  | zero => intro i; simp
  | add x y _ _ hx hy =>
    intro i
    simp only [Pi.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul r y _ hy =>
    intro i
    simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
    rw [mul_left_comm]
    exact mul_mem r.2 (hy i)

theorem lvB_span_int (L : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E)
    (hv : v ∈ Submodule.span E (L : Set (Fin n → E))) : ∃ m : ℤ, m ≠ 0 ∧ m • v ∈ L := by
  first | exact Bl.IntegerMulIntegral.goal1 .. | (apply Bl.IntegerMulIntegral.goal1 <;> assumption) | (intros; apply Bl.IntegerMulIntegral.goal1 <;> assumption) | (apply @Bl.IntegerMulIntegral.goal1 <;> assumption) | (intros; apply @Bl.IntegerMulIntegral.goal1 <;> assumption) | (apply @Bl.IntegerMulIntegral.goal1 <;> first | assumption | infer_instance)

theorem lvB_lat_down (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ y : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ i, y i ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) →
      levelafC E d • y ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  classical
  choose m hm0 hm using fun i : Fin n =>
    lvB_span_int L (Pi.single i 1) (hspan ▸ Submodule.mem_top)
  set M : ℤ := ∏ i, m i with hMdef
  have hM : ∀ i, M • (Pi.single i (1 : E) : Fin n → E) ∈ L := fun i => by
    rw [hMdef, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, mul_smul]
    exact zsmul_mem (hm i) _
  refine ⟨(M : 𝓞 F), Int.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hm0 i), ?_⟩
  intro y hy
  rw [lvB_C_intCast]
  have e : (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) • y =
      ∑ i, (⟨y i, hy i⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) •
        (fun j => inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
          ((M • (Pi.single i (1 : E) : Fin n → E)) j)) := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Subring.smul_def,
      Pi.single_apply, zsmul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [e]
  exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨_, hM i⟩, rfl⟩)

end Adelic

end PI.UnitaryGroupMassFormula.InHHClassFin
