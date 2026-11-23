import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatLevel

noncomputable section

namespace GlobalTheory.ThKLevelOpen

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_int_den (s : Finset E) : ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ s, IsIntegral ℤ ((N : E) * x) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ s
  exact ⟨y, hy, fun x hx => by simpa [zsmul_eq_mul] using h x hx⟩

theorem exists_int_single {d : ℕ} (L : Submodule (𝓞 E) (Fin d → E)) (hL : L.IsLattice E) {m : ℕ}
    (e : Fin m → E) : ∃ N : ℤ, N ≠ 0 ∧ ∀ y ∈ L, ∀ i l j, (N : E) • Pi.single i (e j * y l) ∈ L := by
  classical
  have hsm : ∀ c : E, IsIntegral ℤ c → ∀ a ∈ L, c • a ∈ L := fun c hc a ha =>
    L.smul_mem (⟨c, hc⟩ : 𝓞 E) ha
  have hspan : ∀ i : Fin d, ∃ (f : (Fin d → E) → E) (t : Finset (Fin d → E)),
      (t : Set (Fin d → E)) ⊆ L ∧ ∑ a ∈ t, f a • a = Pi.single i 1 := by
    intro i
    have hi : Pi.single i (1 : E) ∈ Submodule.span E (L : Set (Fin d → E)) := by
      rw [hL.span_eq_top]; trivial
    obtain ⟨f, t, ht, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.1 hi
    exact ⟨f, t, ht, hsum⟩
  choose f t ht hsum using hspan
  obtain ⟨D, hD0, hD⟩ := exists_int_den (Finset.univ.biUnion fun i => (t i).image (f i))
  have h1 : ∀ i (x : E), IsIntegral ℤ x → (D : E) • Pi.single i x ∈ L := by
    intro i x hx
    have heq : (D : E) • Pi.single i x = ∑ a ∈ t i, (x * ((D : E) * f i a)) • a := by
      have : (D : E) • Pi.single i x = (x * D) • Pi.single i (1 : E) := by
        funext k; by_cases hk : k = i <;> simp [hk, Pi.single_apply, mul_comm]
      rw [this, ← hsum i, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul, mul_assoc]
    rw [heq]
    exact Submodule.sum_mem _ fun a ha => hsm _ (hx.mul (hD _ (Finset.mem_biUnion.2
      ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ ha⟩))) _ (ht i ha)
  obtain ⟨S, hS⟩ := hL.fg
  obtain ⟨D', hD'0, hD'⟩ := exists_int_den
    (Finset.univ.biUnion fun p : Fin m × Fin d => S.image fun y => e p.1 * y p.2)
  have h2 : ∀ y ∈ L, ∀ j l, IsIntegral ℤ ((D' : E) * (e j * y l)) := by
    intro y hy
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => intro j l; exact hD' _ (Finset.mem_biUnion.2
        ⟨(j, l), Finset.mem_univ _, Finset.mem_image_of_mem (fun y => e (j, l).1 * y (j, l).2) hy⟩)
    | zero => intro j l; simpa using (isIntegral_zero : IsIntegral ℤ (0 : E))
    | add y z _ _ hy hz => intro j l; simpa [mul_add] using (hy j l).add (hz j l)
    | smul o y _ hy =>
      intro j l
      have : (D' : E) * (e j * (o • y) l) = (algebraMap (𝓞 E) E o) * ((D' : E) * (e j * y l)) := by
        rw [Pi.smul_apply, Algebra.smul_def]; ring
      rw [this]; exact (RingOfIntegers.isIntegral_coe o).mul (hy j l)
  refine ⟨D * D', mul_ne_zero hD0 hD'0, fun y hy i l j => ?_⟩
  have := h1 i _ (h2 y hy j l)
  convert this using 1
  funext k; by_cases hk : k = i <;> simp [hk, Pi.single_apply]; ring

variable (F) in

def nbhd (N : ℤ) : Set (AF F) :=
  {b | ∀ v : Pl F, evFin F v (algebraMap F (AF F) (N : F)⁻¹ * b) ∈ v.adicCompletionIntegers F}

theorem isOpen_nbhd (N : ℤ) : IsOpen (nbhd F N) := by
  have h : IsOpen {x : Af F | ∀ v : Pl F, x.1 v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : Pl F => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  exact h.preimage (continuous_snd.comp (continuous_const.mul continuous_id))

theorem zero_mem_nbhd (N : ℤ) : (0 : AF F) ∈ nbhd F N := fun v => by
  rw [mul_zero, map_zero]; exact zero_mem _

theorem smul_mulVec_mem {d : ℕ} (W : Spc F E d) (w : Pl F) {m : ℕ} (B : Module.Basis (Fin m) (AF F) (AE F E))
    (e : Fin m → E) (hB : ∀ j, B j = inclR (F := F) (AF F) (e j)) (N : ℤ) (hN0 : N ≠ 0)
    (hN : ∀ y ∈ W.L, ∀ i l j, (N : E) • Pi.single i (e j * y l) ∈ W.L)
    (M : Matrix (Fin d) (Fin d) (AE F E)) (hM : ∀ i l j, B.repr (M i l) j ∈ nbhd F N)
    (a : AF F) (ha : At (evFin F w) a) (hai : evFin F w a ∈ w.adicCompletionIntegers F)
    (y : Fin d → E) (hy : y ∈ W.L) :
    a • (M *ᵥ fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt W w := by
  classical
  have hexp : ∀ k l, M k l * inclR (F := F) (AF F) (y l) =
      ∑ j, B.repr (M k l) j • inclR (F := F) (AF F) (e j * y l) := by
    intro k l
    conv_lhs => rw [← B.sum_repr (M k l)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, hB, map_mul]
  have hinc : ∀ t : E, inclR (F := F) (AF F) ((N : E) * t) =
      algebraMap F (AF F) (N : F) • inclR (F := F) (AF F) t := by
    intro t
    rw [map_mul, map_intCast, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
  have hNc : algebraMap F (AF F) (N : F)⁻¹ * algebraMap F (AF F) (N : F) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hN0), map_one]

  have hterm : ∀ k l j, Pi.single k ((a * B.repr (M k l) j) • inclR (F := F) (AF F) (e j * y l)) ∈
      GlobalTheory.InertSph.latAt W w := by
    intro k l j
    set r := B.repr (M k l) j
    refine AddSubgroup.subset_closure ⟨a * (algebraMap F (AF F) (N : F)⁻¹ * r), ?_, ?_,
      (N : E) • Pi.single k (e j * y l), hN y hy k l j, ?_⟩
    · intro u hu
      rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u a, ha u hu, zero_mul]
    · rw [map_mul]
      exact mul_mem hai (hM k l j w)
    · funext i
      by_cases hik : i = k
      · subst hik
        simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, hinc, smul_smul]
        congr 1
        linear_combination (-(a * r)) * hNc
      · simp [Pi.single_eq_of_ne hik]
  rw [← Finset.univ_sum_single (a • _)]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  have hk : (a • (M *ᵥ fun i => inclR (F := F) (AF F) (y i))) k =
      ∑ l, ∑ j, (a * B.repr (M k l) j) • inclR (F := F) (AF F) (e j * y l) := by
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, hexp, Finset.smul_sum, smul_smul]
  rw [hk]
  change _ ∈ (GlobalTheory.InertSph.latAt W w).comap (AddMonoidHom.single _ k)
  exact AddSubgroup.sum_mem _ fun l _ => AddSubgroup.sum_mem _ fun j _ => hterm k l j

theorem mulVec_mem_latAt {d : ℕ} (W : Spc F E d) (w : Pl F) {m : ℕ} (B : Module.Basis (Fin m) (AF F) (AE F E))
    (e : Fin m → E) (hB : ∀ j, B j = inclR (F := F) (AF F) (e j)) (N : ℤ) (hN0 : N ≠ 0)
    (hN : ∀ y ∈ W.L, ∀ i l j, (N : E) • Pi.single i (e j * y l) ∈ W.L)
    (P : Matrix (Fin d) (Fin d) (AE F E)) (hP : ∀ i l j, B.repr ((P - 1) i l) j ∈ nbhd F N)
    {z : Fin d → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt W w) : P *ᵥ z ∈ GlobalTheory.InertSph.latAt W w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
    have e1 : P *ᵥ (a • fun i => inclR (F := F) (AF F) (y i)) = a • (fun i => inclR (F := F) (AF F) (y i)) +
        a • ((P - 1) *ᵥ fun i => inclR (F := F) (AF F) (y i)) := by
      rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub]; abel
    rw [e1]
    exact add_mem (AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, rfl⟩)
      (smul_mulVec_mem W w B e hB N hN0 hN _ hP a ha hai y hy)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem exists_open_latLevel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d), W.L.IsLattice E →
    ∃ U : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J), IsOpen U ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J) ∈ U ∧
      U ∩ GlobalTheory.ThKAdm.FinPt σ W ⊆ GlobalTheory.ThKLevel.latLevel σ W := by
  intro F E _ _ _ _ _ σ d W hL
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hB : ∀ j, B j = inclR (F := F) (AF F) (b j) := fun j => by
    simp [B, Algebra.TensorProduct.basis_apply, inclR]
  obtain ⟨N, hN0, hN⟩ := exists_int_single W.L hL (fun j => b j)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun g : UA σ W.J => mat g⁻¹ :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have hc : ∀ j, Continuous fun x : AE F E => B.repr x j := fun j =>
    IsModuleTopology.continuous_of_linearMap (B.coord j)
  have hent : ∀ (f : UA σ W.J → Matrix (Fin d) (Fin d) (AE F E)), Continuous f → ∀ i l j,
      IsOpen {g | B.repr ((f g - 1) i l) j ∈ nbhd F N} := fun f hf i l j =>
    (isOpen_nbhd N).preimage ((hc j).comp
      (((continuous_apply l).comp (continuous_apply i)).comp (hf.sub continuous_const)))
  refine ⟨{g | ∀ i l j, B.repr ((mat g - 1) i l) j ∈ nbhd F N ∧ B.repr ((mat g⁻¹ - 1) i l) j ∈ nbhd F N},
    ?_, ?_, ?_⟩
  · simp only [Set.setOf_forall, Set.setOf_and]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun l => isOpen_iInter_of_finite fun j =>
      (hent _ hm i l j).inter (hent _ hmi i l j)
  · intro i l j
    rw [inv_one, show mat (1 : UA σ W.J) = 1 from rfl, sub_self]
    simp only [Matrix.zero_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, and_self]
    exact zero_mem_nbhd N
  · rintro k ⟨hkU, hkF⟩
    refine ⟨hkF, fun w z hz => ⟨?_, ?_⟩⟩
    · exact mulVec_mem_latAt W w B (fun j => b j) hB N hN0 hN _ (fun i l j => (hkU i l j).1) hz
    · exact mulVec_mem_latAt W w B (fun j => b j) hB N hN0 hN _ (fun i l j => (hkU i l j).2) hz

end GlobalTheory.ThKLevelOpen

end
