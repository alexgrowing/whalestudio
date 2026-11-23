import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousExtensionAdicCompletion
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsHomOfBasis
import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlace

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.EvExtend

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]

theorem norm_natCast_lt_one : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h := PadicComplex.norm_extends l ((l : ℕ) : PadicAlgCl l)
  rw [← h]
  simpa using ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one (p := l)

theorem norm_int_le_one (φ : F →+* PadicAlgCl l) (y : 𝓞 F) : ‖φ (y : F)‖ ≤ 1 := by
  have hi : IsIntegral ℤ (φ (y : F)) := (RingOfIntegers.isIntegral_coe y).map φ.toIntAlgHom
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).isIntegral_iff_v_le_one.mp
    hi.tower_top
  exact_mod_cast (show ‖φ (y : F)‖₊ ≤ 1 from h2)

def placeOf (φ : F →+* PadicAlgCl l) : HeightOneSpectrum (𝓞 F) where
  asIdeal := ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal ((algebraMap (PadicAlgCl l) ℂ_[l]).comp φ)
  isPrime := ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal_isPrime _
  ne_bot := by
    intro h
    have hm : ((l : ℕ) : 𝓞 F) ∈ ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal ((algebraMap (PadicAlgCl l) ℂ_[l]).comp φ) := by
      rw [ReciprocityTheory.ChartRestriction.B3.IotaPl.mem_smallIdeal]
      simpa using ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one (p := l)
    rw [h, Submodule.mem_bot] at hm
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hm

theorem mem_placeOf (φ : F →+* PadicAlgCl l) (x : 𝓞 F) : x ∈ (placeOf φ).asIdeal ↔ ‖φ (x : F)‖ < 1 := by
  show ‖(algebraMap (PadicAlgCl l) ℂ_[l]) (φ (x : F))‖ < 1 ↔ _
  rw [show ‖(algebraMap (PadicAlgCl l) ℂ_[l]) (φ (x : F))‖ = ‖φ (x : F)‖ from PadicComplex.norm_extends _ _]

theorem norm_le_one_iff (φ : F →+* PadicAlgCl l) (x : F) : ‖φ x‖ ≤ 1 ↔ (placeOf φ).valuation F x ≤ 1 :=
  Formalism.BasicNotions.Examples₂.norm_le_one_iff_val φ (placeOf φ) (norm_int_le_one φ) (mem_placeOf φ) x

theorem val_lt_one_iff (φ : F →+* PadicAlgCl l) (x : F) : (placeOf φ).valuation F x < 1 ↔ ‖φ x‖ < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := norm_le_one_iff φ x⁻¹
  have hpos : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx)
  have hv : 0 < (placeOf φ).valuation F x := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff _).2 hx
  rw [map_inv₀, norm_inv, inv_le_one₀ hpos, map_inv₀, inv_le_one₀ hv] at h
  rw [← not_le, ← not_le, h]

end GlobalTheory.EvExtend

namespace GlobalTheory.EvExtend

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]

theorem exists_ext (φ : F →+* PadicAlgCl l) :
    ∃ j : (placeOf φ).adicCompletion F →+* PadicAlgCl l, Continuous j ∧
      (∀ x : F, j (algebraMap F _ x) = φ x) ∧
      (∀ y ∈ (placeOf φ).adicCompletionIntegers F, ‖j y‖ ≤ 1) ∧
      ∀ (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → (∀ x, φ x ∈ K) → ∀ y, j y ∈ K := by
  obtain ⟨j, hjc, hj⟩ := GlobalTheory.exists_continuous_extension_adicCompletion F l φ (placeOf φ) (val_lt_one_iff φ)
  have hj' : ∀ x : F, j (algebraMap F _ x) = φ x := fun x => RingHom.congr_fun hj x
  have hd := HeightOneSpectrum.denseRange_algebraMap F (placeOf φ)
  refine ⟨j, hjc, hj', fun y hy => ?_, fun K hK hφK y => ?_⟩
  · have hO : IsOpen (((placeOf φ).adicCompletionIntegers F : Set ((placeOf φ).adicCompletion F))) :=
      Valued.isOpen_valuationSubring _
    have hcl : IsClosed {y : (placeOf φ).adicCompletion F | ‖j y‖ ≤ 1} :=
      isClosed_le (continuous_norm.comp hjc) continuous_const
    refine closure_minimal ?_ hcl (hd.open_subset_closure_inter hO hy)
    rintro _ ⟨hy1, x, rfl⟩
    show ‖j (algebraMap F _ x)‖ ≤ 1
    rw [hj', norm_le_one_iff]
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, ReciprocityTheory.Aut.adic_valued_algebraMap] at hy1
    exact hy1
  · haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
    have hKc : IsClosed (K : Set (PadicAlgCl l)) := (completeSpace_coe_iff_isComplete.mp ‹_›).isClosed
    exact hd.induction_on (p := fun y => j y ∈ K) y (hKc.preimage hjc) fun x => by
      show j (algebraMap F _ x) ∈ K
      rw [hj']; exact hφK x

end GlobalTheory.EvExtend

namespace GlobalTheory.EvExtend

theorem exists_evOk : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (l : ℕ) [Fact l.Prime]
    (i : E →+* PadicAlgCl l), ∃ ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l, GlobalTheory.FrameOf.EvOk i ev := by
  intro F E _ _ _ _ _ l _ i
  let φ : F →+* PadicAlgCl l := i.comp (algebraMap F E)
  obtain ⟨j, -, hj, hint, hK⟩ := exists_ext φ
  let v := placeOf φ
  let e0 : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
    { toFun := fun a => a v, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  letI : Algebra F (PadicAlgCl l) := φ.toAlgebra
  let f : FiniteAdeleRing (𝓞 F) F →ₐ[F] PadicAlgCl l :=
    { j.comp e0 with commutes' := fun x => hj x }
  let g : E →ₐ[F] PadicAlgCl l := { i with commutes' := fun x => rfl }
  let ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l :=
    (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _).toRingHom
  have hev : ∀ a e, ev (a ⊗ₜ[F] e) = j (a v) * i e := fun a e => Algebra.TensorProduct.lift_tmul _ _ _ _ _
  refine ⟨ev, fun x => ?_, fun a ha => ?_, fun a ha => ?_, fun y => ?_⟩
  · rw [hev]
    show j 1 * i x = i x
    rw [map_one, one_mul]
  · rw [hev, map_one, mul_one]
    exact hint _ (ha v)
  · have hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [mem_placeOf]
      simpa [φ] using norm_natCast_lt_one (l := l)
    rw [hev, ha v hl, map_zero, zero_mul]
  · have hKle : Formalism.BasicNotions.Examples₂.LB.Kphi i ≤ IntermediateField.adjoin ℚ_[l] (Set.range i) :=
      IntermediateField.adjoin.mono _ _ _ (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩)
    have hmem : ∀ a e, ev (a ⊗ₜ[F] e) ∈ Formalism.BasicNotions.Examples₂.LB.Kphi i := fun a e => by
      rw [hev]
      exact mul_mem (hK _ inferInstance (fun x => Formalism.BasicNotions.Examples₂.LB.phi_mem i _) _) (Formalism.BasicNotions.Examples₂.LB.phi_mem i e)
    refine hKle ?_
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a e => exact hmem a e
    | add y z hy hz => rw [map_add]; exact add_mem hy hz

end GlobalTheory.EvExtend
