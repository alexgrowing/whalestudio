import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.InertAsm

section Gen

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem intInd_congr {x y : K} (h : modulus x = modulus y) : (intInd x : ℂ) = intInd y := by
  have hxy : x ∈ 𝒪[K] ↔ y ∈ 𝒪[K] := by
    rw [← modulus_le_one_iff, ← modulus_le_one_iff, h]
  by_cases hx : x ∈ 𝒪[K]
  · simp [intInd, hx, hxy.1 hx]
  · have hy : y ∉ 𝒪[K] := fun hy => hx (hxy.2 hy)
    simp [intInd, hx, hy]

theorem ord_eq_zero_of_modulus_eq_one {x : K} (hx : x ≠ 0) (h : modulus x = 1) : ord x = 0 := by
  rw [modulus_of_ne_zero hx] at h
  have hq := one_lt_residueCard_nnreal (K := K)
  have h1 : -ord x = 0 :=
    zpow_right_injective₀ (zero_lt_one.trans hq) hq.ne' (by simpa using h)
  omega

theorem char_congr (c : Kˣ →* ℂˣ) (hc : IsUnramifiedChar c) {u v : Kˣ}
    (h : modulus (u : K) = modulus (v : K)) : c u = c v := by
  have hm : modulus ((u * v⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, modulus_mul, modulus_inv, h]
    exact mul_inv_cancel₀ (modulus_ne_zero v.ne_zero)
  have h0 := isUnramifiedChar_iff.1 hc _ (ord_eq_zero_of_modulus_eq_one (Units.ne_zero _) hm)
  rw [map_mul, map_inv] at h0
  exact mul_inv_eq_one.1 h0

theorem intInd_isLocallyConstant : IsLocallyConstant (intInd : K → ℂ) := by
  have ho : IsOpen (𝒪[K] : Set K) := Valuation.isOpen_integer
  have hcl : IsClosed (𝒪[K] : Set K) := Valuation.isClosed_integer (v := ValuativeRel.valuation K)
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  by_cases hx : x ∈ 𝒪[K]
  · filter_upwards [ho.mem_nhds hx] with y hy
    have hy' : y ∈ 𝒪[K] := hy
    simp [intInd, hx, hy']
  · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    have hy' : y ∉ 𝒪[K] := hy
    simp [intInd, hx, hy']

theorem intInd_hasCompactSupport : HasCompactSupport (intInd : K → ℂ) := by
  have hc : IsCompact (𝒪[K] : Set K) := IsNonarchimedeanLocalField.isCompact_closedBall K 1
  refine HasCompactSupport.intro hc fun x hx => ?_
  have hx' : x ∉ 𝒪[K] := hx
  simp [intInd, hx']

end Gen

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)]

open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep (modulus_norm modulus_algebraMap)

theorem intInd_mem_SBc (c : Eˣ →* ℂˣ) (hc : IsUnramifiedChar c) :
    (intInd : E → ℂ) ∈ GL2LocalData.SBc F E c := by
  refine ⟨intInd_isLocallyConstant, intInd_hasCompactSupport, fun u hu x => ?_⟩
  have hm : modulus (u : E) = 1 := by
    rw [← modulus_norm (K := F), hu, modulus_one]
  have h1 : c u = 1 := by
    have := char_congr c hc (u := u) (v := 1) (by simpa using hm)
    simpa using this
  rw [h1, inv_one, Units.val_one, one_mul]
  exact intInd_congr (by rw [modulus_mul, hm, mul_one])

def val (χ : AddChar F Circle) (c : Eˣ →* ℂˣ) (g : GL (Fin 2) F) (t : Eˣ) : ℂ :=
  ((c t : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
    ((((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * GL2LocalData.nsg E (mRow g) * (χ (xRow g) : ℂ) *
      intInd ((t : E) * algebraMap F E (mRow g)⁻¹))

theorem Wc_eq {χ : AddChar F Circle} {σ : E ≃ₐ[F] E} {μ : Measure E} {c : Eˣ →* ℂˣ}
    (hc : IsUnramifiedChar c)
    (hform : ∀ (g : GL (Fin 2) F) (t : Eˣ), Algebra.norm F (t : E) = (g.val).det →
      GL2LocalData.rW χ σ μ 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1)
        (fun x => intInd (x * (t : E))) 1 =
      (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * GL2LocalData.nsg E (mRow g) * (χ (xRow g) : ℂ) *
        intInd ((t : E) * algebraMap F E (mRow g)⁻¹))
    (g : GL (Fin 2) F) (t : Eˣ) (ht : Algebra.norm F (t : E) = (g.val).det) :
    GL2LocalData.Wc χ σ μ 1 c intInd g = val χ c g t := by
  have h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det := ⟨t, ht⟩
  have hm : modulus (h.choose : E) = modulus (t : E) := by
    rw [← modulus_norm (K := F), ← modulus_norm (K := F) (t : E), h.choose_spec, ht]
  rw [GL2LocalData.Wc, dif_pos h, hform g _ h.choose_spec, val, char_congr c hc hm,
    intInd_congr (x := (h.choose : E) * algebraMap F E (mRow g)⁻¹)
      (y := (t : E) * algebraMap F E (mRow g)⁻¹) (by rw [modulus_mul, modulus_mul, hm])]

theorem val_eq {χ : AddChar F Circle} {η : Fˣ →* ℂˣ} {c : Eˣ →* ℂˣ} (hχ : Ad3.IsStd χ)
    (hη : ∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) (hηu : IsUnramifiedChar η)
    (hc : IsUnramifiedChar c) {g g' : GL (Fin 2) F} {t t' : Eˣ}
    (ht : Algebra.norm F (t : E) = (g.val).det) (ht' : Algebra.norm F (t' : E) = (g'.val).det)
    (hm0 : mRow g ≠ 0) (hm0' : mRow g' ≠ 0)
    (hdet : modulus (g'.val).det = modulus (g.val).det)
    (hmm : modulus (mRow g') = modulus (mRow g))
    (hx : modulus (g.val).det ≤ modulus (mRow g) ^ 2 → xRow g' - xRow g ∈ 𝒪[F]) :
    val χ c g' t' = val (E := E) χ c g t := by
  have htt : modulus (t' : E) = modulus (t : E) := by
    rw [← modulus_norm (K := F), ← modulus_norm (K := F) (t : E), ht, ht', hdet]
  have hns : GL2LocalData.nsg E (mRow g') = GL2LocalData.nsg E (mRow g) := by
    have h1 := hη (Units.mk0 _ hm0')
    have h2 := hη (Units.mk0 _ hm0)
    rw [Units.val_mk0] at h1 h2
    rw [← h1, ← h2, char_congr η hηu (u := Units.mk0 _ hm0') (v := Units.mk0 _ hm0) (by simpa using hmm)]
  have hI : (intInd ((t' : E) * algebraMap F E (mRow g')⁻¹) : ℂ) =
      intInd ((t : E) * algebraMap F E (mRow g)⁻¹) :=
    intInd_congr (by
      rw [modulus_mul, modulus_mul, modulus_algebraMap (K := F), modulus_algebraMap (K := F),
        modulus_inv, modulus_inv, hmm, htt])
  unfold val
  rw [char_congr c hc htt, hdet, hmm, hns, hI]
  by_cases hz : (intInd ((t : E) * algebraMap F E (mRow g)⁻¹) : ℂ) = 0
  · simp only [hz, mul_zero]
  · have hO : (t : E) * algebraMap F E (mRow g)⁻¹ ∈ 𝒪[E] := by
      by_contra h
      exact hz (by rw [intInd, if_neg h])
    have hle : modulus (g.val).det ≤ modulus (mRow g) ^ 2 := by
      have h1 := modulus_le_one_iff.2 hO
      rw [modulus_mul, modulus_algebraMap (K := F), modulus_inv,
        ← modulus_norm (K := F) (t : E), ht] at h1
      have hb : 0 < modulus (mRow g) ^ 2 := pow_pos (modulus_pos hm0) 2
      rwa [inv_pow, ← div_eq_mul_inv, div_le_one₀ hb] at h1
    have hχx : χ (xRow g') = χ (xRow g) := by
      have h1 := isTrivialOn_addCharConductor hχ.1 hχ.2.1 (xRow g' - xRow g)
        (by rw [hχ.2.2]; exact mem_valBall_zero_iff.2 (hx hle))
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv] at h1
      exact mul_inv_eq_one.1 h1
    rw [hχx]

omit [MeasurableSpace F] [BorelSpace F] in
theorem mRow_one : mRow (1 : GL (Fin 2) F) = 1 := by
  simp [mRow]

omit [MeasurableSpace F] [BorelSpace F] in
theorem xRow_one : xRow (1 : GL (Fin 2) F) = 0 := by
  simp [xRow]

end Main

end GlobalTheory.CompanionTheory.SphTheta.InertAsm
