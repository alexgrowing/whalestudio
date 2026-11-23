import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.SmallRadAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.BallLev
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman

noncomputable section

open ValuativeRel Matrix GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem conj_entry (d : Fin n → kˣ) (g : GL (Fin n) k) (i j : Fin n) :
    (((diagT k (Fin n) d)⁻¹ * g * diagT k (Fin n) d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (d i : k)⁻¹ * (g : Matrix (Fin n) (Fin n) k) i j * (d j : k) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp

private theorem conj_ball {r : ValueGroupWithZero k} {d : Fin n → kˣ} (hd : ∀ i, valuation k (d i : k) = 1)
    {g : GL (Fin n) k} (hg : g ∈ ball n r) :
    (diagT k (Fin n) d)⁻¹ * g * diagT k (Fin n) d ∈ ball n r := by
  intro i j
  rw [conj_entry]
  by_cases h : i = j
  · subst h
    have e : (d i : k)⁻¹ * (g : Matrix (Fin n) (Fin n) k) i i * (d i : k) = (g : Matrix (Fin n) (Fin n) k) i i := by
      have := (d i).ne_zero
      field_simp
    rw [e]
    exact hg i i
  · have := hg i j
    rw [Matrix.one_apply_ne h, sub_zero] at this ⊢
    rw [map_mul, map_mul, hd j, mul_one, map_inv₀, hd i, inv_one, one_mul]
    exact this

private theorem diag_ball {r : ValueGroupWithZero k} {a : GL (Fin n) k} (ha : a ∈ ball n r) {d : Fin n → kˣ}
    (hd : ∀ i, valuation k (d i : k) = 1)
    (h : ∀ i, ((a * diagT k (Fin n) d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = 1) :
    diagT k (Fin n) d ∈ ball n r := by
  intro i j
  rw [val_diagT]
  by_cases hij : i = j
  · subst hij
    have e := h i
    rw [Units.val_mul, val_diagT, Matrix.mul_diagonal] at e
    have e' : (d i : k) - 1 = (d i : k) * -((a : Matrix (Fin n) (Fin n) k) i i - 1) := by
      linear_combination e
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, e', map_mul, hd i, one_mul, Valuation.map_neg]
    have := ha i i
    rwa [Matrix.one_apply_eq] at this
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, sub_zero, map_zero]
    exact zero_le'

end

theorem levOf : LevOf := by
  intro k _ _ _ _ n r h0 h1 D hDc hDv
  obtain ⟨B, hB, hBo, hBc⟩ := ballSub k n r h0 h1
  obtain ⟨hBI, hBd⟩ := ballLev k n r h0 h1 B hB
  have mB : ∀ {g : GL (Fin n) k}, g ∈ B ↔ g ∈ ball n r := fun {g} => by rw [← SetLike.mem_coe, hB]
  have hconj : ∀ d ∈ D, ∀ g ∈ B, (diagT k (Fin n) d)⁻¹ * g * diagT k (Fin n) d ∈ B :=
    fun d hd g hg => mB.2 (conj_ball (hDv d hd) (mB.1 hg))
  have hconj' : ∀ d ∈ D, ∀ g ∈ B, diagT k (Fin n) d * g * (diagT k (Fin n) d)⁻¹ ∈ B := fun d hd g hg => by
    have := hconj d⁻¹ (D.inv_mem hd) g hg
    rwa [map_inv, inv_inv] at this
  have hcomm : ∀ s t : Fin n → kˣ, diagT k (Fin n) s * diagT k (Fin n) t = diagT k (Fin n) t * diagT k (Fin n) s :=
    fun s t => by rw [← map_mul, ← map_mul, mul_comm]
  let K : Subgroup (GL (Fin n) k) :=
    { carrier := {g | ∃ a ∈ B, ∃ d ∈ D, g = a * diagT k (Fin n) d}
      one_mem' := ⟨1, B.one_mem, 1, D.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, d, hd, rfl⟩ ⟨a', ha', d', hd', rfl⟩
        refine ⟨a * (diagT k (Fin n) d * a' * (diagT k (Fin n) d)⁻¹), B.mul_mem ha (hconj' d hd a' ha'), d * d',
          D.mul_mem hd hd', ?_⟩
        rw [map_mul]
        group
      inv_mem' := by
        rintro _ ⟨a, ha, d, hd, rfl⟩
        refine ⟨(diagT k (Fin n) d)⁻¹ * a⁻¹ * diagT k (Fin n) d, hconj d hd _ (B.inv_mem ha), d⁻¹, D.inv_mem hd, ?_⟩
        rw [map_inv]
        group }
  have hK : ∀ {g}, g ∈ K ↔ ∃ a ∈ B, ∃ d ∈ D, g = a * diagT k (Fin n) d := Iff.rfl
  have hBK : B ≤ K := fun a ha => ⟨a, ha, 1, D.one_mem, by simp⟩
  have hDK : ∀ d ∈ D, diagT k (Fin n) d ∈ K := fun d hd => ⟨1, B.one_mem, d, hd, by simp⟩
  have hK1 : ∀ g ∈ K, (∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1) → g ∈ B := by
    rintro _ ⟨a, ha, d, hd, rfl⟩ h
    exact B.mul_mem ha (mB.2 (diag_ball (mB.1 ha) (hDv d hd) h))
  have hdc : Continuous (diagT k (Fin n)) := (continuous_leviEmb k _).comp (continuous_leviTorus k (Fin n))
  refine ⟨K, fun g => ⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rintro ⟨a, ha, d, hd, rfl⟩
    exact ⟨a, mB.1 ha, d, hd, rfl⟩
  · rintro ⟨a, ha, d, hd, rfl⟩
    exact ⟨a, mB.2 ha, d, hd, rfl⟩
  · have := (hBc.prod hDc).image (f := fun p : GL (Fin n) k × (Fin n → kˣ) => p.1 * diagT k (Fin n) p.2)
      (continuous_fst.mul (hdc.comp continuous_snd))
    convert this using 1
    ext g
    constructor
    · rintro ⟨a, ha, d, hd, rfl⟩
      exact ⟨(a, d), ⟨ha, hd⟩, rfl⟩
    · rintro ⟨⟨a, d⟩, ⟨ha, hd⟩, rfl⟩
      exact ⟨a, ha, d, hd, rfl⟩
  · exact Subgroup.isOpen_mono hBK hBo
  · rintro _ ⟨a, ha, d, hd, rfl⟩
    obtain ⟨u, hu, d', hd', c, hc, e⟩ := hBI.fact a ha
    refine ⟨u, ⟨hBK hu.1, hu.2⟩, d' * d, ?_, (diagT k (Fin n) d)⁻¹ * c * diagT k (Fin n) d,
      ⟨hBK (hconj d hd c hc.1), ?_⟩, ?_⟩
    · rw [map_mul]
      exact K.mul_mem (hBK hd') (hDK d hd)
    · have := GlobalTheory.IwahoriTraceProof.conj_mem_unipBLower d⁻¹ hc.2
      rwa [map_inv, inv_inv] at this
    · rw [e, map_mul]
      group
  · intro t ht u hu
    exact hBK (hBI.up t ht u ⟨hK1 u hu.1 ((mem_unipB k).1 hu.2).2, hu.2⟩)
  · intro t ht c hc
    exact hBK (hBI.low t ht c ⟨hK1 c hc.1 (GlobalTheory.IwahoriTraceProof.mem_unipBLower.1 hc.2).2, hc.2⟩)
  · intro t
    ext g
    constructor
    · rintro ⟨_, ⟨a, ha, d, hd, rfl⟩, _, ⟨a', ha', d', hd', rfl⟩, rfl⟩
      refine ⟨a, mB.1 ha, (diagT k (Fin n) d')⁻¹ * a' * diagT k (Fin n) d', mB.1 (hconj d' hd' a' ha'),
        t * (d * d'), ⟨d * d', D.mul_mem hd hd', rfl⟩, ?_⟩
      have e := hcomm d t
      rw [map_mul, map_mul]
      calc a * diagT k (Fin n) d * diagT k (Fin n) t * (a' * diagT k (Fin n) d')
          = a * (diagT k (Fin n) d * diagT k (Fin n) t) * (a' * diagT k (Fin n) d') := by group
        _ = a * (diagT k (Fin n) t * diagT k (Fin n) d) * (a' * diagT k (Fin n) d') := by rw [e]
        _ = _ := by group
    · rintro ⟨a, ha, b, hb, _, ⟨d, hd, rfl⟩, rfl⟩
      refine ⟨a * diagT k (Fin n) d, ⟨a, mB.2 ha, d, hd, rfl⟩, b, hBK (mB.2 hb), ?_⟩
      have e := hcomm d t
      rw [map_mul]
      calc a * (diagT k (Fin n) t * diagT k (Fin n) d) * b
          = a * (diagT k (Fin n) d * diagT k (Fin n) t) * b := by rw [e]
        _ = _ := by group

end UpperTheory.Gal.InertialTypesAlt.L
