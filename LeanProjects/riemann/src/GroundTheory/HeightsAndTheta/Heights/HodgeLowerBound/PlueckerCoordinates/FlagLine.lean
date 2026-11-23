import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.IsPlueckerCoord
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix

abbrev DL : ComponentDataHodge zeroSystem Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) := lineDataHodgeZero

def lineM : Unit → Fin DL.N → ℕ
  | _, ⟨0, _⟩ => 2
  | _, ⟨1, _⟩ => 1
  | _, ⟨_ + 2, _⟩ => 0

def lineGen : ∀ (τ : Unit) (i : Fin DL.N), Fin (lineM τ i) →
    ((Fin 2 → Ω) [⋀^Fin ((i : ℕ) + 1)]→ₗ[Ω] Ω)
  | _, ⟨0, _⟩ => fun m => AlternatingMap.ofSubsingleton Ω (Fin 2 → Ω) Ω (0 : Fin 1) (LinearMap.proj m)
  | _, ⟨1, _⟩ => fun _ => (Pi.basisFun Ω (Fin 2)).det
  | _, ⟨_ + 2, _⟩ => fun m => m.elim0

theorem twistFactor_zero (c : (k : Unit) → PBlk 2 k) : twistFactor DL.y c 0 = 1 := by
  simp [twistFactor]

theorem altFin1_apply (φ : (Fin 2 → Ω) [⋀^Fin 1]→ₗ[Ω] Ω) (v : Fin 1 → Fin 2 → Ω) :
    φ v = ∑ m, v 0 m * φ (fun _ => Pi.basisFun Ω (Fin 2) m) := by
  set ψ := (AlternatingMap.ofSubsingleton Ω (Fin 2 → Ω) Ω (0 : Fin 1)).symm φ
  have hψ : ∀ w, φ (fun _ => w) = ψ w := fun w => by
    conv_lhs => rw [← (AlternatingMap.ofSubsingleton Ω (Fin 2 → Ω) Ω (0 : Fin 1)).apply_symm_apply φ]
    rfl
  have hv : v = fun _ => v 0 := funext fun a => by rw [Subsingleton.elim a 0]
  rw [hv, hψ]
  simp only [hψ]
  conv_lhs => rw [← (Pi.basisFun Ω (Fin 2)).sum_repr (v 0)]
  simp [map_smul, smul_eq_mul]

theorem altFin1_eq (φ : (Fin 2 → Ω) [⋀^Fin 1]→ₗ[Ω] Ω) :
    φ = ∑ m : Fin 2, φ (fun _ => Pi.basisFun Ω (Fin 2) m) •
      AlternatingMap.ofSubsingleton Ω (Fin 2 → Ω) Ω (0 : Fin 1) (LinearMap.proj m) := by
  ext v
  rw [altFin1_apply, Fin.sum_univ_two, Fin.sum_univ_two, AlternatingMap.add_apply,
    AlternatingMap.smul_apply, AlternatingMap.smul_apply]
  simp [smul_eq_mul, mul_comm]

theorem lat_line (c : (k : Unit) → PBlk 2 k) (e : Fin 2 → Ω) :
    e ∈ (DL.W ()).lat c ↔ ∀ q, e q ∈ chartRing ℤ (segreCoord yLine) c :=
  mem_trivLat

theorem det_mem (c : (k : Unit) → PBlk 2 k) (e : Fin 2 → Fin 2 → Ω)
    (he : ∀ a q, e a q ∈ chartRing ℤ (segreCoord yLine) c) :
    (Pi.basisFun Ω (Fin 2)).det e ∈ chartRing ℤ (segreCoord yLine) c := by
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  exact sub_mem (mul_mem (he _ _) (he _ _)) (mul_mem (he _ _) (he _ _))

theorem basis_mem (c : (k : Unit) → PBlk 2 k) (m : Fin 2) :
    Pi.basisFun Ω (Fin 2) m ∈ (DL.W ()).lat c := by
  rw [lat_line]
  intro q
  simp only [Pi.basisFun_apply, Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

def linePlueckerData : PlueckerData DL where
  b := 0
  M := lineM
  M_ge := by
    rintro _ ⟨_ | _ | n, hi⟩
    · show Nat.choose 2 (0 + 1) ≤ 2
      decide
    · show Nat.choose 2 (0 + 1 + 1) ≤ 1
      decide
    · exact absurd hi (by show ¬ (n + 2 < 2); omega)
  gen := lineGen
  global := by
    rintro _ ⟨_ | _ | n, hi⟩ m c _ e he
    · rw [twistFactor_zero, mul_one]
      show e 0 m ∈ chartRing ℤ (segreCoord yLine) c
      exact (lat_line c (e 0)).1 (he 0) m
    · rw [twistFactor_zero, mul_one]
      exact det_mem c e fun a => (lat_line c (e a)).1 (he a)
    · exact absurd hi (by show ¬ (n + 2 < 2); omega)
  generates := by
    rintro _ ⟨_ | _ | n, hi⟩ c _ φ hφ
    · refine ⟨fun m => φ (fun _ => Pi.basisFun Ω (Fin 2) m), fun m => ?_, altFin1_eq φ⟩
      have := hφ (fun _ => Pi.basisFun Ω (Fin 2) m) fun _ => basis_mem c m
      rwa [twistFactor_zero, mul_one] at this
    · refine ⟨fun _ => φ (Pi.basisFun Ω (Fin 2)), fun _ => ?_, ?_⟩
      · have := hφ (Pi.basisFun Ω (Fin 2)) fun a => basis_mem c a
        rwa [twistFactor_zero, mul_one] at this
      · show φ = ∑ m : Fin 1, φ (Pi.basisFun Ω (Fin 2)) • (Pi.basisFun Ω (Fin 2)).det
        rw [Fin.sum_univ_one]
        exact φ.eq_smul_basis_det (Pi.basisFun Ω (Fin 2))
    · exact absurd hi (by show ¬ (n + 2 < 2); omega)

abbrev PL : PlueckerData DL := linePlueckerData

theorem isValueAt_intCast (z : (Σ _ : Unit, Fin 2) → ℂ) (a : ℤ) : IsValueAt yLine (a : Ω) z a :=
  ⟨0, C a, 1, isMultiHomog_C_zero a, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

theorem isTwValueAt_intCast (c : (k : Unit) → PBlk 2 k) (z : (Σ _ : Unit, Fin 2) → ℂ)
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) (a : ℤ) : IsTwValueAt DL.y c 0 (a : Ω) z a :=
  ⟨hz, a, by rw [twistFactor_zero, mul_one]; exact isValueAt_intCast z a, by simp⟩

def detInt (q : Fin 2 → Fin 2) : ℤ := (Matrix.of fun p a => if q a = p then (1 : ℤ) else 0).det

theorem basis_det_comp (q : Fin 2 → Fin 2) :
    (Pi.basisFun Ω (Fin 2)).det (Pi.basisFun Ω (Fin 2) ∘ q) = (detInt q : Ω) := by
  rw [Module.Basis.det_apply, detInt, Int.cast_det]
  congr 1
  ext p a
  simp [Module.Basis.toMatrix_apply, Pi.single_apply, eq_comm]

theorem sum_fin_two_arrow (F : (Fin 2 → Fin 2) → ℂ) :
    ∑ q : Fin 2 → Fin 2, F q = F ![0, 0] + F ![0, 1] + (F ![1, 0] + F ![1, 1]) := by
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_two]
  rfl

theorem sum_det_expand (g : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ q : Fin 2 → Fin 2, (∏ a, g (q a) a) * (detInt q : ℂ) = g.det := by
  rw [sum_fin_two_arrow, Matrix.det_fin_two]
  simp [detInt, Matrix.det_fin_two, Fin.prod_univ_two]
  ring

theorem pluecker_step1 (i0 : Fin 2) (z : (Σ _ : Unit, Fin 2) → ℂ) (hz0 : z ⟨(), i0⟩ ≠ 0)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 2) :
    IsPlueckerCoord DL.y (fun _ => i0) 0
      (AlternatingMap.ofSubsingleton Ω (Fin 2 → Ω) Ω (0 : Fin 1) (LinearMap.proj m))
      (Pi.basisFun Ω (Fin 2)) z (firstCols g 1 (by decide)) (g m 0) := by
  refine ⟨fun q => ((if q 0 = m then 1 else 0 : ℤ) : ℂ), fun q => ?_, ?_⟩
  · have hval : (AlternatingMap.ofSubsingleton Ω (Fin 2 → Ω) Ω (0 : Fin 1) (LinearMap.proj m))
        (Pi.basisFun Ω (Fin 2) ∘ q) = ((if q 0 = m then 1 else 0 : ℤ) : Ω) := by
      show (Pi.basisFun Ω (Fin 2) (q 0)) m = _
      rw [Pi.basisFun_apply, Pi.single_apply]
      by_cases h : q 0 = m
      · simp [h]
      · simp [h, Ne.symm h]
    rw [hval]
    exact isTwValueAt_intCast _ _ (fun _ => hz0) _
  · rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
    simp [firstCols, Equiv.funUnique]

theorem pluecker_step2 (i0 : Fin 2) (z : (Σ _ : Unit, Fin 2) → ℂ) (hz0 : z ⟨(), i0⟩ ≠ 0)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    IsPlueckerCoord DL.y (fun _ => i0) 0 (Pi.basisFun Ω (Fin 2)).det
      (Pi.basisFun Ω (Fin 2)) z (firstCols g 2 le_rfl) g.det := by
  refine ⟨fun q => (detInt q : ℂ), fun q => ?_, ?_⟩
  · rw [basis_det_comp]
    exact isTwValueAt_intCast _ _ (fun _ => hz0) _
  · rw [← sum_det_expand g]
    simp [firstCols]

theorem mem_flagPts_line (u : (Σ k : YBlk DL, ιY PL k) → ℂ)
    (hz : ∃ i, zPart PL u ⟨(), i⟩ ≠ 0) (h1 : ∃ m : Fin 2, wPart PL u ((), ⟨0, by decide⟩) m ≠ 0)
    (h2 : wPart PL u ((), ⟨1, by decide⟩) (0 : Fin 1) ≠ 0) : u ∈ flagPts PL := by
  obtain ⟨i0, hi0⟩ := hz
  refine ⟨mem_mcPts_line.2 ⟨i0, hi0⟩, fun τ => ?_⟩
  obtain rfl : τ = () := rfl
  set w1 : Fin 2 → ℂ := wPart PL u ((), ⟨0, by decide⟩) with hw1
  set w2 : ℂ := wPart PL u ((), ⟨1, by decide⟩) (0 : Fin 1) with hw2
  have hw1ne : w1 ≠ 0 := fun h => by obtain ⟨m, hm⟩ := h1; exact hm (congrFun h m)
  set t : Fin 2 → ℂ := if w1 0 ≠ 0 then ![0, 1] else ![1, 0] with ht
  set g : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![w1 0, t 0], ![w1 1, t 1]] with hg
  have hdet : g.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    by_cases h0 : w1 0 ≠ 0
    · simp [hg, ht, h0]
    · have h1' : w1 1 ≠ 0 := by
        intro h1'
        apply hw1ne
        funext p
        fin_cases p
        · simpa using h0
        · simpa using h1'
      simp [hg, ht, h0, h1']
  have hz0 : zPart PL u ⟨(), i0⟩ ≠ 0 := hi0
  refine ⟨fun _ => i0, 1, Pi.basisFun Ω (Fin 2), g,
    fun i => if (i : ℕ) = 0 then 1 else w2 / g.det,
    ⟨segreCoord_line_ne_zero i0, one_mem _, one_ne_zero, (Pi.basisFun Ω (Fin 2)).linearIndependent,
      trivial_frame_iff _ 2 _⟩, inFrameDomain_line hz0, hdet, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs
    · exact one_ne_zero
    · exact div_ne_zero h2 hdet
  · rintro ⟨_ | _ | n, hi⟩ m
    · refine ⟨g m 0, pluecker_step1 i0 (zPart PL u) hz0 g m, ?_⟩
      show wPart PL u ((), ⟨0, hi⟩) m = (if (0 : ℕ) = 0 then 1 else w2 / g.det) * g m 0
      rw [if_pos rfl, one_mul]
      have hm : g m 0 = w1 m := by
        fin_cases m <;> rfl
      rw [hm]
    · refine ⟨g.det, pluecker_step2 i0 (zPart PL u) hz0 g, ?_⟩
      have hm0 : (m : ℕ) = 0 := by
        have h := m.isLt
        change (m : ℕ) < 1 at h
        omega
      show wPart PL u ((), ⟨0 + 1, hi⟩) m = (if (0 + 1 : ℕ) = 0 then 1 else w2 / g.det) * g.det
      rw [if_neg (by omega), div_mul_cancel₀ _ hdet, hw2]
      have : m = (0 : Fin 1) := Fin.ext hm0
      rw [this]
    · exact absurd hi (by show ¬ (n + 2 < 2); omega)

theorem PY_line : PY PL = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot]
  have hvan : ∀ u ∈ flagPts PL, eval u (map (Int.castRingHom ℂ) f) = 0 := by
    intro u hu
    have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf u) hu
    simpa using this
  have hzero : map (Int.castRingHom ℂ) f = 0 := by
    refine funext_set (fun _ => ({0}ᶜ : Set ℂ)) (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl) ?_
    intro u hu
    rw [map_zero, hvan u (mem_flagPts_line u ⟨0, hu _ trivial⟩ ⟨0, hu _ trivial⟩ (hu _ trivial))]
  exact MvPolynomial.map_injective _ (Int.castRingHom ℂ).injective_int (by rw [hzero, map_zero])

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
