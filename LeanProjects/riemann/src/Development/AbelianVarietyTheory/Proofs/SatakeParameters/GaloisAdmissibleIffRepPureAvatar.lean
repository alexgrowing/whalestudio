import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.GaloisRepresentations

noncomputable section

namespace GlobalTheory.GaloisInputCompare

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations.At GlobalTheory.IndefiniteRowSideFullHecke.GaloisRepresentations

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem norm_le_one_of_isIntegral {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := K)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff] at h
  exact_mod_cast h

theorem exists_inducesW (i : N.Loc) (τ : H.E →+* Qbar (N.l i)) :
    ∃ w ∈ placesOver H.E (N.l i), InducesW N i τ w := by
  have hle : ∀ x : 𝓞 H.E, ‖τ (x : H.E)‖ ≤ 1 := fun x =>
    norm_le_one_of_isIntegral (map_isIntegral_int τ (RingOfIntegers.isIntegral_coe x))
  let I : Ideal (𝓞 H.E) :=
    { carrier := {x | ‖τ (x : H.E)‖ < 1}
      zero_mem' := by simp
      add_mem' := fun {x y} hx hy => by
        change ‖τ ((x + y : 𝓞 H.E) : H.E)‖ < 1
        rw [show ((x + y : 𝓞 H.E) : H.E) = x + y from rfl, map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      smul_mem' := fun c x hx => by
        change ‖τ ((c * x : 𝓞 H.E) : H.E)‖ < 1
        rw [show ((c * x : 𝓞 H.E) : H.E) = c * x from rfl, map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) hx }
  have hI : ∀ x : 𝓞 H.E, x ∈ I ↔ ‖τ (x : H.E)‖ < 1 := fun x => Iff.rfl
  have hl : ((N.l i : ℕ) : 𝓞 H.E) ∈ I := by
    rw [hI, show (((N.l i : ℕ) : 𝓞 H.E) : H.E) = (N.l i : ℕ) by simp, map_natCast,
      ← map_natCast (algebraMap ℚ_[N.l i] (PadicAlgCl (N.l i))), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hP : I.IsPrime := by
    refine ⟨fun h => ?_, fun {x y} h => ?_⟩
    · have := (hI 1).1 (h ▸ Submodule.mem_top)
      simp at this
    · rw [hI, show ((x * y : 𝓞 H.E) : H.E) = x * y from rfl, map_mul, norm_mul] at h
      by_contra hn
      rw [not_or, hI, hI, not_lt, not_lt] at hn
      exact absurd h (not_lt.2 (one_le_mul_of_one_le_of_one_le hn.1 hn.2))
  refine ⟨⟨I, hP, fun h => ?_⟩, hl, fun x => (hI x).symm⟩
  rw [h, Ideal.mem_bot] at hl
  exact (N.lPrime i).out.ne_zero (by exact_mod_cast hl)

def ClauseRep (i : N.Loc) : Prop :=
  ∀ a, 1 ≤ a → ∀ π : A.CG a, A.csd π → A.ralg π →
      ∃ ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)),
        Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) ∧
        IsSSRep ρ ∧
        (∀ w, w ∉ placesOver H.E (N.l i) →
          A.wdOf i ρ w = A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2) ∧ A.tempered (A.locG π w)) ∧
        (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧
          (∀ τ, InducesW N i τ w → A.jumpsW i ρ τ = A.jumpsInf i π τ) ∧
          A.wdOf i ρ w = A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2))

def ClausePure : Prop :=
  ∀ a (π : A.CG a), A.ralg π → ∃ w₀ : ℂ, ∀ τ : H.E →+* ℂ,
      A.infG π (τ.comp (H.conj : H.E ≃ₐ[ℚ] H.E).toRingEquiv.toRingHom) = (A.infG π τ).map (w₀ - ·)

def ClauseChar (i : N.Loc) : Prop :=
  ∀ (χ : A.CG 1) (s : ℝ), (∀ τ : H.E →+* ℂ, ∀ z ∈ A.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) →
      ∃ ρ : G H.E N.Om →* GL (Fin 1) (Qbar (N.l i)), ContQ N i ρ ∧
        (∀ w, w ∉ placesOver H.E (N.l i) → A.wdOf i ρ w = A.lpTw (A.locG χ w) s) ∧
        ∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧ A.wdOf i ρ w = A.lpTw (A.locG χ w) s ∧
          ∀ τ, InducesW N i τ w → (A.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) =
            (A.infG χ ((A.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ)))

def PureRegular : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → A.ralg π →
    ∃ u : ℤ, ∀ τ : H.E →+* ℂ, A.infG π ((starRingEnd ℂ).comp τ) = (A.infG π τ).map (fun z => (u : ℂ) - z)

def PureSingular : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → IsAlg N A π → ¬ A.ralg π →
    ∃ u : ℤ, ∀ τ : H.E →+* ℂ, A.infG π ((starRingEnd ℂ).comp τ) = (A.infG π τ).map (fun z => (u : ℂ) - z)

def SelfDualWeightZero : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → IsAlg N A π → A.csd π →
    ∀ τ : H.E →+* ℂ, A.infG π ((starRingEnd ℂ).comp τ) = (A.infG π τ).map (fun z => -z)

open Classical in

def padded : NAut N :=
  { A with
    CG := fun a => A.CG a × Option ((H.E →+* ℂ) → ℂ)
    csd := fun p => A.csd p.1
    ralg := fun {a} p => A.ralg p.1 ∧ (2 ≤ a → p.2 = none)
    locG := fun p => A.locG p.1
    locG_dim := fun p => A.locG_dim p.1
    locG_unr_ae := fun p => A.locG_unr_ae p.1
    tw := fun p χ => (A.tw p.1 χ.1, p.2.map fun g τ => g τ + (A.infG χ.1 τ).sum)
    locG_tw := fun p χ => A.locG_tw p.1 χ.1
    infG := fun {a} p τ => if 2 ≤ a then p.2.elim (A.infG p.1 τ) fun g => Multiset.replicate a (g τ) else A.infG p.1 τ
    infG_card := fun {a} p τ => by
      obtain ⟨π, _ | g⟩ := p <;> by_cases h : 2 ≤ a <;> simp [h, A.infG_card]
    ralg_def := fun {a} p => by
      obtain ⟨π, _ | g⟩ := p
      · simpa using A.ralg_def π
      · by_cases h : 2 ≤ a
        · simp only [h, if_true, Option.elim, forall_true_left, reduceCtorEq, and_false, false_iff]
          intro hh
          obtain ⟨τ⟩ : Nonempty (H.E →+* ℂ) := inferInstance
          have := Multiset.nodup_iff_count_le_one.1 (hh τ).1 (g τ)
          rw [Multiset.count_replicate_self] at this
          omega
        · simpa [h] using A.ralg_def π
    infG_tw := fun {a} p χ τ s hs => by
      have hs' : A.infG χ.1 τ = {s} := by simpa using hs
      obtain ⟨π, _ | g⟩ := p <;> by_cases h : 2 ≤ a <;> simp [h, hs', A.infG_tw _ _ _ _ hs']
    csd_tw := fun p χ => A.csd_tw p.1 χ.1
    csd_unr := fun p => A.csd_unr p.1
    muC := fun i => (A.muC i, none)
    etaT := (A.etaT, none)
    etaTinv := (A.etaTinv, none)
    jumpsInf := fun i _ p => A.jumpsInf i p.1
    jumpsInf_def := fun i a p τ hr => by
      obtain ⟨π, o⟩ := p
      by_cases h : 2 ≤ a
      · obtain rfl : o = none := hr.2 h
        simpa using A.jumpsInf_def i π τ hr.1
      · simpa [h] using A.jumpsInf_def i π τ hr.1 }

end GlobalTheory.GaloisInputCompare
