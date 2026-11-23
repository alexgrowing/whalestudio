import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.PrincCong

open Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_cj (w : Pl E) (x : w.adicCompletion E) : cj w (cj w x) = x := by
  by_cases h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)
  · obtain ⟨hc, he⟩ := GlobalTheory.ConjAtPlace.cj_spec w h
    have := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) E w).equalizer (hc.comp hc) continuous_id
      (funext fun k => by simp only [Function.comp_apply, id, he, IsCMField.complexConj_apply_apply])
    exact congrFun this x
  · rw [GlobalTheory.ConjAtPlace.cj_of_not w h]; rfl

theorem cj_lt_one (w : Pl E) {z : w.adicCompletion E} (hz : Valued.v z < 1) : Valued.v (cj w z) < 1 := by
  by_cases h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)
  · exact GlobalTheory.ConjAtPlace.lt_one_of_continuous _ (GlobalTheory.ConjAtPlace.cj_spec w h).1 hz
  · rw [GlobalTheory.ConjAtPlace.cj_of_not w h]; exact hz

theorem v_cj (w : Pl E) (x : w.adicCompletion E) : Valued.v (cj w x) = Valued.v x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hsx : cj w x ≠ 0 := fun h => hx (by rw [← cj_cj w x, h, map_zero])
  have p1 : 0 < Valued.v x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx)
  have p2 : 0 < Valued.v (cj w x) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hsx)
  rcases lt_trichotomy (Valued.v (cj w x)) (Valued.v x) with hlt | heq | hgt
  · exfalso
    have h1 : Valued.v (cj w x / x) < 1 := by rw [map_div₀, div_lt_one₀ p1]; exact hlt
    have h2 := cj_lt_one w h1
    rw [map_div₀ (cj w), cj_cj, map_div₀, div_lt_one₀ p2] at h2
    exact absurd h2 (not_lt.2 hlt.le)
  · exact heq
  · exfalso
    have h1 : Valued.v (x / cj w x) < 1 := by rw [map_div₀, div_lt_one₀ p2]; exact hgt
    have h2 := cj_lt_one w h1
    rw [map_div₀ (cj w), cj_cj, map_div₀, div_lt_one₀ p1] at h2
    exact absurd h2 (not_lt.2 hgt.le)

def congIdeal (w : Pl E) (k : ℕ) : Ideal (Ov E w) where
  carrier := {x | Valued.v (x : w.adicCompletion E) ≤ WithZero.exp (-(k : ℤ))}
  add_mem' := fun {a b} ha hb => by
    show Valued.v ((a : w.adicCompletion E) + b) ≤ _
    exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  zero_mem' := by
    show Valued.v ((0 : w.adicCompletion E)) ≤ _
    simp
  smul_mem' := fun c x hx => by
    show Valued.v ((c : w.adicCompletion E) * x) ≤ _
    have hc : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
    rw [map_mul]
    exact mul_le_of_le_one_of_le hc hx

end GlobalTheory.PrincCong

namespace GlobalTheory.PrincCong

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def congSub (w : Pl E) (n k : ℕ) : Subgroup (GLw n w) :=
  ((GeneralLinearGroup.map (Ideal.Quotient.mk (congIdeal w k)) : GL (Fin n) (Ov E w) →* _).ker).map
    (bc (Ov E w).subtype)

theorem mem_ker_iff (w : Pl E) (n k : ℕ) (h : GL (Fin n) (Ov E w)) :
    h ∈ (GeneralLinearGroup.map (Ideal.Quotient.mk (congIdeal w k)) : GL (Fin n) (Ov E w) →* _).ker ↔
      ∀ i j, Valued.v ((((h : Matrix (Fin n) (Fin n) (Ov E w)) i j : Ov E w) : w.adicCompletion E) -
        (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  apply forall_congr'; intro i; apply forall_congr'; intro j
  change Ideal.Quotient.mk _ ((h : Matrix (Fin n) (Fin n) (Ov E w)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j ↔ _
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq]
    rw [← map_one (Ideal.Quotient.mk (congIdeal w k)), Ideal.Quotient.eq]
    show Valued.v (((_ - 1 : Ov E w)) : w.adicCompletion E) ≤ _ ↔ _
    push_cast; rfl
  · simp only [Matrix.one_apply_ne hij, Ideal.Quotient.eq_zero_iff_mem, sub_zero]
    rfl

theorem mem_congSub_iff (w : Pl E) (n k : ℕ) (g : GLw n w) :
    g ∈ congSub w n k ↔ g ∈ GlobalTheory.LFun.KGL w n ∧ ∀ i j, Valued.v (g.val i j -
      (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, rfl⟩, (mem_ker_iff w n k h).1 hh⟩
  · rintro ⟨⟨h, rfl⟩, hg⟩
    exact ⟨h, (mem_ker_iff w n k h).2 hg, rfl⟩

end GlobalTheory.PrincCong

namespace GlobalTheory.PrincCong

open Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_mem_Ov (w : Pl E) (x : w.adicCompletion E) (hx : x ∈ Ov E w) : cj w x ∈ Ov E w := by
  change Valued.v (cj w x) ≤ 1
  rw [v_cj]; exact hx

theorem thL_mem_congSub (w : Pl E) (hw : ¬ IsSplitAt w) (n k : ℕ) (g : GLw n w) (hg : g ∈ congSub w n k) :
    thL n w g ∈ congSub w n k := by
  obtain ⟨h, hh, rfl⟩ := hg
  have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hw]
  rw [ht]
  let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (cj_mem_Ov w)
  have hI : congIdeal w k ≤ (congIdeal w k).comap c' := by
    intro x hx
    show Valued.v (cj w (x : w.adicCompletion E)) ≤ _
    rw [v_cj]; exact hx
  let c'' := Ideal.quotientMap (congIdeal w k) c' hI
  refine ⟨thetaGL n c' h, ?_, GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) h⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker] at hh ⊢
  rw [GlobalTheory.ThetaPull.map_thetaGL (Ideal.Quotient.mk (congIdeal w k)) c' c''
    (fun x => (Ideal.quotientMap_mk).symm) h, hh, map_one]

theorem isOpen_ball (w : Pl E) (m : ℤ) : IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} = {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_ball_subset (w : Pl E) {U : Set (w.adicCompletion E)} {x : w.adicCompletion E} (hU : U ∈ 𝓝 x) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y, Valued.v (y - x) ≤ WithZero.exp (-(N : ℤ)) → y ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1, fun N hN y hy => hγ ?_⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
  refine hy.trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hne]
  rw [WithZero.exp_lt_exp]
  omega

theorem isOpen_congSub (w : Pl E) (n k : ℕ) : IsOpen (congSub w n k : Set (GLw n w)) := by
  have hs : (congSub w n k : Set (GLw n w)) = (GlobalTheory.LFun.KGL w n : Set (GLw n w)) ∩
      ⋂ i, ⋂ j, {g : GLw n w | Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
        WithZero.exp (-(k : ℤ))} := by
    ext g
    simp only [SetLike.mem_coe, mem_congSub_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hs]
  refine (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  exact (isOpen_ball w _).preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)

theorem exists_mat_subset (w : Pl E) (n : ℕ) {C : Set (Matrix (Fin n) (Fin n) (w.adicCompletion E))}
    (hC : C ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E),
      (∀ i j, Valued.v (M i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(N : ℤ))) → M ∈ C := by
  have h1 : C ∈ Filter.pi fun i => Filter.pi fun j => 𝓝 ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) := by
    have e : 𝓝 (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
        Filter.pi fun i => Filter.pi fun j => 𝓝 ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) := by
      change 𝓝 (fun i j => (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) = _
      rw [nhds_pi]; congr 1; funext i; rw [nhds_pi]
    rw [← e]; exact hC
  obtain ⟨I, -, t, ht, hsub⟩ := Filter.mem_pi.1 h1
  have h2 : ∀ i, ∃ t' : Fin n → Set (w.adicCompletion E),
      (∀ j, t' j ∈ 𝓝 ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) ∧ Set.univ.pi t' ⊆ t i := by
    intro i
    obtain ⟨J, -, t', ht', hs'⟩ := Filter.mem_pi.1 (ht i)
    exact ⟨t', ht', fun x hx => hs' fun j _ => hx j (Set.mem_univ j)⟩
  choose t' ht' hs' using h2
  have h3 : ∀ i j, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y, Valued.v (y - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(N : ℤ)) → y ∈ t' i j := fun i j => exists_ball_subset w (ht' i j)
  choose N₀ hN₀ using h3
  refine ⟨Finset.univ.sup fun p : Fin n × Fin n => N₀ p.1 p.2, fun N hN M hM => hsub fun i _ => hs' i fun j _ => ?_⟩
  refine hN₀ i j N ?_ _ (hM i j)
  exact le_trans (Finset.le_sup (f := fun p : Fin n × Fin n => N₀ p.1 p.2) (Finset.mem_univ (i, j))) hN

end GlobalTheory.PrincCong

namespace GlobalTheory.PrincCong

open Filter Topology

end GlobalTheory.PrincCong
