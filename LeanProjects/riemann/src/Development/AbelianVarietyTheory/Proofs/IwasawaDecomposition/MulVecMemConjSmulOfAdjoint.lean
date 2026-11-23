import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtIdMulSupNatCastConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemExtIdSmulIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProdLeOfIsRadical

open Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Pointwise Classical

namespace GlobalTheory.Mem.RowsBundle

theorem exists_conj_involution (I : AutInst) :
    ∃ cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E), (∀ v, cj (cj v) = v) ∧
      (∀ v v', IsConj I v v' ↔ v' = cj v) ∧
      ∀ (m : ℕ) (v : HeightOneSpectrum (𝓞 I.E)), (m : 𝓞 I.E) ∈ v.asIdeal → (m : 𝓞 I.E) ∈ (cj v).asIdeal := by
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  have hsurj : Function.Surjective st := fun a => ⟨st a, hst2 a⟩
  let cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E) := fun v => v.comap st hsurj
  have hcj : ∀ v a, a ∈ (cj v).asIdeal ↔ st a ∈ v.asIdeal := fun v a => Iff.rfl
  refine ⟨cj, fun v => HeightOneSpectrum.ext (Ideal.ext fun a => by rw [hcj, hcj, hst2]), fun v v' => ?_,
    fun m v hv => by rw [hcj, map_natCast]; exact hv⟩
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun b => ?_)
    rw [hcj]
    exact (h (st b) b (by rw [hst, star_star])).symm
  · rintro rfl a b hab
    have : b = st a := RingOfIntegers.ext hab
    subst this
    rw [hcj, hst2]

theorem meets_iff_card {X P : Type} (cj : X → X) (hc : ∀ v, cj (cj v) = v) (S : Set X) (hS : ∀ v ∈ S, cj v ∈ S)
    {m : ℕ} (hm : 0 < m) (hcard : S.ncard = 2 * m) (w : P → X) (hw : ∀ v, w v ∈ S) (hinj : Function.Injective w)
    (hn : ∀ v v', w v' ≠ cj (w v)) : (∀ u ∈ S, ∃ v, u = w v ∨ u = cj (w v)) ↔ Nat.card P = m := by
  let f : P ⊕ P → S := Sum.elim (fun v => ⟨w v, hw v⟩) (fun v => ⟨cj (w v), hS _ (hw v)⟩)
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) h
    · exact congrArg _ (hinj (congrArg Subtype.val h))
    · exact absurd (congrArg Subtype.val h) (hn _ _)
    · exact absurd (congrArg Subtype.val h).symm (hn _ _)
    · have h' : cj (w a) = cj (w b) := congrArg Subtype.val h
      exact congrArg _ (hinj (by rw [← hc (w a), h', hc]))
  have hS' : Nat.card S = 2 * m := hcard
  haveI : Finite S := Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite P := Finite.of_injective _ (hf.comp Sum.inl_injective)
  have hP : Nat.card (P ⊕ P) = Nat.card P + Nat.card P := Nat.card_sum
  constructor
  · intro h
    have hs : Function.Surjective f := fun u => by
      obtain ⟨v, e | e⟩ := h u.1 u.2
      · exact ⟨Sum.inl v, Subtype.ext e.symm⟩
      · exact ⟨Sum.inr v, Subtype.ext e.symm⟩
    have := Nat.card_eq_of_bijective f ⟨hf, hs⟩
    omega
  · intro h u hu
    have hb := (Nat.bijective_iff_injective_and_card f).2 ⟨hf, by omega⟩
    obtain ⟨v | v, e⟩ := hb.2 ⟨u, hu⟩
    · exact ⟨v, Or.inl (congrArg Subtype.val e).symm⟩
    · exact ⟨v, Or.inr (congrArg Subtype.val e).symm⟩

theorem isChoice_of_card (I : AutInst) (g : Fin 2 → ℕ) (hg : ∀ k, (g k).Prime) (hne : g 0 ≠ g 1)
    (hsp : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal →
      Ideal.absNorm v.asIdeal = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ v.asIdeal ^ 2 ∧ ¬ IsConj I v v)
    {m : ℕ} (hm : 0 < m)
    (hcard : ∀ k, {v : HeightOneSpectrum (𝓞 I.E) | ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal}.ncard = 2 * m) :
    (∃ w : ∀ _ : Fin 2, Fin m → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin m) w) ∧
      ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)),
        (∀ k, Fintype.card (Pl k) = m) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) →
        (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
  obtain ⟨cj, hc, hconj, hmem⟩ := exists_conj_involution I
  obtain ⟨Pl₀, w₀, -, h₀⟩ := exists_choice I g hg hne hsp
  have key : ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)),
      (∀ k, Fintype.card (Pl k) = m) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) →
      (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
    intro Pl _ w h1 h2 h3 h4
    refine ⟨hg, hne, h₀.2.2.1, fun k v => ⟨h2 k v, (hsp k _ (h2 k v)).1⟩, h3, h4, fun k u hu => ?_⟩
    simp only [hconj] at h4 ⊢
    exact (meets_iff_card cj hc _ (hmem (g k)) hm (hcard k) (w k) (h2 k) (h3 k) (h4 k)).2
      (by rw [Nat.card_eq_fintype_card, h1]) u hu
  refine ⟨?_, key⟩
  obtain ⟨-, -, -, h2, h3, h4, h5⟩ := h₀
  have hP : ∀ k, Nat.card (Pl₀ k) = m := fun k => by
    simp only [hconj] at h4 h5
    exact (meets_iff_card cj hc _ (hmem (g k)) hm (hcard k) (w₀ k) (fun v => (h2 k v).1) (h3 k) (h4 k)).1 (h5 k)
  have e : ∀ k, Fin m ≃ Pl₀ k := fun k =>
    haveI : Finite (Pl₀ k) := Nat.finite_of_card_ne_zero (by rw [hP]; omega)
    (Finite.equivFinOfCardEq (hP k)).symm
  exact ⟨fun k v => w₀ k (e k v), key _ _ (fun _ => Fintype.card_fin m) (fun k v => (h2 k _).1)
    (fun k => (h3 k).comp (e k).injective) fun k v v' => h4 k _ _⟩

section Unip

variable {I : AutInst}

theorem hAf_eq_dot (u v : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I u v =
    (fun i => sigR I.cm.sig (Af I.F) (u i)) ⬝ᵥ (I.J.map (inclE (F := I.F) (Af I.F)) *ᵥ v) := by
  simp only [hAf, hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hAf_inv_mulVec (x : I.Gf) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I (I.fmat x⁻¹ *ᵥ y) z = hAf I y (I.fmat x *ᵥ z) := by
  have hx : cT (sigR I.cm.sig (Af I.F)) (I.fmat x⁻¹) * I.J.map (inclE (F := I.F) (Af I.F)) * I.fmat x⁻¹ = _ := x⁻¹.2
  have hs : (fun i => sigR I.cm.sig (Af I.F) ((I.fmat x⁻¹ *ᵥ y) i)) =
      (fun i => sigR I.cm.sig (Af I.F) (y i)) ᵥ* cT (sigR I.cm.sig (Af I.F)) (I.fmat x⁻¹) := by
    funext i
    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, cT, map_sum, mul_comm]
  have h1 : I.fmat x⁻¹ * I.fmat x = 1 := by rw [← fmat_mul, inv_mul_cancel, fmat_one]
  rw [hAf_eq_dot, hAf_eq_dot, hs, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  conv_rhs => rw [← hx, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem hAf_pow_adjoint (x : I.Gf) (m : ℕ) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I ((I.fmat x⁻¹ - 1) ^ m *ᵥ y) z = hAf I y ((I.fmat x - 1) ^ m *ᵥ z) := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← ih, Matrix.sub_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]
    generalize (I.fmat x⁻¹ - 1) ^ m *ᵥ y = u
    have h := hAf_inv_mulVec x u z
    simp only [hAf, hform, Pi.sub_apply, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib] at h ⊢
    rw [h]

theorem sub_one_pow_mem {x : I.Gf} (hx : x ∈ I.Kset) (m : ℕ) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    (I.fmat x - 1) ^ m *ᵥ y ∈ I.Lf := by
  induction m with
  | zero => simpa using hy
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (mulVec_mem hx ih) ih

end Unip

end GlobalTheory.Mem.RowsBundle
