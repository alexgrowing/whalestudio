import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitShear

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem centre_volume : VolZZ σ v := by
  intro g r TF TF' m hS hg hTF hTF' hdiff μ hμ hm
  haveI := hμ
  obtain ⟨D⟩ := exists_SD hS
  have hp0 : ∀ s t, D.p 0 (D.pt s t) = s := fun s t => (D.p_pt s t).1
  have hp1 : ∀ s t, D.p 1 (D.pt s t) = t := fun s t => (D.p_pt s t).2
  have hg0 : (g : Fv F v) ≠ 0 := natCast_ne_zero v hg
  have hgO : (g : Fv F v) ∈ v.adicCompletionIntegers F := natCast_mem _ g
  have hT1 : ∀ a b, sigR (Fv F v) σ (TF b a) = TF a b := hTF
  have hT1' : ∀ a b, sigR (Fv F v) σ (TF' b a) = TF' a b := hTF'
  have hf : ∀ a b, D.p 1 (TF a b) = D.p 0 (TF b a) := fun a b => by rw [← hT1 a b, (D.p_sig _).2]
  have hf' : ∀ a b, D.p 1 (TF' a b) = D.p 0 (TF' b a) := fun a b => by rw [← hT1' a b, (D.p_sig _).2]
  obtain ⟨t, ht⟩ : ∃ t : Fin (r + 1) × Fin (r + 1) → Fv F v, ∀ k, t k = alp v r k.1 * alp v r k.2 :=
    ⟨_, fun _ => rfl⟩
  have ht0 : ∀ k, t k ≠ 0 := fun k => by rw [ht]; exact mul_ne_zero (alp_ne_zero v r _) (alp_ne_zero v r _)
  obtain ⟨y, hy⟩ : ∃ y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E,
      ∀ k, y k = D.pt (((g : Fv F v)⁻¹) ^ 2 * t k) ((g : Fv F v)⁻¹ * t k) := ⟨_, fun _ => rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E,
      ∀ k, κ k = D.pt (-(D.p 0 (TF k.1 k.2) + D.p 0 (TF' k.1 k.2)) / t k) (-(D.p 0 (TF k.2 k.1)) / t k) :=
    ⟨_, fun _ => rfl⟩
  have hd : ∀ i j, (D.p 0 (TF' i j) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
    intro i j
    have := hdiff i j
    rw [D.mem_iff] at this
    simpa only [map_mul, map_sub, D.p_sc] using this.1
  have hset : ZZTyp σ v g r TF TF' = (D.shear Prod.swap) ⁻¹' ((fun w => w + κ) ⁻¹'
      Set.univ.pi fun k => {c | y k * c ∈ OEv (E := E) v}) := by
    ext z
    simp only [ZZTyp, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Pi.add_apply]
    have hR : ∀ i j, y (i, j) * ((D.shear Prod.swap) z (i, j) + κ (i, j)) ∈ OEv (E := E) v ↔
        ((g : Fv F v)⁻¹) ^ 2 * t (i, j) * (D.p 0 (z (i, j)) + D.p 1 (z (j, i)) +
            -(D.p 0 (TF i j) + D.p 0 (TF' i j)) / t (i, j)) ∈ v.adicCompletionIntegers F ∧
          (g : Fv F v)⁻¹ * t (i, j) * (D.p 1 (z (i, j)) + -(D.p 0 (TF j i)) / t (i, j)) ∈
            v.adicCompletionIntegers F := by
      intro i j
      rw [D.mem_iff, hy, hκ, map_mul, map_mul, map_add, map_add, D.shear_first_coordinate, D.shear_second_coordinate, hp0, hp1, hp0, hp1]
      rfl
    have hL : ∀ i j, ((locZ v z i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v ∧
        ((locZ v z i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ +
          sigR (Fv F v) σ ((locZ v z j i - TF j i) * sc (E := E) v (g : Fv F v)⁻¹) -
          (TF' i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v) ↔
        (((alp v r i * alp v r j) * D.p 0 (z (i, j)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ ∈
            v.adicCompletionIntegers F ∧
          ((alp v r i * alp v r j) * D.p 1 (z (i, j)) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹ ∈
            v.adicCompletionIntegers F) ∧
        ((((alp v r i * alp v r j) * D.p 0 (z (i, j)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ +
            ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ -
            (D.p 0 (TF' i j) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹) * (g : Fv F v)⁻¹ ∈
            v.adicCompletionIntegers F ∧
          (((alp v r i * alp v r j) * D.p 1 (z (i, j)) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹ +
            ((alp v r j * alp v r i) * D.p 0 (z (j, i)) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹ -
            (D.p 0 (TF' j i) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹) * (g : Fv F v)⁻¹ ∈
            v.adicCompletionIntegers F) := by
      intro i j
      rw [D.mem_iff, D.mem_iff]
      simp only [locZ, map_mul, map_sub, map_add, D.p_sc, (D.p_sig _).1, (D.p_sig _).2, hf, hf']
    constructor
    · intro hz k
      obtain ⟨i, j⟩ := k
      have ai := alp_ne_zero v r i
      have aj := alp_ne_zero v r j
      rw [hR]
      have h1 := (hL i j).1 (hz i j)
      refine ⟨?_, ?_⟩
      · convert h1.2.1 using 1
        rw [ht]
        field_simp
        ring
      · convert h1.1.2 using 1
        rw [ht]
        field_simp
        ring
    · intro hz i j
      have ai := alp_ne_zero v r i
      have aj := alp_ne_zero v r j
      rw [hL]
      have r1 := (hR i j).1 (hz (i, j))
      have r2 := (hR j i).1 (hz (j, i))
      have e1 : ((alp v r i * alp v r j) * D.p 1 (z (i, j)) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹ =
          (g : Fv F v)⁻¹ * t (i, j) * (D.p 1 (z (i, j)) + -(D.p 0 (TF j i)) / t (i, j)) := by
        have := ht0 (i, j)
        rw [ht] at this ⊢
        field_simp
        ring
      have e2 : (((alp v r i * alp v r j) * D.p 0 (z (i, j)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ +
            ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ -
            (D.p 0 (TF' i j) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹) * (g : Fv F v)⁻¹ =
          ((g : Fv F v)⁻¹) ^ 2 * t (i, j) * (D.p 0 (z (i, j)) + D.p 1 (z (j, i)) +
            -(D.p 0 (TF i j) + D.p 0 (TF' i j)) / t (i, j)) := by
        have := ht0 (i, j)
        rw [ht] at this ⊢
        field_simp
        ring
      have e3 : (((alp v r i * alp v r j) * D.p 1 (z (i, j)) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹ +
            ((alp v r j * alp v r i) * D.p 0 (z (j, i)) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹ -
            (D.p 0 (TF' j i) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹) * (g : Fv F v)⁻¹ =
          ((g : Fv F v)⁻¹) ^ 2 * t (j, i) * (D.p 0 (z (j, i)) + D.p 1 (z (i, j)) +
            -(D.p 0 (TF j i) + D.p 0 (TF' j i)) / t (j, i)) := by
        have := ht0 (j, i)
        rw [ht] at this ⊢
        field_simp
        ring
      have e4 : ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ =
          (g : Fv F v)⁻¹ * t (j, i) * (D.p 1 (z (j, i)) + -(D.p 0 (TF i j)) / t (j, i)) := by
        have := ht0 (j, i)
        rw [ht] at this ⊢
        field_simp
        ring
      have e5 : ((alp v r i * alp v r j) * D.p 0 (z (i, j)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ =
          (g : Fv F v) * ((((alp v r i * alp v r j) * D.p 0 (z (i, j)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ +
            ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ -
            (D.p 0 (TF' i j) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹) * (g : Fv F v)⁻¹) -
          ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ +
          (D.p 0 (TF' i j) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ := by
        field_simp
        ring
      have c2 : (((alp v r i * alp v r j) * D.p 0 (z (i, j)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ +
            ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ -
            (D.p 0 (TF' i j) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹) * (g : Fv F v)⁻¹ ∈
            v.adicCompletionIntegers F := by rw [e2]; exact r1.1
      have c4 : ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ ∈
          v.adicCompletionIntegers F := by rw [e4]; exact r2.2
      refine ⟨⟨?_, by rw [e1]; exact r1.2⟩, c2, by rw [e3]; exact r2.1⟩
      rw [e5]
      exact add_mem (sub_mem (mul_mem hgO c2) c4) (hd i j)
  have hsh := haar_shear μ (D.shear Prod.swap) (Obox (E := E) v _) (obox_compact _) (obox_open _)
    (obox_nonempty _) (D.shear_box Prod.swap)
  have hu : ∀ k, IsUnit (y k) := fun k => by
    rw [hy]
    exact D.isUnit_pt (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hg0)) (ht0 k)) (mul_ne_zero (inv_ne_zero hg0) (ht0 k))
  rw [hset, hsh, measure_preimage_add_right, BM.box_measure_mul (E := E) v _ μ y hu, hm]
  have hk : ∀ k : Fin (r + 1) × Fin (r + 1), (absV v (Algebra.norm (Fv F v) (y k)))⁻¹ =
      absV v (g : Fv F v) ^ 3 * ((absV v (alp v r k.1) * absV v (alp v r k.2)) ^ 2)⁻¹ := by
    intro k
    rw [hy, D.norm_pt, ht]
    simp only [absV_mul, absV_pow, absV_inv]
    have h1 := absV_pos v (alp_ne_zero v r k.1)
    have h2 := absV_pos v (alp_ne_zero v r k.2)
    have hG := absV_pos v hg0
    field_simp
  rw [Finset.prod_congr rfl (fun k _ => hk k), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, ← Fintype.prod_prod_type' (f := fun i j =>
      ((absV v (alp v r i) * absV v (alp v r j)) ^ 2)⁻¹), pow_mul]
  ring

end PI.UnitaryGroupMassFormula.LocJacTyp
