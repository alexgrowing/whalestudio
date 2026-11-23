import Mathlib
import Formalism.LocalToGlobal.KernelLattices.MuProd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.UG Formalism.UG.P

section XV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def xvY (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 E) : RInt F E := toRInt F E b * quE E v + (1 - quE E v)

theorem xv_coe (v : HeightOneSpectrum (𝓞 F)) (w : Eˣ) (b : 𝓞 E) (hw : (w : E) = (b : E)) :
    ((xvY v b : RInt F E) : AfE F E) = ((locId E v w : (AfE F E)ˣ) : AfE F E) := by
  show ((algebraMap (𝓞 E) E b) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1) + (1 - (1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1) =
    (w : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hw, TensorProduct.tmul_sub]
  rfl

theorem xv_supp (v : HeightOneSpectrum (𝓞 F)) (w : Eˣ) : locId E v w ∈ suppAt E v := by
  unfold suppAt
  rw [Subgroup.mem_iInf]
  intro v'
  rw [Subgroup.mem_iInf]
  intro hne
  rw [MonoidHom.mem_ker]
  apply Units.ext
  show (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F v')) ((w : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)) = 1
  rw [map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_sub, Formalism.L2.G.sgl_apply_ne F v 1 hne,
    TensorProduct.tmul_zero, zero_add, sub_zero, map_one (evalV F v')]
  rfl

theorem xv_cong (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (hv : P.asIdeal.under (𝓞 F) = v.asIdeal) (b t : 𝓞 E) (k : ℕ)
    (h : b - t ∈ P.asIdeal ^ k) : xvY v b - toRInt F E t ∈ (P.asIdeal ^ k).map (toRInt F E) := by
  have e : xvY v b - toRInt F E t = toRInt F E (b - t) * quE E v + toRInt F E (1 - t) * (1 - quE E v) := by
    unfold xvY
    rw [map_sub, map_sub, map_one]; ring
  rw [e]
  refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h)) (Ideal.mul_mem_left _ _ (qu_one_sub_mem v _ k ?_))
  intro a ha
  have h1 : algebraMap (𝓞 F) (𝓞 E) a ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E)) := Ideal.mem_map_of_mem _ ha
  rw [Ideal.map_pow] at h1
  refine Ideal.pow_right_mono ?_ k h1
  rw [Ideal.map_le_iff_le_comap, ← hv]

theorem xv_other (v : HeightOneSpectrum (𝓞 F)) (P' : HeightOneSpectrum (𝓞 E)) (b : 𝓞 E)
    (h : P'.asIdeal.under (𝓞 F) = v.asIdeal → b - 1 ∈ P'.asIdeal) : xvY v b - 1 ∈ P'.asIdeal.map (toRInt F E) := by
  have e : xvY v b - 1 = toRInt F E (b - 1) * quE E v := by
    unfold xvY
    rw [map_sub, map_one]; ring
  rw [e]
  by_cases hP' : P'.asIdeal.under (𝓞 F) = v.asIdeal
  · exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h hP'))
  · refine Ideal.mul_mem_left _ _ ?_
    have hex : ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a ∈ P'.asIdeal ∧ a ∉ v.asIdeal := by
      by_contra hcon
      push Not at hcon
      apply hP'
      have hle : P'.asIdeal.under (𝓞 F) ≤ v.asIdeal := fun a ha => hcon a ha
      have hbot : P'.asIdeal.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) P'.ne_bot
      have hpr : (P'.asIdeal.under (𝓞 F)).IsPrime := inferInstance
      exact (hpr.isMaximal hbot).eq_of_le v.isPrime.ne_top hle
    obtain ⟨a, ha1, ha2⟩ := hex
    exact qu_eps_mem v _ a ha1 ha2

theorem xv_top (P : HeightOneSpectrum (𝓞 E)) (K : Ideal (RInt F E)) (hK : ∀ P' : HeightOneSpectrum (𝓞 E), P'.asIdeal.map (toRInt F E) ⊔ K = ⊤)
    (D : 𝓞 F) (hD0 : D ≠ 0) (hD : toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) ∈ K) : K = ⊤ := by
  have hI : Ideal.span {algebraMap (𝓞 F) (𝓞 E) D} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    intro h
    apply adelstab_algebraMap_ne_zero (E := E) D hD0
    rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, h, map_zero]
  obtain ⟨n, hn⟩ := qe_strip P K (fun P' _ => hK P') _ hI 0 (by
    rw [pow_zero, one_mul, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; exact hD)
  have h1 : (P.asIdeal.map (toRInt F E)) ^ n ⊔ K = ⊤ := Ideal.pow_sup_eq_top (hK P)
  rw [← Ideal.map_pow, sup_eq_right.2 hn] at h1
  exact h1

variable {L : Type} [Field L]

theorem xv_same (ξ : Chr F E L) (v : HeightOneSpectrum (𝓞 F)) (hξ : inertAt E v ≤ ξ.ker) (P : HeightOneSpectrum (𝓞 E)) (q q' : 𝓞 E)
    (hq : q ∈ P.asIdeal) (hq2 : q ∉ P.asIdeal ^ 2) (hq' : q' ∈ P.asIdeal) (hq2' : q' ∉ P.asIdeal ^ 2) (y y' : (AfE F E)ˣ) (y₀ y₀' : RInt F E)
    (hy : (y₀ : AfE F E) = (y : AfE F E)) (hy' : (y₀' : AfE F E) = (y' : AfE F E)) (hs : y ∈ suppAt E v) (hs' : y' ∈ suppAt E v)
    (h1 : y₀ - toRInt F E q ∈ (P.asIdeal ^ 2).map (toRInt F E)) (h1' : y₀' - toRInt F E q' ∈ (P.asIdeal ^ 2).map (toRInt F E))
    (h2 : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E))
    (h2' : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀' - 1 ∈ P'.asIdeal.map (toRInt F E)) : ξ y = ξ y' := by
  have hle := qe_le P y y₀ hy q hq hq2 h1 h2
  have hle' := qe_le P y' y₀' hy' q' hq' hq2' h1' h2'
  have hmem : ∀ (z₀ : RInt F E) (c : 𝓞 E), c ∈ P.asIdeal → z₀ - toRInt F E c ∈ (P.asIdeal ^ 2).map (toRInt F E) → z₀ ∈ P.asIdeal.map (toRInt F E) := by
    intro z₀ c hc hz
    have e : z₀ = (z₀ - toRInt F E c) + toRInt F E c := by ring
    rw [e]
    exact add_mem (Ideal.map_mono (Ideal.pow_le_self two_ne_zero) hz) (Ideal.mem_map_of_mem _ hc)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hle' (hmem y₀ q hq h1))
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (hle (hmem y₀' q' hq' h1'))
  have haa : a * a' = 1 := by
    have e0 : a * a' * y₀ = y₀ := by rw [mul_assoc, ha', ha]
    have e1 : ((a * a' : RInt F E) : AfE F E) * (y : AfE F E) = 1 * (y : AfE F E) := by
      rw [one_mul, ← hy]
      exact congrArg Subtype.val e0
    exact Subtype.ext (y.isUnit.mul_right_cancel e1)
  let u : (RInt F E)ˣ := ⟨a, a', haa, by rw [mul_comm]; exact haa⟩
  have hu : Units.map (RInt F E).subtype.toMonoidHom u = y * y'⁻¹ := by
    apply Units.ext
    show (a : AfE F E) = (y : AfE F E) * ((y'⁻¹ : (AfE F E)ˣ) : AfE F E)
    have e2 : (a : AfE F E) * (y' : AfE F E) = (y : AfE F E) := by
      rw [← hy, ← hy']
      exact congrArg Subtype.val ha
    rw [← e2, mul_assoc, Units.mul_inv, mul_one]
  have hw : Units.map (RInt F E).subtype.toMonoidHom u ∈ inertAt E v := by
    refine Subgroup.mem_inf.2 ⟨?_, by rw [hu]; exact mul_mem hs (inv_mem hs')⟩
    show _ ∈ (RInt F E).toSubmonoid.units
    rw [Submonoid.mem_units_iff]
    exact ⟨a.2, a'.2⟩
  have h3 := hξ hw
  rw [hu, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3

end XV

theorem xv_tame {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L] {S : Set ℕ}
    (ξ : Tup F E L S) (v : HeightOneSpectrum (𝓞 F)) : wildAt E v ≤ (ξ : Chr F E L).ker :=
  mem_kills.1 ((Subgroup.mem_iInf.1 ξ.2.1.2) v)

theorem twist_value_at_q : XiQ := by
  intro F E _ _ _ _ _ L _ S ξ v P hv hq w b hw hb1 hb2
  exact qVal_spec_tup ξ P hq v hv (locId E v w) (xvY v b) (xv_coe v w b hw) (xv_supp v w) (xv_cong v P hv b _ 2 hb1)
    (fun P' hne => xv_other v P' b (hb2 P' hne))

theorem twist_residue_character : XiRes := by
  intro F E _ _ _ _ _ L _ S ξ v P hv w b r hw hb hb2
  have hbP : b ∉ P.asIdeal := by
    intro h
    rw [← Ideal.Quotient.eq_zero_iff_mem, hb] at h
    exact r.ne_zero h
  have hc1 : xvY (F := F) v b - toRInt F E b ∈ P.asIdeal.map (toRInt F E) := by
    have := xv_cong v P hv b b 1 (by rw [sub_self]; exact zero_mem _)
    rwa [pow_one] at this
  have hoth : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → xvY (F := F) v b - 1 ∈ P'.asIdeal.map (toRInt F E) :=
    fun P' hne => xv_other v P' b (hb2 P' hne)
  have hy0 : xvY (F := F) v b ∈ Ideal.span {xvY (F := F) v b} := Ideal.mem_span_singleton_self _
  have hK : ∀ P' : HeightOneSpectrum (𝓞 E), P'.asIdeal.map (toRInt F E) ⊔ Ideal.span {xvY (F := F) v b} = ⊤ := by
    intro P'
    rw [Ideal.eq_top_iff_one]
    by_cases hP' : P' = P
    · rw [hP']
      obtain ⟨b', i, hi, hbi⟩ := P.isMaximal.exists_inv hbP
      have e3 := congrArg (toRInt F E) hbi
      simp only [map_add, map_mul, map_one] at e3
      have e : (1 : RInt F E) = (toRInt F E i - (xvY (F := F) v b - toRInt F E b) * toRInt F E b') + xvY (F := F) v b * toRInt F E b' := by
        linear_combination -e3
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (sub_mem (Ideal.mem_map_of_mem _ hi) (Ideal.mul_mem_right _ _ hc1)))
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ hy0))
    · have e : (1 : RInt F E) = -(xvY (F := F) v b - 1) + xvY (F := F) v b := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (neg_mem (hoth P' hP'))) (Ideal.mem_sup_right hy0)
  obtain ⟨D, hD0, hD⟩ := qe_denom (locId E v w) (xvY v b) (xv_coe v w b hw)
  have htop := xv_top P _ hK D hD0 hD
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 ((Ideal.eq_top_iff_one _).1 htop)
  let u : (RInt F E)ˣ := ⟨xvY v b, a, by rw [mul_comm]; exact ha, ha⟩
  have hu : Units.map (RInt F E).subtype.toMonoidHom u = locId E v w := Units.ext (xv_coe v w b hw)
  have h := b_resChar_spec (ξ : Chr F E L) (xv_tame ξ) P v hv u r b hb (by rw [hu]; exact xv_supp v w) hc1 hoth
  rw [hu] at h
  exact h

theorem twist_value_at_uniformizer : XiUnif := by
  intro F E _ _ _ _ _ L _ S ξ v P hv hQ w b hw hb1 hb2 hb3
  have hin : inertAt E v ≤ (ξ : Chr F E L).ker := by
    by_contra h
    exact hQ h
  have hY1 : xvY (F := F) v b - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E) := xv_cong v P hv b b 2 (by rw [sub_self]; exact zero_mem _)
  have hY2 : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → xvY (F := F) v b - 1 ∈ P'.asIdeal.map (toRInt F E) :=
    fun P' hne => xv_other v P' b (hb3 P' hne)
  have hex : ∃ k, IsUnifVal (ξ : Chr F E L) P k := by
    refine ⟨(ξ : Chr F E L) (locId E v w), fun v' hv' y y₀ b' hy hb1' hb2' hs h1 h2 => ?_⟩
    have hvv : v' = v := HeightOneSpectrum.ext (hv'.symm.trans hv)
    subst hvv
    exact xv_same (ξ : Chr F E L) v' hin P b' b hb1' hb2' hb1 hb2 y (locId E v' w) y₀ (xvY v' b) hy (xv_coe v' w b hw) hs (xv_supp v' w) h1 hY1 h2 hY2
  have hsp : IsUnifVal (ξ : Chr F E L) P (unifVal (ξ : Chr F E L) P) := by
    unfold unifVal
    rw [dif_pos hex]
    exact hex.choose_spec
  exact hsp v hv (locId E v w) (xvY v b) b (xv_coe v w b hw) hb1 hb2 (xv_supp v w) hY1 hY2

end Formalism.L2.Ker
