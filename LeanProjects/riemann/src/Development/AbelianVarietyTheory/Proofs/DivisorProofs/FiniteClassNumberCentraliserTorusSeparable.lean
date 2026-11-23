import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultLabelRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCentralizerOfCommutePadicPointsSpliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiPNeighborhoodInLevelSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TCAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeCentraliserClassNumberFiniteBorelStatement

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls

theorem exists_finset_cosets {A : Type} [Group A] (U₀ U : Subgroup A) (h : U.relIndex U₀ ≠ 0) :
    ∃ F : Finset A, ∀ u ∈ U₀, ∃ f ∈ F, f ∈ U₀ ∧ ∃ v ∈ U, u = f * v := by
  haveI : (U.subgroupOf U₀).FiniteIndex := ⟨h⟩
  haveI : Finite (U₀ ⧸ U.subgroupOf U₀) := Subgroup.finite_quotient_of_finiteIndex
  haveI := Fintype.ofFinite (U₀ ⧸ U.subgroupOf U₀)
  refine ⟨Finset.univ.image (fun q : U₀ ⧸ U.subgroupOf U₀ => ((q.out : U₀) : A)), ?_⟩
  intro u hu
  set q : U₀ ⧸ U.subgroupOf U₀ := QuotientGroup.mk ⟨u, hu⟩
  refine ⟨((q.out : U₀) : A), Finset.mem_image_of_mem _ (Finset.mem_univ _), (q.out).2,
    ((q.out : U₀) : A)⁻¹ * u, ?_, by group⟩
  have h1 : (q.out)⁻¹ * ⟨u, hu⟩ ∈ U.subgroupOf U₀ := QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

end GlobalTheory.CentCls

namespace GlobalTheory.CentCls

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (K' : Subgroup (Gr G 1)), Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → ∀ (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∀ r : G.GAf × Gr G 1, ∃ R : Finset (G.GAf × Gr G 1), ∀ c : G.GAf × Gr G 1, c * (toAfF G β x t hx y₀, toP1 G β y₀) = (toAfF G β x t hx y₀, toP1 G β y₀) * c → ∃ y : grp G β, y * y₀ = y₀ * y ∧ ∃ s ∈ R, ∃ k : G.GAf × Gr G 1, k.1 ∈ L.K.toSubgroup ∧ k.2 ∈ K' ∧ c * r = (toAfF G β x t hx y, toP1 G β y) * s * k := by
  intro p hp G L K' hK' β x t hx hsh y₀ _ _ r
  obtain ⟨r₁, r₂⟩ := r
  obtain ⟨F₂, hF₂⟩ := exists_finset_cosets (KHT p G.m G.n 1 G.Fw) K' hK'.1
  let ι : G.GAf →* (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ :=
    { toFun := fun g => g, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let U₁ : Subgroup ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :=
    ((L.K.toSubgroup.map (MulAut.conj r₁).toMonoidHom).map ι).comap (psiAway G x)
  let U₂ : Subgroup ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ) :=
    ((KHT p G.m G.n 1 G.Fw).map (MulAut.conj r₂).toMonoidHom).comap (psiP G)
  obtain ⟨O₁, hO₁, h1O₁, hO₁K⟩ :=
    exists_open_psiAway_mem_conj_level p G L β x t hx (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) r₁
  obtain ⟨O₂, hO₂, h1O₂, hO₂K⟩ := GlobalTheory.T.psi_p_neighborhood_in_level_subgroup p G r₂
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  obtain ⟨S, hS⟩ := GlobalTheory.T.similitudeCentraliser_classNumber_finite_borel G.C G.star (β : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) p
    (U₁.prod U₂) ⟨O₁ ×ˢ O₂, hO₁.prod hO₂, ⟨h1O₁, h1O₂⟩,
      fun z hz hT1 _ => Subgroup.mem_prod.mpr ⟨by
        obtain ⟨k, hk, hk'⟩ := hO₁K z.1 hz.1 hT1
        exact Subgroup.mem_comap.mpr
          (Subgroup.mem_map.mpr ⟨r₁ * k * r₁⁻¹, Subgroup.mem_map.mpr ⟨k, hk, rfl⟩, hk'⟩), by
        have h2 := hO₂K z.2 hz.2
        refine Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨r₂⁻¹ * psiP G z.2 * r₂, h2, ?_⟩)
        show r₂ * (r₂⁻¹ * psiP G z.2 * r₂) * r₂⁻¹ = psiP G z.2
        group⟩⟩
  let Pf : G.Cˣ × ℚˣ → Prop := fun e =>
    (e.1 : G.C) * β * MulOpposite.unop (G.star e.1) = algebraMap ℚ G.C e.2 * β ∧
      Commute (e.1 : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
  let e₀ : G.Cˣ × ℚˣ := if h : ∃ e, Pf e ∧ (e.2 : ℚ) < 0 then h.choose else 1
  let S' := S ∪ S.image (fun s => dg G.C p e₀ * s)
  let gOf : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ → G.GAf := fun w =>
    if h : ∃ g : G.GAf, (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w then h.choose else 1
  have hgOf : ∀ w (g : G.GAf), (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w →
      ((gOf w : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w := by
    intro w g hg
    have h : ∃ g : G.GAf, (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w := ⟨g, hg⟩
    simp only [gOf, dif_pos h]
    exact h.choose_spec
  refine ⟨(S' ×ˢ F₂).image (fun q => (gOf (psiAway G x q.1.1) * r₁, psiP G q.1.2 * r₂ * q.2)), ?_⟩
  intro c hc
  obtain ⟨c₁, c₂⟩ := c
  have hc1 : c₁ * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c₁ := congrArg Prod.fst hc
  have hc2 : c₂ * toP1 G β y₀ = toP1 G β y₀ * c₂ := congrArg Prod.snd hc
  have hz₁ := inT_psiAway_inv_of_commute p G β x t hx y₀ c₁ hc1
  obtain ⟨z₂, hz₂, hz₂c⟩ := GlobalTheory.T.exists_unitaryCentralizer_of_commute_padicPoints_split p G β hsh y₀ c₂ hc2
  obtain ⟨γ, hγf, hγc, s, hs, u, hu, hz⟩ := hS (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), z₂) hz₁ hz₂
  obtain ⟨γ', ⟨hγ'f, hγ'c⟩, hγ'pos, s', hs', hds⟩ : ∃ γ' : G.Cˣ × ℚˣ, Pf γ' ∧ (0 : ℚ) < (γ'.2 : ℚ) ∧
      ∃ s' ∈ S', dg G.C p γ * s = dg G.C p γ' * s' := by
    rcases lt_or_gt_of_ne (Units.ne_zero γ.2) with hneg | hpos
    · have hex : ∃ e, Pf e ∧ (e.2 : ℚ) < 0 := ⟨γ, ⟨hγf, hγc⟩, hneg⟩
      have he₀ : e₀ = hex.choose := by simp only [e₀, dif_pos hex]
      obtain ⟨⟨he1, he2⟩, he3⟩ := hex.choose_spec
      refine ⟨γ * e₀⁻¹, ⟨?_, ?_⟩, ?_, dg G.C p e₀ * s,
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs), ?_⟩
      · rw [he₀]
        exact form_mul_inv G.star (β : G.C) γ.1 hex.choose.1 γ.2 hex.choose.2 hγf he1
      · rw [he₀]
        show Commute ((γ.1 * hex.choose.1⁻¹ : G.Cˣ) : G.C) _
        rw [Units.val_mul]
        exact hγc.mul_left he2.units_inv_left
      · rw [he₀]
        show (0 : ℚ) < ((γ.2 * hex.choose.2⁻¹ : ℚˣ) : ℚ)
        rw [Units.val_mul, Units.val_inv_eq_inv_val]
        exact mul_pos_of_neg_of_neg hneg (inv_lt_zero.mpr he3)
      · rw [map_mul, map_inv]
        group
    · exact ⟨γ, ⟨hγf, hγc⟩, hpos, s, Finset.mem_union_left _ hs, rfl⟩
  let y : grp G β := ⟨γ', hγ'f, hγ'pos⟩
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_prod.mp hu
  obtain ⟨g, hg1, hg⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hu1)
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg1
  obtain ⟨k₂, hk₂, hk₂e⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hu2)
  obtain ⟨f, hf, -, v, hv, hkv⟩ := hF₂ k₂ hk₂
  have hz' : (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), z₂) = dg G.C p γ' * s' * u := by
    rw [hz, hds]
  have hz1 := congrArg Prod.fst hz'
  have hz2 := congrArg Prod.snd hz'
  simp only [Prod.fst_mul, Prod.snd_mul] at hz1 hz2
  have hc₁ : (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      psiAway G x (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    simp [psiAway_apply, mul_assoc]
  have e1 : psiAway G x (dg G.C p γ').1 = ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :=
    (toAfF_eq_psiAway G β x t hx y).symm
  rw [hz1, map_mul, map_mul, e1, ← hg] at hc₁
  have hs1 : ((gOf (psiAway G x s'.1) : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = psiAway G x s'.1 := by
    refine hgOf _ ((toAfF G β x t hx y)⁻¹ * c₁ * g⁻¹) ?_
    show ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)⁻¹ *
      (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) * (ι g)⁻¹ = _
    rw [hc₁]
    group
  have hc₁' : c₁ = toAfF G β x t hx y * gOf (psiAway G x s'.1) * g := by
    apply Subtype.ext
    show (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) *
      ((gOf (psiAway G x s'.1) : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) * ι g
    rw [hs1]
    exact hc₁
  have e2 : psiP G (dg G.C p γ').2 = toP1 G β y := (formGroupToPadicPointsDegreeOne_eq_unitaryPoints G β y).symm
  have hc₂' : c₂ = toP1 G β y * psiP G s'.2 * (r₂ * k₂ * r₂⁻¹) := by
    rw [← hz₂c, hz2, map_mul, map_mul, e2, ← hk₂e]
    rfl
  have hg' : g = r₁ * k * r₁⁻¹ := hkg.symm
  have hmem : (s', f) ∈ S' ×ˢ F₂ := Finset.mem_product.mpr ⟨hs', hf⟩
  refine ⟨y, Subtype.ext (Prod.ext (Units.ext hγ'c.eq) (mul_comm _ _)), _,
    Finset.mem_image_of_mem _ hmem, (k, v), hk, hv, ?_⟩
  rw [hc₁', hg', hc₂', hkv]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> simp only [Prod.fst_mul, Prod.snd_mul] <;> group

end GlobalTheory.CentCls
