import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem val_le_iff (x p : kˣ) :
    ValuativeRel.valuation k (x : k) ≤ ValuativeRel.valuation k (p : k) ↔ ord (p : k) ≤ ord (x : k) := by
  have h := mem_valBall_iff_le_ord (n := 0) (x * p⁻¹ : kˣ).ne_zero
  rw [mem_valBall_zero_iff, Valuation.mem_integer_iff, ord_units_mul, ord_units_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, map_mul, map_inv₀,
    mul_inv_le_iff₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 p.ne_zero)), one_mul] at h
  rw [h]
  omega

private theorem val_lt_iff (x : kˣ) : ValuativeRel.valuation k (x : k) < 1 ↔ 1 ≤ ord (x : k) := by
  have h := mem_valBall_iff_le_ord (n := 1) x.ne_zero
  rwa [mem_valBall_one_iff] at h

private theorem ord_unif : ord ((UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k : kˣ) : k) = 1 := by
  have hex : ∃ p : kˣ, ValuativeRel.valuation k (p : k) < 1 ∧
      ∀ x : k, ValuativeRel.valuation k x < 1 → ValuativeRel.valuation k x ≤ ValuativeRel.valuation k (p : k) := by
    refine ⟨unifUnit k, (val_lt_iff _).2 ord_unifUnit.ge, fun x hx => ?_⟩
    by_cases h0 : x = 0
    · simp [h0]
    · have h1 := (val_lt_iff (Units.mk0 x h0)).1 hx
      exact (val_le_iff (Units.mk0 x h0) _).2 (by rw [ord_unifUnit]; exact h1)
  obtain ⟨h1, h2⟩ := Classical.epsilon_spec hex
  have a := (val_lt_iff _).1 h1
  have b := (val_le_iff _ _).1 (h2 _ ((val_lt_iff (unifUnit k)).2 ord_unifUnit.ge))
  rw [ord_unifUnit] at b
  exact le_antisymm b a

private theorem unr_mul {a b : kˣ →* ℂˣ} (ha : IsUnramifiedChar a) (hb : IsUnramifiedChar b) :
    IsUnramifiedChar (a * b) :=
  isUnramifiedChar_iff.2 fun u hu => by
    rw [MonoidHom.mul_apply, isUnramifiedChar_iff.1 ha u hu, isUnramifiedChar_iff.1 hb u hu, one_mul]

private theorem unr_inv {a : kˣ →* ℂˣ} (ha : IsUnramifiedChar a) : IsUnramifiedChar a⁻¹ :=
  isUnramifiedChar_iff.2 fun u hu => by
    rw [MonoidHom.inv_apply, isUnramifiedChar_iff.1 ha u hu, inv_one]

private theorem local_l_factor_rank_three_unramified {ν c : kˣ →* ℂˣ} (hν : IsUnramifiedChar ν) (hc : IsUnramifiedChar c) (s : ℂ) :
    Ad3.lf3 ν c s = ((tri (ν (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k)) (c (unifUnit k))).map
      fun b => (1 - b * (residueCard k : ℂ) ^ (-s))⁻¹).prod := by
  rw [Ad3.lf3, localLFactor_of_isUnramified (unr_mul hν hc), localLFactor_of_isUnramified hc,
    localLFactor_of_isUnramified (unr_mul (unr_inv hν) hc), quasiChar_apply_eq_of_isUnramified hν ord_unif]
  simp only [tri, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_assoc]

end Loc

private theorem tri_inv (a x : ℂˣ) : (tri a x).map (·⁻¹) = tri a x⁻¹ := by
  simp only [tri, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Units.val_mul,
    Units.val_inv_eq_inv_val, mul_inv, inv_inv]
  rw [← Multiset.cons_zero, ← Multiset.cons_zero ((↑a)⁻¹ * (↑x)⁻¹ : ℂ), Multiset.cons_swap (((↑a)⁻¹ * (↑x)⁻¹ : ℂ)),
    Multiset.cons_swap (((↑a)⁻¹ * (↑x)⁻¹ : ℂ)), Multiset.cons_swap ((↑x)⁻¹ : ℂ)]

private theorem localChar_inv' (c : HeckeCharacter ℚ) (v : Ad3.Pl) : localChar c⁻¹ v = (localChar c v)⁻¹ := by
  ext x
  simp [GroundTheory.Automorphic.GodementSection.coe_localChar, HeckeCharacter.localComponent_apply,
    HeckeCharacter.toIdele_apply]
  exact Circle.coe_inv _

theorem UpperTheory.euler_product_adjoint_eq_standard :
    ∀ (D : Ad3.Dat) (c : HeckeCharacter ℚ) (δ : Bool) (S : Finset Ad3.Pl), Ad3.admitted D c δ S → ∀ s : ℂ,
        Ad3.eul D c S s = eulerL ℚ (par D (toH c)) S s ∧ Ad3.eul D c⁻¹ S (1 - s) = eulerLd ℚ (par D (toH c)) S s := by
  intro D c δ S h s
  constructor
  · refine tprod_congr fun v => ?_
    have hν := D.unr v.1 fun hb => v.2 (h.bad hb)
    have hc := h.unr v.1 v.2
    refine (local_l_factor_rank_three_unramified hν hc s).trans ?_
    rw [GroundTheory.Global.residueCard_adicCompletion, ← Ad3P.DihedralUnramifiedPlaces.val_eq hc]
    rfl
  · refine tprod_congr fun v => ?_
    have hν := D.unr v.1 fun hb => v.2 (h.bad hb)
    have hc := h.unr v.1 v.2
    rw [localChar_inv']
    refine (local_l_factor_rank_three_unramified hν (unr_inv hc) (1 - s)).trans ?_
    rw [GroundTheory.Global.residueCard_adicCompletion, MonoidHom.inv_apply, ← Ad3P.DihedralUnramifiedPlaces.val_eq hc, ← tri_inv]
    rfl
