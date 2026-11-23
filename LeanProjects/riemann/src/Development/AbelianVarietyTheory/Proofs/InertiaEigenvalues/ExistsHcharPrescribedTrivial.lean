import Mathlib
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChars

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocLanglands

namespace GlobalTheory.DelEps.Twist

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def filtSub (a : ℕ) : Subgroup kˣ where
  carrier := unitFilt k a
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := fun {x y} hx hy => ⟨by rw [Units.val_mul, map_mul, hx.1, hy.1, one_mul], by
    have e : ((x * y : kˣ) : k) - 1 = (x : k) * ((y : k) - 1) + ((x : k) - 1) := by rw [Units.val_mul]; ring
    rw [e]
    refine Valuation.map_add_le _ ?_ hx.2
    rw [map_mul, hx.1, one_mul]
    exact hy.2⟩
  inv_mem' := fun {x} hx => by
    have h1 : valuation k ((x⁻¹ : kˣ) : k) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hx.1, inv_one]
    refine ⟨h1, ?_⟩
    have e : ((x⁻¹ : kˣ) : k) - 1 = -(((x⁻¹ : kˣ) : k) * ((x : k) - 1)) := by
      linear_combination x.inv_mul
    rw [e, Valuation.map_neg, map_mul, h1, one_mul]
    exact hx.2

theorem isOpen_filtSub (a : ℕ) : IsOpen (filtSub k a : Set kˣ) :=
  (GroundTheory.LocalField.isOpen_setOf_valuation_eq_one.inter (GroundTheory.LocalField.isOpen_setOf_valuation_sub_le (a := (1 : k))
    (pow_ne_zero a uniformizer_ne_zero))).preimage Units.continuous_val

theorem ord_zpow (p : kˣ) (n : ℤ) : ord k (p ^ n) = n * ord k p := by
  let f : kˣ →* Multiplicative ℤ :=
    { toFun := fun x => Multiplicative.ofAdd (ord k x)
      map_one' := by rw [ord_eq_zero (by simp)]; rfl
      map_mul' := fun x y => by rw [ord_mul]; rfl }
  have := congrArg Multiplicative.toAdd (map_zpow f p n)
  simpa [f] using this

end Local

section Global

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {k : Type} [Field k] [NumberField k]

def comp (w : HeightOneSpectrum (𝓞 k)) : Ideles k →* (w.adicCompletion k)ˣ :=
  Units.map
    { toFun := fun a : AdeleRing (𝓞 k) k => a.2 w
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem continuous_comp (w : HeightOneSpectrum (𝓞 k)) : Continuous (comp w) :=
  Continuous.units_map _ ((RestrictedProduct.continuous_eval w).comp continuous_snd)

theorem comp_diag (w : HeightOneSpectrum (𝓞 k)) (x : kˣ) : comp w (diagUnits k x) = atFin w x := Units.ext rfl

theorem comp_local_self (w : HeightOneSpectrum (𝓞 k)) (x : (w.adicCompletion k)ˣ) : comp w (localIdele k w x) = x :=
  Units.ext (localIdele_snd_self k w x)

theorem comp_local_ne {w w' : HeightOneSpectrum (𝓞 k)} (h : w' ≠ w) (x : (w.adicCompletion k)ˣ) :
    comp w' (localIdele k w x) = 1 :=
  Units.ext ((localIdele_isSupportedAt k w x).2 w' h)

theorem comp_inf (w : HeightOneSpectrum (𝓞 k)) (u : InfinitePlace k) (x : (u.Completion)ˣ) : comp w (infIdele k u x) = 1 :=
  Units.ext rfl

theorem exists_hchar_prescribed (k : Type) [Field k] [NumberField k] (S : Finset (HeightOneSpectrum (𝓞 k)))
    (θ : ∀ w : HeightOneSpectrum (𝓞 k), (w.adicCompletion k)ˣ →* ℂˣ) (hs : ∀ w ∈ S, IsSmoothChar (θ w))
    (hf : ∀ w ∈ S, ∃ N : ℕ, 0 < N ∧ θ w ^ N = 1) :
    ∃ η : HChar k, (∃ n : ℕ, 0 < n ∧ η.OrderDvd n) ∧ (∀ u : InfinitePlace k, η.locInf u = 1) ∧ ∀ w ∈ S, η.loc w = θ w := by
  classical
  choose! N hN0 hN using hf
  have hm0 : 0 < ∏ w ∈ S, N w := Finset.prod_pos hN0
  have hm : ∀ w ∈ S, ∀ x, θ w x ^ (∏ w ∈ S, N w) = 1 := fun w hw x => by
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem N hw
    rw [hd, pow_mul, ← MonoidHom.pow_apply, hN w hw, MonoidHom.one_apply, one_pow]
  set m := ∏ w ∈ S, N w
  obtain ⟨T, hST, hT⟩ := GlobalTheory.ChevalleySUnits.exists_places k S m hm0
  let U : Subgroup (Ideles k) := GlobalTheory.LevelChars.levSub k T 1 ⊓ ⨅ w : S, (θ w).ker.comap (comp w.1)
  have hU : IsOpen (U : Set (Ideles k)) := by
    have h1 : IsOpen (GlobalTheory.LevelChars.levSub k T 1 : Set (Ideles k)) := by
      convert (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open k).2 T 1 using 1
      ext a
      exact ⟨fun h => ⟨fun v => (h v).1, fun v hv => (h v).2 hv⟩, fun h v => ⟨h.1 v, h.2 v⟩⟩
    rw [Subgroup.coe_inf, Subgroup.coe_iInf]
    exact h1.inter (isOpen_iInter_of_finite fun w => (hs w w.2).preimage (continuous_comp w.1))
  let β : (∀ w : S, (w.1.adicCompletion k)ˣ) →* Ideles k :=
    ∏ w : S, (localIdele k w.1).comp (Pi.evalMonoidHom (fun w : S => (w.1.adicCompletion k)ˣ) w)
  let γ : (∀ w : S, (w.1.adicCompletion k)ˣ) →* ℂˣ :=
    ∏ w : S, (θ w.1).comp (Pi.evalMonoidHom (fun w : S => (w.1.adicCompletion k)ˣ) w)
  have hβ : ∀ y, β y = ∏ w : S, localIdele k w.1 (y w) := fun y => MonoidHom.finsetProd_apply _ _ _
  have hγ : ∀ y, γ y = ∏ w : S, θ w.1 (y w) := fun y => MonoidHom.finsetProd_apply _ _ _
  have hβS : ∀ y (w : S), comp w.1 (β y) = y w := fun y w => by
    rw [hβ, map_prod, Finset.prod_eq_single w, comp_local_self]
    · exact fun w' _ h => comp_local_ne (fun e => h (Subtype.ext e.symm)) _
    · simp
  have hβn : ∀ y v, v ∉ S → comp v (β y) = 1 := fun y v hv => by
    rw [hβ, map_prod]
    exact Finset.prod_eq_one fun w _ => comp_local_ne (fun e : v = w.1 => hv (e ▸ w.2)) _
  obtain ⟨χ, hχ, -, hχU, hχα⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Ideles k)
    (kˣ × ∀ w : S, (w.1.adicCompletion k)ˣ) U hU ((diagUnits k).coprod β) ((1 : kˣ →* ℂˣ).coprod γ) 1 continuous_const
    (fun _ => by simp)
    (fun y => by
      have h1 : γ y.2 ^ m = 1 := by
        rw [hγ, ← Finset.prod_pow]
        exact Finset.prod_eq_one fun w _ => hm w w.2 _
      have h2 : ((γ y.2 : ℂˣ) : ℂ) ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
      simpa using Complex.norm_eq_one_of_pow_eq_one h2 hm0.ne')
    (by
      rintro ⟨x, y⟩ ⟨h1, h2⟩
      have hval : ∀ (v : HeightOneSpectrum (𝓞 k)) (z : k),
          Valued.v (algebraMap k (v.adicCompletion k) z) = v.valuation k z := fun v z =>
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
      have hc : ∀ v, v ∉ S → GlobalTheory.LevelChars.compAt k v ((diagUnits k).coprod β (x, y)) =
          algebraMap k (v.adicCompletion k) (x : k) := fun v hv => by
        have e : comp v ((diagUnits k).coprod β (x, y)) = atFin v x := by
          rw [MonoidHom.coprod_apply, map_mul, comp_diag, hβn _ v hv, mul_one]
        exact congrArg Units.val e
      obtain ⟨z, hz⟩ := hT x (fun v hv => by rw [← hval, ← hc v hv]; exact (h1 v).1) (fun t ht => by
        have h3 := (h1 t).2 ht
        rw [hc t (Finset.disjoint_right.1 hST ht), ← map_one (algebraMap k (t.adicCompletion k)), ← map_sub, hval] at h3
        refine h3.trans_lt ?_
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        simp)
      have hz0 : z ≠ 0 := by
        rintro rfl
        exact x.ne_zero (by rw [← hz, zero_pow hm0.ne'])
      have hxz : x = Units.mk0 z hz0 ^ m := Units.ext (by simp [hz])
      rw [MonoidHom.coprod_apply, MonoidHom.one_apply, MonoidHom.one_apply, one_mul, hγ]
      refine Finset.prod_eq_one fun w _ => ?_
      have h4 : θ w.1 (comp w.1 ((diagUnits k).coprod β (x, y))) = 1 := Subgroup.mem_iInf.1 h2 w
      rwa [MonoidHom.coprod_apply, map_mul, comp_diag, hβS, map_mul, hxz, map_pow, map_pow, hm w w.2, one_mul] at h4)
  let η : HChar k := ⟨χ, hχ, fun x => by simpa using hχα (x, 1)⟩
  have hinf : ∀ u : InfinitePlace k, η.locInf u = 1 := fun u => by
    ext x
    refine congrArg Units.val (hχU (infIdele k u x) ⟨fun v => ⟨map_one _, fun _ => ?_⟩, Subgroup.mem_iInf.2 fun w => ?_⟩)
    · change Valued.v ((1 : v.adicCompletion k) - 1) ≤ _
      simp
    · rw [Subgroup.mem_comap, comp_inf]
      exact one_mem _
  refine ⟨η, GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one k η fun x => ?_, hinf, fun w hw => ?_⟩
  · change χ (infDiag x) = 1
    rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
    exact Finset.prod_eq_one fun u _ => DFunLike.congr_fun (hinf u) (atInf u x)
  · refine MonoidHom.ext fun x => ?_
    have h := hχα (1, Pi.mulSingle (⟨w, hw⟩ : S) x)
    rw [MonoidHom.coprod_apply, MonoidHom.coprod_apply, map_one, map_one, one_mul, one_mul] at h
    dsimp only at h
    rw [hβ, hγ, Finset.prod_eq_single (⟨w, hw⟩ : S), Finset.prod_eq_single (⟨w, hw⟩ : S), Pi.mulSingle_eq_same] at h
    · exact h
    · intro w' _ h'
      rw [Pi.mulSingle_eq_of_ne h', map_one]
    · simp
    · intro w' _ h'
      rw [Pi.mulSingle_eq_of_ne h', map_one]
    · simp

end Global

end GlobalTheory.DelEps.Twist

end
