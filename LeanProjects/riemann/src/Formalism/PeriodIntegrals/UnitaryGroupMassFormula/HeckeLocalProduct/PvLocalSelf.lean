import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.Kernel

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct

namespace PI.HeckeProdW

variable {L : Type} [Field L] [NumberField L]

def pv (v : HeightOneSpectrum (𝓞 L)) : Ideles L →* v.adicCompletion L where
  toFun a := (a : AdeleRing (𝓞 L) L).2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def pw (w : InfinitePlace L) : Ideles L →* w.Completion where
  toFun a := (a : AdeleRing (𝓞 L) L).1 w
  map_one' := rfl
  map_mul' _ _ := rfl

theorem f_inv_mul {M : Type*} [Monoid M] (f : Ideles L →* M) (A D : Ideles L) (h : f A = f D) :
    f (A⁻¹ * D) = 1 := by
  rw [map_mul, ← h, ← map_mul, inv_mul_cancel, map_one]

theorem f_inv_mul' {M : Type*} [Monoid M] (f : Ideles L →* M) (A D : Ideles L) (h : f A = 1) :
    f (A⁻¹ * D) = f D := by
  have h1 : f A⁻¹ = 1 := by
    calc f A⁻¹ = f A⁻¹ * f A := by rw [h, mul_one]
      _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [map_mul, h1, one_mul]

theorem Phi_single [DecidableEq (HeightOneSpectrum (𝓞 L))] (v : HeightOneSpectrum (𝓞 L))
    (w : (v.adicCompletionIntegers L)ˣ) :
    Phi L (Pi.mulSingle v w) = localIdele L v (Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom w) := by
  refine Units.ext (Prod.ext rfl (Subtype.ext (funext fun v' => ?_)))
  change (((Pi.mulSingle v w : Pu L) v' : v'.adicCompletionIntegers L) : v'.adicCompletion L) = pv v' (localIdele L v (Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom w))
  by_cases h : v' = v
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact (localIdele_snd_self L v' (Units.map (v'.adicCompletionIntegers L).subtype.toMonoidHom w)).symm
  · rw [Pi.mulSingle_eq_of_ne h]
    exact ((localIdele_isSupportedAt L v _).2 v' h).symm

theorem chi_unit (χ : HChar L) (u : Ideles L) (h1 : (u : AdeleRing (𝓞 L) L).1 = 1)
    (h2 : ∀ v, Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1)
    (h3 : ∀ v, (u : AdeleRing (𝓞 L) L).2 v ≠ 1 → χ.UnrAt v) : χ.1 u = 1 := by
  classical
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring χ
  have hmemO : ∀ v : HeightOneSpectrum (𝓞 L), (u : AdeleRing (𝓞 L) L).2 v ∈ v.adicCompletionIntegers L := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact (h2 v).le
  have hunit : ∀ v : HeightOneSpectrum (𝓞 L), IsUnit (⟨_, hmemO v⟩ : v.adicCompletionIntegers L) := fun v =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 (h2 v)
  let y : Pu L := fun v => (hunit v).unit
  have hu : u = Phi L y := Units.ext (Prod.ext (h1.trans rfl) (Subtype.ext (funext fun v => rfl)))
  set p : Pu L := ∏ v ∈ T, Pi.mulSingle v (y v) with hp
  have hpv : ∀ v ∈ T, p v = y v := fun v hv => by
    rw [hp, Finset.prod_apply, Finset.prod_pi_mulSingle, if_pos hv]
  have hsplit : y = p * (p⁻¹ * y) := by rw [mul_inv_cancel_left]
  have hrest : χ.1 (Phi L (p⁻¹ * y)) = 1 :=
    hT _ fun v hv => by rw [Pi.mul_apply, Pi.inv_apply, hpv v hv, inv_mul_cancel]
  rw [hu, hsplit, map_mul, map_mul, hrest, mul_one, hp, map_prod, map_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [Phi_single]
  by_cases hv : χ.UnrAt v
  · exact hv _ (h2 v)
  · have hv1 : (u : AdeleRing (𝓞 L) L).2 v = 1 := by
      by_contra h
      exact hv (h3 v h)
    have hx : Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom (y v) = 1 := Units.ext hv1
    rw [hx, map_one, map_one]

theorem pw_local (w : InfinitePlace L) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    pw w (localIdele L v x) = 1 :=
  (localIdele_isSupportedAt L v x).1 w

theorem pv_local_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    pv v (localIdele L v x) = x := by
  classical
  show (RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L) v
    (x : v.adicCompletion L)) v = x
  simp

theorem pv_local_ne (v v' : HeightOneSpectrum (𝓞 L)) (h : v' ≠ v) (x : (v.adicCompletion L)ˣ) :
    pv v' (localIdele L v x) = 1 := by
  classical
  show (RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L) v
    (x : v.adicCompletion L)) v' = 1
  simp [h]

theorem infDiag_eq (k : Lˣ) : (infDiag k : Ideles L) = ∏ w : InfinitePlace L, infIdele L w (atInf w k) := by
  rw [infDiag, MonoidHom.finsetProd_apply]
  rfl

theorem pw_infDiag (w : InfinitePlace L) (k : Lˣ) : pw w (infDiag k) = (atInf w k : w.Completion) := by
  rw [infDiag_eq, map_prod, Finset.prod_eq_single w]
  · exact infIdele_fst_self L w _
  · intro b _ hb
    exact infIdele_fst_ne L b w (Ne.symm hb) _
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem pv_infDiag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : pv v (infDiag k) = 1 := by
  rw [infDiag_eq, map_prod]
  exact Finset.prod_eq_one fun w _ => infIdele_snd L w (atInf w k) v

theorem pw_diag (w : InfinitePlace L) (k : Lˣ) : pw w (diagUnits L k) = (atInf w k : w.Completion) := rfl

theorem pv_diag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : pv v (diagUnits L k) = (atFin v k : v.adicCompletion L) := rfl

theorem valued_atFin (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = v.valuation L (k : L) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : L)

theorem locK_eq (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) (k : Lˣ) :
    χ.locK v k = χ.val v ^ ordF v k := by
  have hx : IsUnitAt v (atFin v k * (atFin v (unif v)) ^ (-ordF v k)) := by
    have hu := unif_spec v
    unfold IsUnifAt at hu
    unfold IsUnitAt
    have h0 : v.valuation L (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hu, valued_atFin,
      ← WithZero.exp_log h0, ← WithZero.exp_zsmul, ← WithZero.exp_add, ← WithZero.exp_zero]
    congr 1
    simp only [ordF, smul_eq_mul]
    ring
  have e : atFin v k = (atFin v k * (atFin v (unif v)) ^ (-ordF v k)) * (atFin v (unif v)) ^ ordF v k := by
    rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  calc χ.locK v k = χ.loc v (atFin v k) := rfl
    _ = χ.loc v (atFin v k * (atFin v (unif v)) ^ (-ordF v k)) * χ.loc v (atFin v (unif v)) ^ ordF v k := by
      conv_lhs => rw [e]
      rw [map_mul (χ.loc v), map_zpow (χ.loc v)]
    _ = χ.val v ^ ordF v k := by rw [h _ hx, one_mul]; rfl

theorem productRule (χ : HChar L) : χ.ProductRule := by
  classical
  intro S hS k
  have hfin : {v : HeightOneSpectrum (𝓞 L) | ¬ Valued.v ((diagUnits L k : AdeleRing (𝓞 L) L).2 v) = 1}.Finite :=
    Filter.eventually_cofinite.1 (valued_comp_eventually L (diagUnits L k))
  set T0 : Finset (HeightOneSpectrum (𝓞 L)) := S ∪ hfin.toFinset with hT0
  set A : Ideles L := infDiag k * ∏ v ∈ T0, localIdele L v (atFin v k) with hA
  set u : Ideles L := A⁻¹ * diagUnits L k with hu
  have hAw : ∀ w, pw w A = pw w (diagUnits L k) := by
    intro w
    rw [hA, map_mul, map_prod, Finset.prod_eq_one (fun v _ => pw_local w v _), mul_one, pw_infDiag, pw_diag]
  have hAv_in : ∀ v ∈ T0, pv v A = pv v (diagUnits L k) := by
    intro v hv
    rw [hA, map_mul, map_prod, pv_infDiag, one_mul,
      Finset.prod_eq_single v (fun b _ hb => pv_local_ne b v (Ne.symm hb) _) (fun h => absurd hv h),
      pv_local_self, pv_diag]
  have hAv_out : ∀ v ∉ T0, pv v A = 1 := by
    intro v hv
    rw [hA, map_mul, map_prod, pv_infDiag, one_mul]
    exact Finset.prod_eq_one fun b hb => pv_local_ne b v (fun h => hv (h ▸ hb)) _
  have hu1 : χ.1 u = 1 := by
    apply chi_unit χ u
    · funext w
      exact f_inv_mul (pw w) A _ (hAw w)
    · intro v
      by_cases hv : v ∈ T0
      · show Valued.v (pv v u) = 1
        rw [hu, f_inv_mul (pv v) A _ (hAv_in v hv)]
        exact map_one _
      · show Valued.v (pv v u) = 1
        rw [hu, f_inv_mul' (pv v) A _ (hAv_out v hv)]
        by_contra h
        exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
    · intro v hne
      have hv : v ∉ T0 := fun hv => hne (by
        show pv v u = 1
        rw [hu, f_inv_mul (pv v) A _ (hAv_in v hv)])
      exact hS v (fun h => hv (Finset.mem_union_left _ h))
  have hD : diagUnits L k = A * u := by rw [hu, mul_inv_cancel_left]
  have hmain : χ.inf k * ∏ v ∈ T0, χ.locK v k = 1 := by
    have h := χ.2.2 k
    rw [hD, map_mul, hu1, mul_one, hA, map_mul, map_prod] at h
    exact h
  have hord : ∀ v ∉ T0, ordF v k = 0 := by
    intro v hv
    have h1 : Valued.v ((diagUnits L k : AdeleRing (𝓞 L) L).2 v) = 1 := by
      by_contra h
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
    rw [diag_comp] at h1
    simp [ordF, h1]
  have hfp : (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), χ.val v ^ ordF v k) = ∏ v ∈ T0 \ S, χ.locK v k := by
    change (∏ᶠ v ∈ ((S : Set (HeightOneSpectrum (𝓞 L)))ᶜ), χ.val v ^ ordF v k) = _
    rw [finprod_mem_eq_prod_of_subset _ (t := T0 \ S)]
    · exact Finset.prod_congr rfl fun v hv => (locK_eq χ (hS v (Finset.mem_sdiff.1 hv).2) k).symm
    · rintro v ⟨hvS, hvf⟩
      rw [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe]
      refine ⟨?_, hvS⟩
      by_contra hv
      exact hvf (by show χ.val v ^ ordF v k = 1; rw [hord v hv, zpow_zero])
    · intro v hv
      rw [Finset.coe_sdiff] at hv
      exact hv.2
  rw [hfp, mul_assoc, mul_comm (∏ v ∈ S, χ.locK v k), Finset.prod_sdiff Finset.subset_union_left]
  exact hmain

end PI.HeckeProdW
