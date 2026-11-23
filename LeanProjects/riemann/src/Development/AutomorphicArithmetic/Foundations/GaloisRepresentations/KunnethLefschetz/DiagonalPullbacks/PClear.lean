import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion
import Development.EtaleCohomology.EtaleTrace.LRingPf
import Development.EtaleCohomology.EtaleTrace.H0LimitCoherence

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di.ClearPf

variable {l : ℕ} [Fact l.Prime]

private theorem coe_ne {b : ℤ_[l]} (hb : b ≠ 0) : (b : ℚ_[l]) ≠ 0 := by
  rwa [Ne, PadicInt.coe_eq_zero]

private theorem den {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] (z : ℚ_[l] ⊗[ℤ_[l]] M) :
    ∃ b : ℤ_[l], b ≠ 0 ∧ ∀ B : ℤ_[l], b ∣ B → ∃ y : M, (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y = (B : ℚ_[l]) • z := by
  obtain ⟨b, x, hb, rfl⟩ := H0LimitCoherence.tensor_form l z
  refine ⟨b, hb, fun B hB => ?_⟩
  obtain ⟨c, rfl⟩ := hB
  refine ⟨c • x, ?_⟩
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  congr 1
  have hb' := coe_ne hb
  rw [Algebra.smul_def, smul_eq_mul, PadicInt.coe_mul, mul_one]
  simp only [PadicInt.algebraMap_apply]
  field_simp

private theorem toV_cup (R : Ring l) {X : Scheme.{0}} {i j : ℕ} {x : TT l X i} {y : TT l X j} {z : TT l X (i + j)}
    (hz : CupL x y z) (hh : (i : ℤ) + j = ((i + j : ℕ) : ℤ)) : toV z = cupV l X hh (toV x) (toV y) := by
  exact (R.isCup X (i : ℤ) (j : ℤ) _ hh x y z (fun k => (hz k).trans rfl)).symm

private theorem ex_cup (h11 : A11) {X : Scheme.{0}} {i j : ℕ} (x : TT l X i) (y : TT l X j) :
    ∃ z : TT l X (i + j), CupL x y z :=
  ⟨LRingPf.cupL l (sch.obj X) (Nat.cast_add i j).symm h11 x y, fun _ => rfl⟩

private theorem toV_castL (R : Ring l) {X : Scheme.{0}} {i j n : ℕ} {x : TT l X i} {y : TT l X j} {z : TT l X (i + j)}
    (hz : CupL x y z) (hn : i + j = n) (hh : (i : ℤ) + j = (n : ℤ)) :
    toV (castL hn z) = cupV l X hh (toV x) (toV y) := by
  subst hn
  exact toV_cup R hz hh

private theorem scale {X P : Scheme.{0}} (p₁ p₂ : P ⟶ X) {i j : ℕ} {r : ℤ} (hh : (i : ℤ) + j = r) (β : ℚ_[l])
    {a : V l X i} {b : V l X j} {ah : TT l X i} {bh : TT l X j} (ha : toV ah = β • a) (hb : toV bh = β • b) :
    cupV l P hh (toV (pullHl l (sch.map p₁) _ 0 ah)) (toV (pullHl l (sch.map p₂) _ 0 bh)) =
      β • β • cupV l P hh (pb l p₁ _ a) (pb l p₂ _ b) := by
  have e₁ : toV (pullHl l (sch.map p₁) (i : ℤ) 0 ah) = pb l p₁ (i : ℤ) (toV ah) :=
    (LRingPf.pb_tmul l p₁ (i : ℤ) ah).symm
  have e₂ : toV (pullHl l (sch.map p₂) (j : ℤ) 0 bh) = pb l p₂ (j : ℤ) (toV bh) :=
    (LRingPf.pb_tmul l p₂ (j : ℤ) bh).symm
  rw [e₁, e₂, ha, hb]
  simp only [map_smul, LinearMap.smul_apply]

end UpperTheory.Gal.KunnethLefschetz.Di.ClearPf

open UpperTheory.Gal.KunnethLefschetz.Di.ClearPf in
theorem UpperTheory.Gal.KunnethLefschetz.Di.clear_holds :
    UpperTheory.Gal.KunnethLefschetz.Di.Clear := by
  intro hIn l _ R d X P W p₁ p₂ π hl e hQ
  obtain ⟨δ, m, s, a, b, t, i, j, hij, u, v, hπ, hlin, hsum, hj, hδ⟩ := hQ
  have h11 := hIn.a11
  obtain ⟨bm, hbm0, hbm⟩ := den (l := l) m
  choose ba hba0 hba using fun c => den (l := l) (a c)
  choose bb hbb0 hbb using fun c => den (l := l) (b c)
  choose bu hbu0 hbu using fun c => den (l := l) (u c)
  choose bv hbv0 hbv using fun c => den (l := l) (v c)
  set D : ℤ_[l] := bm * (∏ c, ba c * bb c) * (∏ c, bu c * bv c) with hD
  have hD0 : D ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hbm0 ?_) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun c _ => mul_ne_zero (hba0 c) (hbb0 c)
    · exact Finset.prod_ne_zero_iff.mpr fun c _ => mul_ne_zero (hbu0 c) (hbv0 c)
  have dA : ∀ c, ba c ∣ D := fun c => dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right ((dvd_mul_right _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ c))) _) _
  have dB : ∀ c, bb c ∣ D := fun c => dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right ((dvd_mul_left _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ c))) _) _
  have dU : ∀ c, bu c ∣ D := fun c =>
    dvd_mul_of_dvd_right ((dvd_mul_right _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ c))) _
  have dV : ∀ c, bv c ∣ D := fun c =>
    dvd_mul_of_dvd_right ((dvd_mul_left _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ c))) _
  have dM : bm ∣ D * D := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  clear_value D
  obtain ⟨w, hw⟩ := hbm _ dM
  choose a₀ ha₀ using fun c => hba c D (dA c)
  choose b₀ hb₀ using fun c => hbb c D (dB c)
  choose a₁ ha₁ using fun c => hbu c D (dU c)
  choose b₁ hb₁ using fun c => hbv c D (dV c)
  obtain ⟨z, hz⟩ := ex_cup h11 e w
  choose ab₀ hab₀ using fun c =>
    ex_cup h11 (pullHl l (sch.map p₁) _ 0 (a₀ c)) (pullHl l (sch.map p₂) _ 0 (b₀ c))
  choose ab hab using fun c =>
    ex_cup h11 (pullHl l (sch.map p₁) _ 0 (a₁ c)) (pullHl l (sch.map p₂) _ 0 (b₁ c))
  obtain ⟨one₀, hone, hone'⟩ := R.one_def X hl
  have hc : toV (∑ c, ab₀ c + ∑ c, castL (hij c) (ab c)) =
      ∑ c, toV (ab₀ c) + ∑ c, toV (castL (hij c) (ab c)) := by
    simp only [toV, TensorProduct.tmul_add, TensorProduct.tmul_sum]
  refine ⟨∑ c, ab₀ c + ∑ c, castL (hij c) (ab c), w, z, s, a₀, b₀, ab₀, t, i, j, hij, a₁, b₁, ab, one₀,
    (D : ℚ_[l]), hz, ?_, hab₀, hab, hj, hc, hone, coe_ne hD0, ?_, ?_⟩
  · refine (LRingPf.pb_tmul l π _ _).symm.trans ?_
    change pb l π _ (toV (∑ c, ab₀ c + ∑ c, castL (hij c) (ab c))) = toV z
    have hw' : toV w = ((D * D : ℤ_[l]) : ℚ_[l]) • m := hw
    rw [hc, toV_cup R hz (by push_cast; ring), hw', map_smul, ← hπ, ← map_smul]
    congr 1
    rw [hδ, smul_add, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [toV_cup R (hab₀ c) (by push_cast; ring), scale p₁ p₂ _ _ (ha₀ c) (hb₀ c), ← mul_smul,
        ← PadicInt.coe_mul]
      rfl
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [toV_castL R (hab c) (hij c) (by exact_mod_cast hij c), scale p₁ p₂ _ _ (ha₁ c) (hb₁ c),
        ← mul_smul, ← PadicInt.coe_mul]
  · have hfun : (fun c => toV (a₀ c)) = fun c => (D : ℚ_[l]) • a c := funext ha₀
    rw [hfun]
    exact hlin.units_smul fun _ => Units.mk0 _ (coe_ne hD0)
  · have hb : ∀ c, toV (b₀ c) = (D : ℚ_[l]) • b c := hb₀
    rw [Finset.sum_congr rfl fun c _ => hb c, ← Finset.smul_sum, hsum, hone']
