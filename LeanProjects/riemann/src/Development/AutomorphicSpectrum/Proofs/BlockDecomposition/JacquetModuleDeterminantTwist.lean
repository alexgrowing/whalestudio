import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.JacBridge

open GlobalTheory.SmGL Matrix
open scoped Kronecker
open GroundTheory.Automorphic.Parabolic (levi jacquetRep JacquetModule sqrtModular invSqrtModular leviIncl unipotentRadical
  jacquetRep_mk mem_unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper mem_blockUpper)
open GroundTheory.Automorphic.Measures (adLie parabolicCoord ParabolicIndex coe_adLie coe_parabolicCoord_symm_single
  mul_single_mul_apply modularCharacter_blockUpper)

theorem prod_le_pairs {α G : Type} [Fintype α] [LinearOrder α] [CommGroup G] (f : α → G) (n : α → ℕ) :
    ∏ a, ∏ c, (if a ≤ c then f a ^ n c * (f c)⁻¹ ^ n a else 1) =
      ∏ a, f a ^ ((∑ b with a < b, (n b : ℤ)) - ∑ b with b < a, (n b : ℤ)) := by
  have h1 : ∀ a c : α, (if a ≤ c then f a ^ n c * (f c)⁻¹ ^ n a else 1) =
      (if a < c then f a ^ n c else 1) * (if a < c then (f c)⁻¹ ^ n a else 1) := by
    intro a c
    rcases lt_trichotomy a c with h | rfl | h
    · simp [h.le, h]
    · simp
    · simp [not_le.mpr h, not_lt.mpr h.le]
  have hA : ∀ a : α, ∏ c, (if a < c then f a ^ n c else 1) = f a ^ (∑ b with a < b, n b) := by
    intro a
    rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum]
  have hB : ∀ c : α, ∏ a, (if a < c then (f c)⁻¹ ^ n a else 1) =
      (f c ^ (∑ b with b < c, n b))⁻¹ := by
    intro c
    rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, inv_pow]
  calc ∏ a, ∏ c, (if a ≤ c then f a ^ n c * (f c)⁻¹ ^ n a else 1)
      = ∏ a, ∏ c, ((if a < c then f a ^ n c else 1) * (if a < c then (f c)⁻¹ ^ n a else 1)) :=
        Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun c _ => h1 a c
    _ = (∏ a, ∏ c, (if a < c then f a ^ n c else 1)) *
          ∏ a, ∏ c, (if a < c then (f c)⁻¹ ^ n a else 1) := by
        simp only [Finset.prod_mul_distrib]
    _ = (∏ a, ∏ c, (if a < c then f a ^ n c else 1)) *
          ∏ c, ∏ a, (if a < c then (f c)⁻¹ ^ n a else 1) := by
        congr 1
        exact Finset.prod_comm
    _ = (∏ a, f a ^ (∑ b with a < b, n b)) * ∏ a, (f a ^ (∑ b with b < a, n b))⁻¹ := by
        rw [Finset.prod_congr rfl fun a _ => hA a, Finset.prod_congr rfl fun c _ => hB c]
    _ = ∏ a, f a ^ (∑ b with a < b, n b) * (f a ^ (∑ b with b < a, n b))⁻¹ := by
        rw [Finset.prod_mul_distrib]
    _ = ∏ a, f a ^ ((∑ b with a < b, (n b : ℤ)) - ∑ b with b < a, (n b : ℤ)) := by
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [_root_.zpow_sub, ← Nat.cast_sum, ← Nat.cast_sum, zpow_natCast, zpow_natCast]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)]
  [∀ j, DecidableEq (m' j)] {N : ℕ}

theorem label_eq_iff {e' : (Σ j, m' j) ≃ Fin N} {γ : Fin N → ℕ}
    (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) (x y : Fin N) :
    γ x = γ y ↔ blk e' x = blk e' y := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have a1 : ¬ blk e' x < blk e' y := fun hl => by
      have := (hγ x y).mpr hl
      rw [h] at this
      exact lt_irrefl _ this
    have a2 : ¬ blk e' y < blk e' x := fun hl => by
      have := (hγ y x).mpr hl
      rw [h] at this
      exact lt_irrefl _ this
    exact le_antisymm (not_lt.mp a2) (not_lt.mp a1)
  · have a1 : ¬ γ x < γ y := fun hl => by
      have := (hγ x y).mp hl
      rw [h] at this
      exact lt_irrefl _ this
    have a2 : ¬ γ y < γ x := fun hl => by
      have := (hγ y x).mp hl
      rw [h] at this
      exact lt_irrefl _ this
    exact le_antisymm (not_lt.mp a2) (not_lt.mp a1)

theorem unipRad_eq {e' : (Σ j, m' j) ≃ Fin N} {γ : Fin N → ℕ}
    (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) :
    unipRad k e' = unipotentRadical k N γ := by
  ext g
  rw [GlobalTheory.SmGL.mem_unipRad, GlobalTheory.SmGL.mem_parab, mem_unipotentRadical, mem_blockUpper]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => h1 i j ((hγ j i).mp hij), fun i j hij => ?_⟩
    have hb := (label_eq_iff hγ i j).mp hij
    obtain ⟨⟨a, u⟩, rfl⟩ := e'.surjective i
    obtain ⟨⟨b, v⟩, rfl⟩ := e'.surjective j
    rw [blk_apply, blk_apply] at hb
    subst hb
    rw [h2 a u v]
    simp [Matrix.one_apply]
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => h1 ((hγ j i).mpr hij), fun a u v => ?_⟩
    rw [h2 _ _ ((label_eq_iff hγ _ _).mpr (by rw [blk_apply, blk_apply]))]
    simp [Matrix.one_apply]

def adCoord {γ : Fin N → ℕ} (p : blockUpper k N γ) :
    (ParabolicIndex N γ → k) →ₗ[k] (ParabolicIndex N γ → k) :=
  (((parabolicCoord k N γ).symm.trans ((adLie k N γ p).trans (parabolicCoord k N γ))) :
    (ParabolicIndex N γ → k) →ₗ[k] (ParabolicIndex N γ → k))

theorem det_adLie_eq {γ : Fin N → ℕ} (p : blockUpper k N γ) :
    (LinearEquiv.det (adLie k N γ p) : k) = (LinearMap.toMatrix' (adCoord p)).det := by
  rw [LinearMap.det_toMatrix', adCoord, ← LinearEquiv.coe_det]
  exact congrArg Units.val (LinearEquiv.det_conj (adLie k N γ p) (parabolicCoord k N γ)).symm

theorem adCoord_apply {γ : Fin N → ℕ} (p : blockUpper k N γ) (s t : ParabolicIndex N γ) :
    LinearMap.toMatrix' (adCoord p) s t =
      ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) s.1.1 t.1.1 *
        (((p : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) t.1.2 s.1.2 := by
  rw [LinearMap.toMatrix'_apply]
  show ((adLie k N γ p ((parabolicCoord k N γ).symm (Pi.single t 1)) : Matrix (Fin N) (Fin N) k)) s.1.1 s.1.2 = _
  rw [coe_adLie, coe_parabolicCoord_symm_single, mul_single_mul_apply]

theorem leviEmb_apply_ne' (e' : (Σ j, m' j) ≃ Fin N) (g : Levi k m') {x y : Fin N}
    (h : blk e' x ≠ blk e' y) : (leviEmb k e' g : Matrix (Fin N) (Fin N) k) x y = 0 := by
  simp only [leviEmb, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.blockDiagonal'_apply]
  exact dif_neg h

def parabolicBlockPair (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ) (s : ParabolicIndex N γ) : Lex (β' × β') :=
  toLex (blk e' s.1.1, blk e' s.1.2)

section DetAd

variable {e' : (Σ j, m' j) ≃ Fin N} {γ : Fin N → ℕ}
  (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) (g : Levi k m') (p : blockUpper k N γ)
  (hp : (p : GL (Fin N) k) = leviEmb k e' g)

include hp in
theorem adCoord_apply_levi (s t : ParabolicIndex N γ) :
    LinearMap.toMatrix' (adCoord p) s t =
      (leviEmb k e' g : Matrix (Fin N) (Fin N) k) s.1.1 t.1.1 *
        (leviEmb k e' g⁻¹ : Matrix (Fin N) (Fin N) k) t.1.2 s.1.2 := by
  rw [adCoord_apply, hp, ← map_inv]

include hp in
theorem adCoord_blockTriangular :
    (LinearMap.toMatrix' (adCoord p)).BlockTriangular (parabolicBlockPair e' γ) := by
  intro s t hst
  rw [adCoord_apply_levi g p hp s t]
  by_cases h1 : blk e' s.1.1 = blk e' t.1.1
  · by_cases h2 : blk e' t.1.2 = blk e' s.1.2
    · have heq : parabolicBlockPair e' γ t = parabolicBlockPair e' γ s := by
        simp only [parabolicBlockPair, h1, h2]
      rw [heq] at hst
      exact absurd hst (lt_irrefl _)
    · rw [leviEmb_apply_ne' e' g⁻¹ h2, mul_zero]
  · rw [leviEmb_apply_ne' e' g h1, zero_mul]

include hγ hp in
theorem block_det_of_le {a c : β'} (hac : a ≤ c) :
    ((LinearMap.toMatrix' (adCoord p)).toSquareBlock (parabolicBlockPair e' γ) (toLex (a, c))).det =
      (g a : Matrix (m' a) (m' a) k).det ^ Fintype.card (m' c) *
        ((g c)⁻¹ : GL (m' c) k).val.det ^ Fintype.card (m' a) := by
  have hmem : ∀ (u : m' a) (v : m' c), ¬ γ (e' ⟨c, v⟩) < γ (e' ⟨a, u⟩) := by
    intro u v h
    have h' := (hγ _ _).mp h
    simp only [blk, Equiv.symm_apply_apply] at h'
    exact absurd hac (not_le.mpr h')
  let F : m' a × m' c → {s : ParabolicIndex N γ // parabolicBlockPair e' γ s = toLex (a, c)} :=
    fun uv => ⟨⟨(e' ⟨a, uv.1⟩, e' ⟨c, uv.2⟩), hmem uv.1 uv.2⟩, by simp [parabolicBlockPair, blk]⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨u, v⟩ ⟨u', v'⟩ h
      have h1 : e' ⟨a, u⟩ = e' ⟨a, u'⟩ := congrArg (fun s => s.1.1.1) h
      have h2 : e' ⟨c, v⟩ = e' ⟨c, v'⟩ := congrArg (fun s => s.1.1.2) h
      simp only [EmbeddingLike.apply_eq_iff_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h1 h2
      rw [h1, h2]
    · rintro ⟨⟨⟨i, j⟩, hij⟩, hs⟩
      simp only [parabolicBlockPair, toLex_inj, Prod.mk.injEq] at hs
      obtain ⟨hi, hj⟩ := hs
      obtain ⟨⟨ai, u⟩, rfl⟩ := e'.surjective i
      obtain ⟨⟨cj, v⟩, rfl⟩ := e'.surjective j
      simp only [blk, Equiv.symm_apply_apply] at hi hj
      subst hi hj
      exact ⟨(u, v), rfl⟩
  have hL : ∀ (g' : Levi k m') (b : β') (x y : m' b),
      (leviEmb k e' g' : Matrix (Fin N) (Fin N) k) (e' ⟨b, x⟩) (e' ⟨b, y⟩) =
        (g' b : Matrix (m' b) (m' b) k) x y := by
    intro g' b x y
    simp only [leviEmb, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_eq]
  let E := Equiv.ofBijective F hF
  have hM : ((LinearMap.toMatrix' (adCoord p)).toSquareBlock (parabolicBlockPair e' γ) (toLex (a, c))).submatrix E E =
      (g a : Matrix (m' a) (m' a) k) ⊗ₖ (((g c)⁻¹ : GL (m' c) k) : Matrix (m' c) (m' c) k)ᵀ := by
    ext ⟨u, v⟩ ⟨u', v'⟩
    show LinearMap.toMatrix' (adCoord p) (F (u, v)).1 (F (u', v')).1 =
      (g a : Matrix (m' a) (m' a) k) u u' * (((g c)⁻¹ : GL (m' c) k) : Matrix (m' c) (m' c) k) v' v
    rw [adCoord_apply_levi g p hp]
    show (leviEmb k e' g : Matrix (Fin N) (Fin N) k) (e' ⟨a, u⟩) (e' ⟨a, u'⟩) *
      (leviEmb k e' g⁻¹ : Matrix (Fin N) (Fin N) k) (e' ⟨c, v'⟩) (e' ⟨c, v⟩) = _
    rw [hL g a u u', hL g⁻¹ c v' v]
    rfl
  rw [← Matrix.det_submatrix_equiv_self E, hM, Matrix.det_kronecker, Matrix.det_transpose]

include hγ in
theorem block_det_of_not_le {a c : β'} (hac : ¬ a ≤ c) :
    ((LinearMap.toMatrix' (adCoord p)).toSquareBlock (parabolicBlockPair e' γ) (toLex (a, c))).det = 1 := by
  haveI : IsEmpty {s : ParabolicIndex N γ // parabolicBlockPair e' γ s = toLex (a, c)} := ⟨fun s => by
    have hs := s.2
    simp only [parabolicBlockPair, toLex_inj, Prod.mk.injEq] at hs
    apply s.1.2
    rw [hγ, hs.1, hs.2]
    exact not_le.mp hac⟩
  exact Matrix.det_isEmpty

include hγ hp in

theorem det_adLie_levi :
    (LinearEquiv.det (adLie k N γ p) : kˣ) =
      ∏ a, GeneralLinearGroup.det (g a) ^ modExp m' a := by
  have key := prod_le_pairs (fun a => GeneralLinearGroup.det (g a)) (fun a => Fintype.card (m' a))
  apply Units.ext
  rw [det_adLie_eq, (adCoord_blockTriangular g p hp).det,
    Finset.prod_subset (Finset.subset_univ _) (fun x _ hx => ?hz)]
  case hz =>
    haveI : IsEmpty {s : ParabolicIndex N γ // parabolicBlockPair e' γ s = x} :=
      ⟨fun s => hx (Finset.mem_image.mpr ⟨s.1, Finset.mem_univ _, s.2⟩)⟩
    exact Matrix.det_isEmpty
  rw [← Equiv.prod_comp toLex, Fintype.prod_prod_type]
  change _ = ((∏ a, GeneralLinearGroup.det (g a) ^ ((∑ b with a < b, (Fintype.card (m' b) : ℤ)) -
    ∑ b with b < a, (Fintype.card (m' b) : ℤ)) : kˣ) : k)
  rw [← key, Units.coe_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  by_cases hac : a ≤ c
  · rw [if_pos hac, block_det_of_le hγ g p hp hac, ← Matrix.GeneralLinearGroup.val_det_apply,
      ← Matrix.GeneralLinearGroup.val_det_apply, map_inv, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val]
  · rw [if_neg hac, block_det_of_not_le hγ p hac, Units.val_one]

end DetAd

section Main

theorem modularCharacter_levi {e' : (Σ j, m' j) ≃ Fin N} {γ : Fin N → ℕ}
    (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) (g : Levi k m') (p : blockUpper k N γ)
    (hp : (p : GL (Fin N) k) = leviEmb k e' g) :
    ((MeasureTheory.Measure.modularCharacter p : NNReal) : ℝ) = modulus k m' g := by
  rw [modularCharacter_blockUpper, det_adLie_levi hγ g p hp, map_prod, NNReal.coe_prod, modulus]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_zpow, NNReal.coe_zpow]
  rfl

theorem invSqrtModular_levi {e' : (Σ j, m' j) ≃ Fin N} {γ : Fin N → ℕ}
    (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) (g : Levi k m') (p : blockUpper k N γ)
    (hp : (p : GL (Fin N) k) = leviEmb k e' g) :
    invSqrtModular k N γ p = (((deltaHalf k m' g)⁻¹ : ℂˣ) : ℂ) := by
  have hpos : ∀ a, 0 ≤ GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det (g a)) := fun a => NNReal.coe_nonneg _
  have h1 : ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter p) : NNReal) : ℝ) =
      ∏ a, GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det (g a)) ^ ((modExp m' a : ℝ) / 2) := by
    rw [Real.coe_sqrt, modularCharacter_levi hγ g p hp, modulus, Real.sqrt_eq_rpow,
      ← Real.finsetProd_rpow _ _ (fun a _ => zpow_nonneg (hpos a) _)]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Real.rpow_intCast, ← Real.rpow_mul (hpos a)]
    ring_nf
  simp only [invSqrtModular, sqrtModular, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h1, Units.val_inv_eq_inv_val]
  congr 1
  rw [deltaHalf, MonoidHom.finsetProd_apply, Units.coe_prod, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Complex.ofReal_cpow (hpos a)]
  simp only [MonoidHom.comp_apply, Pi.evalMonoidHom_apply, detChar, absPow, MonoidHom.coe_toHomUnits,
    MonoidHom.coe_mk, OneHom.coe_mk]
  push_cast
  rfl

theorem twKer_eq_ker {e' : (Σ j, m' j) ≃ Fin N} {γ : Fin N → ℕ}
    (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    GlobalTheory.PRep.twKer π (unipRad k e') 1 =
      Representation.Coinvariants.ker (π.comp (unipotentRadical k N γ).subtype) := by
  rw [unipRad_eq hγ]
  unfold GlobalTheory.PRep.twKer Representation.Coinvariants.ker
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_range, MonoidHom.one_apply, Units.val_one, one_smul, Prod.exists,
    MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply]
  constructor <;> rintro ⟨n, v, h⟩ <;> exact ⟨n, v, h.symm⟩

theorem jac_equiv_jacquetRep (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type}
    [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {N : ℕ} (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ)
    (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) (φ' : Levi k m' ≃* levi k N γ)
    (hφ : ∀ g, ((φ' g : levi k N γ) : GL (Fin N) k) = leviEmb k e' g)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    Nonempty ((jac e' π).Equiv ((jacquetRep k N γ π).comp φ'.toMonoidHom)) := by
  let L : GlobalTheory.PRep.Jacquet π (unipRad k e') ≃ₗ[ℂ] JacquetModule k N γ π :=
    Submodule.quotEquivOfEq _ _ (twKer_eq_ker hγ π)
  have hL : ∀ v : V, L (Submodule.Quotient.mk v) =
      Representation.Coinvariants.mk (π.comp (unipotentRadical k N γ).subtype) v := fun v => rfl
  have hI : ∀ (g : Levi k m') (x : GlobalTheory.PRep.Jacquet π (unipRad k e')),
      L (jac e' π g x) = ((jacquetRep k N γ π).comp φ'.toMonoidHom) g (L x) := by
    intro g x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (GlobalTheory.PRep.twKer π (unipRad k e') 1) x
    have hp : ((leviIncl (φ' g) : blockUpper k N γ) : GL (Fin N) k) = leviEmb k e' g := hφ g
    have h1 : jac e' π g (Submodule.Quotient.mk v) =
        (((deltaHalf k m' g)⁻¹ : ℂˣ) : ℂ) •
          (Submodule.Quotient.mk (π (leviEmb k e' g) v) : GlobalTheory.PRep.Jacquet π (unipRad k e')) := rfl
    rw [h1, map_smul, hL, hL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, jacquetRep_mk,
      invSqrtModular_levi hγ g _ hp, hφ g]
  exact ⟨Representation.Equiv.mk' ⟨L.toLinearMap, fun g => LinearMap.ext fun x => hI g x⟩
    L.symm L.left_inv L.right_inv⟩

end Main

end GlobalTheory.CompanionTheory.JacBridge
