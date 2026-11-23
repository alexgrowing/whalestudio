import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem alt_expand {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] {d q : ℕ} (f : M [⋀^Fin q]→ₗ[R] N) (a : Fin q → Fin d → R) (v : Fin d → M) :
    f (fun i => ∑ l, a i l • v l) =
      ∑ S : {S : Finset (Fin d) // S.card = q},
        (Matrix.of fun i j => a i (S.1.orderEmbOfFin S.2 j)).det •
          f (fun j => v (S.1.orderEmbOfFin S.2 j)) := by
  classical
  have h1 : f (fun i => ∑ l, a i l • v l) =
      ∑ φ : Fin q → Fin d, (∏ i, a i (φ i)) • f (fun i => v (φ i)) := by
    have h := f.toMultilinearMap.map_sum (fun i l => a i l • v l)
    refine h.trans (Finset.sum_congr rfl fun φ _ => ?_)
    exact f.toMultilinearMap.map_smul_univ _ _
  let e : {S : Finset (Fin d) // S.card = q} → Fin q → Fin d := fun S j => S.1.orderEmbOfFin S.2 j
  have he : ∀ S, Function.Injective (e S) := fun S => (S.1.orderEmbOfFin S.2).injective
  have hr : ∀ S, Set.range (e S) = S.1 := fun S => Finset.range_orderEmbOfFin S.1 S.2
  let Φ : (Σ _ : {S : Finset (Fin d) // S.card = q}, Equiv.Perm (Fin q)) →
      {φ : Fin q → Fin d // Function.Injective φ} :=
    fun p => ⟨e p.1 ∘ p.2, (he p.1).comp p.2.injective⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨S, σ⟩ ⟨S', σ'⟩ h
      have h' : e S ∘ σ = e S' ∘ σ' := congrArg Subtype.val h
      have hS : S = S' := by
        apply Subtype.ext
        apply Finset.coe_injective
        rw [← hr S, ← hr S', ← σ.surjective.range_comp (e S), ← σ'.surjective.range_comp (e S'), h']
      subst hS
      have : σ = σ' := by
        ext i
        exact congrArg _ (he S (congrFun h' i))
      rw [this]
    · rintro ⟨φ, hφ⟩
      have hc : (Finset.univ.image φ).card = q := by
        rw [Finset.card_image_of_injective _ hφ]; simp
      let S : {S : Finset (Fin d) // S.card = q} := ⟨_, hc⟩
      have hm : ∀ i, ∃ j, e S j = φ i := fun i => by
        have : φ i ∈ Set.range (e S) := by rw [hr]; simp [S]
        exact this
      choose s hs using hm
      have hsi : Function.Injective s := fun i i' h => hφ (by rw [← hs, ← hs, h])
      refine ⟨⟨S, Equiv.ofBijective s (Finite.injective_iff_bijective.1 hsi)⟩, ?_⟩
      apply Subtype.ext
      funext i
      exact hs i
  rw [h1, ← Fintype.sum_subtype_add_sum_subtype (fun φ : Fin q → Fin d => Function.Injective φ)]
  have h0 : ∑ φ : {φ : Fin q → Fin d // ¬ Function.Injective φ},
      (∏ i, a i (φ.1 i)) • f (fun i => v (φ.1 i)) = 0 := by
    refine Finset.sum_eq_zero fun φ _ => ?_
    have : ¬ Function.Injective (fun i => v (φ.1 i)) := fun h => φ.2 fun i i' hi => h (by simp [hi])
    rw [f.map_eq_zero_of_not_injective _ this, smul_zero]
  rw [h0, add_zero, ← hΦ.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Matrix.det_transpose, Matrix.det_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hp := f.map_perm (fun j => v (e S j)) σ
  have hp' : f (fun i => v (e S (σ i))) = Equiv.Perm.sign σ • f (fun j => v (e S j)) := hp
  change (∏ i, a i (e S (σ i))) • f (fun i => v (e S (σ i))) = _
  rw [hp']
  have hq : ∏ i, (Matrix.of fun i j => a i (S.1.orderEmbOfFin S.2 j)).transpose (σ i) i =
      ∏ i, a i (e S (σ i)) := by
    rfl
  rw [hq]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, e]

private theorem mapDR_iM (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] (n : ℕ) (v : Fin n → K) :
    mapDR ℂ K L (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (v a)) =
      ExteriorAlgebra.ιMulti L n fun a => D ℂ L (algebraMap K L (v a)) := by
  simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext a
  simp [mapDR, map1, KaehlerDifferential.map_D]

private theorem pullback_kahler_iMulti {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] (j2 : K →ₐ[ℂ] L)
    (n : ℕ) (v : Fin n → K) :
    pr2L j2 (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (v a)) =
      ExteriorAlgebra.ιMulti L n fun a => D ℂ L (j2 (v a)) := by
  letI : Algebra K L := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_iM K L n v

private theorem iM_cast {L : Type} [Field L] [Algebra ℂ L] {d : ℕ} (S : Finset (Fin d)) (q : ℕ)
    (h : S.card = q) (w : Fin d → Ω[L⁄ℂ]) :
    ExteriorAlgebra.ιMulti L q (fun j => w (S.orderEmbOfFin h j)) =
      ExteriorAlgebra.ιMulti L S.card (fun j => w (S.orderEmbOfFin rfl j)) := by
  subst h; rfl

theorem UpperTheory.Gal.productCup_of_system.dtPull_of :
    LocOne → ValBasic → DtPull := by
  intro hLO hVB F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY e he T
  refine ⟨?_, ?_⟩
  · refine (mapDR_iM K K' _ _).trans ?_
    unfold dtS
    congr 1
    funext a
    simp only [tt, ← IsScalarTower.algebraMap_apply]
  · obtain ⟨hle, ⟨ev, hev⟩, hbv, -⟩ := hVB K' (rB ℂ K' (xv x) {0}) e.1
    have hLoc := hLO F K' d x hY.covY hY.red e
    have htB : ∀ l, tt K' x l ∈ rB ℂ K' (xv x) {0} := fun l => tco_mem ℂ K' (xv x) l
    have ht0 : ∀ l, ev ⟨tt K' x l, hle (htB l)⟩ = 0 := fun l => by
      obtain ⟨h, hh⟩ := (hev _ _).1 (hbv ⟨tt K' x l, htB l⟩)
      exact hh.trans (e.2 l)
    choose g hgv hgt using hY.tan e he
    have hg : ∀ m l, ∃ h : g m l ∈ loc (rB ℂ K' (xv x) {0}) e.1, ev ⟨g m l, h⟩ = A e m l :=
      fun m l => (hev _ _).1 (hgv m l)
    choose hgl hge using hg
    choose c hcl hcD using fun m l => hLoc (g m l) (hgl m l)
    let ah : Matrix (Fin d) (Fin d) (loc (rB ℂ K' (xv x) {0}) e.1) := fun m l =>
      ⟨g m l, hgl m l⟩ + ∑ l', ⟨tt K' x l', hle (htB l')⟩ * ⟨c m l' l, hcl m l' l⟩
    have hah : ∀ m l, (ah m l : K') = g m l + ∑ l', tt K' x l' * c m l' l := fun m l => by
      simp [ah]
    have hAh : ev.mapMatrix ah = A e := by
      ext m l
      change ev (⟨g m l, hgl m l⟩ + ∑ l', ⟨tt K' x l', hle (htB l')⟩ * ⟨c m l' l, hcl m l' l⟩) = A e m l
      rw [map_add, map_sum, hge]
      simp only [map_mul, ht0, zero_mul, Finset.sum_const_zero, add_zero]
    have hD : ∀ m, D ℂ K' (j2 (tt K x m)) = ∑ l, (ah m l : K') • D ℂ K' (tt K' x l) := by
      intro m
      rw [hgt m, map_sum]
      simp_rw [hah, add_smul, Finset.sum_add_distrib, Derivation.leibniz, hcD, Finset.smul_sum,
        Finset.sum_smul, smul_smul]
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm
    refine ⟨fun S => if hS : S.card = T.card then
      (((ah.submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin hS)).det :
        loc (rB ℂ K' (xv x) {0}) e.1) : K') else 0, ?_, ?_⟩
    · have h1 : pr2L j2 (dtS K x T) = ExteriorAlgebra.ιMulti K' T.card (fun a =>
          ∑ l, (ah (T.orderEmbOfFin rfl a) l : K') • D ℂ K' (tt K' x l)) := by
        unfold dtS
        rw [pullback_kahler_iMulti]
        congr 1
        funext a
        exact hD _
      rw [h1, alt_expand (ExteriorAlgebra.ιMulti K' T.card)
        (fun a l => (ah (T.orderEmbOfFin rfl a) l : K')) (fun l => D ℂ K' (tt K' x l)),
        Finset.sum_subtype (Finset.univ.powersetCard T.card) (p := fun S => S.card = T.card)
          (by simp [Finset.mem_powersetCard])]
      refine Finset.sum_congr rfl fun S _ => ?_
      simp only [dif_pos S.2]
      rw [iM_cast S.1 T.card S.2 (fun l => D ℂ K' (tt K' x l))]
      unfold dtS
      congr 1
      exact ((loc (rB ℂ K' (xv x) {0}) e.1).val.map_det
        (ah.submatrix (T.orderEmbOfFin rfl) (S.1.orderEmbOfFin S.2))).symm
    · intro S hS
      simp only [dif_pos hS]
      refine (hev _ _).2 ⟨SetLike.coe_mem _, ?_⟩
      change ev (ah.submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin hS)).det = _
      rw [AlgHom.map_det, ← hAh]
      rfl
