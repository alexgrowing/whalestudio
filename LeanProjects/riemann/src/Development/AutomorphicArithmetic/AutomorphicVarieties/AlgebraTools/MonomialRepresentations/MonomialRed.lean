import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CharPerm

open Polynomial Matrix

private theorem exists_subring_hom_algebraicClosure_of_injective (B K k : Type) [CommRing B] [Field K] [Field k] (j : B →+* K)
    (hj : Function.Injective j) (φ : B →+* k) :
    ∃ (C : Subring K) (ρ : C →+* AlgebraicClosure k) (hC : ∀ b, j b ∈ C),
      (∀ b, ρ ⟨j b, hC b⟩ = algebraMap k (AlgebraicClosure k) (φ b)) ∧
      ∀ p : B[X], p.Monic → ∀ z : K, (p.map j).IsRoot z → z ∈ C := by
  letI : Algebra B K := j.toAlgebra
  let C := integralClosure B K
  have hCj : ∀ b, (algebraMap B C b : K) = j b := fun b => rfl
  have hinj : Function.Injective (algebraMap B C) := by
    intro a c h
    apply hj
    rw [← hCj, ← hCj, h]
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (R := B) (S := C)
    (RingHom.ker φ) ⊥ (by
      intro b hb
      rw [Ideal.mem_comap, Ideal.mem_bot, ← (algebraMap B C).map_zero] at hb
      rw [hinj hb, RingHom.mem_ker, φ.map_zero])
  haveI := hQ
  haveI hQ' : (Q.comap (algebraMap B C)).IsPrime := by
    rw [hQc]
    infer_instance
  let R := B ⧸ Q.comap (algebraMap B C)
  let S := C ⧸ Q
  let M := AlgebraicClosure k
  haveI hRd : IsDomain R := Ideal.Quotient.isDomain _
  haveI : Nontrivial R := hRd.toNontrivial
  haveI : IsDomain S := Ideal.Quotient.isDomain _
  let f : R →+* k := Ideal.Quotient.lift _ φ (fun b hb => by
    rw [hQc] at hb
    exact hb)
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 (fun x hx => ?_)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem, hQc]
    exact hx
  letI : Algebra R M := ((algebraMap k M).comp f).toAlgebra
  have hRS : Function.Injective (algebraMap R S) := by
    refine (injective_iff_map_eq_zero _).2 (fun x hx => ?_)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  have hRM : Function.Injective (algebraMap R M) :=
    (algebraMap k M).injective.comp hf
  haveI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.2 hRS
  haveI : Module.IsTorsionFree R M := Module.isTorsionFree_iff_algebraMap_injective.2 hRM
  haveI hI : Algebra.IsIntegral R S := Algebra.IsIntegral.quotient
  haveI : Algebra.IsAlgebraic R S := hI.isAlgebraic
  let L : S →ₐ[R] M := IsAlgClosed.lift
  refine ⟨C.toSubring, L.toRingHom.comp (Ideal.Quotient.mk Q), fun b => (algebraMap B C b).2, ?_, ?_⟩
  · intro b
    show L (Ideal.Quotient.mk Q (algebraMap B C b)) = _
    have h2 : Ideal.Quotient.mk Q (algebraMap B C b) =
        algebraMap R S (Ideal.Quotient.mk (Q.comap (algebraMap B C)) b) := rfl
    rw [h2, L.commutes]
    rfl
  · intro p hp z hz
    refine ⟨p, hp, ?_⟩
    rw [← Polynomial.eval_map]
    exact hz

private theorem monomialRed_lemma_2 {K G : Type} [Field K] [Group G] {n : ℕ}
    (r : G →* Matrix (Fin n) (Fin n) K) (b : Module.Basis (Fin n) K (Fin n → K)) (y : G)
    (e : Fin n → K) (he : ∀ i, r y *ᵥ b i = e i • b i) :
    (r y).charpoly = ∏ i, (X - C (e i)) := by
  rw [← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix _ b]
  have h : LinearMap.toMatrix b b (Matrix.toLin' (r y)) = Matrix.diagonal e := by
    ext i l
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, he, map_smul, b.repr_self,
      Matrix.diagonal_apply]
    by_cases hil : i = l
    · subst hil
      simp
    · simp [hil, Finsupp.single_apply, Ne.symm hil]
  rw [h, Matrix.charpoly_diagonal]

private theorem roots_prod_X_sub_C_fin_eq_map_univ {F : Type} [Field F] {n : ℕ} (f : Fin n → F) :
    (∏ i, (X - C (f i))).roots = Finset.univ.val.map f := by
  rw [Finset.prod_eq_multiset_prod]
  have h : (Finset.univ.val.map fun i => X - C (f i)) =
      (Finset.univ.val.map f).map (fun a => X - C a) := by
    rw [Multiset.map_map]
    rfl
  rw [h, Polynomial.roots_multiset_prod_X_sub_C]

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.AlgebraTools.monomialRed :
    ∀ (K k B G : Type) [Field K] [IsAlgClosed K] [Field k] [CommRing B] [Group G] (n : ℕ) (r : G →* Matrix (Fin n) (Fin n) K)
      (j : B →+* K) (φ : B →+* k) (χ : Fin n → G →* kˣ), Function.Injective j →
      (∀ g, ∃ p : B[X], p.map j = (r g).charpoly ∧ p.map φ = ∏ i, (X - C (χ i g : k))) →
      ∀ (b : Module.Basis (Fin n) K (Fin n → K)) (π : G →* Equiv.Perm (Fin n)),
      (∀ g i, ∃ a : K, r g *ᵥ b i = a • b (π g i)) → (∀ i j, ∃ g, π g i = j) → ∀ g ∈ π.ker, ∀ s t, χ s g = χ t g := by
  intro K k B G _ _ _ _ _ n r j φ χ hj hchar b π hmon htrans g hg s t
  obtain ⟨C', ρ, hC, hρ, hroot⟩ := exists_subring_hom_algebraicClosure_of_injective B K k j hj φ
  have hcanc : ∀ (i : Fin n) (a a' : K), a • b i = a' • b i → a = a' :=
    fun i a a' h => smul_left_injective K (b.ne_zero i) h
  have hinv : ∀ (x : G) (v : Fin n → K), r x *ᵥ (r x⁻¹ *ᵥ v) = v := by
    intro x v
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  have hdiag : ∀ y ∈ π.ker, ∀ i, ∃ a : K, r y *ᵥ b i = a • b i := by
    intro y hy i
    obtain ⟨a, ha⟩ := hmon y i
    rw [MonoidHom.mem_ker] at hy
    rw [hy, Equiv.Perm.one_apply] at ha
    exact ⟨a, ha⟩
  choose! e he using hdiag
  have hmemC : ∀ y ∈ π.ker, ∀ i, e y i ∈ C' := by
    intro y hy i
    obtain ⟨p, hp1, -⟩ := hchar y
    refine hroot p (Polynomial.monic_of_injective hj (by rw [hp1]; exact Matrix.charpoly_monic _)) _ ?_
    rw [hp1, monomialRed_lemma_2 r b y (e y) (he y hy), Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hms : ∀ y (hy : y ∈ π.ker), (Finset.univ.val.map fun i => ρ ⟨e y i, hmemC y hy i⟩) =
      (Finset.univ.val.map fun s => algebraMap k (AlgebraicClosure k) ((χ s y : kˣ) : k)) := by
    intro y hy
    obtain ⟨p, hp1, hp2⟩ := hchar y
    let j' : B →+* C' := j.codRestrict C' hC
    have hq : p.map j' = ∏ i, (X - C (⟨e y i, hmemC y hy i⟩ : C')) := by
      apply Polynomial.map_injective C'.subtype Subtype.val_injective
      rw [Polynomial.map_map]
      have hcomp : C'.subtype.comp j' = j := RingHom.ext fun _ => rfl
      rw [hcomp, hp1, monomialRed_lemma_2 r b y (e y) (he y hy), Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl
    have hρj : ρ.comp j' = (algebraMap k (AlgebraicClosure k)).comp φ :=
      RingHom.ext fun c => by exact hρ c
    have h1 : (p.map j').map ρ = (p.map φ).map (algebraMap k (AlgebraicClosure k)) := by
      rw [Polynomial.map_map, Polynomial.map_map, hρj]
    rw [hq, hp2, Polynomial.map_prod, Polynomial.map_prod] at h1
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h1
    rw [← roots_prod_X_sub_C_fin_eq_map_univ, ← roots_prod_X_sub_C_fin_eq_map_univ, h1]
  have hg' : g⁻¹ ∈ π.ker := π.ker.inv_mem hg
  have hpair : ∀ l, e g l * e g⁻¹ l = 1 := by
    intro l
    have h := hinv g (b l)
    rw [he g⁻¹ hg' l, Matrix.mulVec_smul, he g hg l, smul_smul] at h
    apply hcanc l
    rw [mul_comm, h, one_smul]
  have hconst : ∀ i l, ρ ⟨e g i, hmemC g hg i⟩ = ρ ⟨e g l, hmemC g hg l⟩ := by
    intro i l
    obtain ⟨h, hlh⟩ := htrans l i
    have hy : g * h * g⁻¹ * h⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker] at hg ⊢
      simp [hg]
    have hli : (π h⁻¹) i = l := by
      rw [map_inv, Equiv.Perm.inv_eq_iff_eq]
      exact hlh.symm
    obtain ⟨c, hc⟩ := hmon h⁻¹ i
    obtain ⟨d, hd⟩ := hmon h l
    rw [hli] at hc
    rw [hlh] at hd
    have hcd : c * d = 1 := by
      have h0 := hinv h (b i)
      rw [hc, Matrix.mulVec_smul, hd, smul_smul] at h0
      apply hcanc i
      rw [h0, one_smul]
    have hey : e (g * h * g⁻¹ * h⁻¹) i = e g i * e g⁻¹ l := by
      apply hcanc i
      rw [← he _ hy i, map_mul, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hc]
      simp only [Matrix.mulVec_smul, he g⁻¹ hg' l, hd, he g hg i, smul_smul]
      congr 1
      linear_combination (e g i * e g⁻¹ l) * hcd
    have hy1 : ρ ⟨e _ i, hmemC _ hy i⟩ = 1 := by
      have hmem : ρ ⟨e _ i, hmemC _ hy i⟩ ∈ (Finset.univ.val.map fun s =>
          algebraMap k (AlgebraicClosure k) ((χ s (g * h * g⁻¹ * h⁻¹) : kˣ) : k)) := by
        rw [← hms _ hy]
        exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
      obtain ⟨s', -, hs'⟩ := Multiset.mem_map.1 hmem
      rw [← hs']
      have h1 : χ s' (g * h * g⁻¹ * h⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [mul_comm (χ s' g) (χ s' h), mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
      rw [h1, Units.val_one, map_one]
    have hprod : ρ ⟨e _ i, hmemC _ hy i⟩ = ρ ⟨e g i, hmemC g hg i⟩ * ρ ⟨e g⁻¹ l, hmemC _ hg' l⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hey
    have hpl : ρ ⟨e g l, hmemC g hg l⟩ * ρ ⟨e g⁻¹ l, hmemC _ hg' l⟩ = 1 := by
      rw [← map_mul, ← map_one ρ]
      congr 1
      exact Subtype.ext (hpair l)
    have hu : ρ ⟨e g⁻¹ l, hmemC _ hg' l⟩ ≠ 0 := right_ne_zero_of_mul_eq_one hpl
    exact mul_right_cancel₀ hu (by rw [← hprod, hy1, hpl])
  have hχ : ∀ s', ∃ i, algebraMap k (AlgebraicClosure k) ((χ s' g : kˣ) : k) =
      ρ ⟨e g i, hmemC g hg i⟩ := by
    intro s'
    have hmem : algebraMap k (AlgebraicClosure k) ((χ s' g : kˣ) : k) ∈
        (Finset.univ.val.map fun i => ρ ⟨e g i, hmemC g hg i⟩) := by
      rw [hms g hg]
      exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val s')
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
    exact ⟨i, hi.symm⟩
  obtain ⟨i1, h1⟩ := hχ s
  obtain ⟨i2, h2⟩ := hχ t
  apply Units.ext
  apply (algebraMap k (AlgebraicClosure k)).injective
  rw [h1, h2, hconst]
