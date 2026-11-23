import Mathlib

noncomputable section

open Matrix Module

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb

universe u

theorem exists_equiv_of_torsion {k A : Type*} [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]
    (I : Ideal A) [I.IsMaximal] (M M' : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M'] [FiniteDimensional k M]
    [FiniteDimensional k M'] (hM : Module.IsTorsionBySet A M I) (hM' : Module.IsTorsionBySet A M' I)
    (h : finrank k M = finrank k M') : Nonempty (M ≃ₗ[A] M') := by
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  letI := hM.module
  letI := hM'.module
  have tw : ∀ (P : Type u) [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
      (hP : Module.IsTorsionBySet A P I), @IsScalarTower k (A ⧸ I) P _ hP.module.toSMul _ := by
    intro P _ _ _ _ hP
    letI := hP.module
    refine ⟨fun c x m => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hP.mk_smul, hP.mk_smul, mul_smul,
      algebraMap_smul]
  haveI := tw M hM
  haveI := tw M' hM'
  haveI : Module.Finite (A ⧸ I) M := Module.Finite.of_restrictScalars_finite k (A ⧸ I) M
  haveI : Module.Finite (A ⧸ I) M' := Module.Finite.of_restrictScalars_finite k (A ⧸ I) M'
  have h1 := Module.finrank_mul_finrank k (A ⧸ I) M
  have h2 := Module.finrank_mul_finrank k (A ⧸ I) M'
  have hpos : 0 < finrank k (A ⧸ I) := Module.finrank_pos
  have hK : finrank (A ⧸ I) M = finrank (A ⧸ I) M' := Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, h2, h])
  let T := LinearEquiv.ofFinrankEq M M' hK
  refine ⟨{ toFun := T
            map_add' := T.map_add
            map_smul' := fun a m => ?_
            invFun := T.symm
            left_inv := T.left_inv
            right_inv := T.right_inv }⟩
  show T (a • m) = a • T m
  rw [← hM.mk_smul, T.map_smul, hM'.mk_smul]

open Classical in

def pidem (A : Type*) [CommRing A] [IsArtinianRing A] [IsReduced A] (I : MaximalSpectrum A) : A :=
  (IsArtinianRing.equivPi A).symm (Pi.single I 1)

section idem
open Classical
variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A]

theorem equivPi_pidem (I J : MaximalSpectrum A) :
    IsArtinianRing.equivPi A (pidem A I) J = Pi.single (M := fun I : MaximalSpectrum A => A ⧸ I.asIdeal) I 1 J := by
  rw [pidem, AlgEquiv.apply_symm_apply]

theorem pidem_mul (I J : MaximalSpectrum A) : pidem A I * pidem A J = if I = J then pidem A I else 0 := by
  apply (IsArtinianRing.equivPi A).injective
  funext L
  split_ifs with h
  · subst h
    rw [map_mul, Pi.mul_apply, equivPi_pidem]
    by_cases hL : L = I
    · subst hL; simp
    · simp [Pi.single_apply, hL]
  · rw [map_mul, Pi.mul_apply, equivPi_pidem, equivPi_pidem, map_zero, Pi.zero_apply]
    by_cases hL : L = I
    · subst hL; simp [Pi.single_apply, Ne.symm h]
    · simp [Pi.single_apply, hL]

theorem pidem_idem (I : MaximalSpectrum A) : IsIdempotentElem (pidem A I) := by
  have h := pidem_mul I I
  rw [if_pos rfl] at h
  exact h

theorem sum_pidem [Fintype (MaximalSpectrum A)] : ∑ I, pidem A I = 1 := by
  apply (IsArtinianRing.equivPi A).injective
  funext L
  rw [map_sum, Finset.sum_apply, map_one, Pi.one_apply]
  simp_rw [equivPi_pidem]
  simp [Pi.single_apply]

theorem mul_pidem_of_mem (I : MaximalSpectrum A) {x : A} (hx : x ∈ I.asIdeal) : x * pidem A I = 0 := by
  apply (IsArtinianRing.equivPi A).injective
  funext L
  rw [map_mul, Pi.mul_apply, equivPi_pidem, map_zero, Pi.zero_apply]
  by_cases hL : L = I
  · subst hL
    rw [IsArtinianRing.equivPi_apply, (Ideal.Quotient.eq_zero_iff_mem).2 hx, zero_mul]
  · simp [Pi.single_apply, hL]

end idem

def piece {A : Type*} (M : Type*) [CommRing A] [AddCommGroup M] [Module A M] (e : A) : Submodule A M :=
  LinearMap.range (LinearMap.lsmul A M e)

section dec
open Classical
variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A] [Fintype (MaximalSpectrum A)]

theorem pidem_smul_piece (P : Type*) [AddCommGroup P] [Module A P] (I J : MaximalSpectrum A) {y : P}
    (hy : y ∈ piece P (pidem A I)) : pidem A J • y = if J = I then y else 0 := by
  obtain ⟨m, rfl⟩ := hy
  rw [LinearMap.lsmul_apply, smul_smul, pidem_mul]
  split_ifs with h
  · subst h; rfl
  · exact zero_smul A m

def decomp (P : Type*) [AddCommGroup P] [Module A P] : P ≃ₗ[A] ∀ I : MaximalSpectrum A, piece P (pidem A I) where
  toFun m I := ⟨pidem A I • m, m, rfl⟩
  map_add' m m' := by funext I; ext; simp [smul_add]
  map_smul' a m := by funext I; ext; simp [smul_comm (pidem A I) a m]
  invFun x := ∑ I, (x I : P)
  left_inv m := by
    simp only
    rw [← Finset.sum_smul, sum_pidem, one_smul]
  right_inv x := by
    funext J
    ext
    simp only [Finset.smul_sum]
    rw [Finset.sum_eq_single J]
    · rw [pidem_smul_piece P J J (x J).2, if_pos rfl]
    · intro I _ hI
      rw [pidem_smul_piece P I J (x I).2, if_neg (Ne.symm hI)]
    · intro h; exact absurd (Finset.mem_univ J) h

end dec

theorem exists_equiv_of_finrank {k A : Type*} [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]
    [IsReduced A] (M M' : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M'] [FiniteDimensional k M]
    [FiniteDimensional k M']
    (h : ∀ e : A, IsIdempotentElem e → finrank k (piece M e) = finrank k (piece M' e)) :
    Nonempty (M ≃ₗ[A] M') := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  have tor : ∀ (P : Type u) [AddCommGroup P] [Module A P] (I : MaximalSpectrum A),
      Module.IsTorsionBySet A (piece P (pidem A I)) I.asIdeal := by
    intro P _ _ I y a
    obtain ⟨y, m, rfl⟩ := y
    ext
    simp [smul_smul, mul_pidem_of_mem I a.2]
  have fd : ∀ (P : Type u) [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
      [FiniteDimensional k P] (e : A), FiniteDimensional k (piece P e) := fun P _ _ _ _ _ e =>
    Module.Finite.of_injective ((piece P e).subtype.restrictScalars k) Subtype.val_injective
  have T : ∀ I : MaximalSpectrum A, Nonempty (piece M (pidem A I) ≃ₗ[A] piece M' (pidem A I)) := fun I =>
    haveI := fd M (pidem A I)
    haveI := fd M' (pidem A I)
    exists_equiv_of_torsion I.asIdeal _ _ (tor M I) (tor M' I) (h _ (pidem_idem I))
  exact ⟨(decomp M).trans ((LinearEquiv.piCongrRight fun I => (T I).some).trans (decomp M').symm)⟩

section rep
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {N : ℕ}

@[nolint unusedArguments]
def Rep (_ρ : A →ₐ[k] Matrix (Fin N) (Fin N) k) : Type _ := Fin N → k

variable (ρ : A →ₐ[k] Matrix (Fin N) (Fin N) k)

instance : AddCommGroup (Rep ρ) := inferInstanceAs (AddCommGroup (Fin N → k))
instance : Module k (Rep ρ) := inferInstanceAs (Module k (Fin N → k))
instance : FiniteDimensional k (Rep ρ) := inferInstanceAs (FiniteDimensional k (Fin N → k))
instance : Module A (Rep ρ) :=
  Module.compHom (Fin N → k) ((Matrix.toLinAlgEquiv' (R := k) (n := Fin N)).toAlgHom.comp ρ).toRingHom

theorem rep_smul (a : A) (v : Rep ρ) : a • v = (ρ a *ᵥ (v : Fin N → k) : Fin N → k) := rfl

instance : IsScalarTower k A (Rep ρ) := ⟨fun c a v => by
  rw [rep_smul, rep_smul, map_smul]
  exact Matrix.smul_mulVec _ _ _⟩

theorem finrank_piece_rep (e : A) : finrank k (piece (Rep ρ) e) = (ρ e).rank := by
  have hs : ((piece (Rep ρ) e).restrictScalars k : Submodule k (Fin N → k)) =
      LinearMap.range (ρ e).mulVecLin := by
    ext v
    simp only [Submodule.restrictScalars_mem, piece, LinearMap.mem_range, LinearMap.lsmul_apply,
      Matrix.mulVecLin_apply]
    rfl
  rw [Matrix.rank, ← hs]
  rfl

end rep

theorem orbHom_gen (k : Type*) [Field k] (N : ℕ) (A : Type*) [CommRing A] [Algebra k A] [FiniteDimensional k A]
    (hA : IsReduced A) (ρ ρ' : A →ₐ[k] Matrix (Fin N) (Fin N) k)
    (h : ∀ e : A, IsIdempotentElem e → (ρ e).rank = (ρ' e).rank) :
    ∃ g : GL (Fin N) k, ∀ a, ρ' a = g.val * ρ a * g⁻¹.val := by
  obtain ⟨F⟩ := exists_equiv_of_finrank (k := k) (A := A) (Rep ρ) (Rep ρ') fun e he => by
    rw [finrank_piece_rep, finrank_piece_rep, h e he]
  let f : (Fin N → k) ≃ₗ[k] (Fin N → k) := F.restrictScalars k
  have hf : ∀ a v, f (ρ a *ᵥ v) = ρ' a *ᵥ f v := fun a v => F.map_smul a v
  let g : GL (Fin N) k := ⟨LinearMap.toMatrix' f.toLinearMap, LinearMap.toMatrix' f.symm.toLinearMap, by
      rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]; congr 1; ext v; simp, by
      rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]; congr 1; ext v; simp⟩
  refine ⟨g, fun a => ?_⟩
  have hc : ρ' a * g.val = g.val * ρ a := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
    show Matrix.toLin' (ρ' a) ∘ₗ Matrix.toLin' (LinearMap.toMatrix' f.toLinearMap) =
      Matrix.toLin' (LinearMap.toMatrix' f.toLinearMap) ∘ₗ Matrix.toLin' (ρ a)
    rw [Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact (hf a v).symm
  calc ρ' a = ρ' a * (g.val * g⁻¹.val) := by rw [Units.mul_inv, mul_one]
    _ = g.val * ρ a * g⁻¹.val := by rw [← mul_assoc, hc]

end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
