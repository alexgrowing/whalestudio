import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Matrix

namespace GlobalTheory.RealPar

variable {p q n : ℕ}

def BlockOrd (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) : Prop :=
  (∀ i, ε (e (Sum.inl i)) = true) ∧ (∀ j, ε (e (Sum.inr j)) = false) ∧ ∀ a b, posC a b → e a < e b

def Factors {T : GrpData p q} (U : URep T) (e : Ix p q ≃ Fin n)
    (σ : Matrix (Fin n) (Fin n) ℂ → (U.H →L[ℂ] U.H)) : Prop :=
  ∀ x, U.π x = σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))

theorem BlockOrd.sameBlock_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (a b : Ix p q) :
    sameBlock a b ↔ ε (e a) = ε (e b) := by
  obtain ⟨h1, h2, -⟩ := h
  cases a <;> cases b <;> simp [sameBlock, h1, h2]

theorem BlockOrd.posC_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (a b : Ix p q) :
    posC a b ↔ e a < e b ∧ ε (e a) = ε (e b) := by
  constructor
  · intro hab
    refine ⟨h.2.2 a b hab, ?_⟩
    rw [← h.sameBlock_iff]
    cases a <;> cases b <;> simp_all [posC, sameBlock]
  · rintro ⟨hlt, heq⟩
    rw [← h.sameBlock_iff] at heq
    have hne : a ≠ b := fun hab => by subst hab; exact lt_irrefl _ hlt
    have hnot : ¬ posC b a := fun hba => lt_asymm hlt (h.2.2 b a hba)
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        simp only [posC] at hnot ⊢
        rcases lt_trichotomy i j with hij | hij | hij
        · exact hij
        · exact absurd (congrArg Sum.inl hij) hne
        · exact absurd hij hnot
      | inr j => simp [sameBlock] at heq
    | inr i =>
      cases b with
      | inl j => simp [sameBlock] at heq
      | inr j =>
        simp only [posC] at hnot ⊢
        rcases lt_trichotomy i j with hij | hij | hij
        · exact hij
        · exact absurd (congrArg Sum.inr hij) hne
        · exact absurd hij hnot

theorem exists_blockOrd (ε : Fin n → Bool) (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) : ∃ e : Ix p q ≃ Fin n, BlockOrd e ε := by
  classical
  set S := Finset.univ.filter fun a => ε a = true with hS
  set T := Finset.univ.filter fun a => ε a = false with hT
  have hcard : p + q = n := by
    have h0 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun a => ε a = true)
    simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h0
    rw [← hp, ← hq]
    exact h0
  let f : Ix p q → Fin n := fun x =>
    match x with
    | Sum.inl i => S.orderEmbOfFin hp i
    | Sum.inr j => T.orderEmbOfFin hq j
  have fS : ∀ i, ε (f (Sum.inl i)) = true := fun i =>
    (Finset.mem_filter.mp (S.orderEmbOfFin_mem hp i)).2
  have fT : ∀ j, ε (f (Sum.inr j)) = false := fun j =>
    (Finset.mem_filter.mp (T.orderEmbOfFin_mem hq j)).2
  have hinj : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl ((S.orderEmbOfFin hp).injective hxy)
      | inr j =>
        have h1 := fS i
        rw [hxy, fT j] at h1
        exact absurd h1 (by simp)
    | inr i =>
      cases y with
      | inl j =>
        have h1 := fT i
        rw [hxy, fS j] at h1
        exact absurd h1 (by simp)
      | inr j => exact congrArg Sum.inr ((T.orderEmbOfFin hq).injective hxy)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp [hcard]
  refine ⟨Equiv.ofBijective f hbij, ?_, ?_, ?_⟩
  · intro i
    exact fS i
  · intro j
    exact fT j
  · intro a b hab
    simp only [Equiv.ofBijective_apply]
    cases a with
    | inl i =>
      cases b with
      | inl j => exact (S.orderEmbOfFin hp).strictMono hab
      | inr j => exact absurd hab (by simp [posC])
    | inr i =>
      cases b with
      | inl j => exact absurd hab (by simp [posC])
      | inr j => exact (T.orderEmbOfFin hq).strictMono hab

theorem BlockOrd.reindex_Jm {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) :
    Matrix.reindex e e (Jm p q) = Formalism.REAL.Jm ε := by
  obtain ⟨h1, h2, -⟩ := h
  ext a b
  obtain ⟨a', rfl⟩ := e.surjective a
  obtain ⟨b', rfl⟩ := e.surjective b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm,
    Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, Jm, Formalism.UG.Jpq]
  cases a' <;> cases b' <;> simp [h1, h2, Matrix.one_apply] <;> split_ifs <;> simp

theorem BlockOrd.inUJ_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (g : Mat p q) :
    Formalism.REAL.inUJ ε (Matrix.reindex e e g) ↔ gᴴ * Jm p q * g = Jm p q := by
  have key : ∀ M N : Mat p q, Matrix.reindex e e M * Matrix.reindex e e N = Matrix.reindex e e (M * N) := by
    intro M N
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  unfold Formalism.REAL.inUJ
  rw [← h.reindex_Jm, Matrix.conjTranspose_reindex, key, key]
  exact (Matrix.reindex e e).injective.eq_iff

theorem mem_Upq (g : GL (Ix p q) ℂ) : g ∈ Formalism.UG.Upq p q ↔ (g : Mat p q)ᴴ * Jm p q * g = Jm p q := by
  unfold Formalism.UG.Upq Formalism.UG.UJ
  rw [Subgroup.mem_mk]
  show Formalism.UG.cT (starRingEnd ℂ) (g : Mat p q) * Formalism.UG.Jpq p q * (g : Mat p q) = Formalism.UG.Jpq p q ↔ _
  have hc : Formalism.UG.cT (starRingEnd ℂ) (g : Mat p q) = (g : Mat p q)ᴴ := by
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hc]
  rfl

theorem BlockOrd.cov_mem {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) ∈ UJset ε := by
  show Formalism.REAL.inUJ ε _
  exact (h.inUJ_iff _).mpr ((mem_Upq _).mp (T.cov_mem x))

theorem BlockOrd.cov_surj {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ x : T.G, Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = g := by
  have hg' : Formalism.REAL.inUJ ε g := hg
  set g' : Mat p q := (Matrix.reindex e e).symm g
  have hre : Matrix.reindex e e g' = g := (Matrix.reindex e e).apply_symm_apply g
  have hU : g'ᴴ * Jm p q * g' = Jm p q := by
    rw [← h.inUJ_iff, hre]
    exact hg'
  have hJJ : Jm p q * Jm p q = 1 := by
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have hleft : (Jm p q * g'ᴴ * Jm p q) * g' = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g'ᴴ, hU, hJJ]
  have hright : g' * (Jm p q * g'ᴴ * Jm p q) = 1 := mul_eq_one_comm.mp hleft
  let u : GL (Ix p q) ℂ := ⟨g', Jm p q * g'ᴴ * Jm p q, hright, hleft⟩
  have hu : u ∈ Formalism.UG.Upq p q := (mem_Upq u).mpr hU
  have hdet : (u : Mat p q).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det (u : Mat p q)).mp u.isUnit
    exact this.ne_zero
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : Mat p q).det (by norm_num : 0 < 2)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hz]; simp)
  obtain ⟨x, ⟨hx, -⟩, -⟩ := T.bij u hu (Units.mk0 z hz0) (by simpa using hz)
  refine ⟨x, ?_⟩
  rw [hx]
  exact hre

theorem exists_factors {T : GrpData p q} (U : URep T) (e : Ix p q ≃ Fin n)
    (h : ∀ x, T.cov x = 1 → U.π x = 1) : ∃ σ, Factors U e σ := by
  classical
  refine ⟨fun M => if hM : ∃ x, Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = M
    then U.π hM.choose else 0, ?_⟩
  intro x
  have hM : ∃ y, Matrix.reindex e e ((T.cov y : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) := ⟨x, rfl⟩
  simp only [dif_pos hM]
  set y := hM.choose with hy
  have hyx : T.cov y = T.cov x := Units.ext ((Matrix.reindex e e).injective hM.choose_spec)
  have h1 : T.cov (y⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hyx, inv_mul_cancel]
  have h2 : U.π y⁻¹ * U.π x = 1 := by
    rw [← map_mul]
    exact h _ h1
  calc U.π x = U.π (y * y⁻¹) * U.π x := by simp
    _ = U.π y * (U.π y⁻¹ * U.π x) := by rw [map_mul, mul_assoc]
    _ = U.π y := by rw [h2, mul_one]

end GlobalTheory.RealPar

end
