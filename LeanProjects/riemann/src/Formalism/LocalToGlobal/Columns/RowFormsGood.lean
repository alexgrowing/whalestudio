import Mathlib
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section CM

variable {X : Fields}

theorem rf_emb_mem_cmMax (hX : X.Ok) (τ : X.Tau) (x : X.E) : X.emb τ x ∈ cmMax X.K := by
  intro σ
  rw [← hX.emb_star]
  exact hX.conjE (σ.comp (X.emb τ)) x

theorem rf_root_mem_cmMax (hX : X.Ok) {c : X.K} {m : ℕ} (hm : 0 < m) (hc : c ^ m = 1) : c ∈ cmMax X.K := by
  intro σ
  have h1 : star c = c⁻¹ := eq_inv_of_mul_eq_one_left (star_mul_root hX.conjK hm hc)
  rw [h1, map_inv₀]
  have h2 : (σ c) ^ m = 1 := by rw [← map_pow, hc, map_one]
  exact Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h2 hm.ne')

end CM

section Pk

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

structure CoefPk.RatP {D : Type} (C : CoefPk X n D) : Prop where
  pair_rat : ∀ i j, C.pair (C.bV i) (C.bV j) ∈ cmMax X.K
  act_rat : ∀ (γ : UF X.E n) i j, C.bV.repr (C.rho γ (C.bV j)) i ∈ cmMax X.K
  pos : ∀ v : InfinitePlace X.K, (Matrix.of fun i j => v.embedding (C.pair (C.bV i) (C.bV j))).PosDef

structure CoefPk.DualP {D : Type} (C : CoefPk X n D) : Prop where
  symm : C.pair.IsSymm
  nondeg : C.pair.Nondegenerate
  nab_lat : ∀ d, Submodule.IsLattice X.K (C.Nab d)
  del_le : ∀ d, C.Del d ≤ C.Nab d
  dual : ∀ d, Formalism.HermitianLatticesTheory.dual C.pair (C.Nab d) = C.Del d

theorem formGSD_rat (hX : X.Ok) (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG) (hC : C.RatP) :
    (formGSD C Λ).Rat where
  pair_rat := hC.pair_rat
  act_rat g i j := by
    show C.bV.repr (((Λ.chr g.2 : X.Kˣ) : X.K) • C.rho g.1 (C.bV j)) i ∈ cmMax X.K
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    obtain ⟨m, hm, hc⟩ := LevFam.chr_root Λ g.2
    exact mul_mem (rf_root_mem_cmMax hX hm hc) (hC.act_rat g.1 i j)
  pos := hC.pos

theorem formGSD_good (hX : X.Ok) (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG) (hE : C.Eqv)
    (hC : C.DualP) : (formGSD C Λ).Good 1 where
  ok := formGSD_ok C Λ hX hE
  symm := hC.symm
  nondeg := hC.nondeg
  nab_lat := hC.nab_lat
  del_le := hC.del_le
  s_pos := Nat.one_pos
  dual_le d y hy := by
    rw [Nat.cast_one, one_smul]
    have : y ∈ Formalism.HermitianLatticesTheory.dual C.pair (C.Nab d) := hy
    rw [hC.dual d] at this
    exact this
  del_dual d y hy := by
    rw [Nat.cast_one, one_smul]
    show y ∈ Formalism.HermitianLatticesTheory.dual C.pair (C.Nab d)
    rw [hC.dual d]
    exact hy

end Pk

section Brackets

variable {X : Fields} {n : ℕ} (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n))

theorem rf_gramK_one (τ : X.Tau) : gramK X.emb (1 : Matrix (Fin n) (Fin n) X.E) τ = 1 := by
  unfold gramK
  rw [Matrix.map_one _ (map_zero _) (map_one _)]

theorem rf_gramKd_one (τ : X.Tau) : gramKd X.emb (1 : Matrix (Fin n) (Fin n) X.E) τ = 1 := by
  unfold gramKd
  rw [Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]

theorem rf_one_entry_mem (K0 : Subfield X.K) (a b : Fin n) : (1 : Matrix (Fin n) (Fin n) X.K) a b ∈ K0 := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem rf_one_map_posDef (φ : X.K →+* ℂ) : ((1 : Matrix (Fin n) (Fin n) X.K).map φ).PosDef := by
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.PosDef.one

theorem squarePk_ratP (hX : X.Ok) : (squarePk X lam L).RatP where
  pair_rat i j := pairRat X.K X.Tau n lam (cmMax X.K) _ (fun τ a b => by rw [rf_gramK_one]; exact rf_one_entry_mem _ a b) i j
  act_rat γ i j := actRat X.K X.Tau n lam (cmMax X.K) _ (fun τ a b => by
    rw [embGL_coe]
    exact rf_emb_mem_cmMax hX τ _) i j
  pos v := pairPos X.K X.Tau n lam _ v.embedding fun τ => by rw [rf_gramK_one]; exact rf_one_map_posDef _

theorem roundPk_ratP (hX : X.Ok) : (roundPk X lam L).RatP where
  pair_rat i j := pairRat X.K X.Tau n lam (cmMax X.K) _ (fun τ a b => by rw [rf_gramKd_one]; exact rf_one_entry_mem _ a b) i j
  act_rat γ i j := actRat X.K X.Tau n lam (cmMax X.K) _ (fun τ a b => by
    show ((invTrK (embGL X.emb (ufGL X.E n γ)) τ : GL (Fin n) X.K) : Matrix (Fin n) (Fin n) X.K) a b ∈ cmMax X.K
    rw [invTrK_coe, embGL_inv, embGL_coe]
    exact rf_emb_mem_cmMax hX τ _) i j
  pos v := pairPos X.K X.Tau n lam _ v.embedding fun τ => by rw [rf_gramKd_one]; exact rf_one_map_posDef _

theorem rf_hform_one (x y : Sp X.E n) : Formalism.UG.hform (starRingEnd X.E) (1 : Matrix (Fin n) (Fin n) X.E) x y = hStd X.E n x y := by
  unfold Formalism.UG.hform
  rw [hStd_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, mul_one]
    rfl
  · intro j _ hj
    rw [Matrix.one_apply_ne hj.symm, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem rf_hdualFr_tauLat (hX : X.Ok) {N : Submodule (𝓞 X.E) (Sp X.E n)} (hl : Submodule.IsLattice X.E N)
    (hu : IsUnimodular (hStd X.E n) N) (τ : X.Tau) :
    hdualFr (1 : Matrix (Fin n) (Fin n) X.K) (tauLat X.emb τ N) = tauLat X.emb τ N := by
  have h := tauLatDual X.E X.K X.Tau n X.emb (starRingEnd X.E) τ (fun x => (hX.emb_star τ x).symm) 1 N N
    (by rw [Matrix.det_one]; exact isUnit_one) hl (fun y => by
      have hu' : dual (hStd X.E n) N = N := hu
      conv_lhs => rw [← hu', mem_dual]
      refine forall₂_congr fun x _ => ?_
      rw [rf_hform_one, Submodule.mem_one]
      rfl)
  rw [rf_gramK_one] at h
  exact h

theorem squarePk_dualP (hX : X.Ok) (hl : ∀ d, Submodule.IsLattice X.E (L d))
    (hu : ∀ d, IsUnimodular (hStd X.E n) (L d)) : (squarePk X lam L).DualP where
  symm := pairSymm X.K X.Tau n lam _ fun τ => by rw [rf_gramK_one, Matrix.conjTranspose_one]
  nondeg := pairNondeg X.K X.Tau n lam _ fun τ => by rw [rf_gramK_one, Matrix.det_one]; exact isUnit_one
  nab_lat d := (nabDelLattice X.K X.Tau n lam _ fun τ => tauLatLattice X.E X.K X.Tau n X.emb τ _ (hl d)).1
  del_le := squarePk_del_le X lam L
  dual d := by
    have h := (nabDelDual X.K X.Tau n lam (gramK X.emb 1) (fun τ => tauLat X.emb τ (L d))
      (fun τ => by rw [rf_gramK_one, Matrix.conjTranspose_one])
      (fun τ => by rw [rf_gramK_one, Matrix.det_one]; exact isUnit_one)
      (fun τ => tauLatLattice X.E X.K X.Tau n X.emb τ _ (hl d))).1
    show Formalism.HermitianLatticesTheory.dual (pairK lam (gramK X.emb 1)) (nabK lam fun τ => tauLat X.emb τ (L d)) =
      delK lam fun τ => tauLat X.emb τ (L d)
    rw [h]
    congr 1
    funext τ
    rw [rf_gramK_one, rf_hdualFr_tauLat hX (hl d) (hu d)]

theorem roundPk_dualP (hX : X.Ok) (hl : ∀ d, Submodule.IsLattice X.E (L d))
    (hu : ∀ d, IsUnimodular (hStd X.E n) (L d)) : (roundPk X lam L).DualP where
  symm := pairSymm X.K X.Tau n lam _ fun τ => by rw [rf_gramKd_one, Matrix.conjTranspose_one]
  nondeg := pairNondeg X.K X.Tau n lam _ fun τ => by rw [rf_gramKd_one, Matrix.det_one]; exact isUnit_one
  nab_lat d := (nabDelLattice X.K X.Tau n lam _ fun τ =>
    (dualFrLattice X.K n 1 _ (by rw [Matrix.det_one]; exact isUnit_one)
      (tauLatLattice X.E X.K X.Tau n X.emb τ _ (hl d))).1).1
  del_le := roundPk_del_le X lam L
  dual d := by
    have hlat : ∀ τ, Submodule.IsLattice X.K (dualFr (tauLat X.emb τ (L d))) := fun τ =>
      (dualFrLattice X.K n 1 _ (by rw [Matrix.det_one]; exact isUnit_one)
        (tauLatLattice X.E X.K X.Tau n X.emb τ _ (hl d))).1
    have h := (nabDelDual X.K X.Tau n lam (gramKd X.emb 1) (fun τ => dualFr (tauLat X.emb τ (L d)))
      (fun τ => by rw [rf_gramKd_one, Matrix.conjTranspose_one])
      (fun τ => by rw [rf_gramKd_one, Matrix.det_one]; exact isUnit_one) hlat).1
    show Formalism.HermitianLatticesTheory.dual (pairK lam (gramKd X.emb 1)) (nabK lam fun τ => dualFr (tauLat X.emb τ (L d))) =
      delK lam fun τ => dualFr (tauLat X.emb τ (L d))
    rw [h]
    congr 1
    funext τ
    have h2 := dualFrHdual X.K n (1 : Matrix (Fin n) (Fin n) X.K) (tauLat X.emb τ (L d)) Matrix.conjTranspose_one
      (by rw [Matrix.det_one]; exact isUnit_one) (tauLatLattice X.E X.K X.Tau n X.emb τ _ (hl d))
    rw [inv_one, Matrix.transpose_one, rf_hdualFr_tauLat hX (hl d) (hu d)] at h2
    rw [rf_gramKd_one, h2]

end Brackets

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem rowVal_ratP (hX : X.Ok) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) : (rowVal W SG).RatP :=
  squarePk_ratP _ _ hX

theorem mtVal_ratP (hX : X.Ok) (j : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) : (mtVal W j SG).RatP :=
  roundPk_ratP _ _ hX

theorem rowVal_dualP (hX : X.Ok) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) : (rowVal W SG).DualP :=
  squarePk_dualP _ _ hX (fun d => d.2.lat) fun d => d.2.uni

theorem mtVal_dualP (hX : X.Ok) (j : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) : (mtVal W j SG).DualP :=
  roundPk_dualP _ _ hX (fun d => d.2.lat) fun d => d.2.uni

theorem mtilde_good (hX : X.Ok) (P : LevFam X.E X.K R.r Pr.vGs) : (mtildeGSD W Ch sel mu P).Good 1 :=
  formGSD_good hX _ _ (rowVal_eqv W hX _) (rowVal_dualP W hX _)

theorem mtildeK_good (hX : X.Ok) : (mtildeKGSD W Ch sel mu).Good 1 :=
  formGSD_good hX _ _ (rowVal_eqv W hX _) (rowVal_dualP W hX _)

theorem mt_good (hX : X.Ok) (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) : (mtGSD W Ch sel mu P j).Good 1 :=
  formGSD_good hX _ _ (mtVal_eqv W hX j _) (mtVal_dualP W hX j _)

theorem mtK_good (hX : X.Ok) (j : ℕ) : (mtKGSD W Ch sel mu j).Good 1 :=
  formGSD_good hX _ _ (mtVal_eqv W hX j _) (mtVal_dualP W hX j _)

theorem mtilde_rat (hX : X.Ok) (P : LevFam X.E X.K R.r Pr.vGs) : (mtildeGSD W Ch sel mu P).Rat :=
  formGSD_rat hX _ _ (rowVal_ratP W hX _)

theorem mtildeK_rat (hX : X.Ok) : (mtildeKGSD W Ch sel mu).Rat := formGSD_rat hX _ _ (rowVal_ratP W hX _)

theorem mt_rat (hX : X.Ok) (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) : (mtGSD W Ch sel mu P j).Rat :=
  formGSD_rat hX _ _ (mtVal_ratP W hX j _)

theorem mtK_rat (hX : X.Ok) (j : ℕ) : (mtKGSD W Ch sel mu j).Rat := formGSD_rat hX _ _ (mtVal_ratP W hX j _)

theorem MtildeCSD_good (hX : X.Ok) (P : LevFam X.E X.K R.r Pr.vGs) (h : (mtildeGSD W Ch sel mu P).Ok) :
    (MtildeCSD W Ch sel mu P h).Good 1 := (mtildeGSD W Ch sel mu P).toCSDOf_good (mtilde_good W Ch sel mu hX P) _

theorem MtildeKCSD_good (hX : X.Ok) (h : (mtildeKGSD W Ch sel mu).Ok) : (MtildeKCSD W Ch sel mu h).Good 1 :=
  (mtildeKGSD W Ch sel mu).toCSDOf_good (mtildeK_good W Ch sel mu hX) _

theorem MtCSD_good (hX : X.Ok) (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) (h : (mtGSD W Ch sel mu P j).Ok) :
    (MtCSD W Ch sel mu P j h).Good 1 := (mtGSD W Ch sel mu P j).toCSDOf_good (mt_good W Ch sel mu hX P j) _

theorem MtKCSD_good (hX : X.Ok) (j : ℕ) (h : (mtKGSD W Ch sel mu j).Ok) : (MtKCSD W Ch sel mu j h).Good 1 :=
  (mtKGSD W Ch sel mu j).toCSDOf_good (mtK_good W Ch sel mu hX j) _

theorem MtildeCSD_rat (hX : X.Ok) (P : LevFam X.E X.K R.r Pr.vGs) (h : (mtildeGSD W Ch sel mu P).Ok) :
    (MtildeCSD W Ch sel mu P h).Rat := (mtildeGSD W Ch sel mu P).toCSDOf_rat h (mtilde_rat W Ch sel mu hX P) _

theorem MtildeKCSD_rat (hX : X.Ok) (h : (mtildeKGSD W Ch sel mu).Ok) : (MtildeKCSD W Ch sel mu h).Rat :=
  (mtildeKGSD W Ch sel mu).toCSDOf_rat h (mtildeK_rat W Ch sel mu hX) _

theorem MtCSD_rat (hX : X.Ok) (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) (h : (mtGSD W Ch sel mu P j).Ok) :
    (MtCSD W Ch sel mu P j h).Rat := (mtGSD W Ch sel mu P j).toCSDOf_rat h (mt_rat W Ch sel mu hX P j) _

theorem MtKCSD_rat (hX : X.Ok) (j : ℕ) (h : (mtKGSD W Ch sel mu j).Ok) : (MtKCSD W Ch sel mu j h).Rat :=
  (mtKGSD W Ch sel mu j).toCSDOf_rat h (mtK_rat W Ch sel mu hX j) _

end Rows

end Formalism.L2.Col
