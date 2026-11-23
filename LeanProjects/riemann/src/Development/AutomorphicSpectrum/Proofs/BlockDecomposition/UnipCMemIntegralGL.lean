import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

set_option maxSynthPendingDepth 1

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeStable

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

local instance fintypeResidueStable : Fintype 𝓀[F] := Fintype.ofFinite _

theorem finsum_cosets {W : Type} [AddCommGroup W] [Module ℂ W] (Φ : GL (Fin n) F → W)
    (hΦ : ∀ g, ∀ k ∈ integralGL F n, Φ (g * k) = Φ g) (r : ℕ) :
    ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
        (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • Φ c.out =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∑ c : Pairs S → 𝓀[F], Φ (gMat S c) := by
  classical
  let D : Finset (Σ S : Finset (Fin n), Pairs S → 𝓀[F]) :=
    ((Finset.univ : Finset (Fin n)).powersetCard r).sigma fun _ => Finset.univ
  let e : (Σ S : Finset (Fin n), Pairs S → 𝓀[F]) → GL (Fin n) F ⧸ integralGL F n :=
    fun x => ((gMat x.1 x.2 : GL (Fin n) F) : GL (Fin n) F ⧸ integralGL F n)
  have hinj : Set.InjOn e D := by
    rintro ⟨S, c⟩ _ ⟨S', c'⟩ _ h
    have hq : ((gMat S c : GL (Fin n) F) : GL (Fin n) F ⧸ integralGL F n) = (gMat S' c' : GL (Fin n) F) := h
    rw [QuotientGroup.eq] at hq
    have hS : S = S' := by
      have h1 := GroundTheory.Automorphic.Iwasawa.iwasawaExponent_mul_of_mem_integralGL F n (gMat S c) hq
      rw [mul_inv_cancel_left, GroundTheory.Automorphic.Spherical.iwasawaExponent_gMat,
        GroundTheory.Automorphic.Spherical.iwasawaExponent_gMat] at h1
      ext i
      have h2 := congrFun h1 i
      simp only [lamS] at h2
      split_ifs at h2 <;> simp_all
    subst hS
    have hc : c = c' := GroundTheory.Automorphic.Spherical.gMat_injective S h
    subst hc
    rfl
  have hsupp : (Function.support fun q : GL (Fin n) F ⧸ integralGL F n =>
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) q.out • Φ q.out) ⊆ (D.image e : Set _) := by
    intro q hq
    rw [Function.mem_support] at hq
    have hmem : q.out ∈ minusculeSet F n r := by
      by_contra hn
      apply hq
      rw [Set.indicator_of_notMem hn, zero_smul]
    obtain ⟨S, hS, c, hc⟩ := GroundTheory.Automorphic.Spherical.exists_gMat hmem
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨S, c⟩, ?_, ?_⟩)
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, Finset.mem_univ _⟩
    · show ((gMat S c : GL (Fin n) F) : GL (Fin n) F ⧸ integralGL F n) = q
      rw [hc, QuotientGroup.out_eq']
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro c _
  have hSc : S.card = r := (Finset.mem_powersetCard.mp hS).2
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) (gMat S c)
  have hmem : gMat S c * (k : GL (Fin n) F) ∈ minusculeSet F n r := by
    have := GroundTheory.Automorphic.Spherical.mul_mem_minusculeSet
      (GroundTheory.Automorphic.Spherical.gMat_mem_minusculeSet S c) (one_mem (integralGL F n)) k.2
    rwa [one_mul, hSc] at this
  show (minusculeSet F n r).indicator (fun _ => (1 : ℂ))
      (((gMat S c : GL (Fin n) F) : GL (Fin n) F ⧸ integralGL F n).out) •
      Φ (((gMat S c : GL (Fin n) F) : GL (Fin n) F ⧸ integralGL F n).out) = Φ (gMat S c)
  rw [hk, Set.indicator_of_mem hmem, one_smul, hΦ _ _ k.2]

theorem unipC_mem_integralGL (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) :
    unipC S c ∈ integralGL F n := by
  apply GroundTheory.Automorphic.Spherical.mem_integralGL_of_forall_mem
  · intro i j
    rw [GroundTheory.Automorphic.Spherical.coe_unipC, Matrix.add_apply]
    refine add_mem ?_ (GroundTheory.Automorphic.Spherical.cMat_mem c i j)
    by_cases h : i = j
    · subst h; rw [Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne h]; exact zero_mem _
  · have hdet : (↑(unipC (F := F) S c) : Matrix (Fin n) (Fin n) F).det = 1 := by
      rw [GroundTheory.Automorphic.Spherical.coe_unipC, Matrix.det_of_upperTriangular]
      · apply Finset.prod_eq_one
        intro i _
        rw [Matrix.add_apply, Matrix.one_apply_eq,
          GroundTheory.Automorphic.Spherical.cMat_apply_of_not c (by simp), add_zero]
      · intro i j hij
        have hij' : j < i := hij
        have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij'
        show (1 : Matrix (Fin n) (Fin n) F) i j + cMat S c i j = 0
        rw [Matrix.one_apply_ne hne,
          GroundTheory.Automorphic.Spherical.cMat_apply_of_not (i := i) (j := j) c (by
            rintro ⟨-, -, h⟩; exact absurd h (not_lt.mpr hij'.le)), add_zero]
    rw [hdet, map_one]

def revCompl (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => Fin.rev i ∉ S

theorem mem_revCompl {S : Finset (Fin n)} {i : Fin n} : i ∈ revCompl S ↔ Fin.rev i ∉ S := by
  simp [revCompl]

theorem revCompl_revCompl (S : Finset (Fin n)) : revCompl (revCompl S) = S := by
  ext i
  rw [mem_revCompl, mem_revCompl, Fin.rev_rev, not_not]

theorem card_revCompl (S : Finset (Fin n)) : (revCompl S).card = n - S.card := by
  have h : revCompl S = (S.map Fin.revPerm.toEmbedding)ᶜ := by
    ext i
    rw [mem_revCompl, Finset.mem_compl, Finset.mem_map_equiv, Fin.revPerm_symm, Fin.revPerm_apply]
  rw [h, Finset.card_compl, Finset.card_map, Fintype.card_fin]

theorem card_pairs_le (S : Finset (Fin n)) :
    Fintype.card (Pairs S) ≤ Fintype.card (Pairs (revCompl S)) := by
  let f : Pairs S → Pairs (revCompl S) := fun p =>
    let q : {p : Fin n × Fin n // p.1 ∈ S ∧ p.2 ∉ S ∧ p.1 < p.2} := p
    (⟨(Fin.rev q.1.2, Fin.rev q.1.1), by
      obtain ⟨h1, h2, h3⟩ := q.2
      refine ⟨?_, ?_, ?_⟩
      · show Fin.rev q.1.2 ∈ revCompl S
        rw [mem_revCompl, Fin.rev_rev]; exact h2
      · show Fin.rev q.1.1 ∉ revCompl S
        rw [mem_revCompl, Fin.rev_rev, not_not]; exact h1
      · show Fin.rev q.1.2 < Fin.rev q.1.1
        exact Fin.rev_lt_rev.mpr h3⟩ :
      {p : Fin n × Fin n // p.1 ∈ revCompl S ∧ p.2 ∉ revCompl S ∧ p.1 < p.2})
  refine Fintype.card_le_of_injective f ?_
  intro p p' h
  have h' := congrArg (fun x : Pairs (revCompl S) =>
    (x : {p : Fin n × Fin n // p.1 ∈ revCompl S ∧ p.2 ∉ revCompl S ∧ p.1 < p.2}).1) h
  simp only [f, Prod.mk.injEq, Fin.rev_inj] at h'
  exact Subtype.ext (Prod.ext h'.2 h'.1)

theorem kappa_revCompl (S : Finset (Fin n)) : kappa F (revCompl S) = kappa F S := by
  have h1 := card_pairs_le S
  have h2 := card_pairs_le (revCompl S)
  rw [revCompl_revCompl] at h2
  have hc : Fintype.card (Pairs (revCompl S)) = Fintype.card (Pairs S) := le_antisymm h2 h1
  unfold kappa
  exact (Nat.card_congr ((Fintype.equivOfCardEq hc).arrowCongr (Equiv.refl _)))

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) F) V}
  {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {v : V}

theorem coeff_mul_mul (hU : Unit' ρ B) (hv : ∀ g ∈ integralGL F n, ρ g v = v)
    {a b : GL (Fin n) F} (ha : a ∈ integralGL F n) (hb : b ∈ integralGL F n) (g : GL (Fin n) F) :
    B v (ρ (a * g * b) v) = B v (ρ g v) := by
  have ha' : ρ a v = v := hv a ha
  have hb' : ρ b v = v := hv b hb
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb']
  calc B v (ρ a (ρ g v)) = B (ρ a v) (ρ a (ρ g v)) := by rw [ha']
    _ = B v (ρ g v) := hU.2.2 a v (ρ g v)

theorem coeff_gMat (hU : Unit' ρ B) (hv : ∀ g ∈ integralGL F n, ρ g v = v) (S : Finset (Fin n))
    (c : Pairs S → 𝓀[F]) :
    B v (ρ (gMat S c) v) = B v (ρ (torusPow F n (lamS S)) v) := by
  have h := coeff_mul_mul hU hv (unipC_mem_integralGL S c) (one_mem _) (torusPow F n (lamS S))
  rw [mul_one] at h
  exact h

theorem coeff_revCompl (hU : Unit' ρ B) (hv : ∀ g ∈ integralGL F n, ρ g v = v)
    (S : Finset (Fin n)) :
    B v (ρ (torusPow F n (lamS (revCompl S))) v) = B v (ρ (torusPow F n (lamS Sᶜ)) v) := by
  let P : Matrix (Fin n) (Fin n) F := (Fin.revPerm : Equiv.Perm (Fin n)).toPEquiv.toMatrix
  have hPP : P * P = 1 := by
    simp only [P]
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    have hrr : (Fin.revPerm : Equiv.Perm (Fin n)).trans Fin.revPerm = Equiv.refl _ := by
      ext i
      simp
    rw [hrr, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let w : GL (Fin n) F := ⟨P, P, hPP, hPP⟩
  have hw : w ∈ integralGL F n := by
    apply GroundTheory.Automorphic.Spherical.mem_integralGL_of_forall_mem
    · intro i j
      show P i j ∈ _
      simp only [P, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · show (ValuativeRel.valuation F) P.det = 1
      have hdet : P.det = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : F) :=
        Matrix.det_permutation _
      rw [hdet]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;>
        simp [h]
  have hconj : torusPow F n (lamS (revCompl S)) = w * torusPow F n (lamS Sᶜ) * w⁻¹ := by
    ext i j
    rw [Units.val_mul, Units.val_mul, GroundTheory.Automorphic.Iwasawa.coe_torusPow,
      GroundTheory.Automorphic.Iwasawa.coe_torusPow]
    show (Matrix.diagonal _ : Matrix (Fin n) (Fin n) F) i j = (P * Matrix.diagonal _ * P : Matrix (Fin n) (Fin n) F) i j
    rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
    simp only [Matrix.diagonal_apply, Fin.revPerm_symm, Fin.revPerm_apply, Fin.rev_inj, lamS,
      mem_revCompl, Finset.mem_compl]
    all_goals simp [Matrix.submatrix_apply, Matrix.diagonal_apply, Fin.rev_inj]
  rw [hconj, coeff_mul_mul hU hv hw (inv_mem hw)]

theorem sum_eig {z : Fin n → ℂˣ} (hH : Heig ρ v z) {r : ℕ} (hr : r ≤ n) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∑ c : Pairs S → 𝓀[F], ρ (gMat S c) v =
      (sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r)) • v := by
  exact (finsum_cosets (fun g => ρ g v)
    (fun g k hk => by rw [map_mul, Module.End.mul_apply, hH.1 k hk]) r).symm.trans (hH.2 r hr)

theorem rho_central {z : Fin n → ℂˣ} (hH : Heig ρ v z) :
    ρ (torusPow F n (lamS (Finset.univ : Finset (Fin n)))) v = evalAt z (esymmL n n) • v := by
  have h := sum_eig hH (le_refl n)
  have hS : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    have := Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    rwa [Finset.card_univ, Fintype.card_fin] at this
  rw [hS, Finset.sum_singleton, Nat.sub_self, mul_zero, pow_zero, one_mul] at h
  haveI hempty : IsEmpty (Pairs (Finset.univ : Finset (Fin n))) :=
    ⟨fun p => (show {p : Fin n × Fin n // p.1 ∈ (Finset.univ : Finset (Fin n)) ∧
      p.2 ∉ (Finset.univ : Finset (Fin n)) ∧ p.1 < p.2} from p).2.2.1 (Finset.mem_univ _)⟩
  have hone : ∀ c : Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F],
      gMat Finset.univ c = torusPow F n (lamS Finset.univ) := by
    intro c
    have hu : unipC (F := F) Finset.univ c = 1 := by
      ext i j
      rw [GroundTheory.Automorphic.Spherical.coe_unipC, Matrix.add_apply,
        GroundTheory.Automorphic.Spherical.cMat_apply_of_not c (by simp), add_zero, Units.val_one]
    show unipC Finset.univ c * torusPow F n (lamS Finset.univ) = _
    rw [hu, one_mul]
  simp only [hone, Finset.sum_const, Finset.card_univ] at h
  have hcard : Fintype.card (Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]) = 1 := by
    rw [Fintype.card_fun, Fintype.card_eq_zero (α := Pairs (Finset.univ : Finset (Fin n))), pow_zero]
  rw [hcard, one_smul] at h
  exact h

theorem lamS_compl (S : Finset (Fin n)) :
    lamS Sᶜ = -lamS S + lamS (Finset.univ : Finset (Fin n)) := by
  funext i
  simp only [lamS, Pi.add_apply, Pi.neg_apply, Finset.mem_compl, Finset.mem_univ, if_true]
  split_ifs <;> norm_num

theorem coeff_compl {z : Fin n → ℂˣ} (hU : Unit' ρ B) (hH : Heig ρ v z) (S : Finset (Fin n)) :
    B v (ρ (torusPow F n (lamS Sᶜ)) v) =
      evalAt z (esymmL n n) * starRingEnd ℂ (B v (ρ (torusPow F n (lamS S)) v)) := by
  have hmul : ∀ l₁ l₂ : Fin n → ℤ, torusPow F n (l₁ + l₂) = torusPow F n l₁ * torusPow F n l₂ := by
    intro l₁ l₂
    unfold torusPow
    rw [← map_mul]
    congr 1
    funext i
    simp [_root_.zpow_add]
  have hc := rho_central hH
  have hinv : ρ (torusPow F n (lamS S)) (ρ (torusPow F n (lamS S))⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [lamS_compl, hmul, GroundTheory.Automorphic.Iwasawa.torusPow_neg, map_mul, Module.End.mul_apply, hc,
    map_smul, map_smul, smul_eq_mul, hU.1 v]
  congr 1
  calc B v (ρ (torusPow F n (lamS S))⁻¹ v)
      = B (ρ (torusPow F n (lamS S)) v)
          (ρ (torusPow F n (lamS S)) (ρ (torusPow F n (lamS S))⁻¹ v)) :=
        (hU.2.2 _ v _).symm
    _ = B (ρ (torusPow F n (lamS S)) v) v := by rw [hinv]

theorem sum_kappa {z : Fin n → ℂˣ} (hU : Unit' ρ B) (hH : Heig ρ v z) {r : ℕ} (hr : r ≤ n) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        (kappa F S : ℂ) * B v (ρ (torusPow F n (lamS S)) v) =
      sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * B v v := by
  have h := congrArg (B v) (sum_eig hH hr)
  rw [map_sum, map_smul, smul_eq_mul] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro S _
  rw [map_sum]
  simp only [coeff_gMat hU hH.1]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  unfold kappa
  rw [Nat.card_eq_fintype_card]

theorem conj_sqrtQ_pow (k : ℕ) : starRingEnd ℂ (sqrtQ F ^ k) = sqrtQ F ^ k := by
  rw [map_pow]
  congr 1
  unfold sqrtQ
  exact Complex.conj_ofReal _

end GlobalTheory.CompanionTheory.SatakeStable

open GlobalTheory.CompanionTheory.SatakeStable in

theorem GlobalTheory.CompanionTheory.SatakeStable.l11 : liftZP_unit := by
  unfold liftZP_unit
  intro F _ _ _ _ n V _ _ ρ B hU v z hv0 hH r hr
  have hA := sum_kappa hU hH hr
  have hB := sum_kappa hU hH (Nat.sub_le n r)
  have hsum : ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      (kappa F S : ℂ) * (evalAt z (esymmL n n) * starRingEnd ℂ (B v (ρ (torusPow F n (lamS S)) v))) =
      sqrtQ F ^ ((n - r) * (n - (n - r))) * evalAt z (esymmL n (n - r)) * B v v := by
    rw [← hB]
    refine Finset.sum_nbij' revCompl revCompl ?_ ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_powersetCard] at hS ⊢
      exact ⟨Finset.subset_univ _, by rw [card_revCompl, hS.2]⟩
    · intro T hT
      rw [Finset.mem_powersetCard] at hT ⊢
      exact ⟨Finset.subset_univ _, by rw [card_revCompl, hT.2, Nat.sub_sub_self hr]⟩
    · intro S _
      exact revCompl_revCompl S
    · intro T _
      exact revCompl_revCompl T
    · intro S _
      rw [kappa_revCompl, coeff_revCompl hU hH.1, coeff_compl hU hH]
  have hL : ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      (kappa F S : ℂ) * (evalAt z (esymmL n n) * starRingEnd ℂ (B v (ρ (torusPow F n (lamS S)) v))) =
      evalAt z (esymmL n n) * starRingEnd ℂ (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        (kappa F S : ℂ) * B v (ρ (torusPow F n (lamS S)) v)) := by
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [map_mul, map_natCast]
    ring
  rw [hL, hA, map_mul, map_mul, conj_sqrtQ_pow, hU.1 v v] at hsum
  have hk : (n - r) * (n - (n - r)) = r * (n - r) := by rw [Nat.sub_sub_self hr, mul_comm]
  rw [hk] at hsum
  have hsq : sqrtQ F ≠ 0 := by
    have hq : qF F ≠ 0 := Nat.card_pos.ne'
    unfold sqrtQ
    simpa using hq
  have hb : B v v ≠ 0 := by
    intro h
    have h' := hU.2.1 v hv0
    rw [h, Complex.zero_re] at h'
    exact lt_irrefl 0 h'
  have key : (starRingEnd ℂ (evalAt z (esymmL n r)) * evalAt z (esymmL n n) -
      evalAt z (esymmL n (n - r))) * (sqrtQ F ^ (r * (n - r)) * B v v) = 0 := by
    linear_combination hsum
  rcases mul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (mul_ne_zero (pow_ne_zero _ hsq) hb)

end
