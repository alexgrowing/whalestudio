import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ColumnWordReductionOfFour

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem expand_pow_zmod (p : ℕ) [Fact p.Prime] {σ : Type} (f : MvPolynomial σ (ZMod p)) (n : ℕ) :
    expand (p ^ n) f = f ^ (p ^ n) := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [expand_C, ← map_pow, ZMod.pow_card_pow]
  | add u v hu hv => rw [map_add, hu, hv, add_pow_char_pow]
  | mul_X q v h => rw [map_mul, h, expand_X, mul_pow]

theorem charP_FF {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) : CharP (FF O) p := by
  have h0 : ((p : ℕ) : FF O) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff (p : O)).mpr S.p_mem
    simpa using this
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h0

theorem expand_pow_of_map (p : ℕ) [Fact p.Prime] {Fd : Type} [Field Fd] (φ : ZMod p →+* Fd) {σ : Type}
    (f : MvPolynomial σ (ZMod p)) (n : ℕ) :
    expand (p ^ n) (MvPolynomial.map φ f) = (MvPolynomial.map φ f) ^ (p ^ n) := by
  rw [← map_expand, expand_pow_zmod, map_pow]

theorem map_detPl {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ) :
    MvPolynomial.map f (X.detPl R j x) = X.detPl S j x := by
  unfold Dat.detPl
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem map_DlSeg {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n' r : ℕ} [NeZero n'] (X : Dat n' r)
    (p K : ℕ) (j : ℤ) : MvPolynomial.map f (X.DlSeg p K R j) = X.DlSeg p K S j := by
  unfold Dat.DlSeg
  rw [map_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [map_pow, map_detPl]

theorem ell_split {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (R : Type) [CommRing R] (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (he : X.IsEll p K j e) :
    (monomial e 1 : SegRing R r K) = plEmb R r K (X.ellP K R j e) * nmEmb R r K (X.ellN K R j e) := by
  classical
  rw [monomial_eq, map_one, one_mul]
  have hsub : e.support ⊆ X.toLate j ×ˢ (Finset.univ : Finset (Fin (r + K))) := by
    intro v hv
    rw [Finset.mem_product]
    exact ⟨he.1 v (Finsupp.mem_support_iff.mp hv), Finset.mem_univ _⟩
  rw [Finsupp.prod_of_support_subset e hsub _ (fun _ _ => pow_zero _), Finset.prod_product]
  unfold Dat.ellP Dat.ellN plEmb nmEmb
  simp only [map_prod, map_pow, rename_X]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Fin.prod_univ_add]

theorem frobenius_reduction_product (C₀ : ℝ) : FrobeniusReductionProduct C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hc
  have : Fact p.Prime := ⟨hc.hX.prime⟩
  have : CharP (FF O) p := charP_FF S
  let φ : ZMod p →+* FF O := ZMod.castHom (dvd_refl p) (FF O)
  have hW : MvPolynomial.map (IsLocalRing.residue O) (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) =
      MvPolynomial.map φ (segRen X.F j (ZMod p) (r + K) (PsiPl (ZMod p) q.1 I' * PsiTan (ZMod p) q.2 I'')) := by
    simp only [segRen, map_rename, map_mul, PsiPl_map, PsiTan_map]
  have hW2 : MvPolynomial.map (IsLocalRing.residue O) (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) =
      plEmb (FF O) r K (segRen X.F j (FF O) r (Psi (FF O) q.1 I')) *
        nmEmb (FF O) r K (segRen X.F j (FF O) K (Psi (FF O) q.2 I'')) := by
    rw [← segRen_mul]
    simp only [segRen, map_rename, map_mul, PsiPl_map, PsiTan_map]
    rfl
  unfold Dat.zSeg Dat.Aw Dat.Gw
  rw [map_mul, map_mul, map_expand, hW, expand_pow_of_map, ← hW, hW2, map_monomial, map_one,
    ell_split X p K (FF O) j e hc.he]
  have hD : MvPolynomial.map (IsLocalRing.residue O) (plEmb O r K (X.DlSeg p K O j)) =
      plEmb (FF O) r K (X.DlSeg p K (FF O) j) := by
    unfold plEmb
    rw [map_rename, map_DlSeg]
  rw [hD]
  simp only [map_mul, map_pow, mul_pow]
  ring

end Formalism.MainNotions.SelectionLemmas.Pf
