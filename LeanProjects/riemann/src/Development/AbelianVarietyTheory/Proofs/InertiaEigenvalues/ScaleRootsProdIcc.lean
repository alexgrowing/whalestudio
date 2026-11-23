import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section
namespace GlobalTheory.UseLoc.InstPoly
open Polynomial

section Alg

theorem charpoly_smul_unit {R : Type} [CommRing R] [IsDomain R] [Infinite R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) {c : R} (hc : IsUnit c) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨u, rfl⟩ := hc
  obtain ⟨y, rfl⟩ : ∃ y, x = (u : R) * y := ⟨((u⁻¹ : Rˣ) : R) * x, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

theorem scaleRoots_prod_Icc {R : Type} [CommRing R] [IsDomain R] (a : ℕ → R) (s : R) (S : Finset ℕ) :
    (∏ c ∈ S, (X - C (a c))).scaleRoots s = ∏ c ∈ S, (X - C (s * a c)) := by
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro c S hc ih
    rw [Finset.prod_insert hc, Finset.prod_insert hc, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots,
      mul_comm (a c) s]

theorem natDegree_blk {R : Type} [CommRing R] [Nontrivial R] {r : ℕ} (B : Matrix (Fin r) (Fin r) R)
    (a : ℕ → R) (t : ℕ) : (B.charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (a c))).natDegree = r + t := by
  rw [(Matrix.charpoly_monic B).natDegree_mul (monic_prod_of_monic _ _ fun c _ => monic_X_sub_C (a c)),
    Matrix.charpoly_natDegree_eq_dim, natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C (a c)]
  simp [natDegree_X_sub_C]

theorem scale_mem {R : Type} [CommRing R] (J : Ideal R) (p q : R[X]) (hdeg : p.natDegree = q.natDegree) (s : R)
    (h : ∀ k, (p - q).coeff k ∈ J) (k : ℕ) : (p.scaleRoots s - q.scaleRoots s).coeff k ∈ J := by
  rw [coeff_sub, coeff_scaleRoots, coeff_scaleRoots, hdeg, ← sub_mul]
  exact J.mul_mem_right _ (by simpa [coeff_sub] using h k)

theorem congr_mod {O S : Type} [CommRing O] [IsLocalRing O] [CommRing S] (f : O →+* S)
    (hf : ∀ a ∈ IsLocalRing.maximalIdeal O, f a = 0) {n r : ℕ} (A : Matrix (Fin n) (Fin n) O)
    (B : Matrix (Fin r) (Fin r) O) (χ : ℕ → O) (t : ℕ)
    (h : (A.map (IsLocalRing.residue O)).charpoly = (B.map (IsLocalRing.residue O)).charpoly *
      ∏ c ∈ Finset.Icc 1 t, (X - C (IsLocalRing.residue O (χ c)))) :
    A.charpoly.map f = (B.charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (χ c))).map f := by
  let ψ : IsLocalRing.ResidueField O →+* S := Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) f hf
  have hfψ : ∀ p : O[X], p.map f = (p.map (IsLocalRing.residue O)).map ψ := fun p => by
    rw [Polynomial.map_map]
    exact congrArg (fun g : O →+* S => p.map g) (RingHom.ext fun a => rfl)
  rw [hfψ, hfψ, ← Matrix.charpoly_map, h]
  simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Matrix.charpoly_map]

theorem mod_ideal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] (φ : O →+* R) (J : Ideal R)
    (hφ : ∀ a ∈ IsLocalRing.maximalIdeal O, φ a ∈ J) {n r : ℕ} (A : Matrix (Fin n) (Fin n) O)
    (B : Matrix (Fin r) (Fin r) O) (χ : ℕ → O) (t : ℕ)
    (h : (A.map (IsLocalRing.residue O)).charpoly = (B.map (IsLocalRing.residue O)).charpoly *
      ∏ c ∈ Finset.Icc 1 t, (X - C (IsLocalRing.residue O (χ c)))) (k : ℕ) :
    ((A.map φ).charpoly - (B.map φ).charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (φ (χ c)))).coeff k ∈ J := by
  have H := congr_mod ((Ideal.Quotient.mk J).comp φ)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hφ a ha)) A B χ t h
  have e : (B.map φ).charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (φ (χ c))) =
      (B.charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (χ c))).map φ := by
    simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Matrix.charpoly_map]
  have H2 : (A.map φ).charpoly.map (Ideal.Quotient.mk J) =
      ((B.map φ).charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (φ (χ c)))).map (Ideal.Quotient.mk J) := by
    rw [e, Matrix.charpoly_map, Polynomial.map_map, Polynomial.map_map, H]
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_sub, H2, sub_self, coeff_zero]

end Alg

section Val
variable {l : ℕ} [Fact l.Prime]

theorem isUnit_of_incO {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (x : ↥(OL LL)) (hx : IsUnit (incO h x)) :
    IsUnit x := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [map_zero] at hx
    exact absurd hx not_isUnit_zero
  have hx0' : (x : ↥LL.1) ≠ 0 := fun e => hx0 (Subtype.ext e)
  obtain ⟨u, hu⟩ := hx
  have hinv : IsIntegral ℤ_[l] ((x : ↥LL.1)⁻¹) := by
    have hy : IsIntegral ℤ_[l] (((u⁻¹ : (↥(OL LL'))ˣ) : ↥(OL LL')) : ↥LL'.1) := (((u⁻¹ : (↥(OL LL'))ˣ) : ↥(OL LL'))).2
    have he : IntermediateField.inclusion h ((x : ↥LL.1)⁻¹) = (((u⁻¹ : (↥(OL LL'))ˣ) : ↥(OL LL')) : ↥LL'.1) := by
      rw [map_inv₀]
      have h1 : ((incO h x : ↥(OL LL')) : ↥LL'.1) = IntermediateField.inclusion h (x : ↥LL.1) := rfl
      rw [← h1, ← hu]
      have h2 : ((u : ↥(OL LL')) : ↥LL'.1) * (((u⁻¹ : (↥(OL LL'))ˣ) : ↥(OL LL')) : ↥LL'.1) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
      exact inv_eq_of_mul_eq_one_right h2
    rw [← he] at hy
    exact (isIntegral_algHom_iff ((IntermediateField.inclusion h).restrictScalars ℤ_[l])
      (IntermediateField.inclusion h).injective).1 hy
  refine isUnit_iff_exists_inv.2 ⟨⟨(x : ↥LL.1)⁻¹, hinv⟩, Subtype.ext ?_⟩
  show (x : ↥LL.1) * (x : ↥LL.1)⁻¹ = 1
  exact mul_inv_cancel₀ hx0'

theorem dvd_of_not_isUnit (P : LocPrime l) (LL : FinExt l) {lam y : ↥(OL LL)} (hl : Irreducible lam)
    (hy : ¬ IsUnit y) : lam ∣ y := by
  by_cases hy0 : y = 0
  · rw [hy0]; exact dvd_zero lam
  have hl0 : (lam : ↥LL.1) ≠ 0 := fun e => hl.ne_zero (Subtype.ext e)
  have hy0' : (y : ↥LL.1) ≠ 0 := fun e => hy0 (Subtype.ext e)
  have hu0 : (y : ↥LL.1) / lam ≠ 0 := div_ne_zero hy0' hl0
  have key : 0 ≤ P.v LL ((y : ↥LL.1) / lam) ∨ 0 ≤ P.v LL ((y : ↥LL.1) / lam)⁻¹ := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    have hs : P.v LL ((y : ↥LL.1) / lam) + P.v LL ((y : ↥LL.1) / lam)⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hu0, AddValuation.map_one]
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt h1)
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt h2)
    rw [← ha] at h1 hs
    rw [← hb] at h2 hs
    have hab : a + b = 0 := by exact_mod_cast hs
    have ha' : a < 0 := by exact_mod_cast h1
    have hb' : b < 0 := by exact_mod_cast h2
    linarith
  rcases key with h | h
  · refine ⟨⟨(y : ↥LL.1) / lam, (P.v_O LL _).1 h⟩, Subtype.ext ?_⟩
    show (y : ↥LL.1) = lam * ((y : ↥LL.1) / lam)
    field_simp
  · have hlam : lam = y * ⟨((y : ↥LL.1) / lam)⁻¹, (P.v_O LL _).1 h⟩ := Subtype.ext (by
      show (lam : ↥LL.1) = y * ((y : ↥LL.1) / lam)⁻¹
      rw [inv_div]; field_simp)
    obtain ⟨z, hz⟩ : ∃ z : ↥(OL LL), lam = y * z := ⟨_, hlam⟩
    rcases hl.isUnit_or_isUnit hz with h' | h'
    · exact absurd h' hy
    · exact ⟨((h'.unit⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)), by rw [hz, mul_assoc, h'.mul_val_inv, mul_one]⟩

end Val
end GlobalTheory.UseLoc.InstPoly

namespace GlobalTheory.UseLoc.InstPoly
open Polynomial

set_option synthInstance.maxHeartbeats 200000 in
theorem core {R O : Type} [CommRing R] [IsDomain R] [Infinite R] [CommRing O] [IsLocalRing O]
    (φ : O →+* R) (lam : R) (hφ : ∀ a ∈ IsLocalRing.maximalIdeal O, lam ∣ φ a) {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (B : Matrix (Fin r) (Fin r) O) (χ : ℕ → O) (t : ℕ)
    (h : (A.map (IsLocalRing.residue O)).charpoly = (B.map (IsLocalRing.residue O)).charpoly *
      ∏ c ∈ Finset.Icc 1 t, (X - C (IsLocalRing.residue O (χ c))))
    (s : R) (hs : IsUnit s) (k : ℕ) :
    ∃ y, ((s • A.map φ).charpoly - (s • B.map φ).charpoly *
      ∏ c ∈ Finset.Icc 1 t, (X - C (s * φ (χ c)))).coeff k = lam * y := by
  have hn : n = r + t := by
    have h1 := congrArg natDegree h
    have h2 := natDegree_blk (B.map (IsLocalRing.residue O)) (fun c => IsLocalRing.residue O (χ c)) t
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h1
    exact h1.trans h2
  rw [charpoly_smul_unit _ hs, charpoly_smul_unit _ hs, ← scaleRoots_prod_Icc (fun c => φ (χ c)) s,
    ← mul_scaleRoots_of_noZeroDivisors]
  have hdeg : (A.map φ).charpoly.natDegree =
      ((B.map φ).charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (φ (χ c)))).natDegree := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hn]
    exact (natDegree_blk (B.map φ) (fun c => φ (χ c)) t).symm
  have hmem := scale_mem (Ideal.span {lam}) _ _ hdeg s
    (mod_ideal φ (Ideal.span {lam}) (fun a ha => Ideal.mem_span_singleton.2 (hφ a ha)) A B χ t h) k
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨y, by rw [← hy, mul_comm]⟩

section Main
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

abbrev phiC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) : D.nd.O i →+* ↥(OL C.LL) :=
  (incO C.le).comp (D.nbr i w hw).eO.toRingHom

theorem locOC_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (g : Br.G D.nbr i w hw) :
    locOC C M g = (M (decS D.nd w (Br.iota D.nbr i w hw g))).map (phiC C) := rfl

theorem charpoly_repV (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL))
    (g : Br.G D.nbr i w hw) :
    LinearMap.charpoly (repV C N g) = (N g).charpoly.map (algebraMap ↥(OL C.LL) ↥C.LL.1) := by
  have h : LinearMap.charpoly (repV C N g) = ((N g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)).charpoly :=
    Matrix.charpoly_toLin' _
  rw [h, Matrix.charpoly_map]

set_option synthInstance.maxHeartbeats 200000 in
theorem twist_locOC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ) (g : Br.G D.nbr i w hw) :
    twistM (locOC C (twistM M χ)) θ g =
      (((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) *
        phiC C ((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) •
        (M (decS D.nd w (Br.iota D.nbr i w hw g))).map (phiC C) := by
  ext p q
  simp only [twistM, MonoidHom.coe_mk, OneHom.coe_mk, locOC_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, map_mul]
  ring

theorem chiOC_val (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (χ : GE D.nd →* (D.nd.O i)ˣ) (g : Br.G D.nbr i w hw) :
    ((chiOC C χ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) =
      phiC C ((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) := rfl

set_option maxHeartbeats 1000000 in
theorem chiT_val (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ)
    (g : Br.G D.nbr i w hw) :
    ((chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) =
      (((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) *
        phiC C ((((chiU D.nd i 1)⁻¹ (decS D.nd w (Br.iota D.nbr i w hw g))) : (D.nd.O i)ˣ) : D.nd.O i)) *
      phiC C ((chiU D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) := by
  have e : ((chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) =
      ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) *
        ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := rfl
  have e2 : ((((chiU D.nd i c * (chiU D.nd i 1)⁻¹) (decS D.nd w (Br.iota D.nbr i w hw g))) : (D.nd.O i)ˣ) : D.nd.O i)
      = ((chiU D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
        ((((chiU D.nd i 1)⁻¹ (decS D.nd w (Br.iota D.nbr i w hw g))) : (D.nd.O i)ˣ) : D.nd.O i) := rfl
  rw [e, chiOC_val C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g, e2, map_mul]
  ring

end Main

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

theorem charpoly_congr : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (lam : ↥(OL C.LL)), Irreducible lam → TruncatedSeriesCountingIdentities.admG3 i r ρ π → ∀ (x : D.nd.X i) (g : Br.G D.nbr i w hw) (k : ℕ), ∃ y : ↥(OL C.LL), (LinearMap.charpoly (repV C (twistM (locOC C (rTwO D.nd i r x)) θ) g) - tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t g).coeff k = algebraMap (↥(OL C.LL)) (↥C.LL.1) (lam * y) := by
  intro D i r ρ π w hw C θ lam hlam hG3 x g k
  haveI : CharZero ↥C.LL.1 :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[D.nd.l i] ↥C.LL.1).injective
  haveI : Infinite ↥(OL C.LL) := Infinite.of_injective (fun n : ℕ => (n : ↥(OL C.LL))) (fun a b hab => by
    have := congrArg (fun z : ↥(OL C.LL) => (z : ↥C.LL.1)) hab
    simpa using this)
  obtain ⟨s, hs_def⟩ : ∃ s : ↥(OL C.LL), s = ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) *
      phiC C ((((chiU D.nd i 1)⁻¹ (decS D.nd w (Br.iota D.nbr i w hw g))) : (D.nd.O i)ˣ) : D.nd.O i) := ⟨_, rfl⟩
  have hs : IsUnit s := hs_def ▸ (θ g).isUnit.mul ((Units.isUnit _).map (phiC C))
  have e1 : twistM (locOC C (rTwO D.nd i r x)) θ g =
      s • (rO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g))).map (phiC C) := by
    rw [hs_def]; exact twist_locOC C θ (rO D.nd i r x) (chiU D.nd i 1)⁻¹ g
  have e2 : twistM (locOC C (WpO D.nd i ρ π)) θ g =
      s • (rhoO D.nd i ρ π (decS D.nd w (Br.iota D.nbr i w hw g))).map (phiC C) := by
    rw [hs_def]; exact twist_locOC C θ (rhoO D.nd i ρ π) (chiU D.nd i 1)⁻¹ g
  have hprod : ∏ c ∈ Finset.Icc 1 D.R.t, (X - Polynomial.C (((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ)) : ↥C.LL.1)) =
      (∏ c ∈ Finset.Icc 1 D.R.t, (X - Polynomial.C (s * phiC C ((chiU D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) :
        (D.nd.O i)ˣ) : D.nd.O i)))).map (algebraMap ↥(OL C.LL) ↥C.LL.1) := by
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hs_def, ← chiT_val]
    rfl
  have hφ : ∀ a ∈ IsLocalRing.maximalIdeal (D.nd.O i), lam ∣ phiC C a := by
    intro a ha
    apply dvd_of_not_isUnit (D.loc (D.nd.l i)) C.LL hlam
    intro hu
    have h1 := isUnit_of_incO C.le ((D.nbr i w hw).eO a) hu
    have h2 : IsUnit a := by simpa using h1.map (D.nbr i w hw).eO.symm
    exact (IsLocalRing.mem_maximalIdeal a).1 ha h2
  obtain ⟨y, hy⟩ := core (phiC C) lam hφ (rO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g)))
    (rhoO D.nd i ρ π (decS D.nd w (Br.iota D.nbr i w hw g)))
    (fun c => ((chiU D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) D.R.t
    (hG3.2.1 x _) s hs k
  refine ⟨y, ?_⟩
  rw [charpoly_repV, e1, tableLineDegreeTwo.resPoly, charpoly_repV, e2, hprod, ← Polynomial.map_mul, ← Polynomial.map_sub,
    Polynomial.coeff_map, hy]

end GlobalTheory.UseLoc.InstPoly
