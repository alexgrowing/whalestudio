import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EcoefQNormLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer.SFil

def texp {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) (x : R) :
    Matrix (Fin d) (Fin d) R :=
  ∑ i ∈ Finset.range d, (q ((i.factorial : ℚ)⁻¹) * x ^ i) • N ^ i

theorem map_sum_smul_pow {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {d : ℕ}
    (N : Matrix (Fin d) (Fin d) R) (a : ℕ → R) :
    (∑ i ∈ Finset.range d, a i • N ^ i).map f = ∑ i ∈ Finset.range d, f (a i) • (N.map f) ^ i := by
  change f.mapMatrix _ = ∑ i ∈ Finset.range d, f (a i) • (f.mapMatrix N) ^ i
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow]
  ext a b
  simp [RingHom.mapMatrix_apply]

theorem texp_map {R R' : Type} [CommRing R] [CommRing R'] (q : ℚ →+* R) (q' : ℚ →+* R') (f : R →+* R') {d : ℕ}
    (N : Matrix (Fin d) (Fin d) R) (x : R) : (texp q N x).map f = texp q' (N.map f) (f x) := by
  have e : q' = f.comp q := Subsingleton.elim _ _
  unfold texp
  rw [map_sum_smul_pow, e]
  simp only [map_mul, map_pow, RingHom.comp_apply]

theorem texp_add {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) (hN : N ^ d = 0)
    (x y : R) : texp q N x * texp q N y = texp q N (x + y) := by
  letI : Algebra ℚ R := q.toAlgebra
  have h : ∀ z : R, (z • N) ^ d = 0 := fun z => by rw [smul_pow, hN, smul_zero]
  have e : ∀ z : R, texp q N z = IsNilpotent.exp (z • N) := fun z => by
    rw [IsNilpotent.exp_eq_sum (h z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, mul_smul]
    exact algebraMap_smul R ((i.factorial : ℚ)⁻¹) _
  rw [e, e, e, add_smul, IsNilpotent.exp_add_of_commute _ ⟨d, h x⟩ ⟨d, h y⟩]
  exact ((Commute.refl N).smul_left x).smul_right y

theorem texp_zero {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) :
    texp q N 0 = 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  unfold texp
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [zero_pow hi]
  · intro h
    exact absurd (Finset.mem_range.2 hd) h

theorem texp_sub_mem {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) (I : Ideal R)
    {x y : R} (h : x - y ∈ I) (i j : Fin d) : (texp q N x - texp q N y) i j ∈ I := by
  unfold texp
  rw [← Finset.sum_sub_distrib, Matrix.sum_apply]
  refine I.sum_mem fun n _ => ?_
  rw [← sub_smul, Matrix.smul_apply, smul_eq_mul, ← mul_sub]
  exact I.mul_mem_right _ (I.mul_mem_left _ (Ideal.mem_of_dvd I (sub_dvd_pow_sub_pow x y n) h))

theorem cleared_map {S R : Type} [CommRing S] [CommRing R] (q : ℚ →+* R) (f : S →+* R) {d : ℕ}
    (N : Matrix (Fin d) (Fin d) S) {l : ℕ} (hl : l ≠ 0) (c e : ℕ) (a : ℕ → S)
    (ha : ∀ i < d, ((i.factorial : S) * (l : S) ^ (c * i)) * a i = (l : S) ^ e) (x : S) :
    (∑ i ∈ Finset.range d, (a i * x ^ i) • N ^ i).map f =
      (l : R) ^ e • texp q (N.map f) (q ((l : ℚ) ^ c)⁻¹ * f x) := by
  rw [map_sum_smul_pow]
  unfold texp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [smul_smul]
  congr 1
  have h1 := congrArg f (ha i (Finset.mem_range.1 hi))
  simp only [map_mul, map_pow, map_natCast] at h1
  have h2 : q ((i.factorial : ℚ)⁻¹) * q ((l : ℚ) ^ c)⁻¹ ^ i * ((i.factorial : R) * (l : R) ^ (c * i)) = 1 := by
    have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
    have hf : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    rw [← map_natCast q, ← map_natCast q l, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul, ← map_one q]
    congr 1
    rw [pow_mul, inv_pow]
    field_simp
  rw [map_mul, map_pow, mul_pow, ← h1]
  linear_combination (-(f (a i) * f x ^ i)) * h2

theorem exists_cleared {l : ℕ} [Fact l.Prime] (c d : ℕ) :
    ∃ (e : ℕ) (a : ℕ → ℤ_[l]), ∀ i < d, ((i.factorial : ℤ_[l]) * (l : ℤ_[l]) ^ (c * i)) * a i = (l : ℤ_[l]) ^ e := by
  obtain ⟨e, m, hm, hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd d.factorial_ne_zero l (Fact.out : l.Prime).ne_one
  refine ⟨e + c * d, fun i => ecoef l (e + c * d) c i, fun i hi => ?_⟩
  apply Subtype.ext
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hf0 : (i.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero i)
  push_cast
  rw [ecoef_val (ecoefQ_norm_le c hm hd hi)]
  unfold ecoefQ
  field_simp

theorem approx {l : ℕ} [Fact l.Prime] {S R : Type} [CommRing S] [IsDomain S] [CharZero S] [CommRing R]
    (z : ℤ_[l] →+* S) (q : ℚ →+* R) (f : S →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) S) (hN : N ^ d = 0)
    (I : Ideal R) (k k' : ℕ) (s : S) (lam : R) (h : f s - (l : R) ^ k' * lam ∈ I) :
    ∃ (e : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) S), Λ * Λ' = (l : S) ^ (2 * e) • (1 : Matrix (Fin d) (Fin d) S) ∧
      ∀ i j, (Λ.map f - (l : R) ^ e • texp q (N.map f) (-(q ((l : ℚ) ^ k)⁻¹ * lam))) i j ∈ I := by
  obtain ⟨e, a, ha⟩ := exists_cleared (l := l) (k + k') d
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have ha' : ∀ i < d, ((i.factorial : S) * (l : S) ^ ((k + k') * i)) * z (a i) = (l : S) ^ e := fun i hi => by
    simpa only [map_mul, map_pow, map_natCast] using congrArg z (ha i hi)
  refine ⟨e, ∑ i ∈ Finset.range d, (z (a i) * (-s) ^ i) • N ^ i, ∑ i ∈ Finset.range d, (z (a i) * s ^ i) • N ^ i,
    ?_, fun i j => ?_⟩
  · have hinj := IsFractionRing.injective S (FractionRing S)
    apply Matrix.map_injective hinj
    have hN' : (N.map (algebraMap S (FractionRing S))) ^ d = 0 := by
      change ((algebraMap S (FractionRing S)).mapMatrix N) ^ d = 0
      rw [← map_pow, hN, map_zero]
    change Matrix.map _ _ = Matrix.map _ _
    rw [Matrix.map_mul, cleared_map (algebraMap ℚ _) _ N hl _ _ _ ha', cleared_map (algebraMap ℚ _) _ N hl _ _ _ ha',
      Matrix.smul_mul, Matrix.mul_smul, texp_add _ _ hN', map_neg, mul_neg, neg_add_cancel, texp_zero, smul_smul,
      ← pow_add, two_mul]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  · rw [cleared_map q f N hl _ _ _ ha', ← smul_sub, Matrix.smul_apply, smul_eq_mul]
    refine I.mul_mem_left _ (texp_sub_mem q _ I ?_ i j)
    have h2 : q ((l : ℚ) ^ k)⁻¹ = q ((l : ℚ) ^ (k + k'))⁻¹ * (l : R) ^ k' := by
      have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
      rw [← map_natCast q l, ← map_pow, ← map_mul]
      congr 1
      field_simp
      ring
    have h3 := I.mul_mem_left (-q ((l : ℚ) ^ (k + k'))⁻¹) h
    convert h3 using 1
    rw [h2, map_neg]
    ring

theorem invariant_basis_approx : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)) (k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), Mn ^ d = 0 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∀ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) → ∃ Λ₀ : Matrix (Fin d) (Fin d) (Per.BdRp l), (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * (U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))).map (Per.σD (g : GQ l)) = U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) (bk.S)), Λ * Λ' = (l : bk.S) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ ∀ i j, (Λ.map ((aDp l).comp bk.ev) - (l : Per.BdRp l) ^ k • Λ₀) i j ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hF d ρ U k Mn c hMn hU lam hlam happ
  obtain ⟨-, -, -, -, -, -, -, -, -, hD, hDp, -, -⟩ := ActLaws.act_laws l
  let q : ℚ →+* Per.BdRp l := C.o.comp (algebraMap ℚ (Om l))
  let a : Per.BdRp l →+* Per.BdR l := algebraMap (Per.BdRp l) (Per.BdR l)
  let w : Wq l bk.a →+* Per.BdRp l := (aDp l).comp (wA l bk.a).toRingHom
  refine ⟨texp q (Mn.map w) (-(q ((l : ℚ) ^ k)⁻¹ * lam)), fun g => ?_, fun m => ?_⟩
  · have hN : ((Mn.map w).map a) ^ d = 0 := by
      change (a.mapMatrix (w.mapMatrix Mn)) ^ d = 0
      rw [← map_pow, ← map_pow, hMn, map_zero, map_zero]
    have hNσ : ((Mn.map w).map a).map (Per.σD (g : GQ l)) = (Mn.map w).map a := by
      ext i j
      change Per.σD (g : GQ l) (a (aDp l (wA l bk.a (Mn i j)))) = a (aDp l (wA l bk.a (Mn i j)))
      rw [hD, hDp, bk.gal_w]
    have hq : ∀ x : ℚ, Per.σD (g : GQ l) (a (q x)) = a (q x) := fun x =>
      RingHom.congr_fun (Subsingleton.elim ((Per.σD (g : GQ l)).comp (a.comp q)) (a.comp q)) x
    have hqB : ∀ x : ℚ, C.ι (C.qB (x : ℚ_[l])) = a (q x) := fun x =>
      RingHom.congr_fun (Subsingleton.elim (C.ι.comp (C.qB.comp (Rat.castHom ℚ_[l]))) (a.comp q)) x
    have h1 := congrArg (fun M => Matrix.map M C.ι) (hU g)
    simp only [Matrix.map_mul] at h1
    rw [map_sum_smul_pow] at h1
    have e1 : ((ρ g).map (Per.zB l)).map C.ι = (ρ g).map (Per.zD l) := by
      ext i j
      change C.ι (Per.zB l (ρ g i j)) = Per.zD l (ρ g i j)
      rw [← T.zB, ← hF.ι, AlgHom.commutes, T.zD]
    have e2 : (U.map (Per.σB (g : GQ l))).map C.ι = (U.map C.ι).map (Per.σD (g : GQ l)) := by
      ext i j
      exact ULaws.iota_sigma C _ _
    have e3 : (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)).map C.ι = (Mn.map w).map a := by
      ext i j
      exact ULaws.iota_aB C _
    have e4 : ∑ i ∈ Finset.range d, C.ι (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) *
        (Per.zB l (c g) * C.tB) ^ i) • ((Mn.map w).map a) ^ i =
        texp (a.comp q) ((Mn.map w).map a) (a (q ((l : ℚ) ^ k)⁻¹) * a (aDp l (Per.zA l (c g)) * C.j C.t)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have e5 : (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) =
          (((i.factorial : ℚ)⁻¹ * ((l : ℚ) ^ k)⁻¹ ^ i : ℚ) : ℚ_[l]) := by
        push_cast
        rw [mul_inv, pow_mul, inv_pow]
      have e6 : C.ι (Per.zB l (c g)) = a (aDp l (Per.zA l (c g))) := by
        rw [← ULaws.u_padicInt C, C.ι_u, ← C.o_sec.z]
        rfl
      have e7 : C.ι C.tB = a (C.j C.t) := C.ι_j _
      rw [map_mul C.ι, e5, hqB, map_pow C.ι, map_mul C.ι, e6, e7]
      simp only [map_mul, map_pow, RingHom.comp_apply, mul_pow]
      ring
    rw [e1, e2, e3, e4] at h1
    change _ * (U.map C.ι * Matrix.map _ a).map _ = U.map C.ι * Matrix.map _ a
    rw [texp_map q (a.comp q) a, Matrix.map_mul, texp_map (a.comp q) (a.comp q), hNσ, ← Matrix.mul_assoc, h1,
      Matrix.mul_assoc, texp_add _ _ hN]
    congr 2
    have e8 : Per.σD (g : GQ l) (a lam) = a lam + a (aDp l (Per.zA l (c g)) * C.j C.t) :=
      (hD _ lam).trans ((congrArg a (hlam g)).trans (map_add a _ _))
    rw [map_neg a, map_mul a (q _), map_neg, map_mul (Per.σD (g : GQ l)), hq, e8]
    ring
  · obtain ⟨k', s, -, hs⟩ := happ m
    haveI : CharZero bk.S := RingHom.charZero ((Per.θD l).comp ((aDp l).comp bk.ev))
    have hN : (Mn.map (PowerSeries.C : Wq l bk.a →+* bk.S)) ^ d = 0 := by
      change ((PowerSeries.C : Wq l bk.a →+* bk.S).mapMatrix Mn) ^ d = 0
      rw [← map_pow, hMn, map_zero]
    have e1 : (Mn.map (PowerSeries.C : Wq l bk.a →+* bk.S)).map ((aDp l).comp bk.ev) = Mn.map w := by
      ext i j
      exact congrArg (aDp l) (bk.ev_C _)
    have := approx ((PowerSeries.C : Wq l bk.a →+* bk.S).comp (algebraMap ℤ_[l] (Wq l bk.a))) q
      ((aDp l).comp bk.ev) _ hN (Per.FilP l m) k k' s lam hs
    rwa [e1] at this

end GlobalTheory.SstPer.SFil

end
