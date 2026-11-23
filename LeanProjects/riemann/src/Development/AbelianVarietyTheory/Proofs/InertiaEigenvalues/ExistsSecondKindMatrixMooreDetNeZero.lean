import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZeroProofStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantCrisPlusNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPlusFrobeniusStableSubringInFilZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfFrobeniusPeriodicMemDeRhamFilZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.SecondKind

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem fil_add {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P a) : x + y ∈ Fil P a :=
  ((P.PD (botExt l)).Fil a).add_mem hx hy

theorem fil_zero (a : ℤ) : (0 : P.R.BdR) ∈ Fil P a := ((P.PD (botExt l)).Fil a).zero_mem

theorem fil_sum {a : ℤ} {ι : Type} (s : Finset ι) (f : ι → P.R.BdR) (hf : ∀ i ∈ s, f i ∈ Fil P a) :
    ∑ i ∈ s, f i ∈ Fil P a := ((P.PD (botExt l)).Fil a).sum_mem hf

theorem fil_smul {a : ℤ} (q : ℚ_[l]) {x : P.R.BdR} (hx : x ∈ Fil P a) : q • x ∈ Fil P a :=
  ((P.PD (botExt l)).Fil a).smul_of_tower_mem q hx

theorem fil_mul {a b : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P b) : x * y ∈ Fil P (a + b) :=
  (P.PD (botExt l)).Fil_mul a b x y hx hy

theorem fil_one : (1 : P.R.BdR) ∈ Fil P 0 := (P.PD (botExt l)).one_mem

theorem fil_natCast_mul {a : ℤ} (n : ℕ) {x : P.R.BdR} (hx : x ∈ Fil P a) : (n : P.R.BdR) * x ∈ Fil P a := by
  rw [← nsmul_eq_mul]; exact ((P.PD (botExt l)).Fil a).toAddSubmonoid.nsmul_mem hx n

theorem iter_smul (n : ℕ) (q : ℚ_[l]) (x : P.R.B) : P.φB^[n] (q • x) = q • P.φB^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_smul, ih]

theorem iter_add (n : ℕ) (x y : P.R.B) : P.φB^[n] (x + y) = P.φB^[n] x + P.φB^[n] y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_add, ih]

def phiN (n : ℕ) : P.R.B →+* P.R.B := (P.φB : P.R.B →+* P.R.B) ^ n

theorem phiN_apply (n : ℕ) (x : P.R.B) : phiN P n x = P.φB^[n] x := by
  simp only [phiN, RingHom.coe_pow]; rfl

theorem iter_natCast (n m : ℕ) : P.φB^[n] (m : P.R.B) = m := by
  rw [← phiN_apply, map_natCast]

theorem iter_mul (n : ℕ) (x y : P.R.B) : P.φB^[n] (x * y) = P.φB^[n] x * P.φB^[n] y := by
  rw [← phiN_apply, map_mul, phiN_apply, phiN_apply]

theorem ev_mul (n : ℕ) (x y : P.R.B) : ev P n (x * y) = ev P n x * ev P n y := by
  simp only [ev, iter_mul, map_mul]

theorem ev_smul (n : ℕ) (q : ℚ_[l]) (x : P.R.B) : ev P n (q • x) = q • ev P n x := by
  simp only [ev, iter_smul, map_smul]

theorem ev_add (n : ℕ) (x y : P.R.B) : ev P n (x + y) = ev P n x + ev P n y := by
  simp only [ev, iter_add, map_add]

theorem crisFrobenius_cyclotomicPeriod : P.φB P.tB = (l : P.R.B) * P.tB := by
  have h := (P.PD (botExt l)).t_φ
  rw [P.PD_φ, P.period_datum_t_eq, P.PD_p, Algebra.smul_def, map_natCast] at h
  exact h

theorem crisFrobenius_iterate_cyclotomicPeriod (n : ℕ) : P.φB^[n] P.tB = (l : P.R.B) ^ n * P.tB := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast, crisFrobenius_cyclotomicPeriod]; ring

end GlobalTheory.SecondKind
end

noncomputable section
namespace GlobalTheory.SecondKind

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def fil0 : Subring P.R.BdR where
  carrier := Fil P 0
  mul_mem' := fun hx hy => by simpa using fil_mul P hx hy
  one_mem' := fil_one P
  add_mem' := fun hx hy => fil_add P hx hy
  zero_mem' := fil_zero P 0
  neg_mem' := fun hx => ((P.PD (botExt l)).Fil 0).neg_mem hx

theorem det_mul_mem {k : ℕ} (M : Matrix (Fin k) (Fin k) P.R.BdR) (hM : ∀ i m, M i m ∈ Fil P 0)
    (v : Fin k → P.R.BdR) (hv : ∀ i, M.mulVec v i ∈ Fil P 1) (m : Fin k) : M.det * v m ∈ Fil P 1 := by
  let M' : Matrix (Fin k) (Fin k) (fil0 P) := fun i m => ⟨M i m, hM i m⟩
  have hMM : M = (fil0 P).subtype.mapMatrix M' := by ext i m; rfl
  have hadj : ∀ i, M.adjugate m i ∈ Fil P 0 := by
    intro i
    rw [hMM, ← RingHom.map_adjugate]
    exact (M'.adjugate m i).2
  have key : M.det * v m = (M.adjugate.mulVec (M.mulVec v)) m := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [key]
  show ∑ i, M.adjugate m i * M.mulVec v i ∈ Fil P 1
  refine fil_sum P _ _ fun i _ => ?_
  simpa using fil_mul P (hadj i) (hv i)

end GlobalTheory.SecondKind
end

noncomputable section
namespace GlobalTheory.SecondKind

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def tI : P.R.B := (((isUnit_tB P).unit⁻¹ : P.R.Bˣ) : P.R.B)

theorem tI_mul : tI P * P.tB = 1 := (isUnit_tB P).val_inv_mul

theorem iter_tI (n : ℕ) : P.φB^[n] (tI P) * ((l : P.R.B) ^ n * P.tB) = 1 := by
  rw [← crisFrobenius_iterate_cyclotomicPeriod, ← iter_mul, tI_mul, ← phiN_apply, map_one]

theorem eq_zero_of_frobeniusImages_mem_filOne {AI : LocAinf l P} (T : LocTied l P AI) (h k : ℕ) (hkh : k < h) (d : P.R.B)
    (hφ : P.φB^[h] d = (l : P.R.B) ^ k * d) (hev : ∀ j, ev P j d ∈ Fil P 1) : d = 0 := by
  have hB := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  have hl0 : ((l : ℚ_[l])) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero

  have hc : (l : P.R.B) ^ (h - k) * P.φB^[h] (d * tI P) = d * tI P := by
    have h1 := iter_tI P h
    rw [iter_mul, hφ]
    have h2 : (l : P.R.B) ^ h * P.φB^[h] (tI P) = tI P := by
      calc (l : P.R.B) ^ h * P.φB^[h] (tI P) = (l : P.R.B) ^ h * P.φB^[h] (tI P) * (P.tB * tI P) := by
            rw [mul_comm P.tB, tI_mul, mul_one]
        _ = (P.φB^[h] (tI P) * ((l : P.R.B) ^ h * P.tB)) * tI P := by ring
        _ = tI P := by rw [h1, one_mul]
    calc (l : P.R.B) ^ (h - k) * ((l : P.R.B) ^ k * d * P.φB^[h] (tI P))
        = d * ((l : P.R.B) ^ (h - k + k) * P.φB^[h] (tI P)) := by rw [pow_add]; ring
      _ = d * tI P := by rw [Nat.sub_add_cancel hkh.le, h2]

  have hcf : ∀ j < h, ev P j (d * tI P) ∈ Fil P 0 := by
    intro j _
    have hiff := (hB.2.2.1 0 1 (ev P j (d * tI P)))
    rw [hiff, hB.2.2.2.2.2.2.2.2.2.2, ev_mul]
    have e1 : ev P j (tI P) * (((l : P.R.BdR)) ^ j * P.ιB P.tB) = 1 := by
      have := congrArg P.ιB (iter_tI P j)
      rwa [map_mul, map_one, map_mul, map_pow, map_natCast] at this
    have e2 : P.ιB P.tB * ev P j (tI P) = algebraMap ℚ_[l] P.R.BdR (((l : ℚ_[l]) ^ j)⁻¹) := by
      have hq : ((l : P.R.BdR)) ^ j * algebraMap ℚ_[l] P.R.BdR (((l : ℚ_[l]) ^ j)⁻¹) = 1 := by
        rw [← map_natCast (algebraMap ℚ_[l] P.R.BdR), ← map_pow, ← map_mul,
          mul_inv_cancel₀ (pow_ne_zero _ hl0), map_one]
      calc P.ιB P.tB * ev P j (tI P)
          = P.ιB P.tB * ev P j (tI P) * ((l : P.R.BdR) ^ j * algebraMap ℚ_[l] P.R.BdR (((l : ℚ_[l]) ^ j)⁻¹)) := by
            rw [hq, mul_one]
        _ = (ev P j (tI P) * ((l : P.R.BdR) ^ j * P.ιB P.tB)) * algebraMap ℚ_[l] P.R.BdR (((l : ℚ_[l]) ^ j)⁻¹) := by ring
        _ = _ := by rw [e1, one_mul]
    have : P.ιB P.tB * (ev P j d * ev P j (tI P)) = ((l : ℚ_[l]) ^ j)⁻¹ • ev P j d := by
      rw [Algebra.smul_def, ← e2]; ring
    rw [this]
    simpa using fil_smul P (((l : ℚ_[l]) ^ j)⁻¹) (hev j)
  have hz := GlobalTheory.T.eq_zero_of_frobenius_periodic_mem_deRhamFil_zero l P AI T h (h - k) (by omega) (by omega) (d * tI P) hc hcf
  calc d = d * tI P * P.tB := by rw [mul_assoc, tI_mul, mul_one]
    _ = 0 := by rw [hz, zero_mul]

end GlobalTheory.SecondKind
end

noncomputable section
namespace GlobalTheory.SecondKind

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def evL (n : ℕ) : P.R.B →ₗ[ℚ_[l]] P.R.BdR where
  toFun := ev P n
  map_add' := ev_add P n
  map_smul' := ev_smul P n

theorem ev_shift (h i : ℕ) (x : P.R.B) (hx : P.φB^[h] x = (l : P.R.B) * x) :
    ev P (i + h) x = (l : P.R.BdR) * ev P i x := by
  simp only [ev]
  rw [Function.iterate_add_apply, hx, iter_mul, iter_natCast, map_mul, map_natCast]

theorem sum_all (h : ℕ) (hh : 0 < h) (lam : Fin h → P.R.BdR) (a : Fin h → P.R.B)
    (haφ : ∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j)
    (hs : ∀ i : Fin h, ∑ j, lam j * ev P i (a j) ∈ Fil P 1) (i : ℕ) :
    ∑ j, lam j * ev P i (a j) ∈ Fil P 1 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < h
    · exact hs ⟨i, hi⟩
    · have e : i = (i - h) + h := by omega
      have : ∑ j, lam j * ev P i (a j) = (l : P.R.BdR) * ∑ j, lam j * ev P (i - h) (a j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [e, ev_shift P h (i - h) (a j) (haφ j), Nat.add_sub_cancel]; ring
      rw [this]
      exact fil_natCast_mul P l (ih (i - h) (by omega))

theorem span_props {AI : LocAinf l P} (T : LocTied l P AI) (h : ℕ) (a : Fin h → P.R.B)
    (haP : ∀ j, Plus T (a j)) (haφ : ∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) (x : P.R.B)
    (hx : x ∈ Submodule.span ℚ_[l] (Set.range a)) :
    Plus T x ∧ P.φB^[h] x = (l : P.R.B) * x := by
  have hp := GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero l P AI T
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨haP j, haφ j⟩
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa using hp.2.2.2.1 0
    · rw [← phiN_apply, map_zero, mul_zero]
  | add x y _ _ hx hy =>
    exact ⟨(hp.2.2.1 x y hx.1 hy.1).1, by rw [iter_add, hx.2, hy.2, mul_add]⟩
  | smul q x _ hx =>
    refine ⟨?_, ?_⟩
    · rw [Algebra.smul_def]; exact (hp.2.2.1 _ _ (hp.2.2.2.1 q) hx.1).2
    · rw [iter_smul, hx.2, mul_smul_comm]

end GlobalTheory.SecondKind
end

noncomputable section
namespace GlobalTheory.SecondKind

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem dep_false {AI : LocAinf l P} (T : LocTied l P AI) (h : ℕ) (hh : 2 ≤ h) (lam : Fin h → P.R.BdR)
    (hlam : ∀ j, lam j ∈ Fil P 0) (hind : ∀ c : Fin h → ℚ_[l], ∑ j, c j • lam j ∈ Fil P 1 → c = 0)
    (a : Fin h → P.R.B) (ha0 : a ≠ 0) (haP : ∀ j, Plus T (a j))
    (haφ : ∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j)
    (hs : ∀ i : Fin h, ∑ j, lam j * ev P i (a j) ∈ Fil P 1) (hli : ¬ LinearIndependent ℚ_[l] a) : False := by
  have hB := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  have hp := GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero l P AI T
  let V := Submodule.span ℚ_[l] (Set.range a)
  haveI : FiniteDimensional ℚ_[l] V := FiniteDimensional.span_of_finite ℚ_[l] (Set.finite_range a)
  let k := Module.finrank ℚ_[l] V
  let bas : Module.Basis (Fin k) ℚ_[l] V := Module.finBasis ℚ_[l] V
  let b : Fin k → P.R.B := fun m => (bas m : P.R.B)
  have hkh : k < h := by
    have h1 : k ≤ h := (by simpa using finrank_range_le_card (R := ℚ_[l]) a : Set.finrank ℚ_[l] (Set.range a) ≤ h)
    rcases h1.lt_or_eq with h1 | h1
    · exact h1
    · exfalso; apply hli
      rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]; exact h1.symm
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso; apply ha0
      have hbot : V = ⊥ := Submodule.finrank_eq_zero.mp h0
      funext j
      have : a j ∈ V := Submodule.subset_span ⟨j, rfl⟩
      rw [hbot, Submodule.mem_bot] at this
      exact this
    · exact h0
  let c : Fin h → Fin k → ℚ_[l] := fun j m => bas.repr ⟨a j, Submodule.subset_span ⟨j, rfl⟩⟩ m
  have hac : ∀ j, a j = ∑ m, c j m • b m := by
    intro j
    have := congrArg Subtype.val (bas.sum_repr ⟨a j, Submodule.subset_span ⟨j, rfl⟩⟩)
    rw [Submodule.coe_sum] at this
    simpa [c, b] using this.symm
  have hbP : ∀ m, Plus T (b m) ∧ P.φB^[h] (b m) = (l : P.R.B) * b m :=
    fun m => span_props P T h a haP haφ _ (bas m).2
  have hbli : LinearIndependent ℚ_[l] b :=
    bas.linearIndependent.map' V.subtype V.ker_subtype
  have hd := GlobalTheory.T.mooreDeterminant_crisPlus_ne_zero l P AI T h k hkh.le b (fun m => (hbP m).1) (fun m => (hbP m).2) hbli
  let lam' : Fin k → P.R.BdR := fun m => ∑ j, c j m • lam j
  have hlam'0 : ∀ m, lam' m ∈ Fil P 0 := fun m => fil_sum P _ _ fun j _ => fil_smul P _ (hlam j)
  let m0 : Fin k := ⟨0, hk0⟩
  have hm0 : lam' m0 ∉ Fil P 1 := by
    intro hmem
    have hz := hind (fun j => c j m0) hmem
    have hle : Submodule.span ℚ_[l] ((Subtype.val : V → P.R.B) ⁻¹' Set.range a) ≤
        LinearMap.ker (bas.coord m0) := by
      rw [Submodule.span_le]
      rintro x ⟨j, hj⟩
      have hx : x = ⟨a j, Submodule.subset_span ⟨j, rfl⟩⟩ := Subtype.ext hj.symm
      subst hx
      show bas.coord m0 _ = 0
      rw [Module.Basis.coord_apply]
      exact congrFun hz j
    rw [Submodule.span_span_coe_preimage] at hle
    have := hle (Submodule.mem_top (x := bas m0))
    rw [LinearMap.mem_ker, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same] at this
    exact one_ne_zero this
  have hsum' : ∀ i : ℕ, ∑ m, lam' m * ev P i (b m) ∈ Fil P 1 := by
    intro i
    have e : ∑ j, lam j * ev P i (a j) = ∑ m, lam' m * ev P i (b m) := by
      calc ∑ j, lam j * ev P i (a j) = ∑ j, lam j * evL P i (∑ m, c j m • b m) :=
            Finset.sum_congr rfl fun j _ => by rw [← hac j]; rfl
        _ = ∑ j, ∑ m, (c j m • lam j) * ev P i (b m) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [map_smul, mul_smul_comm, smul_mul_assoc]; rfl
        _ = ∑ m, lam' m * ev P i (b m) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.sum_mul]
    rw [← e]; exact sum_all P h (by omega) lam a haφ hs i
  have hdet : ∀ j : ℕ, ev P j (Matrix.of fun i m : Fin k => P.φB^[i] (b m)).det ∈ Fil P 1 := by
    intro j
    let M : Matrix (Fin k) (Fin k) P.R.BdR := Matrix.of fun i m => ev P (j + i) (b m)
    have eM : ev P j (Matrix.of fun i m : Fin k => P.φB^[i] (b m)).det = M.det := by
      have : ev P j = ((P.ιB : P.R.B →+* P.R.BdR).comp (phiN P j)) := by
        funext x; simp [ev, phiN_apply]
      rw [this, RingHom.map_det]
      congr 1
      ext i m
      simp [M, ev, phiN_apply, Function.iterate_add_apply]
    rw [eM]
    have hMv : ∀ i, M.mulVec lam' i ∈ Fil P 1 := by
      intro i
      show ∑ m, M i m * lam' m ∈ Fil P 1
      have e : ∑ m, M i m * lam' m = ∑ m, lam' m * ev P (j + i) (b m) :=
        Finset.sum_congr rfl fun m _ => mul_comm _ _
      rw [e]; exact hsum' (j + i)
    have h1 := det_mul_mem P M (fun i m => hp.2.1 _ (hbP m).1 (j + i)) lam' hMv m0
    obtain ⟨y, hy0, hy⟩ := hB.2.2.2.1 (lam' m0) (hlam'0 m0) hm0
    have := fil_mul P h1 hy0
    rw [mul_assoc, hy, mul_one] at this
    simpa using this
  have hdφ : P.φB^[h] (Matrix.of fun i m : Fin k => P.φB^[i] (b m)).det =
      (l : P.R.B) ^ k * (Matrix.of fun i m : Fin k => P.φB^[i] (b m)).det := by
    rw [← phiN_apply, RingHom.map_det]
    have : (phiN P h).mapMatrix (Matrix.of fun i m : Fin k => P.φB^[i] (b m)) =
        (l : P.R.B) • Matrix.of fun i m : Fin k => P.φB^[i] (b m) := by
      ext i m
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
        phiN_apply]
      rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, (hbP m).2, iter_mul, iter_natCast]
    rw [this, Matrix.det_smul, Fintype.card_fin]
  exact hd (eq_zero_of_frobeniusImages_mem_filOne P T h k hkh _ hdφ hdet)

end GlobalTheory.SecondKind

namespace GlobalTheory.SecondKind

theorem exists_secondKind : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 2 ≤ h → ∀ lam : Fin h → P.R.BdR, (∀ j, lam j ∈ Fil P 0) → (∀ c : Fin h → ℚ_[l], ∑ j, c j • lam j ∈ Fil P 1 → c = 0) → ∃ a : Fin h → P.R.B, (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) ∧ (∀ (i : ℕ) j, ev P i (a j) ∈ Fil P 0) ∧ (∀ i : Fin h, ∑ j, lam j * ev P i (a j) ∈ Fil P 1) ∧ (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ≠ 0 := by
  intro l _ P AI T h hh lam hlam hind
  obtain ⟨a, ha0, haP, haφ, hs⟩ := GlobalTheory.T.existsNonzeroFrobVectorResidueZero_proof l P AI T h hh lam hlam hind
  refine ⟨a, haφ, fun i j => (GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero l P AI T).2.1 _ (haP j) i, hs, ?_⟩
  by_cases hli : LinearIndependent ℚ_[l] a
  · exact GlobalTheory.T.mooreDeterminant_crisPlus_ne_zero l P AI T h h le_rfl a haP haφ hli
  · exact (dep_false P T h hh lam hlam hind a ha0 haP haφ hs hli).elim

end GlobalTheory.SecondKind
end
