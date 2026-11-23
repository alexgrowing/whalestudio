import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffTeichSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfConstantCoeffZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLift

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL PowerSeries

noncomputable section

namespace GlobalTheory.HWL.IoLayer

section General

variable {O A E S : Type} [CommRing O] [CommRing A] [CommRing E] [CommRing S]
  [Algebra O A] [Algebra O E] [Algebra O S] [Algebra A E] [IsScalarTower O A E]

theorem sep_of_haus (y : S) [IsHausdorff (Ideal.span {y}) S] (x : S) (hx : ∀ n, y ^ n ∣ x) : x = 0 :=
  GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (hx n)

theorem lim_of_precomplete (y : S) [h : IsPrecomplete (Ideal.span {y}) S] (f : ℕ → S)
    (hf : ∀ m n, m ≤ n → y ^ m ∣ f m - f n) : ∃ L, ∀ n, y ^ n ∣ f n - L := by
  obtain ⟨L, hL⟩ := h.prec' f (by
    intro m n hmn
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact Ideal.mem_span_singleton.2 (hf m n hmn))
  refine ⟨L, fun n => ?_⟩
  have hn := hL n
  simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hn
  exact Ideal.mem_span_singleton.1 hn

theorem ext_unique (p : ℕ) (π : A) (hπ : IsUnit (algebraMap A E π))
    (hd : ∀ (x : E) (k : ℕ), ∃ (a : A) (m : ℕ),
      x * algebraMap A E (π ^ m) - algebraMap A E a ∈ Ideal.span {((p : ℕ) : E) ^ k})
    (hs : ∀ x : S, (∀ n, (p : S) ^ n ∣ x) → x = 0) (F F' : E →ₐ[O] S)
    (h : ∀ a, F (algebraMap A E a) = F' (algebraMap A E a)) (x : E) : F x = F' x := by
  rw [← sub_eq_zero]
  refine hs _ fun k => ?_
  obtain ⟨a, m, hm⟩ := hd x k
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hm
  have h1 := congrArg F hc
  have h2 := congrArg F' hc
  rw [map_sub, map_mul, map_mul, map_pow _ (p : E), map_natCast] at h1 h2
  rw [← h, ← h] at h2
  have hu : IsUnit (F (algebraMap A E (π ^ m))) := by
    rw [map_pow]; exact (hπ.pow m).map F
  rw [← hu.dvd_mul_right]
  exact ⟨F c - F' c, by linear_combination h1 - h2⟩

theorem ext_exists (p : ℕ) (π : A)
    (hd : ∀ (x : E) (k : ℕ), ∃ (a : A) (m : ℕ),
      x * algebraMap A E (π ^ m) - algebraMap A E a ∈ Ideal.span {((p : ℕ) : E) ^ k})
    (hsat : ∀ (a : A) (k : ℕ), algebraMap A E a ∈ Ideal.span {((p : ℕ) : E) ^ k} →
      ∃ b : A, a = ((p : ℕ) : A) ^ k * b)
    [IsAdicComplete (Ideal.span {(p : S)}) S] (f : A →ₐ[O] S) (hf : IsUnit (f π)) :
    ∃ F : E →ₐ[O] S, ∀ a, F (algebraMap A E a) = f a := by
  let Rel : ℕ → E → S → Prop := fun k x y => ∃ (a : A) (m : ℕ),
    (p : E) ^ k ∣ x * algebraMap A E π ^ m - algebraMap A E a ∧ (p : S) ^ k ∣ y * f π ^ m - f a
  have uniq : ∀ k x y y', Rel k x y → Rel k x y' → (p : S) ^ k ∣ y - y' := by
    rintro k x y y' ⟨a, m, ⟨c, hc⟩, ⟨d, hd⟩⟩ ⟨a', m', ⟨c', hc'⟩, ⟨d', hd'⟩⟩
    obtain ⟨b, hb⟩ := hsat (a * π ^ m' - a' * π ^ m) k (Ideal.mem_span_singleton.2
      ⟨c' * algebraMap A E π ^ m - c * algebraMap A E π ^ m', by
        simp only [map_sub, map_mul, map_pow]
        linear_combination algebraMap A E π ^ m * hc' - algebraMap A E π ^ m' * hc⟩)
    have h1 := congrArg f hb
    simp only [map_sub, map_mul, map_pow, map_natCast] at h1
    rw [← (hf.pow (m + m')).dvd_mul_right]
    exact ⟨d * f π ^ m' - d' * f π ^ m + f b, by
      linear_combination f π ^ m' * hd - f π ^ m * hd' + h1⟩
  have mono : ∀ j k x y, j ≤ k → Rel k x y → Rel j x y := by
    rintro j k x y hjk ⟨a, m, h1, h2⟩
    exact ⟨a, m, (pow_dvd_pow _ hjk).trans h1, (pow_dvd_pow _ hjk).trans h2⟩
  have ex1 : ∀ k x, ∃ y, Rel k x y := by
    intro k x
    obtain ⟨a, m, h⟩ := hd x k
    obtain ⟨u, hu⟩ := (hf.pow m).exists_left_inv
    refine ⟨f a * u, a, m, by simpa using Ideal.mem_span_singleton.1 h, ?_⟩
    rw [mul_assoc, hu]; simp
  have ex : ∀ x, ∃ y, ∀ k, Rel k x y := by
    intro x
    choose y hy using fun k => ex1 k x
    obtain ⟨L, hL⟩ := lim_of_precomplete (p : S) y fun m n hmn =>
      uniq m x _ _ (hy m) (mono _ _ _ _ hmn (hy n))
    refine ⟨L, fun k => ?_⟩
    obtain ⟨a, m, h1, h2⟩ := hy k
    refine ⟨a, m, h1, ?_⟩
    convert dvd_sub h2 ((hL k).mul_right (f π ^ m)) using 1
    ring
  choose F hF using ex
  have eqF : ∀ x y, (∀ k, Rel k x y) → F x = y := fun x y h => by
    rw [← sub_eq_zero]
    exact sep_of_haus (p : S) _ fun k => uniq k x _ _ (hF x k) (h k)
  have hA : ∀ a, F (algebraMap A E a) = f a := fun a => eqF _ _ fun k => ⟨a, 0, by simp, by simp⟩
  have hadd : ∀ x x', F (x + x') = F x + F x' := fun x x' => eqF _ _ fun k => by
    obtain ⟨a, m, h1, h2⟩ := hF x k
    obtain ⟨a', m', h1', h2'⟩ := hF x' k
    refine ⟨a * π ^ m' + a' * π ^ m, m + m', ?_, ?_⟩
    · convert dvd_add (h1.mul_right (algebraMap A E π ^ m')) (h1'.mul_right (algebraMap A E π ^ m)) using 1
      simp only [map_add, map_mul, map_pow]; ring
    · convert dvd_add (h2.mul_right (f π ^ m')) (h2'.mul_right (f π ^ m)) using 1
      simp only [map_add, map_mul, map_pow]; ring
  have hmul : ∀ x x', F (x * x') = F x * F x' := fun x x' => eqF _ _ fun k => by
    obtain ⟨a, m, h1, h2⟩ := hF x k
    obtain ⟨a', m', h1', h2'⟩ := hF x' k
    refine ⟨a * a', m + m', ?_, ?_⟩
    · convert dvd_add (h1.mul_right (x' * algebraMap A E π ^ m')) (h1'.mul_left (algebraMap A E a)) using 1
      simp only [map_mul]; ring
    · convert dvd_add (h2.mul_right (F x' * f π ^ m')) (h2'.mul_left (f a)) using 1
      simp only [map_mul]; ring
  refine ⟨{ toFun := F
            map_one' := by simpa using hA 1
            map_mul' := hmul
            map_zero' := by simpa using hA 0
            map_add' := hadd
            commutes' := fun r => ?_ }, hA⟩
  change F _ = _
  rw [IsScalarTower.algebraMap_apply O A E, hA, f.commutes]

def cst (O : Type) [CommRing O] (n : ℕ) : (ZMod n → O) →ₐ[O] LetA O n :=
  AlgHom.pi fun i => (Algebra.ofId O O⟦X⟧).comp (Pi.evalAlgHom O (fun _ : ZMod n => O) i)

theorem cst_apply {n : ℕ} (o : ZMod n → O) : cst O n o = fun i => C (o i) := by
  funext i
  simp [cst, Algebra.ofId_apply, PowerSeries.algebraMap_eq]

theorem let_unique {n : ℕ} (f f' : LetA O n →ₐ[O] S) (hπ : f letπ = f' letπ)
    (hc : ∀ o, f (cst O n o) = f' (cst O n o)) (hs : ∀ x : S, (∀ k, f letπ ^ k ∣ x) → x = 0) :
    f = f' := by
  have key : ∀ (k : ℕ) (a : LetA O n), f letπ ^ k ∣ f a - f' a := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      have ha : a = cst O n (fun i => constantCoeff (a i)) +
          letπ * fun i => PowerSeries.mk fun j => coeff (j + 1) (a i) := by
        funext i
        rw [cst_apply, add_comm]
        exact eq_X_mul_shift_add_const (a i)
      rw [ha, map_add, map_add, map_mul, map_mul, hc, ← hπ, pow_succ', add_sub_add_left_eq_sub, ← mul_sub]
      exact mul_dvd_mul_left _ (ih _)
  ext1 a
  rw [← sub_eq_zero]
  exact hs _ fun k => key k a

theorem let_exists {n : ℕ} [NeZero n] (y : S) [IsAdicComplete (Ideal.span {y}) S]
    (u : (ZMod n → O) →ₐ[O] S) :
    ∃ f : LetA O n →ₐ[O] S, f letπ = y ∧ ∀ o, f (cst O n o) = u o := by
  obtain ⟨ev, hev⟩ := GlobalTheory.Cyc.IoMap.algHom_exists (R := O) y
    (GlobalTheory.Per.AinfComplete.summ_of_precomplete y) (sep_of_haus y)
  have h1 : ∑ i, u (Pi.single i 1) = 1 := by
    rw [← map_sum, Finset.univ_sum_single (fun _ : ZMod n => (1 : O))]
    exact map_one u
  have h2 : ∀ i j, u (Pi.single i 1) * u (Pi.single j 1) = if i = j then u (Pi.single i 1) else 0 := by
    intro i j
    rw [← map_mul]
    split_ifs with h
    · subst h; rw [← Pi.single_mul, one_mul]
    · rw [← map_zero u]; congr 1
      funext k
      by_cases hk : k = i
      · subst hk; simp [h]
      · simp [hk]
  have h3 : ∀ o : ZMod n → O, ∑ i, u (Pi.single i 1) * algebraMap O S (o i) = u o := by
    intro o
    conv_rhs => rw [← Finset.univ_sum_single o, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, ← Algebra.smul_def, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
  have h4 : ∀ r : O, ev (C r) = algebraMap O S r := fun r => by
    rw [← ev.commutes, PowerSeries.algebraMap_eq]
  refine ⟨{ toFun := fun a => ∑ i, u (Pi.single i 1) * ev (a i)
            map_one' := by simpa using h1
            map_mul' := fun a b => ?_
            map_zero' := by simp
            map_add' := fun a b => by simp [mul_add, Finset.sum_add_distrib]
            commutes' := fun r => ?_ }, ?_, fun o => ?_⟩
  · rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [mul_mul_mul_comm, h2, if_pos rfl, Pi.mul_apply, map_mul]
    · intro j _ hj
      rw [mul_mul_mul_comm, h2, if_neg hj.symm, zero_mul]
    · simp
  · change ∑ i, u (Pi.single i 1) * ev (algebraMap O O⟦X⟧ r) = _
    rw [ev.commutes, ← Finset.sum_mul, h1, one_mul]
  · change ∑ i, u (Pi.single i 1) * ev X = _
    rw [hev, ← Finset.sum_mul, h1, one_mul]
  · change ∑ i, u (Pi.single i 1) * ev (cst O n o i) = _
    simp only [cst_apply, h4, h3]

end General

section Witt

theorem eq_teichmuller_of_frobenius {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    [PerfectRing R p] (x : WittVector p R) (hx : WittVector.frobenius x = x ^ p) :
    x = WittVector.teichmuller p (x.coeff 0) := by
  have h1 : ∀ k : ℕ, ∃ y : WittVector p R, y ^ p ^ k = x := by
    let σ := (WittVector.frobeniusEquiv p R).symm
    have h2 : ∀ z : WittVector p R, WittVector.frobenius z = z ^ p →
        (σ z) ^ p = z ∧ WittVector.frobenius (σ z) = (σ z) ^ p := by
      intro z hz
      have : (σ z) ^ p = z := by
        rw [← map_pow, ← hz]
        exact (WittVector.frobeniusEquiv p R).symm_apply_apply z
      exact ⟨this, this.symm ▸ (WittVector.frobeniusEquiv p R).apply_symm_apply z⟩
    have h3 : ∀ k : ℕ, ∃ y : WittVector p R, y ^ p ^ k = x ∧ WittVector.frobenius y = y ^ p := by
      intro k
      induction k with
      | zero => exact ⟨x, by simp, hx⟩
      | succ k ih =>
        obtain ⟨y, hy, hy'⟩ := ih
        exact ⟨σ y, by rw [pow_succ', pow_mul, (h2 y hy').1, hy], (h2 y hy').2⟩
    exact fun k => (h3 k).imp fun _ h => h.1
  rw [← sub_eq_zero]
  refine sep_of_haus ((p : ℕ) : WittVector p R) _ fun k => ?_
  obtain ⟨y, hy⟩ := h1 k
  have h4 : ((p : ℕ) : WittVector p R) ∣ y - WittVector.teichmuller p (y.coeff 0) := by
    rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    change WittVector.constantCoeff (y - WittVector.teichmuller p (y.coeff 0)) = 0
    rw [map_sub, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, sub_self]
  have h5 := dvd_sub_pow_of_dvd_sub h4 k
  have h6 : x.coeff 0 = y.coeff 0 ^ p ^ k := by
    rw [← hy]
    exact map_pow (WittVector.constantCoeff) y _
  rw [hy, ← map_pow, ← h6] at h5
  exact (pow_dvd_pow _ (Nat.le_succ k)).trans h5

variable {l : ℕ} [Fact l.Prime]

theorem binomialSeries_natMul (k : ℕ) (b : ℤ_[l]) :
    binomialSeries ℤ_[l] ((k : ℤ_[l]) * b) = binomialSeries ℤ_[l] b ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, binomialSeries_add, ih, pow_succ]

theorem binomial_eval {B : Type} [CommRing B] [CharP B l] (ψ : ℤ_[l]⟦X⟧ →+* B) (N a : ℕ) (c : ℤ_[l])
    (hc : (l : ℤ_[l]) ^ N ∣ c - a) (hz : (1 + ψ X) ^ l ^ N = 1) :
    ψ (binomialSeries ℤ_[l] c) = (1 + ψ X) ^ a := by
  obtain ⟨b, hb⟩ := hc
  have h1 : c = a + ((l ^ N : ℕ) : ℤ_[l]) * b := by push_cast; linear_combination hb
  have h2 : ψ X ^ l ^ N = 0 := by
    rw [add_pow_char_pow, one_pow] at hz
    linear_combination hz
  obtain ⟨h, hh⟩ : (X : ℤ_[l]⟦X⟧) ∣ binomialSeries ℤ_[l] b - 1 := by
    rw [X_dvd_iff]; simp
  have h3 : binomialSeries ℤ_[l] b = 1 + X * h := by linear_combination hh
  rw [h1, binomialSeries_add, binomialSeries_natMul, binomialSeries_nat, h3]
  simp only [map_mul, map_pow, map_add, map_one]
  rw [add_pow_char_pow, mul_pow, h2]
  simp

end Witt

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem εroot_pow (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem εroot_ne_one (s : ℕ) : AI.εroot s ≠ 1 := fun h =>
  AI.ε_ne_one (by rw [← εroot_pow AI s, h, one_pow])

theorem εroot_sub_not_unit (s : ℕ) : ¬ IsUnit (AI.εroot s - 1) := by
  intro h
  have h1 := (h.pow (l ^ s)).map (PreTilt.coeff 0)
  rw [sub_pow_char_pow, εroot_pow, one_pow, map_sub, AI.ε_coeff, AI.ζ_zero, map_one, map_one,
    sub_self] at h1
  exact not_isUnit_zero h1

theorem coeff_εroot (s n : ℕ) : PreTilt.coeff n (AI.εroot s) =
    Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (n + s)) := by
  rw [← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm]

theorem io_binomial (s : ℕ) (g : GQ l) (c : ℤ_[l]) (hc : (c : ℚ_[l]) = (P.χQ g : ℚ_[l]))
    (io : ℤ_[l]⟦X⟧ →ₐ[ℤ_[l]] Ainf l) (hio : GlobalTheory.Cyc.IsIo (AI.εroot s) io) :
    io (binomialSeries ℤ_[l] c) = WittVector.teichmuller l (AI.actT g (AI.εroot s)) := by
  have hφ := ((GlobalTheory.Cyc.IoMap.main l _ (εroot_sub_not_unit AI s)).2 io hio).1
  obtain ⟨hX, hmul, -⟩ := GlobalTheory.T.cyclotomicPowerSeriesAlgHom_action_laws l ℤ_[l]
  have hcyc : ∀ c, GlobalTheory.Cyc.cyc l ℤ_[l] c = binomialSeries ℤ_[l] c - 1 := fun c => by
    simp [GlobalTheory.Cyc.cyc]
  have h1 : GlobalTheory.Cyc.phi l ℤ_[l] (binomialSeries ℤ_[l] c) = binomialSeries ℤ_[l] c ^ l := by
    have := hmul (l : ℤ_[l]) c X
    rw [hX, hX, hcyc, hcyc, map_sub, map_one, binomialSeries_natMul, sub_left_inj] at this
    exact this
  have h2 := eq_teichmuller_of_frobenius (io (binomialSeries ℤ_[l] c)) (by rw [← hφ, h1, map_pow])
  rw [h2]
  congr 1
  have hz : ∀ m, P.ζQ m ^ l ^ m = 1 := by
    intro m
    induction m with
    | zero => simpa using P.ζQ_zero
    | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  have hz' : ∀ m, AI.ζ m ^ l ^ m = 1 := by
    intro m
    induction m with
    | zero => simpa using AI.ζ_zero
    | succ m ih => rw [pow_succ', pow_mul, AI.ζ_succ, ih]
  refine Perfection.ext fun n => ?_
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g (n + s) _ (hz (n + s))
  obtain ⟨y', h3, h4⟩ := AI.actT_coeff g _ n _ (coeff_εroot AI s n)
  have h5 : y' = AI.ζ (n + s) ^ a := by
    apply Subtype.ext
    rw [h3, SubmonoidClass.coe_pow, AI.ζ_eq, AI.actC_ext, hga]
    exact map_pow (algebraMap (Om l) (PadicComplex l)) _ _
  let ψ : ℤ_[l]⟦X⟧ →+* ModP (OC l) l :=
    (PreTilt.coeff n).comp ((WittVector.constantCoeff : Ainf l →+* OCb l).comp io.toRingHom)
  have hψ : 1 + ψ X = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (n + s)) := by
    change 1 + PreTilt.coeff n (WittVector.constantCoeff (io X)) = _
    rw [show io X = _ from hio, GlobalTheory.Cyc.IoMap.constantCoeff_teich_sub, map_sub, map_one, coeff_εroot]
    ring
  have hdiv : (l : ℤ_[l]) ^ (n + s) ∣ c - a := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_def,
      PadicInt.coe_sub, PadicInt.coe_natCast, hc]
    exact ha
  have h6 := binomial_eval ψ (n + s) a c hdiv (by rw [hψ, ← map_pow, hz', map_one])
  change ψ _ = PreTilt.coeff n _
  rw [h6, hψ, h4, h5]
  exact (map_pow _ _ _).symm

theorem eq_of_pow_coprime {M : Type} [CommMonoid M] {y y' : M} {a m : ℕ} (hm : 0 < m)
    (h : Nat.Coprime a m) (hy : y ^ m = 1) (hy' : y' ^ m = 1) (he : y ^ a = y' ^ a) : y = y' := by
  have h1 : a * a ^ (Nat.totient m - 1) ≡ 1 [MOD m] := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.totient_pos.2 hm)]
    exact Nat.ModEq.pow_totient h
  rw [← pow_one y, ← pow_one y', ← pow_eq_pow_of_modEq h1 hy, ← pow_eq_pow_of_modEq h1 hy', pow_mul,
    pow_mul, he]

theorem actT_tilt (g : GQ l) (c : Om l) (hg : g c = c) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m) (xb : OCb l)
    (h : IsTiltOf c m xb) : AI.actT g xb = xb := by
  refine Perfection.ext fun n => ?_
  obtain ⟨y, h1, h2, h3⟩ := h n
  obtain ⟨y', h4, h5⟩ := AI.actT_coeff g _ n _ h3
  have h2' : (y : PadicComplex l) ^ m = 1 := by simpa using congrArg Subtype.val h2
  have : y' = y := by
    apply Subtype.ext
    refine eq_of_pow_coprime (a := l ^ n) hm
      (Nat.Coprime.pow_left n (((Fact.out : l.Prime).coprime_iff_not_dvd).2 hl)) ?_ h2' ?_
    · rw [h4, ← map_pow, h2', map_one]
    · rw [h4, ← map_pow, h1, AI.actC_ext, hg]
  change PreTilt.coeff n _ = PreTilt.coeff n _
  rw [h5, h3, this]

theorem tilt_pow {c : Om l} {m : ℕ} {xb : OCb l} (h : IsTiltOf c m xb) (j : ℕ) :
    IsTiltOf (c ^ j) m (xb ^ j) := by
  intro k
  obtain ⟨y, h1, h2, h3⟩ := h k
  refine ⟨y ^ j, ?_, by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow], by rw [map_pow, h3, map_pow]⟩
  rw [SubmonoidClass.coe_pow, ← pow_mul, mul_comm, pow_mul, h1]
  exact (map_pow (algebraMap (Om l) (PadicComplex l)) _ _).symm

theorem eq_of_norm_sub_lt {a b : Om l} {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) (ha : a ^ m = 1)
    (hb : b ^ m = 1) (h : ‖a - b‖ < 1) : a = b := by
  have hn : ∀ x : Om l, x ^ m = 1 → ‖x‖ = 1 := fun x hx => by
    have := congrArg norm hx
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this
  have hb0 : b ≠ 0 := fun h0 => by simpa [h0] using hn b hb
  by_contra hne
  set z := a / b with hz
  have hz1 : z ^ m = 1 := by rw [hz, div_pow, ha, hb, div_one]
  have hz2 : ‖z - 1‖ < 1 := by
    rw [hz, div_sub_one hb0, norm_div, hn b hb, div_one]; exact h
  have hz3 : z - 1 ≠ 0 := fun h0 => hne ((div_eq_one_iff_eq hb0).1 (sub_eq_zero.1 h0))
  have hs : ∑ i ∈ Finset.range m, z ^ i = 0 := by
    have := geom_sum_mul z m
    rw [hz1, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hz3
  have hp : ∀ i : ℕ, ‖z ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show z ^ (i + 1) - 1 = z * (z ^ i - 1) + (z - 1) by ring]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hz2)
      rw [norm_mul, hn z hz1, one_mul]; exact ih
  have hq : ∀ k : ℕ, ‖∑ i ∈ Finset.range k, z ^ i - k‖ < 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, show ∑ i ∈ Finset.range k, z ^ i + z ^ k - ((k + 1 : ℕ) : Om l) =
        (∑ i ∈ Finset.range k, z ^ i - k) + (z ^ k - 1) by push_cast; ring]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ih (hp k))
  have h1 := hq m
  rw [hs, zero_sub, norm_neg, ← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap',
    Padic.norm_natCast_lt_one_iff] at h1
  exact hl h1

theorem sigma_root (K : FinExt l) (c : ↥(K0 K)) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m)
    (hc : (c : Om l) ^ m = 1) : (P.PD K).σ c = c ^ l := by
  have hc' : c ^ m = 1 := Subtype.ext (by simpa using hc)
  have hn : ‖(c : Om l)‖ = 1 := by
    have := congrArg norm hc
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this
  apply Subtype.ext
  refine eq_of_norm_sub_lt hm hl ?_ ?_ (by simpa using P.PD_σ K c hn.le)
  · have : (P.PD K).σ c ^ m = 1 := by rw [← map_pow, hc', map_one]
    simpa using congrArg Subtype.val this
  · have : (c ^ l) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hc', one_pow]
    simpa using congrArg Subtype.val this

def φRA (LL : FinExt l) : RA LL →ₐ[↥(OL LL)] RA LL :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (GlobalTheory.Cyc.IoMap.frobA l)

def gRA (LL : FinExt l) (g : GQ l) : RA LL →ₐ[↥(OL LL)] RA LL :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (AI.actWHom g).toAlgHom

theorem φRA_teich (LL : FinExt l) (x : OCb l) :
    φRA LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l x) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (x ^ l) := by
  rw [φRA, Algebra.TensorProduct.map_tmul]
  congr 1
  exact WittVector.map_teichmuller l (frobenius (OCb l) l) x

theorem gRA_teich (LL : FinExt l) (g : GQ l) (x : OCb l) :
    gRA AI LL g ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l x) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (AI.actT g x) := by
  rw [gRA, Algebra.TensorProduct.map_tmul]
  congr 1
  exact WittVector.map_teichmuller l (AI.actT g).toRingHom x

theorem inclR_φRA (LL : FinExt l) : (inclR LL).comp (φRA LL) = (φRW LL).comp (inclR LL) := by
  have h : (inclWA l).comp (GlobalTheory.Cyc.IoMap.frobA l) = (frobW l).comp (inclWA l) := by
    refine AlgHom.ext fun w => WittVector.ext fun k => ?_
    exact map_pow (algebraMap (OCb l) (Cb l)) (w.coeff k) l
  rw [inclR, φRA, φRW, ← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, h]

theorem inclR_gRA (LL : FinExt l) (g : GQ l) :
    (inclR LL).comp (gRA AI LL g) = (AI.gRW LL g).comp (inclR LL) := by
  have h : (inclWA l).comp (AI.actWHom g).toAlgHom = (AI.actWCbHom g).toAlgHom.comp (inclWA l) := by
    refine AlgHom.ext fun w => WittVector.ext fun k => ?_
    exact (autCb_alg l (AI.actT g) (w.coeff k)).symm
  rw [inclR, gRA, LocAinf.gRW, ← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, h]

theorem tmul_sub_one (LL : FinExt l) (w : Ainf l) :
    (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (w - 1) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w - 1 := by
  rw [TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]

theorem sepRA (LL : FinExt l) (e : OCb l) (he : ¬ IsUnit (e - 1)) (x : RA LL)
    (hx : ∀ k, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1) : RA LL) ^ k ∣ x) : x = 0 :=
  haveI := (GlobalTheory.HWL.TensorWitt.main l LL).2.2.2.2 e he
  sep_of_haus _ x hx

theorem isUnit_inclR (LL : FinExt l) (e : OCb l) (he : e ≠ 1) :
    IsUnit (inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1))) := by
  have h : IsUnit (inclW l (WittVector.teichmuller l e - 1)) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [inclW, WittVector.map_coeff, ← WittVector.constantCoeff_apply,
      GlobalTheory.Cyc.IoMap.constantCoeff_teich_sub]
    intro hz
    exact sub_ne_zero.2 he ((IsFractionRing.injective (OCb l) (Cb l)) (hz.trans (map_zero _).symm))
  exact h.map (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] RW LL)

theorem io_zl (LL : FinExt l) (n : ℕ) (e : OCb l) (he : ¬ IsUnit (e - 1))
    (f : LetA ↥(OL LL) n →ₐ[↥(OL LL)] RA LL)
    (hf : f letπ = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1))
    (io : ℤ_[l]⟦X⟧ →ₐ[ℤ_[l]] Ainf l) (hio : GlobalTheory.Cyc.IsIo e io) (a : ℤ_[l]⟦X⟧) :
    f (fun _ => PowerSeries.map (algebraMap ℤ_[l] ↥(OL LL)) a) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] io a := by
  let f1 : ℤ_[l]⟦X⟧ →ₐ[ℤ_[l]] RA LL :=
    { toRingHom := f.toRingHom.comp (zlA LL n)
      commutes' := fun r => by
        have : zlA LL n (algebraMap ℤ_[l] ℤ_[l]⟦X⟧ r) =
            algebraMap ↥(OL LL) (LetA ↥(OL LL) n) (algebraMap ℤ_[l] ↥(OL LL) r) := by
          funext i
          simp [zlA, PowerSeries.algebraMap_eq]
        change f (zlA LL n _) = _
        rw [this, f.commutes]
        rfl }
  let f2 : ℤ_[l]⟦X⟧ →ₐ[ℤ_[l]] RA LL :=
    (Algebra.TensorProduct.includeRight : Ainf l →ₐ[ℤ_[l]] RA LL).comp io
  have e1 : f1 X = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1) := by
    rw [← hf]
    change f (zlA LL n X) = _
    congr 1
    funext i
    simp [zlA, letπ]
  have e2 : f2 X = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1) := by
    rw [← show io X = _ from hio]
    rfl
  have := GlobalTheory.Cyc.IoMap.algHom_unique f1 f2 (e1.trans e2.symm) (by rw [e1]; exact sepRA LL e he)
  exact DFunLike.congr_fun this a

end Concrete

section Assemble

variable {O S : Type} [CommRing O] [CommRing S] [Algebra O S] {n : ℕ}

theorem algHom_C (f : O⟦X⟧ →ₐ[O] O⟦X⟧) (r : O) : f (C r) = C r := by
  rw [← PowerSeries.algebraMap_eq]; exact f.commutes r

theorem letφ_cst (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (o : ZMod n → O) :
    letφ φ₀ (cst O n o) = cst O n fun i => o (i - 1) := by
  rw [cst_apply, cst_apply]
  funext i
  exact algHom_C φ₀ _

theorem letγ_cst (g₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (o : ZMod n → O) : letγ g₀ (cst O n o) = cst O n o := by
  rw [cst_apply]
  funext i
  exact algHom_C g₀ _

def shift (O : Type) [CommRing O] (n : ℕ) : (ZMod n → O) →ₐ[O] (ZMod n → O) :=
  AlgHom.pi fun i => Pi.evalAlgHom O (fun _ : ZMod n => O) (i - 1)

theorem comm_φ (p : ℕ) (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (h0 : φ₀ X = (1 + X) ^ p - 1) (f : LetA O n →ₐ[O] S)
    (u : (ZMod n → O) →ₐ[O] S) (hu : ∀ o, f (cst O n o) = u o) (φ : S →ₐ[O] S) (t : S)
    (ht : f letπ = t - 1) (hφ : φ t = t ^ p) (hc : u.comp (shift O n) = φ.comp u)
    (hs : ∀ x : S, (∀ k, (t ^ p - 1) ^ k ∣ x) → x = 0) : f.comp (letφ φ₀) = φ.comp f := by
  have h1 : (f.comp (letφ φ₀)) letπ = t ^ p - 1 := by
    have : letφ φ₀ (letπ : LetA O n) = (1 + letπ) ^ p - 1 := funext fun i => h0
    rw [AlgHom.comp_apply, this, map_sub, map_pow, map_add, map_one, ht]
    ring
  refine let_unique _ _ ?_ (fun o => ?_) (by rw [h1]; exact hs)
  · rw [h1, AlgHom.comp_apply, ht, map_sub, map_one, hφ]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, letφ_cst, hu, hu]
    exact DFunLike.congr_fun hc o

theorem comm_γ (g₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (b : O⟦X⟧) (h0 : g₀ X = b - 1) (f : LetA O n →ₐ[O] S)
    (u : (ZMod n → O) →ₐ[O] S) (hu : ∀ o, f (cst O n o) = u o) (g : S →ₐ[O] S) (t t' : S)
    (ht : f letπ = t - 1) (hb : f (fun _ => b) = t') (hg : g t = t') (hc : u = g.comp u)
    (hs : ∀ x : S, (∀ k, (t' - 1) ^ k ∣ x) → x = 0) : f.comp (letγ g₀) = g.comp f := by
  have h1 : (f.comp (letγ g₀)) letπ = t' - 1 := by
    have : letγ g₀ (letπ : LetA O n) = (fun _ => b) - 1 := funext fun i => h0
    rw [AlgHom.comp_apply, this, map_sub, map_one, hb]
  refine let_unique _ _ ?_ (fun o => ?_) (by rw [h1]; exact hs)
  · rw [h1, AlgHom.comp_apply, ht, map_sub, map_one, hg]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, letγ_cst, hu]
    exact DFunLike.congr_fun hc o

end Assemble

section Layer

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s}

theorem assemble (R : WSer Γ) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] (inclR : RA →ₐ[O] RW) (φR : RW →ₐ[O] RW) (gR : G → (RW →ₐ[O] RW)) (πA : RA)
    (φA : RA →ₐ[O] RA) (gA : G → (RA →ₐ[O] RA)) (hφ : inclR.comp φA = φR.comp inclR)
    (hg : ∀ g, inclR.comp (gA g) = (gR g).comp inclR)
    (hc : IsAdicComplete (Ideal.span {((PD.p : ℕ) : RW)}) RW) (io : LetA O n →ₐ[O] RA)
    (hπ : io letπ = πA) (hu : IsUnit (inclR πA)) (h1 : io.comp (letφ R.φ₀) = φA.comp io)
    (h2 : ∀ g, io.comp (letγ (R.γ₀ (Γ.resΓ g))) = (gA g).comp io) :
    ∃ I : WIo R RA RW inclR φR gR πA, I.io = io := by
  obtain ⟨F, hF⟩ := ext_exists PD.p letπ R.EE_dense R.EE_sat (inclR.comp io)
    (by rw [AlgHom.comp_apply, hπ]; exact hu)
  refine ⟨⟨io, hπ, F, hF, ?_, fun g => ?_⟩, rfl⟩
  · refine ext_unique PD.p letπ R.EE_π R.EE_dense (sep_of_haus _) (F.comp R.φE) (φR.comp F) fun a => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, R.φE_ext, hF, hF]
    exact (congrArg inclR (DFunLike.congr_fun h1 a)).trans (DFunLike.congr_fun hφ (io a))
  · refine ext_unique PD.p letπ R.EE_π R.EE_dense (sep_of_haus _) (F.comp (R.γE (Γ.resΓ g)))
      ((gR g).comp F) fun a => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, R.γE_ext, hF, hF]
    exact (congrArg inclR (DFunLike.congr_fun (h2 g) a)).trans (DFunLike.congr_fun (hg g) (io a))

end Layer

end GlobalTheory.HWL.IoLayer
