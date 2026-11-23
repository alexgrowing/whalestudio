import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresTr
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresDl
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresMono
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumAlg
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.WdVal
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PEvHom
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.Cl1

private lemma dl_mul {R : Type} [CommRing R] {f g : PowerSeries R} (hf : IsUnit f) (hg : IsUnit g) :
    dl (f * g) = dl f + dl g := by
  obtain ⟨u, rfl⟩ := hf
  obtain ⟨w, rfl⟩ := hg
  unfold dl dd
  rw [← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, Ring.inverse_unit, Units.val_mul, Derivation.leibniz,
    mul_inv_rev, Units.val_mul, smul_eq_mul, smul_eq_mul]
  have h1 := u.mul_inv
  have h2 := w.mul_inv
  linear_combination ((1 + PowerSeries.X) * (PowerSeries.derivative R) (w : PowerSeries R) * ((w⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)) * h1 +
    ((1 + PowerSeries.X) * (PowerSeries.derivative R) (u : PowerSeries R) * ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)) * h2

private lemma der_eval {R : Type} [CommRing R] (P : Polynomial R) :
    PowerSeries.derivative R (P.eval₂ PowerSeries.C (1 + PowerSeries.X)) =
      (Polynomial.derivative P).eval₂ PowerSeries.C (1 + PowerSeries.X) := by
  induction P using Polynomial.induction_on' with
  | add f g hf hg => simp [Polynomial.eval₂_add, hf, hg]
  | monomial n a =>
    rw [Polynomial.derivative_monomial, Polynomial.eval₂_monomial, Polynomial.eval₂_monomial, Derivation.leibniz,
      Derivation.leibniz_pow]
    simp
    ring

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {j : Ω →+* Qbar l}

private lemma ser_mul (Φ : Fr l A j) (P Q : Polynomial (R0 A)) : Φ.ser (P * Q) = Φ.ser P * Φ.ser Q := by
  unfold Fr.ser
  rw [Polynomial.map_mul, Polynomial.eval₂_mul]

private lemma eps_ser (Φ : Fr l A j) (ε : PowerSeries Φ.R →+* ℂ_[l]) (w : Ω)
    (hC : ∀ x, ε (PowerSeries.C x) = Φ.jh x) (hz : ε (1 + PowerSeries.X) = algebraMap (PadicAlgCl l) ℂ_[l] (j w))
    (P : Polynomial (R0 A)) :
    ε (Φ.ser P) = algebraMap (PadicAlgCl l) ℂ_[l] (j ((P.map (R0 A).subtype).eval w)) := by
  unfold Fr.ser
  induction P using Polynomial.induction_on' with
  | add f g hf hg => simp only [Polynomial.map_add, Polynomial.eval₂_add, Polynomial.eval_add, map_add, hf, hg]
  | monomial n a =>
    simp only [Polynomial.map_monomial, Polynomial.eval₂_monomial, Polynomial.eval_monomial, map_mul, map_pow, hC, hz,
      Φ.jh_comp_incl]
    rfl

private lemma eps_dl (Φ : Fr l A j) (ε : PowerSeries Φ.R →+* ℂ_[l]) (w : Ω)
    (hC : ∀ x, ε (PowerSeries.C x) = Φ.jh x) (hz : ε (1 + PowerSeries.X) = algebraMap (PadicAlgCl l) ℂ_[l] (j w))
    (P : Polynomial (R0 A)) (hP : IsUnit (Φ.ser P)) :
    ε (dl (Φ.ser P)) = algebraMap (PadicAlgCl l) ℂ_[l]
      (j (w * (Polynomial.derivative (P.map (R0 A).subtype)).eval w / (P.map (R0 A).subtype).eval w)) := by
  have h1 : PowerSeries.derivative Φ.R (Φ.ser P) = Φ.ser (Polynomial.derivative P) := by
    unfold Fr.ser
    rw [der_eval, Polynomial.derivative_map]
  have h2 : ε (Ring.inverse (Φ.ser P)) = (ε (Φ.ser P))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, Ring.inverse_mul_cancel _ hP, map_one]
  unfold dl dd
  rw [map_mul, map_mul, h1, h2, hz, eps_ser Φ ε w hC hz, eps_ser Φ ε w hC hz, Polynomial.derivative_map]
  simp only [map_div₀, map_mul, div_eq_mul_inv, map_inv₀]

private lemma lam_act (Φ : Fr l A j) {c : Coef l} (β : Bas c) (a : c.O) (x : Fin β.d → Φ.R) :
    Φ.lam β (fun i => ∑ k, algebraMap ℤ_[l] Φ.R (β.mat a i k) * x k) =
      algebraMap (PadicAlgCl l) ℂ_[l] (a : PadicAlgCl l) * Φ.lam β x := by
  have h : ∀ k, ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.mat a i k) = (a : PadicAlgCl l) * β.val k := by
    intro k
    have h1 := β.e.sum_repr (a * β.e k)
    have h2 := congrArg (fun y : c.O => (y : PadicAlgCl l)) h1
    simp only [Bas.val, Bas.mat, Algebra.leftMulMatrix_eq_repr_mul]
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, ← Algebra.smul_def]
    rfl
  unfold Fr.lam
  simp only [map_sum, map_mul, Finset.mul_sum, Φ.jh_alg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← map_mul, ← h k, map_sum, Finset.sum_mul]
  simp only [map_mul, mul_assoc]

private lemma tw_succ (Φ : Fr l A j) {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ_[l]) (D : Fin d → PowerSeries Φ.R)
    (h : ∀ i, Φ.tw 1 (D i) = Φ.act M D i) (m n : ℕ) (i : Fin d) :
    (Φ.tw (m + 1) (D i)).coeff n = ∑ k, algebraMap ℤ_[l] Φ.R (M i k) * (Φ.tw m (D k)).coeff n := by
  haveI := Φ.fl.complete
  have h1 := congrArg (PowerSeries.coeff n) (h i)
  simp only [Fr.tw, Fr.act, PowerSeries.coeff_map, pow_one, map_sum, PowerSeries.coeff_C_mul] at h1 ⊢
  rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, h1, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  congr 1
  exact RingHom.congr_fun (padicHom_ext l ((((Φ.σ.symm : Φ.R ≃+* Φ.R) : Φ.R →+* Φ.R) ^ m).comp (algebraMap ℤ_[l] Φ.R))
    (algebraMap ℤ_[l] Φ.R)) _

private lemma lam_tw (Φ : Fr l A j) {c : Coef l} (β : Bas c) (a : c.O) (D : Fin β.d → PowerSeries Φ.R)
    (h : ∀ i, Φ.tw 1 (D i) = Φ.act (β.mat a) D i) (m n : ℕ) :
    Φ.lam β (fun i => (Φ.tw m (D i)).coeff n) =
      algebraMap (PadicAlgCl l) ℂ_[l] (a : PadicAlgCl l) ^ m * Φ.lam β (fun i => (D i).coeff n) := by
  induction m with
  | zero => simp [Fr.tw, RingHom.one_def]
  | succ m ih =>
    simp only [tw_succ Φ _ D h]
    rw [lam_act, ih]; ring

private lemma lc_norm {R : Type} [CommRing R] {m n : ℕ} (ε : lev R l m →+* ℂ_[l]) (hε : ∀ y, ‖ε y‖ ≤ 1)
    {f g : PowerSeries R} (h : LC l m n f g) : ‖ε (ev R l m f) - ε (ev R l m g)‖ ≤ ‖(l : ℂ_[l]) ^ n‖ := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  rw [← map_sub, ← hy, map_mul, norm_mul, map_pow, map_natCast]
  exact mul_le_of_le_one_left (norm_nonneg _) (hε y)

private lemma pow_le {n n' : ℕ} (h : n ≤ n') : ‖(l : ℂ_[l]) ^ n'‖ ≤ ‖(l : ℂ_[l]) ^ n‖ := by
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) h

private lemma norm_alg (x : PadicAlgCl l) : ‖algebraMap (PadicAlgCl l) ℂ_[l] x‖ = ‖x‖ := by
  exact norm_algebraMap' _ x

private lemma sum_le {K : Type} [NormedField K] [IsUltrametricDist K] {ι : Type} (s : Finset ι) (o x : ι → K) {r : ℝ} (hr : 0 ≤ r)
    (ho : ∀ i, ‖o i‖ ≤ 1) (hx : ∀ i, ‖x i‖ ≤ r) : ‖∑ i ∈ s, o i * x i‖ ≤ r := by
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun i _ => ?_
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (ho i)).trans (hx i)

private lemma add_le {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖x + y‖ ≤ r := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

private lemma coef_le {c : Coef l} (β : Bas c) (a : c.O) : ‖(a : PadicAlgCl l)‖ ≤ 1 := by
  have h2 := congrArg (fun y : c.O => (y : PadicAlgCl l)) (β.e.sum_repr a)
  simp only [AddSubmonoidClass.coe_finset_sum] at h2
  have h3 : (a : PadicAlgCl l) = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr a i) := by
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, ← Algebra.smul_def]
    rfl
  rw [h3]
  refine sum_le _ _ _ zero_le_one ((pBasEx l c).2 β).1 fun i => ?_
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  exact PadicInt.norm_le_one _

private lemma pv_mul (P Q : Polynomial (R0 A)) (z : Ω) : pv (P * Q) z = pv P z * pv Q z := by
  unfold pv
  rw [Polynomial.eval₂_mul]

private lemma bpres_mul [IsAlgClosure ℚ Ω] (hl : l ≠ 2) (hA : OverL l A) {c : Coef l} (β : Bas c) {ζ : ℕ → Ω} (hζ : Roots l ζ)
    {Z Z' : Sy Ω l} {m n : ℕ} {P P' : Fin β.d → Polynomial (R0 A)} (h : BPres β A ζ Z m n P) (h' : BPres β A ζ Z' m n P') :
    BPres β A ζ (fun r s x => Z r s x + Z' r s x) m n (fun i => P i * P' i) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨-, -, h3', -, h5'⟩ := h'
  refine ⟨h1, h2, fun i => ?_, h4, fun s hs hc hz => ?_⟩
  · simp only [pv_mul, mul_inv]
    exact ⟨A.mul_mem _ _ (h3 i).1 (h3' i).1, mul_ne_zero (h3 i).2.1 (h3' i).2.1, A.mul_mem _ _ (h3 i).2.2 (h3' i).2.2⟩
  · obtain ⟨k, hk, hk2⟩ := h5 s hs hc hz
    obtain ⟨k', hk', hk2'⟩ := h5' s hs hc hz
    refine ⟨fun i => k i + k' i, fun i => ?_, ?_⟩
    · simp only [pv_mul]
      exact ((pKumAlg l hl Ω A hA ζ hζ m n h2 s ⟨hs, hc⟩).1 _ _ _ _ (hk i) (hk' i)).1
    · haveI : NeZero (l ^ n) := ⟨(pow_pos (Fact.out : l.Prime).pos n).ne'⟩
      have e : ‖∑ i, β.val i * (((k i).val : Qbar l) + ((k' i).val : Qbar l) - ((k i + k' i).val : Qbar l))‖ ≤
          ‖((l : ℕ) : Qbar l) ^ n‖ := by
        refine sum_le _ _ _ (norm_nonneg _) h4 fun i => ?_
        have e1 := congrArg (Nat.cast : ℕ → Qbar l) (Nat.mod_add_div ((k i).val + (k' i).val) (l ^ n))
        rw [← ZMod.val_add] at e1
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at e1
        rw [← e1, add_sub_cancel_left, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
      unfold Cg at hk2 hk2' ⊢
      convert add_le (add_le hk2 hk2') e using 2
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring

private lemma htv_expand {ι : Type} [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) (ζ : Ω) (d b b' : ℕ) (hd : 0 < d)
    (h : ζ ^ b' = (ζ ^ b) ^ d) :
    htv j ζ (fun i => Polynomial.expand Ω d (P i)) o b = (d : Qbar l) * htv j ζ P o b' := by
  unfold htv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Polynomial.derivative_expand, h, Polynomial.eval_mul, Polynomial.expand_eval, Polynomial.expand_eval,
    ← map_natCast j, mul_left_comm (j _), ← map_mul]
  congr 2
  simp only [Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X, Nat.add_sub_cancel]
  ring

end UpperTheory.Kd.C7.Cl1

open UpperTheory.Kd.C7.Cl1 in
theorem UpperTheory.Kd.C7.pClause1 :
    UpperTheory.Kd.C7.SClause1 := by
  intro l _ hl Ω _ _ _ A hA j Φ c β ζ hζ hj Z hZ d₀ hd D a Gs v vm hRep hFr hGs hlam hvm e₀
  obtain ⟨c₁, m₁, hR⟩ := hRep
  refine ⟨c₁ + e₀ + 1, m₁ + 1, fun m hm P hP b => ?_⟩
  have hm1 : 1 ≤ m := by omega
  obtain ⟨S, hS, hSD⟩ := hR m (by omega)
  set n := m - (c₁ + e₀ + 1) with hn
  have hd0 : 0 < d₀ := Nat.pos_of_ne_zero (by rintro rfl; exact hd (dvd_zero l))
  have hP' : BPres β A ζ Z m n P := pPresMono l hl Ω A hA c β ζ hζ Z Z m _ n P (by omega) (fun s _ => by simp [Cg]) hP
  have hS' : BPres β A ζ (sharp d₀ hd Z) m n S :=
    pPresMono l hl Ω A hA c β ζ hζ _ _ m _ n S (by omega) (fun s _ => by simp [Cg]) hS
  have hE := pPresTr l hl Ω A hA c β ζ hζ Z hZ d₀ hd m n P hP'
  have hM : BPres β A ζ Z m n (fun i => S i * Polynomial.expand (R0 A) d₀ (P i)) :=
    pPresMono l hl Ω A hA c β ζ hζ _ _ m n n _ le_rfl (fun s _ => by simp [Cg, sharp]) (bpres_mul hl hA β hζ hS' hE)
  have hU := pWD l hl Ω A hA j Φ ζ hζ m hm1
  have uP : ∀ i, IsUnit (Φ.ser (P i)) := fun i => (hU _).2 (hP'.2.2.1 i)
  have uS : ∀ i, IsUnit (Φ.ser (S i)) := fun i => (hU _).2 (hS'.2.2.1 i)
  have uE : ∀ i, IsUnit (Φ.ser (Polynomial.expand (R0 A) d₀ (P i))) := fun i => (hU _).2 (hE.2.2.1 i)
  have hdl := fun i => (pPresDl l hl Ω A hA j Φ c β ζ hζ Z m n hm1 _ _ hP' hM i).2
  haveI : NeZero (l ^ m) := ⟨(pow_pos (Fact.out : l.Prime).pos m).ne'⟩
  set w : Ω := ζ m ^ (b : ZMod (l ^ m)).val with hw
  have hwp : IsPrimitiveRoot w (l ^ m) := (hζ m).1.pow_of_coprime _ (ZMod.val_coe_unit_coprime b)
  have hzp : IsPrimitiveRoot (algebraMap (PadicAlgCl l) ℂ_[l] (j w)) (l ^ m) :=
    (hwp.map_of_injective j.injective).map_of_injective (algebraMap (PadicAlgCl l) ℂ_[l]).injective
  obtain ⟨ε, hε1, hεC, hεz, hεt⟩ := pEvHom l hl Ω A hA j Φ m hm1 _ hzp
  have key := fun Q hQ => eps_dl Φ (ε.comp (ev Φ.R l m)) w hεC hεz Q hQ
  simp only [RingHom.comp_apply] at key
  have hβ : ∀ i, ‖algebraMap (PadicAlgCl l) ℂ_[l] (β.val i)‖ ≤ 1 := fun i => by rw [norm_alg]; exact hP.2.2.2.1 i
  have hh : ∀ Q : Fin β.d → Polynomial (R0 A), (∀ i, IsUnit (Φ.ser (Q i))) →
      algebraMap (PadicAlgCl l) ℂ_[l] (htv j (ζ m) (fun i => (Q i).map (R0 A).subtype) β.val (b : ZMod (l ^ m)).val) =
      ∑ i, algebraMap (PadicAlgCl l) ℂ_[l] (β.val i) * ε (ev Φ.R l m (dl (Φ.ser (Q i)))) := by
    intro Q hQ
    unfold htv
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, key _ (hQ i)]
  have hex : (d₀ : Qbar l) * htv j (ζ m) (fun i => (P i).map (R0 A).subtype) β.val
      ((b * un d₀ hd m : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)).val =
      htv j (ζ m) (fun i => (Polynomial.expand (R0 A) d₀ (P i)).map (R0 A).subtype) β.val (b : ZMod (l ^ m)).val := by
    simp only [Polynomial.map_expand]
    refine (htv_expand _ _ _ _ _ _ hd0 ?_).symm
    rw [← pow_mul, Units.val_mul, un, ZMod.coe_unitOfCoprime, ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod_mod]
    exact (pow_eq_pow_mod _ (hζ m).1.pow_eq_one).symm
  set ι := algebraMap (PadicAlgCl l) ℂ_[l] with hι
  have hr := norm_nonneg ((l : ℂ_[l]) ^ n)
  have e1 : ‖∑ i, ι (β.val i) * (ε (ev Φ.R l m (dl (Φ.ser (P i)))) -
      ε (ev Φ.R l m (dl (Φ.ser (S i * Polynomial.expand (R0 A) d₀ (P i))))))‖ ≤ ‖(l : ℂ_[l]) ^ n‖ :=
    sum_le _ _ _ hr hβ fun i => (lc_norm ε hε1 (hdl i)).trans (pow_le (by omega))
  have e2 : ‖∑ i, ι (β.val i) * (ε (ev Φ.R l m (dl (Φ.ser (S i)))) - ε (ev Φ.R l m (Φ.tw m (D i))))‖ ≤ ‖(l : ℂ_[l]) ^ n‖ :=
    sum_le _ _ _ hr hβ fun i => by
      rw [norm_sub_rev]; exact (lc_norm ε hε1 (hSD i)).trans (pow_le (by omega))
  have e3 : ‖∑ i, ι (β.val i) * (ε (ev Φ.R l m (Φ.tw m (D i))) -
      ∑ k ∈ Finset.range (l ^ (3 * m)), Φ.jh ((Φ.tw m (D i)).coeff k) * (ι (j w) - 1) ^ k)‖ ≤ ‖(l : ℂ_[l]) ^ n‖ :=
    sum_le _ _ _ hr hβ fun i => (hεt _).trans (pow_le (by omega))
  have ht : ‖tval Gs (l ^ (3 * m)) (j w)‖ ≤ 1 := by
    refine sum_le _ _ _ zero_le_one hGs fun k => ?_
    rw [norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    rw [sub_eq_add_neg]
    refine add_le ?_ (by simp)
    rw [← norm_alg, ← hι, ← hεz]
    exact hε1 _
  have e4 : ‖(v - ι (vm m)) * (ι a ^ m * ι (tval Gs (l ^ (3 * m)) (j w)))‖ ≤ ‖(l : ℂ_[l]) ^ n‖ := by
    rw [norm_mul, norm_sub_rev]
    refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans ((hvm m).trans (pow_le (by omega)))
    rw [norm_mul, norm_pow, norm_alg, norm_alg]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (coef_le β a)) (norm_nonneg _) ht
  have e5 : ∑ i, ι (β.val i) * ∑ k ∈ Finset.range (l ^ (3 * m)), Φ.jh ((Φ.tw m (D i)).coeff k) * (ι (j w) - 1) ^ k =
      v * (ι a ^ m * ι (tval Gs (l ^ (3 * m)) (j w))) := by
    simp only [tval, Finset.mul_sum, map_sum, map_mul, map_pow, map_sub, map_one]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := lam_tw Φ β a D hFr m k
    rw [hlam, Fr.lam] at h1
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, h1]
    ring
  unfold Cg
  rw [hex, ← map_pow j, ← hw, ← norm_alg, ← norm_alg ((l : PadicAlgCl l) ^ n), ← hι, map_pow ι, map_natCast, map_sub, map_sub, hh P uP, hh _ uE]
  refine le_of_eq_of_le (congrArg _ ?_) (add_le (add_le (add_le e1 e2) e3) e4)
  simp only [ser_mul, dl_mul (uS _) (uE _), map_add, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, e5,
    map_mul, map_pow]
  ring
