import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.HkApply
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.BandOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompBound
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.KillOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic PositivityTheory.Rg.Fx UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

private theorem exists_esymm (n : ℕ) (c : Fin n → ℂ) :
    ∃ y : Fin n → ℂ, ∀ i : Fin n, MvPolynomial.aeval y (MvPolynomial.esymm (Fin n) ℂ ((i : ℕ) + 1)) = c i := by
  classical
  let a : Fin n → ℂ := fun k => (-1) ^ (n - (k : ℕ)) * c (Fin.rev k)
  let q : Polynomial ℂ := ∑ k : Fin n, Polynomial.C (a k) * Polynomial.X ^ (k : ℕ)
  have hq : q.degree < n := Polynomial.degree_sum_fin_lt a
  let p : Polynomial ℂ := Polynomial.X ^ n + q
  have hm : p.Monic := Polynomial.monic_X_pow_add hq
  have hd : p.natDegree = n := by
    have h0 : q.degree < (Polynomial.X ^ n : Polynomial ℂ).degree := by rwa [Polynomial.degree_X_pow]
    simp only [p]
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt h0, Polynomial.natDegree_X_pow]
  have hs : Multiset.card p.roots = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hl : p.roots.toList.length = n := by rw [Multiset.length_toList, hs, hd]
  refine ⟨fun j => p.roots.toList.get (j.cast hl.symm), fun i => ?_⟩
  have hy : (Finset.univ : Finset (Fin n)).val.map (fun j => p.roots.toList.get (j.cast hl.symm)) = p.roots := by
    rw [Fin.univ_val_map]
    conv_rhs => rw [← Multiset.coe_toList p.roots]
    congr 1
    refine List.ext_get (by simpa using hl.symm) fun k h1 h2 => ?_
    simp
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, hy]
  have hi : ((Fin.rev i : Fin n) : ℕ) + ((i : ℕ) + 1) = n := by
    have := i.2
    rw [Fin.val_rev]; omega
  have hcoef := Polynomial.coeff_eq_esymm_roots_of_card hs (k := ((Fin.rev i : Fin n) : ℕ)) (by omega)
  have e1 : p.natDegree - ((Fin.rev i : Fin n) : ℕ) = (i : ℕ) + 1 := by omega
  rw [e1, hm.leadingCoeff, one_mul] at hcoef
  have e2 : p.coeff ((Fin.rev i : Fin n) : ℕ) = (-1) ^ ((i : ℕ) + 1) * c i := by
    have h3 : (Polynomial.X ^ n : Polynomial ℂ).coeff ((Fin.rev i : Fin n) : ℕ) = 0 := by
      rw [Polynomial.coeff_X_pow, if_neg (by omega)]
    have h4 : q.coeff ((Fin.rev i : Fin n) : ℕ) = a (Fin.rev i) := by
      simp only [q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      rw [Finset.sum_eq_single (Fin.rev i)]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (Fin.ext h.symm)), mul_zero]
      · simp
    simp only [p, Polynomial.coeff_add, h3, zero_add, h4, a, Fin.rev_rev]
    congr 2
    omega
  rw [e2] at hcoef
  have h5 : ((-1 : ℂ) ^ ((i : ℕ) + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_left_cancel₀ h5 hcoef).symm

private theorem aeval_blockE_injective (τ : Type) (n : ℕ) :
    Function.Injective (MvPolynomial.aeval blockE : MvPolynomial (τ × Fin n) ℂ →ₐ[ℂ] MvPolynomial (τ × Fin n) ℂ) := by
  refine (injective_iff_map_eq_zero _).2 fun P hP => MvPolynomial.funext fun c => ?_
  choose y hy using fun t : τ => exists_esymm n fun i => c (t, i)
  let x : τ × Fin n → ℂ := fun p => y p.1 p.2
  have h : (MvPolynomial.aeval x : MvPolynomial (τ × Fin n) ℂ →ₐ[ℂ] ℂ).comp (MvPolynomial.aeval blockE) = MvPolynomial.aeval c := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, blockE, MvPolynomial.aeval_rename]
    exact hy p.1 p.2
  have h2 := DFunLike.congr_fun h P
  rw [AlgHom.comp_apply, hP, map_zero] at h2
  rw [map_zero, ← MvPolynomial.coe_aeval_eq_eval]
  exact h2.symm

private theorem vars_of_gen {τ κ : Type} [Fintype τ] {n : ℕ} {F : KF (τ × Fin n) κ}
    {G : MvPolynomial κ (MvPolynomial (τ × Fin n) ℂ)} {k : ℕ}
    (h : MvPolynomial.map (MvPolynomial.aeval blockE : MvPolynomial (τ × Fin n) ℂ →ₐ[ℂ] MvPolynomial (τ × Fin n) ℂ).toRingHom G =
      pieceK k F) {β : κ →₀ ℕ} (hβ : β ∈ G.support) : β ∈ F.support := by
  classical
  by_contra hF
  have h1 : (pieceK k F).coeff β = 0 := by
    rw [pieceK, MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [MvPolynomial.coeff_monomial, if_neg (fun e : b = β => hF (e ▸ hb))]
  rw [← h, MvPolynomial.coeff_map] at h1
  exact MvPolynomial.mem_support_iff.1 hβ ((injective_iff_map_eq_zero _).1 (aeval_blockE_injective τ n) _ h1)

section Ops

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

private def Q (S : Set (Pl E)) (C : ℝ) (ψ : Sm E n) : Prop := Band C ψ ∧ Sph S ψ

private def Op (S : Set (Pl E)) (C : ℝ) (k : GA E n) (T : Module.End ℂ (Sm E n)) : Prop :=
  ∀ ψ, Q S C ψ → Q S C (T ψ) ∧ rt E n k (T ψ) = T (rt E n k ψ)

variable {S : Set (Pl E)} {C : ℝ} {k : GA E n}

private theorem Q_zero (hb : BandOps E) (hC : 0 ≤ C) : Q S C (0 : Sm E n) :=
  ⟨(hb n C hC).1, fun w _ x _ => map_zero _⟩

private theorem Q_add (hb : BandOps E) (hC : 0 ≤ C) {ψ χ : Sm E n} (h : Q S C ψ) (h' : Q S C χ) : Q S C (ψ + χ) :=
  ⟨((hb n C hC).2 ψ h.1).1 χ h'.1, fun w hw x hx => by rw [map_add, h.2 w hw x hx, h'.2 w hw x hx]⟩

private theorem Op_zero (hb : BandOps E) (hC : 0 ≤ C) : Op S C k (0 : Module.End ℂ (Sm E n)) := fun ψ _ =>
  ⟨Q_zero hb hC, by simp⟩

private theorem Op_one : Op S C k (1 : Module.End ℂ (Sm E n)) := fun ψ h => ⟨h, rfl⟩

private theorem Op_add (hb : BandOps E) (hC : 0 ≤ C) {T T' : Module.End ℂ (Sm E n)} (h : Op S C k T) (h' : Op S C k T') :
    Op S C k (T + T') := fun ψ hψ =>
  ⟨Q_add hb hC (h ψ hψ).1 (h' ψ hψ).1, by
    rw [LinearMap.add_apply, LinearMap.add_apply, map_add, (h ψ hψ).2, (h' ψ hψ).2]⟩

private theorem Op_sum (hb : BandOps E) (hC : 0 ≤ C) {ι : Type*} (s : Finset ι) {T : ι → Module.End ℂ (Sm E n)}
    (h : ∀ i ∈ s, Op S C k (T i)) : Op S C k (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Op_zero hb hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Op_add hb hC (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem Q_rt (hh : HkOps E) (hb : BandOps E) (hC : 0 ≤ C) (k : KA E n) {ψ : Sm E n} (h : Q S C ψ) :
    Q S C (rt E n (k : GA E n) ψ) :=
  ⟨((hb n C hC).2 ψ h.1).2.2.2.1 _, fun w hw =>
    ((((hh n w 0).2.2.2 S ψ hw h.2).2.2.1 k).1) w hw⟩

private theorem Op_mul {k : KA E n} (hh : HkOps E) (hb : BandOps E) (hC : 0 ≤ C) {T T' : Module.End ℂ (Sm E n)}
    (h : Op S C (k : GA E n) T) (h' : Op S C (k : GA E n) T') : Op S C (k : GA E n) (T * T') := fun ψ hψ =>
  ⟨(h _ (h' ψ hψ).1).1, by
    rw [Module.End.mul_apply, Module.End.mul_apply, (h _ (h' ψ hψ).1).2, (h' ψ hψ).2]⟩

private theorem Op_pow {k : KA E n} (hh : HkOps E) (hb : BandOps E) (hC : 0 ≤ C) {T : Module.End ℂ (Sm E n)}
    (h : Op S C (k : GA E n) T) (m : ℕ) : Op S C (k : GA E n) (T ^ m) := by
  induction m with
  | zero => simpa using Op_one
  | succ m ih => rw [pow_succ]; exact Op_mul hh hb hC ih h

private theorem Op_prod {k : KA E n} (hh : HkOps E) (hb : BandOps E) (hC : 0 ≤ C) (L : List (Module.End ℂ (Sm E n)))
    (h : ∀ T ∈ L, Op S C (k : GA E n) T) : Op S C (k : GA E n) L.prod := by
  induction L with
  | nil => simpa using Op_one
  | cons a L ih =>
    rw [List.prod_cons]
    exact Op_mul hh hb hC (h a List.mem_cons_self) (ih fun T hT => h T (List.mem_cons_of_mem a hT))

private theorem Op_hk {k : KA E n} (hh : HkOps E) (hb : BandOps E) (hC : 0 ≤ C) {w : Pl E} (hw : w ∉ S) (j : ℕ) :
    Op S C (k : GA E n) (hk n w j) := fun ψ hψ =>
  ⟨⟨((hb n C hC).2 ψ hψ.1).2.2.2.2 w j, ((hh n w j).2.2.2 S ψ hw hψ.2).1⟩,
    (((hh n w j).2.2.2 S ψ hw hψ.2).2.2.1 k).2⟩

private theorem zop_mem (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) : zop P ∈ Zalg E n := by
  rw [Zalg_eq_map]
  exact ⟨_, (evZ E n P).2, rfl⟩

private theorem Op_zop (hb : BandOps E) (hC : 0 ≤ C) (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) :
    Op S C k (zop P) := fun ψ hψ => by
  have hc : ∀ (g : GA E n) (χ : Sm E n), rt E n g (zop P χ) = zop P (rt E n g χ) := fun g χ =>
    (LinearMap.congr_fun (GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg (zop_mem P) g).eq χ).symm
  refine ⟨⟨((hb n C hC).2 ψ hψ.1).2.2.1 _, fun w hw x hx => ?_⟩, hc k ψ⟩
  exact (hc _ ψ).trans (congrArg _ (hψ.2 w hw x hx))

private theorem Op_app {k : KA E n} (hh : HkOps E) (hb : BandOps E) (hC : 0 ≤ C)
    {G : MvPolynomial (Pl E × Fin n) (MvPolynomial ((E →+* ℂ) × Fin n) ℂ)}
    (hG : ∀ β ∈ G.support, ∀ p ∈ β.support, p.1 ∉ S) : Op S C (k : GA E n) (app G) := by
  refine Op_sum hb hC _ fun β hβ => Op_mul hh hb hC (Op_zop hb hC _) (Op_prod hh hb hC _ fun T hT => ?_)
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT
  exact Op_pow hh hb hC (Op_hk hh hb hC (hG β hβ p (Finset.mem_toList.1 hp)) _) _

end Ops

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW in
theorem UpperTheory.ConvolutionTheory.BW.killComp :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.KillComp E := by
  intro E _ _ _ S n C φ w F G hC hφ hS hw hv hG hsum k d hd
  have hh := UpperTheory.ConvolutionTheory.BW.hkOps E
  have hb := UpperTheory.ConvolutionTheory.BW.bandOps E
  have hu := UpperTheory.ConvolutionTheory.BW.umgOps E
  have hc := UpperTheory.ConvolutionTheory.BW.compBound E
  have ho := UpperTheory.ConvolutionTheory.BW.killOne E
  funext t
  have hQ : Q S C φ := ⟨hφ, hS⟩
  have hQk : Q S C (rt E n (k : GA E n) φ) := Q_rt hh hb hC k hQ
  have hop : ∀ i, Op S C (k : GA E n) (app (G i)) := fun i => Op_app hh hb hC fun β hβ p hp =>
    hv p ((MvPolynomial.mem_vars p).2 ⟨β, vars_of_gen (hG i) hβ, hp⟩)
  let W : ℕ → Sm E n := fun e => ∑ i ∈ Finset.range e, app (G i) φ
  have hWQ : ∀ e, Q S C (W e) := fun e => by
    have h := (Op_sum hb hC (Finset.range e) fun i _ => hop i) φ hQ
    simpa only [LinearMap.sum_apply] using h.1
  have hUk : ∀ ψ : Sm E n, Umg ψ → Umg (rt E n (k : GA E n) ψ) := fun ψ h => ((hu n).2 ψ h).2.2.2.2.1 _
  have hWU : ∀ e, Umg (rt E n (k : GA E n) (W e)) := fun e => hUk _ (hWQ e).1.toUmg
  obtain ⟨N, hN⟩ := hsum
  obtain ⟨C₀, R, hB⟩ := (hc S n d).1 N
  have hlin := (hc S n d).2
  have hzero : d.comp (0 : Sm E n).1 t = 0 := by
    have h := hlin 0 0 1 ((hu n).1) ((hu n).1) t
    simp only [one_smul, add_zero, one_mul] at h
    exact left_eq_add.1 h
  have hpart : ∀ e, d.comp (rt E n (k : GA E n) (W e)).1 t =
      ∑ i ∈ Finset.range e, d.comp (app (G i) (rt E n (k : GA E n) φ)).1 t := by
    intro e
    induction e with
    | zero => simpa [W] using hzero
    | succ e ih =>
      have e1 : rt E n (k : GA E n) (W (e + 1)) =
          (1 : ℂ) • rt E n (k : GA E n) (W e) + app (G e) (rt E n (k : GA E n) φ) := by
        simp only [W, Finset.sum_range_succ, map_add, one_smul]
        rw [(hop e φ hQ).2]
      have hU2 : Umg (app (G e) (rt E n (k : GA E n) φ)) := (hop e _ hQk).1.1.toUmg
      rw [e1, hlin _ _ 1 (hWU e) hU2 t, ih, one_mul, Finset.sum_range_succ]
  have hlim : Filter.Tendsto (fun e => ∑ i ∈ Finset.range e, d.comp (app (G i) (rt E n (k : GA E n) φ)).1 t)
      Filter.atTop (nhds 0) := by
    rcases hd with h | h
    · exact (ho S n C d _ F G hC hQk.1 hQk.2 hv h hG t).tendsto_sum_nat
    · have h0 : ∀ i, d.comp (app (G i) (rt E n (k : GA E n) φ)).1 t = 0 := fun i =>
        congrFun (h _ (hop i _ hQk).1.1 (hop i _ hQk).1.2) t
      simp [h0]
  have hwk := hUk w hw
  let D : ℕ → Sm E n := fun e => (-1 : ℂ) • rt E n (k : GA E n) (W e) + rt E n (k : GA E n) w
  have hDU : ∀ e, Umg (D e) := fun e => ((hu n).2 _ (((hu n).2 _ (hWU e)).2.2.1 (-1))).2.1 _ hwk
  have hDc : ∀ e, d.comp (D e).1 t = d.comp (rt E n (k : GA E n) w).1 t -
      ∑ i ∈ Finset.range e, d.comp (app (G i) (rt E n (k : GA E n) φ)).1 t := fun e => by
    rw [hlin _ _ (-1) (hWU e) hwk t, hpart]
    ring
  have hDv : ∀ e g, (D e).1 g = (w - W e).1 (g * (k : GA E n)) := fun e g => by
    simp only [D]
    change (-1 : ℂ) • (W e).1 (g * (k : GA E n)) + w.1 (g * (k : GA E n)) = w.1 (g * (k : GA E n)) - (W e).1 (g * (k : GA E n))
    simp only [smul_eq_mul]
    ring
  set M : ℝ := (AutomorphicForm.heightConst E n * AutomorphicForm.height (k : GA E n)) ^ N with hM
  have hM0 : 0 ≤ M := pow_nonneg (mul_nonneg (zero_le_one.trans AutomorphicForm.one_le_heightConst)
    (AutomorphicForm.height_pos _).le) N
  have hconv : Filter.Tendsto (fun e => ∑ i ∈ Finset.range e, d.comp (app (G i) (rt E n (k : GA E n) φ)).1 t)
      Filter.atTop (nhds (d.comp (rt E n (k : GA E n) w).1 t)) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    set X : ℝ := Real.exp (R * ‖t‖) with hX
    have hX0 : 0 ≤ X := (Real.exp_pos _).le
    set A : ℝ := |C₀| * M * X + 1 with hA
    have hA0 : 0 < A := by positivity
    have hε : 0 < δ / (2 * A) := by positivity
    filter_upwards [hN _ hε] with e he
    have hb1 : ∀ g, ‖(D e).1 g‖ ≤ (δ / (2 * A) * M) * AutomorphicForm.height g ^ N := fun g => by
      rw [hDv]
      refine (he _).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hε.le
      rw [hM, ← mul_pow]
      refine pow_le_pow_left₀ (AutomorphicForm.height_pos _).le ((AutomorphicForm.height_mul_le _ _).trans (le_of_eq ?_)) N
      ring
    have hb2 := hB _ _ (hDU e) hb1 t
    rw [hDc] at hb2
    rw [dist_comm, dist_eq_norm]
    refine lt_of_le_of_lt hb2 ?_
    have h3 : C₀ * (δ / (2 * A) * M) * X ≤ |C₀| * (δ / (2 * A) * M) * X := by
      have : 0 ≤ δ / (2 * A) * M := mul_nonneg hε.le hM0
      gcongr
      exact le_abs_self _
    refine lt_of_le_of_lt h3 ?_
    have h4 : |C₀| * (δ / (2 * A) * M) * X = δ / (2 * A) * (A - 1) := by
      rw [hA]; ring
    rw [h4]
    have h5 : δ / (2 * A) * (A - 1) ≤ δ / (2 * A) * A := by
      exact mul_le_mul_of_nonneg_left (by linarith) hε.le
    have h6 : δ / (2 * A) * A = δ / 2 := by field_simp
    linarith
  exact tendsto_nhds_unique hconv hlim
