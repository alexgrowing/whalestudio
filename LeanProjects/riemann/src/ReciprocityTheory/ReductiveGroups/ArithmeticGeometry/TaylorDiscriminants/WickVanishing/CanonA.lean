import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced

noncomputable section

open MvPowerSeries TensorProduct

namespace ReciprocityTheory.ChartRestriction.G.TB.Canon

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

theorem inner_of_derivation {O W : Type} [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] [AddCommGroup W]
    [Module ℚ W] (L R : O →+* Module.End ℚ W) (hc : ∀ a b, L a * R b = R b * L a) (D : O →+ W)
    (hD : ∀ a b, D (a * b) = R b (D a) + L a (D b)) : ∃ β : W, ∀ a, D a = R a β - L a β := by
  let S := ℚ ⊗[ℤ] O
  let _ : Algebra O S := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ)) S := IsLocalization.tensorRight _ _
  have : IsReduced S := isReduced_localizationPreserves (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ)) S inferInstance
  have : IsArtinianRing S := IsArtinianRing.of_finite ℚ S
  have : ∀ I : MaximalSpectrum S, Algebra.FormallyUnramified ℚ (S ⧸ I.asIdeal) := fun I => by
    let _ := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyUnramified.of_isSeparable ℚ _
  have : Algebra.FormallyUnramified ℚ S := Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi S).restrictScalars ℚ).symm
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := ℚ) (S := S)).1 this
  let L' : S →ₗ[ℚ] Module.End ℚ W := LinearMap.liftBaseChange ℚ L.toAddMonoidHom.toIntLinearMap
  let D' : S →ₗ[ℚ] W := LinearMap.liftBaseChange ℚ D.toIntLinearMap
  let Φ : S ⊗[ℚ] S →ₗ[ℚ] W := TensorProduct.lift (L'.compl₂ D')
  have key : ∀ (a : O) (u : S ⊗[ℚ] S), Φ (((1 : S) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] a : S) - ((1 : ℚ) ⊗ₜ[ℤ] a : S) ⊗ₜ[ℚ] (1 : S)) * u) =
      R a (Φ u) - L a (Φ u) + L' (Algebra.TensorProduct.lmul' ℚ u) (D a) := by
    intro a u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [mul_add, map_add, hu, hv, LinearMap.add_apply]; abel
    | tmul x y =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' hx hx' => simp only [add_tmul, mul_add, map_add, hx, hx', LinearMap.add_apply]; abel
      | tmul p x =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y y' hy hy' => simp only [tmul_add, mul_add, map_add, hy, hy', LinearMap.add_apply]; abel
        | tmul q y =>
          have c := LinearMap.congr_fun (hc x a) (D y)
          simp only [Module.End.mul_apply] at c
          simp only [S, sub_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_sub, Φ, TensorProduct.lift.tmul,
            LinearMap.compl₂_apply, L', D', LinearMap.liftBaseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
            RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, LinearMap.smul_apply, map_smul,
            Algebra.TensorProduct.lmul'_apply_tmul, mul_comm a y, hD, map_add, c, map_mul, Module.End.mul_apply]
          module
  refine ⟨-Φ t, fun a => ?_⟩
  have := key a t
  rw [ht, map_zero, ht1, show L' 1 = 1 from by
    show L' ((1 : ℚ) ⊗ₜ[ℤ] (1 : O)) = 1
    exact (LinearMap.liftBaseChange_tmul ℚ _ _ _).trans ((one_smul _ _).trans (map_one L))] at this
  simp only [map_neg, Module.End.one_apply] at this ⊢
  linear_combination (norm := abel) -this

section Prim

variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [DecidableEq τ]

def primT (T : Finset τ) (ω : τ → MvPowerSeries τ k) : MvPowerSeries τ k := fun m =>
  algebraMap ℚ k (((∑ w ∈ T, m w : ℕ) : ℚ)⁻¹) * ∑ w ∈ T, if m w = 0 then 0 else coeff (m - Finsupp.single w 1) (ω w)

theorem pderiv_primT (T : Finset τ) (ω : τ → MvPowerSeries τ k)
    (hω : ∀ a ∈ T, ∀ c ∈ T, pderiv k c (ω a) = pderiv k a (ω c)) (v : τ) (hv : v ∈ T) : pderiv k v (primT T ω) = ω v := by
  ext n
  rw [MvPowerSeries.coeff_pderiv]
  have hS : (∑ w ∈ T, (n + Finsupp.single v 1 : τ →₀ ℕ) w) = (∑ w ∈ T, n w) + 1 := by
    simp [Finset.sum_add_distrib, Finsupp.single_apply, hv]
  have hterm : ∀ w ∈ T, (if (n + Finsupp.single v 1 : τ →₀ ℕ) w = 0 then 0 else
      coeff (n + Finsupp.single v 1 - Finsupp.single w 1) (ω w)) * ((n v : k) + 1) =
      ((n w : k) + if w = v then 1 else 0) * coeff n (ω v) := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      have h1 : (n + Finsupp.single w 1 : τ →₀ ℕ) w ≠ 0 := by simp
      rw [if_neg h1, add_tsub_cancel_right, if_pos rfl]
      ring
    · have hvw : v ≠ w := Ne.symm hwv
      by_cases hn : n w = 0
      · have h0 : (n + Finsupp.single v 1 : τ →₀ ℕ) w = 0 := by
          rw [Finsupp.add_apply, Finsupp.single_apply, if_neg hvw, hn, add_zero]
        rw [if_pos h0, if_neg hwv, hn]
        simp
      · obtain ⟨p, rfl⟩ : ∃ p : τ →₀ ℕ, n = p + Finsupp.single w 1 := by
          refine ⟨n - Finsupp.single w 1, ?_⟩
          ext x
          by_cases hx : x = w
          · subst hx
            rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
            omega
          · rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hx)]
            simp
        have h1 : (p + Finsupp.single w 1 + Finsupp.single v 1 : τ →₀ ℕ) w ≠ 0 := by
          simp [Finsupp.single_apply, hvw]
        have h2 : p + Finsupp.single w 1 + Finsupp.single v 1 - Finsupp.single w 1 =
            p + Finsupp.single v 1 := by
          rw [add_right_comm, add_tsub_cancel_right]
        have h3 : (p + Finsupp.single w 1 : τ →₀ ℕ) v = p v := by
          rw [Finsupp.add_apply, Finsupp.single_apply, if_neg hwv, add_zero]
        have h4 : (p + Finsupp.single w 1 : τ →₀ ℕ) w = p w + 1 := by
          rw [Finsupp.add_apply, Finsupp.single_eq_same]
        rw [if_neg h1, h2, h3, h4, if_neg hwv, ← MvPowerSeries.coeff_pderiv, hω w hw v hv,
          MvPowerSeries.coeff_pderiv]
        push_cast
        ring
  show (algebraMap ℚ k (((∑ w ∈ T, (n + Finsupp.single v 1 : τ →₀ ℕ) w : ℕ) : ℚ)⁻¹) *
      ∑ w ∈ T, (if (n + Finsupp.single v 1 : τ →₀ ℕ) w = 0 then 0 else
        coeff (n + Finsupp.single v 1 - Finsupp.single w 1) (ω w))) * ((n v : k) + 1) = coeff n (ω v)
  rw [mul_assoc, Finset.sum_mul, Finset.sum_congr rfl hterm, ← Finset.sum_mul, Finset.sum_add_distrib, hS]
  simp only [Finset.sum_ite_eq', hv, if_true, ite_true]
  have hc : (∑ w ∈ T, (n w : k)) + 1 = algebraMap ℚ k (((∑ w ∈ T, n w) + 1 : ℕ) : ℚ) := by simp
  rw [hc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by positivity), map_one, one_mul]

end Prim

variable {k : Type} [CommRing k] {d : ℕ}

variable (k d) in

def Q (n : ℕ) : AddSubgroup (Pt k n d) where
  carrier := {p | ∀ i, constantCoeff (p i) = 0}
  add_mem' := fun ha hb i => by rw [Pi.add_apply, map_add, ha i, hb i, add_zero]
  zero_mem' := fun _ => map_zero _
  neg_mem' := fun ha i => by rw [Pi.neg_apply, map_neg, ha i, neg_zero]

variable {n l : ℕ}

def gen (j : Fin n) : Q k d n := ⟨pt k d j, cc_pt j⟩

theorem czQ (b : Fin n → Q k d l) : CZ (fun j => (b j).1) := fun j i => (b j).2 i

def sb (b : Fin n → Q k d l) : PS k n d →+* PS k l d := evHom (czQ b)

theorem sb_apply (b : Fin n → Q k d l) (f : PS k n d) : sb b f = ev (fun j => (b j).1) f := evHom_apply (czQ b) f

def sq (b : Fin n → Q k d l) : Q k d n →+ Q k d l where
  toFun p := ⟨fun i => sb b (p.1 i), fun i =>
    (congrArg constantCoeff (sb_apply b _)).trans (constantCoeff_ev (czQ b) (p.2 i))⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

@[simp] theorem sq_gen (b : Fin n → Q k d l) (j : Fin n) : sq b (gen j) = b j := Subtype.ext <| funext fun i => (sb_apply b _).trans (ev_X (czQ b) j i)

theorem sb_sb {m : ℕ} (b : Fin n → Q k d l) (a : Fin m → Q k d n) (f : PS k m d) :
    sb b (sb a f) = sb (fun j => sq b (a j)) f := by
  simp only [sb_apply]
  rw [ev_ev (czQ b) (czQ a)]
  congr 1
  funext j i
  exact (sb_apply b _).symm

theorem sb_gen (f : PS k n d) : sb gen f = f := (sb_apply _ f).trans (ev_pt f)

def E2 (f : PS k 2 d) (u v : Q k d n) : PS k n d := sb ![u, v] f

def E3 (f : PS k 3 d) (u v w : Q k d n) : PS k n d := sb ![u, v, w] f

@[simp] theorem formalPointSubstitutionSeries_valueAtTwoPoints (b : Fin n → Q k d l) (f : PS k 2 d) (u v : Q k d n) : sb b (E2 f u v) = E2 f (sq b u) (sq b v) := by
  have e : (fun j => sq b (![u, v] j)) = ![sq b u, sq b v] := by
    funext i
    fin_cases i <;> rfl
  show sb b (sb ![u, v] f) = sb ![sq b u, sq b v] f
  rw [sb_sb, e]

@[simp] theorem formalPointSubstitutionSeries_valueAtThreePoints (b : Fin n → Q k d l) (f : PS k 3 d) (u v w : Q k d n) :
    sb b (E3 f u v w) = E3 f (sq b u) (sq b v) (sq b w) := by
  have e : (fun j => sq b (![u, v, w] j)) = ![sq b u, sq b v, sq b w] := by
    funext i
    fin_cases i <;> rfl
  show sb b (sb ![u, v, w] f) = sb ![sq b u, sq b v, sq b w] f
  rw [sb_sb, e]

theorem formalSeriesValueAtTwoPoints_genericPoints (f : PS k 2 d) : E2 f (gen 0) (gen 1) = f := by
  have h : (![gen 0, gen 1] : Fin 2 → Q k d 2) = gen := by
    funext i
    fin_cases i <;> rfl
  show sb ![gen 0, gen 1] f = f
  rw [h, sb_gen]

theorem formalSeriesValueAtThreePoints_genericPoints (f : PS k 3 d) : E3 f (gen 0) (gen 1) (gen 2) = f := by
  have h : (![gen 0, gen 1, gen 2] : Fin 3 → Q k d 3) = gen := by
    funext i
    fin_cases i <;> rfl
  show sb ![gen 0, gen 1, gen 2] f = f
  rw [h, sb_gen]

def Dir (j : Fin n) (p : Q k d n) (t : PS k n d) : Prop := ∀ b c, pderiv k (j, b) (p.1 c) = if c = b then t else 0

theorem dir_same (j : Fin n) : Dir j (gen j : Q k d n) 1 := by
  intro b c
  show pderiv k (j, b) (pt k d j c) = _
  rw [pderiv_pt]
  simp

theorem dir_ne {i j : Fin n} (h : i ≠ j) : Dir j (gen i : Q k d n) 0 := by
  intro b c
  show pderiv k (j, b) (pt k d i c) = _
  rw [pderiv_pt]
  simp [h]

theorem dir_zero (j : Fin n) : Dir j (0 : Q k d n) 0 := by
  intro b c
  show pderiv k (j, b) 0 = _
  simp

theorem Dir.add {j : Fin n} {p q : Q k d n} {s t : PS k n d} (h : Dir j p s) (h' : Dir j q t) : Dir j (p + q) (s + t) := by
  intro b c
  show pderiv k (j, b) (p.1 c + q.1 c) = _
  rw [map_add, h b c, h' b c]
  split_ifs <;> simp

theorem pd_sb {m : ℕ} (a : Fin m → Q k d n) (t : Fin m → PS k n d) {j : Fin n} (h : ∀ i, Dir j (a i) (t i)) (b : Fin d)
    (f : PS k m d) : pderiv k (j, b) (sb a f) = ∑ i, sb a (pderiv k (i, b) f) * t i := by
  rw [sb_apply, pderiv_ev (czQ a), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [h i b, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, sb_apply]

theorem pderiv_eval_two {j : Fin n} {u v : Q k d n} {s t : PS k n d} (hu : Dir j u s) (hv : Dir j v t) (b : Fin d) (f : PS k 2 d) :
    pderiv k (j, b) (E2 f u v) = E2 (pderiv k (0, b) f) u v * s + E2 (pderiv k (1, b) f) u v * t := by
  have hd : ∀ i, Dir j (![u, v] i) (![s, t] i) := fun i => by
    fin_cases i
    · exact hu
    · exact hv
  show pderiv k (j, b) (sb ![u, v] f) = _
  rw [pd_sb ![u, v] ![s, t] hd b f, Fin.sum_univ_two]
  all_goals rfl

theorem pderiv_eval_three {j : Fin n} {u v w : Q k d n} {s t r : PS k n d} (hu : Dir j u s) (hv : Dir j v t) (hw : Dir j w r) (b : Fin d)
    (f : PS k 3 d) : pderiv k (j, b) (E3 f u v w) =
      E3 (pderiv k (0, b) f) u v w * s + E3 (pderiv k (1, b) f) u v w * t + E3 (pderiv k (2, b) f) u v w * r := by
  have hd : ∀ i, Dir j (![u, v, w] i) (![s, t, r] i) := fun i => by
    fin_cases i
    · exact hu
    · exact hv
    · exact hw
  show pderiv k (j, b) (sb ![u, v, w] f) = _
  rw [pd_sb ![u, v, w] ![s, t, r] hd b f, Fin.sum_univ_three]
  all_goals rfl

theorem coeff_kill (j : Fin n) (f : PS k n d) (m : Fin n × Fin d →₀ ℕ) :
    coeff m (sb (Function.update gen j 0) f) = if ∀ b, m (j, b) = 0 then coeff m f else 0 := by
  let a : Fin n × Fin d → PS k n d := fun p => ((Function.update gen j 0 p.1 : Q k d n) : Pt k n d) p.2
  have ha : MvPowerSeries.HasSubst a := (czQ (Function.update gen j 0)).hasSubst
  have key : ∀ e : Fin n × Fin d →₀ ℕ, coeff m (e.prod fun s i => a s ^ i) =
      if e = m ∧ ∀ b, m (j, b) = 0 then 1 else 0 := by
    intro e
    by_cases he : ∀ b, e (j, b) = 0
    · have hp : (e.prod fun s i => a s ^ i) = MvPowerSeries.monomial e 1 := by
        refine (Finsupp.prod_congr fun s hs => ?_).trans (MvPowerSeries.monomial_one_eq e).symm
        have hs1 : s.1 ≠ j := by
          intro h1
          apply Finsupp.mem_support_iff.mp hs
          rw [show s = (j, s.2) from Prod.ext h1 rfl]
          exact he s.2
        show ((Function.update gen j 0 s.1 : Q k d n) : Pt k n d) s.2 ^ e s = X s ^ e s
        rw [Function.update_of_ne hs1]
        rfl
      rw [hp, MvPowerSeries.coeff_monomial]
      by_cases hem : e = m
      · subst hem
        simp [he]
      · rw [if_neg (Ne.symm hem), if_neg (fun h => hem h.1)]
    · push_neg at he
      obtain ⟨b, hb⟩ := he
      have hp : (e.prod fun s i => a s ^ i) = 0 := by
        refine Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hb) ?_
        show ((Function.update gen j 0 j : Q k d n) : Pt k n d) b ^ e (j, b) = 0
        first
        | rw [Function.update_self]
        | rw [Function.update_same]
        exact zero_pow hb
      rw [hp, map_zero, if_neg]
      rintro ⟨rfl, h⟩
      exact hb (h b)
  rw [sb_apply]
  show coeff m (MvPowerSeries.subst a f) = _
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ m]
  · show coeff m f • coeff m (m.prod fun s i => a s ^ i) = _
    rw [key]
    by_cases hm : ∀ b, m (j, b) = 0 <;> simp [hm]
  · intro e he
    show coeff e f • coeff m (e.prod fun s i => a s ^ i) = 0
    rw [key, if_neg (fun h => he h.1), smul_zero]

variable [Algebra ℚ k]

theorem zero_of_pd (j : Fin n) {f : PS k n d} (h : ∀ b, pderiv k (j, b) f = 0) (h0 : sb (Function.update gen j 0) f = 0) :
    f = 0 := by
  ext m
  rw [map_zero]
  by_cases hm : ∀ b, m (j, b) = 0
  · have := congrArg (coeff m) h0
    rw [coeff_kill, if_pos hm, map_zero] at this
    exact this
  · push_neg at hm
    obtain ⟨b, hb⟩ := hm
    obtain ⟨m', rfl⟩ : ∃ m' : Fin n × Fin d →₀ ℕ, m = m' + Finsupp.single (j, b) 1 := by
      refine ⟨m - Finsupp.single (j, b) 1, ?_⟩
      ext x
      by_cases hx : x = (j, b)
      · subst hx
        rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      · rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hx)]
        simp
    have hc := congrArg (coeff m') (h b)
    rw [MvPowerSeries.coeff_pderiv, map_zero] at hc
    have hu : IsUnit ((m' (j, b) : k) + 1) := by
      have e : ((m' (j, b) : k) + 1) = algebraMap ℚ k ((m' (j, b) : ℚ) + 1) := by simp
      rw [e]
      exact (isUnit_iff_ne_zero.mpr (by positivity)).map (algebraMap ℚ k)
    exact hu.mul_left_eq_zero.mp hc

theorem update_three_one_zero : (Function.update gen 1 0 : Fin 3 → Q k d 3) = ![gen 0, 0, gen 2] := by
  funext i
  fin_cases i <;> first | rfl | simp [Function.update_apply]

theorem update_three_two_zero : (Function.update gen 2 0 : Fin 3 → Q k d 3) = ![gen 0, gen 1, 0] := by
  funext i
  fin_cases i <;> first | rfl | simp [Function.update_apply]

private theorem pd_comm_lemma (i j : Fin n × Fin d) (f : PS k n d) :
    pderiv k i (pderiv k j f) = pderiv k j (pderiv k i f) := by
  by_cases h : i = j
  · subst h
    rfl
  · ext m
    simp only [MvPowerSeries.coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply, h, Ne.symm h,
      if_false, ite_false, add_zero]
    rw [add_right_comm m (Finsupp.single i 1) (Finsupp.single j 1)]
    ring

private theorem d1_lemma_2 (α : PS k 3 d)
    (coc : ∀ {n} (x y t w : Q k d n), E3 α x y w + E3 α (x + y) t w = E3 α y t w + E3 α x (y + t) w)
    (b : Fin d) :
    pderiv k (1, b) α = E2 (E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1)) (gen 0 + gen 1) (gen 2) -
      E2 (E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1)) (gen 1) (gen 2) := by
  have hψ : ∀ (u w : Q k d 3), E2 (E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1)) u w =
      E3 (pderiv k (1, b) α) u 0 w := by
    intro u w
    show sb ![u, w] (E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1)) = _
    rw [formalPointSubstitutionSeries_valueAtThreePoints, sq_gen, sq_gen, map_zero]
    all_goals rfl
  have d0 : Dir (3 : Fin 4) (gen 0 : Q k d 4) 0 := dir_ne (by decide)
  have d1 : Dir (3 : Fin 4) (gen 1 : Q k d 4) 0 := dir_ne (by decide)
  have d2 : Dir (3 : Fin 4) (gen 2 : Q k d 4) 0 := dir_ne (by decide)
  have d3 : Dir (3 : Fin 4) (gen 3 : Q k d 4) 1 := dir_same 3
  have e := congrArg (pderiv k ((3 : Fin 4), b)) (coc (gen 0) (gen 1) (gen 3) (gen 2))
  rw [map_add, map_add, pderiv_eval_three d0 d1 d2, pderiv_eval_three (d0.add d1) d3 d2, pderiv_eval_three d1 d3 d2,
    pderiv_eval_three d0 (d1.add d3) d2] at e
  simp only [mul_zero, zero_add, add_zero, mul_one] at e
  have e' := congrArg (sb (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3)) e
  have s0 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 0) = gen 0 := sq_gen _ 0
  have s1 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 1) = gen 1 := sq_gen _ 1
  have s2 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 2) = gen 2 := sq_gen _ 2
  have s3 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 3) = 0 := sq_gen _ 3
  rw [map_add, formalPointSubstitutionSeries_valueAtThreePoints, formalPointSubstitutionSeries_valueAtThreePoints, formalPointSubstitutionSeries_valueAtThreePoints, map_add, map_add, s0, s1, s2, s3, add_zero, formalSeriesValueAtThreePoints_genericPoints] at e'
  rw [hψ, hψ, e']
  ring

private theorem d0_lemma_4 (α : PS k 3 d) (sym : ∀ {n} (x y w : Q k d n), E3 α x y w = E3 α y x w)
    (coc : ∀ {n} (x y t w : Q k d n), E3 α x y w + E3 α (x + y) t w = E3 α y t w + E3 α x (y + t) w)
    (b : Fin d) :
    pderiv k (0, b) α = E2 (E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1)) (gen 1 + gen 0) (gen 2) -
      E2 (E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1)) (gen 0) (gen 2) := by
  have hs : α = E3 α (gen 1) (gen 0) (gen 2) := (formalSeriesValueAtThreePoints_genericPoints α).symm.trans (sym _ _ _)
  have d0 : Dir (0 : Fin 3) (gen 1 : Q k d 3) 0 := dir_ne (by decide)
  have d1 : Dir (0 : Fin 3) (gen 0 : Q k d 3) 1 := dir_same 0
  have d2 : Dir (0 : Fin 3) (gen 2 : Q k d 3) 0 := dir_ne (by decide)
  have h1 := d1_lemma_2 α coc b
  have e : pderiv k (0, b) α = E3 (pderiv k (1, b) α) (gen 1) (gen 0) (gen 2) := by
    conv_lhs => rw [hs]
    rw [pderiv_eval_three d0 d1 d2]
    simp only [mul_zero, zero_add, add_zero, mul_one]
  rw [e]
  show sb ![gen 1, gen 0, gen 2] (pderiv k (1, b) α) = _
  conv_lhs => rw [h1]
  rw [map_sub, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtTwoPoints, map_add, sq_gen, sq_gen, sq_gen]
  all_goals rfl

private theorem closed_lemma_5 (α : PS k 3 d) (sym : ∀ {n} (x y w : Q k d n), E3 α x y w = E3 α y x w)
    (coc : ∀ {n} (x y t w : Q k d n), E3 α x y w + E3 α (x + y) t w = E3 α y t w + E3 α x (y + t) w)
    (b c : Fin d) :
    pderiv k (0, c) (E3 (pderiv k (1, b) α) (gen 0 : Q k d 2) 0 (gen 1)) =
      pderiv k (0, b) (E3 (pderiv k (1, c) α) (gen 0 : Q k d 2) 0 (gen 1)) := by
  have a0 : Dir (0 : Fin 3) (gen 0 : Q k d 3) 1 := dir_same 0
  have a1 : Dir (0 : Fin 3) (gen 1 : Q k d 3) 0 := dir_ne (by decide)
  have a2 : Dir (0 : Fin 3) (gen 2 : Q k d 3) 0 := dir_ne (by decide)
  have b0 : Dir (1 : Fin 3) (gen 0 : Q k d 3) 0 := dir_ne (by decide)
  have b1 : Dir (1 : Fin 3) (gen 1 : Q k d 3) 1 := dir_same 1
  have b2 : Dir (1 : Fin 3) (gen 2 : Q k d 3) 0 := dir_ne (by decide)
  have e1 := congrArg (pderiv k ((0 : Fin 3), c)) (d1_lemma_2 α coc b)
  have e2 := congrArg (pderiv k ((1 : Fin 3), b)) (d0_lemma_4 α sym coc c)
  rw [map_sub, pderiv_eval_two (a0.add a1) a2, pderiv_eval_two a1 a2] at e1
  rw [map_sub, pderiv_eval_two (b1.add b0) b2, pderiv_eval_two b0 b2] at e2
  simp only [mul_zero, add_zero, zero_add, mul_one, sub_zero] at e1 e2
  rw [pd_comm_lemma, e2] at e1
  have e3 := congrArg (sb (![gen 0, 0, gen 1] : Fin 3 → Q k d 2)) e1
  have t0 : sq (![gen 0, 0, gen 1] : Fin 3 → Q k d 2) (gen 0) = gen 0 := sq_gen _ 0
  have t1 : sq (![gen 0, 0, gen 1] : Fin 3 → Q k d 2) (gen 1) = 0 := sq_gen _ 1
  have t2 : sq (![gen 0, 0, gen 1] : Fin 3 → Q k d 2) (gen 2) = gen 1 := sq_gen _ 2
  rw [formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtTwoPoints, map_add, map_add, t0, t1, t2, add_zero, zero_add, formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_genericPoints] at e3
  exact e3.symm

theorem split (α : PS k 3 d) (ax : ∀ {n} (y w : Q k d n), E3 α 0 y w = 0) (sym : ∀ {n} (x y w : Q k d n), E3 α x y w = E3 α y x w)
    (coc : ∀ {n} (x y t w : Q k d n), E3 α x y w + E3 α (x + y) t w = E3 α y t w + E3 α x (y + t) w) :
    ∃ H : PS k 2 d, (∀ {n} (x y w : Q k d n), E3 α x y w = E2 H x w + E2 H y w - E2 H (x + y) w) ∧
      (∀ {n} (w : Q k d n), E2 H 0 w = 0) ∧ ∀ {n} (b) (w : Q k d n), E2 (pderiv k (0, b) H) 0 w = 0 := by
  let T : Finset (Fin 2 × Fin d) := Finset.univ.filter (fun p => p.1 = 0)
  let ω : Fin 2 × Fin d → PS k 2 d := fun p => E3 (pderiv k (1, p.2) α) (gen 0) 0 (gen 1)
  have hω : ∀ a ∈ T, ∀ c ∈ T, pderiv k c (ω a) = pderiv k a (ω c) := by
    rintro ⟨a1, a2⟩ ha ⟨c1, c2⟩ hc
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at ha hc
    subst ha hc
    exact closed_lemma_5 α sym coc a2 c2
  have hpd : ∀ b, pderiv k (0, b) (-primT T ω) = -E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1) := by
    intro b
    rw [map_neg, pderiv_primT T ω hω (0, b) (by simp [T])]
    all_goals rfl
  have hz : sb (Function.update gen 0 0 : Fin 2 → Q k d 2) (primT T ω) = 0 := by
    ext m
    rw [coeff_kill, map_zero]
    by_cases hm : ∀ b, m (0, b) = 0
    · rw [if_pos hm]
      show algebraMap ℚ k (((∑ w ∈ T, m w : ℕ) : ℚ)⁻¹) * _ = 0
      have h0 : (∑ w ∈ T, m w) = 0 := Finset.sum_eq_zero fun p hp => by
        obtain ⟨p1, p2⟩ := p
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        subst hp
        exact hm p2
      rw [h0]
      simp
    · rw [if_neg hm]
  have h2 : (Function.update gen 0 0 : Fin 2 → Q k d 2) = ![0, gen 1] := by
    funext i
    fin_cases i <;> first | rfl | simp [Function.update_apply]
  rw [h2] at hz
  have hP1 : ∀ {n : ℕ} (w : Q k d n), E2 (-primT T ω) 0 w = 0 := by
    intro n w
    have e := congrArg (sb (![0, w] : Fin 2 → Q k d n)) hz
    change sb (![0, w] : Fin 2 → Q k d n) (E2 (primT T ω) 0 (gen 1)) = _ at e
    rw [formalPointSubstitutionSeries_valueAtTwoPoints, map_zero, map_zero, sq_gen] at e
    show sb ![0, w] (-primT T ω) = 0
    rw [map_neg, neg_eq_zero]
    exact e
  have hax : ∀ {n : ℕ} (b : Fin d) (w : Q k d n), E3 (pderiv k (1, b) α) 0 0 w = 0 := by
    intro n b w
    have z0 : Dir (0 : Fin 2) (0 : Q k d 2) 0 := dir_zero 0
    have z1 : Dir (0 : Fin 2) (gen 0 : Q k d 2) 1 := dir_same 0
    have z2 : Dir (0 : Fin 2) (gen 1 : Q k d 2) 0 := dir_ne (by decide)
    have e := congrArg (pderiv k ((0 : Fin 2), b)) (ax (gen 0 : Q k d 2) (gen 1))
    rw [pderiv_eval_three z0 z1 z2, map_zero] at e
    simp only [mul_zero, zero_add, add_zero, mul_one] at e
    have e' := congrArg (sb (![0, w] : Fin 2 → Q k d n)) e
    rw [formalPointSubstitutionSeries_valueAtThreePoints, map_zero, map_zero, sq_gen, sq_gen] at e'
    exact e'
  have hneg : ∀ (f : PS k 2 d) (u v : Q k d 3), E2 (-f) u v = -E2 f u v := fun f u v => map_neg _ f
  have hG : α - (E2 (-primT T ω) (gen 0) (gen 2) + E2 (-primT T ω) (gen 1) (gen 2) -
      E2 (-primT T ω) (gen 0 + gen 1) (gen 2)) = 0 := by
    apply zero_of_pd 1
    · intro b
      have c0 : Dir (1 : Fin 3) (gen 0 : Q k d 3) 0 := dir_ne (by decide)
      have c1 : Dir (1 : Fin 3) (gen 1 : Q k d 3) 1 := dir_same 1
      have c2 : Dir (1 : Fin 3) (gen 2 : Q k d 3) 0 := dir_ne (by decide)
      rw [map_sub, map_sub, map_add, pderiv_eval_two c0 c2, pderiv_eval_two c1 c2, pderiv_eval_two (c0.add c1) c2,
        d1_lemma_2 α coc b, hpd b]
      simp only [mul_zero, add_zero, zero_add, mul_one]
      rw [hneg, hneg]
      ring
    · rw [update_three_one_zero, map_sub, map_sub, map_add, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtTwoPoints, map_add]
      have u0 : sq (![gen 0, 0, gen 2] : Fin 3 → Q k d 3) (gen 0) = gen 0 := sq_gen _ 0
      have u1 : sq (![gen 0, 0, gen 2] : Fin 3 → Q k d 3) (gen 1) = 0 := sq_gen _ 1
      have u2 : sq (![gen 0, 0, gen 2] : Fin 3 → Q k d 3) (gen 2) = gen 2 := sq_gen _ 2
      have hα : sb (![gen 0, 0, gen 2] : Fin 3 → Q k d 3) α = 0 :=
        (sym (gen 0) 0 (gen 2)).trans (ax (gen 0) (gen 2))
      rw [u0, u1, u2, add_zero, hP1, hα]
      ring
  refine ⟨-primT T ω, ?_, hP1, ?_⟩
  · intro n x y w
    have e := congrArg (sb (![x, y, w] : Fin 3 → Q k d n)) hG
    rw [map_sub, map_sub, map_add, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtTwoPoints, map_add, sq_gen, sq_gen, sq_gen, map_zero,
      sub_eq_zero] at e
    exact e
  · intro n b w
    rw [hpd b]
    show sb ![0, w] (-(E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1))) = 0
    rw [map_neg, neg_eq_zero, formalPointSubstitutionSeries_valueAtThreePoints, sq_gen, sq_gen, map_zero]
    exact hax b w

theorem zero_of_add (f : PS k 3 d) (add : ∀ {n} (x y v v' : Q k d n), E3 f x y (v + v') = E3 f x y v + E3 f x y v')
    (h : ∀ {n} b (x y : Q k d n), E3 (pderiv k (2, b) f) x y 0 = 0) : f = 0 := by
  have h0 : ∀ {n : ℕ} (x y : Q k d n), E3 f x y 0 = 0 := by
    intro n x y
    have e := add x y 0 0
    rw [add_zero] at e
    linear_combination -e
  have hd : ∀ b, pderiv k (2, b) f = 0 := by
    intro b
    have e := congrArg (pderiv k ((3 : Fin 4), b)) (add (gen 0) (gen 1) (gen 2) (gen 3))
    have d0 : Dir (3 : Fin 4) (gen 0 : Q k d 4) 0 := dir_ne (by decide)
    have d1 : Dir (3 : Fin 4) (gen 1 : Q k d 4) 0 := dir_ne (by decide)
    have d2 : Dir (3 : Fin 4) (gen 2 : Q k d 4) 0 := dir_ne (by decide)
    have d3 : Dir (3 : Fin 4) (gen 3 : Q k d 4) 1 := dir_same 3
    rw [map_add, pderiv_eval_three d0 d1 (d2.add d3), pderiv_eval_three d0 d1 d2, pderiv_eval_three d0 d1 d3] at e
    simp only [mul_zero, zero_add, add_zero, mul_one] at e
    have e' := congrArg (sb (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3)) e
    have s0 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 0) = gen 0 := sq_gen _ 0
    have s1 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 1) = gen 1 := sq_gen _ 1
    have s2 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 2) = gen 2 := sq_gen _ 2
    have s3 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 3) = 0 := sq_gen _ 3
    rw [formalPointSubstitutionSeries_valueAtThreePoints, formalPointSubstitutionSeries_valueAtThreePoints, map_add, s0, s1, s2, s3, add_zero, h b (gen 0) (gen 1), formalSeriesValueAtThreePoints_genericPoints] at e'
    exact e'
  have hz : sb (Function.update gen 2 0) f = 0 := by
    rw [update_three_two_zero]
    exact h0 (gen 0) (gen 1)
  exact zero_of_pd 2 hd hz

end ReciprocityTheory.ChartRestriction.G.TB.Canon
