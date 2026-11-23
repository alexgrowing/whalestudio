import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PtOfDif
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KumCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.EOmZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SgIsog
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Square

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

private theorem mul_eq_up (k M : ℕ) [NeZero k] [NeZero M] (x : Row M) (i : Fin 2) (z : ZMod (k * M))
    (h : ZMod.castHom (dvd_mul_left M k) (ZMod M) z = x i) : up k M x i = (k : ZMod (k * M)) * z := by
  haveI : NeZero (k * M) := ⟨mul_ne_zero (NeZero.ne k) (NeZero.ne M)⟩
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
  rw [map_natCast] at h
  simp only [up]
  rw [← h, ZMod.val_natCast, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  exact (Nat.mod_modEq n M).mul_left' k

private theorem cast_eq_zero_of (k M : ℕ) [NeZero k] [NeZero M] (z : ZMod (k * M))
    (h : (k : ZMod (k * M)) * z = 0) : ZMod.castHom (dvd_mul_left M k) (ZMod M) z = 0 := by
  haveI : NeZero (k * M) := ⟨mul_ne_zero (NeZero.ne k) (NeZero.ne M)⟩
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
  rw [map_natCast, ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero (NeZero.ne k)) h

private def InF (k M : ℕ) (x : Row M) (x' : Row (k * M)) : Prop := x' 0 = up k M x 0 ∧ dn k M x' 1 = x 1

private theorem lift_ex (k M : ℕ) (w : ZMod M) : ∃ z : ZMod (k * M), ZMod.castHom (dvd_mul_left M k) (ZMod M) z = w :=
  ZMod.castHom_surjective _ w

private theorem inF_ex (k M : ℕ) (x : Row M) : ∃ x', InF k M x x' := by
  obtain ⟨z, hz⟩ := lift_ex k M (x 1)
  exact ⟨![up k M x 0, z], rfl, hz⟩

private theorem inF_two (k M : ℕ) [NeZero k] [NeZero M] (x : Row M) (x' : Row (k * M)) (h : InF k M x x')
    (hx : (2 : ZMod M) • x ≠ 0) : (2 : ZMod (k * M)) • x' ≠ 0 := by
  intro h0
  apply hx
  obtain ⟨z, hz⟩ := lift_ex k M (x 0)
  have a0 : (2 : ZMod (k * M)) * x' 0 = 0 := congrFun h0 0
  have a1 : (2 : ZMod (k * M)) * x' 1 = 0 := congrFun h0 1
  have b0 : (2 : ZMod M) * x 0 = 0 := by
    rw [h.1, mul_eq_up k M x 0 z hz, mul_left_comm] at a0
    have := cast_eq_zero_of k M _ a0
    rwa [map_mul, hz, map_ofNat] at this
  have b1 : (2 : ZMod M) * x 1 = 0 := by
    have := congrArg (ZMod.castHom (dvd_mul_left M k) (ZMod M)) a1
    rw [map_mul, map_ofNat, map_zero] at this
    rw [← h.2]; exact this
  funext i
  fin_cases i
  · exact b0
  · exact b1

private theorem rt_zero {M : ℕ} (x : Row M) (γ : SL(2, ℤ)) : rt x γ 0 = x 0 * (γ.1 0 0 : ℤ) + x 1 * (γ.1 1 0 : ℤ) := by
  simp [rt, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem rt_one' {M : ℕ} (x : Row M) (γ : SL(2, ℤ)) : rt x γ 1 = x 0 * (γ.1 0 1 : ℤ) + x 1 * (γ.1 1 1 : ℤ) := by
  simp [rt, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem rt_rt {M : ℕ} (x : Row M) (γ δ : SL(2, ℤ)) : rt (rt x γ) δ = rt x (γ * δ) := by
  simp only [rt, Matrix.vecMul_vecMul, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]

private theorem rt_id {M : ℕ} (x : Row M) : rt x 1 = x := by
  simp [rt]

private theorem inF_rt (k M : ℕ) [NeZero k] [NeZero M] (γ γ' : SL(2, ℤ))
    (hg : !![(k : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), 0; 0, 1])
    (x : Row M) (x' : Row (k * M)) (h : InF k M x x') : InF k M (rt x γ') (rt x' γ) := by
  have hk : (k : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne k
  have e00 : γ'.1 0 0 = γ.1 0 0 := by
    have := congrFun (congrFun hg 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    exact mul_left_cancel₀ hk (by linarith)
  have e01 : γ'.1 0 1 = k * γ.1 0 1 := by
    have := congrFun (congrFun hg 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linarith
  have e10 : γ.1 1 0 = k * γ'.1 1 0 := by
    have := congrFun (congrFun hg 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linarith
  have e11 : γ'.1 1 1 = γ.1 1 1 := by
    have := congrFun (congrFun hg 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linarith
  obtain ⟨z, hz⟩ := lift_ex k M (x 0)
  have h0 : x' 0 = k * z := h.1.trans (mul_eq_up k M x 0 z hz)
  have h1 : ZMod.castHom (dvd_mul_left M k) (ZMod M) (x' 1) = x 1 := h.2
  constructor
  · rw [mul_eq_up k M (rt x γ') 0 (z * (γ'.1 0 0 : ℤ) + x' 1 * (γ'.1 1 0 : ℤ))
      (by rw [rt_zero, map_add, map_mul, map_mul, hz, h1, map_intCast, map_intCast]), rt_zero, h0, e00, e10]
    push_cast; ring
  · show ZMod.castHom (dvd_mul_left M k) (ZMod M) (rt x' γ 1) = _
    rw [rt_one', rt_one', h0, map_add, map_mul, map_mul, map_mul, hz, h1, map_intCast, map_intCast, map_natCast, e01, e11]
    push_cast; ring

private theorem rel_inv (k : ℕ) (γ γ' : SL(2, ℤ))
    (hg : !![(k : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), 0; 0, 1]) :
    !![(k : ℤ), 0; 0, 1] * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((γ'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), 0; 0, 1] := by
  have a : ((γ'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * γ' = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have b : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc _ = (((γ'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * γ') * !![(k : ℤ), 0; 0, 1] * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [a, one_mul]
    _ = _ := by rw [mul_assoc _ (γ' : Matrix (Fin 2) (Fin 2) ℤ), ← hg, mul_assoc, mul_assoc, b, mul_one]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem inF_gr (k M : ℕ) [NeZero k] [NeZero M] (s : Ω ≃ₐ[ℚ] Ω)
    (x : Row M) (x' : Row (k * M)) (h : InF k M x x') : InF k M (gr M s x) (gr (k * M) s x') := by
  have H := (rowB Ω M (Nat.pos_of_ne_zero (NeZero.ne M))).2.2.2 k (Nat.pos_of_ne_zero (NeZero.ne k))
  refine ⟨h.1, ?_⟩
  rw [H.2.2.2.2.1 s x']
  show cyc M s * dn k M x' 1 = cyc M s * x 1
  rw [h.2]

private theorem mv_cancel (X : Tower Ω ε) (m : ℕ) (hm : 0 < m) (τ τ' : X.K ≃+* X.K) (s s' : Ω ≃ₐ[ℚ] Ω) (hτ : admitted X τ s)
    (hτ' : admitted X τ' s') (u v : X.K) (P Q R : Pt X m) (hP : IsPt X m u v P) (hQ : IsPt X m (τ u) (τ v) Q)
    (hR : IsPt X m (τ' (τ u)) (τ' (τ v)) R) (f : X.Kˣ) (h1 : Mv X m τ s P Q 1) (h2 : Mv X m (τ.trans τ') (s' * s) P R f) :
    Mv X m τ' s' Q R f := by
  have E := mvEx Ω ε X m hm τ' s' hτ' _ _ Q hQ
  obtain ⟨f0, -, h0⟩ := E.1 R hR
  have hc := mvComp Ω ε X m hm τ τ' s s' hτ hτ' u v P Q R hP hQ hR 1 f0 h1 h0
  rw [map_one, one_pow, one_mul] at hc
  have hA := (admB Ω ε X).2.2.2.1 τ s τ' s' hτ hτ'
  exact (E.2.2.2 R hR f0 f h0).2 (((mvEx Ω ε X m hm _ _ hA u v P hP).2.2.2 R hR f0 f hc).1 h2)

private theorem mv_swap (X : Tower Ω ε) (m : ℕ) (hm : 0 < m) (τ ρ ρ' : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω) (hτ : admitted X τ 1)
    (hρ : admitted X ρ s) (hρ' : admitted X ρ' s) (hc : ∀ f, ρ' (τ f) = τ (ρ f)) (u v u' v' : X.K) (hu : ρ u = u') (hv : ρ v = v')
    (P P' Q Q' : Pt X m) (hP : IsPt X m u v P) (hP' : IsPt X m u' v' P') (hQ : IsPt X m (τ u) (τ v) Q)
    (hQ' : IsPt X m (τ u') (τ v') Q') (h1 : Mv X m τ 1 P Q 1) (h2 : Mv X m τ 1 P' Q' 1) (f : X.Kˣ)
    (h3 : Mv X m ρ s P P' f) : Mv X m ρ' s Q Q' (unU X τ f) := by
  subst hu hv
  have h4 := mvComp Ω ε X m hm ρ τ s 1 hρ hτ u v P P' Q' hP hP' hQ' f 1 h3 h2
  have hA := (admB Ω ε X).2.2.2.1 ρ s τ 1 hρ hτ
  have h5 : Mv X m (ρ.trans τ) (1 * s) P Q' (unU X τ f) := by
    refine ((mvEx Ω ε X m hm _ _ hA u v P hP).2.2.2 Q' hQ' _ _ h4).2 ?_
    rw [((lgB Ω ε X m hm).2.2.2.2.2.2 1 1).2.1, mul_one]
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hm) with h | h
    · subst h
      exact ⟨_, by rw [pow_one]; exact (mul_inv_cancel_left _ _).symm⟩
    · haveI : Fact (1 < m) := ⟨h⟩
      exact ⟨1, by rw [ZMod.val_one, pow_one, one_pow, mul_one]⟩
  have e : ρ.trans τ = τ.trans ρ' := RingEquiv.ext fun f => (hc f).symm
  rw [e, one_mul, ← mul_one s] at h5
  refine mv_cancel X m hm τ ρ' 1 s hτ hρ' u v P Q Q' hP hQ ?_ _ h1 h5
  rw [hc, hc]; exact hQ'

open Classical in
theorem pIsog : PIsog := by
  intro Ω _ _ _ ε X m c d k M _ _ hm hc hd hc6 hd6 hL t w' w ht hw' hw
  haveI : NeZero (k * M) := ⟨mul_ne_zero (NeZero.ne k) (NeZero.ne M)⟩
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hcM : Nat.Coprime c M := hL.2.1.coprime_mul_left_right
  have hdM : Nat.Coprime d M := hL.2.2.coprime_mul_left_right
  have RB := rowB Ω M hM
  have RB' := rowB Ω (k * M) hL.1
  have AB := admB Ω ε X
  have GD := galDg Ω ε X k hk
  have Sc := sgB Ω ε X c M hc hc6 hM hcM
  have Sd := sgB Ω ε X d M hd hd6 hM hdM
  have Sc' := sgB Ω ε X c (k * M) hc hc6 hL.1 hL.2.1
  have Sd' := sgB Ω ε X d (k * M) hd hd6 hL.1 hL.2.2
  let fib : Row M → Finset (Row (k * M)) := fun x => Finset.univ.filter (fun x' => x' 0 = up k M x 0 ∧ dn k M x' 1 = x 1)
  have mf : ∀ x x', x' ∈ fib x ↔ InF k M x x' := fun x x' => by simp only [fib, InF, Finset.mem_filter, Finset.mem_univ, true_and]
  have ne : ∀ x, (fib x).Nonempty := fun x => (inF_ex k M x).imp fun x' h => (mf x x').2 h
  have ok : ∀ x y, Ok x y → ∀ i ∈ fib x, ∀ j ∈ fib y, Ok i j := fun x y h i hi j hj =>
    ⟨inF_two k M x i ((mf _ _).1 hi) h.1, inF_two k M y j ((mf _ _).1 hj) h.2⟩
  have nzc : ∀ x y, Ok x y → ∀ i ∈ fib x, i ≠ 0 := fun x y h i hi =>
    (RB'.2.1 _ _ (ok x y h i hi _ (ne y).choose_spec)).1
  have nzd : ∀ x y, Ok x y → ∀ j ∈ fib y, j ≠ 0 := fun x y h j hj =>
    (RB'.2.1 _ _ (ok x y h _ (ne x).choose_spec j hj)).2.1
  have T' := fun (x y : Row M) (h : Ok x y) i (hi : i ∈ fib x) j (hj : j ∈ fib y) =>
    ht _ _ (Sc' i (nzc x y h i hi)).1 (Sd' j (nzd x y h j hj)).1
  have T := fun (x y : Row M) (h : Ok x y) => ht _ _ (Sc x (RB.2.1 x y h).1).1 (Sd y (RB.2.1 x y h).2.1).1
  have gg : ∀ (N : ℕ) (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (x : Row N), gr N s (gr N s⁻¹ x) = x ∧ gr N s⁻¹ (gr N s x) = x :=
    fun N hN s x => by
      have H := (rowB Ω N hN).1
      exact ⟨by rw [← (H _ _ x).1, mul_inv_cancel, (H 1 1 x).2], by rw [← (H _ _ x).1, inv_mul_cancel, (H 1 1 x).2]⟩
  have bg : ∀ (s : Ω ≃ₐ[ℚ] Ω) (x : Row M), Set.BijOn (gr (k * M) s⁻¹) (fib x) (fib (gr M s⁻¹ x)) := fun s x => by
    refine Set.InvOn.bijOn (f' := gr (k * M) s) ⟨fun i _ => (gg _ hL.1 s i).1, fun i _ => (gg _ hL.1 s i).2⟩
      (fun i hi => (mf _ _).2 (inF_gr k M _ x i ((mf _ _).1 hi))) fun i hi => (mf _ _).2 ?_
    have := inF_gr k M s _ i ((mf _ _).1 hi)
    rwa [(gg M hM s x).1] at this
  have rr : ∀ (N : ℕ) (γ : SL(2, ℤ)) (x : Row N), rt (rt x γ) γ⁻¹ = x ∧ rt (rt x γ⁻¹) γ = x := fun N γ x =>
    ⟨by rw [rt_rt, mul_inv_cancel, rt_id], by rw [rt_rt, inv_mul_cancel, rt_id]⟩
  have br : ∀ γ γ' : SL(2, ℤ),
      !![(k : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), 0; 0, 1] →
      ∀ x : Row M, Set.BijOn (fun i : Row (k * M) => rt i γ⁻¹) (fib (rt x γ') : Set (Row (k * M))) (fib x : Set (Row (k * M))) := fun γ γ' hg x => by
    refine Set.InvOn.bijOn (s := (fib (rt x γ') : Set (Row (k * M)))) (t := (fib x : Set (Row (k * M)))) (f' := fun i => rt i γ) ⟨fun i _ => (rr _ γ i).2, fun i _ => (rr _ γ i).1⟩
      (fun i hi => ?_) fun i hi => ?_
    · refine (mf _ _).2 ?_
      have := inF_rt k M _ _ (rel_inv k γ γ' hg) _ i ((mf _ _).1 hi)
      rwa [(rr M γ' x).1] at this
    · exact (mf (rt x γ') (rt i γ)).2 (inF_rt k M γ γ' hg x i ((mf x i).1 hi))
  have hR : ∀ x y : Row M, ∃ R : Pt X m, Ok x y →
      IsSum X m (fib x) (fib y) (fun i j => t (sg X c (k * M) i) (sg X d (k * M) j)) R ∧
      IsPt X m (slR X (dg k) (sg X c M x)) (slR X (dg k) (sg X d M y)) R := fun x y => by
    by_cases h : Ok x y
    · have S := sumB Ω ε X m hm _ _ (fib x) (fib y) (sg X c (k * M)) (sg X d (k * M)) _ (ne x) (ne y)
        fun i hi j hj => (T' x y h i hi j hj).1
      obtain ⟨R, hR⟩ := S.1
      have h2 := S.2 R hR
      have e1 := sgIsog Ω ε X c k M hc hc6 hL.2.1 x (RB.2.1 x y h).1
      have e2 := sgIsog Ω ε X d k M hd hd6 hL.2.2 y (RB.2.1 x y h).2.1
      refine ⟨R, fun _ => ⟨hR, ?_⟩⟩
      convert h2 using 1
      · exact e1.symm.trans (by congr)
      · exact e2.symm.trans (by congr)
    · exact ⟨t 1 1, fun h' => absurd h' h⟩
  choose R hR using hR
  have hQ : ∀ x y : Row M, ∃ Q : Pt X m, Ok x y →
      IsPt X m (slR X (dg k) (sg X c M x)) (slR X (dg k) (sg X d M y)) Q ∧
      Mv X m (slR X (dg k)) 1 (t (sg X c M x) (sg X d M y)) Q 1 := fun x y => by
    by_cases h : Ok x y
    · obtain ⟨Q, hQ⟩ := (mvEx Ω ε X m hm _ _ (AB.1 (dg k)) _ _ _ (T x y h).1).2.1
      exact ⟨Q, fun _ => hQ⟩
    · exact ⟨t 1 1, fun h' => absurd h' h⟩
  choose Q hQ using hQ
  obtain ⟨a, ha, hb⟩ := cmp Ω ε X m M hm hM (fun x => slR X (dg k) (sg X c M x)) (fun y => slR X (dg k) (sg X d M y)) R Q
    (fun s => pushH X k M (w' s)) (fun s x y => slU X (toGQ !![(k : ℤ), 0; 0, 1]) (w s x y))
    (fun x y h => ⟨(hR x y h).2, (hQ x y h).1⟩) (fun s x y h => by
      have h0 := (RB.2.1 x y h).2.2.1 s⁻¹
      have eu : X.gal s (sg X c M (gr M s⁻¹ x)) = sg X c M x := by
        rw [(Sc _ (RB.2.1 _ _ h0).1).2.2.1, (gg M hM s x).1]
      have ev : X.gal s (sg X d M (gr M s⁻¹ y)) = sg X d M y := by
        rw [(Sd _ (RB.2.1 _ _ h0).2.1).2.2.1, (gg M hM s y).1]
      refine ⟨(GD.1 s _).trans (congrArg _ eu), (GD.1 s _).trans (congrArg _ ev), ?_, ?_⟩
      · have := sumMv Ω ε X m hm _ _ _ (fib x) _ (fib y) (sg X c (k * M)) (sg X c (k * M)) (sg X d (k * M)) (sg X d (k * M))
          _ _ _ _ _ _ (X.gal s) s (AB.2.1 s) (ne _) (ne _) (bg s x) (bg s y)
          (fun i hi j hj => (T' _ _ h0 i hi j hj).1) (fun i hi j hj => (T' _ _ h i hi j hj).1)
          (fun i hi => by rw [(Sc' _ (nzc _ _ h0 _ ((bg s x).mapsTo hi))).2.2.1, (gg _ hL.1 s i).1])
          (fun i hi => by rw [(Sd' _ (nzd _ _ h0 _ ((bg s y).mapsTo hi))).2.2.1, (gg _ hL.1 s i).1])
          (hR _ _ h0).1 (hR _ _ h).1 (w' s) (fun i hi j hj => (hw' s i j (ok x y h i hi j hj)).2)
        convert this using 1
        simp only [pushH, fib]
      · exact mv_swap X m hm (slR X (dg k)) (X.gal s) (X.gal s) s (AB.1 _) (AB.2.1 s) (AB.2.1 s) (GD.1 s) _ _ _ _ eu ev
          _ _ _ _ (T _ _ h0).1 (T _ _ h).1 (hQ _ _ h0).1 (hQ _ _ h).1 (hQ _ _ h0).2 (hQ _ _ h).2 _ (hw s x y h).2)
  refine ⟨a, fun x y h => ⟨(hb x y h).1, fun γ γ' hg => ?_⟩, ha⟩
  have h1 := (RB.2.1 x y h).2.2.2 γ'
  have eu := (Sc x (RB.2.1 x y h).1).2.1 γ'
  have ev := (Sd y (RB.2.1 x y h).2.1).2.1 γ'
  refine (hb x y h).2 (slR X (ofSL γ)) _ _ (AB.1 _) h1 ((GD.2.1 γ γ' hg _).trans (congrArg _ eu))
    ((GD.2.1 γ γ' hg _).trans (congrArg _ ev)) ?_ ?_
  · have ei : ∀ i ∈ fib (rt x γ'), sg X c (k * M) i = X.sl (ofSL γ) (sg X c (k * M) (rt i γ⁻¹)) := fun i hi => by
      rw [(Sc' _ (nzc _ _ h _ ((br γ γ' hg x).mapsTo hi))).2.1, (rr _ γ i).2]
    have ej : ∀ i ∈ fib (rt y γ'), sg X d (k * M) i = X.sl (ofSL γ) (sg X d (k * M) (rt i γ⁻¹)) := fun i hi => by
      rw [(Sd' _ (nzd _ _ h _ ((br γ γ' hg y).mapsTo hi))).2.1, (rr _ γ i).2]
    have := sumMv Ω ε X m hm _ _ (fib x) _ (fib y) _ (sg X c (k * M)) (sg X c (k * M)) (sg X d (k * M)) (sg X d (k * M))
      _ _ _ _ _ _ (slR X (ofSL γ)) 1 (AB.1 _) (ne _) (ne _) (br γ γ' hg x) (br γ γ' hg y)
      (fun i hi j hj => (T' _ _ h i hi j hj).1) (fun i hi j hj => (T' _ _ h1 i hi j hj).1) ei ej
      (hR _ _ h).1 (hR _ _ h1).1 (fun _ _ => 1) (fun i hi j hj => by
        have := (T' _ _ h _ ((br γ γ' hg x).mapsTo hi) _ ((br γ γ' hg y).mapsTo hj)).2 γ
        rwa [← ei i hi, ← ej j hj] at this)
    simpa only [Finset.prod_const_one] using this
  · have h3 := (T x y h).2 γ'
    rw [eu, ev] at h3
    have := mv_swap X m hm (slR X (dg k)) (slR X (ofSL γ')) (slR X (ofSL γ)) 1 (AB.1 _) (AB.1 _) (AB.1 _) (GD.2.1 γ γ' hg)
      _ _ _ _ eu ev _ _ _ _ (T _ _ h).1 (T _ _ h1).1 (hQ _ _ h).1 (hQ _ _ h1).1 (hQ _ _ h).2 (hQ _ _ h1).2 _ h3
    rwa [map_one] at this

end UpperTheory.V.Z.Kato.Sym

end
