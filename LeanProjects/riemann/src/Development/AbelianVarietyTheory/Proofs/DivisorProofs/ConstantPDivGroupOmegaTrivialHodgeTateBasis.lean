import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra WithConv

namespace GlobalTheory.ConstHT

theorem isIntegrallyClosedIn_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

theorem exists_eq_apply_of_algHom {O : Type} [CommRing O] [IsDomain O] {N : ℕ}
    (f : (Fin N → O) →ₐ[O] O) : ∃ k, ∀ v, f v = v k := by
  have hsq : ∀ k, (Pi.single k (1 : O) : Fin N → O) * Pi.single k 1 = Pi.single k 1 := fun k => by
    ext j; by_cases hj : j = k <;> simp [Pi.single_apply, hj]
  have hid : ∀ k, f (Pi.single k 1) = 0 ∨ f (Pi.single k 1) = 1 := fun k =>
    IsIdempotentElem.iff_eq_zero_or_one.1 (by
      change f _ * f _ = f _
      rw [← map_mul, hsq])
  have hsum : ∑ k, f (Pi.single k 1) = 1 := by
    rw [← map_sum, ← map_one f]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨k, hk⟩ : ∃ k, f (Pi.single k 1) = 1 := by
    by_contra hne
    push_neg at hne
    have h0 : ∑ k, f (Pi.single k 1) = 0 :=
      Finset.sum_eq_zero fun k _ => (hid k).resolve_right (hne k)
    exact zero_ne_one (h0.symm.trans hsum)
  refine ⟨k, fun v => ?_⟩
  have h1 : v * Pi.single k 1 = (v k) • (Pi.single k 1 : Fin N → O) := by
    ext j; by_cases hj : j = k <;> simp [Pi.single_apply, hj]
  calc f v = f v * f (Pi.single k 1) := by rw [hk, mul_one]
    _ = v k := by rw [← map_mul, h1, map_smul, hk, smul_eq_mul, mul_one]

theorem cot_eq_zero_of_equiv {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Bialgebra O A]
    {N : ℕ} (e : A ≃ₐ[O] (Fin N → O)) (w : Cot O A) : w = 0 := by
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ w
  obtain ⟨k, hk⟩ := exists_eq_apply_of_algHom ((counitAlgHom O A).comp (e.symm : (Fin N → O) →ₐ[O] A))
  have he : ∀ x, counitAlgHom O A x = e x k := fun x => by
    have := hk (e x)
    simpa using this
  set b := a - algebraMap O A (counitAlgHom O A a) with hbdef
  set c := e.symm (1 - Pi.single k 1) with hcdef
  have hb : counitAlgHom O A b = 0 := by simp [b]
  have hc : counitAlgHom O A c = 0 := by rw [he]; simp [c]
  have hbc : b = b * c := e.injective <| funext fun j => by
    rw [map_mul, Pi.mul_apply]
    by_cases hj : j = k
    · subst hj
      rw [← he, ← he, hb, zero_mul]
    · simp [c, hj]
  have h : AugCot.d (counitAlgHom O A) b = 0 := by
    rw [hbc, AugCot.d_mul, hb, hc, zero_smul, zero_smul, add_zero]
  rwa [hbdef, map_sub, AugCot.d_algebraMap, sub_zero] at h

theorem hodgeTate_smul_val {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)
    (a : ℤ_[p]) (t : G.Tate) (n : ℕ) :
    (hodgeTate G (a • t)).1 n = (digit n a : O) • (hodgeTate G t).1 n := by
  obtain ⟨c, hc⟩ := pow_dvd_sub_digit n a
  have ha : a = (digit n a : ℤ_[p]) + (p : ℤ_[p]) ^ n * c := by rw [← hc]; ring
  have h2 : (hodgeTate G ((p : ℤ_[p]) ^ n • (c • t))).1 n = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul]
    change (p ^ n) • ((hodgeTate G (c • t)).1 n) = 0
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
    exact G.dual.pow_smul_cot n _
  have h3 : (hodgeTate G ((digit n a : ℤ_[p]) • t)).1 n = (digit n a : O) • (hodgeTate G t).1 n := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul O]
    rfl
  have e1 : a • t = (digit n a : ℤ_[p]) • t + (p : ℤ_[p]) ^ n • (c • t) := by
    rw [← mul_smul, ← add_smul, ← ha]
  rw [e1, map_add]
  change (hodgeTate G _).1 n + (hodgeTate G _).1 n = _
  rw [h2, add_zero, h3]

end GlobalTheory.ConstHT

namespace GlobalTheory.ConstHT
open GlobalTheory.PDivLat

theorem level_span (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsIntegrallyClosedIn O C]
    (G : PDivGroup p O) (hG : IsConst G) (h : ℕ) (b : Module.Basis (Fin h) ℤ_[p] G.Tate) (n : ℕ)
    (w : Cot O (G.dual.A n)) : ∃ c : Fin h → O, ∑ i, c i • (hodgeTate G (b i)).1 n = w := by
  obtain ⟨e⟩ := hG n
  let Lev : (Fin h → O) →ₗ[O] Cot O (G.dual.A n) :=
    (LinearMap.proj n ∘ₗ G.dual.omegaSub.subtype) ∘ₗ
      Fintype.linearCombination O (fun i => hodgeTate G (b i))
  have hLev : ∀ c, Lev c = ∑ i, c i • (hodgeTate G (b i)).1 n := fun c => by
    simp only [Lev, LinearMap.comp_apply, Fintype.linearCombination_apply, map_sum, map_smul]
    rfl
  have hpt : ∀ t : G.Tate, (hodgeTate G t).1 n ∈ LinearMap.range Lev := fun t => by
    refine ⟨fun i => (digit n (b.repr t i) : O), ?_⟩
    rw [hLev]
    conv_rhs => rw [← b.sum_repr t]
    rw [map_sum]
    change _ = ((∑ i, hodgeTate G (b.repr t i • b i) : G.dual.omega) : ∀ k, Cot O (G.dual.A k)) n
    rw [Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (hodgeTate_smul_val G _ _ n).symm
  let β : Module.Basis (Fin (p ^ (n * G.height))) O (G.A n) :=
    (Pi.basisFun O (Fin (p ^ (n * G.height)))).map e.symm.toLinearEquiv
  let γ : Fin (p ^ (n * G.height)) → (G.A n →ₐ[O] O) := fun k =>
    (Pi.evalAlgHom O (fun _ => O) k).comp (e : G.A n →ₐ[O] _)
  have hγ : ∀ k, β.coord k = (γ k).toLinearMap := fun k => LinearMap.ext fun x => by
    simp [β, γ]
  have hmem : ∀ k, dUnit O (toConv (γ k).toLinearMap : CartierDual O (G.A n)) ∈
      LinearMap.range Lev := fun k => by
    obtain ⟨t, ht⟩ := G.pt_surjective C n (γ k)
    have := hodgeTate_val t n
    simp only at ht
    rw [ht] at this
    rw [← this]
    exact hpt t
  obtain ⟨φ, rfl⟩ := AugCot.d_surjective _ w
  have hφ : φ = ∑ k, φ.ofConv (β k) • (toConv (γ k).toLinearMap : CartierDual O (G.A n)) := by
    refine WithConv.ofConv_injective ?_
    conv_lhs => rw [← β.sum_dual_apply_smul_coord φ.ofConv]
    change _ = CartierDual.toDual O (G.A n) _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hγ]
    rfl
  suffices hw : AugCot.d (counitAlgHom O (G.dual.A n)) φ ∈ LinearMap.range Lev by
    obtain ⟨c, hc⟩ := hw
    exact ⟨c, (hLev c).symm.trans hc⟩
  rw [hφ, map_sum]
  exact Submodule.sum_mem _ fun k _ => by rw [map_smul]; exact Submodule.smul_mem _ _ (hmem k)

end GlobalTheory.ConstHT

namespace GlobalTheory.ConstHT
open GlobalTheory.PDivLat

theorem level_indep (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsIntegrallyClosedIn O C]
    (G : PDivGroup p O) (hG : IsConst G) (h : ℕ) (b : Module.Basis (Fin h) ℤ_[p] G.Tate) (n : ℕ)
    (c : Fin h → O) (hc : ∑ i, c i • (hodgeTate G (b i)).1 n = 0) (i : Fin h) :
    (p : O) ^ n ∣ c i := by
  obtain ⟨e⟩ := hG n
  let β : Module.Basis (Fin (p ^ (n * G.height))) O (G.A n) :=
    (Pi.basisFun O (Fin (p ^ (n * G.height)))).map e.symm.toLinearEquiv
  let γ : Fin (p ^ (n * G.height)) → (G.A n →ₐ[O] O) := fun k =>
    (Pi.evalAlgHom O (fun _ => O) k).comp (e : G.A n →ₐ[O] _)
  have hγ : ∀ k, β.coord k = (γ k).toLinearMap := fun k => LinearMap.ext fun x => by
    simp [β, γ]
  let B : Module.Basis (Fin (p ^ (n * G.height))) O (CartierDual O (G.A n)) :=
    β.dualBasis.map (CartierDual.toDual O (G.A n)).symm
  have hB : ∀ k, B k = toConv (γ k).toLinearMap := fun k => by
    simp only [B, Module.Basis.map_apply, Module.Basis.coe_dualBasis, hγ]
    rfl
  have hall : ∀ x : G.A n →ₐ[O] O, ∃ k, x = γ k := fun x => by
    obtain ⟨k, hk⟩ := exists_eq_apply_of_algHom (x.comp e.symm.toAlgHom)
    exact ⟨k, AlgHom.ext fun a => by simpa [γ] using hk (e a)⟩
  let Q := O ⧸ Ideal.span {(p : O) ^ n}
  let g : ZMod (p ^ n) →+ Q := ZMod.lift (p ^ n) ⟨Int.castAddHom Q, by
    change (((p ^ n : ℕ) : ℤ) : Q) = 0
    rw [Int.cast_natCast, Nat.cast_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)⟩
  have hg1 : g 1 = 1 := by
    rw [← Int.cast_one, ZMod.lift_coe]
    simp
  let f : G.Tate →+ Q :=
    g.comp ((PadicInt.toZModPow n).toAddMonoidHom.comp (b.coord i).toAddMonoidHom)
  have hz : ((p : ZMod (p ^ n)) ^ n) = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hf0 : ∀ u : G.Tate, f ((p : ℤ_[p]) ^ n • u) = 0 := fun u => by
    simp only [f, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, map_smul,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, smul_eq_mul, map_mul, map_pow,
      map_natCast]
    rw [hz, zero_mul, map_zero]
  have hf : ∀ t s : G.Tate, t.pt n = s.pt n → f t = f s := fun t s hts => by
    have h1 : tateLevel G n (t - s) = 0 := by
      rw [map_sub, sub_eq_zero, tateLevel_apply, tateLevel_apply]
      simp only [TateOver.conv, hts]
    obtain ⟨u, hu⟩ := (TateOver.conv_eq_one_iff (t - s) n).1 (by simpa using h1)
    rw [← sub_eq_zero, ← map_sub, ← hu, hf0]
  let a : (G.A n →ₐ[O] O) → Q := fun x => f (Classical.choose (G.pt_surjective C n x))
  have ha : ∀ t : G.Tate, a (t.pt n) = f t := fun t =>
    hf _ _ (Classical.choose_spec (G.pt_surjective C n (t.pt n)))
  let D : CartierDual O (G.A n) →ₗ[O] Q := B.constr O (fun k => a (γ k))
  have hDpt : ∀ x : G.A n →ₐ[O] O, D (toConv x.toLinearMap) = a x := fun x => by
    obtain ⟨k, rfl⟩ := hall x
    rw [← hB, Module.Basis.constr_basis]
  have hε : ∀ x : G.A n →ₐ[O] O,
      counitAlgHom O (CartierDual O (G.A n)) (toConv x.toLinearMap) = 1 := fun x => by
    rw [Bialgebra.counitAlgHom_apply, CartierDual.counit_apply]
    exact map_one x
  have hmul : ∀ x y : G.A n →ₐ[O] O, a (toConv x * toConv y).ofConv = a x + a y := fun x y => by
    obtain ⟨t, rfl⟩ := G.pt_surjective C n x
    obtain ⟨s, rfl⟩ := G.pt_surjective C n y
    change a ((t + s).pt n) = _
    rw [ha, ha, ha, map_add]
  let M : CartierDual O (G.A n) →ₗ[O] CartierDual O (G.A n) →ₗ[O] Q :=
    (LinearMap.lsmul O Q).compl₁₂ (counitAlgHom O (CartierDual O (G.A n))).toLinearMap D
  have key : (LinearMap.mul O (CartierDual O (G.A n))).compr₂ D = M + M.flip :=
    B.ext fun k => B.ext fun l => by
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.add_apply,
        LinearMap.flip_apply, M, LinearMap.compl₁₂_apply, LinearMap.lsmul_apply,
        AlgHom.toLinearMap_apply, hB, hε, one_smul]
      rw [← AlgHom.toLinearMap_convMul, hDpt, hDpt, hDpt, hmul, add_comm]
  have hD : ∀ u v, D (u * v) = counitAlgHom O (CartierDual O (G.A n)) u • D v +
      counitAlgHom O (CartierDual O (G.A n)) v • D u := fun u v =>
    LinearMap.congr_fun₂ key u v
  let Dl := AugCot.lift (counitAlgHom O (CartierDual O (G.A n))) D hD
  have hDl : ∀ i', Dl ((hodgeTate G (b i')).1 n) = if i' = i then 1 else 0 := fun i' => by
    rw [hodgeTate_val]
    change Dl (AugCot.d _ _) = _
    rw [AugCot.lift_d, hDpt, ha]
    simp only [f, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply,
      Module.Basis.repr_self, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    by_cases hi : i' = i
    · subst hi; rw [Finsupp.single_eq_same, map_one, hg1, if_pos rfl]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hi), map_zero, map_zero, if_neg hi]
  have h2 := congrArg Dl hc
  rw [map_sum, map_zero] at h2
  simp only [map_smul, hDl, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  rw [Algebra.smul_def, mul_one] at h2
  exact h2

end GlobalTheory.ConstHT

namespace GlobalTheory.ConstHT
open GlobalTheory.PDivLat

theorem omega_const : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, IsConst G → Subsingleton G.omega ∧ ∀ (h : ℕ) (b : Module.Basis (Fin h) ℤ_[p] G.Tate), Function.Bijective (Fintype.linearCombination O fun i => hodgeTate G (b i)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G hG
  haveI := isIntegrallyClosedIn_of_integers hv
  refine ⟨⟨fun x y => Subtype.ext (funext fun n => ?_)⟩, fun h b => ?_⟩
  · obtain ⟨e⟩ := hG n
    rw [cot_eq_zero_of_equiv e (x.1 n), cot_eq_zero_of_equiv e (y.1 n)]
  set Φ := Fintype.linearCombination O fun i => hodgeTate G (b i) with hΦ
  have hval : ∀ c n, (Φ c).1 n = ∑ i, c i • (hodgeTate G (b i)).1 n := fun c n => by
    rw [hΦ, Fintype.linearCombination_apply]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  have hsmod : ∀ (n : ℕ) (x y : O),
      x ≡ y [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔ (p : O) ^ n ∣ x - y :=
    fun n x y => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    funext i
    refine IsHausdorff.haus' (I := Ideal.span {(p : O)}) (c i) fun n => (hsmod n _ _).2 ?_
    rw [sub_zero]
    exact level_indep p C O G hG h b n c (by rw [← hval, hc]; rfl) i
  · intro w
    choose c hc using fun n => level_span p C O G hG h b n (w.1 n)
    have hcompat : ∀ n i, (p : O) ^ n ∣ c (n + 1) i - c n i := fun n =>
      level_indep p C O G hG h b n _ (by
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
        rw [sub_eq_zero, hc n, ← w.2 n, ← hc (n + 1), map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, (hodgeTate G (b i)).2 n])
    have hL : ∀ i, ∃ L : O, ∀ n, (p : O) ^ n ∣ c n i - L := fun i => by
      obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) (fun n => c n i)
        fun {m n} hmn => by
          induction n, hmn using Nat.le_induction with
          | base => exact SModEq.refl _
          | succ n hmn ih =>
            exact ih.trans ((hsmod m _ _).2 (dvd_sub_comm.1
              ((pow_dvd_pow _ hmn).trans (hcompat n i))))
      exact ⟨L, fun n => (hsmod n _ _).1 (hL n)⟩
    choose L hL using hL
    refine ⟨L, Subtype.ext (funext fun n => ?_)⟩
    change (Φ L).1 n = w.1 n
    rw [hval, ← hc n, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨d, hd⟩ := hL i n
    rw [← sub_smul, show L i - c n i = -((p : O) ^ n * d) by rw [← hd]; ring, neg_smul, mul_smul,
      G.dual.pow_smul_cot n, neg_zero]

end GlobalTheory.ConstHT
