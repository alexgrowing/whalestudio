import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPowerUnitsTowerClosurePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerUnitGroupStableSlashGaloisStatement
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.Kd.K4

section Calc

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem cgF_iff (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (a b : X.Fn l) :
    CgF X l n a b ↔ ∀ u, AdicCompletion.eval (idl l) (X.Kl l) n (a u) =
      AdicCompletion.eval (idl l) (X.Kl l) n (b u) := by
  simp only [CgF, map_sub, sub_eq_zero]

private theorem cg_trans {X : Tower Ω ε} {l : ℕ} [Fact l.Prime] {n : ℕ} {a b c : X.Fn l}
    (h : CgF X l n a b) (h' : CgF X l n b c) : CgF X l n a c := by
  rw [cgF_iff] at *
  exact fun u => (h u).trans (h' u)

private theorem cg_symm {X : Tower Ω ε} {l : ℕ} [Fact l.Prime] {n : ℕ} {a b : X.Fn l}
    (h : CgF X l n a b) : CgF X l n b a := by
  rw [cgF_iff] at *
  exact fun u => (h u).symm

private theorem cg_sum {X : Tower Ω ε} {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Type} (s : Finset ι) {f g : ι → X.Fn l}
    (h : ∀ i ∈ s, CgF X l n (f i) (g i)) : CgF X l n (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  rw [cgF_iff]
  intro u
  simp only [Finset.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i hi => (cgF_iff X l n _ _).1 (h i hi) u

private theorem eval_kmap_eq (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : X.K ≃+* X.K) {y y' : X.Khat l}
    (h : AdicCompletion.eval (idl l) (X.Kl l) n y = AdicCompletion.eval (idl l) (X.Kl l) n y') :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y) =
      AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y') := by
  have e : ∀ z : X.Khat l, AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ z) =
      (LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap
        (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))).reduceModIdeal (idl l ^ n)
        (AdicCompletion.eval (idl l) (X.Kl l) n z) := fun _ => rfl
  rw [e, e, h]

private theorem rep_kmap {X : Tower Ω ε} {l : ℕ} [Fact l.Prime] {n : ℕ} {a : X.Kˣ} {x : X.Khat l}
    (h : Rep X l n a x) (φ : X.K ≃+* X.K) : Rep X l n (Units.map φ.toMonoidHom a) (X.kmap l φ x) := by
  unfold Rep at *
  have e : AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) =
      (LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap
        (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))).reduceModIdeal (idl l ^ n)
        (AdicCompletion.eval (idl l) (X.Kl l) n x) := rfl
  rw [e, h]
  rfl

private theorem cls_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (a b : X.Kˣ) :
    X.cls l n (a * b) = X.cls l n a + X.cls l n b := by
  unfold Tower.cls
  rw [← Submodule.Quotient.mk_add, ← TensorProduct.tmul_add]
  rfl

private theorem cls_one (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : X.cls l n 1 = 0 := by
  unfold Tower.cls
  rw [ofMul_one, TensorProduct.tmul_zero]
  rfl

private theorem cls_prod (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {ι : Type} (s : Finset ι) (f : ι → X.Kˣ) :
    X.cls l n (∏ i ∈ s, f i) = ∑ i ∈ s, X.cls l n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cls_one X l n
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, cls_mul, ih]

private theorem cls_zpow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (a : X.Kˣ) (z : ℤ) :
    X.cls l n (a ^ z) = (z : ℤ_[l]) • X.cls l n a := by
  unfold Tower.cls
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  rw [ofMul_zpow, TensorProduct.tmul_smul, Int.cast_smul_eq_zsmul]

private theorem cls_pow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (h : X.Kˣ) : X.cls l n (h ^ l ^ n) = 0 := by
  have e : h ^ l ^ n = h ^ (((l ^ n : ℕ)) : ℤ) := (zpow_natCast h _).symm
  rw [e, cls_zpow]
  unfold Tower.cls
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  simp

private theorem eval_smul_cong (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {r r' : ℤ_[l]}
    (h : (l : ℤ_[l]) ^ n ∣ r - r') (y : X.Khat l) :
    AdicCompletion.eval (idl l) (X.Kl l) n (r • y) = AdicCompletion.eval (idl l) (X.Kl l) n (r' • y) := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n y)
  rw [map_smul, map_smul, ← hx, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.eq, ← sub_smul]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private theorem act_sec_apply (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) (lam : Fin 2 → ℤ) (x : X.Khat l)
    (δ : SL(2, ℤ)) (u : Fin 2 → ℤ_[l]) :
    X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (sec X l w lam x) u =
      ((lam 0 : ℤ_[l]) * (mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 +
        (lam 1 : ℤ_[l]) * (mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1) ^ w •
        X.kmap l (X.sl (ofSL δ)).toRingEquiv x := by
  show X.kmap l _ (_ • _) = _
  rw [map_smul, toGQ_coe_SL]

private theorem act_sec_cg (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (lam : Fin 2 → ℤ) (x : X.Khat l)
    {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma (l ^ n)) :
    CgF X l n (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (sec X l w lam x))
      (sec X l w lam (X.kmap l (X.sl (ofSL δ)).toRingEquiv x)) := by
  rw [cgF_iff]
  intro u
  rw [act_sec_apply]
  show _ = AdicCompletion.eval (idl l) (X.Kl l) n (((lam 0 : ℤ_[l]) * u 0 + (lam 1 : ℤ_[l]) * u 1) ^ w • _)
  refine eval_smul_cong X l n ?_ _
  refine Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow _ _ w)
  rw [CongruenceSubgroup.Gamma_mem] at hδ
  have hd : ∀ a : ℤ, (a : ZMod (l ^ n)) = 0 → (l : ℤ_[l]) ^ n ∣ (a : ℤ_[l]) := fun a h => by
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (l ^ n)).1 h
    have e := map_dvd (Int.castRingHom ℤ_[l]) h1
    simpa using e
  have e : ((lam 0 : ℤ_[l]) * (mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 +
        (lam 1 : ℤ_[l]) * (mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1) -
      ((lam 0 : ℤ_[l]) * u 0 + (lam 1 : ℤ_[l]) * u 1) =
      (lam 0 : ℤ_[l]) * (((δ 0 0 - 1 : ℤ) : ℤ_[l]) * u 0 + ((δ 0 1 : ℤ) : ℤ_[l]) * u 1) +
      (lam 1 : ℤ_[l]) * (((δ 1 0 : ℤ) : ℤ_[l]) * u 0 + ((δ 1 1 - 1 : ℤ) : ℤ_[l]) * u 1) := by
    simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [e]
  have h00 := hd (δ 0 0 - 1) (by push_cast; rw [hδ.1, sub_self])
  have h01 := hd (δ 0 1) hδ.2.1
  have h10 := hd (δ 1 0) hδ.2.2.1
  have h11 := hd (δ 1 1 - 1) (by push_cast; rw [hδ.2.2.2, sub_self])
  exact dvd_add (Dvd.dvd.mul_left (dvd_add (h00.mul_right _) (h01.mul_right _)) _)
    (Dvd.dvd.mul_left (dvd_add (h10.mul_right _) (h11.mul_right _)) _)

private theorem sec_cong (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (lam : Fin 2 → ℤ) {y y' : X.Khat l}
    (h : AdicCompletion.eval (idl l) (X.Kl l) n y = AdicCompletion.eval (idl l) (X.Kl l) n y') :
    CgF X l n (sec X l w lam y) (sec X l w lam y') := by
  rw [cgF_iff]
  intro u
  show AdicCompletion.eval (idl l) (X.Kl l) n (_ • y) = AdicCompletion.eval (idl l) (X.Kl l) n (_ • y')
  rw [map_smul, map_smul, h]

private theorem act_cg (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) {a b : X.Fn l}
    (h : CgF X l n a b) : CgF X l n (X.act l m a) (X.act l m b) := by
  rw [cgF_iff] at *
  intro u
  exact eval_kmap_eq X l n _ (h _)

private theorem act_coset {X : Tower Ω ε} {l : ℕ} [Fact l.Prime] {n w : ℕ} {H : Subgroup SL(2, ℤ)}
    (hH : H ≤ CongruenceSubgroup.Gamma (l ^ n)) {a : X.Kˣ} (ha : InvH X H (l ^ n) a) {x x' : X.Khat l}
    (hx : Rep X l n a x) (hx' : Rep X l n a x') (lam : Fin 2 → ℤ) {h : SL(2, ℤ)} (hh : h ∈ H) (g : SL(2, ℤ)) :
    CgF X l n (X.act l ((h * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (sec X l w lam x'))
      (X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) (sec X l w lam x)) := by
  rw [← act_act_SL]
  refine act_cg X l n _ (cg_trans (act_sec_cg X l w n lam x' (hH hh)) (sec_cong X l w n lam ?_))
  obtain ⟨t, ht⟩ := ha h hh
  have e : Units.map (X.sl (ofSL h)).toRingEquiv.toMonoidHom a = a * t ^ l ^ n := Units.ext (by simpa using ht)
  have h1 := rep_kmap hx' (X.sl (ofSL h)).toRingEquiv
  unfold Rep at h1 hx
  rw [h1, e, cls_mul, cls_pow, add_zero, hx]

private theorem tr_cg {X : Tower Ω ε} {l : ℕ} [Fact l.Prime] {n w : ℕ} {H G : Subgroup SL(2, ℤ)}
    (hH : H ≤ CongruenceSubgroup.Gamma (l ^ n)) {a : X.Kˣ} (ha : InvH X H (l ^ n) a) {x x' : X.Khat l}
    (hx : Rep X l n a x) (hx' : Rep X l n a x') (lam : Fin 2 → ℤ) {ι ι' : Type} [Fintype ι] [Fintype ι']
    {γ : ι → SL(2, ℤ)} {γ' : ι' → SL(2, ℤ)} (hγ : IsTr H G γ) (hγ' : IsTr H G γ') :
    CgF X l n (trH X l w γ lam x) (trH X l w γ' lam x') := by
  classical
  choose σ hσ hσ' using fun j => hγ.2 (γ' j) (hγ'.1 j)
  have bij : Function.Bijective σ := by
    constructor
    · intro j j' e
      have h1 : γ' j * (γ (σ j))⁻¹ ∈ H := hσ j
      have h2 : γ' j' * (γ (σ j))⁻¹ ∈ H := e ▸ hσ j'
      obtain ⟨k, -, hk⟩ := hγ'.2 (γ' j') (hγ'.1 j')
      have h3 : γ' j' * (γ' j)⁻¹ ∈ H := by
        have := H.mul_mem h2 (H.inv_mem h1)
        simpa [mul_assoc] using this
      have h4 : γ' j' * (γ' j')⁻¹ ∈ H := by simpa using H.one_mem
      exact (hk j h3).trans (hk j' h4).symm
    · intro i
      obtain ⟨j, hj, -⟩ := hγ'.2 (γ i) (hγ.1 i)
      refine ⟨j, ?_⟩
      have h1 : γ' j * (γ i)⁻¹ ∈ H := by
        have := H.inv_mem hj
        simpa using this
      exact (hσ' j i h1).symm
  unfold trH
  rw [← Function.Bijective.sum_comp bij]
  refine cg_symm (cg_sum _ fun j _ => ?_)
  have := act_coset (w := w) hH ha hx hx' lam (hσ j) (γ (σ j))
  rwa [inv_mul_cancel_right] at this

private theorem isTr_mul {H G : Subgroup SL(2, ℤ)} {ι : Type} {γ : ι → SL(2, ℤ)} (hγ : IsTr H G γ) {g : SL(2, ℤ)}
    (hg : g ∈ G) : IsTr H G fun i => γ i * g := by
  refine ⟨fun i => G.mul_mem (hγ.1 i) hg, fun d hd => ?_⟩
  obtain ⟨i, hi, hi'⟩ := hγ.2 (d * g⁻¹) (G.mul_mem hd (G.inv_mem hg))
  refine ⟨i, ?_, fun j hj => hi' j ?_⟩
  · show d * (γ i * g)⁻¹ ∈ H
    rw [mul_inv_rev, ← mul_assoc]
    exact hi
  · have : d * (γ j * g)⁻¹ ∈ H := hj
    rw [mul_inv_rev, ← mul_assoc] at this
    exact this

private theorem isTr_comp {H H' G : Subgroup SL(2, ℤ)} {ι κ : Type} {γ : ι → SL(2, ℤ)} {δ : κ → SL(2, ℤ)}
    (hHH : H' ≤ H) (hH : H ≤ G) (hγ : IsTr H G γ) (hδ : IsTr H' H δ) :
    IsTr H' G fun p : κ × ι => δ p.1 * γ p.2 := by
  refine ⟨fun p => G.mul_mem (hH (hδ.1 p.1)) (hγ.1 p.2), fun d hd => ?_⟩
  obtain ⟨i, hi, hi'⟩ := hγ.2 d hd
  obtain ⟨k, hk, hk'⟩ := hδ.2 _ hi
  refine ⟨(k, i), ?_, ?_⟩
  · show d * (δ k * γ i)⁻¹ ∈ H'
    rw [mul_inv_rev, ← mul_assoc]
    exact hk
  · rintro ⟨k2, i2⟩ h
    have h0 : d * (δ k2 * γ i2)⁻¹ ∈ H' := h
    have h' : d * (γ i2)⁻¹ * (δ k2)⁻¹ ∈ H' := by
      rw [mul_inv_rev, ← mul_assoc] at h0
      exact h0
    have hi2 : d * (γ i2)⁻¹ ∈ H := by
      have := H.mul_mem (hHH h') (hδ.1 k2)
      simpa using this
    have e1 : i2 = i := hi' i2 hi2
    subst e1
    have e2 : k2 = k := hk' k2 h'
    subst e2
    rfl

private theorem tr_comp {X : Tower Ω ε} {l : ℕ} [Fact l.Prime] {n w : ℕ} {H H' : Subgroup SL(2, ℤ)}
    (hH : H ≤ CongruenceSubgroup.Gamma (l ^ n)) {a a' h : X.Kˣ} {x x' : X.Khat l}
    (hx : Rep X l n a x) (hx' : Rep X l n a' x') (lam : Fin 2 → ℤ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (γ : ι → SL(2, ℤ)) {δ : κ → SL(2, ℤ)} (hδ : IsTr H' H δ)
    (hp : ∏ i, X.sl (ofSL (δ i)) (a' : X.K) = a * (h : X.K) ^ l ^ n) :
    CgF X l n (trH X l w (fun p : κ × ι => δ p.1 * γ p.2) lam x') (trH X l w γ lam x) := by
  classical
  unfold trH
  rw [Fintype.sum_prod_type_right]
  refine cg_sum _ fun i _ => ?_
  simp only [← act_act_SL]
  rw [← map_sum]
  refine act_cg X l n _ ?_
  rw [cgF_iff]
  intro u
  rw [Finset.sum_apply, map_sum]
  set r : ℤ_[l] := ((lam 0 : ℤ_[l]) * u 0 + (lam 1 : ℤ_[l]) * u 1) ^ w with hr
  have hk : ∀ k, AdicCompletion.eval (idl l) (X.Kl l) n
      (X.act l (δ k : Matrix (Fin 2) (Fin 2) ℤ) (sec X l w lam x') u) =
      r • X.cls l n (Units.map (X.sl (ofSL (δ k))).toRingEquiv.toMonoidHom a') := by
    intro k
    rw [(cgF_iff X l n _ _).1 (act_sec_cg X l w n lam x' (hH (hδ.1 k))) u]
    show AdicCompletion.eval (idl l) (X.Kl l) n (r • _) = _
    rw [map_smul]
    congr 1
    exact rep_kmap hx' _
  rw [Finset.sum_congr rfl fun k _ => hk k, ← Finset.smul_sum, ← cls_prod]
  have e : ∏ k, Units.map (X.sl (ofSL (δ k))).toRingEquiv.toMonoidHom a' = a * h ^ l ^ n :=
    Units.ext (by simpa [Units.coe_prod] using hp)
  rw [e, cls_mul, cls_pow, add_zero]
  show _ = AdicCompletion.eval (idl l) (X.Kl l) n (r • x)
  rw [map_smul, hx]

private theorem jHol (X : Tower Ω ε) : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) :=
  let ⟨φ, h1, h2⟩ := X.j_hol
  ⟨φ, h2, h1⟩

private def unS [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (m : ℕ) : Subgroup X.Kˣ where
  carrier := X.Un m
  mul_mem' := fun {f g} hf hg => (GlobalTheory.T.localPowerUnitsTower_closure_properties ε X ε.injective (jHol X) m).2.1 f g hf hg
  one_mem' := (GlobalTheory.T.localPowerUnitsTower_closure_properties ε X ε.injective (jHol X) m).1
  inv_mem' := fun {f} hf => (GlobalTheory.T.localPowerUnitsTower_closure_properties ε X ε.injective (jHol X) m).2.2.1 f hf

private theorem polMod_tr [IsAlgClosure ℚ Ω] {X : Tower Ω ε} {l : ℕ} [Fact l.Prime] {n w : ℕ} {a : X.Kˣ}
    {x : X.Khat l} (hx : Rep X l n a x) (ha : a ∈ X.Un (l ^ n)) (lam : Fin 2 → ℤ) {ι : Type} [Fintype ι]
    (γ : ι → SL(2, ℤ)) : PolMod X l w n (trH X l w γ lam x) := by
  classical
  let b : ι → X.Kˣ := fun i => Units.map (X.sl (ofSL (γ i))).toRingEquiv.toMonoidHom a
  let p : ι → ℤ := fun i => lam 0 * γ i 0 0 + lam 1 * γ i 1 0
  let q : ι → ℤ := fun i => lam 0 * γ i 0 1 + lam 1 * γ i 1 1
  let z : ι → ℕ → ℤ := fun i k => p i ^ k * q i ^ (w - k) * (w.choose k : ℤ)
  have hb : ∀ i, b i ∈ X.Un (l ^ n) := fun i =>
    (GlobalTheory.T.modularFunctionTower_unitGroup_stable_slash_galois ε X ε.injective (jHol X) (l ^ n) a ha).1 (ofSL (γ i)) (b i) rfl
  have hr : ∀ i, Rep X l n (b i) (X.kmap l (X.sl (ofSL (γ i))).toRingEquiv x) := fun i => rep_kmap hx _
  refine ⟨fun k => ∑ i, ((z i k : ℤ) : ℤ_[l]) • X.kmap l (X.sl (ofSL (γ i))).toRingEquiv x,
    fun k => ⟨∏ i, b i ^ z i k, ?_, ?_⟩, fun u => ?_⟩
  · exact (unS X (l ^ n)).prod_mem fun i _ => (unS X (l ^ n)).zpow_mem (hb i) _
  · unfold Rep
    rw [map_sum, cls_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, cls_zpow, hr i]
  · unfold trH
    rw [Finset.sum_apply]
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act_sec_apply]
    have e : (lam 0 : ℤ_[l]) * (mZl l (γ i : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 +
        (lam 1 : ℤ_[l]) * (mZl l (γ i : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1 =
        (p i : ℤ_[l]) * u 0 + (q i : ℤ_[l]) * u 1 := by
      simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, p, q]
      ring
    rw [e, add_pow, Finset.sum_smul, Fin.sum_univ_eq_sum_range
      (fun k => (u 0 ^ k * u 1 ^ (w - k)) • ((z i k : ℤ) : ℤ_[l]) • X.kmap l (X.sl (ofSL (γ i))).toRingEquiv x) (w + 1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul]
    congr 1
    simp only [z]
    push_cast
    rw [mul_pow, mul_pow]
    ring

end Calc

end UpperTheory.Kd.K4

theorem UpperTheory.Kd.K4.trc :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l : ℕ) [Fact l.Prime] (N w n : ℕ) (H : Subgroup SL(2, ℤ)), H ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) →
      ∀ (ι : Type) [Fintype ι] (γ : ι → SL(2, ℤ)), IsTr H (Gam N l) γ → ∀ (lam : Fin 2 → ℤ) (a : X.Kˣ) (x : X.Khat l), Rep X l n a x →
      (a ∈ X.Un (l ^ n) → PolMod X l w n (trH X l w γ lam x)) ∧
      (InvH X H (l ^ n) a → ∀ g ∈ Gam N l, CgF X l n (X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) (trH X l w γ lam x)) (trH X l w γ lam x)) ∧
      (InvH X H (l ^ n) a → ∀ (ι' : Type) [Fintype ι'] (γ' : ι' → SL(2, ℤ)), IsTr H (Gam N l) γ' → ∀ x' : X.Khat l, Rep X l n a x' →
        CgF X l n (trH X l w γ lam x) (trH X l w γ' lam x')) ∧
      (∀ (H' : Subgroup SL(2, ℤ)) (κ : Type) [Fintype κ] (δ : κ → SL(2, ℤ)), H' ≤ H → IsTr H' H δ →
        IsTr H' (Gam N l) (fun p : κ × ι => δ p.1 * γ p.2) ∧ ∀ (a' h : X.Kˣ) (x' : X.Khat l), Rep X l n a' x' →
          ∏ i, X.sl (ofSL (δ i)) (a' : X.K) = a * (h : X.K) ^ l ^ n →
          CgF X l n (trH X l w (fun p : κ × ι => δ p.1 * γ p.2) lam x') (trH X l w γ lam x)) := by
  intro Ω _ _ _ ε X l _ N w n H hH ι _ γ hγ lam a x hx
  have hH1 : H ≤ CongruenceSubgroup.Gamma (l ^ n) := hH.trans inf_le_right
  have hH2 : H ≤ Gam N l := hH.trans inf_le_left
  refine ⟨fun ha => polMod_tr hx ha lam γ, fun hi g hg => ?_, fun hi ι' _ γ' hγ' x' hx' => tr_cg hH1 hi hx hx' lam hγ hγ',
    fun H' κ _ δ hHH hδ => ⟨isTr_comp hHH hH2 hγ hδ, fun a' h x' hx' hp => tr_comp hH1 hx hx' lam γ hδ hp⟩⟩
  have e : X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) (trH X l w γ lam x) = trH X l w (fun i => γ i * g) lam x := by
    unfold trH
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => act_act_SL X l _ _ _
  rw [e]
  exact tr_cg hH1 hi hx hx lam (isTr_mul hγ hg) hγ
