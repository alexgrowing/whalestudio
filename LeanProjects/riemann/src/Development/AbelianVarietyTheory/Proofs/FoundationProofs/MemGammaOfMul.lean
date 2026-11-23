import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixPrimeDetCosetRepresentatives
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES.HeckeLev

def rep (M q : ℕ) (γ : SL(2, ℤ)) : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]
  | some j => !![1, ((j : ℕ) : ℤ) * (M : ℤ); 0, (q : ℤ)]

theorem det_rep (M q : ℕ) (γ : SL(2, ℤ)) (o : Option (Fin q)) : (rep M q γ o).det = q := by
  cases o with
  | none => simp [rep, Matrix.det_mul, Matrix.det_fin_two]
  | some j => simp [rep, Matrix.det_fin_two]

abbrev red (M : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) (ZMod M) :=
  (Int.castRingHom (ZMod M)).mapMatrix m

theorem red_mul (M : ℕ) (m m' : Matrix (Fin 2) (Fin 2) ℤ) : red M (m * m') = red M m * red M m' :=
  RingHom.map_mul _ _ _

theorem red_rep {M q : ℕ} {γ : SL(2, ℤ)} (hγ : DiagMod M q γ) (o : Option (Fin q)) :
    red M (rep M q γ o) = !![1, 0; 0, (q : ZMod M)] := by
  obtain ⟨h01, h10, h11⟩ := hγ
  simp only [en] at h01 h10 h11
  cases o with
  | some j =>
    ext i k; fin_cases i <;> fin_cases k <;> simp [rep, red]
  | none =>
    have hdet : (γ 0 0 : ZMod M) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rw [Matrix.det_fin_two] at this
      have := congrArg (fun z : ℤ => (z : ZMod M)) this; push_cast at this; exact this
    rw [h01, h10, h11] at hdet
    ext i k; fin_cases i <;> fin_cases k <;>
      simp [rep, red, Matrix.mul_apply, Fin.sum_univ_two, h01, h10, h11] <;> linear_combination hdet

theorem mem_Gamma_of_mul {M q : ℕ} (hqM : Nat.Coprime q M) (δ : SL(2, ℤ)) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (hm : red M m = !![1, 0; 0, (q : ZMod M)]) (h : red M ((δ : Matrix (Fin 2) (Fin 2) ℤ) * m) = !![1, 0; 0, (q : ZMod M)]) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem']
  have hu : IsUnit (!![1, 0; 0, (q : ZMod M)] : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
    simpa using (ZMod.unitOfCoprime q hqM).isUnit
  have h2 : red M (δ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (q : ZMod M)] = !![1, 0; 0, (q : ZMod M)] := by
    rw [← hm]; exact (RingHom.map_mul _ _ _).symm.trans (h.trans hm.symm)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  exact hu.mul_right_cancel (h2.trans (one_mul _).symm)

theorem map_rep {M q : ℕ} (hq : q.Prime) (hqM : Nat.Coprime q M) {γ : SL(2, ℤ)} (hγ : DiagMod M q γ)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma M) (o : Option (Fin q)) :
    ∃ o', ∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma M ∧
      rep M q γ o * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * rep M q γ o' := by
  set m := rep M q γ o * (δ : Matrix (Fin 2) (Fin 2) ℤ) with hmdef
  have hm : m.det = q := by
    rw [hmdef, Matrix.det_mul, det_rep, Matrix.SpecialLinearGroup.det_coe, mul_one]
  have hδ1 : red M (δ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [CongruenceSubgroup.Gamma_mem'] at hδ
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) (ZMod M) => (x : Matrix (Fin 2) (Fin 2) (ZMod M))) hδ
    simpa using this
  have hred : red M m = !![1, 0; 0, (q : ZMod M)] := by
    rw [hmdef, red_mul, hδ1, Matrix.mul_one, red_rep hγ]

  have fin : ∀ o' (g : Matrix (Fin 2) (Fin 2) ℤ), g * rep M q γ o' = m →
      ∃ g' : SL(2, ℤ), g' ∈ CongruenceSubgroup.Gamma M ∧ m = (g' : Matrix (Fin 2) (Fin 2) ℤ) * rep M q γ o' := by
    intro o' g he
    have hd : g.det = 1 := by
      have := congrArg Matrix.det he
      rw [Matrix.det_mul, det_rep, hm] at this
      have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
      exact mul_right_cancel₀ hq' (this.trans (one_mul _).symm)
    refine ⟨⟨g, hd⟩, ?_, he.symm⟩
    exact mem_Gamma_of_mul hqM _ (rep M q γ o') (red_rep hγ o') (by rw [show ((⟨g, hd⟩ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = g from rfl, he, hred])
  rcases GlobalTheory.cosetPrimeDet q hq m hm with ⟨g, hg⟩ | ⟨k, hk, g, hg⟩
  · have hs : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    obtain ⟨g', hg', he⟩ := fin none (g * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) (by
      rw [← hg]; show _ * ((γ : Matrix (Fin 2) (Fin 2) ℤ) * _) = _
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (γ : Matrix (Fin 2) (Fin 2) ℤ), hs, Matrix.one_mul])
    exact ⟨none, g', hg', he⟩
  ·
    have hMq : IsCoprime (M : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hqM.symm
    obtain ⟨u, v, huv⟩ := hMq
    haveI := Fact.mk hq
    set j : ℕ := ((k : ZMod q) * (u : ZMod q)).val with hj
    have hjq : j < q := ZMod.val_lt _
    have hdiv : (q : ℤ) ∣ (j : ℤ) * M - k := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hj, ZMod.natCast_zmod_val]
      have := congrArg (fun z : ℤ => (z : ZMod q)) huv
      push_cast at this
      rw [ZMod.natCast_self, mul_zero, add_zero] at this
      linear_combination (k : ZMod q) * this
    obtain ⟨t, ht⟩ := hdiv
    obtain ⟨g', hg', he⟩ := fin (some ⟨j, hjq⟩) (g * !![1, -t; 0, 1]) (by
      rw [← hg, Matrix.mul_assoc]; congr 1
      ext a b; fin_cases a <;> fin_cases b <;> simp [rep] <;> linear_combination ht)
    exact ⟨some ⟨j, hjq⟩, g', hg', he⟩

theorem rep_distinct {M q : ℕ} (hq : q.Prime) (hqM : Nat.Coprime q M) (γ : SL(2, ℤ)) (o o' : Option (Fin q))
    (h : SL(2, ℤ)) (H : (h : Matrix (Fin 2) (Fin 2) ℤ) * rep M q γ o = rep M q γ o') : o = o' := by
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.2; rw [Matrix.det_fin_two] at this; exact this
  have nd : ¬ (q : ℤ) ∣ 1 := by
    intro hd
    have : q ∣ 1 := by exact_mod_cast hd
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some k =>
      exfalso
      have e00 := congrFun (congrFun H 0) 0
      simp [rep, Matrix.mul_apply, Fin.sum_univ_two] at e00
      exact nd ⟨h 0 0 * γ 0 0 + h 0 1 * γ 1 0, by linear_combination -e00⟩
  | some j =>
    cases o' with
    | none =>
      exfalso
      have e00 := congrFun (congrFun H 0) 0
      have e10 := congrFun (congrFun H 1) 0
      simp [rep, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
      exact nd ⟨γ 0 0 * h 1 1 - h 0 1 * γ 1 0, by rw [e00, e10] at hdet; linear_combination -hdet⟩
    | some k =>
      have e00 := congrFun (congrFun H 0) 0
      have e01 := congrFun (congrFun H 0) 1
      simp [rep, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
      rw [e00] at e01
      have hdv : (q : ℤ) ∣ ((k : ℕ) - (j : ℕ) : ℤ) * M := ⟨h 0 1, by linear_combination -e01⟩
      have hc : IsCoprime (q : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hqM
      have h2 := hc.dvd_of_dvd_mul_right hdv
      have hj := j.2
      have hk := k.2
      congr 1
      apply Fin.ext
      obtain ⟨c, hc⟩ := h2
      have hj' : ((j : ℕ) : ℤ) < q := by exact_mod_cast hj
      have hk' : ((k : ℕ) : ℤ) < q := by exact_mod_cast hk
      have hj0 : (0 : ℤ) ≤ (j : ℕ) := by positivity
      have hk0 : (0 : ℤ) ≤ (k : ℕ) := by positivity
      have hc0 : c = 0 := by
        rcases lt_trichotomy c 0 with hlt | heq | hgt
        · nlinarith
        · exact heq
        · nlinarith
      rw [hc0, mul_zero] at hc
      exact_mod_cast (by linarith : ((j : ℕ) : ℤ) = (k : ℕ))

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem prod_sl_inv (X : Tower Ω ε) (M : ℕ) {ι : Type} [Fintype ι]
    (r : ι → Matrix (Fin 2) (Fin 2) ℤ) (hr : ∀ i, 0 < (r i).det) (δ : SL(2, ℤ))
    (hmap : ∀ i, ∃ i', ∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma M ∧
      r i * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * r i')
    (hdis : ∀ i i' (h : SL(2, ℤ)), (h : Matrix (Fin 2) (Fin 2) ℤ) * r i = r i' → i = i')
    (f : X.K) (hf : Lev X M f) :
    X.sl (ofSL δ) (∏ i, X.sl (toGQ (r i)) f) = ∏ i, X.sl (toGQ (r i)) f := by
  choose s g hg he using hmap
  have hdet1 : ∀ h : SL(2, ℤ), 0 < (h : Matrix (Fin 2) (Fin 2) ℤ).det := fun h => by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos
  have hinj : Function.Injective s := by
    intro i1 i2 h12
    have hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hg2 : (((g i2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (g i2 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    symm
    apply hdis i2 i1 (g i1 * (g i2)⁻¹)
    have e1 := he i1
    have e2 := he i2
    rw [h12] at e1
    have a1 : r i1 = (g i1 : Matrix (Fin 2) (Fin 2) ℤ) * r (s i2) * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← e1, Matrix.mul_assoc, hδ, Matrix.mul_one]
    have a2 : r i2 = (g i2 : Matrix (Fin 2) (Fin 2) ℤ) * r (s i2) * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← e2, Matrix.mul_assoc, hδ, Matrix.mul_one]
    rw [Matrix.SpecialLinearGroup.coe_mul, a1]
    conv_lhs => rw [a2]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ (g i2 : Matrix (Fin 2) (Fin 2) ℤ), hg2, Matrix.one_mul]
  have hbij : Function.Bijective s := Finite.injective_iff_bijective.mp hinj
  rw [map_prod]
  have step : ∀ i, X.sl (ofSL δ) (X.sl (toGQ (r i)) f) = X.sl (toGQ (r (s i))) f := by
    intro i
    rw [← X.sl_mul, ← MobLaws.toGQ_SL, ← MobLaws.toGQ_mul _ _ (hr i) (hdet1 δ), he i,
      MobLaws.toGQ_mul _ _ (hdet1 (g i)) (hr (s i)), X.sl_mul, MobLaws.toGQ_SL, hf _ (hg i)]
  simp only [step]
  exact Equiv.prod_comp (Equiv.ofBijective s hbij) (fun i => X.sl (toGQ (r i)) f)

end GlobalTheory.KZ.ES.HeckeLev

namespace GlobalTheory.KZ.ES

theorem lev_heckeProd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M q : ℕ) (f : X.K) (γ : SL(2, ℤ)), 0 < M → q.Prime → Nat.Coprime q M → Lev X M f → DiagMod M q γ →
    Lev X M (Nq X M q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := by
  intro Ω _ _ _ ε X M q f γ _ hq hqM hf hγ δ hδ
  have e : Nq X M q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f =
      ∏ o : Option (Fin q), X.sl (toGQ (HeckeLev.rep M q γ o)) f := by
    rw [Fintype.prod_option, mul_comm, Nq, Finset.prod_range]
    rfl
  rw [e]
  exact HeckeLev.prod_sl_inv X M (HeckeLev.rep M q γ)
    (fun o => by rw [HeckeLev.det_rep]; exact_mod_cast hq.pos) δ
    (HeckeLev.map_rep hq hqM hγ δ hδ) (HeckeLev.rep_distinct hq hqM γ) f hf

end GlobalTheory.KZ.ES
