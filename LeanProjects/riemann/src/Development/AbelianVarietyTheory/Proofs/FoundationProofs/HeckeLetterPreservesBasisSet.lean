import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixActionMemHomogeneousPolyFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixPrimeDetCosetRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixChosenDiamondMatrixGamma1Gamma0Statement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section
namespace GlobalTheory.KZ.StabHecke

theorem toGQ_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (hm : 0 < m.det) (hm' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have h : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos hm hm'
  unfold toGQ
  rw [dif_pos h, dif_pos hm, dif_pos hm']
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem kmap_kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ : X.K ≃+* X.K) (x : X.Khat l) :
    X.kmap l φ (X.kmap l ψ x) = X.kmap l (ψ.trans φ) x := by
  simp only [Tower.kmap, LinearMap.coe_restrictScalars]
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp]
  congr 3

theorem act_act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (m m' : Matrix (Fin 2) (Fin 2) ℤ) (hm : 0 < m.det)
    (hm' : 0 < m'.det) (b : X.Fn l) : X.act l m (X.act l m' b) = X.act l (m' * m) b := by
  funext u
  simp only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
  rw [kmap_kmap, toGQ_mul m' m hm' hm]
  have e1 : mZl l (m' * m) = mZl l m' * mZl l m := by
    ext i j; simp [mZl, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e1, ← Matrix.mulVec_mulVec]
  congr 2
  ext f
  simp [X.sl_mul]

theorem polAct (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : ∀ a ∈ X.A l, X.kmap l (X.sl (toGQ m)).toRingEquiv a ∈ X.A l) :
    ∀ b ∈ X.Pol l w, X.act l m b ∈ X.Pol l w := GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions X l w m hA

theorem coset (q : ℕ) (hq : q.Prime) (m : Matrix (Fin 2) (Fin 2) ℤ) (hm : m.det = q) :
    (∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![(q : ℤ), 0; 0, 1] = m) ∨
      ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := GlobalTheory.T.intMatrix_prime_det_coset_representatives q hq m hm

theorem sgD_spec (N l d : ℕ) (hl : l.Prime) (hN : 0 < N) (hNl : Nat.Coprime N l) (hd : Nat.Coprime d N) :
    IsDiam N l d (sgD N l d) := GlobalTheory.T.isDiamondMatrix_chosenDiamondMatrixGamma1Gamma0 N l d hl hN hNl hd

theorem zmod_eq_one_iff (N : ℕ) (x : ℤ) : (x : ZMod N) = 1 ↔ (N : ℤ) ∣ x - 1 := by
  rw [← sub_eq_zero, ← Int.cast_one (R := ZMod N), ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem isCoprime_of_dvd_sub_one {x n : ℤ} (h : n ∣ x - 1) : IsCoprime x n := by
  obtain ⟨t, ht⟩ := h
  exact ⟨1, -t, by linear_combination ht⟩

theorem isCoprime_of_det {a b c d n : ℤ} (h : a * d - b * c = 1) (hc : n ∣ c) : IsCoprime a n := by
  obtain ⟨t, ht⟩ := hc
  exact ⟨d, -b * t, by rw [ht] at h; linear_combination h⟩

theorem mem_Gam_of_mul (N l : ℕ) (g : SL(2, ℤ)) (α m : Matrix (Fin 2) (Fin 2) ℤ)
    (h : (g : Matrix (Fin 2) (Fin 2) ℤ) * α = m) (hα1 : (N : ℤ) ∣ α 1 0) (hα2 : (l : ℤ) ∣ α 1 0)
    (hα3 : IsCoprime (α 0 0) N) (hα4 : IsCoprime (α 0 0) l) (hm1 : (N : ℤ) ∣ m 0 0 - α 0 0)
    (hm2 : (N : ℤ) ∣ m 1 0) (hm3 : (l : ℤ) ∣ m 1 0) : g ∈ Gam N l := by
  have e00 : m 0 0 = g 0 0 * α 0 0 + g 0 1 * α 1 0 := by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : m 1 0 = g 1 0 * α 0 0 + g 1 1 * α 1 0 := by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2; rw [Matrix.det_fin_two] at this; exact this
  have h1 : (N : ℤ) ∣ g 0 0 - 1 := by
    have : (N : ℤ) ∣ (g 0 0 - 1) * α 0 0 := by
      have e : (g 0 0 - 1) * α 0 0 = (m 0 0 - α 0 0) - g 0 1 * α 1 0 := by rw [e00]; ring
      rw [e]; exact dvd_sub hm1 (dvd_mul_of_dvd_right hα1 _)
    exact hα3.symm.dvd_of_dvd_mul_right this
  have h2 : (N : ℤ) ∣ g 1 0 := by
    have : (N : ℤ) ∣ g 1 0 * α 0 0 := by
      have e : g 1 0 * α 0 0 = m 1 0 - g 1 1 * α 1 0 := by rw [e10]; ring
      rw [e]; exact dvd_sub hm2 (dvd_mul_of_dvd_right hα1 _)
    exact hα3.symm.dvd_of_dvd_mul_right this
  have h3 : (l : ℤ) ∣ g 1 0 := by
    have : (l : ℤ) ∣ g 1 0 * α 0 0 := by
      have e : g 1 0 * α 0 0 = m 1 0 - g 1 1 * α 1 0 := by rw [e10]; ring
      rw [e]; exact dvd_sub hm3 (dvd_mul_of_dvd_right hα2 _)
    exact hα4.symm.dvd_of_dvd_mul_right this
  have h4 : (N : ℤ) ∣ g 1 1 - 1 := by
    have e : g 1 1 - 1 = -(g 0 0 - 1) * g 1 1 + g 0 1 * g 1 0 := by linear_combination hdet
    rw [e]; exact dvd_add (dvd_mul_of_dvd_left (dvd_neg.mpr h1) _) (dvd_mul_of_dvd_right h2 _)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨(zmod_eq_one_iff N _).mpr h1, (zmod_eq_one_iff N _).mpr h4, ?_⟩
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
  · rw [CongruenceSubgroup.Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h3

def PP (N l : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  (N : ℤ) ∣ m 0 0 - 1 ∧ (N : ℤ) ∣ m 1 0 ∧ (l : ℤ) ∣ m 1 0 ∧ IsCoprime (m 0 0) (l : ℤ)

theorem congruenceCondition_mul {N l : ℕ} {m m' : Matrix (Fin 2) (Fin 2) ℤ} (h : PP N l m) (h' : PP N l m') : PP N l (m * m') := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  have e00 : (m * m') 0 0 = m 0 0 * m' 0 0 + m 0 1 * m' 1 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (m * m') 1 0 = m 1 0 * m' 0 0 + m 1 1 * m' 1 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00]
    have e : m 0 0 * m' 0 0 + m 0 1 * m' 1 0 - 1 = (m 0 0 - 1) * m' 0 0 + (m' 0 0 - 1) + m 0 1 * m' 1 0 := by ring
    rw [e]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left a1 _) b1) (dvd_mul_of_dvd_right b2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left a2 _) (dvd_mul_of_dvd_right b2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left a3 _) (dvd_mul_of_dvd_right b3 _)
  · rw [e00]
    obtain ⟨t, ht⟩ := b3
    rw [ht, show m 0 1 * ((l : ℤ) * t) = (l : ℤ) * (m 0 1 * t) by ring]
    exact (a4.mul_left b4).add_mul_left_left _

theorem congruenceCondition_of_mem {N l : ℕ} {γ : SL(2, ℤ)} (h : γ ∈ Gam N l) : PP N l (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp h
  rw [CongruenceSubgroup.Gamma1_mem] at h1
  rw [CongruenceSubgroup.Gamma0_mem] at h2
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hl : (l : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  exact ⟨(zmod_eq_one_iff N _).mp h1.1, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1.2.2, hl,
    isCoprime_of_det hdet hl⟩

theorem mem_Gam_of_PP (N l : ℕ) (g : SL(2, ℤ)) (α m : Matrix (Fin 2) (Fin 2) ℤ)
    (h : (g : Matrix (Fin 2) (Fin 2) ℤ) * α = m) (hα : PP N l α) (hm : PP N l m) : g ∈ Gam N l := by
  refine mem_Gam_of_mul N l g α m h hα.2.1 hα.2.2.1 (isCoprime_of_dvd_sub_one hα.1) hα.2.2.2 ?_ hm.2.1 hm.2.2.1
  have e : m 0 0 - α 0 0 = (m 0 0 - 1) - (α 0 0 - 1) := by ring
  rw [e]; exact dvd_sub hm.1 hα.1

theorem det_eq_one_of_mul {q : ℕ} (hq : 0 < q) (g α m : Matrix (Fin 2) (Fin 2) ℤ) (h : g * α = m)
    (hα : α.det = q) (hm : m.det = q) : g.det = 1 := by
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, hα, hm] at this
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have := mul_right_cancel₀ hq' (this.trans (one_mul _).symm)
  exact this

theorem sum_act_inv (X : Tower Ω ε) (l N : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι]
    (r : ι → Matrix (Fin 2) (Fin 2) ℤ) (hr : ∀ i, 0 < (r i).det) (γ : SL(2, ℤ))
    (hmap : ∀ i, ∃ i', ∃ g : SL(2, ℤ), g ∈ Gam N l ∧
      r i * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * r i')
    (hdis : ∀ i i' (h : SL(2, ℤ)), (h : Matrix (Fin 2) (Fin 2) ℤ) * r i = r i' → i = i')
    (b : X.Fn l) (hb : ∀ g ∈ Gam N l, X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) b = b) :
    X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (∑ i, X.act l (r i) b) = ∑ i, X.act l (r i) b := by
  choose f g hg he using hmap
  have hdet1 : ∀ h : SL(2, ℤ), 0 < (h : Matrix (Fin 2) (Fin 2) ℤ).det := fun h => by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos
  have hinj : Function.Injective f := by
    intro i1 i2 h12
    have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hg2 : (((g i2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (g i2 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    symm
    apply hdis i2 i1 (g i1 * (g i2)⁻¹)
    have e1 := he i1
    have e2 := he i2
    rw [h12] at e1
    calc ((g i1 * (g i2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * r i2
        = (g i1 : Matrix (Fin 2) (Fin 2) ℤ) * ((g i2)⁻¹ : SL(2, ℤ)) * (r i2 * γ * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
          rw [Matrix.mul_assoc (r i2), hγ, Matrix.mul_one, Matrix.SpecialLinearGroup.coe_mul]
      _ = (g i1 : Matrix (Fin 2) (Fin 2) ℤ) * ((((g i2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (g i2 : Matrix (Fin 2) (Fin 2) ℤ)) * r (f i2) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [e2]; simp only [Matrix.mul_assoc]
      _ = (g i1 : Matrix (Fin 2) (Fin 2) ℤ) * r (f i2) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [hg2, Matrix.mul_one]
      _ = r i1 * γ * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by rw [e1]
      _ = r i1 := by rw [Matrix.mul_assoc, hγ, Matrix.mul_one]
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
  rw [map_sum]
  have step : ∀ i, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (r i) b) = X.act l (r (f i)) b := by
    intro i
    rw [act_act X l _ _ (hdet1 γ) (hr i), he i, ← act_act X l _ _ (hr (f i)) (hdet1 (g i)), hb _ (hg i)]
  simp only [step]
  exact Equiv.sum_comp (Equiv.ofBijective f hbij) (fun i => X.act l (r i) b)

def repT (q : ℕ) (σ : SL(2, ℤ)) : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => (σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]
  | some j => !![1, ((j : ℕ) : ℤ); 0, (q : ℤ)]

theorem det_repT (q : ℕ) (σ : SL(2, ℤ)) (o : Option (Fin q)) : (repT q σ o).det = q := by
  cases o with
  | none => simp [repT, Matrix.det_mul, Matrix.det_fin_two]
  | some j => simp [repT, Matrix.det_fin_two]

theorem diam_facts {N l d : ℕ} {σ : SL(2, ℤ)} (h : IsDiam N l d σ) :
    (N : ℤ) ∣ σ 1 0 ∧ (l : ℤ) ∣ σ 1 0 ∧ (N : ℤ) ∣ σ 1 1 - d ∧ σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hN, hl⟩ := Subgroup.mem_inf.mp h1
  rw [CongruenceSubgroup.Gamma0_mem] at hN hl
  refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hN, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hl, ?_, ?_⟩
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
    simp only [en] at h2
    rw [h2]; simp
  · have := σ.2; rw [Matrix.det_fin_two] at this; exact this

theorem PP_A (N l q j : ℕ) : PP N l !![1, (j : ℤ); 0, (q : ℤ)] := by
  refine ⟨by simp, by simp, by simp, by simpa using isCoprime_one_left⟩

theorem congruenceCondition_heckeRepresentative {N l q : ℕ} {σ : SL(2, ℤ)} (hσ : IsDiam N l q σ) (hql : IsCoprime (q : ℤ) (l : ℤ))
    (o : Option (Fin q)) : PP N l (repT q σ o) := by
  cases o with
  | some j => exact PP_A N l q j
  | none =>
    obtain ⟨h1, h2, h3, h4⟩ := diam_facts hσ
    have e00 : repT q σ none 0 0 = σ 0 0 * q := by simp [repT, Matrix.mul_apply, Fin.sum_univ_two]
    have e10 : repT q σ none 1 0 = σ 1 0 * q := by simp [repT, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e00]
      have e : σ 0 0 * (q : ℤ) - 1 = -(σ 0 0) * (σ 1 1 - q) + σ 0 1 * σ 1 0 := by linear_combination h4
      rw [e]; exact dvd_add (dvd_mul_of_dvd_right h3 _) (dvd_mul_of_dvd_right h1 _)
    · rw [e10]; exact dvd_mul_of_dvd_left h1 _
    · rw [e10]; exact dvd_mul_of_dvd_left h2 _
    · rw [e00]; exact (isCoprime_of_det h4 h2).mul_left hql

theorem dis_A {q : ℕ} (j k : ℕ) (hj : j < q) (hk : k < q) (h : Matrix (Fin 2) (Fin 2) ℤ)
    (H : h * !![1, (j : ℤ); 0, (q : ℤ)] = !![1, (k : ℤ); 0, (q : ℤ)]) : j = k := by
  have e00 := congrFun (congrFun H 0) 0
  have e01 := congrFun (congrFun H 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  rw [e00] at e01
  have hj' : (j : ℤ) < q := by exact_mod_cast hj
  have hk' : (k : ℤ) < q := by exact_mod_cast hk
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have h0 : h 0 1 = 0 := by
    rcases lt_trichotomy (h 0 1) 0 with hlt | heq | hgt
    · nlinarith
    · exact heq
    · nlinarith
  rw [h0] at e01
  exact_mod_cast (by linarith : (j : ℤ) = k)

theorem not_dvd_one {q : ℕ} (hq : q.Prime) : ¬ (q : ℤ) ∣ 1 := by
  intro h
  have : q ∣ 1 := by exact_mod_cast h
  exact hq.one_lt.ne' (Nat.dvd_one.mp this)

theorem coset_representatives_hecke_disjoint {q : ℕ} (hq : q.Prime) (σ : SL(2, ℤ)) (o o' : Option (Fin q)) (h : SL(2, ℤ))
    (H : (h : Matrix (Fin 2) (Fin 2) ℤ) * repT q σ o = repT q σ o') : o = o' := by
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.2; rw [Matrix.det_fin_two] at this; exact this
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some k =>
      exfalso
      have e00 := congrFun (congrFun H 0) 0
      simp [repT, Matrix.mul_apply, Fin.sum_univ_two] at e00
      exact not_dvd_one hq ⟨h 0 0 * σ 0 0 + h 0 1 * σ 1 0, by linear_combination -e00⟩
  | some j =>
    cases o' with
    | none =>
      exfalso
      have e00 := congrFun (congrFun H 0) 0
      have e10 := congrFun (congrFun H 1) 0
      simp [repT, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
      exact not_dvd_one hq ⟨σ 0 0 * h 1 1 - h 0 1 * σ 1 0, by rw [e00, e10] at hdet; linear_combination -hdet⟩
    | some k =>
      congr 1
      exact Fin.ext (dis_A j k j.2 k.2 _ H)

theorem map_T {N l q : ℕ} (hq : q.Prime) {σ : SL(2, ℤ)} (hσ : IsDiam N l q σ) (hql : IsCoprime (q : ℤ) (l : ℤ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) (o : Option (Fin q)) :
    ∃ o', ∃ g : SL(2, ℤ), g ∈ Gam N l ∧
      repT q σ o * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * repT q σ o' := by
  have hm : (repT q σ o * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det = q := by
    rw [Matrix.det_mul, det_repT, Matrix.SpecialLinearGroup.det_coe, mul_one]
  have hPm : PP N l (repT q σ o * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := congruenceCondition_mul (congruenceCondition_heckeRepresentative hσ hql o) (congruenceCondition_of_mem hγ)
  rcases coset q hq _ hm with ⟨g, hg⟩ | ⟨k, hk, g, hg⟩
  · set g' := g * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hg'
    have hs : ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have he : g' * repT q σ none = repT q σ o * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [hg', ← hg]
      show g * _ * ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) = _
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (σ : Matrix (Fin 2) (Fin 2) ℤ), hs, Matrix.one_mul]
    have hd : g'.det = 1 := det_eq_one_of_mul hq.pos g' _ _ he (det_repT q σ none) hm
    refine ⟨none, ⟨g', hd⟩, ?_, he.symm⟩
    exact mem_Gam_of_PP N l ⟨g', hd⟩ _ _ he (congruenceCondition_heckeRepresentative hσ hql none) hPm
  · have he : g * repT q σ (some ⟨k, hk⟩) = repT q σ o * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
      simpa [repT] using hg
    have hd : g.det = 1 := det_eq_one_of_mul hq.pos g _ _ he (det_repT q σ _) hm
    refine ⟨some ⟨k, hk⟩, ⟨g, hd⟩, ?_, he.symm⟩
    exact mem_Gam_of_PP N l ⟨g, hd⟩ _ _ he (congruenceCondition_heckeRepresentative hσ hql _) hPm

def repU (l : ℕ) (j : Fin l) : Matrix (Fin 2) (Fin 2) ℤ := !![1, ((j : ℕ) : ℤ); 0, (l : ℤ)]

theorem map_U {N l : ℕ} (hl : l.Prime) (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) (j : Fin l) :
    ∃ j', ∃ g : SL(2, ℤ), g ∈ Gam N l ∧
      repU l j * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * repU l j' := by
  have hm : (repU l j * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det = l := by
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one]; simp [repU, Matrix.det_fin_two]
  have hPm : PP N l (repU l j * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := congruenceCondition_mul (PP_A N l l j) (congruenceCondition_of_mem hγ)
  rcases coset l hl _ hm with ⟨g, hg⟩ | ⟨k, hk, g, hg⟩
  · exfalso
    have hdvd : (l : ℤ) ∣ (repU l j * (γ : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 :=
      ⟨g 0 0, by rw [← hg]; simp [Matrix.mul_apply, Fin.sum_univ_two]; ring⟩
    have hc := hPm.2.2.2.of_isCoprime_of_dvd_left hdvd
    rw [isCoprime_self, Int.isUnit_iff] at hc
    rcases hc with hc | hc
    · exact hl.one_lt.ne' (by exact_mod_cast hc)
    · have : (0 : ℤ) ≤ l := by positivity
      omega
  · have he : g * repU l ⟨k, hk⟩ = repU l j * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by simpa [repU] using hg
    have hd : g.det = 1 := det_eq_one_of_mul hl.pos g _ _ he (by simp [repU, Matrix.det_fin_two]) hm
    refine ⟨⟨k, hk⟩, ⟨g, hd⟩, ?_, he.symm⟩
    exact mem_Gam_of_PP N l ⟨g, hd⟩ _ _ he (PP_A N l l k) hPm

theorem heckeT_eq (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (q : ℕ) (b : X.Fn l) :
    X.heckeT N l q b = ∑ o : Option (Fin q), X.act l (repT q (sgD N l q) o) b := by
  simp only [Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply, Fintype.sum_option, repT]
  rw [Finset.sum_range, add_comm]

theorem heckeU_eq (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (b : X.Fn l) :
    X.heckeU l b = ∑ j : Fin l, X.act l (repU l j) b := by
  simp only [Tower.heckeU, LinearMap.sum_apply, repU]
  rw [Finset.sum_range]

theorem Pol_zero (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] : (0 : X.Fn l) ∈ X.Pol l w :=
  ⟨0, fun _ => (X.A l).zero_mem, fun u => by simp⟩

theorem Pol_add (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] {b b' : X.Fn l} (hb : b ∈ X.Pol l w)
    (hb' : b' ∈ X.Pol l w) : b + b' ∈ X.Pol l w := by
  obtain ⟨c, hc, e⟩ := hb
  obtain ⟨c', hc', e'⟩ := hb'
  refine ⟨c + c', fun i => (X.A l).add_mem (hc i) (hc' i), fun u => ?_⟩
  simp [e, e', smul_add, Finset.sum_add_distrib]

theorem Pol_sum (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] {ι : Type} (s : Finset ι) (f : ι → X.Fn l)
    (h : ∀ i ∈ s, f i ∈ X.Pol l w) : ∑ i ∈ s, f i ∈ X.Pol l w :=
  Finset.sum_induction f (· ∈ X.Pol l w) (fun _ _ => Pol_add X l w) (Pol_zero X l w) h

variable {l : ℕ}

theorem op_BSet (X : Tower Ω ε) [Fact l.Prime]
    (hA : ∀ (g : GQ), ∀ a ∈ X.A l, X.kmap l (X.sl g).toRingEquiv a ∈ X.A l) (N w : ℕ)
    (hN : 0 < N) (hNl : Nat.Coprime N l) (T : Letter) (hT : admitted N l T) (b : X.Fn l) (hb : b ∈ X.BSet N l w) :
    X.op N l T b ∈ X.BSet N l w := by
  have hl : l.Prime := Fact.out
  cases T with
  | T q =>
    obtain ⟨hq, hqd⟩ := hT
    have hqN : Nat.Coprime q N := (Nat.Prime.coprime_iff_not_dvd hq).mpr (fun h => hqd (dvd_mul_of_dvd_left h l))
    have hql' : Nat.Coprime q l := (Nat.Prime.coprime_iff_not_dvd hq).mpr (fun h => hqd (Dvd.dvd.mul_left h N))
    have hql : IsCoprime (q : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.mpr hql'
    have hσ := sgD_spec N l q hl hN hNl hqN
    show X.heckeT N l q b ∈ X.BSet N l w
    refine ⟨?_, ?_⟩
    · rw [heckeT_eq]; exact Pol_sum X l w _ _ (fun o _ => polAct X l w _ (hA _) b hb.1)
    · intro γ hγ
      rw [heckeT_eq]
      exact sum_act_inv X l N (repT q (sgD N l q)) (fun o => by rw [det_repT]; exact_mod_cast hq.pos) γ
        (map_T hq hσ hql γ hγ) (coset_representatives_hecke_disjoint hq _) b hb.2
  | U =>
    show X.heckeU l b ∈ X.BSet N l w
    refine ⟨?_, ?_⟩
    · rw [heckeU_eq]; exact Pol_sum X l w _ _ (fun j _ => polAct X l w _ (hA _) b hb.1)
    · intro γ hγ
      rw [heckeU_eq]
      exact sum_act_inv X l N (repU l) (fun j => by simp [repU, Matrix.det_fin_two]; exact hl.pos) γ
        (map_U hl γ hγ) (fun j j' h H => Fin.ext (dis_A j j' j.2 j'.2 _ H)) b hb.2
  | D d =>
    have hσ := sgD_spec N l d hl hN hNl hT
    show X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.BSet N l w
    refine ⟨polAct X l w _ (hA _) b hb.1, ?_⟩
    intro γ hγ
    obtain ⟨h1, h2, h3, h4⟩ := diam_facts hσ
    have hPγ := congruenceCondition_of_mem hγ
    have hdet1 : ∀ h : SL(2, ℤ), 0 < (h : Matrix (Fin 2) (Fin 2) ℤ).det := fun h => by
      rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos
    set σ := sgD N l d with hσdef
    have hgσ : ((σ * γ * σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
        (σ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    have e00 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = σ 0 0 * γ 0 0 + σ 0 1 * γ 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have e10 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = σ 1 0 * γ 0 0 + σ 1 1 * γ 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hg : σ * γ * σ⁻¹ ∈ Gam N l := by
      refine mem_Gam_of_mul N l _ _ _ hgσ h1 h2 (isCoprime_of_det h4 h1) (isCoprime_of_det h4 h2) ?_ ?_ ?_
      · rw [e00, show σ 0 0 * γ 0 0 + σ 0 1 * γ 1 0 - σ 0 0 = σ 0 0 * (γ 0 0 - 1) + σ 0 1 * γ 1 0 by ring]
        exact dvd_add (dvd_mul_of_dvd_right hPγ.1 _) (dvd_mul_of_dvd_right hPγ.2.1 _)
      · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right hPγ.2.1 _)
      · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_right hPγ.2.2.1 _)
    calc X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b)
        = X.act l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ)) b := act_act X l _ _ (hdet1 γ) (hdet1 σ) b
      _ = X.act l (((σ * γ * σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ)) b := by rw [hgσ]
      _ = X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l ((σ * γ * σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b) :=
          (act_act X l _ _ (hdet1 σ) (hdet1 _) b).symm
      _ = X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b := by rw [hb.2 _ hg]

end GlobalTheory.KZ.StabHecke

namespace GlobalTheory.KZ

theorem B_stable_op : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ T : Letter, admitted N l T →
    ∀ b ∈ X.B N l w, X.op N l T b ∈ X.B N l w := by
  intro Ω _ _ _ ε X hinj hj N l w _ _ hN hNl _ T hT b hb
  have hA := (GlobalTheory.T.modular_function_tower_integrality ε X hinj hj l).1
  have hle : X.B N l w ≤ (X.B N l w).comap (X.op N l T) :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span
      (StabHecke.op_BSet X hA N w (by omega) hNl T hT x hx))
  exact hle hb

end GlobalTheory.KZ
