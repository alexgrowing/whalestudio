import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB

open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace GlobalTheory.MomDual

variable {g : ℕ}

theorem hf_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hf Hm (z + z') w = hf Hm z w + hf Hm z' w := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hf_sub_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hf Hm (z - z') w = hf Hm z w - hf Hm z' w := by
  simp only [hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem hf_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hf Hm (c • z) w = c * hf Hm z w := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hf_zero_left (Hm : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) : hf Hm 0 w = 0 := by
  simp [hf]

theorem hf_sum_left (Hm : Matrix (Fin g) (Fin g) ℂ) {ι : Type*} (t : Finset ι) (c : ι → ℂ) (v : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : hf Hm (∑ k ∈ t, c k • v k) w = ∑ k ∈ t, c k * hf Hm (v k) w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [hf_zero_left]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, hf_smul_left, ih]

theorem hf_smul_right (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hf Hm z (c • w) = conj c * hf Hm z w := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_conj {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hf Hm w z = conj (hf Hm z w) := by
  simp only [hf, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : Hm j i = conj (Hm i j) := by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this.symm
  rw [h]; ring

theorem hf_self_ne {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.PosDef) {z : Fin g → ℂ} (hz : z ≠ 0) : hf Hm z z ≠ 0 := by
  have hx : star z ≠ 0 := by simpa using hz
  have h := hH.dotProduct_mulVec_pos hx
  have e : dotProduct (star (star z)) (Hm.mulVec (star z)) = hf Hm z z := by
    simp [hf, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [e] at h
  exact h.ne'

theorem dual_basis : ∀ (q : ℕ) [Fact q.Prime] (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ), S.Ok → S.NNBasis q b →
    ∃ (s : ℕ) (c : Fin r → Fin g → ℂ), Nat.Coprime s q ∧ (∀ j, c j ∈ S.La) ∧
      (∀ i j, beta S.d S.Hm (c j) (b i) = if i = j then (s : ℂ) else 0) ∧
      ∀ x ∈ S.La, (s : ℂ) • x = ∑ j, beta S.d S.Hm x (b j) • c j := by
  intro q _ g S r b hS hb
  obtain ⟨hdp, -, hpos, hdisc, hspan, hw0, -, hdual⟩ := hS
  obtain ⟨hbL, hgen, hind⟩ := hb
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = Real.sqrt S.d / 2 := ⟨_, rfl⟩
  have hρ0 : ρ ≠ 0 := by
    have : (0:ℝ) < S.d := by exact_mod_cast hdp.pos
    rw [hρ]; positivity
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0
  have hbeta : ∀ z w, beta S.d S.Hm z w = (ρ : ℂ) * hf S.Hm z w := fun z w => by rw [hρ]; rfl
  have hw0im : (w0 S.d).im = ρ := by simp [w0, rtd, hρ]
  have hOKim : ∀ c ∈ OK S.d, ∃ v : ℤ, c.im = v * ρ := by
    rintro c ⟨u, v, rfl⟩; exact ⟨v, by simp [hw0im]⟩
  have hqs : ∀ s : ℕ, Nat.Coprime s q → s ≠ 0 := by
    rintro s hs rfl
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.mp hs)

  have hmemspan : ∀ x ∈ S.La, ∃ μ : Fin r → ℂ, x = ∑ i, μ i • b i := by
    intro x hx
    obtain ⟨s, hs, c, -, he⟩ := hgen x hx
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hqs s hs
    refine ⟨fun i => (s : ℂ)⁻¹ * c i, ?_⟩
    simp_rw [← smul_smul]
    rw [← Finset.smul_sum, ← he, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have htop : (⊤ : Submodule ℂ (Fin g → ℂ)) ≤ Submodule.span ℂ (Set.range b) := by
    have h1 : Submodule.span ℝ (S.La : Set (Fin g → ℂ)) ≤ (Submodule.span ℂ (Set.range b)).restrictScalars ℝ := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨μ, rfl⟩ := hmemspan x hx
      show _ ∈ Submodule.span ℂ (Set.range b)
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    intro x _
    have : x ∈ Submodule.span ℝ (S.La : Set (Fin g → ℂ)) := by rw [hspan]; trivial
    exact h1 this
  haveI : DiscreteTopology S.La := hdisc
  haveI : IsZLattice ℝ S.La := ⟨hspan⟩
  have hrk : Module.finrank ℤ S.La = 2 * g := by
    rw [ZLattice.rank ℝ S.La]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    ring
  have hli2 : LinearIndependent ℤ (fun p : Fin r ⊕ Fin r => (⟨Sum.elim (fun i => b i) (fun i => w0 S.d • b i) p,
      by rcases p with i | i; exacts [hbL i, hw0 _ (hbL i)]⟩ : S.La)) := by
    rw [Fintype.linearIndependent_iff]
    intro n hn
    have hn' := congrArg Subtype.val hn
    simp only [Fintype.sum_sum_type, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Sum.elim_inl,
      Sum.elim_inr, Submodule.coe_zero] at hn'
    have key : ∑ i, ((n (Sum.inl i) : ℂ) + (n (Sum.inr i) : ℂ) * w0 S.d) • b i = 0 := by
      rw [← hn']
      simp only [add_smul, mul_smul, Finset.sum_add_distrib, Int.cast_smul_eq_zsmul]
    have hc := hind _ (fun i => ⟨n (Sum.inl i), n (Sum.inr i), rfl⟩) key
    have hm : ∀ i, n (Sum.inr i) = 0 := fun i => by
      have := congrArg Complex.im (hc i); simpa [hw0im, hρ0] using this
    have hl : ∀ i, n (Sum.inl i) = 0 := fun i => by
      have := hc i; simp only [hm i, Int.cast_zero, zero_mul, add_zero] at this; exact_mod_cast this
    rintro (i | i); exacts [hl i, hm i]
  have hrg : r ≤ g := by
    have := hli2.fintype_card_le_finrank
    simp only [Fintype.card_sum, Fintype.card_fin, hrk] at this
    omega
  have hlin : LinearIndependent ℂ b :=
    linearIndependent_of_top_le_span_of_card_le_finrank htop (by simpa using hrg)

  have hconj := hf_conj hpos.isHermitian
  have L0 : ∀ μ : Fin r → ℂ, (∀ i, hf S.Hm (∑ k, μ k • b k) (b i) = 0) → ∑ k, μ k • b k = 0 := by
    intro μ h
    by_contra hne
    apply hf_self_ne hpos hne
    rw [hf_sum_left]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hconj, h k, map_zero, mul_zero]
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin r) (Fin r) ℂ, A = fun i j => hf S.Hm (b i) (b j) := ⟨_, rfl⟩
  have hvm : ∀ w : Fin r → ℂ, ∀ i, Matrix.vecMul w A i = hf S.Hm (∑ k, w k • b k) (b i) := by
    intro w i
    rw [hf_sum_left, hAdef]; rfl
  have hA : IsUnit A := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    intro u v huv
    have h0 : ∑ k, (u - v) k • b k = 0 := by
      apply L0
      intro i
      have huv' : Matrix.vecMul u A = Matrix.vecMul v A := huv
      rw [← hvm, Matrix.sub_vecMul, huv', sub_self]; rfl
    have := Fintype.linearIndependent_iff.mp hlin (u - v) h0
    funext i; exact sub_eq_zero.mp (this i)
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  obtain ⟨bs, hbsdef⟩ : ∃ bs : Fin r → Fin g → ℂ, bs = fun j => ∑ k, ((ρ : ℂ)⁻¹ * A⁻¹ j k) • b k := ⟨_, rfl⟩
  have hbs : ∀ j i, (ρ : ℂ) * hf S.Hm (bs j) (b i) = if j = i then 1 else 0 := by
    intro j i
    rw [hbsdef]
    simp only [hf_sum_left]
    have := congrFun (congrFun hinv j) i
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hρc, one_mul, hAdef]
  have hbs2 : ∀ j i, hf S.Hm (bs j) (b i) = (ρ : ℂ)⁻¹ * (if j = i then 1 else 0) := by
    intro j i; rw [← hbs j i, ← mul_assoc, inv_mul_cancel₀ hρc, one_mul]
  have hbs' : ∀ j i, (ρ : ℂ) * hf S.Hm (b i) (bs j) = if j = i then 1 else 0 := by
    intro j i
    rw [hconj, ← Complex.conj_ofReal ρ, ← map_mul, hbs]
    split_ifs <;> simp
  have hOKint : ∀ (c : Fin r → ℂ), (∀ i, c i ∈ OK S.d) → ∀ j, ∃ z : ℤ, (hf S.Hm (∑ i, c i • b i) (bs j)).im = z := by
    intro c hc j
    have e : (ρ : ℂ) * hf S.Hm (∑ i, c i • b i) (bs j) = c j := by
      rw [hf_sum_left, Finset.mul_sum]
      simp_rw [mul_left_comm (ρ : ℂ), hbs']
      simp
    obtain ⟨v, hv⟩ := hOKim _ (hc j)
    refine ⟨v, ?_⟩
    have h2 : hf S.Hm (∑ i, c i • b i) (bs j) = c j / (ρ : ℂ) := by
      rw [← e]; field_simp
    rw [h2, Complex.div_ofReal_im, hv]; field_simp

  have okAdd : ∀ a a', a ∈ OK S.d → a' ∈ OK S.d → a + a' ∈ OK S.d := by
    rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩; exact ⟨u + u', v + v', by push_cast; ring⟩
  have okMul : ∀ (n : ℤ) a, a ∈ OK S.d → (n : ℂ) * a ∈ OK S.d := by
    rintro n _ ⟨u, v, rfl⟩; exact ⟨n * u, n * v, by push_cast; ring⟩
  have ok0 : (0 : ℂ) ∈ OK S.d := ⟨0, 0, by simp⟩
  let P : (Fin g → ℂ) → Prop := fun y => ∃ c : Fin r → ℂ, (∀ i, c i ∈ OK S.d) ∧ y = ∑ i, c i • b i
  have Padd : ∀ y y', P y → P y' → P (y + y') := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact ⟨c + c', fun i => okAdd _ _ (hc i) (hc' i), by simp [add_smul, Finset.sum_add_distrib]⟩
  have P0 : P 0 := ⟨0, fun _ => ok0, by simp⟩
  have Pz : ∀ (n : ℤ) y, P y → P ((n : ℂ) • y) := by
    rintro n _ ⟨c, hc, rfl⟩
    exact ⟨fun i => (n : ℂ) * c i, fun i => okMul n _ (hc i), by rw [Finset.smul_sum]; simp [smul_smul]⟩

  haveI : Module.Finite ℤ S.La := ZLattice.module_finite ℝ S.La
  haveI : Module.Free ℤ S.La := ZLattice.module_free ℝ S.La
  obtain ⟨ι, _, ⟨eB⟩⟩ : ∃ (ι : Type) (_ : Fintype ι), Nonempty (Module.Basis ι ℤ S.La) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ S.La⟩⟩
  classical
  choose sI hsI cI hcI heqI using fun k : ι => hgen _ (eB k).2
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = ∏ k, sI k := ⟨_, rfl⟩
  have hsq : Nat.Coprime s q := hs ▸ Nat.Coprime.prod_left fun k _ => hsI k
  have hsk : ∀ k, (s : ℂ) • ((eB k : S.La) : Fin g → ℂ) =
      (((∏ l ∈ Finset.univ.erase k, sI l : ℕ) : ℤ) : ℂ) • ∑ i, cI k i • b i := by
    intro k
    rw [← heqI k, smul_smul, hs, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
    congr 1; push_cast; ring
  have hP : ∀ x ∈ S.La, P ((s : ℂ) • x) := by
    intro x hx
    have hx' : x = ∑ k, ((eB.repr ⟨x, hx⟩ k : ℤ) : ℂ) • ((eB k : S.La) : Fin g → ℂ) := by
      have h := congrArg Subtype.val (eB.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      calc x = ∑ k, eB.repr ⟨x, hx⟩ k • ((eB k : S.La) : Fin g → ℂ) := h.symm
        _ = _ := Finset.sum_congr rfl fun k _ => (Int.cast_smul_eq_zsmul ℂ _ _).symm
    rw [hx', Finset.smul_sum]
    apply Finset.sum_induction _ P Padd P0
    intro k _
    rw [smul_comm, hsk k]
    exact Pz _ _ (Pz _ _ ⟨cI k, hcI k, rfl⟩)
  refine ⟨s, fun j => (s : ℂ) • bs j, hsq, ?_, ?_, ?_⟩
  · intro j
    apply hdual
    intro x hx
    obtain ⟨c, hc, hce⟩ := hP x hx
    obtain ⟨z, hz⟩ := hOKint c hc j
    refine ⟨z, ?_⟩
    rw [hf_smul_right, map_natCast, ← hf_smul_left, hce, hz]
  · intro i j
    rw [hbeta, hf_smul_left, mul_left_comm, hbs j i]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h, h.symm]
  · intro x hx
    obtain ⟨β, hβ⟩ : ∃ β : Fin r → ℂ, ∀ j, beta S.d S.Hm x (b j) = β j := ⟨_, fun _ => rfl⟩
    simp_rw [hβ]
    have hβ' : ∀ i, hf S.Hm x (b i) = (ρ : ℂ)⁻¹ * β i := fun i => by
      rw [← hβ i, hbeta, ← mul_assoc, inv_mul_cancel₀ hρc, one_mul]
    have key : x = ∑ j, β j • bs j := by
      obtain ⟨μ, hμ⟩ := hmemspan x hx
      rw [← sub_eq_zero]
      have hy : x - ∑ j, β j • bs j = ∑ k, (μ k - ∑ j, β j * ((ρ : ℂ)⁻¹ * A⁻¹ j k)) • b k := by
        rw [hbsdef]
        simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm, ← hμ]
      rw [hy]
      apply L0
      intro i
      rw [← hy, hf_sub_left, hf_sum_left, hβ' i]
      simp only [hbs2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    conv_lhs => rw [key]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

end GlobalTheory.MomDual
