import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Unfold

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace ENNReal

namespace WlocSk

def WRightInv : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    IsFiniteMeasure μW → ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z,
      μW.map (fun x : Formalism.QuantumDeterminants.Mt k r => fun i j => (Matrix.of x * h) i j) = μW

def NUnimod : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    (∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μN K < ⊤) →
    ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m₀ ∈ Formalism.QuantumDeterminants.Nset k r,
      μN.map (fun x : Formalism.QuantumDeterminants.Mt k r => fun i j => (h⁻¹ * Matrix.of x * h * m₀) i j) = μN

namespace AE

variable {k r : ℕ}

lemma cancel {a b : Mat k r} (hab : a * b = 1) (X : Mat k r) : a * (b * X) = X := by
  rw [← Matrix.mul_assoc, hab, Matrix.one_mul]

def affE (a a' b b' : Mat k r) (h1 : a' * a = 1) (h2 : a * a' = 1) (h3 : b * b' = 1) (h4 : b' * b = 1) :
    Formalism.QuantumDeterminants.Mt k r ≃ᵐ Formalism.QuantumDeterminants.Mt k r where
  toFun x := fun i j => (a * Matrix.of x * b) i j
  invFun y := fun i j => (a' * Matrix.of y * b') i j
  left_inv x := by
    funext i j
    show (a' * (a * Matrix.of x * b) * b') i j = x i j
    rw [show a' * (a * Matrix.of x * b) * b' = Matrix.of x by
      simp only [Matrix.mul_assoc]; rw [cancel h1, h3, Matrix.mul_one]]
    rfl
  right_inv y := by
    funext i j
    show (a * (a' * Matrix.of y * b') * b) i j = y i j
    rw [show a * (a' * Matrix.of y * b') * b = Matrix.of y by
      simp only [Matrix.mul_assoc]; rw [cancel h2, h4, Matrix.mul_one]]
    rfl
  measurable_toFun := by
    have : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (fun i j => (a * Matrix.of x * b) i j : Formalism.QuantumDeterminants.Mt k r)) :=
      (continuous_const.matrix_mul Grp.continuous_of).matrix_mul continuous_const
    exact this.measurable
  measurable_invFun := by
    have : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (fun i j => (a' * Matrix.of x * b') i j : Formalism.QuantumDeterminants.Mt k r)) :=
      (continuous_const.matrix_mul Grp.continuous_of).matrix_mul continuous_const
    exact this.measurable

theorem ae_fst {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μN] {U : Set (Mat k r)}
    (hU : μW {x | Matrix.of x ∉ U} = 0) : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ U := by
  rw [ae_iff]
  have e : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r | ¬ Matrix.of p.1 ∈ U} = {x | Matrix.of x ∉ U} ×ˢ Set.univ := by
    ext p
    simp
  rw [e, Measure.prod_prod, hU, zero_mul]

theorem ae_snd {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μN] {U : Set (Mat k r)}
    (hU : μN {x | Matrix.of x ∉ U} = 0) : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ U := by
  rw [ae_iff]
  have e : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r | ¬ Matrix.of p.2 ∈ U} = Set.univ ×ˢ {x | Matrix.of x ∉ U} := by
    ext p
    simp
  rw [e, Measure.prod_prod, hU, mul_zero]

lemma star_of_inv {a b : ℂ} (ha : ‖a‖ = 1) (hab : a * b = 1) : star b = a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hb : b = a⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
  have hconj : star a = a⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, ha]
    simp [Complex.star_def]
  rw [hb, star_inv₀, hconj, inv_inv]

end AE

theorem aEquiv_of (hSG : SGrp) (hPU : PiUnit) (hSig : SigmaG) (hWR : WRightInv) (hNU : NUnimod)
    (hAI : AInt) : AEquiv := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ h hh m hm g hg
  have hAIg := hAI k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ g hg
  obtain ⟨hset, hDS, hHC, -, -, -, -, hW, hN, hWfin, hNK⟩ := hyp
  obtain ⟨-, -, hz, hT, -⟩ := hset
  obtain ⟨hWG, hNG, hWg, hNg, hconj⟩ := hSG k r z c hz hT
  have hσ := hSig k r _ _ H σ hDS
  obtain ⟨⟨-, hπmul⟩, -⟩ := hPU k r z u Vp π hz hT hHC
  have hhG := hWG hh
  have hmG := hNG hm
  have hgG : g ∈ Gr k r := hg
  have hhi : h⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z := (hWg h hh h hh).2.1
  have hih : h⁻¹ * h = 1 := Grp.inv_mul hhG
  have hhi' : h * h⁻¹ = 1 := Grp.mul_inv hhG
  have hinv2 : (h⁻¹)⁻¹ = h :=
    Matrix.nonsing_inv_nonsing_inv h (Matrix.isUnit_det_of_right_inverse hhi')
  have hmi : m⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r := (hNg m hm m hm).2.1
  have hmim : m⁻¹ * m = 1 := Grp.inv_mul hmG
  obtain ⟨hm₀, -⟩ := hconj h⁻¹ hhi m⁻¹ hmi
  rw [hinv2] at hm₀
  obtain ⟨m₀, hm₀def⟩ : ∃ m₀ : Mat k r, m₀ = h * m⁻¹ * h⁻¹ := ⟨_, rfl⟩
  rw [← hm₀def] at hm₀
  have hm₀G := hNG hm₀

  have hW1 := hWR k r z μW hz hT hW hWfin h⁻¹ hhi
  have hN1 := hNU k r z μN hz hT hN hNK h⁻¹ hhi m₀ hm₀
  rw [hinv2] at hN1
  have h3 : h⁻¹ * m₀ * (m₀⁻¹ * h) = 1 := by
    rw [Matrix.mul_assoc, AE.cancel (Grp.mul_inv hm₀G), hih]
  have h4 : m₀⁻¹ * h * (h⁻¹ * m₀) = 1 := by
    rw [Matrix.mul_assoc, AE.cancel hhi', Grp.inv_mul hm₀G]
  let e₁ := AE.affE (k := k) (r := r) 1 1 h⁻¹ h (Matrix.one_mul 1) (Matrix.one_mul 1) hih hhi'
  let e₂ := AE.affE (k := k) (r := r) h h⁻¹ (h⁻¹ * m₀) (m₀⁻¹ * h) hih hhi' h3 h4
  have he₁ : μW.map e₁ = μW := by
    have : (e₁ : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) = fun x => fun i j => (Matrix.of x * h⁻¹) i j := by
      funext x i j
      show ((1 : Mat k r) * Matrix.of x * h⁻¹) i j = _
      rw [Matrix.one_mul]
    rw [this, hW1]
  have he₂ : μN.map e₂ = μN := by
    have : (e₂ : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) =
        fun x => fun i j => (h * Matrix.of x * h⁻¹ * m₀) i j := by
      funext x i j
      show (h * Matrix.of x * (h⁻¹ * m₀)) i j = _
      rw [← Matrix.mul_assoc (h * Matrix.of x)]
    rw [this, hN1]
  have hP : (μW.prod μN).map (e₁.prodCongr e₂) = μW.prod μN := by
    have := hW.1
    have := hN.1
    show (μW.prod μN).map (Prod.map e₁ e₂) = _
    rw [← Measure.map_prod_map μW μN e₁.measurable e₂.measurable, he₁, he₂]
  have := hN.1
  have hWc := AE.ae_fst (μN := μN) hW.2.2.1
  have hNc := AE.ae_snd (μW := μW) hN.2.2.1
  show ∫ p, bInt z c σ π (σ x₀ w) ξ (σ (h * m * g) w) p ∂(μW.prod μN) =
    psiGen k r z c m • π h (∫ p, bInt z c σ π (σ x₀ w) ξ (σ g w) p ∂(μW.prod μN))
  conv_lhs => rw [← hP]
  rw [integral_map_equiv, ← ContinuousLinearMap.integral_comp_comm _ hAIg, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [hWc, hNc] with p h1 h2

  have h1G := hWG h1
  have h2G := hNG h2
  have hXG : (1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)) ∈ Gr k r :=
    Grp.mul_mem (Grp.mul_mem (Grp.mul_mem Grp.one_mem h1G) (Grp.inv_mem hhG))
      (Grp.mul_mem (Grp.mul_mem hhG h2G) (Grp.mul_mem (Grp.inv_mem hhG) hm₀G))
  have hmgG : h * m * g ∈ Gr k r := Grp.mul_mem (Grp.mul_mem hhG hmG) hgG
  have hσ1 : σ ((1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)))
      (σ (h * m * g) w) = σ (Matrix.of p.1 * Matrix.of p.2) (σ g w) := by
    have e1 : σ ((1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)))
        (σ (h * m * g) w) =
        σ ((1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)) * (h * m * g)) w := by
      rw [hσ.1.2 _ hXG _ hmgG]; rfl
    have e2 : σ (Matrix.of p.1 * Matrix.of p.2) (σ g w) = σ (Matrix.of p.1 * Matrix.of p.2 * g) w := by
      rw [hσ.1.2 _ (Grp.mul_mem h1G h2G) _ hgG]; rfl
    have hX : (1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)) * (h * m * g) =
        Matrix.of p.1 * Matrix.of p.2 * g := by
      rw [hm₀def]
      simp only [Matrix.one_mul, Matrix.mul_assoc]
      rw [AE.cancel hih, AE.cancel hih, AE.cancel hih, AE.cancel hmim]
    rw [e1, e2, hX]
  have hψ2 : psiGen k r z c (h * Matrix.of p.2 * (h⁻¹ * m₀)) =
      psiGen k r z c (Matrix.of p.2) * psiGen k r z c m⁻¹ := by
    have hq : h * Matrix.of p.2 * (h⁻¹ * m₀) = (h⁻¹)⁻¹ * (Matrix.of p.2 * m⁻¹) * h⁻¹ := by
      rw [hm₀def, hinv2]
      simp only [Matrix.mul_assoc]
      rw [AE.cancel hih]
    rw [hq, (hconj h⁻¹ hhi _ (hNg _ h2 _ hmi).1).2, (hNg _ h2 _ hmi).2.2.2.1]
  have hψm : star (psiGen k r z c m⁻¹) = psiGen k r z c m := by
    apply AE.star_of_inv (hNg m hm m hm).2.2.2.2
    have h11 : m * m⁻¹ = 1 := (hNg m hm m hm).2.2.1
    have h1N : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
      have := (hNg m hm m⁻¹ hmi).1; rwa [h11] at this
    have hψ1 : psiGen k r z c 1 = 1 := by
      have hmul := (hNg 1 h1N 1 h1N).2.2.2.1
      rw [Matrix.mul_one] at hmul
      have hn : psiGen k r z c 1 ≠ 0 := by
        intro h0; have := (hNg 1 h1N 1 h1N).2.2.2.2; rw [h0, norm_zero] at this; exact zero_ne_one this
      have : psiGen k r z c 1 * (psiGen k r z c 1 - 1) = 0 := by rw [mul_sub, mul_one, ← hmul, sub_self]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hn
      · exact sub_eq_zero.mp h
    rw [← (hNg m hm m⁻¹ hmi).2.2.2.1, h11, hψ1]
  have hπ2 : π (1 * Matrix.of p.1 * h⁻¹)⁻¹ = (π h).comp (π (Matrix.of p.1)⁻¹) := by
    rw [Matrix.one_mul, Matrix.mul_inv_rev, hinv2]
    exact hπmul h hh _ (hWg _ h1 _ h1).2.1
  show (⟪σ x₀ w, σ ((1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)))
      (σ (h * m * g) w)⟫_ℂ * star (psiGen k r z c (h * Matrix.of p.2 * (h⁻¹ * m₀)))) •
      π (1 * Matrix.of p.1 * h⁻¹)⁻¹ ξ =
    psiGen k r z c m • π h ((⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ g w)⟫_ℂ *
      star (psiGen k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹ ξ)
  rw [hσ1, hψ2, hπ2, ContinuousLinearMap.comp_apply, map_smul, smul_smul, star_mul', hψm]
  congr 1
  ring

end WlocSk
