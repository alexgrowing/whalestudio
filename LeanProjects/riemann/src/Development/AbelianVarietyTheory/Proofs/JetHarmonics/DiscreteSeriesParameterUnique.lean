import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory
namespace DSInequiv

open PI.DSInfCharCap

lemma eq_of_capP {n : ℕ} (mu mu' : Fin n → ℝ) (h : StrictAnti mu) (h' : StrictAnti mu')
    (e : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (mu s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (mu' s : ℂ)) Y) :
    mu = mu' := by
  have key : ∀ (a b : Fin n → ℝ),
      (∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (b s : ℂ)) Y) →
      Set.range a ⊆ Set.range b := by
    rintro a b e _ ⟨s, rfl⟩
    have h0 : Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) (-(a s : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp)
    rw [e] at h0
    obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp h0
    refine ⟨t, ?_⟩
    have : (b t : ℂ) = (a s : ℂ) := by linear_combination ht
    exact_mod_cast this
  have hr : Set.range mu = Set.range mu' :=
    Set.Subset.antisymm (key _ _ e) (key _ _ fun Y => (e Y).symm)
  have h1 : StrictMono (fun s => -mu s) := fun a b hab => neg_lt_neg (h hab)
  have h2 : StrictMono (fun s => -mu' s) := fun a b hab => neg_lt_neg (h' hab)
  have hr' : Set.range (fun s => -mu s) = Set.range (fun s => -mu' s) := by
    have := congrArg (fun S => Neg.neg '' S) hr
    simp only [← Set.range_comp] at this
    exact this
  have := (h1.range_inj h2).mp hr'
  funext s
  exact neg_injective (congrFun this s)

section
variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def toReal (V : H ≃L[ℂ] H') : H ≃L[ℝ] H' :=
  { V.toLinearEquiv.restrictScalars ℝ with
    continuous_toFun := V.continuous
    continuous_invFun := V.symm.continuous }

lemma dsig_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Formalism.REAL.inG ε X) (v : H) :
    V (PI.PhMeasCore.dsig τ X v) = PI.PhMeasCore.dsig τ' X (V v) := by
  unfold PI.PhMeasCore.dsig
  have e : (fun t : ℝ => τ' (NormedSpace.exp ((t : ℂ) • X)) (V v)) =
      (toReal V) ∘ (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • X)) v) := by
    funext t
    exact (hV _ (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t) v).symm
  rw [e]
  unfold deriv
  rw [ContinuousLinearEquiv.comp_fderiv]
  rfl

lemma dsigC_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) : V (dsigC ε τ Y v) = dsigC ε τ' Y (V v) := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hH := Formalism.REAL.Jm_conjTranspose ε
  have hJ' := Formalism.REAL.f1alg_JJ_left ε
  unfold dsigC
  rw [map_add, map_smul, dsig_equiv V hV, dsig_equiv V hV]
  · rw [Formalism.REAL.f1alg_inG_iff]
    have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
      simp [Complex.conj_I]
    simp only [thetaJ, conjTranspose_smul, hs, conjTranspose_sub, conjTranspose_neg, conjTranspose_mul, hH,
      conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ, hJ', Matrix.mul_one]
    module
  · rw [Formalism.REAL.f1alg_inG_iff]
    have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
    simp only [thetaJ, conjTranspose_smul, hs, conjTranspose_add, conjTranspose_neg, conjTranspose_mul, hH,
      conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ, hJ', Matrix.mul_one]
    module

lemma dsigCW_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (w : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) : V (dsigCW ε τ w v) = dsigCW ε τ' w (V v) := by
  induction w with
  | nil => rfl
  | cons Y w ih => simp only [dsigCW]; rw [dsigC_equiv V hV, ih]

lemma actU_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : H) : V (actU ε τ p v) = actU ε τ' p (V v) := by
  unfold actU Finsupp.sum
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, dsigCW_equiv V hV]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma smooth_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ) :
    V v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, hE⟩ := hv g₀ hg₀
  refine ⟨U, fun g => V (F g), hU, hm, ?_, fun g hg hg' => ?_⟩
  · exact ((toReal V).contDiff).comp_contDiffOn hF
  · exact (hV g hg' v).symm.trans (congrArg V (hE g hg hg'))

lemma smooth_conj {A B P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hA : Pᴴ * A * P = B) {v : H}
    (hv : PI.UpqRep.SmoothOnH B (fun g => τ g v)) :
    v ∈ PI.PhMeasCore.smoothVecs A (fun g => τ (P⁻¹ * g * P)) := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hmem : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * A * g = A → PI.UpqRep.inUH B (P⁻¹ * g * P) := by
    intro g hg
    unfold PI.UpqRep.inUH
    have h1 : P * (P⁻¹ * g * P) = g * P := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    calc (P⁻¹ * g * P)ᴴ * B * (P⁻¹ * g * P)
        = (P * (P⁻¹ * g * P))ᴴ * A * (P * (P⁻¹ * g * P)) := by
          rw [← hA, conjTranspose_mul P]; simp only [Matrix.mul_assoc]
      _ = Pᴴ * (gᴴ * A * g) * P := by rw [h1, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = B := by rw [hg, hA]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => P⁻¹ * g * P
      map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by simp }
  let L' := LinearMap.toContinuousLinearMap L
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, hE⟩ := hv _ (hmem g₀ hg₀)
  refine ⟨L' ⁻¹' U, F ∘ L', hU.preimage L'.continuous, hm, hF.comp_continuousLinearMap L', fun g hg hg' => ?_⟩
  exact hE _ hg (hmem g hg')

lemma eq_of_equiv (hc : DSInfCharCap) {mu mu' : Fin n → ℝ} (hm : Formalism.QuantumDeterminants.IsHCParam mu)
    (hm' : Formalism.QuantumDeterminants.IsHCParam mu') (h : PI.UpqRep.IsDS ε mu τ) (h' : PI.UpqRep.IsDS ε mu' τ')
    (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ) (h0 : v ≠ 0) : mu = mu' := by
  refine eq_of_capP mu mu' hm.1 hm'.1 fun Y => ?_
  have e1 := hc n ε mu H τ hm h v hv Y
  have e2 := hc n ε mu' H' τ' hm' h' (V v) (smooth_equiv V hV hv) Y
  rw [← actU_equiv V hV, e1, map_smul] at e2
  exact smul_left_injective ℂ (by simpa using h0) e2

lemma inUJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ PI.UpqRep.UJset ε) (hb : b ∈ PI.UpqRep.UJset ε) :
    a * b ∈ PI.UpqRep.UJset ε := by
  show (a * b)ᴴ * PI.UpqRep.Jm ε * (a * b) = PI.UpqRep.Jm ε
  have ha' : aᴴ * PI.UpqRep.Jm ε * a = PI.UpqRep.Jm ε := ha
  have hb' : bᴴ * PI.UpqRep.Jm ε * b = PI.UpqRep.Jm ε := hb
  calc _ = bᴴ * (aᴴ * PI.UpqRep.Jm ε * a) * b := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

lemma cayley_quot {B P Q : Matrix (Fin n) (Fin n) ℂ} (hQ : IsUnit Q) (hP : Pᴴ * PI.UpqRep.Jm ε * P = B)
    (hQ' : Qᴴ * PI.UpqRep.Jm ε * Q = B) : P * Q⁻¹ ∈ PI.UpqRep.UJset ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  show (P * Q⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * Q⁻¹) = PI.UpqRep.Jm ε
  calc _ = (Q⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * Q⁻¹ := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Q * Q⁻¹)ᴴ * PI.UpqRep.Jm ε * (Q * Q⁻¹) := by
      rw [hP, ← hQ', conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

end

lemma exists_kfin {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} (R : Rep k r)
    {P : Mx k r} (hP : PI.UpqRep.IsCayleyU k r ε P) (h : PI.UpqRep.IsDS ε mu (fun g => R.σ (P⁻¹ * g * P))) :
    ∃ v, R.KFin v ∧ v ≠ 0 := by
  obtain ⟨S, hfin, hst, -, ⟨v, hvS, hv0, -⟩, -⟩ := h.2.2.2.2.2.1
  refine ⟨v, ⟨S, hfin, hvS, ?_⟩, hv0⟩
  rintro g ⟨hg, hgu⟩ x hx
  have hd := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : star P * P = 1 := Unitary.star_mul_self_of_mem hP.2
  have hPP' : P * star P = 1 := Unitary.mul_star_self_of_mem hP.2
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv hPP
  have hgu' : g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hgu
  have hu : P * g * star P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ hP.2 hgu') (Unitary.star_mem hP.2)
  have hJ : (P * g * star P)ᴴ * PI.UpqRep.Jm ε * (P * g * star P) = PI.UpqRep.Jm ε := by
    have hg' : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hg
    have hc := hP.1.2
    rw [Matrix.star_eq_conjTranspose] at hPP' ⊢
    calc _ = P * (gᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * g) * Pᴴ := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = (P * Pᴴ) * PI.UpqRep.Jm ε * (P * Pᴴ) := by
          rw [hc, hg', ← hc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPP']; simp
  have hK : P * g * star P ∈ PI.UpqRep.Kset ε := by
    refine ⟨hu, ?_⟩
    have h1 : (P * g * star P) * (P * g * star P)ᴴ = 1 := Unitary.mul_star_self_of_mem hu
    generalize P * g * star P = m at hJ h1
    calc m * PI.UpqRep.Jm ε = m * (mᴴ * PI.UpqRep.Jm ε * m) := by rw [hJ]
      _ = (m * mᴴ) * PI.UpqRep.Jm ε * m := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.one_mul]
  have := hst _ hK x hx
  have e : P⁻¹ * (P * g * star P) * P = g := by
    rw [hinv]
    calc _ = (star P * P) * g * (star P * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hPP]; simp
  simpa only [e] using this

theorem param_eq_of_equiv : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r), R.IsDS ε mu → R'.IsDS ε mu' → ∀ U : R.H ≃ₗᵢ[ℂ] R'.H, (∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)) → mu = mu' := by
  intro hy k r ε mu mu' R R' hR hR' U hU
  obtain ⟨hm, P, hP, h⟩ := hR
  obtain ⟨hm', Q, hQ, h'⟩ := hR'
  obtain ⟨v, hv, hv0⟩ := exists_kfin R hP h
  have hs := hy.1.2.2.1 k r ε mu R.H R.σ hm ⟨P, hP, h⟩ v hv
  have hs' := smooth_conj (A := Formalism.REAL.Jm ε) hP.1.1 hP.1.2 hs
  have hdP := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hdQ := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.1.1
  have p1 := Matrix.mul_nonsing_inv _ hdP
  have q1 := Matrix.mul_nonsing_inv _ hdQ
  have p2 := Matrix.nonsing_inv_mul _ hdP
  have q2 := Matrix.nonsing_inv_mul _ hdQ
  have p3 : ∀ B : Mx k r, P⁻¹ * (P * B) = B := fun B => by rw [← Matrix.mul_assoc, p2, Matrix.one_mul]
  have q3 : ∀ B : Mx k r, Q⁻¹ * (Q * B) = B := fun B => by rw [← Matrix.mul_assoc, q2, Matrix.one_mul]
  have p4 : ∀ B : Mx k r, P * (P⁻¹ * B) = B := fun B => by rw [← Matrix.mul_assoc, p1, Matrix.one_mul]
  have ha := cayley_quot hQ.1.1 hP.1.2 hQ.1.2
  have hb := cayley_quot hP.1.1 hQ.1.2 hP.1.2
  obtain ⟨⟨hone, hmul⟩, -⟩ := h'.2.2.1
  set τ' : Mx k r → (R'.H →L[ℂ] R'.H) := fun g => R'.σ (Q⁻¹ * g * Q) with hτ'
  have hmul' : ∀ a ∈ PI.UpqRep.UJset ε, ∀ b ∈ PI.UpqRep.UJset ε, ∀ x, τ' a (τ' b x) = τ' (a * b) x := by
    intro a ha b hb x
    rw [hmul a ha b hb]; rfl
  have hab : (P * Q⁻¹) * (Q * P⁻¹) = 1 := by simp only [Matrix.mul_assoc, q3, p1]
  have hba : (Q * P⁻¹) * (P * Q⁻¹) = 1 := by simp only [Matrix.mul_assoc, p3, q1]
  let A : R'.H ≃L[ℂ] R'.H := ContinuousLinearEquiv.equivOfInverse (τ' (P * Q⁻¹)) (τ' (Q * P⁻¹))
    (fun x => by rw [hmul' _ hb _ ha, hba, hone]; rfl) (fun x => by rw [hmul' _ ha _ hb, hab, hone]; rfl)
  refine eq_of_equiv hy.2.2.1 hm hm' h h' (U.toContinuousLinearEquiv.trans A) ?_ hs' hv0
  intro g hg x
  have hg' : g ∈ PI.UpqRep.UJset ε := hg
  have hG : P⁻¹ * g * P ∈ GG k r := by
    show (P⁻¹ * g * P)ᴴ * PI.UpqRep.Hpk k r * (P⁻¹ * g * P) = PI.UpqRep.Hpk k r
    have hgg : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    have hc := hP.1.2
    calc _ = (P * (P⁻¹ * g * P))ᴴ * PI.UpqRep.Jm ε * (P * (P⁻¹ * g * P)) := by
          rw [← hc, conjTranspose_mul P]; simp only [Matrix.mul_assoc]
      _ = Pᴴ * (gᴴ * PI.UpqRep.Jm ε * g) * P := by
          simp only [Matrix.mul_assoc, p4, conjTranspose_mul g]
      _ = _ := by rw [hgg, hc]
  show τ' (P * Q⁻¹) (U (R.σ (P⁻¹ * g * P) x)) = τ' g (τ' (P * Q⁻¹) (U x))
  have e : R'.σ (P⁻¹ * g * P) = τ' (Q * P⁻¹ * g * (P * Q⁻¹)) := by
    simp only [hτ', Matrix.mul_assoc, q3, q2, Matrix.mul_one]
  rw [hU _ hG, e, hmul' _ ha _ (inUJ_mul (inUJ_mul hb hg') ha), hmul' _ hg' _ ha]
  congr 2
  simp only [Matrix.mul_assoc, q3, p4]

end DSInequiv
end GlobalTheory
