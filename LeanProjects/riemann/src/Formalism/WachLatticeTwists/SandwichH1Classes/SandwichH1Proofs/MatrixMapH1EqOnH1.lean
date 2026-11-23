import Formalism.WachLatticeTwists.SandwichH1Classes.HypothesisWGivesUnitCongruence
import Formalism.WachLatticeTwists.SandwichH1Classes.SandwichH1Proofs.GmIApply

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

section

variable {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ) {r : ℕ}

def hat (M : Matrix (Fin r) (Fin r) R.As) : Matrix (Fin r) (Fin r) R.WC := (M.map R.jA).map R.ι

lemma hat_mul (M M' : Matrix (Fin r) (Fin r) R.As) : hat R (M * M') = hat R M * hat R M' := by
  unfold hat
  rw [Matrix.map_mul, Matrix.map_mul]

lemma hat_one : hat R (1 : Matrix (Fin r) (Fin r) R.As) = 1 := by
  unfold hat
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

lemma hat_inj {M0 h0 : ℕ} (F : R.Facts r M0 h0) {M M' : Matrix (Fin r) (Fin r) R.As}
    (h : hat R M = hat R M') : M = M' := by
  ext i j
  exact F.injj (F.injι (congrFun (congrFun h i) j))

lemma map_inj_ι {M0 h0 : ℕ} (F : R.Facts r M0 h0) {M M' : Matrix (Fin r) (Fin r) R.AA}
    (h : M.map R.ι = M'.map R.ι) : M = M' := by
  ext i j
  exact F.injι (congrFun (congrFun h i) j)

end

theorem gmCocycle : StatGmCocycle := by
  intro ℓ _ R r L En M0 h0 W F
  have cancel : ∀ M M' : Matrix (Fin r) (Fin r) R.WC, M * W.Xx = M' * W.Xx → M = M' := by
    intro M M' h
    have : M * W.Xx * W.Xi = M' * W.Xx * W.Xi := by rw [h]
    rwa [Matrix.mul_assoc, Matrix.mul_assoc, W.inv1, Matrix.mul_one, Matrix.mul_one] at this
  constructor
  · apply hat_inj R F
    apply cancel
    rw [hat_one, Matrix.one_mul]
    have := W.W2 1
    rw [L.one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
    rw [show hat R (W.Gm 1) * W.Xx = ((W.Gm 1).map R.jA).map R.ι * W.Xx from rfl, ← this]
    ext i j
    simp
  · intro h
    apply hat_inj R F
    apply cancel
    have e1 : (hat R (W.Gm h)).map (R.act R.γ) = hat R ((W.Gm h).map R.σ) := by
      ext i j
      show R.act R.γ (R.ι (R.jA (W.Gm h i j))) = R.ι (R.jA (R.σ (W.Gm h i j)))
      rw [← F.eqι, F.gσ]
    have e2 : ((L.ρ h).map (algebraMap ℤ_[ℓ] R.WC)).map (R.act R.γ)
        = (L.ρ h).map (algebraMap ℤ_[ℓ] R.WC) := by
      ext i j
      exact F.actZ _ _
    have e3 : W.Xx.map (R.act (R.γ * h)) = (W.Xx.map (R.act h)).map (R.act R.γ) := by
      ext i j
      simp [map_mul]
    calc hat R (W.Gm (R.γ * h)) * W.Xx
        = W.Xx.map (R.act (R.γ * h)) * ((L.ρ (R.γ * h)).map (algebraMap ℤ_[ℓ] R.WC)) := (W.W2 _).symm
      _ = (W.Xx.map (R.act h) * (L.ρ h).map (algebraMap ℤ_[ℓ] R.WC)).map (R.act R.γ)
            * (L.ρ R.γ).map (algebraMap ℤ_[ℓ] R.WC) := by
          rw [L.mul, Matrix.map_mul, Matrix.map_mul, e2, e3, Matrix.mul_assoc]
      _ = (hat R (W.Gm h)).map (R.act R.γ) * (W.Xx.map (R.act R.γ)
            * (L.ρ R.γ).map (algebraMap ℤ_[ℓ] R.WC)) := by
          rw [W.W2 h, Matrix.map_mul, Matrix.mul_assoc]
          rfl
      _ = hat R ((W.Gm h).map R.σ * W.Gm R.γ) * W.Xx := by
          rw [W.W2 R.γ, e1, hat_mul, Matrix.mul_assoc]
          rfl

theorem gmIter : StatGmIter := by
  intro ℓ _ R r L En M0 h0 W F k i
  obtain ⟨g1, gmul⟩ := gmCocycle ℓ R r L En M0 h0 W F
  induction k with
  | zero =>
    rw [pow_zero, g1, Function.iterate_zero, id]
    funext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  | succ k ih =>
    rw [pow_succ', gmul, Function.iterate_succ_apply', ← ih, Matrix.mul_apply_eq_vecMul]
    rfl

theorem w3Vm : HypothesisWGivesUnitCongruence := by
  intro ℓ _ R r L En M0 h0 W F a b
  have hℓ : ℓ.Prime := Fact.out
  have hz : R.z ∣ (ℓ : R.Tt.Om) := ⟨R.z', by rw [F.zz]; simp⟩
  have hϖ : R.ϖ ∣ (ℓ : R.Tt.Om) := ⟨R.ϖ₁, by rw [F.ϖϖ]; simp⟩
  have := w3Um ℓ hℓ R.As R.Tt.Om R.σ R.πs R.ϑs R.z R.ϖ R.ϖ' r R.s (n0 ℓ (M0 + h0)) (W.Gm R.γ)
    F.σ1 F.σ2 (W.W3 R.γ) F.ϑπ F.dv' hz hϖ F.dvd a b
  rw [← gmIter ℓ R r L En M0 h0 W F, ← F.pg] at this
  have e : (VmW R L W - 1) a b
      = R.ϑs (W.Gm (R.p R.gg) a b - (1 : Matrix (Fin r) (Fin r) R.As) a b) := by
    rw [map_sub, Matrix.sub_apply]
    congr 1
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  rw [e]
  exact this

theorem wInter : StatWInter := by
  intro ℓ _ R r L En M0 h0 W A F hA g
  have key : A.map (R.actA g) * (L.ρ g).map (algebraMap ℤ_[ℓ] R.AA)
      = ((R.cx g) ^ M0 • W.Gm g).map R.jA * A := by
    apply map_inj_ι R F
    have e1 : (A.map (R.actA g)).map R.ι = (A.map R.ι).map (R.act g) := by
      ext i j
      exact F.eqι g _
    have e2 : ((L.ρ g).map (algebraMap ℤ_[ℓ] R.AA)).map R.ι = (L.ρ g).map (algebraMap ℤ_[ℓ] R.WC) := by
      ext i j
      exact F.algι _
    have e3 : ((R.ι (R.jA R.x)) ^ M0 • W.Xx).map (R.act g)
        = (R.ι (R.jA (R.cx g)) * R.ι (R.jA R.x)) ^ M0 • W.Xx.map (R.act g) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
      rw [← F.eqι, F.gx, map_mul]
    have e4 : (((R.cx g) ^ M0 • W.Gm g).map R.jA).map R.ι
        = (R.ι (R.jA (R.cx g))) ^ M0 • ((W.Gm g).map R.jA).map R.ι := by
      ext i j
      simp
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2, hA, e3, e4, Matrix.smul_mul, W.W2 g, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, mul_pow]
  have := congrArg (fun M => M.map R.ϑ) key
  simp only [Matrix.map_mul] at this
  have f1 : (A.map (R.actA g)).map R.ϑ = (A.map R.ϑ).map (R.actO g) := by
    ext i j
    exact F.eqϑ g _
  have f2 : ((L.ρ g).map (algebraMap ℤ_[ℓ] R.AA)).map R.ϑ = (L.sl R.actO).Mx g := by
    ext i j
    exact F.algϑ _
  rw [f1, f2] at this
  exact this

theorem umVm : StatUmVm := by
  intro ℓ _ R r L En M0 h0 W F
  have hℓ : ℓ.Prime := Fact.out
  set X := R.ϑ (R.jA R.x) with hX
  have hN : 1 ≤ ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1) :=
    Nat.mul_pos (pow_pos hℓ.pos _) (Nat.sub_pos_of_lt hℓ.one_lt)
  have nzd : ∀ a : R.OC, X * a = 0 → a = 0 := by
    intro a ha
    apply F.lnzd
    obtain ⟨N, hN'⟩ := Nat.exists_eq_add_of_le hN
    rw [← F.thx, hN', add_comm, pow_succ]
    calc X ^ N * X * R.c * a = X ^ N * R.c * (X * a) := by ring
      _ = 0 := by rw [ha, mul_zero]
  have hc : R.ϑ (R.jA (R.cx (R.p R.gg))) = 1 := by
    have h1 := congrArg R.ϑ (F.gx (R.p R.gg))
    rw [F.eqϑ, F.fixx, map_mul] at h1
    have : X * (R.ϑ (R.jA (R.cx (R.p R.gg))) - 1) = 0 := by
      rw [mul_sub, mul_one, mul_comm, ← h1, sub_self]
    exact sub_eq_zero.mp (nzd _ this)
  ext a b
  show R.ϑ (R.jA ((R.cx (R.p R.gg)) ^ M0 * W.Gm (R.p R.gg) a b))
    = R.emb (algebraMap R.Tt.Om R.Tt.Oi (R.ϑs (W.Gm (R.p R.gg) a b)))
  rw [F.embϑ, map_mul, map_mul, map_pow, map_pow, hc, one_pow, one_mul]

lemma ofFun_Mx {ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] {OC : Type} [CommRing OC] [Algebra ℤ_[ℓ] OC]
    (actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)) {r : ℕ} (Um : G → Matrix (Fin r) (Fin r) OC)
    (h : Um 1 = 1 ∧ ∀ g h, Um (g * h) = (Um h).map (actO g) * Um g) : (SL.ofFun actO Um).Mx = Um := by
  unfold SL.ofFun
  rw [dif_pos h]

lemma matrix_map_H1_eq_onH1 {ℓ : ℕ} [Fact ℓ.Prime] {G G' : Type} [Group G] [Group G'] [TopologicalSpace G'] {OC : Type}
    [CommRing OC] [Algebra ℤ_[ℓ] OC] [TopologicalSpace OC] [IsTopologicalRing OC]
    [ContinuousConstSMul ℤ_[ℓ] OC] {actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)} {r : ℕ} (S S' : SL actO r)
    (Y : Matrix (Fin r) (Fin r) OC) (p : G' →* G) (h : Inter S S' Y) :
    matrixMapOnH1 S S' Y p = (h.eqMap.comap p).onH := by
  unfold matrixMapOnH1
  rw [dif_pos h]

lemma w_facts {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ) {r M0 h0 : ℕ} (F : R.Facts r M0 h0) :
    PadicInt.valuation ((R.w : ℤ_[ℓ]) - 1) = mOf ℓ R.s (M0 + h0) ∧ 1 ≤ mOf ℓ R.s (M0 + h0) ∧
      2 ≤ mOf ℓ R.s (M0 + h0) ∧ (ℓ : ℤ_[ℓ]) ^ 2 ∣ (R.w : ℤ_[ℓ]) - 1 := by
  obtain ⟨h1, h2, h3, _⟩ := genM ℓ (R.χ R.γ) R.s (M0 + h0) F.s1 F.s2 F.valγ
  have hw : R.w = (R.χ R.γ) ^ (ℓ ^ (R.s + n0 ℓ (M0 + h0) + 1)) := by
    unfold Setup.w
    rw [F.pg, map_pow]
  rw [← hw] at h1
  refine ⟨h1, h2, h3, ?_⟩
  by_cases h0' : (R.w : ℤ_[ℓ]) - 1 = 0
  · rw [h0']; exact dvd_zero _
  · rw [← Ideal.mem_span_singleton, PadicInt.mem_span_pow_iff_le_valuation _ h0', h1]
    exact h3

theorem pieceWThm : StatPieceW := by
  intro ℓ _ R r L En M0 h0 W U A Y' F hX hA hY1 hY2 hHT i infm infX hInf hT4
  obtain ⟨hv, hm1, hm2, hw2⟩ := w_facts R F
  have hI := wInter ℓ R r L En M0 h0 W A F hA
  have hcoc := slOfInter ℓ R.Gg R.OC R.actO r (L.sl R.actO) (UmW R L W) (A.map R.ϑ) Y' F.lnzd hI hY1
  have hMx := ofFun_Mx R.actO (UmW R L W) hcoc
  have hDT : Inter (SL.ofFun R.actO (UmW R L W)) (L.sl R.actO) (A.map R.ϑ) := by
    intro g
    rw [hMx]
    exact hI g
  have hTD := interInv ℓ R.Gg R.OC R.actO r _ _ _ Y' F.lnzd hDT hY1 hY2
  have hDTi := interTwist ℓ R.Gg R.OC R.actO r _ _ _ R.χ i hDT
  have hTDi := interTwist ℓ R.Gg R.OC R.actO r _ _ _ R.χ i hTD
  have hVm := w3Vm ℓ R r L En M0 h0 W F
  have hT3 : ∀ j : ℤ, _ := fun j => t3W ℓ R.Tt r (VmW R L W) R.z R.z' R.ϖ R.ϖ₁ R.w j F.zz F.ϖϖ hX.1 hX.2
    hVm hw2
  refine ⟨?_, hInf, hT4, hT3 i, ?_, ?_⟩
  · intro x
    show matrixMapOnH1 _ _ (A.map R.ϑ) R.p (matrixMapOnH1 _ _ Y' R.p x) = _
    rw [matrix_map_H1_eq_onH1 _ _ _ _ hDTi, matrix_map_H1_eq_onH1 _ _ _ _ hTDi]
    exact sandwich_composite_on_H1 ℓ R.Gg R.G R.OC R.actO r _ _ _ _ hDTi hTDi R.p hY2 x
  · intro x hx
    funext k
    exact F.omtf _ (congrFun hx k)
  · exact htW ℓ R.Tt r (VmW R L W) R.w U F.omtf hHT (fun u _ => (hT3 u).1) i

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
