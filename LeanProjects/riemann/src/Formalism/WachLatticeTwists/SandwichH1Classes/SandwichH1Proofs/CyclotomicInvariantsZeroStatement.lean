import Formalism.WachLatticeTwists.SandwichH1Classes.ComparisonMatrixIntertwinesEndomorphisms
import Formalism.WachLatticeTwists.SandwichH1Classes.SandwichH1Proofs.LevelOneComputationZero

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

theorem pieceBThm : StatPieceB := by
  intro ℓ _ R r r₀ M0 h0 S Um Vm U Y Y' F hX hI hY1 hY2 hVm hHT i infm infX hInf hT4
  obtain ⟨hv, hm1, hm2, hw2⟩ := w_facts R F
  have hcoc := slOfInter ℓ R.Gg R.OC R.actO r S Um Y Y' F.lnzd hI hY1
  have hMx := ofFun_Mx R.actO Um hcoc
  have hDT : Inter (SL.ofFun R.actO Um) S Y := by
    intro g
    rw [hMx]
    exact hI g
  have hTD := interInv ℓ R.Gg R.OC R.actO r _ _ _ Y' F.lnzd hDT hY1 hY2
  have hDTi := interTwist ℓ R.Gg R.OC R.actO r _ _ _ R.χ i hDT
  have hTDi := interTwist ℓ R.Gg R.OC R.actO r _ _ _ R.χ i hTD
  have hT3 : ∀ j : ℤ, _ := fun j => t3W ℓ R.Tt r Vm R.z R.z' R.ϖ R.ϖ₁ R.w j F.zz F.ϖϖ hX.1 hX.2
    hVm hw2
  refine ⟨?_, hInf, hT4, hT3 i, ?_, ?_⟩
  · intro x
    show matrixMapOnH1 _ _ Y R.p (matrixMapOnH1 _ _ Y' R.p x) = _
    rw [matrix_map_H1_eq_onH1 _ _ _ _ hDTi, matrix_map_H1_eq_onH1 _ _ _ _ hTDi]
    exact sandwich_composite_on_H1 ℓ R.Gg R.G R.OC R.actO r _ _ _ _ hDTi hTDi R.p hY2 x
  · intro x hx
    funext k
    exact F.omtf _ (congrFun hx k)
  · exact htW ℓ R.Tt r Vm R.w U F.omtf hHT (fun u _ => (hT3 u).1) i

theorem square : StatSquare := by
  intro OC _ r c A B hc h
  have hpow : ∀ (n : ℕ) (a : OC), c ^ n * a = 0 → a = 0 := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih =>
      intro a ha
      apply ih
      apply hc
      rw [← mul_assoc, ← pow_succ']
      exact ha
  have h0 : A * (B * A - c • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, sub_self]
  have h1 : A.det • (B * A - c • 1) = 0 := by
    have := congrArg (fun M => A.adjugate * M) h0
    simp only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_zero] at this
    exact this
  have hdet : A.det * B.det = c ^ r := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hz : B * A - c • 1 = 0 := by
    ext i j
    have e := congrFun (congrFun h1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at e
    apply hpow r
    rw [← hdet, mul_comm A.det, mul_assoc, e, mul_zero]
  exact sub_eq_zero.mp hz

theorem sec3 : StatSec3 := by
  intro ℓ _ G _ OC Om _ _ _ eO actO r ρ S Sτ Um Vm Y Y' Pp Sp Cm Bm t hℓ hinj hI hY2 hP hS hB hV
  set Cq := Cm.map eO with hCq
  set Bq := Bm.map eO with hBq
  set Z := Y * Pp with hZ
  have h1 : (Sp * Y' * Bq) * (Cq * Z) = (ℓ : OC) • (1 : Matrix (Fin ρ) (Fin ρ) OC) := by
    rw [Matrix.mul_assoc, ← hB, hZ, Matrix.mul_assoc, ← Matrix.mul_assoc Y', hY2, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, hS]
  have h2 := square OC ρ (ℓ : OC) _ _ hℓ h1
  have hCB : Cm * Bm = 1 := by
    have e1 : (Cq * Bq) * (Cq * Z) = Cq * Z := by rw [Matrix.mul_assoc, ← hB]
    have e2 : (ℓ : OC) • (Cq * Bq) = (ℓ : OC) • (1 : Matrix (Fin ρ) (Fin ρ) OC) := by
      have := congrArg (fun M => M * (Sp * Y' * Bq)) e1
      simp only [Matrix.mul_assoc (Cq * Bq), h2, Matrix.mul_smul, Matrix.mul_one] at this
      exact this
    have e3 := mat_cancel (ℓ : OC) hℓ e2
    ext a b
    apply hinj
    have := congrFun (congrFun e3 a) b
    rw [hCq, hBq, ← Matrix.map_mul] at this
    rw [show eO ((Cm * Bm) a b) = ((Cm * Bm).map eO) a b from rfl, this]
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  refine ⟨h1, h2, ?_, hCB, ?_⟩
  · intro g
    rw [Matrix.map_mul, hZ, Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_assoc, hP g,
      ← Matrix.mul_assoc (Y.map _), hI g, Matrix.mul_assoc (Um g), ← hZ]
    conv_lhs => rw [hB]
    simp only [Matrix.mul_assoc]
  · intro a b
    have : Cm * Vm * Bm - (1 : Matrix (Fin ρ) (Fin ρ) Om) = Cm * (Vm - 1) * Bm := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hCB]
    rw [this, Matrix.mul_apply]
    refine Finset.dvd_sum fun q _ => ?_
    apply Dvd.dvd.mul_right
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun q' _ => Dvd.dvd.mul_left (hV q' q) _

theorem cyclotomicInvariantsZero_statement : CyclotomicInvariantsZero := by
  intro ℓ _ R r r₀ M0 h0 S Um Vm U Y Y' F hX hI hY1 hY2 hVm hHT h0U hfix hemb hg0 hUH hUg v hv
  obtain ⟨hval, hm1, hm2, hw2⟩ := w_facts R F
  have hcoc := slOfInter ℓ R.Gg R.OC R.actO r S Um Y Y' F.lnzd hI hY1
  have hMx := ofFun_Mx R.actO Um hcoc
  have hDT : Inter (SL.ofFun R.actO Um) S Y := by
    intro g
    rw [hMx]
    exact hI g
  have hTD := interInv ℓ R.Gg R.OC R.actO r _ _ _ Y' F.lnzd hDT hY1 hY2
  have hT3 := t3W ℓ R.Tt r Vm R.z R.z' R.ϖ R.ϖ₁ R.w 0 F.zz F.ϖϖ hX.1 hX.2 hVm hw2
  have hT3all : ∀ j : ℤ, _ := fun j => t3W ℓ R.Tt r Vm R.z R.z' R.ϖ R.ϖ₁ R.w j F.zz F.ϖϖ hX.1 hX.2
    hVm hw2
  have hHTp := htW ℓ R.Tt r Vm R.w U F.omtf hHT (fun u _ => (hT3all u).1) 0

  set y := v ᵥ* Y' with hy
  have hinv : ∀ g : R.G, (fun k => R.actO (R.p g) (y k)) ᵥ* Um (R.p g) = y := by
    intro g
    have h1 : (fun k => R.actO (R.p g) (v k)) ᵥ* S.Mx (R.p g) = v := by
      have := hv g
      have e : repS R S 0 g v = (fun k => R.actO (R.p g) (v k)) ᵥ*
          ((((R.χ (R.p g)) ^ (0 : ℤ) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • S.Mx (R.p g)) := rfl
      rw [e] at this
      simpa using this
    have h2 := hTD (R.p g)
    rw [hMx] at h2
    rw [hy, map_vecMul', Matrix.vecMul_vecMul, h2, ← Matrix.vecMul_vecMul, h1]

  have hcoord : ∀ k, ∃ a : R.Tt.Oi, R.emb a = y k := by
    intro k
    apply hfix
    intro h hh
    have := congrFun (hinv h) k
    rw [hUH h hh, Matrix.vecMul_one] at this
    exact this
  choose a ha using hcoord
  have hrel : ∀ t, ∑ q, R.Tt.g0 (a q) * algebraMap R.Tt.Om R.Tt.Oi (Vm q t) = a t := by
    intro t
    apply hemb
    have := congrFun (hinv R.gg) t
    rw [hUg] at this
    rw [ha t, ← this, map_sum]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, map_mul, ← hg0, ha]
    rfl

  let am : Fin r → R.Tt.Om := fun t => R.Tt.pr (a t)
  have ham : R.Tt.gmI Vm R.w 0 am = am := by
    rw [gmI_apply]
    funext t
    have := congrArg R.Tt.pr (hrel t)
    rw [map_sum] at this
    show ∑ q, R.Tt.Vi Vm R.w 0 t q * R.Tt.pr (a q) = R.Tt.pr (a t)
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e : R.Tt.pr (R.Tt.g0 (a q) * algebraMap R.Tt.Om R.Tt.Oi (Vm q t)) = Vm q t * R.Tt.pr (a q) := by
      rw [mul_comm, ← Algebra.smul_def, map_smul, R.Tt.pr_comp_g_zero, smul_eq_mul]
    rw [e, Vi_apply]
    simp
  have htf : ∀ x : Fin r → R.Tt.Om, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0 := by
    intro x hx
    funext k
    exact F.omtf _ (congrFun hx k)
  have ham0 : am = 0 := eigenInj ℓ R.w _ hm1 (fun _ => hm2) hval U 0 h0U (Fin r → R.Tt.Om)
    (R.Tt.gmI Vm R.w 0) htf hHTp am ham

  let aX : Fin r → R.Tt.Xm := fun t => ⟨a t, congrFun ham0 t⟩
  have haX : R.Tt.gXI Vm R.w 0 aX = aX := by
    funext t
    apply Subtype.ext
    rw [gXI_coe]
    show ∑ q, R.Tt.Vi Vm R.w 0 t q • R.Tt.g0 (a q) = a t
    rw [← hrel t]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Vi_apply, Algebra.smul_def, mul_comm]
    simp
  have haX0 := hT3.1 aX haX
  have ha0 : ∀ t, a t = 0 := fun t => congrArg (fun z : R.Tt.Xm => (z : R.Tt.Oi)) (congrFun haX0 t)
  have hy0 : y = 0 := by
    funext k
    rw [← ha k, ha0 k, map_zero]
    rfl
  have : (ℓ : R.OC) • v = 0 := by
    have e : (v ᵥ* Y') ᵥ* Y = (ℓ : R.OC) • v := by
      rw [Matrix.vecMul_vecMul, hY2, Matrix.vecMul_smul, Matrix.vecMul_one]
    rw [← e, ← hy, hy0, Matrix.zero_vecMul]
  funext k
  exact F.lnzd _ (congrFun this k)

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
