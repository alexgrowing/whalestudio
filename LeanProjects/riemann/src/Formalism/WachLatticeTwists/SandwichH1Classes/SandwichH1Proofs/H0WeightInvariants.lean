import Formalism.WachLatticeTwists.SandwichH1Classes.InvariantsOfTwistedModule
import Formalism.WachLatticeTwists.SandwichH1Classes.SandwichH1Proofs.CyclotomicInvariantsZeroStatement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

lemma x_nzd {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ) {r M0 h0 : ℕ} (F : R.Facts r M0 h0) :
    ∀ a : R.OC, R.ϑ (R.jA R.x) * a = 0 → a = 0 := by
  have hℓ : ℓ.Prime := Fact.out
  have hN : 1 ≤ ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1) :=
    Nat.mul_pos (pow_pos hℓ.pos _) (Nat.sub_pos_of_lt hℓ.one_lt)
  intro a ha
  apply F.lnzd
  obtain ⟨N, hN'⟩ := Nat.exists_eq_add_of_le hN
  rw [← F.thx, hN', add_comm, pow_succ]
  calc R.ϑ (R.jA R.x) ^ N * R.ϑ (R.jA R.x) * R.c * a
      = R.ϑ (R.jA R.x) ^ N * R.c * (R.ϑ (R.jA R.x) * a) := by ring
    _ = 0 := by rw [ha, mul_zero]

theorem umH : StatUmH := by
  intro ℓ _ R r L En M0 h0 W F FH h hh
  have hs := FH.pH h hh
  have hG : W.Gm (R.p h) = 1 := by
    apply hat_inj R F
    rw [hat_one]
    have e : hat R (W.Gm (R.p h)) * W.Xx = W.Xx := by
      rw [show hat R (W.Gm (R.p h)) * W.Xx = ((W.Gm (R.p h)).map R.jA).map R.ι * W.Xx from rfl,
        ← W.W2, W.fixH _ hs]
    have := congrArg (fun M => M * W.Xi) e
    simp only [Matrix.mul_assoc, W.inv1, Matrix.mul_one] at this
    exact this
  have hc : R.ϑ (R.jA (R.cx (R.p h))) = 1 := by
    have h1 := congrArg R.ϑ (F.gx (R.p h))
    rw [FH.fixAs _ hs, map_mul] at h1
    have : R.ϑ (R.jA R.x) * (R.ϑ (R.jA (R.cx (R.p h))) - 1) = 0 := by
      rw [mul_sub, mul_one, mul_comm, ← h1, sub_self]
    exact sub_eq_zero.mp (x_nzd R F _ this)
  ext a b
  show R.ϑ (R.jA ((R.cx (R.p h)) ^ M0 * W.Gm (R.p h) a b)) = _
  rw [hG, map_mul, map_mul, map_pow, map_pow, hc, one_pow, one_mul]
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem h0W : InvariantsOfTwistedModule := by
  intro ℓ _ R r L En M0 h0 W A Y' F FH hA hY1 hY2 ρ Sτ Pp Sp Cm Bm Uτ hX hP hS hB hHT h0U hne infm infX X
    hInf hT4 hUn hFl hLES
  obtain ⟨hv, hm1, hm2, _⟩ := w_facts R F
  have hI := wInter ℓ R r L En M0 h0 W A F hA
  have hVm := w3Vm ℓ R r L En M0 h0 W F
  have hinjO : Function.Injective R.eOh := by
    intro a b hab
    have := FH.injE hab
    rw [← R.Tt.pr_alg a, this, R.Tt.pr_alg]
  obtain ⟨s1, s2, s3, s4, s5⟩ := sec3 ℓ R.Gg R.OC R.Tt.Om R.eOh R.actO r ρ (L.sl R.actO) Sτ (UmW R L W)
    (VmW R L W) (A.map R.ϑ) Y' Pp Sp Cm Bm (R.z * R.ϖ) F.lnzd hinjO hI hY2 hP hS hB hVm
  have hPiece := pieceBThm ℓ R ρ r M0 h0 Sτ _ (Cm * VmW R L W * Bm) Uτ _ _ F hX s3 s2 s1 s5 hHT 0 infm infX
    hInf hT4
  have hCB : Cm.map R.eOh * Bm.map R.eOh = 1 := by
    rw [← Matrix.map_mul, s4, Matrix.map_one _ (map_zero _) (map_one _)]
  have hzero := cyclotomicInvariantsZero_statement ℓ R ρ r M0 h0 Sτ _ (Cm * VmW R L W * Bm) Uτ _ _ F hX s3 s2 s1 s5 hHT h0U FH.t4
    FH.injE FH.g0E
    (by
      intro h hh
      show (Cm.map R.eOh).map (R.actO (R.p h)) * UmW R L W (R.p h) * Bm.map R.eOh = 1
      rw [umH ℓ R r L En M0 h0 W F FH h hh, Matrix.mul_one]
      have : (Cm.map R.eOh).map (R.actO (R.p h)) = Cm.map R.eOh := by
        ext a b
        exact FH.fixOi h hh _
      rw [this, hCB])
    (by
      show (Cm.map R.eOh).map (R.actO (R.p R.gg)) * UmW R L W (R.p R.gg) * Bm.map R.eOh = _
      have e1 : (Cm.map R.eOh).map (R.actO (R.p R.gg)) = Cm.map R.eOh := by
        ext a b
        show R.actO (R.p R.gg) (R.emb (algebraMap R.Tt.Om R.Tt.Oi (Cm a b))) = _
        rw [FH.g0E, AlgHom.commutes]
        rfl
      have e2 : UmW R L W (R.p R.gg) = (VmW R L W).map R.eOh := umVm ℓ R r L En M0 h0 W F
      rw [e1, e2, ← Matrix.map_mul, ← Matrix.map_mul]
      rfl)
  refine Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic.h0 ℓ R.w (mOf ℓ R.s (M0 + h0)) hm1 (fun _ => hm2) hv Uτ h0U hne (X.toH0 _) hPiece hUn hFl hLES
    ⟨?_, ?_⟩
  · intro x _ _
    exact Subtype.ext (hzero x.1 x.2)
  · intro x
    exact ⟨map_zero _, map_zero _⟩

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
