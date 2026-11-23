import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntStd

noncomputable section

namespace GlobalTheory.MomN

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.KerInert Formalism.L2.KerInert.ISd

theorem transl_normVec_int : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → EqAt D p (StandardLatticesGL3.stdL D N) L → EqAt D p (StandardLatticesGL3.stdL D N') L' → ∀ t : VC D N N', TorsPrime D p (La D B.tor L L') t → ∃ (m : ℕ) (c : Fin m → ℂ) (s : Fin m → VC D N N'), (∀ k, c k ∈ Qbar ∧ IsIntP (lamC lam (c k))) ∧ (∀ k, TorsPrime D p (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (s k)) ∧ U D B.tor t (B.eNat χ N N' L L') = fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z := by
  intro D cc δ B hcc hδ χ hχ p _ lam N N' M M' hAdm hM hM' t ht
  obtain ⟨s, hs, hsM, hMs⟩ := hM
  obtain ⟨s', hs', hsM', hMs'⟩ := hM'
  have hp : p.Prime := Fact.out
  have spos : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs))
  have spos' : 0 < s' := Nat.pos_of_ne_zero (by rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs'))
  set La0 := La D (tor0 D cc δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') with hLa0
  set La1 := La D (tor0 D cc δ) M (Formalism.MainNotions.StandardLatticesGL3.stdL D N') with hLa1
  set La2 := La D (tor0 D cc δ) M M' with hLa2
  have one_std : ∀ y ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N', ((1 : ℕ) : D.host.E) • y ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N' := by
    intro y hy; simpa using hy
  have one_M : ∀ y ∈ M, ((1 : ℕ) : D.host.E) • y ∈ M := by
    intro y hy; simpa using hy
  have k10 : ∀ z ∈ La1, (s * 1) • z ∈ La0 := fun z hz => La_smul cc δ s 1 hsM one_std hz
  have k21 : ∀ z ∈ La2, (1 * s') • z ∈ La1 := fun z hz => La_smul cc δ 1 s' one_M hMs' hz
  have k20 : ∀ z ∈ La2, (s * s') • z ∈ La0 := fun z hz => La_smul cc δ s s' hsM hMs' hz
  have k12 : ∀ z ∈ La1, (1 * s') • z ∈ La2 := fun z hz => La_smul cc δ 1 s' one_M hsM' hz
  have hδ0 : δ ≠ 0 := delta_nonzero_link D cc hcc δ hδ
  have hI : IO.HfInt (tor0 D cc δ) La2 := hermitian_form_integral_values D cc hcc δ hδ hδ0 N N' M M' hAdm

  let Q2 : VC D N N' → Prop := fun y => ∃ n : ℕ, 0 < n ∧ n • y ∈ La2
  have q2_add : ∀ x y, Q2 x → Q2 y → Q2 (x + y) := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have e : (n * m) • (x + y) = m • (n • x) + n • (m • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm m n]
    rw [e]
    exact add_mem (AddSubgroup.nsmul_mem _ hx m) (AddSubgroup.nsmul_mem _ hy n)
  have q2_2 : ∀ x ∈ La2, Q2 x := fun x hx => ⟨1, one_pos, by simpa using hx⟩
  have q2_1 : ∀ x ∈ La1, Q2 x := fun x hx => ⟨1 * s', by omega, k12 x hx⟩
  have cf_good : ∀ x y, Q2 x → Q2 y → Good lam (IO.cf (tor0 D cc δ) x y) := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    obtain ⟨q, hq⟩ := im_rat (tor0 D cc δ) hI hn hm hx hy
    exact good_cf lam _ x y q hq

  have R1 : Rep lam B.tor (fun y => y ∈ La1) (B.thHalf N N' M) (B.thZero N N') := by
    show Rep lam B.tor (fun y => y ∈ La1) (Iop D B.tor La0 La1 (B.thZero N N')) (B.thZero N N')
    refine rep_Iop (Pt := fun y => y = 0) (rep_self rfl) ?_ ?_
    · rintro x hx y rfl
      exact ⟨cf_good x 0 (q2_1 x hx) (q2_2 0 (zero_mem _)), by simpa using hx⟩
    · exact idx_coprime La0 La1 (s * 1) (by simpa using hs) k10

  have R2 : Rep lam B.tor (fun y => ∃ a ∈ La2, ∃ b ∈ La1, y = a + b) (B.thMoved N N' M M') (B.thZero N N') := by
    show Rep lam B.tor _ (Iop D B.tor La1 La2 (B.thHalf N N' M)) (B.thZero N N')
    refine rep_Iop R1 ?_ ?_
    · intro x hx y hy
      exact ⟨cf_good x y (q2_2 x hx) (q2_1 y hy), x, hx, y, hy, rfl⟩
    · exact idx_coprime La1 La2 (1 * s') (by simpa using hs') k21

  obtain ⟨n, hn, hnp, hnt⟩ := ht
  have R3 : Rep lam B.tor (TorsPrime D p La0) (U D B.tor t (B.thMoved N N' M M')) (B.thZero N N') := by
    refine rep_U t R2 ?_
    rintro y ⟨a, ha, b, hb, rfl⟩
    refine ⟨cf_good t _ ⟨n, hn, hnt⟩ (q2_add a b (q2_2 a ha) (q2_1 b hb)), ?_⟩
    refine ⟨n * (s * s'), Nat.mul_pos hn (Nat.mul_pos spos spos'), Nat.Coprime.mul hnp (Nat.Coprime.mul hs hs'), ?_⟩
    have e : (n * (s * s')) • (t + (a + b)) = (s * s') • (n • t) + (n • ((s * s') • a) + (n * s') • ((s * 1) • b)) := by
      simp only [smul_add, smul_smul]
      congr 1
      · rw [mul_comm]
      · congr 1
        rw [mul_one, mul_assoc, mul_comm s' s]
    rw [e]
    exact add_mem (k20 _ hnt) (add_mem (AddSubgroup.nsmul_mem _ (k20 a ha) n)
      (AddSubgroup.nsmul_mem _ (k10 b hb) (n * s')))

  have hchi := RestC.chiFacUnit (D := D) χ hχ p lam N N' M M' hAdm ⟨s, hs, hsM, hMs⟩ ⟨s', hs', hsM', hMs'⟩
  have hgood : Good lam (Base.chiFac χ N N' M M') := ⟨hchi.1, le_of_eq hchi.2⟩
  have R4 := rep_smul hgood R3
  have e : U D B.tor t (B.eNat χ N N' M M') = fun z => Base.chiFac χ N N' M M' * U D B.tor t (B.thMoved N N' M M') z := by
    funext z
    exact IO.U_smul _ t _ _ z
  rw [e]
  obtain ⟨m, c, s₀, hc, hs₀, hF⟩ := R4
  exact ⟨m, c, s₀, hc, hs₀, hF⟩

end GlobalTheory.MomN
