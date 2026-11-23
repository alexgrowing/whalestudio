import Formalism.WachLatticeTwists.SandwichH1Classes.PerturbationForScalarTwist
import Formalism.WachLatticeTwists.SandwichH1Classes.SandwichH1Proofs.MatrixMapH1EqOnH1

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

theorem betaAB : StatBetaAB := by
  intro ℓ hℓ s e hs
  by_cases he : e = 0
  · subst he
    simp only [bR, aR, beta, if_true, Nat.factorial_zero, padicValNat.one, mul_zero, add_zero]
    omega
  · have h1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
    rw [← betaCount ℓ hℓ s e h1]
    simp only [bR, aR, if_neg he]
    obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le hs
    push_cast
    simp only [Nat.add_sub_cancel_left]
    ring

lemma tf_pow' {ℓ : ℕ} [Fact ℓ.Prime] {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V]
    (h : ∀ x : V, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) (n : ℕ) (x : V) (hx : ((ℓ : ℤ_[ℓ]) ^ n) • x = 0) : x = 0 := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    apply ih
    rw [pow_succ', mul_smul] at hx
    exact h _ hx

theorem recip : StatRecip := by
  intro ℓ _ D s e Os _ _ cupL hs htf hLa hV x k n hx hn
  have hℓ : ℓ.Prime := Fact.out
  rw [hLa] at hx
  obtain ⟨y, hy⟩ := hx
  obtain ⟨z, hz⟩ := hV y
  refine ⟨z, ?_⟩
  have hab := betaAB ℓ hℓ s e hs
  have hnat : aR ℓ s e + n = bR ℓ s e + k := by omega
  have : ((ℓ : ℤ_[ℓ]) ^ aR ℓ s e) • (((ℓ : ℤ_[ℓ]) ^ n) • x - D.ex (D.jW z)) = 0 := by
    rw [smul_sub, hz, hy, smul_smul, smul_smul, ← pow_add, ← pow_add, hnat, sub_self]
  exact sub_eq_zero.mp (tf_pow' htf _ _ this)

theorem kerExp : StatKerExp := by
  intro F _ HV Tg _ _ _ _ _ _ ex Hf δ S c hc hS hval hdim ⟨Lu, hLf, hLk, hLd⟩ z hz
  have hsurj : LinearMap.range ex = ⊤ := by
    rw [eq_top_iff, ← hS, Submodule.span_le]
    intro y hy
    obtain ⟨z, hz⟩ := hval y hy
    refine ⟨c⁻¹ • z, ?_⟩
    rw [map_smul, hz, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hrn := LinearMap.finrank_range_add_finrank_ker ex
  rw [hsurj, finrank_top, hdim] at hrn
  have hk : Module.finrank F (LinearMap.ker ex) = δ := by omega
  have : Lu = LinearMap.ker ex := Submodule.eq_of_le_of_finrank_eq hLk (by rw [hLd, hk])
  exact hLf (this ▸ (LinearMap.mem_ker.mpr hz))

theorem class_of_w_zero_in_H1 : ClassOfWZeroInH1 := by
  intro ℓ _ G _ _ _ M _ _ _ _ _ _ MB _ _ _ _ _ a aB F H γ lg ε s N La c hlg hadd hH hgen hγ hfix hcH hLa
  have key := logClass ℓ G M a H γ lg c (c.1 γ) hlg hadd hH hgen hfix hcH rfl
  set y : MB := ((ε⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (((ℓ : ℤ_[ℓ]) ^ N) • F.f (c.1 γ)) with hy
  have hyfix : ∀ g, aB g y = y := by
    intro g
    rw [hy, map_smul, map_smul, ← F.eqv, hfix]
  let c' : Z1 aB := ⟨fun σ => lg σ • y, hlg.smul continuous_const, fun g h => by
    show lg (g * h) • y = lg g • y + aB g (lg h • y)
    rw [map_smul, hyfix, hadd, add_smul]⟩
  refine ⟨y, La.smul_mem _ hLa, c', fun σ => rfl, ?_⟩
  show ((ℓ : ℤ_[ℓ]) ^ (s + N)) • Submodule.mkQ _ (F.onZ c) = Submodule.mkQ _ c'
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  funext σ
  show ((ℓ : ℤ_[ℓ]) ^ (s + N)) • F.f (c.1 σ) = lg σ • y
  have e1 : ((ε⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (ε : ℤ_[ℓ]) = 1 := by rw [← Units.val_mul]; simp
  have e2 : ((ℓ : ℤ_[ℓ]) ^ s) • c.1 σ = (((ε⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * lg σ) • c.1 γ := by
    rw [mul_smul, ← key σ, hγ, smul_smul, ← mul_assoc, e1, one_mul]
  rw [hy, pow_add, mul_comm, mul_smul, ← map_smul F.f, e2, map_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
