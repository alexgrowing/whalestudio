import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.WeilBound.CoreStatements.HodgeTatePoints.PowCongr
import Development.WeilBound.CoreStatements.HodgeTatePoints.RdBase
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalCharacterStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupTranslationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigenStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusProductStatement

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

section

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem sq_le_aug {X : Type} [AddCommGroup X] {M : Submodule R (X → C)}
    (hmul : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ M) : sqIdeal (augIdeal M) ≤ augIdeal M := by
  rw [sqIdeal, Submodule.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  refine mem_aug.2 ⟨hmul a ha.1 b hb.1, ?_⟩
  rw [Pi.mul_apply, (mem_aug.1 ha).2, zero_mul]

theorem adjoin_decomp (p : ℕ) {N : Type} [AddCommGroup N] {M : Submodule R (N → C)}
    (hone : (1 : N → C) ∈ M) (hmul : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ M) (hint : M ≤ intFun R N)
    {g : N → C} (hg : g ∈ Algebra.adjoin R ((afFun p M : Submodule R (N → C)) : Set (N → C))) :
    ∃ r : R, ∃ h ∈ afFun p M ⊓ augIdeal M, ∃ w ∈ sqIdeal (augIdeal M),
      g = r • (1 : N → C) + h + w := by
  induction hg using Algebra.adjoin_induction with
  | mem g hg =>
    obtain ⟨hg, hadd⟩ := hg
    obtain ⟨r, hr⟩ := hint hg 0
    have hval : ∀ x, (g - r • (1 : N → C)) x = g x - g 0 := fun x => by
      simp [Algebra.smul_def, hr]
    have hm : g - r • (1 : N → C) ∈ M := M.sub_mem hg (M.smul_mem r hone)
    refine ⟨r, g - r • (1 : N → C), ⟨⟨hm, fun x y => ?_⟩, mem_aug.2 ⟨hm, ?_⟩⟩, 0,
      Submodule.zero_mem _, by abel⟩
    · have := Submodule.sub_mem _ (hadd x y) (hadd 0 0)
      convert this using 1
      simp only [hval, add_zero]; ring
    · rw [hval, sub_self]
  | algebraMap r =>
    exact ⟨r, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by
      rw [add_zero, add_zero, Algebra.algebraMap_eq_smul_one]⟩
  | add a b _ _ ha hb =>
    obtain ⟨r, h, hh, w, hw, rfl⟩ := ha
    obtain ⟨r', h', hh', w', hw', rfl⟩ := hb
    exact ⟨r + r', h + h', Submodule.add_mem _ hh hh', w + w', Submodule.add_mem _ hw hw', by
      rw [add_smul]; abel⟩
  | mul a b _ _ ha hb =>
    obtain ⟨r, h, hh, w, hw, rfl⟩ := ha
    obtain ⟨r', h', hh', w', hw', rfl⟩ := hb
    refine ⟨r * r', r • h' + r' • h,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hh') (Submodule.smul_mem _ _ hh),
      r • w' + r' • w + (h + w) * (h' + w'),
      Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hw')
        (Submodule.smul_mem _ _ hw)) (Submodule.subset_span
          ⟨h + w, Submodule.add_mem _ hh.2 (sq_le_aug hmul hw),
            h' + w', Submodule.add_mem _ hh'.2 (sq_le_aug hmul hw'), rfl⟩), ?_⟩
    simp only [Algebra.smul_def, map_mul]
    ring

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {N : Type} [AddCommGroup N] [Module F N]

theorem proj_add (χ : MulChar F R) (g h : N → C) (x : N) :
    proj χ (g + h) x = proj χ g x + proj χ h x := by
  simp only [proj, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem proj_line (χ : MulChar F R) (g : N → C) (t : N) :
    proj χ (g ∘ LinearMap.toSpanSingleton F N t) 1 = proj χ g t := by
  simp [proj]

theorem proj_self [CharZero C] (χ : MulChar F R) (g : N → C) (t : N) (c : R)
    (hg : ∀ a : F, g (a • t) = algebraMap R C (c * χ a)) : proj χ g t = algebraMap R C c := by
  have h1 : ∀ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • t) = algebraMap R C c := by
    intro a
    have : χ⁻¹ (a : F) * χ a = 1 := by
      rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply_coe]
    rw [hg, ← map_mul, mul_left_comm, this, mul_one]
  have h0 : (Fintype.card Fˣ : C) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [proj, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]

end

theorem a_nonunit_of (hproj : type_of% @GlobalTheory.T.stable_hopf_order_fundamental_character) (hstep : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_translation)
    (hom : type_of% @GlobalTheory.T.fundamental_ideal_frobenius_product) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) := by
  intro p hp C _ _ _ v R _ _ hv hp1 F _ _ _ _ f hF N _ _ _ _ AA hst K t ht hgen τ hτ c' c hc' hc hlt
  obtain ⟨⟨S, hS, hSst⟩, -⟩ := hstep p C v R hv hp1 F f hF N AA hst K t ht
  have hprin := GlobalTheory.T.character_ideal_principal_eigen p C v R hv hp1 F f hF S hSst
  choose cc hcc0 hcc using fun χ => (hprin χ).1
  have hcm : c ∈ idealX AA.carrier K t (τ ^ p) := by rw [hc]; exact Ideal.mem_span_singleton_self c
  obtain ⟨g₀, hg₀, e₀⟩ := hcm
  have e1 : ∀ a : F, g₀ (a • t) = algebraMap R C (c * (τ ^ p) a) := fun a => by
    have := congrFun e₀ a
    simpa [LinearMap.funLeft_apply, Algebra.smul_def] using this
  have hmul : ∀ a ∈ invFun AA.carrier K.toAddSubgroup, ∀ b ∈ invFun AA.carrier K.toAddSubgroup,
      a * b ∈ invFun AA.carrier K.toAddSubgroup := fun a ha b hb =>
    ⟨AA.mul_mem a b ha.1 hb.1, fun x k hk => by
      rw [Pi.mul_apply, Pi.mul_apply, ha.2 x k hk, hb.2 x k hk]⟩
  obtain ⟨r, h, ⟨hh, hh0⟩, w, hw, e⟩ := adjoin_decomp p (M := invFun AA.carrier K.toAddSubgroup)
    ⟨AA.one_mem, fun _ _ _ => rfl⟩ hmul (fun a ha => AA.le_int ha.1) (hgen hg₀)
  have hw0 := (mem_aug.1 (sq_le_aug hmul hw)).2
  have hr : r • (1 : N → C) = 0 := by
    have h1 := congrFun e 0
    have h2 := e1 0
    rw [zero_smul, MulChar.map_zero, mul_zero, map_zero] at h2
    rw [h2, Pi.add_apply, Pi.add_apply, (mem_aug.1 hh0).2, hw0, add_zero, add_zero] at h1
    funext x
    exact h1.symm
  rw [hr, zero_add] at e
  have hwS : w ∘ LinearMap.toSpanSingleton F N t ∈ sqIdeal (augIdeal S.carrier) :=
    sq_pull _ (fun g hg => by rw [hS]; exact ⟨g, hg, rfl⟩) hw
  have hwS' := sq_le_aug (fun a ha b hb => S.mul_mem a b ha hb) hwS
  obtain ⟨w1, -, -, -, w5⟩ := hproj p C v R hv hp1 F f hF F S hSst τ hτ _ hwS'
  obtain ⟨ρ, -, hρ⟩ := ((hprin (τ ^ p)).2 _).1 (w1 (τ ^ p))
  have hρ1 := w5 hwS (τ ^ p)
  have hρ2 : ρ ∈ Ideal.span {cc (τ ^ p ^ 0) ^ p} := by
    refine ((hom p C v R hv hp1 F f hF S hSst τ hτ (fun n => cc (τ ^ p ^ n)) (fun n => hcc _)
      0).1 ρ).1 ?_
    rw [zero_add, pow_one, ← hρ]
    exact hρ1
  have hcc' : cc (τ ^ p ^ 0) ∈ Ideal.span {c'} := by
    rw [← hc', idealX, ← hS, pow_zero, pow_one, hcc]
    exact Ideal.mem_span_singleton_self _
  have hρ3 : v (algebraMap R C ρ) < v (algebraMap R C c) := by
    refine lt_of_le_of_lt ?_ hlt
    rw [← map_pow, ← map_pow]
    exact hv.le_of_dvd ((pow_dvd_pow_of_dvd (Ideal.mem_span_singleton.1 hcc') p).trans
      (Ideal.mem_span_singleton.1 hρ2))
  have hwt : proj (τ ^ p) w t = algebraMap R C ρ := by
    rw [← proj_line, hρ]
    simp
  have hht : proj (τ ^ p) h t = algebraMap R C (c - ρ) := by
    have := proj_self (τ ^ p) g₀ t c e1
    rw [e, proj_add, hwt] at this
    rw [map_sub, ← this, add_sub_cancel_right]
  obtain ⟨q1, -, q3, q4, -⟩ := hproj p C v R hv hp1 F f hF N AA hst τ hτ h
    (mem_aug.2 ⟨hh.1.1, (mem_aug.1 hh0).2⟩)
  have hD : c - ρ ∈ idealD p AA.carrier K t (τ ^ p) := by
    refine ⟨proj (τ ^ p) h, q3 ⟨hh.1.1, hh.2⟩ _, fun a x => ?_, fun k hk => ?_, ?_⟩
    · rw [(q1 (τ ^ p)).2 a x, sub_self]; exact Submodule.zero_mem _
    · have := (q4 K hh.1 (τ ^ p)).2 0 k hk
      rw [zero_add, eig_zero (q1 (τ ^ p))] at this
      rw [this]; exact Submodule.zero_mem _
    · rw [hht, sub_self]; exact Submodule.zero_mem _
  have hdvd : c - ρ ∣ c := by
    apply hv.dvd_of_le
    rw [map_sub, v.map_sub_eq_of_lt_left hρ3]
  exact Ideal.mem_of_dvd _ hdvd hD

end PositivityTheory.HtPt.Rd
