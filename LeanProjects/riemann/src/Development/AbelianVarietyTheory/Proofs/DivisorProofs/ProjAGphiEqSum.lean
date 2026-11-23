import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VacProj

theorem mem_vset {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (Λ : Formalism.L2.Pj.GenLat E n) (hU : Λ.Unimod) (hfg : Λ.La.FG) : Λ.La ∈ Vset E n 1 := by
  have hU' := (GenLatCmp.unimod_iff Λ.La).1 hU
  obtain ⟨N, hN, h⟩ := TensLat.exists_mul_le (B := stdL E n) (B' := Λ.La)
    (Submodule.fg_span (Set.finite_range _)) (DualFamily.span_eq_top Λ.La hfg fun x => (hU' x).2)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {N}))
  have h4 : ∀ u ∈ stdL E n, ((Ideal.absNorm (Ideal.span {N}) : ℕ) : E) • u ∈ Λ.La := fun u hu => by
    have e : ((Ideal.absNorm (Ideal.span {N}) : ℕ) : E) = (a : E) * (N : E) := by
      have := congrArg (algebraMap (𝓞 E) E) ha
      rw [map_mul, map_natCast] at this
      exact this.symm
    rw [e, mul_smul]
    exact TensLat.int_smul_mem a.isIntegral_coe (h u hu)
  refine ⟨hfg, hU', _, Nat.pos_of_ne_zero ?_, Nat.coprime_one_right _,
    GenLatCmp.smul_mem_std hU' h4, h4⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hN

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {w : E} {A A' : AddSubgroup (Matrix (Fin n) (Fin r) E)}

theorem heisG_sum {ι : Type} (y : Matrix (Fin n) (Fin r) E) (s : Finset ι) (f : ι → TF n g) :
    heisG X bas y (∑ i ∈ s, f i) = ∑ i ∈ s, heisG X bas y (f i) := by
  funext x; simp [heisG, heisS, Finset.sum_mul]

theorem rho_eq_iff (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : TensVac.Good X w A) (hA' : TensVac.Good X w A') {v : TF n g} (hv : IsVac X bas w A' v)
    {a b : Matrix (Fin n) (Fin r) E} (ha : a ∈ A) (hb : b ∈ A) :
    epsW X w a • heisG X bas a v = epsW X w b • heisG X bas b v ↔ -a + b ∈ A' := by
  have hfix : ∀ y, epsW X w y • heisG X bas y v = v ↔ y ∈ A' := by
    refine fun y => ⟨fun h => ?_, hv.2.2 y⟩
    by_contra hy
    have := hA'.ip_eq_zero idx hs hn hv hy
    rw [h, hv.2.1] at this
    exact one_ne_zero this
  rw [← hfix, ← hA.rho_rho idx hs hn (A.neg_mem ha) hb hv.1]
  constructor
  · intro h
    rw [← h, hA.rho_rho idx hs hn (A.neg_mem ha) ha hv.1, neg_add_cancel,
      TensVac.rho_zero idx hs hn hv.1]
  · intro h
    conv_lhs => rw [← h]
    rw [hA.rho_rho idx hs hn ha (A.neg_mem ha) (TensVac.rho_sb idx hs hn b hv.1), add_neg_cancel,
      TensVac.rho_zero idx hs hn (TensVac.rho_sb idx hs hn b hv.1)]

theorem proj_eq (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : TensVac.Good X w A) (hA' : TensVac.Good X w A') {v : TF n g} (hv : IsVac X bas w A' v)
    (R : Finset (Matrix (Fin n) (Fin r) E)) (hR : ∀ y ∈ R, y ∈ A)
    (hR' : ∀ y ∈ A, ∃! y', y' ∈ R ∧ y - y' ∈ A') :
    R.card = A'.relIndex A ∧
      projA X bas w A v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X w y • heisG X bas y v ∧
      IsVac X bas w A ((Real.sqrt (R.card : ℝ) : ℂ) • projA X bas w A v) := by
  set f : Matrix (Fin n) (Fin r) E → TF n g := fun y => epsW X w y • heisG X bas y v with hf
  have hiff : ∀ a ∈ A, ∀ b ∈ A, f a = f b ↔ -a + b ∈ A' := fun a ha b hb =>
    rho_eq_iff idx hs hn hA hA' hv ha hb
  have hinj : Set.InjOn f R := fun a ha b hb h => by
    have h1 := (hiff a (hR a ha) b (hR b hb)).1 h
    rw [neg_add_eq_sub] at h1
    exact (hR' b (hR b hb)).unique ⟨ha, h1⟩ ⟨hb, by rw [sub_self]; exact A'.zero_mem⟩
  have him : f '' A = f '' R := by
    refine Set.Subset.antisymm ?_ (Set.image_mono fun y hy => hR y hy)
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, ⟨hb, h⟩, -⟩ := hR' a ha
    exact ⟨b, hb, (hiff b (hR b hb) a ha).2 (by rwa [neg_add_eq_sub])⟩
  have hc : (f '' A).ncard = R.card := by
    rw [him, hinj.ncard_image, Set.ncard_coe_finset]
  have hidx : R.card = A'.relIndex A := hc.symm.trans (TensVac.ncard_image_eq f hiff)
  refine ⟨hidx, ?_, ?_⟩
  · have h1 : ∑ᶠ ψ ∈ f '' R, ψ = ∑ y ∈ R, f y :=
      (finsum_mem_image (f := fun ψ : TF n g => ψ) hinj).trans (finsum_mem_coe_finset _ _)
    rw [projA, ← hf, hc, him, h1]
  · obtain ⟨u, hu, -⟩ := hA.vac hs
    have hov := hA.overlap idx hs hn hA' hu hv
    rw [(hA.proj idx hs hn hv.1 hu).2, smul_smul]
    set a := (Real.sqrt (R.card : ℝ) : ℂ) * SW.ip v u with ha
    have hn1 : ‖a‖ ^ 2 = 1 := by
      rw [ha, TensVac.ip_conj hu.1 hv.1, norm_mul, Complex.norm_conj, Complex.norm_real, mul_pow,
        Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _), hidx, hov]
    refine ⟨TensVac.sb_smul a hu.1, ?_, fun y hy => ?_⟩
    · rw [TensVac.ip_smul_left a hu.1 (TensVac.sb_smul a hu.1), TensVac.ip_smul_right a hu.1 hu.1,
        hu.2.1, _root_.mul_one, Complex.mul_conj']
      exact_mod_cast hn1
    · rw [TensVac.heisG_smul, smul_comm, hu.2.2 y hy]

end

theorem projA_gphi_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ (w : E), IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ (Λ₀ Λ : Formalism.L2.Pj.GenLat E n), Λ₀.Unimod → Λ.Unimod → Λ₀.La.FG → Λ.La.FG → ∀ v : TF n g, IsVac X bas w (tens Λ₀.La L) v → ∀ R : Finset (Matrix (Fin n) (Fin r) E), (∀ y ∈ R, y ∈ tens Λ.La L) → (∀ y ∈ tens Λ.La L, ∃! y', y' ∈ R ∧ y - y' ∈ tens Λ₀.La L) → R.card = ((Λ.La ⊓ Λ₀.La).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ^ r ∧ projA X bas w (tens Λ.La L) v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X w y • heisG X bas y v ∧ IsVac X bas w (tens Λ.La L) ((Real.sqrt (R.card : ℝ) : ℂ) • projA X bas w (tens Λ.La L) v) ∧ ∀ (Q : Type) [Fintype Q] (c : Q → ℂ) (Y : Q → Matrix (Fin n) (Fin r) E), gphi X bas w Λ.La L v c Y = ((R.card : ℂ))⁻¹ • ∑ q, ∑ y ∈ R, (c q * epsW X w y) • heisG X bas (Y q) (heisG X bas y v) := by
  intro E _ _ _ r g n X bas idx hs hn w hw hw1 L hL Λ₀ Λ hU₀ hU hf₀ hf v hv R hR hR'
  have h₀ := mem_vset Λ₀ hU₀ hf₀
  have h₁ := mem_vset Λ hU hf
  obtain ⟨a1, a2, a3, -, -, a4⟩ :=
    TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw1 L hL 1 _ h₁
  obtain ⟨b1, b2, b3, -⟩ :=
    TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw1 L hL 1 _ h₀
  obtain ⟨c1, c2, c3⟩ := proj_eq idx hs hn ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ hv R hR hR'
  refine ⟨?_, c2, c3, fun Q _ c Y => ?_⟩
  · rw [c1, a4 _ h₀, ← AddSubgroup.inf_relIndex_left]
    rfl
  · rw [gphi, finsum_eq_sum_of_fintype, c2]
    refine Eq.trans ?_ Finset.smul_sum.symm
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [TensVac.heisG_smul, heisG_sum, smul_comm]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [TensVac.heisG_smul, smul_smul]

end GlobalTheory.AdTh.VacProj
