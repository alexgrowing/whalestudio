import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct nonZeroDivisors ComplexConjugate
open GlobalTheory.PairLift (adjO)

namespace GlobalTheory.LatExchPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev FI (D : D7) : Type := FractionalIdeal (𝓞 D.host.E)⁰ D.host.E

def StarLE (I J : FI D) : Prop := ∀ x ∈ I, star x ∈ J

theorem star_int (c : 𝓞 D.host.E) : ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = star (c : D.host.E) :=
  ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E) c, rfl⟩

theorem starLE_AA : StarLE (D := D) D.host.AA D.host.AAbar := fun x hx => by
  rw [bridge_star_holds D.R D.host x]; exact Formalism.L2.Pj.conj_mem_AAbar D hx

theorem starLE_AAbar : StarLE (D := D) D.host.AAbar D.host.AA := fun x hx => by
  rw [bridge_star_holds D.R D.host x]; exact Formalism.L2.Pj.conj_mem_AA D hx

theorem starLE_mul {I I' J J' : FI D} (h : StarLE I I') (h' : StarLE J J') : StarLE (I * J) (I' * J') := by
  intro x hx
  refine FractionalIdeal.mul_induction_on (C := fun x => star x ∈ I' * J') hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [star_mul']; exact FractionalIdeal.mul_mem_mul (h a ha) (h' b hb)
  · rw [star_add]
    exact Submodule.add_mem ((I' * J' : FI D) : Submodule (𝓞 D.host.E) D.host.E) ha hb

theorem starLE_one : StarLE (D := D) 1 1 := by
  intro x hx
  obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  obtain ⟨c', hc'⟩ := star_int c
  exact (FractionalIdeal.mem_one_iff _).2 ⟨c', hc'⟩

theorem starLE_pow {I J : FI D} (h : StarLE I J) (n : ℕ) : StarLE (I ^ n) (J ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using starLE_one
  | succ n ih => rw [pow_succ, pow_succ]; exact starLE_mul ih h

theorem starLE_inv {I J : FI D} (hI : I ≠ 0) (hJ : J ≠ 0) (h : StarLE J I) : StarLE I⁻¹ J⁻¹ := by
  intro x hx
  rw [FractionalIdeal.mem_inv_iff hJ]
  intro y hy
  rw [FractionalIdeal.mem_inv_iff hI] at hx
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 (hx (star y) (h y hy))
  obtain ⟨c', hc'⟩ := star_int c
  refine (FractionalIdeal.mem_one_iff _).2 ⟨c', ?_⟩
  have e1 : algebraMap (𝓞 D.host.E) D.host.E c' = (c' : D.host.E) := rfl
  have e2 : algebraMap (𝓞 D.host.E) D.host.E c = (c : D.host.E) := rfl
  rw [e2] at hc
  rw [e1, hc', hc, star_mul', star_star]

theorem AAbar_ne : D.host.AAbar ≠ 0 := by
  intro h
  have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  rw [h, mul_zero, zero_mul] at h1
  exact zero_ne_one h1

theorem AA_ne : D.host.AA ≠ 0 := Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D

theorem b_mul_c : (D.host.AAbar * D.host.AA⁻¹) * (D.host.AA * D.host.AAbar⁻¹) = (1 : FI D) := by
  rw [mul_mul_mul_comm, mul_comm D.host.AAbar, ← mul_inv, mul_inv_cancel₀ (mul_ne_zero AA_ne AAbar_ne)]

theorem starLE_b : StarLE (D := D) (D.host.AAbar * D.host.AA⁻¹) (D.host.AA * D.host.AAbar⁻¹) :=
  starLE_mul starLE_AAbar (starLE_inv AA_ne AAbar_ne starLE_AAbar)

theorem starLE_c : StarLE (D := D) (D.host.AA * D.host.AAbar⁻¹) (D.host.AAbar * D.host.AA⁻¹) :=
  starLE_mul starLE_AA (starLE_inv AAbar_ne AA_ne starLE_AA)

theorem AAbar_eq (i : ℕ) : D.host.AAbar =
    D.host.AA * (D.host.AAbar * D.host.AA⁻¹) ^ (i + 1) * (D.host.AA * D.host.AAbar⁻¹) ^ i := by
  have h : D.host.AA * (D.host.AAbar * D.host.AA⁻¹) ^ (i + 1) * (D.host.AA * D.host.AAbar⁻¹) ^ i =
      D.host.AA * (D.host.AAbar * D.host.AA⁻¹) * ((D.host.AAbar * D.host.AA⁻¹) * (D.host.AA * D.host.AAbar⁻¹)) ^ i := by ring
  rw [h, b_mul_c, one_pow, mul_one, mul_comm D.host.AAbar, ← mul_assoc, mul_inv_cancel₀ AA_ne, one_mul]

theorem AA_eq (i : ℕ) : D.host.AA =
    D.host.AAbar * (D.host.AAbar * D.host.AA⁻¹) ^ i * (D.host.AA * D.host.AAbar⁻¹) ^ (i + 1) := by
  have h : D.host.AAbar * (D.host.AAbar * D.host.AA⁻¹) ^ i * (D.host.AA * D.host.AAbar⁻¹) ^ (i + 1) =
      D.host.AAbar * (D.host.AA * D.host.AAbar⁻¹) * ((D.host.AAbar * D.host.AA⁻¹) * (D.host.AA * D.host.AAbar⁻¹)) ^ i := by ring
  rw [h, b_mul_c, one_pow, mul_one, mul_comm D.host.AA, ← mul_assoc, mul_inv_cancel₀ AAbar_ne, one_mul]

end GlobalTheory.LatExchPf

namespace GlobalTheory.LatExchPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def gen (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) : WO S T :=
  Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)

theorem gen_congr {S T : HSp D} (α : Af D.host.F) {a a' : D.host.E} {s s' : Fin S.rank → D.host.E} {t t' : Fin T.rank → D.host.E}
    (h : ∀ i j, a * t i * ∑ k, star (s k) * S.gram k j = a' * t' i * ∑ k, star (s' k) * S.gram k j) :
    gen S T α a s t = gen S T α a' s' t' := by
  ext i j
  simp only [gen, Matrix.of_apply, h]

theorem inv_gram_mul (S : HSp D) (i m : Fin S.rank) : ∑ k, S.gram⁻¹ i k * S.gram k m = if i = m then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)) i) m
  rwa [Matrix.mul_apply, Matrix.one_apply] at h

theorem adj_key (S T : HSp D) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (i : Fin T.rank)
    (j : Fin S.rank) :
    ∑ l, (∑ k, T.gram⁻¹ i k * star (a * s l * ∑ m, star (t m) * T.gram m k)) * S.gram l j =
      star a * t i * ∑ l, star (s l) * S.gram l j := by
  have h1 : ∀ l, ∑ k, T.gram⁻¹ i k * star (a * s l * ∑ m, star (t m) * T.gram m k) = star a * star (s l) * t i := by
    intro l
    have e : ∀ k, T.gram⁻¹ i k * star (a * s l * ∑ m, star (t m) * T.gram m k) =
        star a * star (s l) * ∑ m, t m * (T.gram⁻¹ i k * T.gram k m) := by
      intro k
      simp only [star_mul', star_sum, star_star, GlobalTheory.LatVac.gram_star, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    simp_rw [e]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, inv_gram_mul]
    simp
  simp_rw [h1]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem adjO_gen (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    adjO S T (gen T S α a t s) = gen S T α (star a) s t := by
  have hc : ∀ (p : AF D.host.F) (e : D.host.E), cA D (p ⊗ₜ[D.host.F] e) = p ⊗ₜ star e := fun _ _ => rfl
  have hi : ∀ e : D.host.E, incA D e = 1 ⊗ₜ e := fun _ => rfl
  ext i j
  rw [GlobalTheory.AdjLawPf.adjO_eq]
  simp only [gen, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, hc, hi,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← TensorProduct.tmul_sum]
  congr 1
  exact adj_key S T a s t i j

theorem gen_negSp (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin T.rank → D.host.E) (t : Fin S.rank → D.host.E) :
    (gen (negSp T) S α a s t : WO T S) = gen T S α (-a) s t := by
  have hg : (negSp T).gram = -T.gram := rfl
  ext i j
  simp only [gen, Matrix.of_apply, hg, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]
  congr 1
  ring

theorem gen_add_a {S T : HSp D} (α : Af D.host.F) (a a' : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    gen S T α (a + a') s t = gen S T α a s t + gen S T α a' s t := by
  ext i j
  simp only [gen, Matrix.of_apply, Matrix.add_apply, ← TensorProduct.tmul_add]
  congr 1
  ring

theorem adelicHomHermitianRankOneMap_add_source {S T : HSp D} (α : Af D.host.F) (a : D.host.E) (s s' : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    gen S T α a (s + s') t = gen S T α a s t + gen S T α a s' t := by
  ext i j
  simp only [gen, Matrix.of_apply, Matrix.add_apply, ← TensorProduct.tmul_add, Pi.add_apply, star_add, add_mul,
    Finset.sum_add_distrib]
  congr 1
  ring

theorem adelicHomHermitianRankOneMap_add_target {S T : HSp D} (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t t' : Fin T.rank → D.host.E) :
    gen S T α a s (t + t') = gen S T α a s t + gen S T α a s t' := by
  ext i j
  simp only [gen, Matrix.of_apply, Matrix.add_apply, ← TensorProduct.tmul_add, Pi.add_apply]
  congr 1
  ring

theorem adelicHomHermitianRankOneMap_zero_source {S T : HSp D} (α : Af D.host.F) (a : D.host.E) (t : Fin T.rank → D.host.E) :
    gen S T α a 0 t = 0 := by
  ext i j
  simp [gen]

theorem adelicHomHermitianRankOneMap_zero_target {S T : HSp D} (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) :
    gen S T α a s 0 = 0 := by
  ext i j
  simp [gen]

theorem adelicHomHermitianRankOneMap_smul_source {S T : HSp D} (α : Af D.host.F) (a c : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    gen S T α a (c • s) t = gen S T α (a * star c) s t :=
  gen_congr α fun i j => by
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc, ← Finset.mul_sum]
    ring

theorem adelicHomHermitianRankOneMap_smul_target {S T : HSp D} (α : Af D.host.F) (a c : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    gen S T α a s (c • t) = gen S T α (a * c) s t :=
  gen_congr α fun i j => by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.LatExchPf

namespace GlobalTheory.LatExchPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem fi_neg {I : FI D} {x : D.host.E} (hx : x ∈ I) : -x ∈ I :=
  Submodule.neg_mem (I : Submodule (𝓞 D.host.E) D.host.E) hx

theorem fi_mul_int {I : FI D} {x : D.host.E} (hx : x ∈ I) (c : 𝓞 D.host.E) : x * (c : D.host.E) ∈ I := by
  have h := Submodule.smul_mem (I : Submodule (𝓞 D.host.E) D.host.E) c hx
  rwa [Algebra.smul_def, mul_comm] at h

theorem fi_mul_star_int {I : FI D} {x : D.host.E} (hx : x ∈ I) (c : 𝓞 D.host.E) : x * star (c : D.host.E) ∈ I := by
  obtain ⟨c', hc'⟩ := star_int c
  rw [← hc']; exact fi_mul_int hx c'

theorem smul_int_eq {n : ℕ} (c : 𝓞 D.host.E) (v : Fin n → D.host.E) : c • v = (c : D.host.E) • v := by
  ext k; simp [Algebra.smul_def]

theorem gen_mem_right {V V' : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} (i : ℕ) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop)
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hαP : ∀ v, ¬ P v → evalV D.host.F v α = 0)
    {c : D.host.E} (hc : c ∈ D.host.AAbar) {t : Fin V.rank → D.host.E} (ht : t ∈ Λ) {s : Fin V'.rank → D.host.E} (hs : s ∈ Λ') :
    gen V V' α c t s ∈ latO V V' (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ : Set _)
      (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ (i + 1)) Λ' : Set _) P := by
  rw [AAbar_eq i] at hc
  refine FractionalIdeal.mul_induction_on (C := fun c => gen V V' α c t s ∈ latO V V' _ _ P) hc (fun x hx γ hγ => ?_)
    (fun x y hx hy => by rw [gen_add_a]; exact add_mem hx hy)
  refine FractionalIdeal.mul_induction_on (C := fun x => gen V V' α (x * γ) t s ∈ latO V V' _ _ P) hx (fun a ha β' hβ' => ?_)
    (fun x y hx hy => by rw [add_mul, gen_add_a]; exact add_mem hx hy)
  have hβ : star γ ∈ (D.host.AAbar * D.host.AA⁻¹) ^ i := starLE_pow starLE_c i γ hγ
  have e : gen V V' α (a * β' * γ) t s = gen V V' α a (star γ • t) (β' • s) := by
    rw [adelicHomHermitianRankOneMap_smul_source, adelicHomHermitianRankOneMap_smul_target, star_star]
    exact gen_congr α fun _ _ => by ring
  rw [e]
  exact AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, star γ • t, Submodule.subset_span ⟨star γ, hβ, t, ht, rfl⟩,
    β' • s, Submodule.subset_span ⟨β', hβ', s, hs, rfl⟩, rfl⟩

theorem gen_mem_left {V V' : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} (i : ℕ) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop)
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hαP : ∀ v, ¬ P v → evalV D.host.F v α = 0)
    {t : Fin V'.rank → D.host.E} (ht : t ∈ scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ (i + 1)) Λ') :
    ∀ e ∈ D.host.AAbar, ∀ s ∈ scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ,
      (gen V' V α e t s : WO (negSp V') V) ∈ latO (negSp V') V (Λ' : Set _) (Λ : Set _) P := by
  unfold scaleLat at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨β', hβ', x, hx, rfl⟩ := ht
    intro e he s hs
    unfold scaleLat at hs
    induction hs using Submodule.span_induction generalizing e with
    | mem s hs =>
      obtain ⟨β, hβ, y, hy, rfl⟩ := hs
      have hk : e * β * star β' ∈ D.host.AA := by
        rw [AA_eq i]
        exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mul_mem_mul he hβ) (starLE_pow starLE_b (i + 1) β' hβ')
      have eq : (gen V' V α e (β' • x) (β • y) : WO (negSp V') V) = gen (negSp V') V α (-(e * β * star β')) x y := by
        rw [gen_negSp, neg_neg, adelicHomHermitianRankOneMap_smul_source, adelicHomHermitianRankOneMap_smul_target]
        exact gen_congr α fun _ _ => by ring
      rw [eq]
      exact AddSubgroup.subset_closure ⟨α, hα, hαP, _, fi_neg hk, x, hx, y, hy, rfl⟩
    | zero => rw [adelicHomHermitianRankOneMap_zero_target]; exact zero_mem _
    | add s s' _ _ h h' => rw [adelicHomHermitianRankOneMap_add_target]; exact add_mem (h e he) (h' e he)
    | smul c s _ h =>
      rw [smul_int_eq, adelicHomHermitianRankOneMap_smul_target]
      exact h _ (fi_mul_int he c)
  | zero => intro e _ s _; rw [adelicHomHermitianRankOneMap_zero_source]; exact zero_mem _
  | add t t' _ _ h h' => intro e he s hs; rw [adelicHomHermitianRankOneMap_add_source]; exact add_mem (h e he s hs) (h' e he s hs)
  | smul c t _ h =>
    intro e he s hs
    rw [smul_int_eq, adelicHomHermitianRankOneMap_smul_source]
    exact h _ (fi_mul_star_int he c) s hs

end GlobalTheory.LatExchPf

namespace GlobalTheory.LatExchPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem adj_mem_right {V V' : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} (i : ℕ) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop)
    {x : WO (negSp V') V} (hx : x ∈ latO (negSp V') V (Λ' : Set _) (Λ : Set _) P) :
    adjO V V' x ∈ latO V V' (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ : Set _)
      (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ (i + 1)) Λ' : Set _) P := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩ := hw
    change adjO V V' (gen (negSp V') V α a s t) ∈ _
    rw [gen_negSp, adjO_gen]
    exact gen_mem_right i P hα hαP (by rw [star_neg]; exact fi_neg (starLE_AA a ha)) ht hs
  | zero =>
    change GlobalTheory.AdjLawPf.adjHom V V' 0 ∈ _
    rw [map_zero]; exact zero_mem _
  | add y y' _ _ h h' =>
    rw [GlobalTheory.AdjLawPf.adj_add]; exact add_mem h h'
  | neg y _ h =>
    change GlobalTheory.AdjLawPf.adjHom V V' (-y) ∈ _
    rw [map_neg]; exact neg_mem h

theorem adj_mem_left {V V' : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} (i : ℕ) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop)
    {y : WO V V'} (hy : y ∈ latO V V' (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ : Set _)
      (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ (i + 1)) Λ' : Set _) P) :
    (adjO V' V y : WO (negSp V') V) ∈ latO (negSp V') V (Λ' : Set _) (Λ : Set _) P := by
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩ := hw
    change adjO V' V (gen V V' α a s t) ∈ _
    rw [adjO_gen]
    exact gen_mem_left i P hα hαP ht _ (starLE_AA a ha) s hs
  | zero =>
    change GlobalTheory.AdjLawPf.adjHom V' V 0 ∈ _
    rw [map_zero]; exact zero_mem _
  | add y y' _ _ h h' =>
    rw [GlobalTheory.AdjLawPf.adj_add]; exact add_mem h h'
  | neg y _ h =>
    change GlobalTheory.AdjLawPf.adjHom V' V (-y) ∈ _
    rw [map_neg]; exact neg_mem h

theorem latExch : LatExch := by
  intro D _ T L μ0 _ sc G W M _ i _ r r' hr hr' P x
  have hr0 : GlobalTheory.AdelicU.frameLat r.sp = scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) (G.Λ (.core i)) := hr
  have hr1 : GlobalTheory.AdelicU.frameLat r'.sp = scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ (i + 1)) (G.Λ (.core (i + 1))) := hr'
  rw [hr0, hr1]
  constructor
  · intro hx
    exact adj_mem_right i P hx
  · intro hx
    have h := adj_mem_left (V := G.V (.core i)) (V' := G.V (.core (i + 1))) i P hx
    rwa [GlobalTheory.AdjLawPf.adj_invol] at h

end GlobalTheory.LatExchPf
