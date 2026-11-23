import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneEqSumPlaceIdempotentsOverTwoAddTwoMul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemModTwo

open GlobalTheory.SplitIdem

theorem split_alg {R : Type} [CommRing R] (c : R →+* R) (hcc : ∀ x, c (c x) = x) (e z A : R)
    (he : e * e = e) (hec : e * c e = 0) (hA : c A = A) (hz : e * z = A * e)
    (hp : (e + c e) * (z + c z) = e + c e) :
    (e + c e) * z = A * e + (1 - A) * c e ∧ e * (z * c z) = (A - A * A) * e := by
  have he' : c e * c e = c e := by rw [← map_mul, he]
  have hz' : c e * c z = A * c e := by rw [← map_mul, hz, map_mul, hA]
  have h1 : c e * (z + c z) = c e := by
    linear_combination c e * hp + (1 - (z + c z)) * he' + (1 - (z + c z)) * hec
  have h2 : e * (z + c z) = e := by
    linear_combination e * hp + (1 - (z + c z)) * he + (1 - (z + c z)) * hec
  exact ⟨by linear_combination hz + h1 - hz', by linear_combination (c z - A) * hz + A * h2⟩

theorem val_dichotomy {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (val : Valuation K Γ)
    (h2 : val 2 < 1) (h0 : (2 : K) ≠ 0) (a b : K) (hb : val b ≤ 1) (h : a - a * a = 2 * b) :
    ∃ g : K, val g ≤ 1 ∧ (a = 2 * g ∨ 1 - a = 2 * g) := by
  have key : ∀ x y : K, x + y = 1 → x * y = 2 * b → val y < 1 → ∃ g : K, val g ≤ 1 ∧ y = 2 * g := by
    intro x y hxy hm hy
    have hx : val x = 1 := by
      rw [show x = 1 - y by linear_combination hxy]
      exact val.map_one_sub_of_lt hy
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    refine ⟨b / x, by rw [map_div₀, hx, div_one]; exact hb, ?_⟩
    field_simp
    linear_combination hm
  have hlt : val a * val (1 - a) < 1 := by
    rw [← map_mul, show a * (1 - a) = 2 * b by linear_combination h, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hb) h2
  by_cases ha : val a < 1
  · obtain ⟨g, hg, e⟩ := key (1 - a) a (by ring) (by linear_combination h) ha
    exact ⟨g, hg, Or.inl e⟩
  · have ha' : val (1 - a) < 1 := by
      by_contra hn
      exact absurd hlt (not_lt.2 (one_le_mul (not_lt.1 ha) (not_lt.1 hn)))
    obtain ⟨g, hg, e⟩ := key a (1 - a) (by ring) (by linear_combination h) ha'
    exact ⟨g, hg, Or.inr e⟩

theorem tmul_algebraMap_eq {F A E : Type} [Field F] [CommRing A] [Algebra F A] [CommRing E] [Algebra F E]
    (a : A) (t : F) : a ⊗ₜ[F] algebraMap F E t = algebraMap A (A ⊗[F] E) (algebraMap F A t * a) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
  rfl

theorem tmul_one_inj {F A E : Type} [Field F] [CommRing A] [Algebra F A] [Field E] [Algebra F E]
    {a b : A} (h : a ⊗ₜ[F] (1 : E) = b ⊗ₜ[F] (1 : E)) : a = b :=
  Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (algebraMap F E).injective h

variable (D : D7)

def fj : Af D.host.F →ₙ+* Formalism.L2.Theta.AE D where
  toFun α := pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)
  map_zero' := TensorProduct.zero_tmul _ _
  map_add' x y := by
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero _).symm rfl
  map_mul' x y := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    exact Prod.ext (mul_zero _).symm rfl

theorem fj_eq (α : Af D.host.F) :
    fj D α = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α) := rfl

theorem fj_inj {α β : Af D.host.F} (h : fj D α = fj D β) : α = β :=
  congrArg Prod.snd (tmul_one_inj (a := pairA D.host.F 0 α) (b := pairA D.host.F 0 β) h)

theorem cA_tmul (a : AF D.host.F) (x : D.host.E) :
    cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] star x := rfl

theorem cA_invol (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x => rw [cA_tmul, cA_tmul, star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cA_fj (α : Af D.host.F) : cA D (fj D α) = fj D α := by
  show cA D (_ ⊗ₜ _) = _
  rw [cA_tmul, star_one]; rfl

theorem exists_of_star_eq {x : D.host.E} (h : star x = x) : ∃ t : D.host.F, algebraMap D.host.F D.host.E t = x := by
  haveI := D.host.isCMField_hostE
  exact ⟨⟨x, (IsCMField.complexConj_eq_self_iff D.host.E x).1 h⟩, rfl⟩

theorem exists_add_cA (z : Formalism.L2.Theta.AE D) :
    ∃ y, z + cA D z = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) y := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero, add_zero]⟩
  | tmul a x =>
    obtain ⟨t, ht⟩ := exists_of_star_eq D (x := x + star x) (by rw [star_add, star_star, add_comm])
    exact ⟨_, by rw [cA_tmul, ← TensorProduct.tmul_add, ← ht, tmul_algebraMap_eq]⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [RingHom.map_add, RingHom.map_add, ← ha, ← hb]; ring⟩

theorem singleV_mul (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Fv D.host.F v) (α : Af D.host.F) :
    α * singleV D.host.F v y = singleV D.host.F v (evalV D.host.F v α * y) := af_ext _ fun w => by
  by_cases hw : w = v
  · subst hw; simp only [map_mul, evalV_singleV_same]
  · simp only [map_mul, evalV_singleV_ne _ v _ hw, mul_zero]

theorem singleV_sub (v : HeightOneSpectrum (𝓞 D.host.F)) (x y : Fv D.host.F v) :
    singleV D.host.F v (x - y) = singleV D.host.F v x - singleV D.host.F v y := af_ext _ fun w => by
  by_cases hw : w = v
  · subst hw; simp only [map_sub, evalV_singleV_same]
  · simp only [map_sub, evalV_singleV_ne _ v _ hw, sub_zero]

theorem algebraMap_mul_fj (y : AF D.host.F) (α : Af D.host.F) :
    algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) y * fj D α = fj D (y.2 * α) := by
  rw [fj_eq, fj_eq, ← map_mul]
  congr 1
  exact Prod.ext (mul_zero _) rfl

abbrev pl (v : HeightOneSpectrum (𝓞 D.host.F)) : Formalism.L2.Theta.AE D := fj D (singleV D.host.F v 1)

def SplitAt (v : HeightOneSpectrum (𝓞 D.host.F)) (e : Formalism.L2.Theta.AE D) : Prop :=
  e * e = e ∧ e * cA D e = 0 ∧ e + cA D e = pl D v

variable {D}

theorem isSplitIdem_iff (e : Formalism.L2.Theta.AE D) : IsSplitIdem D e ↔ ∃ v, SplitAt D v e := by
  constructor
  · rintro ⟨h1, h2, v, _, ⟨α, rfl, h3, h4⟩, h5⟩
    have : α = singleV D.host.F v 1 := af_ext _ fun w => by
      by_cases hw : w = v
      · subst hw; rw [h3, evalV_singleV_same]
      · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
    subst this
    exact ⟨v, h1, h2, h5⟩
  · rintro ⟨v, h1, h2, h3⟩
    exact ⟨h1, h2, v, _, ⟨_, rfl, evalV_singleV_same _ v 1, fun w hw => evalV_singleV_ne _ v _ hw⟩, h3⟩

theorem SplitAt.conj {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) : SplitAt D v (cA D e) :=
  ⟨by rw [← map_mul, he.1], by rw [cA_invol, mul_comm, he.2.1], by rw [cA_invol, add_comm, he.2.2]⟩

theorem SplitAt.pl_mul {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) : pl D v * e = e := by
  rw [← he.2.2, add_mul, he.1, mul_comm, he.2.1, add_zero]

theorem pl_mul_pl {v v' : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ v') : pl D v * pl D v' = 0 := by
  rw [← map_mul, singleV_mul, evalV_singleV_ne _ v _ h.symm, zero_mul, ← sub_self (0 : Fv D.host.F v'),
    singleV_sub, sub_self, map_zero]

theorem SplitAt.orth {v v'} {e e' : Formalism.L2.Theta.AE D} (he : SplitAt D v e) (he' : SplitAt D v' e') (h : v ≠ v') :
    e * e' = 0 := by
  rw [← he.pl_mul, ← he'.pl_mul, mul_mul_mul_comm, pl_mul_pl h, zero_mul]

theorem SplitAt.exists_scalar {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) (z : Formalism.L2.Theta.AE D) :
    ∃ a : Fv D.host.F v, e * z = fj D (singleV D.host.F v a) * e := by
  obtain ⟨y, hy⟩ := exists_add_cA D (e * z)
  refine ⟨evalV D.host.F v y.2 * 1, ?_⟩
  rw [← singleV_mul, ← algebraMap_mul_fj, mul_assoc, he.pl_mul, ← hy, map_mul]
  linear_combination (-z) * he.1 - cA D z * he.2.1

theorem SplitAt.scalar_inj {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) {α β : Af D.host.F}
    (h : fj D α * e = fj D β * e) : evalV D.host.F v α = evalV D.host.F v β := by
  have h' := congrArg (cA D) h
  rw [map_mul, map_mul, cA_fj, cA_fj] at h'
  have h2 : fj D α * pl D v = fj D β * pl D v := by
    rw [← he.2.2, mul_add, mul_add, h, h']
  rw [← map_mul, ← map_mul] at h2
  have h3 := congrArg (evalV D.host.F v) (fj_inj D h2)
  rwa [map_mul, map_mul, evalV_singleV_same, mul_one, mul_one] at h3

theorem SplitAt.decomp {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) (z : Formalism.L2.Theta.AE D)
    (hz : pl D v * (z + cA D z) = pl D v) (β : Af D.host.F) (hβ : e * (z * cA D z) = fj D β * e) :
    ∃ a : Fv D.host.F v, a - a * a = evalV D.host.F v β ∧
      pl D v * z = fj D (singleV D.host.F v a) * e + fj D (singleV D.host.F v (1 - a)) * cA D e := by
  obtain ⟨a, ha⟩ := he.exists_scalar z
  obtain ⟨h1, h2⟩ := split_alg (cA D) (cA_invol D) e z _ he.1 he.2.1 (cA_fj D _) ha (by rw [he.2.2, hz])
  refine ⟨a, ?_, ?_⟩
  · rw [hβ, ← map_mul, ← map_sub] at h2
    rw [he.scalar_inj h2, map_sub, map_mul, evalV_singleV_same]
  · rw [← he.2.2, h1, singleV_sub, map_sub, sub_mul, sub_mul, he.conj.pl_mul, one_mul]

theorem SplitAt.unique {v} {e e' : Formalism.L2.Theta.AE D} (he : SplitAt D v e) (he' : SplitAt D v e') :
    e' = e ∨ cA D e' = e := by
  obtain ⟨a, ha, h⟩ := he.decomp e' (by rw [mul_add, he'.pl_mul, he'.conj.pl_mul, he'.2.2]) 0
    (by rw [he'.2.1, map_zero, mul_zero, zero_mul])
  have h0 : singleV D.host.F v 0 = 0 := by
    rw [← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self]
  rw [map_zero, ← mul_one_sub, mul_eq_zero, sub_eq_zero] at ha
  rw [he'.pl_mul] at h
  rcases ha with rfl | rfl
  · right
    rw [h0, map_zero, zero_mul, zero_add, sub_zero, he.conj.pl_mul] at h
    rw [h, cA_invol]
  · left
    rwa [sub_self, h0, map_zero, zero_mul, add_zero, he.pl_mul] at h

variable (D) in

abbrev intL : AddSubgroup (Formalism.L2.Theta.AE D) :=
  AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E,
    z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}

theorem fj_mul_tmul (β α : Af D.host.F) (x : D.host.E) :
    fj D β * pairA D.host.F 0 α ⊗ₜ[D.host.F] x = pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] x := by
  show (_ ⊗ₜ _) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  exact Prod.ext (mul_zero _) rfl

theorem fj_mul_mem {β : Af D.host.F} (hβ : β ∈ intAf D.host.F) {z : Formalism.L2.Theta.AE D} (hz : z ∈ intL D) :
    fj D β * z ∈ intL D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, o, fj_mul_tmul β α _⟩
    rw [map_mul]
    exact mul_mem (hβ v) (hα v)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

variable (D) in

def inF : Af D.host.F ⊗[D.host.F] D.host.E →+ Formalism.L2.Theta.AE D :=
  (LinearMap.rTensor D.host.E (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F))).toAddMonoidHom

theorem inF_tmul (α : Af D.host.F) (x : D.host.E) :
    inF D (α ⊗ₜ[D.host.F] x) = pairA D.host.F 0 α ⊗ₜ[D.host.F] x := rfl

theorem inF_finPart (z : Formalism.L2.Theta.AE D) : inF D (finPart D z) = fj D 1 * z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, AddMonoidHom.map_zero, mul_zero]
  | tmul a x =>
    show pairA D.host.F 0 a.2 ⊗ₜ[D.host.F] x = (_ ⊗ₜ _) * _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    exact Prod.ext (zero_mul _).symm (one_mul _).symm
  | add x y hx hy => rw [RingHom.map_add, AddMonoidHom.map_add, hx, hy, mul_add]

theorem inF_mem {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) : inF D z ∈ intL D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩
  | zero => rw [AddMonoidHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [AddMonoidHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [AddMonoidHom.map_neg]; exact neg_mem hx

theorem SplitAt.one_mul' {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) : fj D 1 * e = e := by
  rw [← he.pl_mul, ← mul_assoc, ← map_mul, one_mul]

theorem SplitAt.mem {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) : e ∈ intL D := by
  rw [← he.one_mul', ← inF_finPart]
  exact inF_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1]))

theorem val_two_lt (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (hv : (2 : 𝓞 F) ∈ v.asIdeal) (t : F) (ht : IsIntegral ℤ t) (a : Fv F v)
    (ha : a - a * a = evalV F v (algebraMap F (Af F) (2 * t))) :
    ∃ g : v.adicCompletionIntegers F, a = 2 * (g : Fv F v) ∨ 1 - a = 2 * (g : Fv F v) := by
  rw [AlgHom.commutes, RingHom.map_mul, map_ofNat] at ha
  have hv2 : Valued.v (2 : Fv F v) < 1 := by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]
    have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)) = v.valuation F (2 : F) :=
      v.valuedAdicCompletion_eq_valuation' _
    rw [h2, ← map_ofNat (algebraMap (𝓞 F) F) 2]
    exact (v.valuation_lt_one_iff_mem _).2 hv
  have hvt : Valued.v (algebraMap F (Fv F v) t) ≤ 1 := by
    have h2 : Valued.v (algebraMap F (Fv F v) t) = v.valuation F t :=
      v.valuedAdicCompletion_eq_valuation' _
    rw [h2]
    exact v.valuation_le_one (K := F) (⟨t, ht⟩ : 𝓞 F)
  have h20 : (2 : Fv F v) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]
    exact (_root_.map_ne_zero _).2 two_ne_zero
  obtain ⟨g, hg, hga⟩ := val_dichotomy Valued.v hv2 h20 a _ hvt ha
  exact ⟨⟨g, hg⟩, hga⟩

theorem exists_local (W : Formalism.L2.Theta.AE D) (h1 : W + cA D W = fj D 1) (t : D.host.F) (ht : IsIntegral ℤ t)
    (h2 : W * cA D W = fj D (algebraMap D.host.F (Af D.host.F) (2 * t)))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : (2 : 𝓞 D.host.F) ∈ v.asIdeal) :
    ∃ e, SplitAt D v e ∧ ∃ a ∈ intL D, pl D v * W - e = 2 * a := by
  obtain ⟨e, he1, he2, he3, -⟩ := exists_split_idempotent D v hv
  have he : SplitAt D v e := ⟨he1, he2, he3⟩
  obtain ⟨a, ha, h⟩ := he.decomp W (by rw [h1, ← map_mul, mul_one]) _ (by rw [h2, mul_comm])
  obtain ⟨⟨g, hg⟩, hga⟩ := val_two_lt D.host.F v hv t ht a ha
  have hgi : singleV D.host.F v g ∈ intAf D.host.F := singleV_mem_intAf D.host.F v ⟨g, hg⟩
  have h2g : fj D (singleV D.host.F v (2 * g)) = 2 * fj D (singleV D.host.F v g) := by
    rw [← map_ofNat (evalV D.host.F v) 2, ← singleV_mul, two_mul, two_mul, map_add]
  have h1g : fj D (singleV D.host.F v (1 - 2 * g)) = pl D v - 2 * fj D (singleV D.host.F v g) := by
    rw [singleV_sub, map_sub, h2g]
  rcases hga with rfl | hga
  · refine ⟨cA D e, he.conj, _, fj_mul_mem hgi (sub_mem he.mem he.conj.mem), ?_⟩
    linear_combination h + e * h2g + cA D e * h1g + he.conj.pl_mul
  · obtain rfl : a = 1 - 2 * g := by rw [← hga]; ring
    refine ⟨e, he, _, fj_mul_mem hgi (sub_mem he.conj.mem he.mem), ?_⟩
    rw [sub_sub_cancel] at h
    linear_combination h + cA D e * h2g + e * h1g + he.pl_mul

set_option maxHeartbeats 800000 in
theorem exists_global (W : Formalism.L2.Theta.AE D) (hW : W ∈ intL D) (h3 : fj D 1 * W = W) (h1 : W + cA D W = fj D 1)
    (t : D.host.F) (ht : IsIntegral ℤ t) (h2 : W * cA D W = fj D (algebraMap D.host.F (Af D.host.F) (2 * t))) :
    ∃ s : Finset (Formalism.L2.Theta.AE D),
      (∀ e ∈ s, IsSplitIdem D e ∧ ∀ e' ∈ s, e ≠ e' → e * e' = 0 ∧ e * cA D e' = 0) ∧
      (∃ a ∈ intL D, W - ∑ e ∈ s, e = 2 * a) ∧ (∃ a ∈ intL D, fj D 1 - ∑ e ∈ s, (e + cA D e) = 2 * a) ∧
      ∀ e, IsSplitIdem D e → e ∈ intL D ∧ (e ∈ s ∨ cA D e ∈ s ∨ ∃ a ∈ intL D, e = 2 * a) := by
  obtain ⟨P, hP, -, β, hβ, hone⟩ := GlobalTheory.LatVac.one_eq_sum_singleV_add_two_mul D.host.F
  have hloc : ∀ v, ∃ e : Formalism.L2.Theta.AE D, ∃ a : Formalism.L2.Theta.AE D, v ∈ P → SplitAt D v e ∧ a ∈ intL D ∧
      pl D v * W - e = 2 * a := fun v => by
    by_cases hv : v ∈ P
    · obtain ⟨e, he, a, ha, h⟩ := exists_local W h1 t ht h2 v (hP v hv)
      exact ⟨e, a, fun _ => ⟨he, ha, h⟩⟩
    · exact ⟨0, 0, fun h => absurd h hv⟩
  choose f g hfg using hloc
  have hinj : ∀ v ∈ P, ∀ v' ∈ P, f v = f v' → v = v' := fun v hv v' hv' h => by
    by_contra hne
    have h3 : pl D v = pl D v' := by rw [← (hfg v hv).1.2.2, ← (hfg v' hv').1.2.2, h]
    have h4 := congrArg (evalV D.host.F v) (fj_inj D h3)
    rw [evalV_singleV_same, evalV_singleV_ne _ v' _ hne] at h4
    exact one_ne_zero h4
  have hone' : fj D 1 = ∑ v ∈ P, pl D v + 2 * fj D β := by
    rw [hone, map_add, map_sum, two_mul, two_mul, map_add]
  have h1L : fj D 1 ∈ intL D :=
    AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, 1, rfl⟩
  refine ⟨P.image f, fun e he => ?_, ⟨∑ v ∈ P, g v + fj D β * W,
    add_mem (sum_mem fun v hv => (hfg v hv).2.1) (fj_mul_mem hβ hW), ?_⟩,
    ⟨fj D β * fj D 1, fj_mul_mem hβ h1L, ?_⟩, fun e he => ?_⟩
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
    refine ⟨(isSplitIdem_iff _).2 ⟨v, (hfg v hv).1⟩, fun e' he' hne => ?_⟩
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.1 he'
    have hvv : v ≠ v' := fun h => hne (by rw [h])
    exact ⟨(hfg v hv).1.orth (hfg v' hv').1 hvv, (hfg v hv).1.orth (hfg v' hv').1.conj hvv⟩
  · have h4 : ∑ v ∈ P, (pl D v * W - f v) = ∑ v ∈ P, 2 * g v :=
      Finset.sum_congr rfl fun v hv => (hfg v hv).2.2
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at h4
    rw [Finset.sum_image hinj]
    linear_combination h4 - h3 + W * hone'
  · rw [Finset.sum_image hinj, Finset.sum_congr rfl fun v hv => (hfg v hv).1.2.2, ← map_mul, mul_one]
    exact sub_eq_of_eq_add' hone'
  · obtain ⟨v, hv⟩ := (isSplitIdem_iff _).1 he
    refine ⟨hv.mem, ?_⟩
    by_cases hvP : v ∈ P
    · rcases (hfg v hvP).1.unique hv with h | h
      · exact Or.inl (Finset.mem_image.2 ⟨v, hvP, h.symm⟩)
      · exact Or.inr (Or.inl (Finset.mem_image.2 ⟨v, hvP, h.symm⟩))
    · refine Or.inr (Or.inr ⟨fj D β * e, fj_mul_mem hβ hv.mem, ?_⟩)
      have h5 : ∑ v' ∈ P, pl D v' * e = 0 := Finset.sum_eq_zero fun v' hv' => by
        have hne : v' ≠ v := fun h => hvP (by rw [← h]; exact hv')
        linear_combination e * pl_mul_pl (D := D) hne - pl D v' * hv.pl_mul
      rw [← Finset.sum_mul] at h5
      linear_combination h5 - hv.one_mul' + e * hone'

theorem tmul_mul_cA (w : D.host.E) (t : D.host.F) (h : w * star w = algebraMap D.host.F D.host.E t) :
    (pairA D.host.F 0 1 ⊗ₜ[D.host.F] w : Formalism.L2.Theta.AE D) * cA D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] w) =
      fj D (algebraMap D.host.F (Af D.host.F) t) := by
  rw [cA_tmul, Algebra.TensorProduct.tmul_mul_tmul, h, tmul_algebraMap_eq, fj_eq]
  congr 1
  exact Prod.ext (by show _ * ((0 : Ainf D.host.F) * 0) = 0; rw [mul_zero, mul_zero])
    (by show _ * ((1 : Af D.host.F) * 1) = _; rw [mul_one, mul_one]; rfl)

theorem exists_split_idempotents : ∀ (D : D7) (w : D.host.E), IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∃ s : Finset (Formalism.L2.Theta.AE D), (∀ e ∈ s, IsSplitIdem D e ∧ ∀ e' ∈ s, e ≠ e' → e * e' = 0 ∧ e * cA D e' = 0) ∧ (∃ a ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}, pairA D.host.F 0 1 ⊗ₜ[D.host.F] w - ∑ e ∈ s, e = 2 * a) ∧ (∃ a ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}, pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) - ∑ e ∈ s, (e + cA D e) = 2 * a) ∧ ∀ e, IsSplitIdem D e → e ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)} ∧ (e ∈ s ∨ cA D e ∈ s ∨ ∃ a ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}, e = 2 * a) := by
  intro D w hw h1 ⟨b, hb, h2⟩
  change w + star w = 1 at h1
  change w * star w = 2 * b at h2
  have hsb : star b = b := by
    have h3 := congrArg star h2
    rw [star_mul', star_star, mul_comm, h2, star_mul', star_ofNat] at h3
    exact (mul_left_cancel₀ two_ne_zero h3).symm
  obtain ⟨t, rfl⟩ := exists_of_star_eq D hsb
  have ht : IsIntegral ℤ t := (isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective).1 hb
  exact exists_global (pairA D.host.F 0 1 ⊗ₜ[D.host.F] w)
    (AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, ⟨w, hw⟩, rfl⟩)
    ((fj_mul_tmul (D := D) 1 1 w).trans (by rw [mul_one]))
    (by rw [cA_tmul, ← TensorProduct.tmul_add, h1]; rfl) t ht
    (tmul_mul_cA w (2 * t) (by rw [h2, RingHom.map_mul, map_ofNat]))

end GlobalTheory.IdemModTwo

end
