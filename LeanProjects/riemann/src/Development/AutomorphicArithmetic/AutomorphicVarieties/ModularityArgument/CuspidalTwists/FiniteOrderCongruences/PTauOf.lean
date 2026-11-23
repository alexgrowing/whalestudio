import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.TwistIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

namespace TauOf

section Alg

variable {Γ R : Type} [Group Γ] [CommRing R] (H : Subgroup Γ) (k : Γ → R) (u : R) (g0 : Γ)

theorem mat_eq {a b c d a' b' c' d' : R} (h1 : a = a') (h2 : b = b') (h3 : c = c') (h4 : d = d') :
    (!![a, b; c, d] : M2 R) = !![a', b'; c', d'] := by
  rw [h1, h2, h3, h4]

theorem ofTwo {u a b : R} (hu : 2 * u = 1) (h : a * (2 * u) = b) : a = b := by
  rw [hu, mul_one] at h
  exact h

def aa (x : Γ) : R := u * (k x + k x⁻¹)

def bb (x : Γ) : R := u * (k x - k x⁻¹)

def Nm (x : Γ) : M2 R := !![aa k u x, bb k u x; bb k u x, aa k u x]

open Classical in
def xg (g : Γ) : Γ := if g ∈ H then g else g * g0⁻¹

open Classical in
def sg (g : Γ) : R := if g ∈ H then 1 else -1

def tauF (g : Γ) : M2 R :=
  !![aa k u (xg H g0 g), (sg H g : R) * bb k u (xg H g0 g); bb k u (xg H g0 g), (sg H g : R) * aa k u (xg H g0 g)]

structure Hyp : Prop where
  hi : H.index = 2
  hu : 2 * u = 1
  one : k 1 = 1
  mul : ∀ x ∈ H, ∀ y ∈ H, k (x * y) = k x * k y
  conj : ∀ t ∉ H, ∀ x ∈ H, k (t * x * t⁻¹) = k x⁻¹
  sq : k (g0 * g0) = 1
  g0 : g0 ∉ H

variable {H k u g0}

theorem mem_conj (hy : Hyp H k u g0) (t : Γ) {x : Γ} (hx : x ∈ H) : t * x * t⁻¹ ∈ H := by
  rw [Subgroup.mul_mem_iff_of_index_two hy.hi, Subgroup.mul_mem_iff_of_index_two hy.hi, inv_mem_iff]
  simp [hx]

theorem xg_mem (hy : Hyp H k u g0) (g : Γ) : xg H g0 g ∈ H := by
  unfold xg
  split_ifs with hg
  · exact hg
  · rw [Subgroup.mul_mem_iff_of_index_two hy.hi, inv_mem_iff]
    exact iff_of_false hg hy.g0

theorem k_inv (hy : Hyp H k u g0) {x : Γ} (hx : x ∈ H) : k x * k x⁻¹ = 1 := by
  rw [← hy.mul x hx _ (inv_mem hx), mul_inv_cancel, hy.one]

theorem Nm_one_of (hy : Hyp H k u g0) {x : Γ} (h1 : k x = 1) (h2 : k x⁻¹ = 1) : (Nm k u x : M2 R) = 1 := by
  rw [Matrix.one_fin_two]
  simp only [Nm, aa, bb, h1, h2]
  refine mat_eq ?_ ?_ ?_ ?_ <;> first | ring1 | linear_combination hy.hu

theorem Nm_mul (hy : Hyp H k u g0) {x y : Γ} (hx : x ∈ H) (hy' : y ∈ H) : Nm k u (x * y) = Nm k u x * Nm k u y := by
  have e1 := hy.mul x hx y hy'
  have e2 : k (x * y)⁻¹ = k x⁻¹ * k y⁻¹ := by
    rw [mul_inv_rev, hy.mul _ (inv_mem hy') _ (inv_mem hx), mul_comm]
  simp only [Nm, aa, bb, e1, e2]
  rw [Matrix.mul_fin_two]
  refine mat_eq ?_ ?_ ?_ ?_ <;> exact ofTwo hy.hu (by ring)

theorem Nm_inv (x : Γ) : Nm k u x⁻¹ = !![(1 : R), 0; 0, -1] * Nm k u x * !![(1 : R), 0; 0, -1] := by
  simp only [Nm, aa, bb, inv_inv]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  refine mat_eq ?_ ?_ ?_ ?_ <;> ring

theorem Nm_conj (hy : Hyp H k u g0) {t x : Γ} (ht : t ∉ H) (hx : x ∈ H) : Nm k u (t * x * t⁻¹) = Nm k u x⁻¹ := by
  have a := hy.conj t ht x hx
  have b : k (t * x * t⁻¹)⁻¹ = k x := by
    rw [show (t * x * t⁻¹)⁻¹ = t * x⁻¹ * t⁻¹ by group, hy.conj t ht _ (inv_mem hx), inv_inv]
  simp only [Nm, aa, bb, a, b, inv_inv]

theorem JJ : (!![(1 : R), 0; 0, -1] * !![(1 : R), 0; 0, -1] : M2 R) = 1 := by
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  refine mat_eq ?_ ?_ ?_ ?_ <;> ring

theorem tauF_mem {g : Γ} (hg : g ∈ H) : tauF H k u g0 g = Nm k u g := by
  simp only [tauF, Nm, xg, sg, if_pos hg, one_mul]

theorem tauF_nmem {g : Γ} (hg : g ∉ H) : tauF H k u g0 g = Nm k u (g * g0⁻¹) * !![(1 : R), 0; 0, -1] := by
  simp only [tauF, Nm, xg, sg, if_neg hg]
  rw [Matrix.mul_fin_two]
  refine mat_eq ?_ ?_ ?_ ?_ <;> ring

def tau (hy : Hyp H k u g0) : Γ →* M2 R where
  toFun := tauF H k u g0
  map_one' := by
    show tauF H k u g0 1 = 1
    rw [tauF_mem (one_mem H)]
    exact Nm_one_of hy hy.one (by rw [inv_one, hy.one])
  map_mul' a b := by
    show tauF H k u g0 (a * b) = tauF H k u g0 a * tauF H k u g0 b
    have hm := fun a b : Γ => Subgroup.mul_mem_iff_of_index_two hy.hi (a := a) (b := b)
    have g0i : g0⁻¹ ∉ H := fun h => hy.g0 (by simpa using inv_mem h)
    by_cases ha : a ∈ H <;> by_cases hb : b ∈ H
    · rw [tauF_mem ((hm a b).2 (iff_of_true ha hb)), tauF_mem ha, tauF_mem hb, Nm_mul hy ha hb]
    · have hab : a * b ∉ H := fun h => hb (((hm a b).1 h).1 ha)
      have hbg : b * g0⁻¹ ∈ H := (hm _ _).2 (iff_of_false hb g0i)
      rw [tauF_nmem hab, tauF_mem ha, tauF_nmem hb, mul_assoc a b, Nm_mul hy ha hbg, mul_assoc]
    · have hab : a * b ∉ H := fun h => ha (((hm a b).1 h).2 hb)
      have hag : a * g0⁻¹ ∈ H := (hm _ _).2 (iff_of_false ha g0i)
      have e : a * b * g0⁻¹ = a * g0⁻¹ * (g0 * b * g0⁻¹) := by group
      rw [tauF_nmem hab, tauF_nmem ha, tauF_mem hb, e, Nm_mul hy hag (mem_conj hy g0 hb), Nm_conj hy hy.g0 hb, Nm_inv]
      simp only [mul_assoc, JJ, mul_one]
    · have hab : a * b ∈ H := (hm a b).2 (iff_of_false ha hb)
      have hag : a * g0⁻¹ ∈ H := (hm _ _).2 (iff_of_false ha g0i)
      have hbg : b * g0⁻¹ ∈ H := (hm _ _).2 (iff_of_false hb g0i)
      have hc := mem_conj hy g0 hbg
      have hsq : g0 * g0 ∈ H := Subgroup.mul_self_mem_of_index_two hy.hi g0
      have e : a * b = a * g0⁻¹ * (g0 * (b * g0⁻¹) * g0⁻¹) * (g0 * g0) := by group
      have h1 : Nm k u (g0 * g0) = 1 :=
        Nm_one_of hy hy.sq (by have := k_inv hy hsq; rwa [hy.sq, one_mul] at this)
      rw [tauF_mem hab, tauF_nmem ha, tauF_nmem hb, e, Nm_mul hy (H.mul_mem hag hc) hsq, Nm_mul hy hag hc,
        Nm_conj hy hy.g0 hbg, Nm_inv, h1]
      simp only [mul_assoc, mul_one]

theorem tau_apply (hy : Hyp H k u g0) (g : Γ) : tau hy g = tauF H k u g0 g := rfl

theorem form_of (a b s : R) (h1 : a * a - b * b = 1) (h2 : s * s = 1) :
    (!![a, s * b; b, s * a] : M2 R)ᵀ * !![1, 0; 0, -1] * !![a, s * b; b, s * a] = !![1, 0; 0, -1] := by
  have eT : (!![a, s * b; b, s * a] : M2 R)ᵀ = !![a, b; s * b, s * a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [eT, Matrix.mul_fin_two, Matrix.mul_fin_two]
  refine mat_eq ?_ ?_ ?_ ?_
  · linear_combination h1
  · ring
  · ring
  · linear_combination (-(s * s)) * h1 - h2

theorem form (hy : Hyp H k u g0) (g : Γ) :
    (tauF H k u g0 g)ᵀ * !![1, 0; 0, -1] * tauF H k u g0 g = !![1, 0; 0, -1] := by
  have hx := xg_mem hy g
  have hkk := k_inv hy hx
  have hab : aa k u (xg H g0 g) * aa k u (xg H g0 g) - bb k u (xg H g0 g) * bb k u (xg H g0 g) = 1 := by
    simp only [aa, bb]
    linear_combination (4 * u ^ 2) * hkk + (2 * u + 1) * hy.hu
  have hs : (sg H g : R) * sg H g = 1 := by
    unfold sg
    split_ifs <;> ring
  exact form_of _ _ _ hab hs

open Classical in
theorem cont_ite {X Y : Type} [Group X] [TopologicalSpace X] [TopologicalSpace Y] (H : Subgroup X)
    (hs : IsClopen (H : Set X)) {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => if x ∈ H then f x else g x := by
  refine Continuous.if (fun a ha => ?_) hf hg
  have e : frontier {x | x ∈ H} = ∅ := hs.frontier_eq
  rw [e] at ha
  simp at ha

end Alg

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem two_unit (c : Coef l) (hl : l ≠ 2) : IsUnit (2 : c.O) := by
  by_contra h
  have h2 : (2 : c.O) ∈ maximalIdeal c.O := (mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)
  have hlm : (l : c.O) ∈ maximalIdeal c.O := by
    rw [(UpperTheory.V.Fr.sc_norm l c _).2]
    have e : ((l : c.O) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [e, norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨j, hj⟩ := (Fact.out : l.Prime).odd_of_ne_two hl
  have h1 : (1 : c.O) ∈ maximalIdeal c.O := by
    have e0 : ((l : ℕ) : c.O) = ((2 * j + 1 : ℕ) : c.O) := congrArg (Nat.cast : ℕ → c.O) hj
    push_cast at e0
    have e : (1 : c.O) = 2 * ((j : c.O) + 1) - l := by
      rw [e0]
      ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h2) hlm
  exact (maximalIdeal.isMaximal c.O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem res_inj (K' : IntermediateField ℚ Ω) : Function.Injective (resQ K') := fun a b h =>
  AlgEquiv.ext fun x => DFunLike.congr_fun h x

theorem setup (K' : IntermediateField ℚ Ω) [NumberField K'] (hK : Module.finrank ℚ K' = 2) :
    (∀ g, g ∈ K'.fixingSubgroup ↔ ∃ x, resQ K' x = g) ∧ K'.fixingSubgroup.index = 2 ∧
      Topology.IsEmbedding (resQ K') ∧ IsOpen (K'.fixingSubgroup : Set (G ℚ Ω)) := by
  haveI : FaithfulSMul K' Ω := (faithfulSMul_iff_algebraMap_injective K' Ω).2 (algebraMap K' Ω).injective
  haveI : Module.IsTorsionFree K' Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  obtain ⟨hemb, hopen, hidx⟩ := galEmbTop ℚ K' Ω
  have hfix : galOf ℚ K' Ω = K'.fixingSubgroup := by
    ext σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.2⟩
  refine ⟨fun g => ?_, ?_, hemb, ?_⟩
  · rw [← hfix, ← range_galEmb]
    exact MonoidHom.mem_range
  · rw [← hfix]
    exact hidx.trans hK
  · rw [← hfix]
    exact hopen

theorem chi_coe (c : Coef l) (g : G ℚ Ω) (m : ℕ) :
    (((chiO ℚ Ω l c.O g ^ m : c.Oˣ) : c.O) : Qbar l) = ((cycBar ℚ Ω l g ^ m : (Qbar l)ˣ) : Qbar l) := by
  rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
  rfl

theorem exists_ine (A : ValuationSubring Ω) (hv : A.valuation (l : Ω) < 1) {n : ℤ} (hn : n ≠ 0) :
    ∃ g ∈ Ine (F := ℚ) A, cycBar ℚ Ω l g ^ n ≠ 1 := by
  obtain ⟨v, hv'⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv v
  refine ⟨σ, hσ, fun h => hv' n hn ?_⟩
  have hinj : Function.Injective
      (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) :=
    Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
  apply hinj
  rw [map_one, ← h, cycBar, MonoidHom.comp_apply, hσu, map_zpow]

section Kap

variable (K' : IntermediateField ℚ Ω) (κ : G K' Ω →* (Qbar l)ˣ) (c : Coef l) (hc : ∀ h, (κ h : Qbar l) ∈ c.O)

def kO (g : G ℚ Ω) : c.O :=
  @dite _ (∃ x, resQ K' x = g) (Classical.propDecidable _) (fun h => ⟨κ h.choose, hc _⟩) (fun _ => 1)

theorem kO_res (x : G K' Ω) : ((kO K' κ c hc (resQ K' x) : c.O) : Qbar l) = κ x := by
  have h : ∃ y, resQ K' y = resQ K' x := ⟨x, rfl⟩
  unfold kO
  rw [dif_pos h]
  show (κ h.choose : Qbar l) = κ x
  rw [res_inj K' h.choose_spec]

theorem kO_off (g : G ℚ Ω) (hg : ¬ ∃ x, resQ K' x = g) : kO K' κ c hc g = 1 := by
  unfold kO
  rw [dif_neg hg]

def PP (e : ℤ) (A : ValuationSubring Ω) : Prop :=
  ∀ h : G K' Ω, resQ K' h ∈ Ine (F := ℚ) A → κ h = cycBar K' Ω l h ^ e

open Classical in

def sA (m : ℕ) (A : ValuationSubring Ω) : c.O := if PP K' κ (m : ℤ) A then 1 else -1

end Kap

theorem excl (K' : IntermediateField ℚ Ω) (hH : ∀ g, g ∈ K'.fixingSubgroup ↔ ∃ x, resQ K' x = g)
    (hDec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K'.fixingSubgroup)
    (κ : G K' Ω →* (Qbar l)ˣ) (m : ℕ) (hm : 1 ≤ m) (B : ValuationSubring Ω) (hB : B.valuation (l : Ω) < 1) :
    ¬ (PP K' κ (m : ℤ) B ∧ PP K' κ (-(m : ℤ)) B) := by
  rintro ⟨h1, h2⟩
  obtain ⟨σ, hσ, hne⟩ := exists_ine B hB (n := 2 * (m : ℤ)) (by omega)
  obtain ⟨y, rfl⟩ := (hH σ).1 (hDec B hB (Ine_le_Dec (F := ℚ) B hσ))
  apply hne
  have e : cycBar K' Ω l y ^ (m : ℤ) = cycBar K' Ω l y ^ (-(m : ℤ)) := (h1 y hσ).symm.trans (h2 y hσ)
  have e3 : cycBar K' Ω l y ^ (m : ℤ) * cycBar K' Ω l y ^ (m : ℤ) = 1 := by
    calc _ = cycBar K' Ω l y ^ (m : ℤ) * cycBar K' Ω l y ^ (-(m : ℤ)) := by rw [← e]
      _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
  show cycBar K' Ω l y ^ (2 * (m : ℤ)) = 1
  rw [two_mul, zpow_add]
  exact e3

theorem conj_comm {M : Type} [CommGroup M] (a b : M) : a⁻¹ * b * a = b := by
  rw [mul_comm a⁻¹, inv_mul_cancel_right]

end TauOf

open TauOf in
theorem tauOf : TauOf := by
  intro Ω _ _ _ l _ ι K' _ hl hK hDec g0 hg0 m κ hκ c₂ hc
  obtain ⟨hH, hi, hemb, hopen⟩ := setup K' hK
  obtain ⟨k, kres, kred⟩ : ∃ k : G ℚ Ω → c₂.O, (∀ x, ((k (resQ K' x) : c₂.O) : Qbar l) = κ x) ∧
      (∀ g, (∀ x, resQ K' x ≠ g) → k g = 1) :=
    ⟨kO K' κ c₂ hc, kO_res K' κ c₂ hc, fun g hg => kO_off K' κ c₂ hc g (fun ⟨x, hx⟩ => hg x hx)⟩
  obtain ⟨u, hu⟩ : ∃ u : c₂.O, 2 * u = 1 := ⟨(((two_unit c₂ hl).unit⁻¹ : c₂.Oˣ) : c₂.O), (two_unit c₂ hl).mul_val_inv⟩
  have kH : ∀ x : G K' Ω, resQ K' x ∈ K'.fixingSubgroup := fun x => (hH _).2 ⟨x, rfl⟩
  have kone : k 1 = 1 := Subtype.ext (by rw [← map_one (resQ K'), kres, map_one]; rfl)
  have kmul : ∀ x ∈ K'.fixingSubgroup, ∀ y ∈ K'.fixingSubgroup, k (x * y) = k x * k y := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (hH x).1 hx
    obtain ⟨b, rfl⟩ := (hH y).1 hy
    rw [← map_mul]
    apply Subtype.ext
    rw [MulMemClass.coe_mul, kres, kres, kres, map_mul, Units.val_mul]
  have kconj : ∀ t ∉ K'.fixingSubgroup, ∀ x ∈ K'.fixingSubgroup, k (t * x * t⁻¹) = k x⁻¹ := by
    intro t ht x hx
    obtain ⟨a, rfl⟩ := (hH x).1 hx
    have hm : t * resQ K' a * t⁻¹ ∈ K'.fixingSubgroup := by
      rw [Subgroup.mul_mem_iff_of_index_two hi, Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff]
      exact ⟨fun h => h.2 (kH a), fun h => iff_of_true h (kH a)⟩
    obtain ⟨b, hb⟩ := (hH _).1 hm
    have h1 := hκ.anti t ht a b hb
    rw [← hb, ← map_inv (resQ K') a]
    apply Subtype.ext
    rw [kres, kres, map_inv, eq_inv_of_mul_eq_one_right h1]
  have ksq : k (g0 * g0) = 1 := by
    obtain ⟨a, ha⟩ := (hH _).1 (Subgroup.mul_self_mem_of_index_two hi g0)
    rw [← ha]
    apply Subtype.ext
    rw [kres, hκ.ver g0 hg0 a ha]
    rfl
  have hy : Hyp K'.fixingSubgroup k u g0 := ⟨hi, hu, kone, kmul, kconj, ksq, hg0⟩
  have kmax : ∀ g, k g - 1 ∈ maximalIdeal c₂.O := by
    intro g
    rcases em (∃ x, resQ K' x = g) with h | h
    · obtain ⟨x, rfl⟩ := h
      rw [(UpperTheory.V.Fr.sc_norm l c₂ _).2, AddSubgroupClass.coe_sub, kres]
      have := hκ.red x
      simpa [Cong] using this
    · rw [kred g (fun x hx => h ⟨x, hx⟩), sub_self]
      exact zero_mem _
  refine ⟨tau hy, sA K' κ c₂ m, hκ.pos, ?_, fun g => form hy g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hκ.cont, hκ.alg⟩
  ·
    intro i j
    apply ((UpperTheory.integrality_of_norm_coefficients l).2 c₂ (G ℚ Ω) _).2
    have hcl : IsClopen (K'.fixingSubgroup : Set (G ℚ Ω)) := ⟨Subgroup.isClosed_of_isOpen _ hopen, hopen⟩
    have hK : Continuous fun g => ((k g : c₂.O) : Qbar l) := by
      rw [continuous_iff_continuousAt]
      intro g
      rcases em (∃ x, resQ K' x = g) with h | h
      · obtain ⟨x, rfl⟩ := h
        have hr : Set.range (resQ K') ∈ nhds (resQ K' x) := by
          have e : Set.range (resQ K') = (K'.fixingSubgroup : Set (G ℚ Ω)) := Set.ext fun g => (hH g).symm
          rw [e]
          exact hopen.mem_nhds (kH x)
        rw [← hemb.toIsInducing.continuousAt_iff' hr]
        have e : (fun g => ((k g : c₂.O) : Qbar l)) ∘ resQ K' = fun x => (κ x : Qbar l) := funext fun x => kres x
        rw [e]
        exact (Units.continuous_val.comp hκ.cont).continuousAt
      · have hc' : (K'.fixingSubgroup : Set (G ℚ Ω))ᶜ ∈ nhds g :=
          hcl.isClosed.isOpen_compl.mem_nhds (fun hg => h ((hH g).1 hg))
        refine (continuousAt_const (y := (1 : Qbar l))).congr ?_
        filter_upwards [hc'] with y hy'
        exact (congrArg (fun z : c₂.O => (z : Qbar l)) (kred y (fun x hx => hy' ((hH y).2 ⟨x, hx⟩)))).symm
    have hxg : Continuous fun g => xg K'.fixingSubgroup g0 g := by
      simp only [xg]
      exact cont_ite _ hcl continuous_id (continuous_id.mul continuous_const)
    have hS : Continuous fun g => ((sg K'.fixingSubgroup g : c₂.O) : Qbar l) := by
      classical
      have e : (fun g => ((sg K'.fixingSubgroup g : c₂.O) : Qbar l)) =
          fun g => if g ∈ K'.fixingSubgroup then (1 : Qbar l) else -1 := by
        funext g
        unfold sg
        split_ifs <;> simp
      rw [e]
      exact cont_ite _ hcl continuous_const continuous_const
    have hA : Continuous fun g => ((aa k u (xg K'.fixingSubgroup g0 g) : c₂.O) : Qbar l) :=
      continuous_const.mul ((hK.comp hxg).add (hK.comp (continuous_inv.comp hxg)))
    have hB : Continuous fun g => ((bb k u (xg K'.fixingSubgroup g0 g) : c₂.O) : Qbar l) :=
      continuous_const.mul ((hK.comp hxg).sub (hK.comp (continuous_inv.comp hxg)))
    fin_cases i <;> fin_cases j
    · exact hA
    · exact hS.mul hB
    · exact hB
    · exact hS.mul hA
  ·
    intro g hg
    show (sg K'.fixingSubgroup g : c₂.O) * aa k u (xg K'.fixingSubgroup g0 g) = aa k u (xg K'.fixingSubgroup g0 g) ∧
      bb k u (xg K'.fixingSubgroup g0 g) = (sg K'.fixingSubgroup g : c₂.O) * bb k u (xg K'.fixingSubgroup g0 g)
    simp only [sg, if_pos hg, one_mul, and_self]
  ·
    intro g hg
    show (sg K'.fixingSubgroup g : c₂.O) * aa k u (xg K'.fixingSubgroup g0 g) = -aa k u (xg K'.fixingSubgroup g0 g) ∧
      bb k u (xg K'.fixingSubgroup g0 g) = -((sg K'.fixingSubgroup g : c₂.O) * bb k u (xg K'.fixingSubgroup g0 g))
    simp only [sg, if_neg hg]
    constructor <;> ring
  ·
    intro g
    show aa k u (xg K'.fixingSubgroup g0 g) - 1 ∈ maximalIdeal c₂.O ∧
      (sg K'.fixingSubgroup g : c₂.O) * bb k u (xg K'.fixingSubgroup g0 g) ∈ maximalIdeal c₂.O
    generalize xg K'.fixingSubgroup g0 g = x
    have h1 := kmax x
    have h2 := kmax x⁻¹
    constructor
    · have e : aa k u x - 1 = u * (k x - 1) + u * (k x⁻¹ - 1) := by
        simp only [aa]
        linear_combination hu
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    · have e : bb k u x = u * ((k x - 1) - (k x⁻¹ - 1)) := by
        simp only [bb]
        ring
      rw [e]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.sub_mem _ h1 h2))
  ·
    show tauF K'.fixingSubgroup k u g0 g0 = _
    rw [tauF_nmem hg0, mul_inv_cancel, Nm_one_of hy hy.one (by rw [inv_one, hy.one]), one_mul]
  ·
    intro A hA g hg hgH
    obtain ⟨x, rfl⟩ := (hH g).1 hgH
    have h1 : κ x = 1 := hκ.unr A hA x hg
    have h2 : κ x⁻¹ = 1 := hκ.unr A hA x⁻¹ (by rw [map_inv]; exact inv_mem hg)
    show tauF K'.fixingSubgroup k u g0 (resQ K' x) = 1
    rw [tauF_mem hgH]
    refine Nm_one_of hy (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [kres, h1]
      rfl
    · rw [← map_inv (resQ K') x, kres, h2]
      rfl
  ·
    intro A
    unfold sA
    split_ifs <;> simp
  ·
    intro A A' g hA hgA
    have e1 : g (l : Ω) = l := map_natCast g l
    have hA' : A'.valuation (l : Ω) < 1 := by
      have i1 := hgA (l : Ω)
      have i2 := hgA (l : Ω)⁻¹
      rw [e1] at i1
      rw [map_inv₀, e1] at i2
      have hA2 := hA
      rw [valuation_lt_one_iff'] at hA2 ⊢
      rw [i1, i2]
      exact hA2
    have hL : UpperTheory.V.IsLift (RingEquiv.refl ℚ) g.toRingEquiv := fun x => g.commutes x
    have hcj : ∀ σ ∈ Ine (F := ℚ) A', g⁻¹ * σ * g ∈ Ine (F := ℚ) A := by
      intro σ hσ
      have e : UpperTheory.V.conjGal hL σ = g⁻¹ * σ * g := rfl
      rw [← e]
      exact UpperTheory.V.conjGal_mem_Ine hL hgA hσ
    have tr : ∀ x' : G K' Ω, resQ K' x' ∈ Ine (F := ℚ) A' → ∃ y : G K' Ω, resQ K' y ∈ Ine (F := ℚ) A ∧
        cycBar K' Ω l x' = cycBar K' Ω l y ∧ (g ∈ K'.fixingSubgroup → κ x' = κ y) ∧
        (g ∉ K'.fixingSubgroup → κ x' = (κ y)⁻¹) := by
      intro x' hx'
      have hm := hcj _ hx'
      obtain ⟨y, hy'⟩ := (hH _).1 (hDec A hA (Ine_le_Dec (F := ℚ) A hm))
      refine ⟨y, by rw [hy']; exact hm, ?_, ?_, ?_⟩
      · show cycBar ℚ Ω l (resQ K' x') = cycBar ℚ Ω l (resQ K' y)
        rw [hy', map_mul, map_mul, map_inv, conj_comm]
      · intro hgH
        obtain ⟨z, rfl⟩ := (hH g).1 hgH
        have e : y = z⁻¹ * x' * z := res_inj K' (by rw [hy', map_mul, map_mul, map_inv])
        rw [e, map_mul, map_mul, map_inv, conj_comm]
      · intro hgH
        have := hκ.anti g hgH y x' (by rw [hy']; group)
        exact eq_inv_of_mul_eq_one_right this
    have hex := excl K' hH hDec κ m hκ.pos A' hA'
    have hQ : ¬ PP K' κ (m : ℤ) A → PP K' κ (-(m : ℤ)) A := fun h => (hκ.ine A hA).resolve_left h
    constructor
    · intro hgH
      unfold sA
      rcases em (PP K' κ (m : ℤ) A) with hP | hP
      · have hP' : PP K' κ (m : ℤ) A' := by
          intro x' hx'
          obtain ⟨y, hyA, hcy, hk, -⟩ := tr x' hx'
          rw [hk hgH, hP y hyA, hcy]
        rw [if_pos hP, if_pos hP']
      · have hQ' : PP K' κ (-(m : ℤ)) A' := by
          intro x' hx'
          obtain ⟨y, hyA, hcy, hk, -⟩ := tr x' hx'
          rw [hk hgH, hQ hP y hyA, hcy]
        rw [if_neg hP, if_neg (fun h => hex ⟨h, hQ'⟩)]
    · intro hgH
      unfold sA
      rcases em (PP K' κ (m : ℤ) A) with hP | hP
      · have hQ' : PP K' κ (-(m : ℤ)) A' := by
          intro x' hx'
          obtain ⟨y, hyA, hcy, -, hk⟩ := tr x' hx'
          rw [hk hgH, hP y hyA, hcy, ← zpow_neg]
        rw [if_pos hP, if_neg (fun h => hex ⟨h, hQ'⟩)]
      · have hP' : PP K' κ (m : ℤ) A' := by
          intro x' hx'
          obtain ⟨y, hyA, hcy, -, hk⟩ := tr x' hx'
          rw [hk hgH, hQ hP y hyA, hcy, zpow_neg, inv_inv]
        rw [if_neg hP, if_pos hP', neg_neg]
  ·
    intro A hA g hg
    have hgH : g ∈ K'.fixingSubgroup := hDec A hA (Ine_le_Dec (F := ℚ) A hg)
    obtain ⟨x, rfl⟩ := (hH g).1 hgH
    apply Subtype.ext
    rw [chi_coe, show ((cycBar ℚ Ω l (resQ K' x) ^ m : (Qbar l)ˣ) : Qbar l) =
      ((cycBar K' Ω l x ^ (m : ℤ) : (Qbar l)ˣ) : Qbar l) by rw [zpow_natCast]; rfl]
    show ((aa k u (xg K'.fixingSubgroup g0 (resQ K' x)) + (sg K'.fixingSubgroup (resQ K' x) : c₂.O) *
      bb k u (xg K'.fixingSubgroup g0 (resQ K' x)) * sA K' κ c₂ m A : c₂.O) : Qbar l) = _
    simp only [xg, sg, if_pos hgH]
    unfold sA
    rcases em (PP K' κ (m : ℤ) A) with hP | hP
    · rw [if_pos hP]
      have e : aa k u (resQ K' x) + 1 * bb k u (resQ K' x) * 1 = k (resQ K' x) := by
        simp only [aa, bb]
        linear_combination (k (resQ K' x)) * hu
      rw [e, kres, hP x hg]
    · rw [if_neg hP]
      have hQ : PP K' κ (-(m : ℤ)) A := (hκ.ine A hA).resolve_left hP
      have e : aa k u (resQ K' x) + 1 * bb k u (resQ K' x) * (-1) = k (resQ K' x⁻¹) := by
        rw [map_inv]
        simp only [aa, bb]
        linear_combination (k (resQ K' x)⁻¹) * hu
      rw [e, kres, map_inv, hQ x hg, zpow_neg, inv_inv]
  ·
    intro h
    have hg := kH h
    have e : (tau hy (resQ K' h) 0 0 + tau hy (resQ K' h) 0 1 : c₂.O) = k (resQ K' h) := by
      show aa k u (xg K'.fixingSubgroup g0 (resQ K' h)) +
        (sg K'.fixingSubgroup (resQ K' h) : c₂.O) * bb k u (xg K'.fixingSubgroup g0 (resQ K' h)) = _
      simp only [xg, sg, if_pos hg, aa, bb]
      linear_combination (k (resQ K' h)) * hu
    rw [e, kres]

end UpperTheory.V.Cu2

end
