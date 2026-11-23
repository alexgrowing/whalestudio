import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPoint
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianO1PullbackFubiniStudyMetric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog HermLine)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine

namespace GlobalTheory.CompanionTheory.MixZ.ExRat

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem dehomog_X_chart (c : ∀ k, Bk n k) (k : Fin (m + 1)) : dehomog c (X ⟨k, c k⟩) = 1 := by
  simp only [dehomog, coe_eval₂Hom, eval₂_X, pullRatio_self, map_one]

theorem dehomog_surjective (c : ∀ k, Bk n k) : Function.Surjective (dehomog c) := by
  intro v
  have hle : Subring.closure (Set.range (SmoothRep.rt c)) ≤ (dehomog c).range := by
    rw [Subring.closure_le]
    rintro _ ⟨q, rfl⟩
    exact ⟨X q, by simp [dehomog, SmoothRep.rt]⟩
  exact hle ((SmoothRep.gen m n c).2 ▸ Subring.mem_top v)

theorem isMultiHomog_C (r : ℤ) : IsMultiHomog (C r : Pol n) 0 := by
  intro e he k
  have h0 : e = 0 := by
    by_contra h
    rw [MvPolynomial.mem_support_iff, coeff_C, if_neg (Ne.symm h)] at he
    exact he rfl
  subst h0
  simp

theorem isMultiHomog_X_pow (p : Σ k, Bk n k) (e : ℕ) :
    IsMultiHomog (X p ^ e : Pol n) (e • fun k => if k = p.1 then 1 else 0) := by
  induction e with
  | zero => simpa using isMultiHomog_C (n := n) 1
  | succ e ih =>
    rw [pow_succ, succ_nsmul]
    exact mhMul ih (isMultiHomog_X p)

def mono (c : ∀ k, Bk n k) (d : Fin (m + 1) → ℕ) : Pol n := ∏ k, X ⟨k, c k⟩ ^ d k

theorem isMultiHomog_mono (c : ∀ k, Bk n k) (d : Fin (m + 1) → ℕ) : IsMultiHomog (mono c d) d := by
  have h : ∀ s : Finset (Fin (m + 1)), IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : Pol n) ^ d k)
      (∑ k ∈ s, d k • fun l => if l = k then 1 else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isMultiHomog_C (n := n) 1
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact mhMul (isMultiHomog_X_pow _ _) ih
  have e : (∑ k, d k • fun l : Fin (m + 1) => if l = k then 1 else 0) = d := by
    funext l
    simp [Finset.sum_apply]
  have := h Finset.univ
  rwa [e] at this

theorem dehomog_mono (c : ∀ k, Bk n k) (d : Fin (m + 1) → ℕ) : dehomog c (mono c d) = 1 := by
  simp [mono, map_prod, map_pow, dehomog_X_chart]

theorem exists_homog (c : ∀ k, Bk n k) (F : Pol n) :
    ∃ (a : Fin (m + 1) → ℕ) (F' : Pol n), IsMultiHomog F' a ∧ dehomog c F' = dehomog c F := by
  induction F using MvPolynomial.induction_on with
  | C r => exact ⟨0, C r, isMultiHomog_C r, rfl⟩
  | add p q hp hq =>
    obtain ⟨a, p', hp', ep⟩ := hp
    obtain ⟨b, q', hq', eq⟩ := hq
    refine ⟨a + b, p' * mono c b + q' * mono c a, mhAdd (mhMul hp' (isMultiHomog_mono c b)) ?_, ?_⟩
    · rw [add_comm a b]
      exact mhMul hq' (isMultiHomog_mono c a)
    · simp [dehomog_mono, ep, eq]
  | mul_X p q hp =>
    obtain ⟨a, p', hp', ep⟩ := hp
    exact ⟨_, p' * X q, mhMul hp' (isMultiHomog_X q), by simp [ep]⟩

section Field

variable {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n)

def fnI (V : (MP ℤ m n).Opens) (h : genericPoint X ∈ i ⁻¹ᵁ V) : Γ(MP ℤ m n, V) →+* X.functionField :=
  (fnOf (i ⁻¹ᵁ V) h).comp (i.app V).hom

theorem fnI_resG {V W : (MP ℤ m n).Opens} (e : W ≤ V) (h : genericPoint X ∈ i ⁻¹ᵁ W)
    (hV : genericPoint X ∈ i ⁻¹ᵁ V) (s : Γ(MP ℤ m n, V)) :
    fnI i W h (resG _ e s) = fnI i V hV s := by
  have e₁ : (i.app W).hom (resG _ e s) = resG X (i.preimage_mono e) ((i.app V).hom s) :=
    congr($(i.naturality (homOfLE e).op) s)
  show fnOf (i ⁻¹ᵁ W) h ((i.app W).hom (resG _ e s)) = _
  rw [e₁, fnOf_resG]
  rfl

def yc (c : ∀ k, Bk n k) (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c) (q : Σ k, Bk n k) : X.functionField :=
  fnAt i c hc (MvPolynomial.X q)

theorem fnAt_eq_aeval (c : ∀ k, Bk n k) (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c) (s : Pol n) :
    fnAt i c hc s = aeval (yc i c hc) s := by
  have e : (fnI i (mchart c) hc).comp (dehomog c) = (aeval (yc i c hc) : Pol n →ₐ[ℤ] _).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun p => by simp [yc, fnAt, fnI])
  exact congrArg (fun φ => φ s) e

theorem fnI_pullRatio (c : ∀ k, Bk n k) (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c) {W : (MP ℤ m n).Opens}
    (e : W ≤ mchart c) (h : genericPoint X ∈ i ⁻¹ᵁ W) (k : Fin (m + 1)) (hW : W ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (c k))
    (j : Bk n k) : fnI i W h (pullRatio (prB n k) W (c k) hW j) = yc i c hc ⟨k, j⟩ := by
  have e₁ : yc i c hc ⟨k, j⟩ = fnI i (mchart c) hc (pullRatio (prB n k) (mchart c) (c k) (mchart_le c k) j) := by
    show fnI i (mchart c) hc (dehomog c (MvPolynomial.X ⟨k, j⟩)) = _
    simp only [dehomog, coe_eval₂Hom, eval₂_X]
    rw [resG_pullRatio]
  rw [e₁, ← fnI_resG i e h hc, resG_pullRatio]

theorem yc_self (c : ∀ k, Bk n k) (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c) (k : Fin (m + 1)) :
    yc i c hc ⟨k, c k⟩ = 1 := by
  simp [yc, fnAt, dehomog_X_chart]

theorem yc_mul (c c' : ∀ k, Bk n k) (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c) (hc' : genericPoint X ∈ i ⁻¹ᵁ mchart c')
    (k : Fin (m + 1)) (j : Bk n k) : yc i c hc ⟨k, j⟩ = yc i c hc ⟨k, c' k⟩ * yc i c' hc' ⟨k, j⟩ := by
  have h : genericPoint X ∈ i ⁻¹ᵁ (mchart c ⊓ mchart c') := ⟨hc, hc'⟩
  have e₁ : (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (c k) := inf_le_left.trans (mchart_le c k)
  have e₂ : (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (c' k) := inf_le_right.trans (mchart_le c' k)
  rw [← fnI_pullRatio i c hc inf_le_left h k e₁, ← fnI_pullRatio i c hc inf_le_left h k e₁,
    ← fnI_pullRatio i c' hc' inf_le_right h k e₂, ← map_mul, pullRatio_mul_pullRatio]

theorem yc_ne_zero (c c' : ∀ k, Bk n k) (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c) (hc' : genericPoint X ∈ i ⁻¹ᵁ mchart c')
    (k : Fin (m + 1)) : yc i c hc ⟨k, c' k⟩ ≠ 0 := by
  intro h
  have := yc_mul i c c' hc hc' k (c k)
  rw [yc_self, h, zero_mul] at this
  exact one_ne_zero this

theorem fnAt_change (c c' : ∀ k, Bk n k) (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c)
    (hc' : genericPoint X ∈ i ⁻¹ᵁ mchart c') {s : Pol n} {a : Fin (m + 1) → ℕ} (hs : IsMultiHomog s a) :
    fnAt i c hc s = (∏ k, yc i c hc ⟨k, c' k⟩ ^ a k) * fnAt i c' hc' s := by
  rw [fnAt_eq_aeval, fnAt_eq_aeval, ← BlockImageInverse.aeval_smul hs]
  congr 2
  funext p
  exact yc_mul i c c' hc hc' p.1 p.2

variable [IsClosedImmersion i]

theorem exists_quot (c : ∀ k, Bk n k) (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c) (e : X.functionField) :
    ∃ F G : Pol n, fnAt i c hc G ≠ 0 ∧ e * fnAt i c hc G = fnAt i c hc F := by
  have hA : IsAffineOpen (i ⁻¹ᵁ mchart c) := (SmoothRep.gen m n c).1.preimage i
  haveI : Nonempty (i ⁻¹ᵁ mchart c : X.Opens) := ⟨⟨_, hc⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X _ hA
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, i ⁻¹ᵁ mchart c)) e
  obtain ⟨a', rfl⟩ := i.app_surjective _ (SmoothRep.gen m n c).1 a
  obtain ⟨d', rfl⟩ := i.app_surjective _ (SmoothRep.gen m n c).1 d
  obtain ⟨F, rfl⟩ := dehomog_surjective c a'
  obtain ⟨G, rfl⟩ := dehomog_surjective c d'
  have hd0 : algebraMap Γ(X, i ⁻¹ᵁ mchart c) X.functionField ((i.app _).hom (dehomog c G)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  refine ⟨F, G, hd0, ?_⟩
  exact div_mul_cancel₀ _ hd0

theorem notMem_of_fnAt_ne_zero (hc : genericPoint X ∈ i ⁻¹ᵁ mchart (ptChart (i (genericPoint X))))
    {f : Pol n} {a : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a)
    (h : fnAt i (ptChart (i (genericPoint X))) hc f ≠ 0) : f ∉ ptIdeal (i (genericPoint X)) := by
  intro hmem
  apply h
  have hx : i (genericPoint X) ∈ mchart (ptChart (i (genericPoint X))) := hc
  have h1 := (mem_ptIdeal_iff_aeval_ptCoord m n _ f a hf).1 hmem
  rw [FnForm.aeval_ptCoord_eq_mul _ _ hx hf] at h1
  simp only [ptCoord_ptChart, one_pow, Finset.prod_const_one, one_mul] at h1
  have h2 := Scheme.evaluation_naturality_apply i (genericPoint X) hx (dehomog (ptChart (i (genericPoint X))) f)
  rw [h1, map_zero] at h2
  have h3 : (X.residue (genericPoint X)).hom (fnAt i _ hc f) = 0 := h2.symm
  exact (RingHom.injective ((X.residue (genericPoint X)).hom : X.functionField →+* _)) (h3.trans (map_zero _).symm)

end Field

section Rules

variable {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n)
variable {M : HermLB (mpStr ℤ m n)} {A : HermLine (Bk n)}
  {u : ∀ (b : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U b ⊓ mchart c)ˣ}

theorem fnI_res {V W : (MP ℤ m n).Opens} (e : W ≤ V) (h : genericPoint X ∈ i ⁻¹ᵁ W)
    (hV : genericPoint X ∈ i ⁻¹ᵁ V) (s : Γ(MP ℤ m n, V)ˣ) :
    fnI i W h (Semi.res e s : Γ(MP ℤ m n, W)ˣ).val = fnI i V hV s.val :=
  fnI_resG i e h hV s.val

theorem rule_frame (hu : RepBy M A u) (a b : M.B.ι) (c : ∀ k, Bk n k)
    (ha : genericPoint X ∈ i ⁻¹ᵁ (M.B.U a ⊓ mchart c)) (hb : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c)) :
    fnI i _ hb (u b c).val =
      fnI i (M.B.U a ⊓ M.B.U b) ⟨ha.1, hb.1⟩ (M.B.g a b).val * fnI i _ ha (u a c).val := by
  have hW : genericPoint X ∈ i ⁻¹ᵁ (M.B.U a ⊓ M.B.U b ⊓ mchart c) := ⟨⟨ha.1, hb.1⟩, ha.2⟩
  have e := congrArg (fun v : Γ(MP ℤ m n, M.B.U a ⊓ M.B.U b ⊓ mchart c)ˣ => fnI i _ hW v.val) (hu.1 a b c)
  beta_reduce at e
  rw [Units.val_mul, map_mul, fnI_res i _ hW hb, fnI_res i _ hW (show genericPoint X ∈ i ⁻¹ᵁ (M.B.U a ⊓ M.B.U b) from ⟨ha.1, hb.1⟩), fnI_res i _ hW ha] at e
  exact e

theorem rule_chart (hu : RepBy M A u) (b : M.B.ι) (c c' : ∀ k, Bk n k)
    (hb : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c)) (hb' : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c'))
    (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c) :
    fnI i _ hb (u b c).val = fnI i _ hb' (u b c').val * ∏ k, yc i c hc ⟨k, c' k⟩ ^ A.a k := by
  have hW : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ (mchart c ⊓ mchart c')) := ⟨hb.1, hb.2, hb'.2⟩
  let Φ : Γ(MP ℤ m n, M.B.U b ⊓ (mchart c ⊓ mchart c'))ˣ →* X.functionFieldˣ :=
    Units.map (fnI i _ hW : Γ(MP ℤ m n, M.B.U b ⊓ (mchart c ⊓ mchart c')) →* X.functionField)
  have hval : ∀ (k : Fin (m + 1)) (h : M.B.U b ⊓ (mchart c ⊓ mchart c') ≤
      prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))),
      ((Φ (blockUnit (c k) (c' k) h) : X.functionFieldˣ) : X.functionField) = yc i c hc ⟨k, c' k⟩ := by
    intro k h
    show fnI i _ hW (blockUnit (c k) (c' k) h).val = _
    rw [Inhab.val_blockUnit]
    exact fnI_pullRatio i c hc (inf_le_right.trans inf_le_left) hW k _ (c' k)
  have e := congrArg (fun v => ((Φ v : X.functionFieldˣ) : X.functionField)) (hu.2.1 b c c')
  beta_reduce at e
  simp only [map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val] at e
  refine (fnI_res i _ hW hb _).symm.trans (e.trans ?_)
  exact congrArg₂ (· * ·) (fnI_res i _ hW hb' _) (Finset.prod_congr rfl fun k _ => congrArg (· ^ A.a k) (hval k _))

theorem rat_rule {r : (M.restr i).B.ι → X.functionFieldˣ} (hr : IsRatSec (M.restr i).B r) (a b : M.B.ι)
    (ha : genericPoint X ∈ i ⁻¹ᵁ M.B.U a) (hb : genericPoint X ∈ i ⁻¹ᵁ M.B.U b) :
    (r (fun _ => a) : X.functionField) =
      fnI i (M.B.U a ⊓ M.B.U b) ⟨ha, hb⟩ (M.B.g a b).val * (r (fun _ => b) : X.functionField) := by
  have h : genericPoint X ∈ (M.B.pull i).U (fun _ => a) ⊓ (M.B.pull i).U (fun _ => b) :=
    ⟨(GlobalTheory.DvrModel.pull_U M.B i _).ge ha, (GlobalTheory.DvrModel.pull_U M.B i _).ge hb⟩
  refine (hr (fun _ => a) (fun _ => b) h).trans (congrArg (· * _) ?_)
  show fnOf _ h ((M.B.pull i).g (fun _ => a) (fun _ => b) : Γ(X, (M.B.pull i).U (fun _ => a) ⊓ (M.B.pull i).U (fun _ => b))) = _
  rw [GlobalTheory.DvrModel.coe_pull_g]
  exact fnOf_resG _ h _

theorem fnOf_mul_r_mul_fnAt_eq (hu : RepBy M A u) {r : (M.restr i).B.ι → X.functionFieldˣ} (hr : IsRatSec (M.restr i).B r)
    {f g : Pol n} {α β : Fin (m + 1) → ℕ} (hf : IsMultiHomog f α) (hg : IsMultiHomog g β)
    (hd : ∀ k, (α k : ℤ) - β k = A.a k) (b : M.B.ι) (c : ∀ k, Bk n k)
    (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c) (hb : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c))
    (e : fnI i _ hb (u b c).val * (r (fun _ => b) : X.functionField) * fnAt i c hc g = fnAt i c hc f)
    (b' : M.B.ι) (c' : ∀ k, Bk n k) (hc' : genericPoint X ∈ i ⁻¹ᵁ mchart c')
    (hb' : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b' ⊓ mchart c')) :
    fnOf _ hb' (i.app _ (u b' c').val) * (r (fun _ => b') : X.functionField) * fnAt i c' hc' g = fnAt i c' hc' f := by
  have hbc : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b' ⊓ mchart c) := ⟨hb'.1, hc⟩
  have s1 : fnI i _ hbc (u b' c).val * (r (fun _ => b') : X.functionField) =
      fnI i _ hb (u b c).val * (r (fun _ => b) : X.functionField) := by
    rw [rule_frame i hu b b' c hb hbc, rat_rule i hr b b' hb.1 hb'.1]
    ring
  have s2 := rule_chart i hu b' c c' hbc hb' hc
  rw [← s1, s2, fnAt_change i c c' hc hc' hg, fnAt_change i c c' hc hc' hf] at e
  have hPQ : (∏ k, yc i c hc ⟨k, c' k⟩ ^ α k) =
      (∏ k, yc i c hc ⟨k, c' k⟩ ^ A.a k) * ∏ k, yc i c hc ⟨k, c' k⟩ ^ β k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have h1 : (α k : ℤ) = A.a k + β k := by
      have := hd k
      omega
    rw [← zpow_natCast (yc i c hc ⟨k, c' k⟩) (α k), h1, zpow_add₀ (yc_ne_zero i c c' hc hc' k), zpow_natCast]
  have hne : (∏ k, yc i c hc ⟨k, c' k⟩ ^ A.a k) * ∏ k, yc i c hc ⟨k, c' k⟩ ^ β k ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (yc_ne_zero i c c' hc hc' k))
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (yc_ne_zero i c c' hc hc' k))
  apply mul_left_cancel₀ hne
  have e' : fnI i _ hb' (u b' c').val = fnOf _ hb' (i.app _ (u b' c').val) := rfl
  rw [e'] at e
  linear_combination e + fnAt i c' hc' f * hPQ

end Rules

theorem existsRat : ExistsRat := by
  intro m n M A hA X _ i _ r hr
  obtain ⟨u, hu⟩ := (isHermRep_iff M A).1 hA
  have hx : ∀ k, i (genericPoint X) ∈ blockChart n k (ptChart (i (genericPoint X)) k) :=
    fun k => mem_ptChart _ k
  have hc : genericPoint X ∈ i ⁻¹ᵁ mchart (ptChart (i (genericPoint X))) := Set.mem_iInter.2 hx
  obtain ⟨b, hbU⟩ : ∃ b, i (genericPoint X) ∈ M.B.U b :=
    Opens.mem_iSup.1 (M.isLB.cover.ge (Set.mem_univ (i (genericPoint X))))
  have hb : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart (ptChart (i (genericPoint X)))) := ⟨hbU, hc⟩
  obtain ⟨F₀, G₀, hG₀, hq⟩ := exists_quot i _ hc
    (fnI i _ hb (u b _).val * (r (fun _ => b) : X.functionField))
  obtain ⟨α₀, F₁, hF₁, eF⟩ := exists_homog (ptChart (i (genericPoint X))) F₀
  obtain ⟨β₀, G₁, hG₁, eG⟩ := exists_homog (ptChart (i (genericPoint X))) G₀
  let δ : Fin (m + 1) → ℤ := fun k => A.a k - α₀ k + β₀ k
  have hfm := mhMul hF₁ (isMultiHomog_mono (ptChart (i (genericPoint X))) fun k => (δ k).toNat)
  have hgm := mhMul hG₁ (isMultiHomog_mono (ptChart (i (genericPoint X))) fun k => (-δ k).toNat)
  have ef : fnAt i _ hc (F₁ * mono (ptChart (i (genericPoint X))) fun k => (δ k).toNat) = fnAt i _ hc F₀ := by
    simp only [fnAt, map_mul, dehomog_mono, eF, map_one, mul_one]
  have eg : fnAt i _ hc (G₁ * mono (ptChart (i (genericPoint X))) fun k => (-δ k).toNat) = fnAt i _ hc G₀ := by
    simp only [fnAt, map_mul, dehomog_mono, eG, map_one, mul_one]
  have he : fnI i _ hb (u b _).val * (r (fun _ => b) : X.functionField) ≠ 0 :=
    mul_ne_zero ((u b _).isUnit.map (fnI i _ hb)).ne_zero (r _).ne_zero
  have hF₀ : fnAt i _ hc F₀ ≠ 0 := hq ▸ mul_ne_zero he hG₀
  have hd : ∀ k, (((α₀ + fun k => (δ k).toNat) k : ℕ) : ℤ) - ((β₀ + fun k => (-δ k).toNat) k : ℕ) = A.a k := by
    intro k
    simp only [Pi.add_apply, δ]
    omega
  refine ⟨_, _, ⟨_, _, hfm, hgm, notMem_of_fnAt_ne_zero i hc hfm (ef ▸ hF₀),
    notMem_of_fnAt_ne_zero i hc hgm (eg ▸ hG₀), hd⟩, u, hu, fun b' c' hc' hb' => ?_⟩
  exact fnOf_mul_r_mul_fnAt_eq i hu hr hfm hgm hd b _ hc hb (by rw [ef, eg]; exact hq) b' c' hc' hb'

end GlobalTheory.CompanionTheory.MixZ.ExRat
