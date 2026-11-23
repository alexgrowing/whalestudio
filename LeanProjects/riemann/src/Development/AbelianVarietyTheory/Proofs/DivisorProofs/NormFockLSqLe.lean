import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedWittNormSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRenaming
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfUnitCoord
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormLeOfCoord
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtremalRowWeight
import Formalism.ThetaSupremumBounds.LiftOperatorBoundOfFockJet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSubstLe

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker
open Formalism.REAL (fockF)
open GlobalTheory.SubstMem (padRows)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (substAdj sharp ptTable)
open GlobalTheory.IndefiniteRowSideFullHecke.PaddedWittNormSquare
open GlobalTheory.LvT.PtNorm (eN eN_pos eN_eq fockF_eq fockL_nonneg gram gram_dot gram_psd gram_sub_psd psd_prod)
open GlobalTheory.JetPoint (expL expR)
open scoped Matrix ComplexOrder ComplexConjugate

noncomputable section

namespace GlobalTheory.JetBlock

theorem norm_fockL_sq_le {σ : Type} (f g : MvPolynomial σ ℂ) :
    ‖fockL f g‖ ^ 2 ≤ (fockL f f).re * (fockL g g).re := by
  let c : PreInnerProductSpace.Core ℂ (MvPolynomial σ ℂ) :=
    { inner := fun x y => fockL x y
      conj_inner_symm := fun x y => (fockL_symm x y).symm
      re_inner_nonneg := fun x => (Complex.le_def.mp (fockL_nonneg x)).1
      add_left := fun x y z => by simp only [map_add, LinearMap.add_apply]
      smul_left := fun x y r => by simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] }
  have h : ‖fockL f g‖ * ‖fockL g f‖ ≤ (fockL f f).re * (fockL g g).re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (c := c) f g
  rwa [fockL_symm g f, norm_star, ← sq] at h

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem fock_tensor_le (lam : ι → DomWeight a)
    (F : ι → MvPolynomial (Fin a × Fin a) ℂ →ₗ[ℂ] MvPolynomial (Fin b × Fin b) ℂ) (C : ι → ℝ)
    (h : ∀ τ, ∀ f ∈ nablaSq ℂ a (lam τ), (fockL (F τ f) (F τ f)).re ≤ C τ * (fockL f f).re)
    (T : Pol ℂ ι a →ₗ[ℂ] Pol ℂ ι b) (hT : ∀ f, T (ten f) = ten fun τ => F τ (f τ))
    {p : Pol ℂ ι a} (hp : p ∈ VV ℂ lam) : (fockL (T p) (T p)).re ≤ (∏ τ, C τ) * (fockL p p).re := by
  obtain ⟨k, c, g, rfl⟩ := Submodule.mem_span_set'.mp hp
  choose f hf hf' using fun i => (g i).2
  have hg : ∀ i, (g i : Pol ℂ ι a) = ten (f i) := hf'
  have hten : ∀ {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) ℂ),
      fockL (ten f) (ten g) = ∏ τ, fockL (f τ) (g τ) := fun f g => fk_fock_prod Finset.univ f g
  simp only [hg]
  have key := (psd_prod (fun τ => (C τ : ℂ) • gram fun i => f i τ) (fun τ => gram fun i => F τ (f i τ))
    (fun τ => gram_psd _) (fun τ => gram_sub_psd _ (F τ) (C τ) (h τ) _ (fun i => hf i τ)) Finset.univ).2
  have e1 : (Matrix.of fun i j => ∏ τ, ((C τ : ℂ) • gram fun i => f i τ) i j) =
      ((∏ τ, C τ : ℝ) : ℂ) • gram fun i => ten (f i) := by
    ext i j
    simp [gram, hten, Finset.prod_mul_distrib]
  have e2 : (Matrix.of fun i j => ∏ τ, (gram fun i => F τ (f i τ)) i j) =
      gram fun i => ten fun τ => F τ (f i τ) := by
    ext i j
    simp [gram, hten]
  rw [e1, e2] at key
  have h1 := key.dotProduct_mulVec_nonneg c
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, gram_dot, gram_dot] at h1
  have e3 : T (∑ i, c i • ten (f i)) = ∑ i, c i • ten fun τ => F τ (f i τ) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hT]
  rw [e3]
  have h2 := (Complex.le_def.mp h1).1
  simp only [smul_eq_mul, Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul] at h2
  linarith

theorem normSq_eq {n : ℕ} (lam : ι → DomWeight n) (v : VV ℂ lam) :
    normSq lam v = (fockL (v : Pol ℂ ι n) (v : Pol ℂ ι n)).re / ∏ τ, eN (lam τ) := by
  have h : extNorm ℂ lam = ((∏ τ, eN (lam τ) : ℝ) : ℂ) := by
    rw [extNorm, Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun τ _ => by rw [← eN_eq, fockF_eq, fockL_apply]
  rw [normSq, pairK_apply, pairP_apply, h, ← Complex.div_ofReal_re]
  simp [gramTw, blockAct_one, div_eq_inv_mul]

def sing (h : a ≤ b) (A : Matrix (Fin a) (Fin b) ℂ) : Fin a → ℝ := (fock_subst_le h A).choose

def subOne (h : a ≤ b) (A : Matrix (Fin a) (Fin b) ℂ) (e : ℕ) :
    MvPolynomial (Fin a × Fin a) ℂ →ₗ[ℂ] MvPolynomial (Fin b × Fin b) ℂ :=
  (rowAct ℂ (padRows A)).toLinearMap ∘ₗ (rename (incl h)).toLinearMap ∘ₗ
    LinearMap.mulRight ℂ (GlobalTheory.WeylMinorDual.gdet ℂ a ^ e)

theorem substAdj_ten (h : a ≤ b) (ap : ι → Matrix (Fin a) (Fin b) ℂ) (n : ι → ℕ)
    (f : ι → MvPolynomial (Fin a × Fin a) ℂ) :
    substAdj h ap (sharp n (ten f)) = ten fun τ => subOne h (ap τ) (n τ) (f τ) := by
  rw [sharp, ← GlobalTheory.WeylMinorDual.ten_gdet, ten, ten, ten, ← Finset.prod_mul_distrib, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← map_mul, GlobalTheory.SubstMem.substAdj_blockEmb]
  rfl

theorem toNat_eq {lam ν : DomWeight a} {lam' : DomWeight b} {s' s : ℤ} (h : IsStepWeight lam ν lam' s' s) (i : Fin a) :
    (ν.w i).toNat = lam.natW i + lastEntry ν := by
  have ha := i.pos
  have h1 := GlobalTheory.JetDeg.natW_cast lam i
  have h2 := h.1 i
  have h3 := h.1 ⟨a - 1, by omega⟩
  have h4 := h.2.1 ⟨a - 1, by omega⟩
  have h5 := h.2.1 i
  unfold lastEntry
  unfold DomWeight.detShift at h1 ⊢
  rw [dif_pos ha] at h1 ⊢
  omega

theorem natW_eq_rowNu (hab : a ≤ b) {lam ν : DomWeight a} {lam' : DomWeight b} {s' s : ℤ}
    (h : IsStepWeight lam ν lam' s' s) (hg : a < b ∨ lastEntry ν = 0) :
    lam'.natW = rowNu (r := b) fun i => lam.natW i + lastEntry ν := by
  funext i
  have h1 := natW_eq_padZero hab h hg i
  unfold padZero at h1
  unfold rowNu
  split_ifs at h1 ⊢ with hi
  · have := toNat_eq h ⟨i, hi⟩
    simp only
    omega
  · omega

theorem subOne_mem (hab : a ≤ b) {lam ν : DomWeight a} {lam' : DomWeight b} {s' s : ℤ}
    (h : IsStepWeight lam ν lam' s' s) (hg : a < b ∨ lastEntry ν = 0) (A : Matrix (Fin a) (Fin b) ℂ)
    {f : MvPolynomial (Fin a × Fin a) ℂ} (hf : f ∈ nablaSq ℂ a lam) :
    subOne hab A (lastEntry ν) f ∈ nablaSq ℂ b lam' := by
  rw [nablaSq, natW_eq_rowNu hab h hg]
  refine dualWeylRowStable ℂ b b _ _ _ (GlobalTheory.SubstMem.rename_mem_dualWeyl hab (lam.natW + fun _ => lastEntry ν) _
    (fun i => ?_) (fun j hj => ?_) _ ((dualWeylMul ℂ a a _ _ _ _).1 hf (GlobalTheory.SubstMem.det_pow_mem a _)))
  · simp [rowNu]
  · simp [rowNu, not_lt.mpr hj]

theorem subOne_le (hab : a ≤ b) {lam ν : DomWeight a} {lam' : DomWeight b} {s' s : ℤ}
    (h : IsStepWeight lam ν lam' s' s) (hg : a < b ∨ lastEntry ν = 0) (A : Matrix (Fin a) (Fin b) ℂ)
    {f : MvPolynomial (Fin a × Fin a) ℂ} (hf : f ∈ nablaSq ℂ a lam) :
    (fockL (subOne hab A (lastEntry ν) f) (subOne hab A (lastEntry ν) f)).re ≤
      ((∏ i, sing hab A i ^ (ν.w i).toNat) ^ 2 * (eN lam' / eN lam)) * (fockL f f).re := by
  obtain ⟨h0, -, h1⟩ := (fock_subst_le hab A).choose_spec
  have h2 := h1 (fun i => lam.natW i + lastEntry ν) (f * GlobalTheory.WeylMinorDual.gdet ℂ a ^ lastEntry ν)
    ((dualWeylMul ℂ a a _ _ _ _).1 hf (GlobalTheory.SubstMem.det_pow_mem a _))
  have h3 := fock_mul_det lam.natW (natW_antitone lam) (lastEntry ν) hf
  have h4 : fockF (hw ℂ (le_refl a) fun i => lam.natW i + lastEntry ν)
      (hw ℂ (le_refl a) fun i => lam.natW i + lastEntry ν) = eN lam' := by
    rw [← eN_eq, Formalism.BasicNotions.extremal, natW_eq_rowNu hab h hg, ← rename_hw hab, fockF_rename (incl_injective hab)]
  have h5 : fockF (hw ℂ (le_refl a) lam.natW) (hw ℂ (le_refl a) lam.natW) = eN lam := eN_eq lam
  rw [h4, h5] at h3
  have h6 := congrArg Complex.re h3
  rw [Complex.div_ofReal_re, Complex.div_ofReal_re, div_eq_iff (eN_pos lam').ne'] at h6
  rw [h6, fockF_eq, fockF_eq] at h2
  refine h2.trans (le_of_eq ?_)
  simp only [toNat_eq h, ← Finset.prod_pow, ← pow_mul, mul_comm 2, sing]
  ring

theorem taylor_jetC {G : VCx ι a b → ℂ} (hG : Differentiable ℂ G) (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (cD : ι → ℂ)
    (m : DVar ι a b →₀ ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff (fun u : DVar ι a b → ℂ => G fun τ β α => (r τ : ℂ)⁻¹ * u (τ, β, α)) m *
      (Formalism.DimensionVariation.mfact m : ℂ) * ∏ x : DVar ι a b, (cD x.1 * r x.1) ^ m x = jetC cD G m := by
  classical
  let L : (DVar ι a b → ℂ) →ₗ[ℂ] VCx ι a b :=
    { toFun := fun u τ β α => (r τ : ℂ)⁻¹ * u (τ, β, α)
      map_add' := fun u v => by funext τ β α; simp [mul_add]
      map_smul' := fun c u => by funext τ β α; simp [mul_left_comm] }
  have hF : Differentiable ℂ fun u => G (L u) := hG.comp (LinearMap.toContinuousLinearMap L).differentiable
  have hw : GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms.IsSpelling fun e : DVar ι a b → ℕ =>
      (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm e)).toList := fun e x => by
    rw [← Multiset.coe_count, Multiset.coe_toList, Finsupp.count_toMultiset]
    rfl
  have hne : (Formalism.DimensionVariation.mfact m : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos fun x _ => Nat.factorial_pos _).ne'
  have hL : (L ∘ GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.coordVec) = fun k => (r k.1 : ℂ)⁻¹ • coordX k := by
    funext k τ β α
    obtain ⟨τ', β', α'⟩ := k
    simp only [L, GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.coordVec, coordX, Function.comp, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
      Pi.single_apply, Prod.mk.injEq, smul_eq_mul]
    split_ifs with h
    · rw [h.1]
    · simp
  have hd : derivAt0 G m = lineDerivList ℂ (m.toMultiset.toList.map coordX) G 0 := by
    rw [derivAt0, ← lineDerivList_ofFn (SCV.analyticOnNhd_of_differentiable hG Set.univ 0 (Set.mem_univ _))]
    congr 1
    refine List.ext_getElem (by simp) fun i h1 h2 => by simp
  change GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff (fun u => G (L u)) m * _ * _ = _
  rw [GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff, div_mul_cancel₀ _ hne, ← GlobalTheory.JetFrameCompare.wordDeriv_eq_monoDeriv hw _ hF,
    GlobalTheory.JetFrameCompare.wordDeriv_eq_lineDerivList _ hF, lineDerivList_comp_linearMap, List.map_map, hL,
    lineDerivList_map_smul]
  beta_reduce
  rw [map_zero, Finsupp.equivFunOnFinite_symm_coe, ← hd, jetC, Finsupp.prod_fintype _ _ (by simp)]
  have hp : (m.toMultiset.toList.map fun k => (r k.1 : ℂ)⁻¹).prod = ∏ x : DVar ι a b, (r x.1 : ℂ)⁻¹ ^ m x := by
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList, Finset.prod_multiset_map_count,
      Finsupp.toFinset_toMultiset]
    simp only [Finsupp.count_toMultiset]
    exact Finset.prod_subset (Finset.subset_univ _) fun x _ hx => by simp [Finsupp.notMem_support_iff.mp hx]
  rw [hp, smul_eq_mul, mul_right_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun x _ => ?_
  have : (r x.1 : ℂ) ≠ 0 := by exact_mod_cast (hr x.1).ne'
  rw [← mul_pow]
  congr 1
  field_simp

theorem scalar_block (hab : a ≤ b) (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b) (s' s : ι → ℤ)
    (hw : ∀ τ, IsStepWeight (lam τ) (ν τ) (lam' τ) (s' τ) (s τ))
    (G : VCx ι a b → ℂ) (S : ℝ) (r Om : ι → ℝ) (cD : ι → ℂ) (hG : Differentiable ℂ G) (hr : ∀ τ, 0 < r τ)
    (hS : ∀ z, ‖G z‖ ≤ S * Real.exp (unitNormSq r z / 2)) (hOm : ∀ τ, 0 < Om τ)
    (hc : ∀ τ, ‖cD τ * (r τ : ℂ)‖ ^ 2 = 1 / Om τ) {P : Pol ℂ ι a} (hP : P ∈ VV ℂ lam) (φ : Pol ℂ ι b →ₗ[ℂ] ℂ)
    (hφ : ∀ ap : ι → Matrix (Fin a) (Fin b) ℂ, ‖φ (substAdj hab ap (sharp (fun τ => lastEntry (ν τ)) P))‖ ≤
      ∏ τ, ∏ i, sing hab (ap τ) i ^ ((ν τ).w i).toNat) :
    ‖φ (jetMap (jetC cD G) (fun τ => lastEntry (ν τ)) P)‖ ^ 2 ≤ tmax b ν Om S := by
  classical
  set n : ι → ℕ := fun τ => lastEntry (ν τ) with hn
  set Q := subD ℂ ι a b (sharp n P) with hQ
  set Rc : (ι × Fin b × Fin a → ℕ) →₀ ℂ :=
    ∑ μ ∈ Q.support, Finsupp.single (⇑(expR μ)) (φ (monomial (expL μ) (Q.coeff μ))) with hRc
  have hsum : ∀ g : (ι × Fin b × Fin a → ℕ) → ℂ,
      Rc.sum (fun e A => g e • A) = φ (jetMap (fun m => g m) n P) := by
    intro g
    have : Rc.sum (fun e A => g e • A) = Finsupp.linearCombination ℂ g Rc := by
      rw [Finsupp.linearCombination_apply]
      simp only [smul_eq_mul, mul_comm]
    rw [this, hRc, GlobalTheory.JetPoint.jetMap_eq_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finsupp.linearCombination_single, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  have hcast : ∀ τ i, (((ν τ).w i : ℤ) : ℝ) = (((ν τ).w i).toNat : ℝ) := fun τ i => by
    exact_mod_cast (Int.toNat_of_nonneg ((hw τ).2.1 i)).symm
  have hF : Differentiable ℂ fun u : DVar ι a b → ℂ => G fun τ β α => (r τ : ℂ)⁻¹ * u (τ, β, α) :=
    hG.comp (by fun_prop)
  have key := Formalism.DimensionVariation.blockBound ι (Fin b × Fin a) ℂ a (fun τ i => ((ν τ).w i : ℝ)) (fun τ => wtSize (ν τ))
    (fun _ u => sing hab fun α β => conj (u (β, α))) _ _ Rc (fun τ => cD τ * r τ) Om S
    (fun τ i => by exact_mod_cast (hw τ).2.1 i) (fun τ => by simp only [hcast, wtSize, Nat.cast_sum])
    (fun τ u i => (fock_subst_le hab _).choose_spec.1 i)
    (fun τ u => by
      rw [Formalism.DimensionVariation.nsq, Fintype.sum_prod_type]
      simpa [sing] using (fock_subst_le hab fun α β => conj (u (β, α))).choose_spec.2.1)
    hF.continuous (GlobalTheory.JetFrameCompare.hasSum_taylorCoeff hF)
    (fun u => by
      refine (hS _).trans (le_of_eq ?_)
      have : ∀ τ, (r τ : ℂ) ≠ 0 := fun τ => by exact_mod_cast (hr τ).ne'
      simp only [unitNormSq, Formalism.DimensionVariation.nsq, Fintype.sum_prod_type, mul_inv_cancel_left₀ (this _)])
    (fun e he τ => by
      obtain ⟨μ, hμ, he⟩ := Finsupp.mem_support_finsetSum e he
      have he' : e = ⇑(expR μ) := Finset.mem_singleton.mp (Finsupp.support_single_subset he)
      have h := GlobalTheory.JetDeg.subD_hom (b := b) τ (GlobalTheory.JetDeg.sharp_hom n τ (GlobalTheory.JetDeg.VV_hom lam τ hP))
        (mem_support_iff.mp hμ)
      rw [GlobalTheory.JetDeg.weight_derW] at h
      rw [he', Fintype.sum_prod_type]
      simp only [Finsupp.comapDomain_apply]
      rw [h, wtSize]
      simp [toNat_eq (hw τ), Finset.sum_add_distrib, hn, mul_comm])
    (fun u => by
      rw [hsum]
      have e : (fun m : DVar ι a b →₀ ℕ => Formalism.DimensionVariation.mono (Formalism.DimensionVariation.cj u) m) =
          ptTable fun τ => Matrix.of fun α β => conj (u (τ, β, α)) := by
        funext m
        rw [ptTable, Finsupp.prod_fintype _ _ (by simp)]
        rfl
      rw [e, GlobalTheory.JetPoint.jetMap_ptTable hab]
      simp only [hcast, Real.rpow_natCast]
      exact hφ _)
    hOm (fun τ => by rw [hc, one_div])
  rw [hsum] at key
  simp only [taylor_jetC hG r hr cD] at key
  refine key.trans (le_of_eq ?_)
  simp only [tmax, Fintype.card_prod, Fintype.card_fin, mul_assoc, mul_comm b a]

theorem blockBound : BlockBound := by
  intro ι _ a b hab lam ν lam' s' s hw hg G S r Om cD hG hr hS hOm hc v
  set n : ι → ℕ := fun τ => lastEntry (ν τ) with hn
  let T : (ι → Matrix (Fin a) (Fin b) ℂ) → Pol ℂ ι a →ₗ[ℂ] Pol ℂ ι b := fun ap =>
    (substAdj hab ap).toLinearMap ∘ₗ LinearMap.mulRight ℂ (∏ τ, frDet ℂ a τ ^ n τ)
  have hmem : jetMap (jetC cD G) n (v : Pol ℂ ι a) ∈ VV ℂ lam' := by
    refine GlobalTheory.JetPoint.jetMap_mem hab n _ _ (fun ap => ?_) _
    have : VV ℂ lam ≤ (VV ℂ lam').comap (T ap) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨f, hf, rfl⟩
      exact Submodule.subset_span ⟨_, fun τ => subOne_mem hab (hw τ) (hg τ) (ap τ) (hf τ), substAdj_ten hab ap n f⟩
    exact this v.2
  rw [normSq_eq, normSq_eq, GlobalTheory.JetPoint.coe_jetOp _ _ _ _ _ hmem]
  set w := jetMap (jetC cD G) n (v : Pol ℂ ι a) with hwdef
  have hE : 0 < ∏ τ, eN (lam τ) := Finset.prod_pos fun τ _ => eN_pos _
  have hE' : 0 < ∏ τ, eN (lam' τ) := Finset.prod_pos fun τ _ => eN_pos _
  have hv0 : 0 ≤ (fockL (v : Pol ℂ ι a) (v : Pol ℂ ι a)).re := (Complex.le_def.mp (fockL_nonneg _)).1
  have ht0 : 0 ≤ tmax b ν Om S := by
    unfold tmax
    refine mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun τ _ => ?_)
    have := hOm τ
    positivity
  by_cases hw0 : w = 0
  · rw [hw0, map_zero, Complex.zero_re, zero_div]
    positivity
  have hv1 : (v : Pol ℂ ι a) ≠ 0 := fun h => hw0 (by rw [hwdef, h, map_zero])
  have hpos : ∀ {k : ℕ} {p : Pol ℂ ι k}, p ≠ 0 → 0 < (fockL p p).re := fun {k p} hp => by
    rw [← fockF_eq]
    exact (fockPos _ p hp).1
  set Nw := (fockL w w).re with hNw
  set Nv := (fockL (v : Pol ℂ ι a) (v : Pol ℂ ι a)).re with hNv
  have hNw0 : 0 < Nw := hpos hw0
  have hNv0 : 0 < Nv := hpos hv1
  set D := Nw * ((∏ τ, eN (lam' τ)) / (∏ τ, eN (lam τ)) * Nv) with hD
  have hD0 : 0 < D := by positivity
  have hnorm : ∀ q, ‖((((√D)⁻¹ : ℝ) : ℂ) • fockL w) q‖ ^ 2 = ‖fockL w q‖ ^ 2 / D := fun q => by
    rw [LinearMap.smul_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt hD0.le, div_eq_inv_mul]
  have key := scalar_block hab lam ν lam' s' s hw G S r Om cD hG hr hS hOm hc v.2
    ((((√D)⁻¹ : ℝ) : ℂ) • fockL w) (fun ap => by
      have h1 := fock_tensor_le lam (fun τ => subOne hab (ap τ) (n τ)) _
        (fun τ f hf => subOne_le hab (hw τ) (hg τ) (ap τ) hf) (T ap) (substAdj_ten hab ap n) v.2
      refine le_of_sq_le_sq ?_ (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ =>
        pow_nonneg ((fock_subst_le hab _).choose_spec.1 i) _)
      rw [hnorm, div_le_iff₀ hD0]
      refine (norm_fockL_sq_le _ _).trans ((mul_le_mul_of_nonneg_left h1 hNw0.le).trans (le_of_eq ?_))
      rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_pow, hD]
      ring)
  have hww : fockL w w = (Nw : ℂ) :=
    Complex.ext (by simp [hNw]) (by simpa using (Complex.le_def.mp (fockL_nonneg w)).2.symm)
  rw [hnorm, ← hwdef, hww, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_le_iff₀ hD0, hD, sq,
    mul_left_comm] at key
  have h2 := le_of_mul_le_mul_left key hNw0
  rw [div_le_iff₀ hE']
  refine h2.trans (le_of_eq ?_)
  ring

end GlobalTheory.JetBlock
