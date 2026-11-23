import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthNormLogBoundIffOrthBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingAdmissibleFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLastZeroInclusion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLastRowMonomialReadsCoefficient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingListCharacterProduct
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColAddGenRenameCastSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br
open scoped ComplexOrder Matrix

noncomputable section

namespace GlobalTheory.BranchNorm

section One

open Formalism.GradedWeylDivisibility GlobalTheory.BrCompare

variable {K : Type} [Field K] {n : ℕ}

open GlobalTheory.Branching.AddColumn in

theorem incl_mem (ν : Fin (n + 1) → ℕ) (hν : ν (Fin.last n) = 0) (f : MvPolynomial (Fin (n + 1) × Fin n) K)
    (hf : f ∈ dualWeyl K (n + 1) n fun i => ν i.castSucc) : BrCompare.incl K n f ∈ dualWeyl K (n + 1) (n + 1) ν := by
  unfold BrCompare.incl
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf ⊢
  refine ⟨fun d hd => ?_, fun l j hlj => ?_⟩
  · obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hd
    have h := hf.1 hu
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [(weight_mapDomain (n + 1) n u).2, hν]
    · rw [(weight_mapDomain (n + 1) n u).1, h]
  · induction j using Fin.lastCases with
    | last => exact colAddGen_rename_last K l f
    | cast j =>
      induction l using Fin.lastCases with
      | last => exact absurd hlj (not_lt.2 (Fin.le_last _))
      | cast l =>
        rw [colAddGen_rename_castSucc, hf.2 l j (Fin.castSucc_lt_castSucc_iff.1 hlj), rename_rename, rename_rename]
        rfl

variable {lam : DomWeight (n + 1)} {sg : DomWeight n}

theorem natW_last : lam.natW (Fin.last n) = 0 := by simp [DomWeight.natW, detShift_succ]

theorem xi_mem (hI : Interlace rfl lam sg) (hS : SameShift lam sg) : xiBr K rfl lam sg ∈ nablaSq K (n + 1) lam := by
  obtain ⟨h1, -, -, -, h5⟩ := shifted_branching_list_character n lam sg ((interlace_iff _ _).1 hI) ((sameShift_iff _ _).1 hS).1
  rw [h5]
  exact incl_mem _ natW_last _ (Formalism.BranchingDeterminantCap.bmLift_xi _ _ (Formalism.BranchingDeterminantCap.bm_IL_of _ _ h1)).1

theorem fock_xi_one [CharZero K] (hI : Interlace rfl lam sg) (hS : SameShift lam sg)
    {x : MvPolynomial (Fin (n + 1) × Fin (n + 1)) K} (hx : x ∈ nablaSq K (n + 1) lam) :
    fockB x (xiBr K rfl lam sg) * fockB (extremal K n sg) (extremal K n sg) =
      fockB (xiBr K rfl lam sg) (xiBr K rfl lam sg) *
        fockB (coefOne K n (fun s => (bBr rfl lam sg s).toNat) x) (extremal K n sg) := by
  obtain ⟨h1, -, -, h4, h5⟩ := shifted_branching_list_character n lam sg ((interlace_iff _ _).1 hI) ((sameShift_iff _ _).1 hS).1
  obtain ⟨x', hx', rfl⟩ := exists_eq_incl_of_last_eq_zero K n lam.natW natW_last x hx
  have h := fock_xi h1 x' hx'
  rw [(GlobalTheory.BrCoefFock.fockB_zmon_emb K n _).1] at h
  have hb : ((bfact fun s => lamN lam s - sg.natW s : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun s _ => Nat.factorial_ne_zero _)
  rw [h5, fockB_incl, fockB_incl, funext h4]
  refine mul_right_cancel₀ hb ?_
  unfold extremal
  linear_combination h

theorem coefOne_xi (hI : Interlace rfl lam sg) (hS : SameShift lam sg) :
    coefOne K n (fun s => (bBr rfl lam sg s).toNat) (xiBr K rfl lam sg) = extremal K n sg := by
  have h := GlobalTheory.XiTopCoef.coefLast_xi K _ n rfl lam sg hI hS
  unfold coefOne
  exact (congrArg _ h).trans (GlobalTheory.BranchFormula.rename_snd_unit _)

theorem xi_ne (hI : Interlace rfl lam sg) (hS : SameShift lam sg) : xiBr K rfl lam sg ≠ 0 := by
  intro h0
  have h := coefOne_xi (K := K) hI hS
  rw [h0] at h
  exact Formalism.GradedWeylDivisibility.hwNe K n n le_rfl sg.natW (h.symm.trans (by simp [coefOne]))

theorem cBr_ne (hI : Interlace rfl lam sg) : cBr rfl lam sg ≠ 0 := by
  have h := (Formalism.BranchingDeterminantCap.capConst n lam.w sg.w fun i => by
    have := (interlace_iff _ _).1 hI i
    exact ⟨this.2, this.1⟩).1
  convert h using 1
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => ?_
  ring

theorem fockB_pos {σ : Type} {f : MvPolynomial σ ℝ} (hf : f ≠ 0) : 0 < fockB f f := by
  refine Finset.sum_pos (fun m hm => mul_pos (mul_self_pos.2 (mem_support_iff.1 hm)) ?_) (support_nonempty.2 hf)
  exact Nat.cast_pos.2 (Finset.prod_pos fun _ _ => Nat.factorial_pos _)

theorem kapBr_pos (hI : Interlace rfl lam sg) (hS : SameShift lam sg) : 0 < kapBr ℝ rfl lam sg :=
  div_pos (fockB_pos (xi_ne hI hS)) (fockB_pos (Formalism.GradedWeylDivisibility.hwNe ℝ _ _ le_rfl _))

theorem kapBr_map {L : Type} [Field L] (φ : K →+* L) : φ (kapBr K rfl lam sg) = kapBr L rfl lam sg := by
  simp only [kapBr, map_div₀, ← GlobalTheory.Proof.TensorMapDescent.fockB_map, GlobalTheory.Proof.TensorMapDescent.xiBr_map, Formalism.L2.DIV.map_extremal]

end One

section Bilinear

open GlobalTheory.BrCompare GlobalTheory.BranchFormula

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ}
  {lam : ι → DomWeight (n + 1)} {sg : ι → DomWeight n}

variable (K sg) in

def hiV : VV K sg := ⟨extVV K sg, extVV_mem K sg⟩

variable (K) in

def xiV (hI : ∀ τ, Interlace rfl (lam τ) (sg τ)) (hS : ∀ τ, SameShift (lam τ) (sg τ)) : VV K lam :=
  ⟨ten fun τ => xiBr K rfl (lam τ) (sg τ), Submodule.subset_span ⟨_, fun τ => xi_mem (hI τ) (hS τ), rfl⟩⟩

variable (K lam sg) in

def tr : VV K sg →ₗ[K] VV K lam :=
  (LinearMap.BilinForm.toDual (pairBK (K := K) lam) (pairingBNondegenerate_holds K ι _ lam)).symm.toLinearMap ∘ₗ
    (brStd rfl lam sg).dualMap ∘ₗ pairBK sg

theorem pair_tr (y : VV K sg) (x : VV K lam) :
    pairBK lam (tr K lam sg y) x = pairBK sg y (brStd rfl lam sg x) := by
  simp [tr, LinearMap.BilinForm.apply_toDual_symm_apply]

theorem ext_pair {m : ℕ} {w : ι → DomWeight m} {x y : VV K w} (h : ∀ z, pairBK w x z = pairBK w y z) : x = y := by
  rw [← sub_eq_zero]
  exact (pairingBNondegenerate_holds K ι m w).1 _ fun z => by rw [map_sub, LinearMap.sub_apply, h, sub_self]

variable (hI : ∀ τ, Interlace rfl (lam τ) (sg τ)) (hS : ∀ τ, SameShift (lam τ) (sg τ))
include hI hS

theorem pair_hi {F : Pol K ι (n + 1)} (hF : F ∈ VV K lam) :
    (∏ τ, ((cBr rfl (lam τ) (sg τ) : ℤ) : K)) * pairB lam F (ten fun τ => xiBr K rfl (lam τ) (sg τ)) =
      pairB sg (brStdP rfl lam sg F : Pol K ι n) (extVV K sg) := by
  induction hF using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, rfl⟩ := hy
    change _ * pairB lam (ten f) _ = pairB sg (brStdP rfl lam sg (ten f) : Pol K ι n) _
    simp only [pairB_apply, brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul]
    rw [← fockBL_apply (_ • _), map_smul, LinearMap.smul_apply, fockBL_apply,
      GlobalTheory.BranchFormula.fockB_projVV sg _ (extVV_mem K sg), GlobalTheory.BrCompare.coefLast_ten, extVV,
      GlobalTheory.BrCompare.fockB_ten, GlobalTheory.BrCompare.fockB_ten, brConst, extNormB, extNormB, smul_eq_mul, ← Finset.prod_inv_distrib,
      ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have h := fock_xi_one (hI τ) (hS τ) (hf τ)
    have h1 := fock_extremal_ne (K := K) (lam τ)
    have h2 := fock_extremal_ne (K := K) (sg τ)
    unfold coefOne at h
    unfold kapBr bExp
    field_simp
    linear_combination ((cBr rfl (lam τ) (sg τ) : ℤ) : K) * h
  | zero => simp
  | add y z _ _ hy hz => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, mul_add, hy, hz]
  | smul a y _ hy => simp only [map_smul, LinearMap.smul_apply, Submodule.coe_smul, ← hy, smul_eq_mul]; ring

theorem tr_hi : tr K lam sg (hiV K sg) = (∏ τ, ((cBr rfl (lam τ) (sg τ) : ℤ) : K)) • xiV K hI hS := by
  refine ext_pair fun z => ?_
  rw [pair_tr, map_smul, LinearMap.smul_apply, smul_eq_mul, pairBK_apply, pairBK_apply, pairingBSymm_holds,
    pairingBSymm_holds K ι _ lam]
  exact (pair_hi hI hS z.2).symm

theorem br_xi : brStd rfl lam sg (xiV K hI hS) = brConst rfl K lam sg • hiV K sg := by
  simp only [brStd, brStdP, LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply, xiV]
  rw [GlobalTheory.BrCompare.coefLast_ten, ← projVV_coe sg (hiV K sg)]
  congr 3
  funext τ
  exact coefOne_xi (hI τ) (hS τ)

omit [CharZero K] hI hS in
theorem pairBK_adj {m : ℕ} (w : ι → DomWeight m) (g : ι → GL (Fin m) K) (x y : VV K w) :
    pairBK w (rhoK w g x) y = pairBK w x (rhoK w (invTrK g)⁻¹ y) := by
  rw [pairBK_apply, pairBK_apply, rhoK_coe, rhoK_coe, pairB_adj]

theorem tr_rhoK (g : ι → GL (Fin n) K) (g' : ι → GL (Fin (n + 1)) K)
    (h : ∀ τ, IsBlock rfl (g' τ : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (g τ : Matrix (Fin n) (Fin n) K) 1)
    (y : VV K sg) : tr K lam sg (rhoK sg g y) = rhoK lam g' (tr K lam sg y) := by
  refine ext_pair fun z => ?_
  rw [pair_tr, pairBK_adj, pairBK_adj, pair_tr,
    brStd_rhoK rfl hI hS (invTrK g)⁻¹ (invTrK g')⁻¹ (fun _ => 1) fun τ => (h τ).transpose]
  simp

theorem br_tr (y : VV K sg) : brStd rfl lam sg (tr K lam sg y) =
    ((∏ τ, ((cBr rfl (lam τ) (sg τ) : ℤ) : K)) * brConst rfl K lam sg) • y := by
  obtain ⟨y, hy⟩ := y
  have hy' := hy
  rw [GlobalTheory.OrbitSpan.VV_eq_span_orbit] at hy'
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    choose g' hg' using fun τ => exists_block (g τ) (one_ne_zero (α := K))
    change brStd rfl lam sg (tr K lam sg (rhoK sg g (hiV K sg))) = _ • rhoK sg g (hiV K sg)
    rw [tr_rhoK hI hS g g' hg', brStd_rhoK rfl hI hS g g' (fun _ => 1) hg', tr_hi hI hS, map_smul, br_xi]
    simp [smul_smul]
  | zero => change brStd rfl lam sg (tr K lam sg 0) = _ • 0; simp
  | add x z hx hz h1 h2 =>
    rw [← GlobalTheory.OrbitSpan.VV_eq_span_orbit] at hx hz
    change brStd rfl lam sg (tr K lam sg (⟨x, hx⟩ + ⟨z, hz⟩)) = _ • (⟨x, hx⟩ + ⟨z, hz⟩ : VV K sg)
    rw [map_add, map_add, h1, h2, smul_add]
  | smul a x hx h1 =>
    rw [← GlobalTheory.OrbitSpan.VV_eq_span_orbit] at hx
    change brStd rfl lam sg (tr K lam sg (a • ⟨x, hx⟩)) = _ • (a • ⟨x, hx⟩ : VV K sg)
    rw [map_smul, map_smul, h1, smul_comm]

end Bilinear

section Abstract

variable {K V W : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem norm_le (s : K →+* ℂ) (hs : ∀ x, s (star x) = star (s x)) (B : V →ₗ⋆[K] V →ₗ[K] K) (B' : W →ₗ⋆[K] W →ₗ[K] K)
    (hB : ∀ x y, star (B x y) = B y x) (hB' : ∀ x y, star (B' x y) = B' y x) (hpos : ∀ x, 0 ≤ (s (B x x)).re)
    (P : V →ₗ[K] W) (A : W →ₗ[K] V) (hA : ∀ y x, B (A y) x = B' y (P x)) {k : K} {κ : ℝ} (hk : s k = κ) (hκ : 0 < κ)
    (hPA : ∀ y, P (A y) = k • y) (f : V) : (s (B' (P f) (P f))).re ≤ κ * (s (B f f)).re := by
  have h := hpos (k • f - A (P f))
  have e1 : B f (A (P f)) = B' (P f) (P f) := by rw [← hB, hA, hB']
  have e2 : s (star k) = κ := by rw [hs, hk]; simp
  simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hA, hPA, e1,
    starRingEnd_apply, RingHom.id_apply, map_mul, hk, e2, Complex.sub_re, Complex.re_ofReal_mul] at h
  nlinarith

end Abstract

section Hermitian

open GlobalTheory.BrCompare GlobalTheory.BranchFormula GlobalTheory.IndefiniteRowSideFullHecke.ScaledCoisometryNorms

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι]

def cV {m : ℕ} (w : ι → DomWeight m) (x : VV K w) : VV K w :=
  ⟨map (starRingEnd K) x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ w _ x.2⟩

theorem cV_cV {m : ℕ} (w : ι → DomWeight m) (x : VV K w) : cV w (cV w x) = x := by
  apply Subtype.ext
  change map _ (map _ x.1) = x.1
  rw [map_map, show (starRingEnd K).comp (starRingEnd K) = RingHom.id K from RingHom.ext fun a => star_star a, map_id]

theorem pairBK_cV {m : ℕ} (w : ι → DomWeight m) (x y : VV K w) :
    pairBK w (cV w x) (cV w y) = star (pairBK w x y) := by
  rw [pairBK_apply, pairBK_apply, pairB_apply, pairB_apply, ← starRingEnd_apply, map_mul, map_inv₀,
    ← GlobalTheory.Proof.TensorMapDescent.fockB_map, extNormB, map_prod]
  simp only [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]
  rfl

theorem pairK_eq {m : ℕ} (w : ι → DomWeight m) (G : ι → GL (Fin m) K) (x y : VV K w) :
    pairK w (fun τ => (G τ : Matrix (Fin m) (Fin m) K)) x y = pairBK w (cV w x) (rhoK w G y) := by
  rw [pairK_apply, pairP_eq_pairB, pairBK_apply, rhoK_coe]
  rfl

theorem pairK_pos (s : K →+* ℂ) (hs : ∀ x, s (star x) = star (s x)) {m : ℕ} (w : ι → DomWeight m)
    {G : ι → Matrix (Fin m) (Fin m) K} (hG : ∀ τ, ((G τ).map s).PosDef) (x : VV K w) :
    0 ≤ (s (pairK w G x x)).re := by
  rw [← GlobalTheory.CoefModel.pairK_mapVV s w hs]
  by_cases h : GlobalTheory.CoefModel.mapVV s w x = 0
  · simp [h]
  · exact (Complex.lt_def.1 (GlobalTheory.CoefModel.pairK_pos w hG _ h)).1.le

theorem pairK_star (s : K →+* ℂ) (hs : ∀ x, s (star x) = star (s x)) {m : ℕ} (w : ι → DomWeight m)
    {G : ι → Matrix (Fin m) (Fin m) K} (hG : ∀ τ, ((G τ).map s).PosDef) (x y : VV K w) :
    star (pairK w G x y) = pairK w G y x :=
  (pairSymm K ι m w G fun τ => by
    ext a b
    apply s.injective
    rw [Matrix.conjTranspose_apply, hs]
    exact (hG τ).isHermitian.apply a b).eq x y

omit [StarRing K] in
theorem exists_GL (s : K →+* ℂ) {m : ℕ} {G : Matrix (Fin m) (Fin m) K} (hG : (G.map s).PosDef) :
    ∃ g : GL (Fin m) K, (g : Matrix (Fin m) (Fin m) K) = G := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero G fun h => hG.det_pos.ne' ?_, rfl⟩
  have := s.map_det G
  rw [h, map_zero] at this
  exact this.symm

theorem IsBlock.posDef {n : ℕ} {A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {A : Matrix (Fin n) (Fin n) ℂ} {t : ℂ}
    (h : IsBlock rfl A' A t) (hA : A.PosDef) (ht : 0 < t) : A'.PosDef := by
  have h1 : ∀ a b : Fin n, A' a.castSucc b.castSucc = A a b := h.1
  have h2 : ∀ a : Fin n, A' a.castSucc (Fin.last n) = 0 := fun a => (h.2.1 a).1
  have h3 : ∀ a : Fin n, A' (Fin.last n) a.castSucc = 0 := fun a => (h.2.1 a).2
  have h4 : A' (Fin.last n) (Fin.last n) = t := h.2.2
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext a b
    rw [Matrix.conjTranspose_apply]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases
    · rw [h4]; exact (IsSelfAdjoint.of_nonneg ht.le).star_eq
    · simp [h2, h3]
    · simp [h2, h3]
    · rw [h1, h1]; exact hA.isHermitian.apply _ _
  · have e : star x ⬝ᵥ A' *ᵥ x = star (fun a : Fin n => x a.castSucc) ⬝ᵥ A *ᵥ (fun a : Fin n => x a.castSucc) +
        t * (star (x (Fin.last n)) * x (Fin.last n)) := by
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_castSucc, h1, h2, h3, h4, Pi.star_apply, zero_mul, add_zero,
        Finset.sum_const_zero, zero_add]
      ring
    rw [e]
    by_cases h0 : (fun a : Fin n => x a.castSucc) = 0
    · have h5 : x (Fin.last n) ≠ 0 := fun h5 => hx (funext fun a => Fin.lastCases h5 (fun a => congrFun h0 a) a)
      exact add_pos_of_nonneg_of_pos (hA.posSemidef.dotProduct_mulVec_nonneg _)
        (mul_pos ht (star_mul_self_pos (IsRegular.of_ne_zero h5)))
    · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos h0) (mul_nonneg ht.le (star_mul_self_nonneg _))

variable [CharZero K] {n : ℕ} {lam : ι → DomWeight (n + 1)} {sg : ι → DomWeight n}

theorem br_cV (x : VV K lam) : brStd rfl lam sg (cV lam x) = cV sg (brStd rfl lam sg x) :=
  Subtype.ext (GlobalTheory.Proof.TensorMapDescent.branchingProjection_map (starRingEnd K) rfl lam sg x.1)

theorem tr_cV (y : VV K sg) : cV lam (tr K lam sg y) = tr K lam sg (cV sg y) := by
  refine ext_pair fun z => ?_
  rw [← cV_cV lam z, pairBK_cV, pair_tr, pair_tr, br_cV, br_cV, pairBK_cV, br_cV]

theorem adjoint (hI : ∀ τ, Interlace rfl (lam τ) (sg τ)) (hS : ∀ τ, SameShift (lam τ) (sg τ))
    (G' : ι → GL (Fin n) K) (G : ι → GL (Fin (n + 1)) K) (g t : ι → K) (hg : ∀ τ, g τ ≠ 0)
    (h : ∀ τ, IsBlock rfl (G τ : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (G' τ : Matrix (Fin n) (Fin n) K) (g τ))
    (y : VV K sg) (x : VV K lam) :
    pairK lam (fun τ => (G τ : Matrix (Fin (n + 1)) (Fin (n + 1)) K))
        ((star (∏ τ, (t τ * g τ) ^ (-nBr (lam τ) (sg τ))) • tr K lam sg) y) x =
      pairK sg (fun τ => (G' τ : Matrix (Fin n) (Fin n) K)) y (brAt rfl lam sg t x) := by
  rw [LinearMap.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, brAt,
    LinearMap.smul_apply, map_smul, pairK_eq, pairK_eq, tr_cV, pair_tr, brStd_rhoK rfl hI hS G' G g h, map_smul,
    smul_smul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [mul_zpow, mul_assoc, ← zpow_add₀ (hg τ), neg_add_cancel, zpow_zero, mul_one]

end Hermitian

open GlobalTheory.IndefiniteRowSideFullHecke.ScaledCoisometryNorms GlobalTheory.BranchFormula in
theorem brNorm : BrNorm := by
  intro K _ _ s hs ι _ N n hN lam sg hI hS G' hG' g t T hT ht
  subst hN
  have : CharZero K := (RingHom.charZero_iff s.injective).2 inferInstance
  have ht0 : ∀ τ, 0 < ‖s (t τ)‖ ^ 2 := fun τ => by
    refine lt_of_le_of_ne (sq_nonneg _) fun h => hT.ne' ?_
    have := ht τ
    rw [← h] at this
    exact_mod_cast (by simpa using this.symm : (T : ℂ) = 0)
  have hg : ∀ τ, s (g τ) = ((T / ‖s (t τ)‖ ^ 2 : ℝ) : ℂ) := fun τ => by
    rw [Complex.ofReal_div, ← ht τ, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.2 (ht0 τ).ne')]
  have hg0 : ∀ τ, 0 < s (g τ) := fun τ => by rw [hg]; exact Complex.zero_lt_real.2 (div_pos hT (ht0 τ))
  have hb : ∀ τ, IsBlock rfl (sumGram (n + 1) (G' τ) (g τ)) (G' τ) (g τ) := fun τ => sumGram_entries rfl _ _
  have hG : ∀ τ, ((sumGram (n + 1) (G' τ) (g τ)).map s).PosDef := fun τ =>
    IsBlock.posDef (A := (G' τ).map s) (t := s (g τ)) ⟨fun a b => congrArg s ((hb τ).1 a b),
      fun a => ⟨(congrArg s ((hb τ).2.1 a).1).trans (map_zero s), (congrArg s ((hb τ).2.1 a).2).trans (map_zero s)⟩,
      congrArg s (hb τ).2.2⟩ (hG' τ) (hg0 τ)
  choose u' hu' using fun τ => exists_GL s (hG' τ)
  choose u hu using fun τ => exists_GL s (hG τ)
  have hA := adjoint hI hS u' u g t (fun τ h => (hg0 τ).ne' (by rw [h, map_zero])) fun τ => by rw [hu, hu']; exact hb τ
  simp only [hu, hu'] at hA
  set A := star (∏ τ, (t τ * g τ) ^ (-nBr (lam τ) (sg τ))) • tr K lam sg with hAdef
  set k : K := (∏ τ, t τ ^ (-nBr (lam τ) (sg τ))) * star (∏ τ, (t τ * g τ) ^ (-nBr (lam τ) (sg τ))) *
    ((∏ τ, ((cBr rfl (lam τ) (sg τ) : ℤ) : K)) * brConst rfl K lam sg) with hkdef
  have hPA : ∀ y, brAt rfl lam sg t (A y) = k • y := fun y => by
    rw [brAt, hAdef, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, br_tr hI hS, smul_smul, smul_smul]
  have hk : s k = (brSq rfl lam sg T : ℝ) := by
    simp only [hkdef, brSq, brConst, map_mul, map_prod, hs, star_prod, map_zpow₀, star_zpow₀, map_intCast, kapBr_map,
      Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have e1 : ((kapBr ℝ rfl (lam τ) (sg τ) : ℝ) : ℂ) = kapBr ℂ rfl (lam τ) (sg τ) := kapBr_map Complex.ofRealHom
    have e2 : s (t τ) * star (s (t τ) * s (g τ)) = (T : ℂ) := by
      rw [star_mul', (IsSelfAdjoint.of_nonneg (hg0 τ).le).star_eq, ← mul_assoc, ← ht τ, Complex.star_def,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← mul_zpow, e2]
    push_cast
    rw [e1]
    ring
  have hκ : 0 < brSq rfl lam sg T := Finset.prod_pos fun τ _ => mul_pos (zpow_pos hT _)
    (mul_pos (sq_pos_of_ne_zero (Int.cast_ne_zero.2 (cBr_ne (hI τ)))) (kapBr_pos (hI τ) (hS τ)))
  have hAA : ∀ y y', s (pairK lam (fun τ => sumGram (n + 1) (G' τ) (g τ)) (A y) (A y')) =
      (brSq rfl lam sg T : ℝ) * s (pairK sg G' y y') := fun y y' => by
    rw [hA, hPA, map_smul, smul_eq_mul, map_mul, hk]
  refine ⟨hκ, ⟨A, hA, hAA⟩, fun f => norm_le s hs _ _ (pairK_star s hs lam hG) (pairK_star s hs sg hG')
    (pairK_pos s hs lam hG) _ A hA hk hκ hPA f, A (hiV K sg), fun h0 => ?_, ?_⟩
  · have h1 := hPA (hiV K sg)
    rw [h0, map_zero] at h1
    rcases smul_eq_zero.1 h1.symm with h | h
    · rw [h, map_zero] at hk
      exact hκ.ne (by exact_mod_cast hk)
    · have h2 := pairingBExtremal_holds K ι n sg 1
      have h3 : extVV K sg = 0 := congrArg Subtype.val h
      rw [extVV, ten] at h3
      rw [ten, h3] at h2
      simp at h2
  · rw [nrmSq, nrmSq, hAA, hPA, map_smul, (pairK sg G').map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
      map_mul s k, hk, map_mul s, starRingEnd_apply, hs, hk]
    simp

theorem lastMapNorm : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.LastMapNorm := GlobalTheory.BrNormCompare.lastMapNorm_iff_brNorm.2 brNorm

end GlobalTheory.BranchNorm
