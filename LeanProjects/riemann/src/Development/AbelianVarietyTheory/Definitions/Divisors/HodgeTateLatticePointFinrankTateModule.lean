import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectivePairTOfLev
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.HtCharOfIsUnit

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

abbrev embC (C : Type) [Field C] {O : Type} [CommRing O] [Algebra O C] {Λ : Type} [CommRing Λ]
    {J : Type} (σ : J → Λ →+* O) : J → Λ →+* C := fun i => (algebraMap O C).comp (σ i)

section Independence

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
  (v : Valuation C ℝ≥0)

theorem latNorm_smul (La : Submodule O U) {c : C} (hc : c ≠ 0) (x : U) :
    latNorm v La (c • x) = v c * latNorm v La x := by
  have hpos : 0 < v c := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 hc)
  have e : {r | ∃ a : C, c • x ∈ scaleLat a La ∧ v a = r} =
      OrderIso.mulLeft₀ (v c) hpos '' {r | ∃ a : C, x ∈ scaleLat a La ∧ v a = r} := by
    ext r
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨y, hy, h⟩ := mem_scaleLat.1 ha
      refine ⟨_, ⟨c⁻¹ * a, mem_scaleLat.2 ⟨y, hy, ?_⟩, rfl⟩, ?_⟩
      · rw [mul_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]
      · change v c * v (c⁻¹ * a) = v a
        rw [← map_mul, mul_inv_cancel_left₀ hc]
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      obtain ⟨y, hy, h⟩ := mem_scaleLat.1 ha
      exact ⟨c * a, mem_scaleLat.2 ⟨y, hy, by rw [mul_smul, h]⟩, map_mul v c a⟩
  rw [latNorm, latNorm, e]
  rcases Set.eq_empty_or_nonempty {r | ∃ a : C, x ∈ scaleLat a La ∧ v a = r} with h | h
  · rw [h, Set.image_empty, NNReal.sInf_empty, mul_zero]
  · exact (OrderIso.map_csInf' _ h (OrderBot.bddBelow _)).symm

theorem exists_grNorm_eq_mul {f f' : Fin N → U} (h : ∀ i, step C f' i = step C f i) (k : Fin N)
    (hk : f' k ∉ step C f' k) :
    ∃ c : C, c ≠ 0 ∧ ∀ La : Submodule O U, grNorm v La f' k = v c * grNorm v La f k := by
  have h1 : (step C f k).mkQ (f' k) ∈ Submodule.span C {(step C f k).mkQ (f k)} := by
    rw [← map_mkQ_step_succ, ← h (k + 1)]
    exact Submodule.mem_map_of_mem (mem_step_succ f' k)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, eq_comm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← h] at hc
    exact hk hc
  refine ⟨c, hc0, fun La => ?_⟩
  have key : ∀ F' F : Submodule C U, step C f' k = F' → step C f' (k + 1) = F →
      grNorm v La f' k = latNorm v (grLat La F' F) (F'.mkQ (f' k)) := by
    rintro _ _ rfl rfl
    rfl
  rw [key _ _ (h _) (h _), ← hc, latNorm_smul v _ hc0]
  rfl

variable {U' : Type} [AddCommGroup U'] [Module C U'] [Module O U'] [IsScalarTower O C U']

theorem phiAt_vp_sub_eq (p : ℕ) (al : U →ₗ[C] U') {U₁ : Submodule C U} {j : ℕ}
    (F F' : AdaptedFrame (LinearMap.ker al ⊓ U₁) U₁ N j) (h : ∀ i, step C F'.f i = step C F.f i)
    (LW LW' : Submodule O U) (Lom Lom' : Submodule O U') (lam : Fin N → ℝ)
    (hW : ∀ k : Fin N, (k : ℕ) < j → grNorm v LW F.f k ≠ 0 ∧ grNorm v LW' F.f k ≠ 0)
    (hom : ∀ k : Fin N, j ≤ k → grNorm v Lom (al ∘ F.f) k ≠ 0 ∧ grNorm v Lom' (al ∘ F.f) k ≠ 0) :
    phiAt_vp p v al LW Lom F'.f j lam - phiAt_vp p v al LW' Lom' F'.f j lam =
      phiAt_vp p v al LW Lom F.f j lam - phiAt_vp p v al LW' Lom' F.f j lam := by
  simp only [phiAt_vp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : (k : ℕ) < j
  · obtain ⟨c, hc, e⟩ := exists_grNorm_eq_mul (O := O) v h k (F'.notMem_step k)
    have hc' := (Valuation.ne_zero_iff v).2 hc
    simp only [if_pos hk, e, logAbs_vp_mul p v hc' (hW k hk).1, logAbs_vp_mul p v hc' (hW k hk).2]
    ring
  · obtain ⟨c, hc, e⟩ := exists_grNorm_eq_mul (O := O) v (f := al ∘ F.f) (f' := al ∘ F'.f)
      (fun i => by rw [← map_step, ← map_step, h]) k (F'.map_notMem_step al k (not_lt.1 hk))
    have hc' := (Valuation.ne_zero_iff v).2 hc
    simp only [if_neg hk, e, logAbs_vp_mul p v hc' (hom k (not_lt.1 hk)).1,
      logAbs_vp_mul p v hc' (hom k (not_lt.1 hk)).2]
    ring

end Independence

namespace Point

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

section Free

variable [IsAlgClosed C] [CharZero C]

theorem card_torsion (n : ℕ) :
    Nat.card {x : Pts P.A.A // x ^ p ^ n = 1} = p ^ (2 * P.A.g * n) := by
  have h := (GlobalTheory.firstFiveLaws.1.mulN (Sp C) P.A (p ^ n) (one_le_ppow p n)).2.2.2.2 C (𝟙 _)
    (Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  rw [← pow_mul, mul_comm n] at h
  exact h

theorem nonempty_T_equiv : Nonempty (P.T ≃ₗ[ℤ_[p]] (Fin (2 * P.A.g) → ℤ_[p])) :=
  (tate_free_of_card p _ _ P.card_torsion).1

instance : Module.Free ℤ_[p] P.T := .of_equiv P.nonempty_T_equiv.some.symm

instance : Module.Finite ℤ_[p] P.T := .equiv P.nonempty_T_equiv.some.symm

theorem hodgeTateLatticePoint_finrank_tateModule : Module.finrank ℤ_[p] P.T = 2 * P.A.g := by
  rw [P.nonempty_T_equiv.some.finrank_eq, Module.finrank_fin_fun]

theorem pairT_bijective : Function.Bijective (pairT P.A P.eps) :=
  (bijective_pairT_of_lev p C P.A P.eps (tate_free_of_card p _ _ P.card_torsion).2.1
    (tate_free_of_card p _ _ P.card_torsion).2.2).2

end Free

abbrev OmC : Type := C ⊗[O] omega P.Gt

def actOm : Λ →+* Module.End C P.OmC := baseChangeAction C (omegaAct P.oGt)

def inclOm : omega P.Gt →ₗ[O] P.OmC := TensorProduct.mk O C _ 1

def latOm : Submodule O P.OmC := LinearMap.range P.inclOm

variable [Algebra ℤ_[p] C]

abbrev V : Type := C ⊗[ℤ_[p]] P.T

def actV : Λ →+* Module.End C P.V := baseChangeAction C P.actT

section Pairing

variable [IsAlgClosed C] [CharZero C]

def pairV : LinearMap.BilinForm C P.V := (pairT P.A P.eps).baseChange C

theorem pairV_tmul (c d : C) (s t : P.T) :
    P.pairV (c ⊗ₜ s) (d ⊗ₜ t) = pairT P.A P.eps s t • (c * d) := rfl

theorem pairV_act (a : Λ) (x y : P.V) :
    P.pairV (P.actV a x) y = P.pairV x (P.actV (star a) y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul c s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul d t => exact congrArg (· • (c * d)) (pairT_act P.oA P.eps a s t)

theorem pairV_swap (x y : P.V) : P.pairV x y = -P.pairV y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', neg_add]
  | tmul c s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy', neg_add]
    | tmul d t => rw [pairV_tmul, pairV_tmul, ← (isAlt_pairT P.A P.eps).neg_eq t s, neg_smul, mul_comm]

theorem isAlt_pairV : P.pairV.IsAlt := fun x => by
  have h := P.pairV_swap x x
  exact self_eq_neg.1 h

theorem finrank_V : Module.finrank C P.V = 2 * P.A.g := by
  rw [Module.finrank_baseChange, hodgeTateLatticePoint_finrank_tateModule]

theorem exists_dual_bases : ∃ (n : ℕ) (e s : Module.Basis (Fin n) ℤ_[p] P.T),
    (∀ i t, pairT P.A P.eps (s i) t = e.repr t i) ∧
      ∀ (w : P.V) (j : Fin n), (s.baseChange C).repr w j = P.pairV w (1 ⊗ₜ e j) := by
  let e := Module.finBasis ℤ_[p] P.T
  let q := LinearEquiv.ofBijective _ P.pairT_bijective
  let s := e.dualBasis.map q.symm
  have h1 : ∀ i t, pairT P.A P.eps (s i) t = e.repr t i := fun i t =>
    (LinearMap.congr_fun (q.apply_symm_apply (e.dualBasis i)) t).trans (e.dualBasis_apply i t)
  refine ⟨_, e, s, h1, fun w j => ?_⟩
  have : (s.baseChange C).coord j = P.pairV.flip (1 ⊗ₜ e j) := (s.baseChange C).ext fun i => by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Module.Basis.baseChange_apply]
    change _ = P.pairV (1 ⊗ₜ s i) (1 ⊗ₜ e j)
    rw [pairV_tmul, h1, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  exact LinearMap.congr_fun this w

theorem existsUnique_pairV (l : P.T →ₗ[ℤ_[p]] C) : ∃! w : P.V, ∀ t, P.pairV w (1 ⊗ₜ t) = l t := by
  obtain ⟨n, e, s, h1, h2⟩ := P.exists_dual_bases
  refine ⟨∑ i, l (e i) ⊗ₜ s i, fun t => ?_, fun w hw => ?_⟩
  · conv_rhs => rw [← e.sum_repr t]
    simp only [map_sum, LinearMap.sum_apply, pairV_tmul, h1, map_smul, _root_.mul_one]
  · conv_lhs => rw [← (s.baseChange C).sum_repr w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2, hw, Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]

theorem eq_of_pairV {w w' : P.V} (h : ∀ t : P.T, P.pairV w (1 ⊗ₜ t) = P.pairV w' (1 ⊗ₜ t)) :
    w = w' :=
  (P.existsUnique_pairV (((P.pairV w').restrictScalars ℤ_[p]) ∘ₗ TensorProduct.mk ℤ_[p] C _ 1)).unique
    h fun _ => rfl

end Pairing

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

def inclT : O ⊗[ℤ_[p]] P.T →ₗ[O] P.V := (TensorProduct.mk ℤ_[p] C P.T 1).liftBaseChange O

def latT : Submodule O P.V := LinearMap.range P.inclT

theorem inclT_tmul (c : O) (t : P.T) : P.inclT (c ⊗ₜ t) = algebraMap O C c ⊗ₜ t := by
  rw [inclT, LinearMap.liftBaseChange_tmul, TensorProduct.mk_apply, TensorProduct.smul_tmul',
    Algebra.algebraMap_eq_smul_one]

theorem one_tmul_mem_latT (t : P.T) : (1 : C) ⊗ₜ t ∈ P.latT :=
  ⟨1 ⊗ₜ t, by rw [inclT_tmul, map_one]⟩

variable {J : Type} [DecidableEq J] {σ : J → Λ →+* O} (h : IsSplitting (embC C σ))

abbrev eigV (τ : Λ →+* O) : Submodule C P.V := eigenSub P.actV ((algebraMap O C).comp τ)

abbrev eigOm (τ : Λ →+* O) : Submodule C P.OmC := eigenSub P.actOm ((algebraMap O C).comp τ)

def latTQuot (i : J) : Submodule O P.V := eigQuotLat P.actV h i P.latT

def latTSub (τ : Λ →+* O) : Submodule O P.V := eigSubLat P.actV ((algebraMap O C).comp τ) P.latT

def omRec (i : J) : Submodule O P.OmC := eigQuotLat P.actOm h i P.latOm

theorem latTSub_le_latTQuot (i : J) : P.latTSub (σ i) ≤ P.latTQuot h i :=
  eigSubLat_le_eigQuotLat P.actV h i P.latT

variable [IsAlgClosed C] [CharZero C]

theorem fg_latT : P.latT.FG := Module.Finite.iff_fg.1 (Module.Finite.range P.inclT)

theorem fg_latTQuot (i : J) : (P.latTQuot h i).FG := P.fg_latT.map _

theorem mem_latT_iff (w : P.V) :
    w ∈ P.latT ↔ ∀ t : P.T, ∃ c : O, algebraMap O C c = P.pairV w (1 ⊗ₜ t) := by
  constructor
  · rintro ⟨x, rfl⟩ t
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, by rw [map_add, map_add, map_add, LinearMap.add_apply, hc, hd]⟩
    | tmul c s =>
      refine ⟨pairT P.A P.eps s t • c, ?_⟩
      rw [inclT_tmul, pairV_tmul, _root_.mul_one, Algebra.smul_def, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply]
  · intro hw
    obtain ⟨n, e, s, -, h2⟩ := P.exists_dual_bases
    rw [← (s.baseChange C).sum_repr w]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := hw (e i)
    rw [h2, ← hc, algebraMap_smul, Module.Basis.baseChange_apply]
    exact Submodule.smul_mem _ c (P.one_tmul_mem_latT _)

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

def alC : P.V →ₗ[C] P.OmC := (P.inclOm.restrictScalars ℤ_[p] ∘ₗ P.al₀).liftBaseChange C

theorem alC_tmul (c : C) (t : P.T) : P.alC (c ⊗ₜ t) = c ⊗ₜ P.al₀ t := by
  rw [alC, LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, LinearMap.restrictScalars_apply, inclOm,
    TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]

theorem alC_inclT (x : O ⊗[ℤ_[p]] P.T) : P.alC (P.inclT x) = P.inclOm (P.al x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c t =>
    rw [inclT_tmul, alC_tmul, al_tmul, inclOm, TensorProduct.mk_apply, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]

theorem isEquivariant_alC : IsEquivariant P.actV P.actOm P.alC := by
  intro a x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c t =>
    change P.alC (c ⊗ₜ P.actT a t) = P.actOm a (P.alC (c ⊗ₜ t))
    rw [alC_tmul, alC_tmul, al₀_act]
    rfl

def W : Submodule C P.V := LinearMap.ker P.alC

def eigW (τ : Λ →+* O) : Submodule C P.V := P.W ⊓ P.eigV τ

def omHTAll : Submodule O P.OmC := P.latT.map (P.alC.restrictScalars O)

def wHTAll : Submodule O P.V := P.latT ⊓ P.W.restrictScalars O

def omHT (i : J) : Submodule O P.OmC := (P.latTQuot h i).map (P.alC.restrictScalars O)

def wHT (i : J) : Submodule O P.V := P.latTQuot h i ⊓ (P.eigW (σ i)).restrictScalars O

theorem omHTAll_eq : P.omHTAll = (LinearMap.range P.al).map P.inclOm := by
  rw [omHTAll, latT, ← LinearMap.range_comp, ← LinearMap.range_comp]
  exact congrArg LinearMap.range (LinearMap.ext P.alC_inclT)

theorem omHTAll_le_latOm : P.omHTAll ≤ P.latOm := by
  rw [omHTAll_eq]
  exact LinearMap.map_le_range

theorem omHT_eq (i : J) : P.omHT h i = eigQuotLat P.actOm h i P.omHTAll :=
  map_eigQuotLat P.actV h P.isEquivariant_alC i P.latT

theorem omHT_le_omRec (i : J) : P.omHT h i ≤ P.omRec h i := by
  rw [omHT_eq]
  exact eigQuotLat_mono _ h i P.omHTAll_le_latOm

theorem fg_omHT (i : J) : (P.omHT h i).FG := (P.fg_latTQuot h i).map _

theorem fg_wHT (i : J) : (P.wHT h i).FG := fg_inf P.integers (P.fg_latTQuot h i) _

include h in

theorem iSup_eigW [Fintype J] : ⨆ i, P.eigW (σ i) = P.W := by
  refine le_antisymm (iSup_le fun i => inf_le_left) fun x hx => ?_
  rw [← sum_proj h P.actV x]
  refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨?_, proj_mem h P.actV i x⟩
  change P.alC _ = 0
  rw [P.isEquivariant_alC.proj h i x, show P.alC x = 0 from hx, map_zero]

def evalAl (x : LieG P.Gt) : P.T →ₗ[ℤ_[p]] C :=
  (Algebra.linearMap O C ∘ₗ LinearMap.proj x ∘ₗ (omega P.Gt).subtype).restrictScalars ℤ_[p] ∘ₗ P.al₀

def bLie (x : LieG P.Gt) : P.V := (P.existsUnique_pairV (P.evalAl x)).choose

theorem pairV_bLie (x : LieG P.Gt) (t : P.T) :
    P.pairV (P.bLie x) (1 ⊗ₜ t) = algebraMap O C ((P.al₀ t).1 x) :=
  (P.existsUnique_pairV (P.evalAl x)).choose_spec.1 t

theorem bLie_add (x y : LieG P.Gt) : P.bLie (lieAdd x y) = P.bLie x + P.bLie y :=
  P.eq_of_pairV fun t => by
    rw [map_add, LinearMap.add_apply, pairV_bLie, pairV_bLie, pairV_bLie, omega_lieAdd, map_add]

theorem bLie_zero : P.bLie (lieZero P.Gt) = 0 :=
  P.eq_of_pairV fun t => by
    rw [pairV_bLie, omega_lieZero, map_zero, map_zero, LinearMap.zero_apply]

theorem bLie_scale (c : O) (x : LieG P.Gt) : P.bLie (AvDefs.lieScale P.Gt c x) = c • P.bLie x :=
  P.eq_of_pairV fun t => by
    rw [← algebraMap_smul C c, map_smul, LinearMap.smul_apply, pairV_bLie, pairV_bLie,
      omega_lieScale, map_mul, smul_eq_mul]

theorem bLie_act (a : Λ) (x : LieG P.Gt) :
    P.bLie (AvDefs.lieAct P.Gt P.oGt a x) = P.actV a (P.bLie x) :=
  P.eq_of_pairV fun t => by
    rw [pairV_act, pairV_bLie]
    change _ = P.pairV _ (1 ⊗ₜ P.actT (star a) t)
    rw [pairV_bLie, al₀_act, omegaAct_apply, star_star]

theorem bLie_mem_latT (x : LieG P.Gt) : P.bLie x ∈ P.latT :=
  (P.mem_latT_iff _).2 fun t => ⟨_, (P.pairV_bLie x t).symm⟩

def latLie : Submodule O P.V where
  carrier := Set.range P.bLie
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨_, P.bLie_add x y⟩
  zero_mem' := ⟨_, P.bLie_zero⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl⟩
    exact ⟨_, P.bLie_scale c x⟩

def wRec (τ : Λ →+* O) : Submodule O P.V where
  carrier := {w | ∃ x : AvDefs.LieTau P.Gt P.oGt τ, P.bLie x.1 = w}
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨⟨_, isEig_lieAdd P.oGt x.2 y.2⟩, P.bLie_add x.1 y.1⟩
  zero_mem' := ⟨⟨_, isEig_lieZero P.oGt τ⟩, P.bLie_zero⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl⟩
    exact ⟨⟨_, isEig_lieScale P.oGt c x.2⟩, P.bLie_scale c x.1⟩

theorem latLie_le_latT : P.latLie ≤ P.latT := by
  rintro _ ⟨x, rfl⟩
  exact P.bLie_mem_latT x

theorem wRec_le (τ : Λ →+* O) :
    P.wRec τ ≤ eigSubLat P.actV ((algebraMap O C).comp τ) P.latLie := by
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨x.1, rfl⟩, mem_eigenSub.2 fun a => ?_⟩
  rw [← bLie_act, x.2 a, bLie_scale, RingHom.comp_apply, algebraMap_smul]

theorem wRec_le_latTSub (τ : Λ →+* O) : P.wRec τ ≤ P.latTSub τ :=
  (P.wRec_le τ).trans (eigSubLat_mono _ _ P.latLie_le_latT)

abbrev Frame (τ : Λ →+* O) (N j : ℕ) : Type := AdaptedFrame (P.eigW τ) (P.eigV τ) N j

theorem nonempty_frame (τ : Λ →+* O) :
    Nonempty (P.Frame τ (Module.finrank C (P.eigV τ)) (Module.finrank C (P.eigW τ))) :=
  nonempty_adaptedFrame inf_le_right

variable {P} {N j : ℕ}

def phi_vp (Ψ : Finset J) (F : ∀ i : Ψ, P.Frame (σ i) N j) (lam : Ψ → Fin N → ℝ)
    (LW : J → Submodule O P.V) (Lom : J → Submodule O P.OmC) : ℝ :=
  ∑ i : Ψ, phiAt_vp p v P.alC (LW i) (Lom i) (F i).f j (lam i)

def phiHT_vp (Ψ : Finset J) (F : ∀ i : Ψ, P.Frame (σ i) N j) (lam : Ψ → Fin N → ℝ) : ℝ :=
  phi_vp Ψ F lam (P.wHT h) (P.omHT h)

def phiRec_vp (Ψ : Finset J) (F : ∀ i : Ψ, P.Frame (σ i) N j) (lam : Ψ → Fin N → ℝ) : ℝ :=
  phi_vp Ψ F lam (fun i => P.wRec (σ i)) (P.omRec h)

omit [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] in
variable (P) in

theorem exists_smul_mem_latT (x : P.V) : ∃ a : O, a ≠ 0 ∧ a • x ∈ P.latT := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
  | tmul c t =>
    by_cases hc : v c ≤ 1
    · obtain ⟨b, rfl⟩ := P.integers.exists_of_le_one hc
      refine ⟨1, one_ne_zero, ?_⟩
      rw [one_smul, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ _ (P.one_tmul_mem_latT t)
    · have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      obtain ⟨b, hb⟩ := P.integers.exists_of_le_one (r := c⁻¹) (by
        rw [map_inv₀]; exact inv_le_one_of_one_le₀ (not_le.1 hc).le)
      refine ⟨b, ?_, ?_⟩
      · rintro rfl
        exact inv_ne_zero hc0 (by rw [← hb, map_zero])
      · rw [TensorProduct.smul_tmul', Algebra.smul_def, hb, inv_mul_cancel₀ hc0]
        exact P.one_tmul_mem_latT t

theorem exists_smul_mem_latTQuot (i : J) (F : P.Frame (σ i) N j) (k : Fin N) :
    ∃ a : C, a ≠ 0 ∧ a • F.f k ∈ P.latTQuot h i := by
  obtain ⟨a, ha, hx⟩ := P.exists_smul_mem_latT (F.f k)
  have hV : F.f k ∈ P.eigV (σ i) := (step_mono F.f k.2).trans F.step_N.le (mem_step_succ F.f k)
  refine ⟨algebraMap O C a, fun h0 => ha (P.integers.hom_inj (by rw [h0, map_zero])),
    P.latTSub_le_latTQuot h i ((mem_eigSubLat _).2 ⟨?_, Submodule.smul_mem _ _ hV⟩)⟩
  rw [algebraMap_smul]
  exact hx

theorem grAt_wHT (i : J) (F : P.Frame (σ i) N j) (k : Fin N) (hk : (k : ℕ) < j) :
    ∃ c : C, c ≠ 0 ∧
      grAt C (P.wHT h i) F.f k = Submodule.span O {c • (step C F.f k).mkQ (F.f k)} ∧
      grNorm v (P.wHT h i) F.f k = (v c)⁻¹ := by
  obtain ⟨a, ha, hT⟩ := exists_smul_mem_latTQuot h i F k
  have hW : F.f k ∈ P.eigW (σ i) := (step_mono F.f hk).trans F.step_j.le (mem_step_succ F.f k)
  refine exists_grAt_eq P.integers (P.fg_wHT h i) F.f k (F.notMem_step k) ha
    (Submodule.zero_mem _) ?_
  rw [add_zero]
  exact Submodule.mem_inf.2 ⟨hT, (P.eigW (σ i)).smul_mem a hW⟩

theorem grAt_omHT (i : J) (F : P.Frame (σ i) N j) (k : Fin N) (hk : j ≤ k) :
    ∃ c : C, c ≠ 0 ∧
      grAt C (P.omHT h i) (P.alC ∘ F.f) k =
        Submodule.span O {c • (step C (P.alC ∘ F.f) k).mkQ ((P.alC ∘ F.f) k)} ∧
      grNorm v (P.omHT h i) (P.alC ∘ F.f) k = (v c)⁻¹ := by
  obtain ⟨a, ha, hT⟩ := exists_smul_mem_latTQuot h i F k
  have hn := AdaptedFrame.map_notMem_step P.alC (U₁ := P.eigV (σ i)) F k hk
  refine exists_grAt_eq P.integers (P.fg_omHT h i) (P.alC ∘ F.f) k hn ha (Submodule.zero_mem _) ?_
  rw [add_zero, Function.comp_apply, ← map_smul]
  exact Submodule.mem_map_of_mem (f := P.alC.restrictScalars O) hT

end Point

section Inhabitants

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ]

theorem exists_oAct_polPull {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Out.PolAV S) (o : B.OAct Λ) :
    ∃ o' : (StrictPull.polPull B f).OAct Λ, ∀ a, (o'.act a).left ≫ pullback.fst B.A.hom f =
      pullback.fst B.A.hom f ≫ (o.act a).left :=
  polOActPull _ _ f B (StrictPull.polPull B f) _ (isGrpPullback_pullback B.A f)
    (PolBaseChange.lbIso_refl (StrictPull.polPull B f).isLB) Λ o

def ofGoodReduction (hv : v.Integers O) (ε : Eps p C) (B : Out.PolAV (Sp O)) (o : B.OAct Λ) :
    Point p v O Λ where
  integers := hv
  eps := ε
  A := StrictPull.polPull B (spMap (algebraMap O C))
  oA := (exists_oAct_polPull _ B o).choose
  G := B.A
  semi := isSemiAbelian_of_isAbelianScheme _ B.isAb
  gen := pullback.fst B.A.hom _
  gen_pull := isGrpPullback_pullback B.A _
  oG := o.toRingAct
  gen_act := (exists_oAct_polPull _ B o).choose_spec
  Ext := ZJ.splitExtOfAbelian B.A B.isAb
  Gt := B.A
  D := (ZJ.isGt_splitExtOfAbelian B.A B.isAb).some
  oGt := o.toRingAct
  cmp _ _ _ _ := MulEquiv.refl _
  cmp_nat _ _ _ _ _ _ _ _ _ _ := rfl
  cmp_act _ _ _ _ _ _ := rfl

def padicIntHom (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* 𝓞_ℂ_[p] :=
  ((algebraMap ℚ_[p] ℂ_[p]).comp (PadicInt.Coe.ringHom (p := p))).codRestrict 𝓞_ℂ_[p] fun x => by
    rw [GlobalTheory.PadicComplexHost.mem_iff_norm]
    change ‖algebraMap ℚ_[p] ℂ_[p] (x : ℚ_[p])‖ ≤ 1
    rw [norm_algebraMap']
    exact x.2

theorem exists_point_dim_one : ∃ (_ : Fact ¬IsUnit ((2 : ℕ) : 𝓞_ℂ_[2]))
    (_ : IsAdicComplete (Ideal.span {((2 : ℕ) : 𝓞_ℂ_[2])}) 𝓞_ℂ_[2]) (a₁ : Algebra ℤ_[2] 𝓞_ℂ_[2])
    (a₂ : Algebra ℤ_[2] ℂ_[2])
    (_ : @IsScalarTower ℤ_[2] 𝓞_ℂ_[2] ℂ_[2] a₁.toSMul Algebra.toSMul a₂.toSMul)
    (P : Point 2 (Valued.v : Valuation ℂ_[2] ℝ≥0) 𝓞_ℂ_[2] ℤ),
    P.A.g = 1 ∧ Module.finrank ℂ_[2] P.V = 2 ∧
      IsSplitting (embC ℂ_[2] fun _ : Unit => Int.castRingHom 𝓞_ℂ_[2]) := by
  let W : WeierstrassCurve ℤ_[2] := ⟨0, 0, 1, 0, 0⟩
  have hΔ : W.Δ = -27 := by
    norm_num [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have : W.IsElliptic := ⟨by
    rw [hΔ, PadicInt.isUnit_iff, norm_neg]
    exact_mod_cast (PadicInt.norm_natCast_eq_one_iff (p := 2) (n := 27)).2 (by norm_num)⟩
  obtain ⟨o, -⟩ := exists_oAct_int GlobalTheory.firstFiveLaws.1.cube _ (WeierstrassCurve.ellPolAV W)
  obtain ⟨o', -⟩ := exists_oAct_polPull (spMap (padicIntHom 2)) _ o
  obtain ⟨ε⟩ : Nonempty (Eps 2 ℂ_[2]) := inferInstance
  letI a1 : Algebra ℤ_[2] 𝓞_ℂ_[2] := (padicIntHom 2).toAlgebra
  letI a2 : Algebra ℤ_[2] ℂ_[2] := ((algebraMap 𝓞_ℂ_[2] ℂ_[2]).comp (padicIntHom 2)).toAlgebra
  refine ⟨⟨PadicComplexHost.not_isUnit_p 2⟩, PadicComplexHost.isAdicComplete 2, a1, a2,
    IsScalarTower.of_algebraMap_eq fun _ => rfl,
    ofGoodReduction (PadicComplexInt.integers 2) ε _ o', rfl, Point.finrank_V _, ?_⟩
  exact (isSplitting_int 𝓞_ℂ_[2]).map _

example [IsAdicComplete (Ideal.span {(p : O)}) O] :
    Submodule.span O (Set.range (dlogTv (G := Gm (Sp O)) (p := p))) = ⊤ := by
  refine Submodule.map_injective_of_injective (omega _).injective_subtype ?_
  rw [map_span_dlogTv, Submodule.map_subtype_top]
  exact HodgeTateTest.htSpan_gm p

example [IsAlgClosed C] [CharZero C] (hv : v.Integers O) (E : Type) [Field E] [NumberField E] :
    IsSplitting (embC C fun φ : E →+* C => embO hv φ) := isSplitting_embO hv

end Inhabitants

end GlobalTheory.HTLat
