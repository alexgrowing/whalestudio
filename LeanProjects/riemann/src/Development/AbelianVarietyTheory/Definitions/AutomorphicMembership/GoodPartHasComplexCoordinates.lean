import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfHypotheses
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartOfDefinite
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfMemRangeAdjoint
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeOpEqSpanOfFormsTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorEqRangeGoodCoordinates

noncomputable section

namespace GlobalTheory.Mem.SJ

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Bs : DefBase D.what₂.LL} {A : DefAmb Bs}

structure Read (D : D7) {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) where

  wU : D.what₂.Word → (fc X.zs).Dc.Mem

  eNu : ∀ u, (Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V

  eRR : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V

  jV : (Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb D.what₂.mu0

  v0 : Bs.v0 = InfinitePlace.mk D.what₂.embLL

  twist : ∀ a, Bs.v0.embedding a = cj s (D.what₂.embLL a)

variable {X : CxData A} {fc : DefSub A → DefFace Bs} {s : Bool}

structure Seam (R : Read D X fc s) (cr : Crd A fc) where

  cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc X.zs).Dc.a (R.wU u)) → ℂ)

  cF : (Fin ((fc X.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0

  eR : D.what₂.EE →ₛₗ[cj s] X.EE

  cφ_eq : ∀ u x, (cφ u).symm (cpt D.what₂.embLL x) = D.jN u (R.eNu u x)

  cF_eq : ∀ y, cF (cpt D.what₂.embLL y) = R.jV y

  eR_eq : ∀ y, eR (D.jEE (R.eRR y)) = X.iC cr true Bs.μ0 (cpt Bs.v0.embedding y)

namespace Read

variable (R : Read D X fc s)

def DcPt : Prop :=
  ∀ u x y, D.what₂.embLL ((fc X.zs).Dc.Pt (R.wU u) Bs.μ0 x y) = D.what₂.perCol u D.what₂.mu0 (D.jN u (R.eNu u x)) (R.jV y)

def ReadingFormsSpanGoodSubspace : Prop := Submodule.span ℂ (Set.range R.jV) = D.what₂.V0 D.what₂.mu0

def IotaRd (cr : Crd A fc) : Prop :=
  ∀ y, D.what₂.iota D.what₂.mu0 (R.jV y) =
    D.jEE (R.eRR ((X.rowMat cr true Bs.μ0).mulVec (((lv (fc X.zs) true).Pq Bs.μ0).mulVec y)))

def NuTie : Prop := ∀ u, ∃ L, HLatTie (D.div.Nu u) L ((fc X.zs).Dc.Xc (R.wU u)) (R.eNu u)

def RRTie (cr : Crd A fc) : Prop := ∃ L, HLatTie D.div.RR L (X.XE cr true) R.eRR

end Read

structure CxFacts (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc)
    (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t) : Prop where

  wf : (fc X.zs).Df1.WF

  h2 : X.H2 cr true

  pos : X.H4pos

  theta : ∀ y, X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 y)) =
    X.Θ Bs.μ0 (X.jR Bs.μ0 (cr.toR X.zs true Bs.μ0 (((fc X.zs).Df1.Pq Bs.μ0).mulVec y)))

def cjv (s : Bool) {n : ℕ} (x : Fin n → ℂ) : Fin n → ℂ := fun i => cj s (x i)

namespace Seam

variable {R : Read D X fc s} {cr : Crd A fc} (M : Seam R cr)

def ChainTie : Prop :=
  ∀ u (x : Fin ((fc X.zs).Dc.a (R.wU u)) → D.what₂.LL) (y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL),
    D.what₂.perCol u D.what₂.mu0 ((M.cφ u).symm (cpt D.what₂.embLL x)) (M.cF (cpt D.what₂.embLL y)) =
      D.what₂.embLL ((fc X.zs).Dc.Pt (R.wU u) Bs.μ0 x y)

def GoodPartHasComplexCoordinates : Prop := D.what₂.V0 D.what₂.mu0 ≤ LinearMap.range M.cF

def RowTie (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t) : Prop :=
  (∀ F, M.eR F ∈ X.EEl true) ∧ (∀ e ∈ X.EEl true, ∃ F, M.eR F = e) ∧ (∃ c : ℝ, 0 < c ∧ ∀ F, ‖M.eR F‖ = c * ‖F‖) ∧
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL,
      X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 y)) = lam • M.eR (D.what₂.iota D.what₂.mu0 (M.cF (cpt D.what₂.embLL y)))

def ColNorm : Prop :=
  ∀ u, ∃ c : ℝ, 0 < c ∧ ∀ φ : D.what₂.Mu u, Formalism.DivisionValues.fnorm ((fc X.zs).Dc.Xc (R.wU u) Bs.v0) (cjv s (M.cφ u φ)) = c * ‖φ‖

end Seam

section Extend

theorem lin_cpt_semilinear {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] E) (x : Fin n → K) :
    lin (fun k => j (Pi.single k 1)) (cpt σ x) = j x := by
  have hx : x = ∑ k, x k • (Pi.single k (1 : K) : Fin n → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [lin, cpt, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ]

theorem lin_bijective_of_form {K V E ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {n : ℕ} (j : V →ₛₗ[σ] E) (b : Module.Basis ι K V) (e : (Fin n → K) ≃ₗ[K] V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => j (b i))) = ⊤) :
    Function.Bijective (lin fun k => j (e (Pi.single k 1))) := by
  classical
  have hcpt : ∀ y, lin (fun k => j (e (Pi.single k 1))) (cpt σ y) = j (e y) := fun y =>
    lin_cpt_semilinear σ (j.comp e.toLinearMap) y
  have hsurj : Function.Surjective (lin fun k => j (e (Pi.single k 1))) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine LinearMap.mem_range.2 ⟨cpt σ (e.symm (b i)), ?_⟩
    rw [hcpt, LinearEquiv.apply_symm_apply]
  have : Module.Finite K V := Module.Finite.equiv e
  have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  let bE := Module.Basis.mk hb.1 hb.2.ge
  have : FiniteDimensional ℂ E := Module.Finite.of_basis bE
  have hdim : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ E := by
    rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis bE, ← Module.finrank_eq_card_basis b,
      ← e.finrank_eq, Module.finrank_fin_fun]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj, hsurj⟩

def cjvL (s : Bool) (n : ℕ) : (Fin n → ℂ) →ₛₗ[cj s] (Fin n → ℂ) where
  toFun := cjv s
  map_add' x y := by funext i; simp [cjv]
  map_smul' a x := by funext i; simp [cjv]

namespace Read

variable (R : Read D X fc s)

include R in

theorem cjv_cpt_embLL {n : ℕ} (x : Fin n → D.what₂.LL) : cjv s (cpt D.what₂.embLL x) = cpt Bs.v0.embedding x := by
  funext i
  simp only [cjv, cpt]
  rw [R.twist]

def colCrd (u : D.what₂.Word) : (Fin ((fc X.zs).Dc.a (R.wU u)) → ℂ) ≃ₗ[ℂ] D.what₂.Mu u :=
  LinearEquiv.ofBijective _ (lin_bijective_of_form D.what₂.embLL (D.jN u) (D.div.Nu u).b (R.eNu u) (D.jN_basis u))

def rowCrd : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) ≃ₗ[ℂ] D.what₂.EE :=
  LinearEquiv.ofBijective _ (lin_bijective_of_form D.what₂.embLL D.jEE D.div.RR.b R.eRR D.jEE_basis)

theorem rowCrd_cpt (y : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → D.what₂.LL) :
    R.rowCrd (cpt D.what₂.embLL y) = D.jEE (R.eRR y) := by
  simp only [rowCrd, LinearEquiv.ofBijective_apply]
  exact lin_cpt_semilinear _ (D.jEE.comp R.eRR.toLinearMap) y

def seam (cr : Crd A fc) : Seam R cr where
  cφ u := (R.colCrd u).symm
  cF := lin fun k => R.jV (Pi.single k 1)
  eR := (X.iC cr true Bs.μ0).comp ((cjvL s _).comp R.rowCrd.symm.toLinearMap)
  cφ_eq u x := lin_cpt_semilinear D.what₂.embLL ((D.jN u).comp (R.eNu u).toLinearMap) x
  cF_eq y := lin_cpt_semilinear _ _ y
  eR_eq y := by
    show X.iC cr true Bs.μ0 (cjv s (R.rowCrd.symm _)) = _
    rw [← R.rowCrd_cpt, LinearEquiv.symm_apply_apply, R.cjv_cpt_embLL]

instance (cr : Crd A fc) : Inhabited (Seam R cr) := ⟨R.seam cr⟩

end Read

end Extend

section Untwisted

variable {R : Read D X fc false} {cr : Crd A fc} (M : Seam R cr)

theorem Read.embedding_eq_of_untwisted (R : Read D X fc false) : Bs.v0.embedding = D.what₂.embLL :=
  RingHom.ext fun a => by simpa [cj] using R.twist a

namespace Seam

def eRLin : D.what₂.EE →ₗ[ℂ] X.EE := M.eR

theorem chainTie_iff_untwisted : M.ChainTie ↔
    ∀ u (x : Fin ((fc X.zs).Dc.a (R.wU u)) → D.what₂.LL) (y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL),
      D.what₂.perCol u D.what₂.mu0 ((M.cφ u).symm (cpt Bs.v0.embedding x)) (M.cF (cpt Bs.v0.embedding y)) =
        Bs.v0.embedding ((fc X.zs).Dc.Pt (R.wU u) Bs.μ0 x y) := by
  simp only [ChainTie, Read.embedding_eq_of_untwisted R]

theorem colNorm_iff_untwisted : M.ColNorm ↔
    ∀ u, ∃ c : ℝ, 0 < c ∧ ∀ φ : D.what₂.Mu u, Formalism.DivisionValues.fnorm ((fc X.zs).Dc.Xc (R.wU u) Bs.v0) (M.cφ u φ) = c * ‖φ‖ := by
  have h : ∀ {n : ℕ} (x : Fin n → ℂ), cjv false x = x := fun x => by
    funext i
    simp [cjv, cj]
  simp only [ColNorm, h]

theorem rowTie_iff_untwisted (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t) : M.RowTie eV ↔
    ∃ lam : ℂ, lam ≠ 0 ∧ (∀ F, (lam • M.eRLin) F ∈ X.EEl true) ∧ (∀ e ∈ X.EEl true, ∃ F, (lam • M.eRLin) F = e) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ F, ‖(lam • M.eRLin) F‖ = c * ‖F‖) ∧
      ∀ y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL,
        X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 y)) =
          (lam • M.eRLin) (D.what₂.iota D.what₂.mu0 (M.cF (cpt Bs.v0.embedding y))) := by
  have hE : ∀ F, M.eRLin F = M.eR F := fun _ => rfl
  simp only [RowTie, LinearMap.smul_apply, hE, Read.embedding_eq_of_untwisted R]
  constructor
  · rintro ⟨hmem, hsurj, ⟨c, hc, hn⟩, lam, hlam, hth⟩
    refine ⟨lam, hlam, fun F => Submodule.smul_mem _ _ (hmem F), fun e he => ?_,
      ⟨‖lam‖ * c, mul_pos (norm_pos_iff.2 hlam) hc, fun F => by rw [norm_smul, hn, mul_assoc]⟩, hth⟩
    obtain ⟨F, hF⟩ := hsurj (lam⁻¹ • e) (Submodule.smul_mem _ _ he)
    exact ⟨F, by rw [hF, smul_inv_smul₀ hlam]⟩
  · rintro ⟨lam, hlam, hmem, hsurj, ⟨c, hc, hn⟩, hth⟩
    have hlin : ∀ F, M.eR (lam • F) = lam • M.eR F := fun F => M.eRLin.map_smul lam F
    refine ⟨fun F => ?_, fun e he => ?_,
      ⟨c / ‖lam‖, div_pos hc (norm_pos_iff.2 hlam), fun F => ?_⟩, lam, hlam, hth⟩
    · have h1 := Submodule.smul_mem _ lam⁻¹ (hmem F)
      rwa [inv_smul_smul₀ hlam] at h1
    · obtain ⟨F, hF⟩ := hsurj e he
      exact ⟨lam • F, by rw [hlin, hF]⟩
    · have h1 := hn F
      rw [norm_smul] at h1
      rw [div_mul_eq_mul_div, eq_div_iff (norm_ne_zero_iff.2 hlam)]
      linarith [h1, mul_comm ‖lam‖ ‖M.eR F‖]

end Seam

end Untwisted

section OfTie

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}

def castForms {a b : D.what₂.Tup} (h : a = b) : D.what₂.Amb a →ₗ[ℂ] D.what₂.Amb b := h ▸ LinearMap.id

theorem castForms_heq {a b : D.what₂.Tup} (h : a = b) (x : D.what₂.Amb a) : HEq (castForms h x) x := by
  subst h
  rfl

theorem iota_castForms {a b : D.what₂.Tup} (h : a = b) (x : D.what₂.Amb a) :
    D.what₂.iota b (castForms h x) = D.what₂.iota a x := by
  subst h
  rfl

theorem perCol_castForms {a b : D.what₂.Tup} (h : a = b) (u : D.what₂.Word) (φ : D.what₂.Mu u) (x : D.what₂.Amb a) :
    D.what₂.perCol u b φ (castForms h x) = D.what₂.perCol u a φ x := by
  subst h
  rfl

theorem span_castForms {a b : D.what₂.Tup} (h : a = b) {ι : Type} (f : ι → D.what₂.Amb a)
    (hf : Submodule.span ℂ (Set.range f) = D.what₂.V0 a) :
    Submodule.span ℂ (Set.range fun i => castForms h (f i)) = D.what₂.V0 b := by
  subst h
  exact hf

theorem iota_sharp_side (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  have h : ∀ j, (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      show ((RowSide.sharp D).downTo μ j).comp ((RowSide.sharp D).io μ j) = (D.what₂.downTo μ j).comp (D.what₂.io μ j)
      rw [ih]
      rfl
  show (D.what₂.multZero μ).toLinearEquiv.toLinearMap ∘ₗ (RowSide.sharp D).downTo μ D.R.m ∘ₗ
    (D.what₂.multTop μ).symm.toLinearEquiv.toLinearMap = _
  rw [h]
  rfl

variable (F : Face D A) (X : CxData A.fam.amb) {S₀ : IndefData (A.side F.P0 F.ψ0 X.zs)} {X₀ : BaseLevelRowSide D}
  (I : DivisionCompatibilityData D A F.P0 F.ψ0 F.P1 F.ψ1 X.zs S₀ (X.data F.cr true) X₀ (F.Dc X.zs))

def Read.ofTie (h : TupTie D A S₀ I.tup) : Read D X F.fc (twAt D.what₂.embLL A.v0) where
  wU := I.wU
  eNu := I.eNu
  eRR := I.eRR
  jV := (castForms h.mu0).comp ((I.jA A.μ0).comp (rV0 D A F.P1 F.ψ1 A.μ0).mulVecLin)
  v0 := h.v0
  twist a := by
    have h1 := emb_eq D.what₂.embLL A.v0 a
    rw [sgAt_mk _ h.v0] at h1
    exact h1

theorem Read.ofTie_jV (h : TupTie D A S₀ I.tup) (y : Fin ((A.fam.R A.μ0).nV (A.fam.lvl F.P1 F.ψ1)) → D.what₂.LL) :
    (Read.ofTie F X I h).jV y = castForms h.mu0 (I.jA A.μ0 ((rV0 D A F.P1 F.ψ1 A.μ0).mulVec y)) := rfl

theorem Read.ofTie_dcPt_iff (h : TupTie D A S₀ I.tup) : (Read.ofTie F X I h).DcPt ↔
    ∀ u x y, D.what₂.embLL ((F.Dc X.zs).Pt (I.wU u) A.μ0 x y) =
      D.what₂.perCol u (I.tup A.μ0) (D.jN u (I.eNu u x)) (I.jA A.μ0 ((rV0 D A F.P1 F.ψ1 A.μ0).mulVec y)) := by
  have key : ∀ u φ y, D.what₂.perCol u D.what₂.mu0 φ ((Read.ofTie F X I h).jV y) =
      D.what₂.perCol u (I.tup A.μ0) φ (I.jA A.μ0 ((rV0 D A F.P1 F.ψ1 A.μ0).mulVec y)) :=
    fun u φ y => perCol_castForms h.mu0 u φ _
  unfold Read.DcPt
  exact ⟨fun H u x y => (H u x y).trans (key u _ y), fun H u x y => (H u x y).trans (key u _ y).symm⟩

variable {Sp : SPer (F.Dc X.zs)} {C : ColData (F.Dc X.zs) Sp (X.data F.cr true)}
  {NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin ((F.Dc X.zs).a u) → D.what₂.LL)}

private theorem subE_mulVec_eq_sum_subBasis {K' : Type} [Field K'] [StarRing K'] {n : ℕ} (Z : Submodule K' (Fin n → K'))
    (c : Fin (subDim Z) → K') : (subE Z).mulVec c = ((∑ j, c j • subBasis Z j : Z) : Fin n → K') := by
  funext i
  simp only [subE, Matrix.mulVec, dotProduct, Matrix.of_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem subE_mulVec_mem {K' : Type} [Field K'] [StarRing K'] {n : ℕ} (Z : Submodule K' (Fin n → K'))
    (c : Fin (subDim Z) → K') : (subE Z).mulVec c ∈ Z := by
  rw [subE_mulVec_eq_sum_subBasis]
  exact Submodule.coe_mem _

private theorem exists_subE_mulVec_eq_of_mem {K' : Type} [Field K'] [StarRing K'] {n : ℕ} (Z : Submodule K' (Fin n → K'))
    {z : Fin n → K'} (hz : z ∈ Z) : ∃ c, (subE Z).mulVec c = z :=
  ⟨(subBasis Z).repr ⟨z, hz⟩, by rw [subE_mulVec_eq_sum_subBasis, (subBasis Z).sum_repr]⟩

private theorem gaMat_mul' {K' : Type} [Field K'] [NumberField K'] [StarRing K'] {G' : Type} [Group G']
    [Fintype G'] {P' : Type} (B : BlockDat K' G' P') (a b : MonoidAlgebra K' G') :
    B.S.gaMat B.r (a * b) = B.S.gaMat B.r a * B.S.gaMat B.r b := by
  rw [Formalism.L2.DIV.CSD.gaMat_eq_toMatrix, Formalism.L2.DIV.CSD.gaMat_eq_toMatrix, Formalism.L2.DIV.CSD.gaMat_eq_toMatrix,
    ← LinearMap.toMatrix_comp]
  congr 1
  exact LinearMap.ext fun φ => B.gaOp_mul a b φ

private theorem range_lvlOp_eq_range_lvlPr_mul_vE {K' : Type} [Field K'] [NumberField K'] [StarRing K'] {G' : Type} [Group G']
    [Fintype G'] {P' : Type} (B : BlockDat K' G' P') (ℓ : Lvl K' G') :
    (∀ x, ∃ y, (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X)).mulVec x = (B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ).mulVec y) ∧
      ∀ y, ∃ x, (B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ).mulVec y = (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X)).mulVec x := by
  have hG : B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) =
      B.S.gaMat B.r (idemOf ℓ.X) * B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ) := gaMat_mul' B _ _
  have hO : B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) =
      B.S.lvlPr B.r ℓ.P ℓ.ψ * B.S.gaMat B.r (idemOf ℓ.X) * B.S.lvlE B.r ℓ.P ℓ.ψ := rfl
  constructor
  · intro x
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1
      (subE_mulVec_mem (LinearMap.range (B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ)).mulVecLin) x)
    obtain ⟨y, hy⟩ := exists_subE_mulVec_eq_of_mem (LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin)
      (LinearMap.mem_range_self _ z)
    refine ⟨y, ?_⟩
    rw [hO]
    simp only [← Matrix.mulVec_mulVec]
    congr 1
    have e1 : (B.S.gaMat B.r (idemOf ℓ.X)).mulVec ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec x) =
        (B.S.gaMat B.r (idemOf ℓ.X)).mulVec ((B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ)).mulVec z) :=
      congrArg (B.S.gaMat B.r (idemOf ℓ.X)).mulVec hz.symm
    have e2 : (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVec z = (B.vE ℓ).mulVec y := hy.symm
    rw [e1, Matrix.mulVec_mulVec, ← hG, e2]
  · intro y
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1
      (subE_mulVec_mem (LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin) y)
    obtain ⟨x, hx⟩ := exists_subE_mulVec_eq_of_mem (LinearMap.range (B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ)).mulVecLin)
      (LinearMap.mem_range_self _ z)
    refine ⟨x, ?_⟩
    rw [hO]
    simp only [← Matrix.mulVec_mulVec]
    refine congrArg (B.S.lvlPr B.r ℓ.P ℓ.ψ).mulVec ?_
    have e1 : (B.vE ℓ).mulVec y = (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVec z := hz.symm
    have e2 : (B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec x = (B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ)).mulVec z := hx
    rw [e1, e2, Matrix.mulVec_mulVec, ← hG]

theorem Read.ofTie_spec (h : DivisionCompatible D A F.P0 F.ψ0 F.P1 F.ψ1 X.zs S₀ (X.data F.cr true) X₀ C NuC I) :
    (Read.ofTie F X I h.tup).ReadingFormsSpanGoodSubspace ∧ (Read.ofTie F X I h.tup).IotaRd F.cr ∧ (Read.ofTie F X I h.tup).NuTie ∧
      (Read.ofTie F X I h.tup).RRTie F.cr ∧ Function.Bijective (Read.ofTie F X I h.tup).wU := by
  refine ⟨?_, fun y => ?_, fun u => ⟨NuC (I.wU u), h.cols.Nu u⟩, ⟨_, h.sharp.RR⟩, h.cols.wU_bij⟩
  · have FT : FormsTie D.what₂.embLL (I.jA A.μ0) (rH D A F.P1 F.ψ1 A.μ0) (rE D A F.P1 F.ψ1 A.μ0)
        (D.what₂.eOp (I.tup A.μ0)) := h.sharp.forms A.μ0
    obtain ⟨K1, K2⟩ := range_lvlOp_eq_range_lvlPr_mul_vE (A.fam.R A.μ0) (A.fam.lvl F.P1 F.ψ1)
    have hf : Submodule.span ℂ (Set.range fun y => I.jA A.μ0 ((rV0 D A F.P1 F.ψ1 A.μ0).mulVec y)) =
        D.what₂.V0 (I.tup A.μ0) := by
      show _ = LinearMap.range (D.what₂.eOp (I.tup A.μ0))
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨y, rfl⟩
        obtain ⟨x, hx⟩ := K2 y
        exact LinearMap.mem_range.2 ⟨I.jA A.μ0 x, (FT.op_eq x).trans (congrArg (I.jA A.μ0) hx.symm)⟩
      · have e : LinearMap.range (D.what₂.eOp (I.tup A.μ0)) = Submodule.span ℂ
            ((D.what₂.eOp (I.tup A.μ0)) '' Set.range fun i => I.jA A.μ0 (Pi.single i 1)) := by
          rw [LinearMap.range_eq_map, ← FT.span, Submodule.map_span]
        rw [e, Submodule.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        obtain ⟨y, hy⟩ := K1 (Pi.single i 1)
        exact Submodule.subset_span ⟨y, ((FT.op_eq _).trans (congrArg (I.jA A.μ0) hy)).symm⟩
    exact span_castForms h.tup.mu0 _ hf
  · have e1 : D.what₂.iota D.what₂.mu0 ((Read.ofTie F X I h.tup).jV y) =
        D.what₂.iota (I.tup A.μ0) (I.jA A.μ0 ((rV0 D A F.P1 F.ψ1 A.μ0).mulVec y)) :=
      iota_castForms h.tup.mu0 _
    have e2 := LinearMap.congr_fun (iota_sharp_side D (I.tup A.μ0)) (I.jA A.μ0 ((rV0 D A F.P1 F.ψ1 A.μ0).mulVec y))
    exact e1.trans (e2.symm.trans (h.sharp.iota A.μ0 y))

end OfTie

section Place

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)

def placeGood : (Fin (B.nV ℓ) → K) →ₗ[K] B.S.Forms :=
  (B.S.basis.equivFun.symm : (Fin B.S.dim → K) →ₗ[K] B.S.Forms) ∘ₗ (B.vE ℓ).mulVecLin

theorem toF_eq_placeGood (Z : Submodule K B.S.Forms) (x : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z x = placeGood B ℓ ((B.zE ℓ Z).mulVec x) := rfl

theorem placeGood_injective : Function.Injective (placeGood B ℓ) := by
  intro u v huv
  have hmem : ∀ w : Fin (B.nV ℓ) → K, w ∈ B.Z0 ℓ ⊤ := fun w => by
    show w ∈ B.inV0 ℓ ⊤
    rw [BlockDat.mem_goodPart_iff]
    exact Submodule.mem_top
  obtain ⟨u', rfl⟩ := B.exists_zE ℓ ⊤ (hmem u)
  obtain ⟨v', rfl⟩ := B.exists_zE ℓ ⊤ (hmem v)
  rw [← toF_eq_placeGood, ← toF_eq_placeGood] at huv
  rw [B.toF_injective ℓ ⊤ huv]

theorem range_placeGood : LinearMap.range (placeGood B ℓ) = BlockGood.goodR B ℓ := rfl

theorem csum_placeGood (x y : Fin (B.nV ℓ) → K) :
    CSDForm.csumForm B.S (placeGood B ℓ x) (placeGood B ℓ y) =
      (Nat.card ℓ.P : K) * (star x ⬝ᵥ (B.HV ℓ).mulVec y) := by
  have hmem : ∀ w : Fin (B.nV ℓ) → K, w ∈ B.Z0 ℓ ⊤ := fun w => by
    show w ∈ B.inV0 ℓ ⊤
    rw [BlockDat.mem_goodPart_iff]
    exact Submodule.mem_top
  obtain ⟨x', rfl⟩ := B.exists_zE ℓ ⊤ (hmem x)
  obtain ⟨y', rfl⟩ := B.exists_zE ℓ ⊤ (hmem y)
  rw [← toF_eq_placeGood, ← toF_eq_placeGood, CSDForm.csumForm_apply, BlockGood.csum_toF]
  congr 1
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rfl

theorem csum_toF_placeGood (Z : Submodule K B.S.Forms) (hdet : IsUnit (B.HZ ℓ Z).det) (x : Fin (B.dZ ℓ Z) → K)
    (y : Fin (B.nV ℓ) → K) :
    CSDForm.csumForm B.S (B.toF ℓ Z x) (placeGood B ℓ y) =
      CSDForm.csumForm B.S (B.toF ℓ Z x) (B.toF ℓ Z ((B.Pq ℓ Z).mulVec y)) := by
  have e1 : CSDForm.csumForm B.S (B.toF ℓ Z x) (placeGood B ℓ y) =
      (Nat.card ℓ.P : K) * (star ((B.zE ℓ Z).mulVec x) ⬝ᵥ (B.HV ℓ).mulVec y) := by
    rw [toF_eq_placeGood, csum_placeGood]
  have e2 : CSDForm.csumForm B.S (B.toF ℓ Z x) (B.toF ℓ Z ((B.Pq ℓ Z).mulVec y)) =
      (Nat.card ℓ.P : K) * (star x ⬝ᵥ (B.HZ ℓ Z).mulVec ((B.Pq ℓ Z).mulVec y)) := by
    rw [CSDForm.csumForm_apply, BlockGood.csum_toF]
  have hP : B.HZ ℓ Z * B.Pq ℓ Z = (B.zE ℓ Z).conjTranspose * B.HV ℓ := by
    show B.HZ ℓ Z * ((B.HZ ℓ Z)⁻¹ * ((B.zE ℓ Z).conjTranspose * B.HV ℓ)) = _
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  rw [e1, e2]
  congr 1
  rw [Matrix.mulVec_mulVec, hP, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

end Block

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (F : Face D A)

def goodSubspaceCoordinateMap (Zs : DefSub A.fam.amb) (t : T) : (Fin ((F.fc Zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.fam.amb.FR t :=
  placeGood (A.fam.R t) (A.fam.lvl F.P1 F.ψ1)

variable (X : CxData A.fam.amb) {n : ℕ}

theorem evaluationTie_goodPlacement (hOk : A.fam.Ok n) : X.EVTie F.cr (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) (goodSubspaceCoordinateMap F X.zs) := by
  refine ⟨fun t y => (LinearMap.mem_range_self (placeGood (A.fam.R t) (A.fam.lvl F.P1 F.ψ1)) y : _), fun t y x => ?_⟩
  exact csum_toF_placeGood (A.fam.R t) (A.fam.lvl F.P1 F.ψ1) (X.zs.Z t)
    (BlockDat.HZ_det hOk.conj (hOk.what₂ t) hOk.irr) x y

theorem CxFacts.ofLinks (hOk : A.fam.Ok n) (hsep : A.fam.TypesSep) {Y : CxData.CxCol (fc := F.fc) X} {C CH : ℝ}
    (hL : X.CxLinks F.cr Y C CH) (hJ : X.JIsoR (cvOf A F.P0 F.ψ0 F.P1 F.ψ1))
    (hR : X.RatLev F.cr (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) true) (hDn : X.DnLev (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) true)
    (hUp : X.UpLev (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) true) : CxFacts X F.cr (goodSubspaceCoordinateMap F X.zs) where
  wf := A.fam.side_WF hOk F.P1 F.ψ1 X.zs hL.stable hL.inBlock hsep
  h2 := hL.h2 true
  pos := hL.h4pos
  theta y := CxData.theta_eV X F.cr (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) (goodSubspaceCoordinateMap F X.zs) hJ hR hDn hUp (coordinates_in_good_part_of_definite X true)
    (evaluationTie_goodPlacement F X hOk) _ y

theorem CxFacts.ofPrimitive (hOk : A.fam.Ok n) (hsep : A.fam.TypesSep) (hst : X.zs.Stable) (hin : X.zs.InBlock)
    (hpos : X.H4pos) (hn : NPTie X F.P0 F.P1) (hJ : X.JIsoR (cvOf A F.P0 F.ψ0 F.P1 F.ψ1))
    (hR : X.RatLev F.cr (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) true) (hDn : X.DnLev (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) true)
    (hUp : X.UpLev (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) true) (hB : X.ThmBop true) (hP : X.PartsE true) :
    CxFacts X F.cr (goodSubspaceCoordinateMap F X.zs) where
  wf := A.fam.side_WF hOk F.P1 F.ψ1 X.zs hst hin hsep
  h2 := (cutRows F.cr (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) true (A.fam.side_WF hOk F.P1 F.ψ1 X.zs hst hin hsep) hpos
    (isoR_of hOk hJ hn true) (crdZ_of X true) (coordinates_in_good_part_of_definite X true) hR hDn hUp hB hP).1
  pos := hpos
  theta y := CxData.theta_eV X F.cr (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) (goodSubspaceCoordinateMap F X.zs) hJ hR hDn hUp (coordinates_in_good_part_of_definite X true)
    (evaluationTie_goodPlacement F X hOk) _ y

end Place

example : cjv true ![Complex.I] = ![-Complex.I] := by
  funext i; fin_cases i; simp [cjv, cj]

example {n : ℕ} (x : Fin n → ℂ) : cjv false x = x := rfl

example (R : Read D X fc s) (cr : Crd A fc) (h : R.ReadingFormsSpanGoodSubspace) : (R.seam cr).GoodPartHasComplexCoordinates := by
  rw [Seam.GoodPartHasComplexCoordinates, ← h, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  exact ⟨_, (R.seam cr).cF_eq y⟩

end GlobalTheory.Mem.SJ

end
