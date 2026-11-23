import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.StripBorel

variable {D : D7}

def aInf (D : D7) : AF D.host.F := ((1 : Ainf D.host.F), (0 : Af D.host.F))

def aFin (D : D7) : AF D.host.F := ((0 : Ainf D.host.F), (1 : Af D.host.F))

def inlA (D : D7) : Ainf D.host.F →ₗ[D.host.F] AF D.host.F := LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)

def inrA (D : D7) : Af D.host.F →ₗ[D.host.F] AF D.host.F := LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)

def eInf (D : D7) : AE D := aInf D ⊗ₜ[D.host.F] (1 : D.host.E)

def eFin (D : D7) : AE D := aFin D ⊗ₜ[D.host.F] (1 : D.host.E)

def ιInf (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (inlA D) LinearMap.id

def ιFin (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (inrA D) LinearMap.id

theorem infPart_tmul (a : AF D.host.F) (x : D.host.E) : infPart D (a ⊗ₜ[D.host.F] x) = fstA D.host.F a ⊗ₜ[D.host.F] x := rfl

theorem finPart_tmul (a : AF D.host.F) (x : D.host.E) : finPart D (a ⊗ₜ[D.host.F] x) = sndA D.host.F a ⊗ₜ[D.host.F] x := rfl

theorem ιInf_tmul (b : Ainf D.host.F) (x : D.host.E) : ιInf D (b ⊗ₜ[D.host.F] x) = inlA D b ⊗ₜ[D.host.F] x :=
  TensorProduct.map_tmul _ _ _ _

theorem ιFin_tmul (b : Af D.host.F) (x : D.host.E) : ιFin D (b ⊗ₜ[D.host.F] x) = inrA D b ⊗ₜ[D.host.F] x :=
  TensorProduct.map_tmul _ _ _ _

theorem eInf_mul (z : AE D) : eInf D * z = ιInf D (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, RingHom.map_zero, LinearMap.map_zero]
  | tmul a x =>
    rw [eInf, Algebra.TensorProduct.tmul_mul_tmul, one_mul, infPart_tmul, ιInf_tmul]
    congr 1
    exact Prod.ext (α := Ainf D.host.F) (β := Af D.host.F) (by change (1 : Ainf D.host.F) * a.1 = a.1; exact one_mul _)
      (by change (0 : Af D.host.F) * a.2 = 0; exact zero_mul _)
  | add z z' hz hz' => rw [mul_add, hz, hz', RingHom.map_add, LinearMap.map_add]

theorem eFin_mul (z : AE D) : eFin D * z = ιFin D (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, RingHom.map_zero, LinearMap.map_zero]
  | tmul a x =>
    rw [eFin, Algebra.TensorProduct.tmul_mul_tmul, one_mul, finPart_tmul, ιFin_tmul]
    congr 1
    exact Prod.ext (α := Ainf D.host.F) (β := Af D.host.F) (by change (0 : Ainf D.host.F) * a.1 = 0; exact zero_mul _)
      (by change (1 : Af D.host.F) * a.2 = a.2; exact one_mul _)
  | add z z' hz hz' => rw [mul_add, hz, hz', RingHom.map_add, LinearMap.map_add]

theorem eInf_add_eFin : eInf D + eFin D = 1 := by
  rw [eInf, eFin, ← TensorProduct.add_tmul, Algebra.TensorProduct.one_def]
  congr 1
  exact Prod.ext (α := Ainf D.host.F) (β := Af D.host.F) (by change (1 : Ainf D.host.F) + 0 = 1; exact add_zero _)
    (by change (0 : Af D.host.F) + 1 = 1; exact zero_add _)

theorem eInf_mul_self : eInf D * eInf D = eInf D := by
  rw [eInf_mul, eInf, infPart_tmul, ιInf_tmul]
  rfl

theorem eFin_mul_self : eFin D * eFin D = eFin D := by
  rw [eFin_mul, eFin, finPart_tmul, ιFin_tmul]
  rfl

theorem eFin_mul_eInf : eFin D * eInf D = 0 := by
  rw [eFin_mul, eInf, finPart_tmul]
  have h : sndA D.host.F (aInf D) = 0 := rfl
  rw [h, TensorProduct.zero_tmul, LinearMap.map_zero]

theorem eInf_mul_eFin : eInf D * eFin D = 0 := by rw [mul_comm, eFin_mul_eInf]

theorem eInf_mul_eq {z z' : AE D} (h : infPart D z = infPart D z') : eInf D * z = eInf D * z' := by
  rw [eInf_mul, eInf_mul, h]

theorem eFin_mul_eq {z z' : AE D} (h : finPart D z = finPart D z') : eFin D * z = eFin D * z' := by
  rw [eFin_mul, eFin_mul, h]

theorem smul_eq_of_map_inf {m n : ℕ} {M N : Matrix (Fin m) (Fin n) (AE D)} (h : M.map (infPart D) = N.map (infPart D)) :
    eInf D • M = eInf D • N := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact eInf_mul_eq (congrFun (congrFun h i) j)

theorem smul_eq_of_map_fin {m n : ℕ} {M N : Matrix (Fin m) (Fin n) (AE D)} (h : M.map (finPart D) = N.map (finPart D)) :
    eFin D • M = eFin D • N := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact eFin_mul_eq (congrFun (congrFun h i) j)

theorem mt_map_inf {W : HSp D} {g : GA D W} (hg : g ∈ GfC W) : (mt W g).map (infPart D) = 1 := by
  have h : infHom W g = 1 := MonoidHom.mem_ker.1 hg
  calc (mt W g).map (infPart D) = ((infHom W g).1 : Matrix (Fin W.rank) (Fin W.rank) _) := rfl
    _ = 1 := by rw [h, Units.val_one]

theorem mt_map_fin {W : HSp D} {g : GA D W} (hg : g ∈ GinfC W) : (mt W g).map (finPart D) = 1 := by
  have h : finHom W g = 1 := MonoidHom.mem_ker.1 hg
  calc (mt W g).map (finPart D) = ((finHom W g).1 : Matrix (Fin W.rank) (Fin W.rank) _) := rfl
    _ = 1 := by rw [h, Units.val_one]

theorem smul_mt_mul_of_fin {W : HSp D} {g : GA D W} (hg : g ∈ GfC W) {k : ℕ} (M : Matrix (Fin W.rank) (Fin k) (AE D)) :
    eInf D • (mt W g ⬝ M) = eInf D • M :=
  smul_eq_of_map_inf (by rw [Matrix.map_mul, mt_map_inf hg, Matrix.one_mul])

theorem smul_mt_mul_of_inf {W : HSp D} {g : GA D W} (hg : g ∈ GinfC W) {k : ℕ} (M : Matrix (Fin W.rank) (Fin k) (AE D)) :
    eFin D • (mt W g ⬝ M) = eFin D • M :=
  smul_eq_of_map_fin (by rw [Matrix.map_mul, mt_map_fin hg, Matrix.one_mul])

theorem exists_left_inv {n ρ : ℕ} {x₀ : Matrix (Fin n) (Fin ρ) D.host.E} (hx : LinearIndependent D.host.E x₀.transpose) :
    ∃ y : Matrix (Fin ρ) (Fin n) D.host.E, y * x₀ = 1 := by
  have hinj : Function.Injective x₀.mulVec := Matrix.mulVec_injective_iff.2 hx
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin x₀) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin x₀) = 1 := by rw [hg, LinearMap.toMatrix'_id]
  rwa [LinearMap.toMatrix'_comp, show LinearMap.toMatrix' x₀.mulVecLin = x₀ from LinearMap.toMatrix'_toLin' x₀] at h

theorem diag_mul' {k : ℕ} {x y : Matrix (Fin k) (Fin k) (AE D)}
    (hx : ∀ i j, j < i → x i j = 0) (hy : ∀ i j, j < i → y i j = 0) (i : Fin k) :
    (x ⬝ y) i i = x i i * y i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hx i j h, zero_mul]
  · rw [hy j i h, mul_zero]

def Qset {n ρ : ℕ} (X : Mx D n ρ) (Y : Mx D ρ n) : Set (Mx D n ρ) :=
  {w | X ⬝ (Y ⬝ w) = w ∧ (∀ i j : Fin ρ, j < i → (Y ⬝ w) i j = 0) ∧ ∀ i : Fin ρ, (Y ⬝ w) i i = eInf D}

theorem isClosed_Qset {n ρ : ℕ} (X : Mx D n ρ) (Y : Mx D ρ n) : IsClosed (Qset X Y) := by
  have hc : Continuous fun w : Mx D n ρ => Y ⬝ w := continuous_const.matrix_mul continuous_id
  simp only [Qset, Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter (isClosed_eq (continuous_const.matrix_mul hc) continuous_id) (IsClosed.inter ?_ ?_)
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (hc.matrix_elem i j) continuous_const
  · exact isClosed_iInter fun i => isClosed_eq (hc.matrix_elem i i) continuous_const

def Sset (W : HSp D) {ρ : ℕ} (C : Set (GA D W)) (X : Mx D W.rank ρ) (Y : Mx D ρ W.rank) : Set (Mx D W.rank ρ) :=
  {z | ∃ c ∈ C, eInf D • (mt W c ⬝ z) ∈ Qset X Y}

theorem isClosed_Sset (W : HSp D) {ρ : ℕ} {C : Set (GA D W)} (hC : IsCompact C) (X : Mx D W.rank ρ) (Y : Mx D ρ W.rank) :
    IsClosed (Sset W C X Y) := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
  have h1 : Continuous fun p : C × Mx D W.rank ρ => mt W (p.1 : GA D W) :=
    (GlobalTheory.MixModel.continuous_mt W).comp (continuous_subtype_val.comp continuous_fst)
  have h2 : Continuous fun p : C × Mx D W.rank ρ => mt W (p.1 : GA D W) ⬝ p.2 := h1.matrix_mul continuous_snd
  have hf : Continuous fun p : C × Mx D W.rank ρ => eInf D • (mt W (p.1 : GA D W) ⬝ p.2) :=
    continuous_matrix fun i j => continuous_const.mul (h2.matrix_elem i j)
  have hT : IsClosed {p : C × Mx D W.rank ρ | eInf D • (mt W (p.1 : GA D W) ⬝ p.2) ∈ Qset X Y} :=
    (isClosed_Qset X Y).preimage hf
  convert isClosedMap_snd_of_compactSpace _ hT using 1
  ext z
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨(⟨c, hc⟩, z), h, rfl⟩
  · rintro ⟨⟨c, z'⟩, h, rfl⟩
    exact ⟨c.1, c.2, h⟩

theorem smul_mem_Qset {n ρ : ℕ} {X : Mx D n ρ} {Y : Mx D ρ n} (hYX : Y ⬝ X = 1) (u : GL (Fin ρ) (AE D)) (hu : u ∈ UX D ρ) :
    eInf D • (X ⬝ u.1) ∈ Qset X Y := by
  have hu' := (GlobalTheory.UniIndexPrime.mem_uniSub u).1 hu
  have hm : Y ⬝ (eInf D • (X ⬝ u.1)) = eInf D • u.1 := by rw [Matrix.mul_smul, ← Matrix.mul_assoc, hYX, Matrix.one_mul]
  refine ⟨by rw [hm, Matrix.mul_smul], fun i j hij => ?_, fun i => ?_⟩
  · rw [hm, Matrix.smul_apply, hu'.1 i j hij, smul_zero]
  · rw [hm, Matrix.smul_apply, hu'.2 i, smul_eq_mul, mul_one]

theorem unit_mix {ρ : ℕ} (m' : Matrix (Fin ρ) (Fin ρ) (AE D)) (hlo : ∀ i j : Fin ρ, j < i → m' i j = 0)
    (hd : ∀ i : Fin ρ, m' i i = eInf D) :
    ∃ u₁ : GL (Fin ρ) (AE D), u₁ ∈ UX D ρ ∧ u₁.1 = m' + eFin D • (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) := by
  obtain ⟨v, hv⟩ : ∃ v : Matrix (Fin ρ) (Fin ρ) (AE D), v = m' + eFin D • (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) :=
    ⟨_, rfl⟩
  have hvlo : ∀ i j : Fin ρ, j < i → v i j = 0 := by
    intro i j hij
    rw [hv, Matrix.add_apply, Matrix.smul_apply, hlo i j hij, Matrix.one_apply_ne hij.ne', smul_zero, zero_add]
  have hvd : ∀ i : Fin ρ, v i i = 1 := by
    intro i
    rw [hv, Matrix.add_apply, Matrix.smul_apply, hd i, Matrix.one_apply_eq, smul_eq_mul, _root_.mul_one, eInf_add_eFin]
  have hvdet : IsUnit v.det := by
    rw [Matrix.det_of_upperTriangular (fun a b h => hvlo a b h)]
    simp only [hvd, Finset.prod_const_one]
    exact isUnit_one
  refine ⟨((Matrix.isUnit_iff_isUnit_det v).2 hvdet).unit, ?_, hv⟩
  exact (GlobalTheory.UniIndexPrime.mem_uniSub _).2 ⟨hvlo, hvd⟩

set_option maxHeartbeats 1000000 in
theorem mem_Rgrp_of (W : HSp D) {ρ : ℕ} {X : Mx D W.rank ρ} {Y : Mx D ρ W.rank} {q : GA D W} (hq : q ∈ GinfC W)
    (u : GL (Fin ρ) (AE D)) (hu : u ∈ UX D ρ) (hQ : eInf D • (mt W q ⬝ X ⬝ u.1) ∈ Qset X Y) : q ∈ Rgrp W X := by
  obtain ⟨w, hw⟩ : ∃ w, w = eInf D • (mt W q ⬝ X ⬝ u.1) := ⟨_, rfl⟩
  rw [← hw] at hQ
  obtain ⟨hQ1, hQ2, hQ3⟩ := hQ
  obtain ⟨m, hm⟩ : ∃ m, m = Y ⬝ w := ⟨_, rfl⟩
  rw [← hm] at hQ1 hQ2 hQ3
  have hem : eInf D • m = m := by
    rw [hm, ← Matrix.mul_smul, hw, smul_smul, eInf_mul_self]
  obtain ⟨ui, hui⟩ : ∃ ui : Matrix (Fin ρ) (Fin ρ) (AE D), ui = (u⁻¹ : GL (Fin ρ) (AE D)).1 := ⟨_, rfl⟩
  have huu : u.1 ⬝ ui = 1 := by rw [hui, ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one]
  have hut : IsUnitri ui := by
    rw [hui]
    exact (GlobalTheory.UniIndexPrime.mem_uniSub (u⁻¹ : GL (Fin ρ) (AE D))).1 (inv_mem hu)
  obtain ⟨m', hm'⟩ : ∃ m', m' = m ⬝ ui := ⟨_, rfl⟩
  have hm'e : eInf D • m' = m' := by rw [hm', ← Matrix.smul_mul, hem]
  have hm'lo : ∀ i j : Fin ρ, j < i → m' i j = 0 := by
    intro i j hij
    have hbt : (m ⬝ ui).BlockTriangular id :=
      Matrix.BlockTriangular.mul (fun a b h => hQ2 a b h) (fun a b h => hut.1 a b h)
    rw [hm']
    exact hbt hij
  have hm'd : ∀ i : Fin ρ, m' i i = eInf D := by
    intro i
    rw [hm', diag_mul' hQ2 hut.1 i, hQ3 i, hut.2 i, _root_.mul_one]
  obtain ⟨u₁, hu₁, hv⟩ := unit_mix m' hm'lo hm'd
  have dec : ∀ M : Mx D W.rank ρ, M = eInf D • M + eFin D • M := fun M => by
    rw [← add_smul, eInf_add_eFin, one_smul]
  have r1 : eInf D • (X ⬝ u₁.1) = X ⬝ m' := by
    rw [← Matrix.mul_smul, hv, smul_add, hm'e, smul_smul, eInf_mul_eFin, zero_smul, add_zero]
  have r2 : eInf D • (mt W q ⬝ X) = X ⬝ m' := by
    have h2 : eInf D • (mt W q ⬝ X) = w ⬝ ui := by
      rw [hw, Matrix.smul_mul, Matrix.mul_assoc (mt W q ⬝ X), huu, Matrix.mul_one]
    rw [h2, ← hQ1, hm', Matrix.mul_assoc]
  have r3 : eFin D • (mt W q ⬝ X) = eFin D • X := smul_mt_mul_of_inf hq X
  have r4 : eFin D • (X ⬝ u₁.1) = eFin D • X := by
    rw [← Matrix.mul_smul, hv, smul_add, ← hm'e, smul_smul, eFin_mul_eInf, zero_smul, zero_add, smul_smul, eFin_mul_self,
      Matrix.mul_smul, Matrix.mul_one]
  have key : mt W q ⬝ X = X ⬝ u₁.1 := by
    rw [dec (mt W q ⬝ X), dec (X ⬝ u₁.1), r1, r2, r3, r4]
  exact ⟨u₁, hu₁, key⟩

theorem strip_of_mem (W : HSp D) {ρ : ℕ} {C : Set (GA D W)} (hCinf : C ⊆ GinfC W) {X : Mx D W.rank ρ} {Y : Mx D ρ W.rank}
    (h : GA D W) (u : GL (Fin ρ) (AE D)) (hu : u ∈ UX D ρ) (hS : mt W h⁻¹ ⬝ (X ⬝ u.1) ∈ Sset W C X Y) :
    h ∈ strip W (Rgrp W X) C := by
  have hcomm := (GlobalTheory.AdelicSplit.adelic_split D W).2.2.1
  obtain ⟨c, hc, hQ⟩ := hS
  obtain ⟨sp, hsp⟩ := (GlobalTheory.AdelicSplit.adelic_split D W).2.2.2.1
  obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a ∈ GinfC W, ∃ b ∈ GfC W, h = a * b :=
    ⟨(sp.symm h).1.1, (sp.symm h).1.2, (sp.symm h).2.1, (sp.symm h).2.2, by rw [← hsp, sp.apply_symm_apply]⟩
  have hcI : c ∈ GinfC W := hCinf hc
  have hq : c * a⁻¹ ∈ GinfC W := mul_mem hcI (inv_mem ha)
  have e2 : c * (a * b)⁻¹ = b⁻¹ * (c * a⁻¹) := by
    rw [_root_.mul_inv_rev, ← _root_.mul_assoc, (show Commute c b from hcomm c hcI b hb).inv_right.eq, _root_.mul_assoc]
  have hw : eInf D • (mt W c ⬝ (mt W (a * b)⁻¹ ⬝ (X ⬝ u.1))) = eInf D • (mt W (c * a⁻¹) ⬝ X ⬝ u.1) := by
    rw [← Matrix.mul_assoc, ← mt_mul, e2, mt_mul, Matrix.mul_assoc, smul_mt_mul_of_fin (inv_mem hb), Matrix.mul_assoc]
  rw [hw] at hQ
  have hqR : c * a⁻¹ ∈ Rgrp W X := mem_Rgrp_of W hq u hu hQ
  refine ⟨(c * a⁻¹)⁻¹, inv_mem hqR, c, hc, b, hb, ?_⟩
  rw [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]

theorem mem_of_strip (W : HSp D) {ρ : ℕ} {C : Set (GA D W)} (hCinf : C ⊆ GinfC W) {X : Mx D W.rank ρ} {Y : Mx D ρ W.rank}
    (hYX : Y ⬝ X = 1) (h : GA D W) (u : GL (Fin ρ) (AE D)) (hu : u ∈ UX D ρ) (hh : h ∈ strip W (Rgrp W X) C) :
    mt W h⁻¹ ⬝ (X ⬝ u.1) ∈ Sset W C X Y := by
  have hcomm := (GlobalTheory.AdelicSplit.adelic_split D W).2.2.1
  obtain ⟨r, hr, c, hc, b, hb, rfl⟩ := hh
  obtain ⟨v, hv, hrv⟩ := (Rgrp W X).inv_mem hr
  refine ⟨c, hc, ?_⟩
  have hcI : c ∈ GinfC W := hCinf hc
  have e1 : c * (r * c * b)⁻¹ = b⁻¹ * r⁻¹ := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ← _root_.mul_assoc,
      (show Commute c b from hcomm c hcI b hb).inv_right.eq, _root_.mul_assoc, mul_inv_cancel_left]
  rw [← Matrix.mul_assoc, ← mt_mul, e1, mt_mul, Matrix.mul_assoc, smul_mt_mul_of_fin (inv_mem hb), ← Matrix.mul_assoc, hrv,
    Matrix.mul_assoc, ← Units.val_mul]
  exact smul_mem_Qset hYX _ (mul_mem hv hu)

theorem strip_measurable : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ →
    ∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → MeasurableSet (strip W (Rgrp W (rat x₀)) C) ∧
      ∃ S : Set (Mx D W.rank ρ), MeasurableSet S ∧
        (∀ z z' : Mx D W.rank ρ, z.map (infPart D) = z'.map (infPart D) → (z ∈ S ↔ z' ∈ S)) ∧
        ∀ (h : GA D W) (u : UX D ρ), mt W h⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) ∈ S ↔ h ∈ strip W (Rgrp W (rat x₀)) C := by
  intro D W ρ x₀ hx C hC hCinf
  obtain ⟨y, hy⟩ := exists_left_inv hx.1
  have hYX : (rat y : Mx D ρ W.rank) ⬝ (rat x₀ : Mx D W.rank ρ) = 1 := by
    change y.map (incA D) * x₀.map (incA D) = 1
    rw [← Matrix.map_mul, hy, Matrix.map_one _ (incA D).map_zero (incA D).map_one]
  haveI : BorelSpace (Mx D W.rank ρ) := ⟨rfl⟩
  have hS : MeasurableSet (Sset W C (rat x₀) (rat y)) := (isClosed_Sset W hC _ _).measurableSet
  have hiff : ∀ (h : GA D W) (u : GL (Fin ρ) (AE D)), u ∈ UX D ρ →
      (mt W h⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ u.1) ∈ Sset W C (rat x₀) (rat y) ↔ h ∈ strip W (Rgrp W (rat x₀)) C) :=
    fun h u hu => ⟨strip_of_mem W hCinf h u hu, mem_of_strip W hCinf hYX h u hu⟩
  have hstrip : strip W (Rgrp W (rat x₀)) C =
      (fun h : GA D W => mt W h⁻¹ ⬝ (rat x₀ : Mx D W.rank ρ)) ⁻¹' Sset W C (rat x₀) (rat y) := by
    ext h
    have h1 := hiff h 1 (one_mem _)
    rw [Units.val_one, Matrix.mul_one] at h1
    exact h1.symm
  refine ⟨?_, Sset W C (rat x₀) (rat y), hS, fun z z' hzz => ?_, fun h u => hiff h u.1 u.2⟩
  · rw [hstrip]
    exact (((GlobalTheory.MixModel.continuous_mt W).comp continuous_inv).matrix_mul continuous_const).measurable hS
  · have key : ∀ c : GA D W, eInf D • (mt W c ⬝ z) = eInf D • (mt W c ⬝ z') := fun c =>
      smul_eq_of_map_inf (by rw [Matrix.map_mul, Matrix.map_mul, hzz])
    exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, key c ▸ h⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, (key c).symm ▸ h⟩⟩

end GlobalTheory.StripBorel

end
