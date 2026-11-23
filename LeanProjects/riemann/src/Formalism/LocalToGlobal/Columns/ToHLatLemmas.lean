import Mathlib
import Formalism.LocalToGlobal.Columns.ToHLat
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ClassSumDualGeOfFamily
import Formalism.LocalToGlobal.Columns.AtTRank
import Formalism.LocalToGlobal.Columns.RowFormsGood
import Formalism.LocalToGlobal.Columns.ColFormsInst

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory

section Coord

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] {n : ℕ}

theorem thl_fcoord_coord (b : Basis (Fin n) K V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) (x : V) :
    fcoord b X v x = fcoord (Pi.basisFun K (Fin n)) X v (b.equivFun x) := by
  simp only [Formalism.HermitianLatticesTheory.fcoord]
  congr 1

theorem thl_majAt_coord (b : Basis (Fin n) K V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) (x y : V) :
    majAt b X v x y = majAt (Pi.basisFun K (Fin n)) X v (b.equivFun x) (b.equivFun y) := by
  simp only [majAt, thl_fcoord_coord b X v]

theorem thl_normAt_coord (b : Basis (Fin n) K V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) (x : V) :
    normAt b X v x = normAt (Pi.basisFun K (Fin n)) X v (b.equivFun x) := by
  simp only [normAt, thl_fcoord_coord b X v]

theorem unitary_of_metric_restriction {n d : ℕ} (Xv : Matrix (Fin n) (Fin n) ℂ) (E : Matrix (Fin n) (Fin d) ℂ)
    (Y : Matrix (Fin d) (Fin d) ℂ) (hY : IsUnit Y.det) (h : metOf Y = restrMetC E (metOf Xv)) :
    (Xv⁻¹ * E * Y)ᴴ * (Xv⁻¹ * E * Y) = 1 := by
  have hYi : Y⁻¹ * Y = 1 := Matrix.nonsing_inv_mul Y hY
  have hYi' : Yᴴ * (Y⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hYi, Matrix.conjTranspose_one]
  simp only [metOf, restrMetC] at h
  calc (Xv⁻¹ * E * Y)ᴴ * (Xv⁻¹ * E * Y) = Yᴴ * (Eᴴ * ((Xv⁻¹)ᴴ * Xv⁻¹) * E) * Y := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Yᴴ * ((Y⁻¹)ᴴ * Y⁻¹) * Y := by rw [h]
    _ = (Yᴴ * (Y⁻¹)ᴴ) * (Y⁻¹ * Y) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hYi, hYi', Matrix.one_mul]

end Coord

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

theorem hB_equivFun (h : S.Ok) (φ : S.EqFun) : (S.hB h).equivFun φ = S.hCoord h φ := by
  ext i
  rfl

theorem hB_apply (h : S.Ok) (i : Fin (S.hDim h)) :
    S.res h (S.hB h i) = (S.toCSD h).basis i := by
  simp only [hB, Basis.map_apply, LinearEquiv.apply_symm_apply]

theorem subB_equivFun (h : S.Ok) (U : Submodule K S.EqFun) (x : U) :
    (S.subMat h U).mulVec ((S.subB h U).equivFun x) = S.hCoord h (x : S.EqFun) := by
  have hx : (S.subB h U).equivFun x = (subBasis (S.subZ h U)).equivFun (S.subEq h U x) := by
    ext i
    rfl
  rw [subMat, subE_mulVec, hx, LinearEquiv.symm_apply_apply]
  rfl

theorem subMat_injective (h : S.Ok) (U : Submodule K S.EqFun) : Function.Injective (S.subMat h U).mulVec := by
  intro x y hxy
  rw [subMat, subE_mulVec, subE_mulVec] at hxy
  exact (subBasis (S.subZ h U)).equivFun.symm.injective (Subtype.ext hxy)

theorem card_toH (h : S.Ok) (L : Submodule (𝓞 K) S.EqFun) :
    Fintype.card (S.toH h L).ι = finrank K S.EqFun := by
  exact (Module.finrank_eq_card_basis (S.hB h)).symm

theorem card_subH (h : S.Ok) (U : Submodule K S.EqFun) (L : Submodule (𝓞 K) U) :
    Fintype.card (S.subH h U L).ι = finrank K U := by
  exact (Module.finrank_eq_card_basis (S.subB h U)).symm

variable {S}

theorem PosH.frameOK {h : S.Ok} (hp : S.PosH h) (L : Submodule (𝓞 K) S.EqFun) : FrameOK (S.toH h L) := by
  exact fun v => (Formalism.L2.DIV.stdFrameHermAt K v _ (S.hGram h) hp).1 v

theorem PosH.met {h : S.Ok} (hp : S.PosH h) (v : InfinitePlace K) :
    metOf (stdFrame (S.hGram h) v) = (S.hGram h).map v.embedding := by
  exact (Formalism.L2.DIV.stdFrameHermAt K v _ (S.hGram h) hp).2

theorem PosH.frameOK_sub {h : S.Ok} (hp : S.PosH h) (U : Submodule K S.EqFun) (L : Submodule (𝓞 K) U) :
    FrameOK (S.subH h U L) := by
  exact fun v => (Formalism.L2.DIV.restrFrameSpec K _ _ (S.hGram h) hp (S.subMat h U) (S.subMat_injective h U) v).1

theorem PosH.sub_maj {h : S.Ok} (hp : S.PosH h) (U : Submodule K S.EqFun) (v : InfinitePlace K) (x y : U) :
    majAt (S.subB h U) (restrFrame (S.subMat h U) (S.hGram h)) v x y =
      majAt (S.hB h) (stdFrame (S.hGram h)) v (x : S.EqFun) (y : S.EqFun) := by
  rw [thl_majAt_coord (S.subB h U), thl_majAt_coord (S.hB h),
    (Formalism.L2.DIV.restrFrameSpec K _ _ (S.hGram h) hp (S.subMat h U) (S.subMat_injective h U) v).2.2,
    S.subB_equivFun h U, S.subB_equivFun h U, S.hB_equivFun h, S.hB_equivFun h]

theorem PosH.sub_norm {h : S.Ok} (hp : S.PosH h) (U : Submodule K S.EqFun) (v : InfinitePlace K) (x : U) :
    normAt (S.subB h U) (restrFrame (S.subMat h U) (S.hGram h)) v x =
      normAt (S.hB h) (stdFrame (S.hGram h)) v (x : S.EqFun) := by
  have hm := hp.sub_maj U v x x
  simp only [Formalism.HermitianLatticesTheory.majAt] at hm
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  congr 1
  have key : ∀ {ι : Type} [Fintype ι] (u : ι → ℂ), ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = ∑ i, star (u i) * u i := by
    intro ι _ u
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  exact Complex.ofReal_injective ((key (Formalism.HermitianLatticesTheory.fcoord (S.subB h U) (restrFrame (S.subMat h U) (S.hGram h)) v x)).trans
    (hm.trans (key (Formalism.HermitianLatticesTheory.fcoord (S.hB h) (stdFrame (S.hGram h)) v (x : S.EqFun))).symm))

theorem PosH.isoMat_isometry {h : S.Ok} (hp : S.PosH h) (U : Submodule K S.EqFun) (v : InfinitePlace K) :
    (S.isoMat h U v)ᴴ * S.isoMat h U v = 1 := by
  have hs := Formalism.L2.DIV.restrFrameSpec K _ _ (S.hGram h) hp (S.subMat h U) (S.subMat_injective h U) v
  unfold isoMat
  refine unitary_of_metric_restriction (stdFrame (S.hGram h) v) ((S.subMat h U).map v.embedding) _ hs.1 ?_
  rw [hp.met v]
  exact hs.2.1

theorem PosH.isoMat_fcoord {h : S.Ok} (hp : S.PosH h) (U : Submodule K S.EqFun) (v : InfinitePlace K) (x : U) :
    fcoord (S.hB h) (stdFrame (S.hGram h)) v (x : S.EqFun) =
      (S.isoMat h U v).mulVec (fcoord (S.subB h U) (restrFrame (S.subMat h U) (S.hGram h)) v x) := by
  have hs := Formalism.L2.DIV.restrFrameSpec K _ _ (S.hGram h) hp (S.subMat h U) (S.subMat_injective h U) v
  rw [thl_fcoord_coord (S.hB h), thl_fcoord_coord (S.subB h U), S.hB_equivFun h]
  simp only [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr, isoMat, Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc ((stdFrame (S.hGram h) v)⁻¹ * _), Matrix.mul_nonsing_inv _ hs.1, Matrix.mul_one,
    ← Matrix.mulVec_mulVec, ← S.subB_equivFun h U x]
  congr 1
  funext i
  exact RingHom.map_mulVec v.embedding (S.subMat h U) _ i

variable (S)

def isoHc (h : S.Ok) (L : Submodule (𝓞 K) S.EqFun) : Formalism.L2.GlobalTheoryTheory.HLatOps.Iso (S.toH h L) (S.toHc h L) where
  e := S.hCoord h
  map_L := rfl
  norm := fun v x => by
    show normAt (Pi.basisFun K (Fin (S.hDim h))) (stdFrame (S.hGram h)) v (S.hCoord h x) =
      normAt (S.hB h) (stdFrame (S.hGram h)) v x
    rw [thl_normAt_coord (S.hB h), hB_equivFun]

theorem isLattice_of_map (h : S.Ok) (L : Submodule (𝓞 K) S.EqFun)
    (hL : Submodule.IsLattice K (L.map ((S.hCoord h).toLinearMap.restrictScalars (𝓞 K)))) :
    Submodule.IsLattice K L := by
  refine ⟨Submodule.fg_of_fg_map_injective ((S.hCoord h).toLinearMap.restrictScalars (𝓞 K)) (S.hCoord h).injective hL.fg, ?_⟩
  have h1 := hL.span_eq_top
  have h2 : Submodule.span K ((L.map ((S.hCoord h).toLinearMap.restrictScalars (𝓞 K)) :
      Submodule (𝓞 K) (Fin (S.hDim h) → K)) : Set (Fin (S.hDim h) → K)) =
      (Submodule.span K (L : Set S.EqFun)).map (S.hCoord h).toLinearMap := by
    rw [Submodule.map_span]
    rfl
  rw [h2] at h1
  have h3 := congrArg (Submodule.comap (S.hCoord h).toLinearMap) h1
  rwa [Submodule.comap_map_eq_of_injective (S.hCoord h).injective, Submodule.comap_top] at h3

theorem intDel_isLattice (h : S.Ok) (hD : ∀ d, Submodule.IsLattice K (S.Del d)) :
    Submodule.IsLattice K S.intDel := by
  apply S.isLattice_of_map h
  rw [show S.intDel.map ((S.hCoord h).toLinearMap.restrictScalars (𝓞 K)) = (S.toCSD h).delLat from
    S.map_intDel h S.outSec]
  let _ : Fintype S.Cl := h.fintypeCl
  exact ValuationLatticeField.valLatF_isLattice _ (S.toCSD h).I_injective _ fun c => hD _

theorem intNab_isLattice (h : S.Ok) (hD : ∀ d, Submodule.IsLattice K (S.Nab d)) :
    Submodule.IsLattice K S.intNab := by
  apply S.isLattice_of_map h
  rw [show S.intNab.map ((S.hCoord h).toLinearMap.restrictScalars (𝓞 K)) = (S.toCSD h).nabLat from
    S.map_intNab h S.outSec]
  let _ : Fintype S.Cl := h.fintypeCl
  exact ValuationLatticeField.valLatF_isLattice _ (S.toCSD h).I_injective _ fun c => hD _

variable {S}

theorem PosH.good {h : S.Ok} (hp : S.PosH h) {L : Submodule (𝓞 K) S.EqFun} (hL : Submodule.IsLattice K L) :
    (S.toH h L).Good := ⟨hp.frameOK L, hL.fg, hL.span_eq_top⟩

theorem PosH.good_sub {h : S.Ok} (hp : S.PosH h) {L : Submodule (𝓞 K) S.EqFun} (hL : Submodule.IsLattice K L)
    (U : Submodule K S.EqFun) : (S.subH h U (L.comap (U.subtype.restrictScalars (𝓞 K)))).Good := by
  have h1 := (pull_spec K (S.toH h L) U (Fin (S.subD h U)) (S.subB h U) U.subtype (hp.frameOK L)
    (Submodule.injective_subtype U)).2.2.2.2 (hp.good hL)
  exact ⟨hp.frameOK_sub U _, h1.2.1, h1.2.2⟩

theorem PosH.iso_sub {h : S.Ok} (hp : S.PosH h) (L : Submodule (𝓞 K) S.EqFun) (U : Submodule K S.EqFun) :
    ∃ I : Formalism.L2.GlobalTheoryTheory.HLatOps.Iso (S.subH h U (L.comap (U.subtype.restrictScalars (𝓞 K)))) (sub (S.toH h L) U),
      ∀ x : U, (I.e x : U) = x := by
  obtain ⟨I, hI⟩ := embIso' (S.subH h U (L.comap (U.subtype.restrictScalars (𝓞 K)))) (S.toH h L) U.subtype U
    (hp.frameOK L) (Submodule.injective_subtype U) (Submodule.range_subtype U) (fun v x => hp.sub_norm U v x) rfl
  exact ⟨I, fun x => Subtype.ext (hI x)⟩

end GSD

theorem thl_posDef_sum {ι κ γ : Type} [Fintype ι] [Fintype κ] [Fintype γ] (a : γ → ℂ) (ha : ∀ c, 0 < a c)
    (G : Matrix κ κ ℂ) (hG : G.PosDef) (P : γ → Matrix κ ι ℂ) (hinj : ∀ x, (∀ c, P c *ᵥ x = 0) → x = 0) :
    (∑ c, a c • ((P c)ᴴ * G * P c)).PosDef := by
  have hs : ∀ c, (a c • ((P c)ᴴ * G * P c)).PosSemidef := fun c =>
    (hG.posSemidef.conjTranspose_mul_mul_same (P c)).smul (ha c).le
  have hS := Matrix.posSemidef_sum (s := Finset.univ) (fun c _ => hs c)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hS.1 fun x hx => ?_
  rw [Matrix.sum_mulVec, dotProduct_sum]
  obtain ⟨c, hc⟩ : ∃ c, P c *ᵥ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (hinj x hcon)
  refine Finset.sum_pos' (fun c _ => (hs c).dotProduct_mulVec_nonneg x) ⟨c, Finset.mem_univ c, ?_⟩
  have h1 := hG.dotProduct_mulVec_pos hc
  have h2 : star x ⬝ᵥ ((a c • ((P c)ᴴ * G * P c)) *ᵥ x) = a c * (star (P c *ᵥ x) ⬝ᵥ (G *ᵥ (P c *ᵥ x))) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    congr 1
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [h2]
  exact mul_pos (ha c) h1

theorem csd_hasRatBasis {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (R : S.Rat) :
    S.HasRatBasis := by
  classical
  let A : ∀ c, Module.End K S.V := fun c => (S.wt c : K)⁻¹ • ∑ γ : S.Gam c, S.ρ c γ
  let P : (S.Cl → S.V) →ₗ[K] (S.Cl → S.V) := LinearMap.pi fun c => (A c) ∘ₗ LinearMap.proj c
  have hPc : ∀ f c, P f c = (S.wt c : K)⁻¹ • ∑ γ : S.Gam c, S.ρ c γ (f c) := by
    intro f c
    simp [P, A]
  have hwt : ∀ c, (S.wt c : K) ≠ 0 := fun c => by exact_mod_cast (S.wt_pos c).ne'
  have hmem : ∀ f, P f ∈ S.Forms := by
    intro f c γ'
    rw [hPc, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft γ') _ _ fun γ => ?_
    rw [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]
  have hfix : ∀ f ∈ S.Forms, P f = f := by
    intro f hf
    funext c
    rw [hPc, Finset.sum_congr rfl fun γ _ => hf c γ, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K,
      smul_smul]
    change ((S.wt c : K)⁻¹ * (S.wt c : K)) • f c = f c
    rw [inv_mul_cancel₀ (hwt c), one_smul]
  let B : Basis (Σ _ : S.Cl, S.ιV) K (S.Cl → S.V) := Pi.basis fun _ => S.bV
  have hrange : LinearMap.range P = S.Forms := by
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      exact hmem f
    · intro f hf
      exact ⟨f, hfix f hf⟩
  have hspan : Submodule.span K (P '' Set.range B) = S.Forms := by
    rw [← Submodule.map_span, B.span_eq, Submodule.map_top, hrange]
  have hrat : ∀ t ∈ P '' Set.range B, S.IsRat t := by
    rintro _ ⟨_, ⟨⟨c, j⟩, rfl⟩, rfl⟩ c' i
    rw [hPc, Pi.basis_apply]
    by_cases hcc : c' = c
    · subst hcc
      simp only [Pi.single_eq_same, map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
        smul_eq_mul]
      exact mul_mem (inv_mem (natCast_mem _ _)) (sum_mem fun γ _ => R.act_rat c' γ i j)
    · simp [Pi.single_eq_of_ne hcc]
  obtain ⟨b, hbT, hsp, hli⟩ := exists_linearIndependent K (P '' Set.range B)
  have hZ : Submodule.span K (Set.range ((↑) : b → S.Cl → S.V)) = S.Forms := by
    rw [Subtype.range_coe, hsp, hspan]
  let B1 : Basis b K S.Forms := (Basis.span hli).map (LinearEquiv.ofEq _ _ hZ)
  have : Finite b := Module.Finite.finite_basis B1
  have := Fintype.ofFinite b
  have hcard : Fintype.card b = S.dim := (finrank_eq_card_basis B1).symm
  refine ⟨B1.reindex (Fintype.equivFinOfCardEq hcard), fun j => ?_⟩
  have : ((B1.reindex (Fintype.equivFinOfCardEq hcard)) j : S.Cl → S.V) =
      (((Fintype.equivFinOfCardEq hcard).symm j : b) : S.Cl → S.V) := by
    simp [B1, Basis.span_apply]
  rw [this]
  exact hrat _ (hbT ((Fintype.equivFinOfCardEq hcard).symm j).2)

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

theorem pairAt_add_left (v : InfinitePlace K) (x x' y : S.V) :
    S.pairAt v (x + x') y = S.pairAt v x y + S.pairAt v x' y := by
  simp only [pairAt, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairAt_add_right (v : InfinitePlace K) (x y y' : S.V) :
    S.pairAt v x (y + y') = S.pairAt v x y + S.pairAt v x y' := by
  simp only [pairAt, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairAt_smul_left (v : InfinitePlace K) (a : K) (x y : S.V) :
    S.pairAt v (a • x) y = starRingEnd ℂ (v.embedding a) * S.pairAt v x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pairAt_smul_right (v : InfinitePlace K) (a : K) (x y : S.V) :
    S.pairAt v x (a • y) = v.embedding a * S.pairAt v x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem isSesq_ipAt (h : S.Ok) : IsSesq (fun v (φ ψ : S.EqFun) => S.ipAt h v φ ψ) := by
  intro v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [ipAt, Submodule.coe_add, Pi.add_apply, pairAt_add_left, mul_add, Finset.sum_add_distrib]
  · simp only [ipAt, Submodule.coe_add, Pi.add_apply, pairAt_add_right, mul_add, Finset.sum_add_distrib]
  · simp only [ipAt, Submodule.coe_smul, Pi.smul_apply, pairAt_smul_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · simp only [ipAt, Submodule.coe_smul, Pi.smul_apply, pairAt_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

theorem pairAt_of_rat (v : InfinitePlace K) (x y : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) :
    v.embedding (S.pair x y) = S.pairAt v x y := by
  conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, pairAt,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : v.embedding ((starRingEnd K) (S.bV.repr x i)) = starRingEnd ℂ (v.embedding (S.bV.repr x i)) :=
    hx i v.embedding
  rw [h1, RingHom.id_apply]
  simp only [gramV, Matrix.of_apply]
  ring

def evRep (h : S.Ok) : S.EqFun →ₗ[K] (S.Cl → S.V) := (S.toCSD h).Forms.subtype ∘ₗ (S.res h).toLinearMap

theorem evRep_apply (h : S.Ok) (φ : S.EqFun) (c : S.Cl) : S.evRep h φ c = (φ : S.D → S.V) (S.outSec.rep c) := rfl

theorem evRep_injective (h : S.Ok) : Function.Injective (S.evRep h) :=
  (Submodule.injective_subtype _).comp (S.res h).injective

theorem posAt_ipAt (h : S.Ok) (hpos : ∀ v : InfinitePlace K, (S.gramV.map v.embedding).PosDef)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K S.EqFun) :
    PosAt b (fun v (φ ψ : S.EqFun) => S.ipAt h v φ ψ) := by
  classical
  intro v
  let _ : Fintype S.Cl := h.fintypeCl
  let P : S.Cl → Matrix S.ιV ι ℂ := fun c => Matrix.of fun i a => v.embedding (S.bV.repr (S.evRep h (b a) c) i)
  have hgram : gramOf b (fun (φ ψ : S.EqFun) => S.ipAt h v φ ψ) =
      ∑ c, (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ • ((P c)ᴴ * S.gramV.map v.embedding * P c) := by
    ext a a'
    simp only [gramOf, Matrix.of_apply, ipAt, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp only [pairAt, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, P, Matrix.of_apply,
      Matrix.map_apply, evRep_apply]
    rw [Finset.sum_comm]
    rfl
  rw [hgram]
  refine thl_posDef_sum _ (fun c => ?_) _ (hpos v) P fun x hx => ?_
  · have : (0 : ℝ) < (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (S.toCSD h).wt_pos c)
    have h2 : ((((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ : ℂ) = (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ := by push_cast; rfl
    rw [← h2]
    exact_mod_cast this
  · let Bb : Basis (Σ _ : S.Cl, S.ιV) K (S.Cl → S.V) := Pi.basis fun _ => S.bV
    obtain ⟨g, hg⟩ := (S.evRep h).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 (S.evRep_injective h))
    have h1 : (LinearMap.toMatrix Bb b g).map v.embedding * (LinearMap.toMatrix b Bb (S.evRep h)).map v.embedding = 1 := by
      rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
      simp
    have h2 : (LinearMap.toMatrix b Bb (S.evRep h)).map v.embedding *ᵥ x = 0 := by
      funext ⟨c, i⟩
      have := congrFun (hx c) i
      simpa [Matrix.mulVec, dotProduct, P, LinearMap.toMatrix_apply, Bb, Pi.basis_repr] using this
    have h3 := congrArg ((LinearMap.toMatrix Bb b g).map v.embedding).mulVec h2
    simpa [Matrix.mulVec_mulVec, h1] using h3

theorem gram_ipAt (h : S.Ok) (hr : (S.toCSD h).HasRatBasis) (v : InfinitePlace K) :
    gramOf (S.hB h) (fun (φ ψ : S.EqFun) => S.ipAt h v φ ψ) = (S.hGram h).map v.embedding := by
  ext a a'
  simp only [gramOf, Matrix.of_apply, ipAt, Matrix.map_apply, CSD.H, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have e : ∀ a, ((S.hB h a : S.EqFun) : S.D → S.V) (S.outSec.rep c) = ((S.toCSD h).basis a : S.Cl → S.V) c := by
    intro a
    rw [← S.hB_apply h a]
    rfl
  rw [e, e]
  exact (S.pairAt_of_rat v _ _ fun i => (S.toCSD h).basis_rat hr a c i).symm

theorem Rat.posH {S : GSD K} (R : S.Rat) (h : S.Ok) : S.PosH h := by
  intro v
  rw [← S.gram_ipAt h (csd_hasRatBasis _ (S.toCSDOf_rat h R S.outSec)) v]
  exact S.posAt_ipAt h R.pos (S.hB h) v

theorem Rat.maj_eq {S : GSD K} (R : S.Rat) (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.EqFun) :
    majAt (S.hB h) (stdFrame (S.hGram h)) v φ ψ = S.ipAt h v φ ψ := by
  rw [sesq_eq_sum (isSesq_maj (S.hB h) (stdFrame (S.hGram h))) (S.hB h) v φ ψ,
    sesq_eq_sum (S.isSesq_ipAt h) (S.hB h) v φ ψ, gramOf_maj,
    S.gram_ipAt h (csd_hasRatBasis _ (S.toCSDOf_rat h R S.outSec)) v]
  have := (R.posH h).met v
  unfold metOf at this
  rw [this]

end GSD

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

theorem isSesq_pairAt : IsSesq (fun v (x y : S.V) => S.pairAt v x y) := fun v =>
  ⟨S.pairAt_add_left v, S.pairAt_add_right v, S.pairAt_smul_left v, S.pairAt_smul_right v⟩

theorem bV_rat (i k : S.ιV) : S.bV.repr (S.bV i) k ∈ cmMax K := by
  rw [Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

variable {S}

theorem Rat.pairAt_inv (R : S.Rat) (h : S.Ok) (v : InfinitePlace K) (g : S.G) (x y : S.V) :
    S.pairAt v (S.ρ g x) (S.ρ g y) = S.pairAt v x y := by
  rw [sesq_eq_sum (isSesq_comp S.isSesq_pairAt (S.ρ g)) S.bV v x y, sesq_eq_sum S.isSesq_pairAt S.bV v x y]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2
  simp only [gramOf, Matrix.of_apply]
  rw [← S.pairAt_of_rat v _ _ (fun k => R.act_rat g k i), ← S.pairAt_of_rat v _ _ (S.bV_rat i), h.inv]

theorem Rat.ipAt_indep (R : S.Rat) (h : S.Ok) (s : S.Sec) (v : InfinitePlace K) (φ ψ : S.EqFun) :
    S.ipAt h v φ ψ = letI := h.fintypeCl
      ∑ c : S.Cl, ((Nat.card (MulAction.stabilizer S.G (s.rep c)) : ℕ) : ℂ)⁻¹ *
        S.pairAt v ((φ : S.D → S.V) (s.rep c)) ((ψ : S.D → S.V) (s.rep c)) := by
  unfold ipAt
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := S.outSec.exists_smul s c
  rw [S.wt_eq h S.outSec c, ← hg, S.card_stab_smul, φ.2, ψ.2, R.pairAt_inv h]

end GSD

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

theorem PosH.sub_numbers {h : S.Ok} (hp : S.PosH h) (L' : Submodule (𝓞 K) S.EqFun) (U : Submodule K S.EqFun)
    (L : Submodule (𝓞 K) U) (hL : L.FG) :
    (S.subH h U L).mu = (S.toH h (L.map (U.subtype.restrictScalars (𝓞 K)))).mu ∧
    (S.subH h U L).muMax = (S.toH h (L.map (U.subtype.restrictScalars (𝓞 K)))).muMax ∧
    (S.subH h U L).muMin = (S.toH h (L.map (U.subtype.restrictScalars (𝓞 K)))).muMin := by
  have h1 := ((emb_numbers K (S.subH h U L) (S.toH h L') U.subtype (hp.frameOK L')
    (Submodule.injective_subtype U) (fun v x => hp.sub_norm U v x)).2 L).2 hL
  exact ⟨h1.1, h1.2.1, h1.2.2.1⟩

theorem PosH.muMax_sub_le [IsTotallyComplex K] {h : S.Ok} (hp : S.PosH h) {L : Submodule (𝓞 K) S.EqFun}
    (hL : Submodule.IsLattice K L) (U : Submodule K S.EqFun) (hU : U ≠ ⊥) :
    (S.subH h U (L.comap (U.subtype.restrictScalars (𝓞 K)))).muMax ≤ (S.toH h L).muMax := by
  have hg := hp.good_sub hL U
  rw [(hp.sub_numbers L U _ hg.2.1).2.1]
  refine (with_lattice_index K (S.toH h L) _ (hp.frameOK L) hL.fg (Submodule.map_comap_le _ _) ?_).1
  intro h0
  have hbot : L.comap (U.subtype.restrictScalars (𝓞 K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (U.subtype.restrictScalars (𝓞 K)) x ∈ (⊥ : Submodule (𝓞 K) S.EqFun) := h0 ▸ Submodule.mem_map_of_mem hx
    exact (Submodule.mem_bot _).2 (Subtype.ext ((Submodule.mem_bot _).1 h1))
  apply hU
  have h2 := hg.2.2
  rw [show ((S.subH h U (L.comap (U.subtype.restrictScalars (𝓞 K)))).L) = ⊥ from hbot] at h2
  have h3 : (⊤ : Submodule K U) = ⊥ := by
    rw [← h2]
    simp
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : U) ∈ (⊥ : Submodule K U) := h3 ▸ Submodule.mem_top
  simpa using congrArg Subtype.val ((Submodule.mem_bot K).1 this)

end GSD

section ColsRat

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem colRat (hX : X.Ok) (u : Pr.Word) (j : ℕ) : (colGSD W Ch u j).Rat :=
  formGSD_rat hX _ _ (roundPk_ratP _ _ hX)

theorem thl_colDel_isLattice (u : Pr.Word) (j : ℕ) (d : (colGSD W Ch u j).D) :
    Submodule.IsLattice X.K ((colGSD W Ch u j).Del d) :=
  (nablaDeltaLattice_holds X.K X.Tau (R.N j) (W.lamTrue u j) _ fun τ =>
    (dualFrameLattice_holds X.K (R.N j) 1 _ (by simp) (tauLatticeLattice_holds X.E X.K X.Tau (R.N j) X.emb τ _
      (d : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs).2.Lsh_lattice)).1).2

end ColsRat

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)

theorem colPosH (u : Pr.Word) (j : ℕ) : (colGSD W Ch u j).PosH (colOk W Ch hX u j) :=
  (colRat W Ch hX u j).posH (colOk W Ch hX u j)

include hX in
theorem thl_ColL_isLattice (u : Pr.Word) (j : ℕ) : Submodule.IsLattice X.K (ColL W Ch u j) :=
  (colGSD W Ch u j).intDel_isLattice (colOk W Ch hX u j) (thl_colDel_isLattice W Ch u j)

theorem latH_maj (u : Pr.Word) (j : ℕ) (v : InfinitePlace X.K) (φ ψ : ColV W Ch u j) :
    majAt (latH W Ch hX u j).b (latH W Ch hX u j).X v φ ψ = (colGSD W Ch u j).ipAt (colOk W Ch hX u j) v φ ψ :=
  (colRat W Ch hX u j).maj_eq (colOk W Ch hX u j) v φ ψ

theorem latH_good (u : Pr.Word) (j : ℕ) : (latH W Ch hX u j).Good :=
  (colPosH W Ch hX u j).good (thl_ColL_isLattice W Ch hX u j)

theorem Mu0H_good (u : Pr.Word) : (Mu0H W Ch hX u).Good :=
  latH_good W Ch hX u 0

theorem MramH_good (u : Pr.Word) : (MramH W Ch hX u).Good :=
  (colPosH W Ch hX u 0).good_sub (thl_ColL_isLattice W Ch hX u 0) (MramV W Ch u)

theorem ramInclH_injective (u : Pr.Word) : Function.Injective (ramInclH W Ch hX u) :=
  Submodule.injective_subtype _

theorem ramInclH_norm (u : Pr.Word) (v : InfinitePlace X.K) (x : (MramH W Ch hX u).V) :
    normAt (MramH W Ch hX u).b (MramH W Ch hX u).X v x =
      normAt (Mu0H W Ch hX u).b (Mu0H W Ch hX u).X v (ramInclH W Ch hX u x) :=
  (colPosH W Ch hX u 0).sub_norm (MramV W Ch u) v x

theorem MramH_L (u : Pr.Word) :
    (MramH W Ch hX u).L = (Mu0H W Ch hX u).L.comap ((ramInclH W Ch hX u).restrictScalars (𝓞 X.K)) := rfl

theorem VrC_isometry (u : Pr.Word) (v : InfinitePlace X.K) :
    (VrC W Ch hX u v)ᴴ * VrC W Ch hX u v = 1 :=
  (colPosH W Ch hX u 0).isoMat_isometry (MramV W Ch u) v

theorem VrC_fcoord (u : Pr.Word) (v : InfinitePlace X.K) (x : (MramH W Ch hX u).V) :
    fcoord (Mu0H W Ch hX u).b (Mu0H W Ch hX u).X v (ramInclH W Ch hX u x) =
      (VrC W Ch hX u v).mulVec (fcoord (MramH W Ch hX u).b (MramH W Ch hX u).X v x) :=
  (colPosH W Ch hX u 0).isoMat_fcoord (MramV W Ch u) v x

theorem card_Mu0H (u : Pr.Word) : Fintype.card (Mu0H W Ch hX u).ι = finrank X.K (MfV W Ch u) :=
  (colGSD W Ch u 0).card_toH _ _

theorem card_MramH (u : Pr.Word) : Fintype.card (MramH W Ch hX u).ι = finrank X.K (MramV W Ch u) :=
  (colGSD W Ch u 0).card_subH _ _ _

theorem card_MramH_eq (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) (hT : 2 < Pr.T u) :
    (Fintype.card (MramH W Ch hX u).ι : ℝ) =
      (Fintype.card (Mu0H W Ch hX u).ι : ℝ) * (1 - 1 / ((Pr.T u : ℝ) - 1)) ^ X.f := by
  rw [card_Mu0H, card_MramH]
  have h1 := finrank_MramV_mul W Ch hX hPr hbig u
  have h2 : ((finrank X.K (MramV W Ch u) : ℕ) : ℝ) * ((Pr.T u : ℝ) - 1) ^ X.f =
      ((finrank X.K (MfV W Ch u) : ℕ) : ℝ) * ((Pr.T u : ℝ) - 2) ^ X.f := by
    have := congrArg (Nat.cast : ℕ → ℝ) h1
    push_cast [Nat.cast_sub (show 1 ≤ Pr.T u by omega), Nat.cast_sub (show 2 ≤ Pr.T u by omega)] at this
    exact this
  have hT1 : ((Pr.T u : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) < (Pr.T u : ℝ) := by exact_mod_cast hT
    linarith
  have h3 : (1 - 1 / ((Pr.T u : ℝ) - 1)) = ((Pr.T u : ℝ) - 2) / ((Pr.T u : ℝ) - 1) := by
    field_simp
    ring
  rw [h3, div_pow, ← mul_div_assoc, ← h2, mul_div_assoc, div_self (pow_ne_zero _ hT1), mul_one]

theorem card_MramH_pos (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) (hT : 2 < Pr.T u) :
    0 < Fintype.card (MramH W Ch hX u).ι := by
  rw [card_MramH]
  exact finrank_MramV_pos W Ch hX hPr hbig u hT

theorem MramH_muMax_le (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) (hT : 2 < Pr.T u) :
    (MramH W Ch hX u).muMax ≤ (Mu0H W Ch hX u).muMax := by
  have := hX.cplxK
  refine (colPosH W Ch hX u 0).muMax_sub_le (thl_ColL_isLattice W Ch hX u 0) (MramV W Ch u) ?_
  intro h0
  have h1 := finrank_MramV_pos W Ch hX hPr hbig u hT
  rw [h0, finrank_bot] at h1
  exact lt_irrefl _ h1

theorem MramH_numbers (u : Pr.Word) :
    (MramH W Ch hX u).mu = (withL (Mu0H W Ch hX u) (ramifiedSublattice W Ch u)).mu ∧
    (MramH W Ch hX u).muMax = (withL (Mu0H W Ch hX u) (ramifiedSublattice W Ch u)).muMax ∧
    (MramH W Ch hX u).muMin = (withL (Mu0H W Ch hX u) (ramifiedSublattice W Ch u)).muMin := by
  have h1 := (colPosH W Ch hX u 0).sub_numbers (MfL W Ch u) (MramV W Ch u) (MramL W Ch u) (MramH_good W Ch hX u).2.1
  have h2 : (MramL W Ch u).map ((MramV W Ch u).subtype.restrictScalars (𝓞 X.K)) = ramifiedSublattice W Ch u := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨hy, hy'⟩
      exact ⟨⟨y, hy'⟩, hy, rfl⟩
  rw [h2] at h1
  exact h1

end Cols

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem MtildeH_good (P : LevFam X.E X.K R.r Pr.vGs) : (MtildeH W Ch hX sel mu P).Good :=
  ((mtilde_rat W Ch sel mu hX P).posH (mtildeOk W Ch sel mu hX P)).good
    ((mtildeGSD W Ch sel mu P).intNab_isLattice (mtildeOk W Ch sel mu hX P) (mtilde_good W Ch sel mu hX P).nab_lat)

theorem MtH_good (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) : (MtH W Ch hX sel mu P j).Good :=
  ((mt_rat W Ch sel mu hX P j).posH (mtOk W Ch sel mu hX P j)).good
    ((mtGSD W Ch sel mu P j).intNab_isLattice (mtOk W Ch sel mu hX P j) (mt_good W Ch sel mu hX P j).nab_lat)

end Rows

end Formalism.L2.Col
