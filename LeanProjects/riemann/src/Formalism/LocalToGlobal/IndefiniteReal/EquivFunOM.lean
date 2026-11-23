import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxCutPO

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.DIV.CyclotomicLifting Formalism.IndefR.Cx.EigenprojectionMatrices Formalism.IndefR.Cx.OrthogonalPartDecomposition

namespace GroupActionMatrices

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ} {Z : Submodule K B.S.Forms} {I : Type}

def oM (B : BlockDat K G Pl0) (op : I → Module.End K B.S.Forms) (i : I) : Matrix (Fin B.S.dim) (Fin B.S.dim) K :=
  LinearMap.toMatrix B.S.basis B.S.basis (op i)

structure OkOp (B : BlockDat K G Pl0) (op : I → Module.End K B.S.Forms) : Prop where

  rat : ∀ i a b, oM B op i a b ∈ cmMax K

  adj : ∀ i, ∃ i', ∀ f g : B.S.Forms,
    B.S.csum (op i f : B.S.Cl → B.S.V) (g : B.S.Cl → B.S.V) = B.S.csum (f : B.S.Cl → B.S.V) (op i' g : B.S.Cl → B.S.V)

  comm : Col.PairComm op

  split : Col.SplitOver op

  opG : ∀ i g, Commute (op i) (B.r g)

variable {op : I → Module.End K B.S.Forms}

theorem equivFun_oM (i : I) (f : B.S.Forms) :
    B.S.basis.equivFun (op i f) = (oM B op i).mulVec (B.S.basis.equivFun f) := by
  exact equivFun_end (op i) f

theorem oM_comm (hc : Col.PairComm op) (i j : I) : oM B op i * oM B op j = oM B op j * oM B op i := by
  simp only [oM]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, (hc i j).eq]

private theorem okH_of_okOp (hO : OkOp B op) : BlockDat.OkH ({ S := B.S, r := B.r, Pl := I, pl := id, q := fun _ => 1, n := B.n, t := 1, op := fun p => op p.1, bl := [fun _ => 1] } : BlockDat K G I) :=
  { rat := fun p a b => hO.rat p.1 a b
    adj := fun p => by
      obtain ⟨i', hi'⟩ := hO.adj p.1
      exact ⟨(i', 0), hi'⟩ }

theorem oM_adj (hO : OkOp B op) (i : I) : ∃ i', (oM B op i)ᴴ * B.S.H = B.S.H * oM B op i' := by
  obtain ⟨i', hi'⟩ := opMat_adj (okH_of_okOp hO) (i, 0)
  exact ⟨i'.1, hi'⟩

private theorem blockHyp_of_okOp (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) : BlockHyp ({ S := B.S, r := B.r, Pl := I, pl := id, q := fun _ => 1, n := B.n, t := 1, op := fun p => op p.1, bl := [fun _ => 1] } : BlockDat K G I) ℓ v0 s :=
  { conj := h.conj
    irr := h.irr
    ok :=
    { good := h.ok.good
      hrat := h.ok.hrat
      hpos := h.ok.hpos
      act := h.ok.act
      actRat := h.ok.actRat
      comm := fun p q => hO.comm p.1 q.1
      split := fun p => hO.split p.1
      opG := fun p g => hO.opG p.1 g
      blocks := ⟨le_rfl, List.cons_ne_nil _ _, by simp⟩
      q_pos := fun _ => Nat.one_pos
      pl_inj := Function.injective_id } }

private theorem eigSum_prod_nat_eq_eigSum (C : (I → K) → Prop) :
    Col.eigSum (fun p : I × ℕ => op p.1) (fun y => C (fun i => y (i, 0))) = Col.eigSum op C := by
  apply le_antisymm
  · refine iSup₂_le fun y hy => le_trans ?_ (le_iSup₂ (f := fun x (_ : C x) => Col.eigAt op x) _ hy)
    exact le_iInf fun i => iInf_le (fun p : I × ℕ => (op p.1).maxGenEigenspace (y p)) (i, 0)
  · refine iSup₂_le fun x hx => ?_
    have h2 : Col.eigAt op x ≤ Col.eigAt (fun p : I × ℕ => op p.1) (fun p => x p.1) :=
      le_iInf fun p => iInf_le (fun i => (op i).maxGenEigenspace (x i)) p.1
    refine h2.trans ?_
    unfold Col.eigSum
    refine le_trans ?_ (le_iSup _ (fun p : I × ℕ => x p.1))
    exact le_iSup_of_le (show C (fun i => x i) from hx) le_rfl

theorem eig_ratG (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (C : (I → K) → Prop) :
    SubHasRatBasis (B.inV0 ℓ (Col.eigSum op C)) := by
  have h1 := eig_rat (blockHyp_of_okOp h hO) (okH_of_okOp hO) (fun y => C (fun i => y (i, 0)))
  rw [eigSum_prod_nat_eq_eigSum] at h1
  exact h1

def tVg (B : BlockDat K G Pl0) (ℓ : Lvl K G) (op : I → Module.End K B.S.Forms) (i : I) : Matrix (Fin (B.nV ℓ)) (Fin (B.nV ℓ)) K :=
  B.vPr ℓ * oM B op i * B.vE ℓ

theorem vE_tVg (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (i : I) : B.vE ℓ * tVg B ℓ op i = oM B op i * B.vE ℓ := by
  exact vE_tV (blockHyp_of_okOp h hO) (i, 0)

theorem tVg_comm (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (i j : I) : tVg B ℓ op i * tVg B ℓ op j = tVg B ℓ op j * tVg B ℓ op i := by
  exact tV_comm (blockHyp_of_okOp h hO) (i, 0) (j, 0)

theorem Pq_tVg (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (hZ : ∀ i, Z ≤ Z.comap (op i)) (i : I) :
    B.Pq ℓ Z * tVg B ℓ op i = (B.Pq ℓ Z * tVg B ℓ op i * B.zE ℓ Z) * B.Pq ℓ Z := by
  exact Pq_tV (blockHyp_of_okOp h hO) (okH_of_okOp hO) (fun p => hZ p.1) (i, 0)

theorem adjCg (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (σ : K →+* ℂ) (i : I) :
    ∃ i', (B.HV ℓ).map σ * (tVg B ℓ op i).map σ = ((tVg B ℓ op i').map σ)ᴴ * (B.HV ℓ).map σ := by
  obtain ⟨i', hi'⟩ := adjC (blockHyp_of_okOp h hO) (okH_of_okOp hO) σ (i, 0)
  exact ⟨i'.1, hi'⟩

theorem part_orthg (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (hZ : ∀ i, Z ≤ Z.comap (op i)) (v : InfinitePlace K)
    {C C' : (I → K) → Prop} (hSS : ∀ x, C' x → ¬ C x)
    {x y : Fin (B.dZ ℓ Z) → K} (hx : x ∈ (B.inV0 ℓ (Col.eigSum op C)).comap (B.zE ℓ Z).mulVecLin)
    (hy : y ∈ (B.inV0 ℓ (Col.eigSum op C')).comap (B.zE ℓ Z).mulVecLin) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y = 0 := by
  have hA : ((B.HV ℓ).map v.embedding).PosDef := BlockDat.lf_HV_pos h v
  have hc : Col.PairComm (linF fun i => (tVg B ℓ op i).map v.embedding) := fun i j => by
    refine linF_commute ?_
    have e := congrArg (fun M => M.map v.embedding) (tVg_comm h hO i j)
    simpa only [Matrix.map_mul] using e
  have hs : Col.SplitOver (linF fun i => (tVg B ℓ op i).map v.embedding) := fun i =>
    Module.End.iSup_maxGenEigenspace_eq_top _
  have hcf : Col.PairComm (linF fun i => (oM B op i).map v.embedding) := fun i j => by
    refine linF_commute ?_
    have e := congrArg (fun M => M.map v.embedding) (oM_comm hO.comm i j)
    simpa only [Matrix.map_mul] using e
  have hvv : B.vPr ℓ * B.vE ℓ = 1 := (BlockDat.lf_v_proj h).1.1

  have key : ∀ {D : (I → K) → Prop} {w : Fin (B.dZ ℓ Z) → K},
      w ∈ (B.inV0 ℓ (Col.eigSum op D)).comap (B.zE ℓ Z).mulVecLin →
      (fun a => v.embedding ((B.zE ℓ Z *ᵥ w) a)) ∈ Col.eigSum (linF fun i => (tVg B ℓ op i).map v.embedding)
        (fun y => ∃ x, D x ∧ y = fun i => v.embedding (x i)) := by
    intro D w hw
    have h1 : B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ w) ∈ Col.eigSum (fun i => Matrix.toLin' (oM B op i)) D := by
      have hw' : (B.vE ℓ).mulVecLin ((B.zE ℓ Z).mulVecLin w) ∈ B.coord (Col.eigSum op D) := hw
      obtain ⟨F, hF, hFe⟩ := Submodule.mem_map.1 hw'
      have h3 := eigSum_le_comap_of (B.S.basis.equivFun : B.S.Forms →ₗ[K] (Fin B.S.dim → K)) op
        (fun i => Matrix.toLin' (oM B op i))
        (fun i f => by simp only [LinearEquiv.coe_coe, equivFun_oM, Matrix.toLin'_apply]) D hF
      rw [Submodule.mem_comap, hFe] at h3
      simpa only [Matrix.mulVecLin_apply] using h3
    have h2 := emb_mem_eigSum v.embedding (oM B op) D h1
    refine mem_eigSum_of_emb _ _ ((B.vE ℓ).map v.embedding) ((B.vPr ℓ).map v.embedding)
      (by rw [← Matrix.map_mul, hvv, Matrix.map_one _ (map_zero _) (map_one _)])
      (fun i => by
        have e := congrArg (fun M => M.map v.embedding) (vE_tVg h hO i)
        simpa only [Matrix.map_mul] using e) hc hs hcf _ ?_
    have e : (B.vE ℓ).map v.embedding *ᵥ (fun a => v.embedding ((B.zE ℓ Z *ᵥ w) a)) =
        fun a => v.embedding ((B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ w)) a) := by
      ext a
      exact (RingHom.map_mulVec _ _ _ _).symm
    rw [e]
    exact h2
  have hx' := key hx
  have hy' := key hy
  have hCC : ∀ y, (fun y => ∃ x, C' x ∧ y = fun i => v.embedding (x i)) y →
      ¬ (fun y => ∃ x, C x ∧ y = fun i => v.embedding (x i)) y := by
    rintro y ⟨x', hx1, rfl⟩ ⟨x, hx2, hxx⟩
    have hxe : x = x' := funext fun i => v.embedding.injective (congrFun hxx i).symm
    exact hSS x' hx1 (hxe ▸ hx2)
  have hPN : ∀ i, (B.Pq ℓ Z).map v.embedding * (tVg B ℓ op i).map v.embedding =
      (B.Pq ℓ Z * tVg B ℓ op i * B.zE ℓ Z).map v.embedding * (B.Pq ℓ Z).map v.embedding := fun i => by
    have e := congrArg (fun M => M.map v.embedding) (Pq_tVg h hO hZ i)
    simpa only [Matrix.map_mul] using e
  have hPz : B.Pq ℓ Z * B.zE ℓ Z = 1 := (pq_orth (Z := Z) h).1
  have hPu : ∀ w : Fin (B.dZ ℓ Z) → K,
      (B.Pq ℓ Z).map v.embedding *ᵥ (fun a => v.embedding ((B.zE ℓ Z *ᵥ w) a)) = fun a => v.embedding (w a) := by
    intro w
    ext a
    have e := (RingHom.map_mulVec v.embedding (B.Pq ℓ Z) (B.zE ℓ Z *ᵥ w) a).symm
    rw [Matrix.mulVec_mulVec, hPz, Matrix.one_mulVec] at e
    exact e
  have hq : IsQuotMetric (B.Pq ℓ Z) (B.HV ℓ) (B.XQ ℓ Z) := BlockDat.XQ_quot h.conj h.ok h.irr
  have hvx : ∀ w : Fin (B.dZ ℓ Z) → K,
      Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin (B.dZ ℓ Z))) v w = fun a => v.embedding (w a) := fun w => by
    ext a
    simp [Formalism.HermitianLatticesTheory.vecAt]
  rw [Formalism.HermitianLatticesTheory.majBasic_majAt, (hq v).2, hvx, hvx]
  by_cases hR : IsUnit ((B.Pq ℓ Z).map v.embedding * ((B.HV ℓ).map v.embedding)⁻¹ *
      ((B.Pq ℓ Z).map v.embedding)ᴴ).det
  · have e := cx_quot_orth (hA := hA) (adj := adjCg h hO v.embedding) (hPN := hPN) (hR := hR) (hc := hc)
      (hs := hs) (hCC := hCC) (hu := hx') (hu' := hy')
    rw [hPu, hPu] at e
    exact e
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hR]
    simp

end GroupActionMatrices

end Formalism.IndefR.Cx
