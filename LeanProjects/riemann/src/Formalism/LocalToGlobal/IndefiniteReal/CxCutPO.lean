import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxCutEP

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.DIV.CyclotomicLifting Formalism.IndefR.Cx.EigenprojectionMatrices

namespace OrthogonalPartDecomposition

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ} {Z : Submodule K B.S.Forms}

theorem res_eq {Xg : Finset (G → K)} {Sg Sg' : Pl0 → K[X]} (h : Sg ∈ B.resSet Xg) (h' : Sg' ∈ B.resSet Xg)
    {x : B.Pl × ℕ → K} (hx : B.HasRes Sg x) (hx' : B.HasRes Sg' x) : Sg = Sg' := by
  funext P0
  by_cases hP : P0 ∈ Set.range B.pl
  · obtain ⟨P, rfl⟩ := hP
    exact mul_right_cancel₀ (B.blockProd_ne_zero P) ((hx P).symm.trans (hx' P))
  · rw [h.1 P0 hP, h'.1 P0 hP]

theorem map_conjTranspose_of_mem_cmMax {n d : ℕ} (σ : K →+* ℂ) (E : Matrix (Fin n) (Fin d) K) (hE : ∀ i a, E i a ∈ cmMax K) :
    (Eᴴ).map σ = (E.map σ)ᴴ :=
  map_conjTranspose' σ E fun i a => ConjugateWeightGram.isCMSub_cmMax σ _ (hE i a)

theorem HV_map (h : BlockHyp B ℓ v0 s) (σ : K →+* ℂ) :
    (B.HV ℓ).map σ = σ (Nat.card ℓ.P : K)⁻¹ • (((B.vE ℓ).map σ)ᴴ * B.S.H.map σ * (B.vE ℓ).map σ) := by
  have e : B.HV ℓ = (Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  rw [e, ← map_conjTranspose_of_mem_cmMax σ _ (hv_spec h).1, ← Matrix.map_mul, ← Matrix.map_mul]
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem adjC (h : BlockHyp B ℓ v0 s) (hH : B.OkH) (σ : K →+* ℂ) (i : B.Pl × ℕ) :
    ∃ i', (B.HV ℓ).map σ * (tV B ℓ i).map σ = ((tV B ℓ i').map σ)ᴴ * (B.HV ℓ).map σ := by
  obtain ⟨i', hi'⟩ := opMat_adj hH i
  have hHh : B.S.Hᴴ = B.S.H := FinitelyNonzeroLinear.herm_of_pos h.conj (h.ok.hpos v0)
  have h2 : B.S.H * B.opMat i = (B.opMat i')ᴴ * B.S.H := by
    have := congrArg Matrix.conjTranspose hi'
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh] at this
    exact this
  have h2' : B.S.H.map σ * (B.opMat i).map σ = ((B.opMat i').map σ)ᴴ * B.S.H.map σ := by
    rw [← Matrix.map_mul, h2, Matrix.map_mul, map_conjTranspose_of_mem_cmMax σ _ (hH.rat i')]
  have hT : ∀ k, (B.vE ℓ).map σ * (tV B ℓ k).map σ = (B.opMat k).map σ * (B.vE ℓ).map σ := by
    intro k
    rw [← Matrix.map_mul, ← Matrix.map_mul, vE_tV h]
  refine ⟨i', ?_⟩
  rw [HV_map h σ]
  exact adj_transfer _ _ _ _ _ _ _ (hT i) (hT i') h2'

theorem part_orth (h : BlockHyp B ℓ v0 s) (hH : B.OkH) (hZ : ∀ i, Z ≤ Z.comap (B.op i)) (v : InfinitePlace K)
    {Sg Sg' : Pl0 → K[X]} (hSS : ∀ x, B.HasRes Sg' x → ¬ B.HasRes Sg x)
    {x y : Fin (B.dZ ℓ Z) → K} (hx : x ∈ B.part ℓ Z Sg) (hy : y ∈ B.part ℓ Z Sg') :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y = 0 := by
  classical
  have hpq := (pq_orth (Z := Z) h).1
  have hsurj : Function.Surjective (B.Pq ℓ Z).mulVec := fun w =>
    ⟨(B.zE ℓ Z) *ᵥ w, by rw [Matrix.mulVec_mulVec, hpq, Matrix.one_mulVec]⟩
  have hA : ((B.HV ℓ).map v.embedding).PosDef := (hv_spec h).2.2 v
  have hQ : (quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding)).PosDef :=
    (quotRestrPosDef _ _ _ hA).1 _ (map_surj v.embedding _ hsurj)
  have hmet : metOf (B.XQ ℓ Z v) = quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding) :=
    (frameOfSpec _ _ hQ).2
  have hR : IsUnit (((B.Pq ℓ Z).map v.embedding) * ((B.HV ℓ).map v.embedding)⁻¹ *
      ((B.Pq ℓ Z).map v.embedding)ᴴ).det := by
    have : IsUnit (quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding)).det :=
      isUnit_iff_ne_zero.2 hQ.det_pos.ne'
    rwa [quotMetC, Matrix.isUnit_nonsing_inv_det_iff] at this
  have hc : Col.PairComm (linF fun i => (tV B ℓ i).map v.embedding) := fun i j =>
    linF_commute (by rw [← Matrix.map_mul, ← Matrix.map_mul, tV_comm h])
  have hs : Col.SplitOver (linF fun i => (tV B ℓ i).map v.embedding) := fun i =>
    Module.End.iSup_maxGenEigenspace_eq_top _
  have hcf : Col.PairComm (linF fun i => (B.opMat i).map v.embedding) := fun i j =>
    linF_commute (by rw [← Matrix.map_mul, ← Matrix.map_mul, opMat_comm h.ok.comm])
  have hvv : B.vPr ℓ * B.vE ℓ = 1 := (BlockDat.lf_v_proj h).1.1
  have hΨ : (B.vPr ℓ).map v.embedding * (B.vE ℓ).map v.embedding = 1 := by
    rw [← Matrix.map_mul, hvv, map_one']
  have hΦ : ∀ i, (B.vE ℓ).map v.embedding * (tV B ℓ i).map v.embedding =
      (B.opMat i).map v.embedding * (B.vE ℓ).map v.embedding := fun i => by
    rw [← Matrix.map_mul, ← Matrix.map_mul, vE_tV h]
  have hmem : ∀ {S : Pl0 → K[X]} {z : Fin (B.dZ ℓ Z) → K}, z ∈ B.part ℓ Z S →
      (fun a => v.embedding ((B.zE ℓ Z *ᵥ z) a)) ∈ Col.eigSum (linF fun i => (tV B ℓ i).map v.embedding)
        (fun w => ∃ x, B.HasRes S x ∧ w = fun i => v.embedding (x i)) := by
    intro S z hz
    have h0 : B.S.basis.equivFun.symm (B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z)) ∈ Col.eigSum B.op (B.HasRes S) := by
      have := hz
      rw [BlockDat.part, Submodule.mem_comap, BlockDat.mem_goodPart_iff] at this
      exact this
    have h1 : B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z) ∈ Col.eigSum (fun i => Matrix.toLin' (B.opMat i)) (B.HasRes S) := by
      have := eigSum_le_comap_of (B.S.basis.equivFun : B.S.Forms →ₗ[K] (Fin B.S.dim → K)) B.op
        (fun i => Matrix.toLin' (B.opMat i)) (fun i f => by rw [Matrix.toLin'_apply]; exact equivFun_op i f) _ h0
      rwa [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    have h2 := emb_mem_eigSum v.embedding B.opMat (B.HasRes S) h1
    refine mem_eigSum_of_emb _ _ ((B.vE ℓ).map v.embedding) ((B.vPr ℓ).map v.embedding) hΨ hΦ hc hs hcf _ ?_
    rw [← emb_mulVec]
    exact h2
  have hPN : ∀ i, (B.Pq ℓ Z).map v.embedding * (tV B ℓ i).map v.embedding =
      (B.Pq ℓ Z * tV B ℓ i * B.zE ℓ Z).map v.embedding * (B.Pq ℓ Z).map v.embedding := fun i => by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun M => M.map v.embedding) (Pq_tV h hH hZ i)
  have hCC : ∀ w, (fun w => ∃ x, B.HasRes Sg' x ∧ w = fun i => v.embedding (x i)) w →
      ¬ (fun w => ∃ x, B.HasRes Sg x ∧ w = fun i => v.embedding (x i)) w := by
    rintro w ⟨x', hx', rfl⟩ ⟨x, hx, e⟩
    have : x' = x := funext fun i => v.embedding.injective (by simpa using congrFun e i)
    subst this
    exact hSS x' hx' hx
  have key := cx_quot_orth (fun i => (tV B ℓ i).map v.embedding) ((B.HV ℓ).map v.embedding) hA
    (adjC h hH v.embedding) ((B.Pq ℓ Z).map v.embedding) _ hPN hR hc hs hCC (hmem hx) (hmem hy)
  have ex : ∀ z : Fin (B.dZ ℓ Z) → K,
      (B.Pq ℓ Z).map v.embedding *ᵥ (fun a => v.embedding ((B.zE ℓ Z *ᵥ z) a)) = fun a => v.embedding (z a) := by
    intro z
    rw [← emb_mulVec, Matrix.mulVec_mulVec, hpq, Matrix.one_mulVec]
  rw [ex, ex] at key
  rw [Formalism.L2.DIV.majAt_eq, hmet]
  exact key

end OrthogonalPartDecomposition

section Main

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)
variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

theorem partsOrth_at {s : ℕ} (hOk : A.fam.Ok s) (hH : HeckeRatR A) (hst : X.zs.Stable) (P : Subgroup G)
    (ψ : P →* Kˣ) (v : InfinitePlace K) (p q : A.fam.base.Ix) (hpq : p ≠ q)
    (x : Fin ((A.fam.side P ψ X.zs).dQ A.fam.μ0) → K) (hx : x ∈ (A.fam.side P ψ X.zs).Qp A.fam.μ0 p)
    (y : Fin ((A.fam.side P ψ X.zs).dQ A.fam.μ0) → K) (hy : y ∈ (A.fam.side P ψ X.zs).Qp A.fam.μ0 q) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((A.fam.side P ψ X.zs).XQ A.fam.μ0) v x y = 0 := by
  have hok := hOk.what₂ A.fam.μ0
  have hZ : ∀ i, X.Z A.fam.μ0 ≤ (X.Z A.fam.μ0).comap ((A.fam.R A.fam.μ0).op i) := fun i =>
    Submodule.map_le_iff_le_comap.1 (hst.1 A.fam.μ0 (Sum.inl i))
  have hmemR : ∀ r : A.fam.base.Ix, r.1 ∈ (A.fam.R A.fam.μ0).resSet A.fam.X := fun r =>
    ((A.fam.R A.fam.μ0).mem_ixFin hok.comm _ _).1 r.2
  have hSS : ∀ z, (A.fam.R A.fam.μ0).HasRes q.1 z → ¬ (A.fam.R A.fam.μ0).HasRes p.1 z := by
    intro z hq hp
    exact hpq (Subtype.ext (OrthogonalPartDecomposition.res_eq (hmemR p) (hmemR q) hp hq))
  exact OrthogonalPartDecomposition.part_orth (B := A.fam.R A.fam.μ0) (ℓ := A.fam.lvl P ψ) (Z := X.Z A.fam.μ0)
    ⟨hOk.conj, hOk.irr, hok⟩ hH hZ v hSS hx hy

theorem cutPartsOrth : CutPartsOrth A X P0 ψ0 P1 ψ1 Dc Sp Zsc := by
  intro s hOk hH hst b
  cases b
  · exact fun v _ p q hpq x hx y hy => partsOrth_at A X hOk hH hst P0 ψ0 v p q hpq x hx y hy
  · exact fun v _ p q hpq x hx y hy => partsOrth_at A X hOk hH hst P1 ψ1 v p q hpq x hx y hy

end Main

end Formalism.IndefR.Cx
