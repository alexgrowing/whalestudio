import Mathlib
import Formalism.LocalToGlobal.Divisibility.RowLat
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.PlaceSumSquares
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjTransposeEqOfPosDef
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)

section Basic

variable {B ℓ} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s)
  (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ)

include hv0 h hX

theorem vE_rat (i j) : B.vE ℓ i j ∈ cmMax K :=
  (good_part_hermitian_spec K v0 hv0 B.S h.hrat h.hpos G B.r h.actRat ℓ.X hX ℓ.P ℓ.ψ).1 i j

theorem HV_rat (i j) : B.HV ℓ i j ∈ cmMax K :=
  (good_part_hermitian_spec K v0 hv0 B.S h.hrat h.hpos G B.r h.actRat ℓ.X hX ℓ.P ℓ.ψ).2.1 i j

theorem HV_pos (v : InfinitePlace K) : ((B.HV ℓ).map v.embedding).PosDef :=
  (good_part_hermitian_spec K v0 hv0 B.S h.hrat h.hpos G B.r h.actRat ℓ.X hX ℓ.P ℓ.ψ).2.2 v

theorem nab_lat : Submodule.IsLattice K B.S.nabLat :=
  (local_bounds_first K v0 hv0 B.S s h.good (h.hpos v0) G B.r h.act ℓ.X hX ℓ.P ℓ.ψ).1

theorem Mt_lat : Submodule.IsLattice K (B.Mt ℓ) :=
  (local_bounds_first K v0 hv0 B.S s h.good (h.hpos v0) G B.r h.act ℓ.X hX ℓ.P ℓ.ψ).2.1

theorem Mt_dual : ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (B.HV ℓ)) (B.Mt ℓ),
    ((Fintype.card G * s : ℕ) : 𝓞 K) • x ∈ B.Mt ℓ :=
  (local_bounds_first K v0 hv0 B.S s h.good (h.hpos v0) G B.r h.act ℓ.X hX ℓ.P ℓ.ψ).2.2

theorem vPr_orth : IsOrthProj B.S.H (B.vE ℓ) (B.vPr ℓ) :=
  (level_operator_integral K v0 hv0 B.S (h.hpos v0) G B.r h.act ℓ.X hX ℓ.P ℓ.ψ).1

theorem Pq_orth : IsOrthProj (B.HV ℓ) (B.zE ℓ Z) (B.Pq ℓ Z) :=
  (orthogonal_projection_exists K v0 hv0 _ _ (B.HV ℓ) (HV_pos hv0 h hX v0) (B.zE ℓ Z)
    (subspace_image_spec K _ (B.Z0 ℓ Z)).1).2.2.2.1

theorem HZ_det : IsUnit (B.HZ ℓ Z).det :=
  (orthogonal_projection_exists K v0 hv0 _ _ (B.HV ℓ) (HV_pos hv0 h hX v0) (B.zE ℓ Z)
    (subspace_image_spec K _ (B.Z0 ℓ Z)).1).2.2.1

theorem Pq_surj : Function.Surjective (B.Pq ℓ Z).mulVec := by
  intro y
  refine ⟨(B.zE ℓ Z).mulVec y, ?_⟩
  rw [Matrix.mulVec_mulVec, (Pq_orth hv0 h hX).1, Matrix.one_mulVec]

theorem XQ_quot : IsQuotMetric (B.Pq ℓ Z) (B.HV ℓ) (B.XQ ℓ Z) :=
  quotFrameIsQuot K _ _ (B.HV ℓ) (HV_pos hv0 h hX) (B.Pq ℓ Z) (Pq_surj hv0 h hX)

theorem Lam_lat : Submodule.IsLattice K (B.abelian₂ ℓ Z) :=
  GluingInclusion.matLat_lattice' (B.Pq ℓ Z) (Pq_surj hv0 h hX) (B.Mt ℓ) (Mt_lat hv0 h hX)

theorem XQ_herm : IsHermAt v0 (B.HZ ℓ Z) (B.XQ ℓ Z) :=
  quotFrameHermAt K v0 hv0 _ _ (B.HV ℓ) (HV_pos hv0 h hX) (B.zE ℓ Z) (B.Pq ℓ Z) (Pq_orth hv0 h hX)

theorem XQ_rat (hr : SubHasRatBasis (B.Z0 ℓ Z)) : IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) := by
  have hE : ∀ i a, B.zE ℓ Z i a ∈ cmMax K := fun i a => subE_rat (B.Z0 ℓ Z) hr i a
  have e : B.XQ ℓ Z = restrFrame (B.zE ℓ Z) (B.HV ℓ) :=
    quotEqRestrRat K (cmMax K) (isCMSub_cmMax' K) _ _ (B.HV ℓ) (HV_pos hv0 h hX) (B.zE ℓ Z) (B.Pq ℓ Z) hE
      (Pq_orth hv0 h hX)
  rw [e]
  exact (restrFrameRatHerm K (cmMax K) (isCMSub_cmMax' K) (fun a ha => star_mem_cmMax ha) _ _ (B.HV ℓ)
    (HV_rat hv0 h hX) (HV_pos hv0 h hX) (B.zE ℓ Z) (subspace_image_spec K _ (B.Z0 ℓ Z)).1 hE).1

theorem ker_Pq : LinearMap.ker (B.Pq ℓ Z).mulVecLin = B.U ℓ Z := by
  obtain ⟨h1, h2⟩ := Pq_orth hv0 h hX
  have hrange := (subspace_image_spec K _ (B.Z0 ℓ Z)).2
  ext x
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hx z hz
    have hz' : z ∈ LinearMap.range (B.zE ℓ Z).mulVecLin := by rw [show B.zE ℓ Z = subE (B.Z0 ℓ Z) from rfl, hrange]; exact hz
    obtain ⟨a, rfl⟩ := hz'
    have h3 := congrArg (fun M => star a ⬝ᵥ M.mulVec x) h2
    simp only [Matrix.zero_mulVec, dotProduct_zero] at h3
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec _ _ (B.zE ℓ Z * B.Pq ℓ Z),
      ← Matrix.mulVec_mulVec x (B.zE ℓ Z), hx, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero] at h3
    rw [Matrix.mulVecLin_apply, RationalHermitianForm.hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec]
    exact h3
  · intro hx
    have h4 : ((B.zE ℓ Z)ᴴ * B.HV ℓ).mulVec x = 0 := by
      ext a
      have := hx ((B.zE ℓ Z).mulVec (Pi.single a 1)) (by
        rw [← hrange]; exact ⟨_, rfl⟩)
      rw [RationalHermitianForm.hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
        Matrix.mulVec_mulVec] at this
      have e : star (Pi.single a (1 : K) : Fin (B.dZ ℓ Z) → K) = Pi.single a 1 := by
        ext i
        by_cases hi : i = a
        · subst hi; simp
        · simp [Pi.single_eq_of_ne hi]
      rw [e, single_one_dotProduct] at this
      exact this
    show (((B.zE ℓ Z)ᴴ * B.HV ℓ * B.zE ℓ Z)⁻¹ * ((B.zE ℓ Z)ᴴ * B.HV ℓ)).mulVec x = 0
    rw [← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]

theorem range_vE_le : LinearMap.range (B.vE ℓ).mulVecLin ≤
    LinearMap.range (B.S.lvlE B.r ℓ.P ℓ.ψ).mulVecLin := by
  have h1 := good_part_spec K B.S G B.r ℓ.X hX ℓ.P ℓ.ψ
  have h2 := level_part_spec K B.S G B.r ℓ.P ℓ.ψ
  have h3 := (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ))).2
  calc LinearMap.range (B.vE ℓ).mulVecLin ≤ B.S.lvlPart B.r ℓ.P ℓ.ψ := by
        rw [show B.vE ℓ = B.S.V0E B.r ℓ.X ℓ.P ℓ.ψ from rfl, h1]; exact inf_le_right
    _ = LinearMap.range (B.S.lvlE B.r ℓ.P ℓ.ψ).mulVecLin := by rw [← h2, ← h3]; rfl

theorem lPr_surj : Function.Surjective (B.lPr ℓ Z).mulVec := by
  intro y
  obtain ⟨u, hu⟩ := range_vE_le hv0 h hX (⟨(B.zE ℓ Z).mulVec y, rfl⟩ :
    (B.vE ℓ).mulVecLin ((B.zE ℓ Z).mulVec y) ∈ LinearMap.range (B.vE ℓ).mulVecLin)
  refine ⟨u, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hu
  unfold lPr
  rw [← Matrix.mulVec_mulVec, hu, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (B.vPr ℓ),
    (vPr_orth hv0 h hX).1, Matrix.one_mulVec, Matrix.mulVec_mulVec, (Pq_orth hv0 h hX).1,
    Matrix.one_mulVec]

theorem lvlNab_lat : Submodule.IsLattice K (B.S.lvlNab B.r ℓ.P ℓ.ψ) :=
  exponent_index_lattice.cut_isLattice _ (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ))).1 _
    (nab_lat (ℓ := ℓ) hv0 h hX)

theorem Tl_lat : Submodule.IsLattice K (B.Tl ℓ Z) :=
  GluingInclusion.matLat_lattice' (B.lPr ℓ Z) (lPr_surj hv0 h hX) _ (lvlNab_lat hv0 h hX)

end Basic

end BlockDat

section Eig

open Formalism.L2.Col

variable {K V W I : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {op : I → Module.End K V}

theorem iSupIndep_comap {ι : Type} (f : W →ₗ[K] V) (hf : Function.Injective f) {A : ι → Submodule K V}
    (hA : iSupIndep A) : iSupIndep fun i => (A i).comap f := by
  intro i
  have hle : (⨆ j, ⨆ (_ : j ≠ i), (A j).comap f) ≤ (⨆ j, ⨆ (_ : j ≠ i), A j).comap f :=
    iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂_of_le j hj le_rfl)
  refine Disjoint.mono_right hle ?_
  rw [Submodule.disjoint_def]
  intro x hx1 hx2
  have h0 : f x = 0 := (Submodule.disjoint_def.mp (hA i)) (f x) hx1 hx2
  exact hf (h0.trans (map_zero f).symm)

theorem iSupIndep_eigSum [FiniteDimensional K V] (hc : PairComm op) {ι : Type} (C : ι → (I → K) → Prop)
    (hex : ∀ i j, i ≠ j → ∀ x, C i x → ¬ C j x) : iSupIndep fun i => eigSum op (C i) := by
  intro i
  have hle : (⨆ j, ⨆ (_ : j ≠ i), eigSum op (C j)) ≤ eigSum op fun x => ∃ j, j ≠ i ∧ C j x :=
    iSup₂_le fun j hj => eigSum_mono fun x hx => ⟨j, hj, hx⟩
  exact (disjoint_eigSum hc fun x hx ⟨j, hj, hx'⟩ => hex i j hj.symm x hx hx').mono_right hle

theorem sum_eigProj [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op) {ι : Type} [Fintype ι]
    (C : ι → (I → K) → Prop) (hex : ∀ i j, i ≠ j → ∀ x, C i x → ¬ C j x) {v : V}
    (hv : v ∈ eigSum op fun x => ∃ i, C i x) : ∑ i, eigProj hc hs (C i) v = v := by
  classical
  have hle : (eigSum op fun x => ∃ i, C i x) ≤
      LinearMap.ker ((∑ i, eigProj hc hs (C i)) - LinearMap.id) := by
    refine iSup₂_le fun x hx u hu => ?_
    obtain ⟨i0, hi0⟩ := hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.id_apply,
      Finset.sum_eq_single i0, eigProj_apply_of_mem hc hs (eigAt_le_eigSum hi0 hu), sub_self]
    · intro j _ hj
      exact eigProj_apply_of_mem_not hc hs
        (eigAt_le_eigSum (C := fun x => ¬ C j x) (hex i0 j hj.symm x hi0) hu)
    · intro h; exact absurd (Finset.mem_univ i0) h
  have := hle hv
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.id_apply, sub_eq_zero] at this
  exact this

theorem eigProj_mem_of_stable [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op)
    (C : (I → K) → Prop) {A : Submodule K V} (hA : ∀ i, A ≤ A.comap (op i)) {v : V} (hv : v ∈ A) :
    eigProj hc hs C v ∈ A := by
  let opA : I → Module.End K A := fun i => (op i).restrict (hA i)
  have hcA : PairComm opA := by
    intro i j
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact congrArg (fun f : Module.End K V => f a.1) (hc i j).eq
  have hsA : SplitOver opA := fun i =>
    Module.End.genEigenspace_restrict_eq_top (hA i) (hs i)
  have htop := iSup_eigAt_eq_top hcA hsA
  have key : ∀ a : A, eigProj hc hs C a.1 ∈ A := by
    intro a
    have ha : a ∈ ⨆ x, eigAt opA x := by rw [htop]; exact Submodule.mem_top
    induction ha using Submodule.iSup_induction' with
    | mem x a ha =>
      have h1 : a.1 ∈ eigAt op x := by
        rw [eigAt, Submodule.mem_iInf] at ha ⊢
        intro i
        have h2 := ha i
        rw [Module.End.maxGenEigenspace, Module.End.genEigenspace_restrict] at h2
        exact h2
      by_cases hx : C x
      · rw [eigProj_apply_of_mem hc hs (eigAt_le_eigSum hx h1)]
        exact a.2
      · rw [eigProj_apply_of_mem_not hc hs (eigAt_le_eigSum (C := fun x => ¬ C x) hx h1)]
        exact A.zero_mem
    | zero => simp
    | add a b _ _ iha ihb =>
      rw [Submodule.coe_add, map_add]
      exact A.add_mem iha ihb
  exact key ⟨v, hv⟩

end Eig

namespace CSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)

theorem gaMat_eq_toMatrix (a : MonoidAlgebra K G) :
    S.gaMat r a = LinearMap.toMatrix S.basis S.basis (S.gaOp r a) := by
  unfold CSD.gaMat CSD.gaOp CSD.actMat
  rw [map_sum]
  simp only [map_smul]

theorem gaMat_mulVec_equivFun (a : MonoidAlgebra K G) (φ : S.Forms) :
    (S.gaMat r a).mulVec (S.basis.equivFun φ) = S.basis.equivFun (S.gaOp r a φ) := by
  rw [gaMat_eq_toMatrix]
  simp only [Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]

end CSD

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)

theorem toF_apply (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y = B.S.basis.equivFun.symm ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y)) := rfl

theorem toF_injective : Function.Injective (B.toF ℓ Z) := by
  have h1 : Function.Injective (B.vE ℓ).mulVec := (subspace_image_spec K _ _).1
  have h2 : Function.Injective (B.zE ℓ Z).mulVec := (subspace_image_spec K _ _).1
  intro a b hab
  rw [toF_apply, toF_apply] at hab
  exact h2 (h1 (B.S.basis.equivFun.symm.injective hab))

theorem mem_coord (W : Submodule K B.S.Forms) (x : Fin B.S.dim → K) :
    x ∈ B.coord W ↔ B.S.basis.equivFun.symm x ∈ W := by
  unfold coord
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨_, hx, B.S.basis.equivFun.apply_symm_apply x⟩

theorem mem_goodPart_iff (W : Submodule K B.S.Forms) (u : Fin (B.nV ℓ) → K) :
    u ∈ B.inV0 ℓ W ↔ B.S.basis.equivFun.symm ((B.vE ℓ).mulVec u) ∈ W := by
  unfold inV0
  rw [Submodule.mem_comap, Matrix.mulVecLin_apply, mem_coord]

theorem part_eq_comap (Sg : Pl0 → K[X]) : B.part ℓ Z Sg = (B.partF Sg).comap (B.toF ℓ Z) := by
  ext y
  simp only [part, Submodule.mem_comap, Matrix.mulVecLin_apply, mem_goodPart_iff, toF_apply]

theorem zE_mem (y : Fin (B.dZ ℓ Z) → K) : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := by
  unfold zE
  rw [subE_mulVec]
  exact Submodule.coe_mem _

theorem exists_zE {u : Fin (B.nV ℓ) → K} (hu : u ∈ B.Z0 ℓ Z) : ∃ y, (B.zE ℓ Z).mulVec y = u := by
  have h := (subspace_image_spec K (B.nV ℓ) (B.Z0 ℓ Z)).2
  rw [← h] at hu
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hu
  exact ⟨y, hy⟩

theorem blockPoly_ne_zero (ν : K) (q t : ℕ) : Col.blockPoly ν q t ≠ 0 := by
  unfold Col.blockPoly
  rw [Finset.prod_ne_zero_iff]
  intro c _ h
  have h0 := congrArg (Polynomial.eval 0) h
  simp at h0

theorem blockProd_ne_zero (P : B.Pl) : B.blockProd P ≠ 0 := by
  unfold blockProd
  refine List.prod_ne_zero ?_
  intro h0
  obtain ⟨ν, _, hν⟩ := List.mem_map.mp h0
  exact blockPoly_ne_zero _ _ _ hν

theorem HasRes.hasBlocks {Sg : Pl0 → K[X]} {x : B.Pl × ℕ → K} (hx : B.HasRes Sg x) :
    Col.HasBlocks B.n B.q B.t B.bl x := by
  intro P
  rw [hx P]
  exact dvd_mul_left _ _

theorem HasRes.excl {Sg Sg' : Pl0 → K[X]} (hne : ∃ P : B.Pl, Sg (B.pl P) ≠ Sg' (B.pl P))
    (x : B.Pl × ℕ → K) (hx : B.HasRes Sg x) : ¬ B.HasRes Sg' x := by
  obtain ⟨P, hP⟩ := hne
  intro hx'
  apply hP
  have h1 := hx P
  have h2 := hx' P
  exact mul_right_cancel₀ (B.blockProd_ne_zero P) (h1.symm.trans h2)

theorem exists_of_partF_ne_bot {Sg : Pl0 → K[X]} (h : B.partF Sg ≠ ⊥) :
    ∃ x, B.HasRes Sg x ∧ Col.Occurs B.op x := by
  by_contra hne
  push_neg at hne
  apply h
  unfold partF Col.eigSum
  refine le_antisymm (iSup₂_le fun x hx => ?_) bot_le
  have h0 := hne x hx
  simp only [Col.Occurs, ne_eq, not_not] at h0
  exact h0.le

theorem good_part_coordinates_bot : B.inV0 ℓ ⊥ = ⊥ := by
  have h1 : Function.Injective (B.vE ℓ).mulVec := (subspace_image_spec K _ _).1
  ext u
  rw [mem_goodPart_iff, Submodule.mem_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h
    exact h1 (h.trans (Matrix.mulVec_zero _).symm)
  · rintro rfl
    exact Matrix.mulVec_zero _

theorem resSet_finite (hc : Col.PairComm B.op) (X : Finset (G → K)) : (B.resSet X).Finite := by
  classical
  obtain ⟨F, hF⟩ := Col.exists_finset_occurs hc
  have hex : ∀ Sg ∈ B.resSet X, ∃ x, B.HasRes Sg x ∧ Col.Occurs B.op x := by
    intro Sg hSg
    refine B.exists_of_partF_ne_bot fun h0 => hSg.2 ?_
    rw [h0, good_part_coordinates_bot]
  let f : (Pl0 → K[X]) → (B.Pl × ℕ → K) := fun Sg =>
    if h : Sg ∈ B.resSet X then (hex Sg h).choose else 0
  have hf : ∀ Sg (h : Sg ∈ B.resSet X), B.HasRes Sg (f Sg) ∧ Col.Occurs B.op (f Sg) := by
    intro Sg h
    simp only [f, dif_pos h]
    exact (hex Sg h).choose_spec
  refine Set.Finite.of_injOn (f := f) (t := (F : Set (B.Pl × ℕ → K))) ?_ ?_ F.finite_toSet
  · intro Sg h
    exact Finset.mem_coe.2 ((hF _).1 (hf Sg h).2)
  · intro Sg h Sg' h' e
    funext P0
    by_cases hP : P0 ∈ Set.range B.pl
    · obtain ⟨P, rfl⟩ := hP
      have h1 := (hf Sg h).1 P
      have h2 := (hf Sg' h').1 P
      rw [e] at h1
      exact mul_right_cancel₀ (B.blockProd_ne_zero P) (h1.symm.trans h2)
    · rw [h.1 P0 hP, h'.1 P0 hP]

theorem mem_ixFin (hc : Col.PairComm B.op) (X : Finset (G → K)) (Sg : Pl0 → K[X]) :
    Sg ∈ B.ixFin X ↔ Sg ∈ B.resSet X := by
  unfold ixFin
  rw [dif_pos (B.resSet_finite hc X)]
  exact Set.Finite.mem_toFinset _

theorem part_indep (hc : Col.PairComm B.op) {ι : Type} (Sg : ι → Pl0 → K[X])
    (hsep : ∀ i j, i ≠ j → ∃ P : B.Pl, Sg i (B.pl P) ≠ Sg j (B.pl P)) :
    iSupIndep fun i => B.part ℓ Z (Sg i) := by
  simp only [part_eq_comap]
  exact iSupIndep_comap (B.toF ℓ Z) (B.toF_injective ℓ Z)
    (iSupIndep_eigSum hc (fun i => B.HasRes (Sg i)) fun i j hij x hx => HasRes.excl B (hsep i j hij) x hx)

theorem part_top {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (hZ : ∀ i, Z ≤ Z.comap (B.op i)) {ι : Type} [Fintype ι]
    (Sg : ι → Pl0 → K[X]) (hsep : ∀ i j, i ≠ j → ∃ P : B.Pl, Sg i (B.pl P) ≠ Sg j (B.pl P))
    (hsame : B.Z0 ℓ Z ≤ B.inV0 ℓ (Col.eigSum B.op fun x => ∃ i, B.HasRes (Sg i) x)) :
    (⨆ i, B.part ℓ Z (Sg i)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  set a := goodAt ℓ.X ℓ.P ℓ.ψ with ha
  have hidem : a * a = a := (good_at_spec K v0 hv0 G ℓ.X hX ℓ.P ℓ.ψ).idem
  have hmul := (group_action_matrix_hom K B.S G B.r).2
  have hrange : LinearMap.range (B.vE ℓ).mulVecLin = LinearMap.range (B.S.gaMat B.r a).mulVecLin :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r a)).2
  set φ := B.toF ℓ Z y with hφ
  have hex : ∀ i j, i ≠ j → ∀ x, B.HasRes (Sg i) x → ¬ B.HasRes (Sg j) x :=
    fun i j hij x hx => HasRes.excl B (hsep i j hij) x hx
  have h1 : φ ∈ Col.eigSum B.op fun x => ∃ i, B.HasRes (Sg i) x :=
    (B.mem_goodPart_iff ℓ _ _).1 (hsame (B.zE_mem ℓ Z y))

  have hAφ : B.S.gaOp B.r a φ = φ := by
    apply B.S.basis.equivFun.injective
    rw [← CSD.gaMat_mulVec_equivFun, hφ, toF_apply, LinearEquiv.apply_symm_apply]
    obtain ⟨z, hz⟩ : (B.vE ℓ).mulVecLin ((B.zE ℓ Z).mulVec y) ∈
        LinearMap.range (B.S.gaMat B.r a).mulVecLin := by rw [← hrange]; exact ⟨_, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hz
    rw [← hz, Matrix.mulVec_mulVec, ← hmul, hidem]
  have hcomm : ∀ k, Commute (B.op k) (B.S.gaOp B.r a) := by
    intro k
    unfold CSD.gaOp
    exact Commute.sum_right _ _ _ fun t _ => (h.opG k t).smul_right _
  have key : ∀ i, ∃ yi, B.toF ℓ Z yi = Col.eigProj h.comm h.split (B.HasRes (Sg i)) φ := by
    intro i
    set ψ := Col.eigProj h.comm h.split (B.HasRes (Sg i)) φ with hψ
    have hψA : B.S.gaOp B.r a ψ = ψ := by
      have := (Col.commute_eigProj h.comm h.split (B.HasRes (Sg i)) hcomm).eq
      have h2 := congrArg (fun f : Module.End K B.S.Forms => f φ) this
      simp only [Module.End.mul_apply] at h2
      rw [hψ, ← h2, hAφ]
    obtain ⟨u, hu⟩ : B.S.basis.equivFun ψ ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
      rw [hrange]
      exact ⟨B.S.basis.equivFun ψ, by
        rw [Matrix.mulVecLin_apply, CSD.gaMat_mulVec_equivFun, hψA]⟩
    rw [Matrix.mulVecLin_apply] at hu
    have hu0 : u ∈ B.Z0 ℓ Z := by
      rw [Z0, mem_goodPart_iff, hu, LinearEquiv.symm_apply_apply]
      exact eigProj_mem_of_stable h.comm h.split _ hZ ((B.mem_goodPart_iff ℓ _ _).1 (B.zE_mem ℓ Z y))
    obtain ⟨yi, hyi⟩ := B.exists_zE ℓ Z hu0
    exact ⟨yi, by rw [toF_apply, hyi, hu, LinearEquiv.symm_apply_apply]⟩
  choose yy hyy using key
  have hsum : y = ∑ i, yy i := by
    apply B.toF_injective ℓ Z
    rw [map_sum, Finset.sum_congr rfl fun i _ => hyy i]
    exact (sum_eigProj h.comm h.split _ hex h1).symm
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ?_
  rw [part_eq_comap, Submodule.mem_comap, hyy i]
  exact Col.eigProj_apply_mem h.comm h.split _ φ

theorem gaOp_mul (a b : MonoidAlgebra K G) (φ : B.S.Forms) :
    B.S.gaOp B.r (a * b) φ = B.S.gaOp B.r a (B.S.gaOp B.r b φ) := by
  have h := (group_action_matrix_hom K B.S G B.r).2 a b
  rw [CSD.gaMat_eq_toMatrix, CSD.gaMat_eq_toMatrix, CSD.gaMat_eq_toMatrix, ← LinearMap.toMatrix_mul] at h
  have h2 := (LinearMap.toMatrix B.S.basis B.S.basis).injective h
  rw [h2]
  rfl

theorem gaOp_fix (hidem : goodAt ℓ.X ℓ.P ℓ.ψ * goodAt ℓ.X ℓ.P ℓ.ψ = goodAt ℓ.X ℓ.P ℓ.ψ)
    (u : Fin (B.nV ℓ) → K) :
    B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) (B.S.basis.equivFun.symm ((B.vE ℓ).mulVec u)) =
      B.S.basis.equivFun.symm ((B.vE ℓ).mulVec u) := by
  have hr := (subspace_image_spec K _ (LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin)).2
  have hmem : (B.vE ℓ).mulVec u ∈ LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin := by
    rw [← hr]
    exact LinearMap.mem_range_self _ u
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
  apply B.S.basis.equivFun.injective
  rw [← CSD.gaMat_mulVec_equivFun, LinearEquiv.apply_symm_apply, ← hw, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec, ← (group_action_matrix_hom K B.S G B.r).2, hidem]

theorem exists_vE_of_fix {φ : B.S.Forms} (h : B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) φ = φ) :
    ∃ u, B.S.basis.equivFun.symm ((B.vE ℓ).mulVec u) = φ := by
  have hr := (subspace_image_spec K _ (LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin)).2
  have hmem : B.S.basis.equivFun φ ∈ LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin := by
    rw [← h, ← CSD.gaMat_mulVec_equivFun]
    exact LinearMap.mem_range_self _ _
  rw [← hr] at hmem
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hmem
  refine ⟨u, ?_⟩
  rw [show (B.vE ℓ).mulVec u = B.S.basis.equivFun φ from hu]
  exact B.S.basis.equivFun.symm_apply_apply φ

theorem sameTypes_self {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) :
    B.invariantGoodPart ℓ ≤ B.inV0 ℓ (Col.eigSum B.op fun x => ∃ Sg ∈ B.ixFin ℓ.X, B.HasRes Sg x) := by
  classical
  intro u hu
  rw [mem_goodPart_iff]
  set φ := B.S.basis.equivFun.symm ((B.vE ℓ).mulVec u) with hφ
  have hφZ : φ ∈ B.ZH := (B.mem_goodPart_iff ℓ _ _).1 hu
  set a := goodAt ℓ.X ℓ.P ℓ.ψ with ha
  set a0 := goodAt ℓ.X (⊥ : Subgroup G) 1 with ha0
  have hidem : a * a = a := (good_at_spec K v0 hv0 G ℓ.X hX ℓ.P ℓ.ψ).idem
  have ha0a : a0 * a = a := by
    rw [ha0, ha, goodAt, goodAt, level_idempotent_bot K G 1, mul_one, ← mul_assoc, idemOf_mul_self ℓ.X hX]
  have hAφ : B.S.gaOp B.r a φ = φ := B.gaOp_fix ℓ hidem u
  have hA0φ : B.S.gaOp B.r a0 φ = φ := by
    conv_lhs => rw [← hAφ]
    rw [← gaOp_mul, ha0a, hAφ]
  have hcomm : ∀ k, Commute (B.op k) (B.S.gaOp B.r a0) := by
    intro k
    unfold CSD.gaOp
    exact Commute.sum_right _ _ _ fun t _ => (h.opG k t).smul_right _
  obtain ⟨F, hF⟩ := Col.exists_finset_occurs h.comm
  let HB : (B.Pl × ℕ → K) → Prop := Col.HasBlocks B.n B.q B.t B.bl
  let ι := {x // x ∈ F.filter HB}
  let C : ι → (B.Pl × ℕ → K) → Prop := fun i x => x = i.1
  have hex : ∀ i j : ι, i ≠ j → ∀ x, C i x → ¬ C j x :=
    fun i j hij x hx hx' => hij (Subtype.ext (hx.symm.trans hx'))
  have h1 : φ ∈ Col.eigSum B.op fun x => ∃ i, C i x := by
    have e : Col.eigSum B.op HB = Col.eigSum B.op fun x => ∃ i, C i x :=
      Col.eigSum_congr fun x hx => ⟨fun hb => ⟨⟨x, Finset.mem_filter.2 ⟨(hF x).1 hx, hb⟩⟩, rfl⟩,
        fun ⟨i, hi⟩ => hi ▸ (Finset.mem_filter.1 i.2).2⟩
    rw [← e]; exact hφZ
  rw [← sum_eigProj h.comm h.split C hex h1]
  refine Submodule.sum_mem _ fun i _ => ?_
  set ψ' := Col.eigProj h.comm h.split (C i) φ with hψ'
  by_cases h0 : ψ' = 0
  · rw [h0]; exact Submodule.zero_mem _
  have hmem : ψ' ∈ Col.eigAt B.op i.1 := by
    have h2 : Col.eigSum B.op (C i) ≤ Col.eigAt B.op i.1 := iSup₂_le fun x hx => by rw [hx]
    exact h2 (Col.eigProj_apply_mem h.comm h.split _ φ)
  have hψA : B.S.gaOp B.r a0 ψ' = ψ' := by
    have h2 := congrArg (fun f : Module.End K B.S.Forms => f φ)
      (Col.commute_eigProj h.comm h.split (C i) hcomm).eq
    simp only [Module.End.mul_apply] at h2
    rw [hψ', ← h2, hA0φ]
  have hb : HB i.1 := (Finset.mem_filter.1 i.2).2
  choose c hc using hb
  let Sg : Pl0 → K[X] := fun P0 => if hP : ∃ P, B.pl P = P0 then c hP.choose else 1
  have hSg : ∀ P, Sg (B.pl P) = c P := by
    intro P
    have hP : ∃ P', B.pl P' = B.pl P := ⟨P, rfl⟩
    simp only [Sg, dif_pos hP]
    rw [h.pl_inj hP.choose_spec]
  have hres : B.HasRes Sg i.1 := by
    intro P
    rw [hSg P, mul_comm]
    exact hc P
  refine Col.eigAt_le_eigSum (C := fun x => ∃ Sg ∈ B.ixFin ℓ.X, B.HasRes Sg x) ⟨Sg, ?_, hres⟩ hmem
  rw [B.mem_ixFin h.comm]
  refine ⟨fun P0 hP0 => ?_, ?_⟩
  · have hP : ¬ ∃ P, B.pl P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
    simp only [Sg, dif_neg hP]
  · obtain ⟨u0, hu0⟩ := B.exists_vE_of_fix (Lvl.full ℓ.X) hψA
    intro hbot
    have hu0mem : u0 ∈ B.inV0 (Lvl.full ℓ.X) (B.partF Sg) := by
      rw [mem_goodPart_iff, hu0]
      exact Col.eigAt_le_eigSum (C := B.HasRes Sg) hres hmem
    rw [hbot, Submodule.mem_bot] at hu0mem
    apply h0
    rw [← hu0, hu0mem, Matrix.mulVec_zero, map_zero]

end BlockDat

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)

theorem good_part_coordinates_mono {W W' : Submodule K B.S.Forms} (hW : W ≤ W') : B.inV0 ℓ W ≤ B.inV0 ℓ W' := by
  unfold inV0 coord
  exact Submodule.comap_mono (Submodule.map_mono hW)

theorem equivFun_op (i : B.Pl × ℕ) (f : B.S.Forms) :
    B.S.basis.equivFun (B.op i f) = (B.opMat i).mulVec (B.S.basis.equivFun f) := by
  unfold opMat
  simp only [Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]

theorem equivFun_act (g : G) (f : B.S.Forms) :
    B.S.basis.equivFun (B.r g f) = (B.S.actMat B.r g).mulVec (B.S.basis.equivFun f) := by
  unfold CSD.actMat
  simp only [Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]

theorem gaMat_single (g : G) : B.S.gaMat B.r (MonoidAlgebra.single g 1) = B.S.actMat B.r g := by
  unfold CSD.gaMat
  rw [Finset.sum_eq_single g]
  · simp
  · intro b _ hb
    simp [hb, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ g) h

theorem mem_goodF {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {X : Finset (G → K)} (hX : ∀ χ ∈ X, IsAbsIrrChar χ)
    (φ : B.S.Forms) : φ ∈ B.goodF X ↔ B.S.gaOp B.r (goodAt X (⊥ : Subgroup G) 1) φ = φ := by
  have hidem := (good_at_spec K v0 hv0 G X hX (⊥ : Subgroup G) 1).idem
  constructor
  · rintro ⟨ψ, rfl⟩
    rw [← gaOp_mul, hidem]
  · intro h
    exact ⟨φ, h⟩

theorem good_part_coordinates_good_eq_top {v0 : InfinitePlace K} (hv0 : IsConjAt v0) (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) :
    B.inV0 ℓ (B.goodF ℓ.X) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  rw [mem_goodPart_iff, B.mem_goodF hv0 hX]
  have hidem : goodAt ℓ.X ℓ.P ℓ.ψ * goodAt ℓ.X ℓ.P ℓ.ψ = goodAt ℓ.X ℓ.P ℓ.ψ :=
    (good_at_spec K v0 hv0 G ℓ.X hX ℓ.P ℓ.ψ).idem
  have ha0a : goodAt ℓ.X (⊥ : Subgroup G) 1 * goodAt ℓ.X ℓ.P ℓ.ψ = goodAt ℓ.X ℓ.P ℓ.ψ := by
    rw [goodAt, goodAt, level_idempotent_bot K G 1, mul_one, ← mul_assoc, idemOf_mul_self ℓ.X hX]
  have hAφ := B.gaOp_fix ℓ hidem u
  conv_lhs => rw [← hAφ]
  rw [← gaOp_mul, ha0a, hAφ]

theorem goodF_stable {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) {X : Finset (G → K)}
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) : B.ZStable (B.goodF X) := by
  set a := goodAt X (⊥ : Subgroup G) 1 with ha
  have hcomm : ∀ k, Commute (B.op k) (B.S.gaOp B.r a) := by
    intro k
    unfold CSD.gaOp
    exact Commute.sum_right _ _ _ fun t _ => (h.opG k t).smul_right _
  refine ⟨fun i φ hφ => ?_, fun g φ hφ => ?_⟩
  · rw [Submodule.mem_comap, B.mem_goodF hv0 hX] at *
    have := congrArg (fun f : Module.End K B.S.Forms => f φ) (hcomm i).eq
    simp only [Module.End.mul_apply] at this
    rw [← this, hφ]
  · rw [Submodule.mem_comap, B.mem_goodF hv0 hX] at *
    have hc : MonoidAlgebra.single g (1 : K) * a = a * MonoidAlgebra.single g 1 := by
      rw [ha, goodAt, level_idempotent_bot K G 1]
      simp only [mul_one]
      exact idemOf_central X hX _
    apply B.S.basis.equivFun.injective
    rw [← CSD.gaMat_mulVec_equivFun, equivFun_act, Matrix.mulVec_mulVec, ← gaMat_single,
      ← (group_action_matrix_hom K B.S G B.r).2, ← hc, (group_action_matrix_hom K B.S G B.r).2, gaMat_single,
      ← Matrix.mulVec_mulVec, CSD.gaMat_mulVec_equivFun, hφ]

theorem sep_of_mem_ixFin {X : Finset (G → K)} {Sg Sg' : Pl0 → K[X]} (h : Sg ∈ B.ixFin X)
    (h' : Sg' ∈ B.ixFin X) (hne : Sg ≠ Sg') : ∃ P : B.Pl, Sg (B.pl P) ≠ Sg' (B.pl P) := by
  unfold ixFin at h h'
  split_ifs at h h' with hf
  · rw [Set.Finite.mem_toFinset] at h h'
    simp only [resSet, Set.mem_setOf_eq] at h h'
    by_contra hall
    push_neg at hall
    apply hne
    funext P0
    by_cases hP : P0 ∈ Set.range B.pl
    · obtain ⟨P, rfl⟩ := hP
      exact hall P
    · rw [h.1 P0 hP, h'.1 P0 hP]
  · simp at h

end BlockDat

namespace DefFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J)

theorem isType_iff (B : BlockDat K G Pl0) (f : (Pl0 → K[X]) → Pl0 → K[X]) (x : B.Pl × ℕ → K) :
    F.IsType B f x ↔ ∃ p : ↥((F.R F.μ0).ixFin F.X), B.HasRes (f p.1) x := by
  unfold IsType
  exact ⟨fun ⟨Sg, hS, h⟩ => ⟨⟨Sg, hS⟩, h⟩, fun ⟨p, h⟩ => ⟨p.1, p.2, h⟩⟩

variable {F}

theorem stable_rows {Zs : DefSub F.amb} (hst : Zs.Stable) (t : T) (i : (F.R t).Pl × ℕ) :
    Zs.Z t ≤ (Zs.Z t).comap ((F.R t).op i) := Submodule.map_le_iff_le_comap.mp (hst.1 t (Sum.inl i))

theorem stable_lifts {Zs : DefSub F.amb} (hst : Zs.Stable) (j : J) (t : T) (i : (F.L j t).Pl × ℕ) :
    Zs.Zl j t ≤ (Zs.Zl j t).comap ((F.L j t).op i) := Submodule.map_le_iff_le_comap.mp (hst.2 j t (Sum.inl i))

theorem inBlock_rows {Zs : DefSub F.amb} (hin : Zs.InBlock) (t : T) : Zs.Z t ≤ (F.R t).ZH := by
  exact (hin.1 t).trans inf_le_left

theorem inBlock_lifts {Zs : DefSub F.amb} (hin : Zs.InBlock) (j : J) (t : T) : Zs.Zl j t ≤ (F.L j t).ZH := by
  exact (hin.2 j t).trans inf_le_left

variable (F)

theorem sameTypes_base {s : ℕ} (h : F.Ok s) (P : Subgroup G) (ψ : P →* Kˣ) {Zs : DefSub F.amb}
    (hin : Zs.InBlock) :
    (F.R F.μ0).Z0 (F.lvl P ψ) (Zs.Z F.μ0) ≤
      (F.R F.μ0).inV0 (F.lvl P ψ) (Col.eigSum (F.R F.μ0).op (F.IsType (F.R F.μ0) id)) :=
  ((F.R F.μ0).good_part_coordinates_mono _ (inBlock_rows hin F.μ0)).trans
    ((F.R F.μ0).sameTypes_self (F.lvl P ψ) h.conj (h.what₂ F.μ0) h.irr)

theorem side_WF {s : ℕ} (h : F.Ok s) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb) (hst : Zs.Stable)
    (hin : Zs.InBlock) (hsep : F.TypesSep) : (F.side P ψ Zs).WF where
  cm := isCMSub_cmMax' K
  conj := h.conj
  HV_rat t := BlockDat.HV_rat (ℓ := F.lvl P ψ) h.conj (h.what₂ t) h.irr
  HV_pos t := BlockDat.HV_pos (ℓ := F.lvl P ψ) h.conj (h.what₂ t) h.irr
  Mt_lat t := BlockDat.Mt_lat (ℓ := F.lvl P ψ) h.conj (h.what₂ t) h.irr
  Pq_surj t := BlockDat.Pq_surj (ℓ := F.lvl P ψ) (Z := Zs.Z t) h.conj (h.what₂ t) h.irr
  XQ_quot t := BlockDat.XQ_quot (ℓ := F.lvl P ψ) (Z := Zs.Z t) h.conj (h.what₂ t) h.irr
  Lam_lat t := BlockDat.Lam_lat (ℓ := F.lvl P ψ) (Z := Zs.Z t) h.conj (h.what₂ t) h.irr
  Qp_indep := (F.R F.μ0).part_indep (F.lvl P ψ) (Zs.Z F.μ0) (h.what₂ F.μ0).comm (fun p : F.base.Ix => p.1)
    fun p p' hpp => (F.R F.μ0).sep_of_mem_ixFin p.2 p'.2 fun e => hpp (Subtype.ext e)
  Qp_top := (F.R F.μ0).part_top (F.lvl P ψ) (Zs.Z F.μ0) h.conj (h.what₂ F.μ0) h.irr (stable_rows hst F.μ0)
    (fun p : F.base.Ix => p.1) (fun p p' hpp => (F.R F.μ0).sep_of_mem_ixFin p.2 p'.2 fun e => hpp (Subtype.ext e))
    ((F.sameTypes_base h P ψ hin).trans ((F.R F.μ0).good_part_coordinates_mono _
      (Col.eigSum_mono fun x hx => (F.isType_iff _ id x).1 hx)))
  XT_herm j t := BlockDat.XQ_herm (ℓ := F.lvlA P ψ) (Z := Zs.Zl j t) h.conj (h.lifts j t) h.irr
  Tl_lat j t := BlockDat.Tl_lat (ℓ := F.lvlA P ψ) (Z := Zs.Zl j t) h.conj (h.lifts j t) h.irr
  Zp_indep j := (F.L j F.μ0).part_indep (F.lvlA P ψ) (Zs.Zl j F.μ0) (h.lifts j F.μ0).comm
    (fun p : F.base.Ix => F.tr j p.1) fun p p' hpp => hsep p.1 p.2 p'.1 p'.2 (fun e => hpp (Subtype.ext e)) j

theorem side_Pos (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb) (hrow : F.RowsExist P ψ Zs) :
    (F.side P ψ Zs).Pos := hrow

theorem side_Proviso {s : ℕ} (h : F.Ok s) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)
    (hrat : F.LiftRat P ψ Zs) : (F.side P ψ Zs).Proviso := by
  unfold DefSide.Proviso
  intro j
  exact BlockDat.XQ_rat (B := F.L j F.μ0) (ℓ := F.lvlA P ψ) (Z := Zs.Zl j F.μ0) h.conj (h.lifts j F.μ0) h.irr (hrat j)

theorem side_Types {s : ℕ} (h : F.Ok s) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb) (hst : Zs.Stable)
    (hsep : F.TypesSep) (hsame : F.SameTypes P ψ Zs) : (F.side P ψ Zs).Types :=
  fun j => (F.L j F.μ0).part_top (F.lvlA P ψ) (Zs.Zl j F.μ0) h.conj (h.lifts j F.μ0) h.irr
    (stable_lifts hst j F.μ0) (fun p : F.base.Ix => F.tr j p.1)
    (fun p p' hpp => hsep p.1 p.2 p'.1 p'.2 (fun e => hpp (Subtype.ext e)) j)
    ((hsame j).trans ((F.L j F.μ0).good_part_coordinates_mono _
      (Col.eigSum_mono fun x hx => (F.isType_iff _ (F.tr j) x).1 hx)))

end DefFam

section Side

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

theorem locBasisOf_spec {D : ℕ} (L : Submodule (𝓞 K) (Fin D → K)) (hL : Submodule.IsLattice K L)
    (w : HeightOneSpectrum (𝓞 K)) : IsLocBasis L w (locBasisOf L w) := by
  have hex := semilocal_basis_exists K D L hL w
  unfold locBasisOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem ebOf_spec (hW : Df.WF) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) :
    IsLocBasis (Df.abelian₂ t) w (ebOf Df t w) := locBasisOf_spec _ (hW.Lam_lat t) w

theorem RR_spec (hW : Df.WF) (S : IndefData Df) (hH0 : S.H0) (hι : ∀ t, Function.Surjective (S.ι t).mulVec) :
    Submodule.IsLattice K S.RR ∧ ∀ w : HeightOneSpectrum (𝓞 K),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal S.RR =
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))) := by
  refine lattice_gluing K S.D (matLat (S.ι Bs.μ0) (Df.abelian₂ Bs.μ0))
    (fun w => matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w)))
    (GluingInclusion.matLat_lattice' _ (hι _) _ (hW.Lam_lat _))
    (fun w => GluingInclusion.matLat_lattice' _ (hι _) _ (hW.Lam_lat _)) ?_
  refine S.Tw.finite_toSet.subset fun w hw => ?_
  rw [Finset.mem_coe, hH0.2 w]
  intro e
  apply hw
  show Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))) = _
  rw [e]

theorem sum_partPr (t : Bs.Tup) (hi : iSupIndep (Df.Qp t)) (ht : (⨆ p, Df.Qp t p) = ⊤) :
    ∑ p, partPr Df t p = 1 := by
  classical
  have hc : ∀ p, IsCompl (Df.Qp t p) (⨆ (p' : Bs.Ix) (_ : p' ≠ p), Df.Qp t p') := by
    intro p
    refine ⟨hi p, ?_⟩
    rw [codisjoint_iff, ← iSup_split_single (Df.Qp t) p, ht]
  have hp : ∀ p, partPr Df t p =
      LinearMap.toMatrix' ((Df.Qp t p).subtype ∘ₗ Submodule.projectionOnto _ _ (hc p)) := by
    intro p
    unfold partPr
    rw [dif_pos (hc p)]
  simp_rw [hp, ← map_sum]
  rw [← LinearMap.toMatrix'_id]
  congr 1
  apply LinearMap.ext
  intro x
  have hx : x ∈ ⨆ p, Df.Qp t p := by rw [ht]; exact Submodule.mem_top
  induction hx using Submodule.iSup_induction' with
  | mem q y hy =>
    rw [LinearMap.sum_apply, Finset.sum_eq_single q, LinearMap.id_apply]
    · simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [Submodule.projectionOnto_apply_left (hc q) ⟨y, hy⟩]
    · intro p _ hpq
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [(Submodule.projectionOnto_apply_eq_zero_iff (hc p)).2
        (Submodule.mem_iSup_of_mem q (Submodule.mem_iSup_of_mem (Ne.symm hpq) hy))]
      rfl
    · intro hq
      exact absurd (Finset.mem_univ q) hq
  | zero => simp
  | add a b _ _ iha ihb => rw [map_add, iha, ihb, map_add]

theorem rowXE_spec (hW : Df.WF) (Y : Matrix (Fin (Df.dQ Bs.μ0)) (Fin (Df.dQ Bs.μ0)) ℂ) (hY : IsUnit Y.det)
    (κ : InfinitePlace K → ℝ) (hκ : ∀ v, 0 < κ v) (lam : Bs.J → Bs.Ix → InfinitePlace K → ℝ)
    (hlam : ∀ j p v, 0 < lam j p v) :
    (∀ v, IsUnit (rowXE Df Y κ lam v).det) ∧ rowXE Df Y κ lam Bs.v0 = Y ∧
    ∀ v, v ≠ Bs.v0 → ∀ x y : Fin (Df.dQ Bs.μ0) → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (rowXE Df Y κ lam) v x y =
        ∑ p, ((κ v * ∏ j, lam j p v : ℝ) : ℂ) *
          Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Df.XQ Bs.μ0) v
            ((partPr Df Bs.μ0 p).mulVec x) ((partPr Df Bs.μ0 p).mulVec y) := by
  have hsum : ∑ p, partPr Df Bs.μ0 p = 1 := sum_partPr Bs.μ0 hW.Qp_indep hW.Qp_top
  have hX : ∀ v, IsUnit (Df.XQ Bs.μ0 v).det := fun v => (hW.XQ_quot Bs.μ0 v).1
  have ht : ∀ (p : Bs.Ix) (v : InfinitePlace K), 0 < κ v * ∏ j, lam j p v :=
    fun p v => mul_pos (hκ v) (Finset.prod_pos fun j _ => hlam j p v)
  have hwf := weightFrameSpec K _ Bs.Ix (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam j p v)
    (Df.XQ Bs.μ0) hX ht hsum
  have hS := spliceFrameSpec K _ Bs.v0 Y
    (pushFrame 1 (weightFrame (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam j p v) (Df.XQ Bs.μ0)))
  have hpush : ∀ v, pushFrame (1 : Matrix (Fin (Df.dQ Bs.μ0)) (Fin (Df.dQ Bs.μ0)) K)
      (weightFrame (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam j p v) (Df.XQ Bs.μ0)) v =
      weightFrame (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam j p v) (Df.XQ Bs.μ0) v := by
    intro v
    rw [pushFrame, map_one', Matrix.one_mul]
  refine ⟨fun v => ?_, hS.1, fun v hv x y => ?_⟩
  · by_cases hv : v = Bs.v0
    · subst hv
      rw [rowXE, rowFrame, hS.1]; exact hY
    · rw [rowXE, rowFrame, hS.2 v hv, hpush]
      exact (hwf v).1
  · rw [majAt_congr_frame (rowXE Df Y κ lam) _ v ((hS.2 v hv).trans (hpush v))]
    exact (hwf v).2.2 x y

end Side

namespace DefFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J)

theorem GmOf_le [IsTotallyComplex K] {s : ℕ} (h : F.Ok s) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)
    (t : T) (w : HeightOneSpectrum (𝓞 K)) :
    vw w (GmOf (F.side P ψ Zs) t w) ≤
      (((F.side P ψ Zs).dQ t : ℕ) : ℤ) * vw w ((Fintype.card G * s : ℕ) : K) := by
  have hl : 0 < Fintype.card G * s := Nat.mul_pos Fintype.card_pos (h.what₂ t).good.s_pos
  have hlat := BlockDat.Lam_lat (ℓ := F.lvl P ψ) (Z := Zs.Z t) h.conj (h.what₂ t) h.irr
  have := reduction_lemma_first K (cmMax K) (isCMSub_cmMax' K) F.v0 h.conj _ _ ((F.R t).HV (F.lvl P ψ))
    (BlockDat.HV_rat (ℓ := F.lvl P ψ) h.conj (h.what₂ t) h.irr)
    (BlockDat.HV_pos (ℓ := F.lvl P ψ) h.conj (h.what₂ t) h.irr) ((F.R t).Pq (F.lvl P ψ) (Zs.Z t))
    (BlockDat.Pq_surj (ℓ := F.lvl P ψ) h.conj (h.what₂ t) h.irr) ((F.R t).Mt (F.lvl P ψ))
    (BlockDat.Mt_lat (ℓ := F.lvl P ψ) h.conj (h.what₂ t) h.irr) (Fintype.card G * s) 1 hl
    (by
      intro x hx
      rw [pow_one]
      exact BlockDat.Mt_dual (ℓ := F.lvl P ψ) h.conj (h.what₂ t) h.irr x hx)
    w (ebOf (F.side P ψ Zs) t w) (locBasisOf_spec _ hlat w)
  rw [Nat.cast_one, one_mul] at this
  exact this

end DefFam

end Formalism.L2.DIV

namespace Formalism.L2.DIV.Test

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Col Formalism.L2.NCov

theorem mem_cmMax_rat (a : ℚ) : a ∈ cmMax ℚ := by
  show ∀ σ : ℚ →+* ℂ, σ (star a) = starRingEnd ℂ (σ a)
  intro σ
  first
    | rw [star_trivial, eq_ratCast σ a, map_ratCast]
    | simp [eq_ratCast σ a]

abbrev G3 := Equiv.Perm (Fin 3)

def x0 : Unit × ℕ → ℚ := fun p => if p.2 = 0 then 1 else if p.2 = 1 then 5 else 0

def tB : BlockDat ℚ G3 Unit where
  S := regCSD ℚ G3
  r := regAct ℚ G3
  Pl := Unit
  pl := id
  q := fun _ => 2
  n := 1
  t := 1
  op := fun p => x0 p • 1
  bl := [fun _ => 5]

abbrev tX : Finset (G3 → ℚ) := {fun _ => 1}

def tF : DefFam ℚ G3 Unit Unit Unit where
  v0 := Classical.arbitrary _
  μ0 := ()
  X := tX
  R := fun _ => tB
  L := fun _ _ => tB
  tr := fun _ => id

theorem tB_eigAt : eigAt tB.op x0 = ⊤ := by
  unfold eigAt
  rw [iInf_eq_top]
  intro i
  exact maxGen_smul_one (x0 i)

theorem tB_hasRes : tB.HasRes (fun _ => 1) x0 := by
  intro P
  simp only [heckePoly, heckePolyOf, BlockDat.blockProd, blockPoly, tB, x0, Finset.sum_range_succ,
    Finset.sum_range_zero, Finset.prod_range_succ, Finset.prod_range_zero, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  simp
  ring

theorem tB_partF : tB.partF (fun _ => 1) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← tB_eigAt]
  exact eigAt_le_eigSum tB_hasRes

theorem tB_ZH : tB.ZH = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← tB_eigAt]
  exact eigAt_le_eigSum (BlockDat.HasRes.hasBlocks tB tB_hasRes)

theorem example_good_coordinates_top (ℓ : Lvl ℚ G3) : tB.inV0 ℓ ⊤ = ⊤ := by
  refine eq_top_iff.mpr fun u _ => ?_
  rw [BlockDat.mem_goodPart_iff]
  exact Submodule.mem_top

theorem tB_res_eq {Sg : Unit → ℚ[X]} (h : tB.partF Sg ≠ ⊥) : Sg = fun _ => 1 := by
  obtain ⟨x, hx, hocc⟩ := tB.exists_of_partF_ne_bot h
  have hxx : x = x0 := funext fun i =>
    eq_of_occurs_of_le (op := tB.op) hocc ((maxGen_smul_one (V := tB.S.Forms) (x0 i)).symm ▸ le_top)
  subst hxx
  funext P
  exact mul_right_cancel₀ (tB.blockProd_ne_zero P) (((hx P).symm.trans (tB_hasRes P)))

theorem tB_resSet : tB.resSet tX = {fun _ => 1} := by
  ext Sg
  rw [Set.mem_singleton_iff]
  constructor
  · intro h
    refine tB_res_eq fun h0 => h.2 ?_
    rw [h0, BlockDat.good_part_coordinates_bot]
  · rintro rfl
    refine ⟨fun _ _ => rfl, ?_⟩
    show tB.inV0 _ (tB.partF fun _ => 1) ≠ ⊥
    rw [tB_partF, example_good_coordinates_top]
    have hpos : 0 < tB.nV (Lvl.full tX) := reg_V0dim_pos_lvl ℚ G3 ⊥
    have : Nonempty (Fin (tB.nV (Lvl.full tX))) := ⟨⟨0, hpos⟩⟩
    exact top_ne_bot

theorem tB_mem_ixFin (Sg : Unit → ℚ[X]) : Sg ∈ tB.ixFin tX ↔ Sg = fun _ => 1 := by
  have hfin : (tB.resSet tX).Finite := by
    rw [tB_resSet]; exact Set.finite_singleton _
  unfold BlockDat.ixFin
  rw [dif_pos hfin, Set.Finite.mem_toFinset, tB_resSet, Set.mem_singleton_iff]

theorem tB_ok : tB.Ok 1 where
  good := reg_good ℚ G3
  hrat _ _ := mem_cmMax_rat _
  hpos v := reg_H_posDef ℚ G3 v (rat_isConjAt v)
  act := regAct_good ℚ G3
  actRat _ _ _ := mem_cmMax_rat _
  comm i j := by
    apply LinearMap.ext
    intro v
    show x0 i • (x0 j • v) = x0 j • (x0 i • v)
    exact smul_comm _ _ _
  split i := top_unique (le_iSup_of_le (x0 i) (maxGen_smul_one (x0 i)).ge)
  opG i g := by
    apply LinearMap.ext
    intro v
    show x0 i • (tB.r g v) = tB.r g (x0 i • v)
    exact (map_smul _ _ _).symm
  blocks := ⟨le_rfl, List.cons_ne_nil _ _, fun ν hν P => by
    have hν' : ν = fun _ => (5 : ℚ) := List.mem_singleton.1 hν
    subst hν'
    norm_num⟩
  q_pos _ := show 0 < 2 by norm_num
  pl_inj := Function.injective_id

theorem tX_irr : ∀ χ ∈ tX, IsAbsIrrChar χ := by
  intro χ hχ
  rw [show χ = fun _ => (1 : ℚ) from Finset.mem_singleton.1 hχ]
  exact isAbsIrrChar_one ℚ G3

theorem tF_ok : tF.Ok 1 where
  conj := rat_isConjAt _
  tup_fin := inferInstance
  irr := tX_irr
  what₂ _ := tB_ok
  lifts _ _ := tB_ok

def tZs : DefSub tF.amb := ⟨fun _ => tB.goodF tX, fun _ _ => tB.goodF tX⟩

theorem tZs_stable : tZs.Stable := by
  have hs := tB.goodF_stable tF_ok.conj tB_ok tX_irr
  unfold DefSub.Stable
  refine ⟨fun t i => ?_, fun j t i => ?_⟩
  · rcases i with i | g
    · exact Submodule.map_le_iff_le_comap.mpr (hs.1 i)
    · exact Submodule.map_le_iff_le_comap.mpr (hs.2 g)
  · rcases i with i | g
    · exact Submodule.map_le_iff_le_comap.mpr (hs.1 i)
    · exact Submodule.map_le_iff_le_comap.mpr (hs.2 g)

theorem tZs_inBlock : tZs.InBlock := by
  unfold DefSub.InBlock
  refine ⟨fun t => ?_, fun j t => ?_⟩
  · show tB.goodF tX ≤ tB.ZH ⊓ tB.goodF tX
    rw [tB_ZH]
    exact le_inf le_top le_rfl
  · show tB.goodF tX ≤ tB.ZH ⊓ tB.goodF tX
    rw [tB_ZH]
    exact le_inf le_top le_rfl

theorem example_invariant_good_top (P : Subgroup G3) : tB.Z0 (tF.lvl P 1) (tB.goodF tX) = ⊤ := by
  exact tB.good_part_coordinates_good_eq_top (tF.lvl P 1) tF_ok.conj tX_irr

theorem tF_rows (P : Subgroup G3) : tF.RowsExist P 1 tZs := by
  show 0 < subDim (tB.Z0 (tF.lvl P 1) (tB.goodF tX))
  rw [example_invariant_good_top]
  unfold subDim
  rw [finrank_top, finrank_fin_fun]
  exact reg_V0dim_pos_lvl ℚ G3 P

theorem tF_isType (f : (Unit → ℚ[X]) → Unit → ℚ[X]) (hf : f (fun _ => 1) = fun _ => 1) :
    eigSum tB.op (tF.IsType tB f) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← tB_eigAt]
  have hx : tF.IsType tB f x0 := by
    unfold DefFam.IsType
    refine ⟨fun _ => 1, (tB_mem_ixFin _).mpr rfl, ?_⟩
    rw [hf]
    exact tB_hasRes
  exact eigAt_le_eigSum hx

theorem tF_same (P : Subgroup G3) : tF.SameTypes P 1 tZs := by
  intro j
  have h1 := tF_isType (tF.tr j) rfl
  have h2 := example_good_coordinates_top (tF.lvlA P 1)
  show tB.Z0 _ _ ≤ tB.inV0 _ (eigSum tB.op (tF.IsType tB (tF.tr j)))
  rw [h1, h2]
  exact le_top

theorem tF_sep : tF.TypesSep := by
  first
    | (unfold DefFam.TypesSep
       intro Sg hSg Sg' hSg' hne j
       exact absurd (((tB_mem_ixFin Sg).mp hSg).trans ((tB_mem_ixFin Sg').mp hSg').symm) hne)
    | (intro Sg hSg Sg' hSg' hne j
       exfalso
       exact hne (((tB_mem_ixFin Sg).mp hSg).trans ((tB_mem_ixFin Sg').mp hSg').symm))
    | (intro Sg hSg Sg' hSg' hne
       exact absurd (((tB_mem_ixFin Sg).mp hSg).trans ((tB_mem_ixFin Sg').mp hSg').symm) hne)

theorem tF_rat (P : Subgroup G3) : tF.LiftRat P 1 tZs :=
  fun _ => ⟨finBasis ℚ _, fun _ _ => mem_cmMax_rat _⟩

theorem tF_WF (P : Subgroup G3) :
    (tF.side P 1 tZs).WF ∧ (tF.side P 1 tZs).Pos ∧ (tF.side P 1 tZs).Proviso ∧ (tF.side P 1 tZs).Types := by
  exact ⟨tF.side_WF tF_ok P 1 tZs tZs_stable tZs_inBlock tF_sep, tF.side_Pos P 1 tZs (tF_rows P),
    tF.side_Proviso tF_ok P 1 tZs (tF_rat P), tF.side_Types tF_ok P 1 tZs tZs_stable tF_sep (tF_same P)⟩

end Formalism.L2.DIV.Test
