import Mathlib
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.ProvRowSide

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def stdHLat (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)) : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := L

theorem stdHLat_frames (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)) (v : InfinitePlace K) :
    IsUnit ((stdHLat K n L).X v).det := by
  show IsUnit (1 : Matrix (Fin n) (Fin n) ℂ).det
  simp

variable {K}

def coordMap (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} (c : Fin n → W) :
    (Fin n → K) →ₛₗ[e] W where
  toFun x := ∑ i, e (x i) • c i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

set_option linter.unusedSectionVars false in
theorem coordMap_basisFun (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} (c : Fin n → W)
    (i : Fin n) : coordMap e c (Pi.basisFun K (Fin n) i) = c i := by
  simp [coordMap, Pi.single_apply, apply_ite e, ite_smul]

theorem normAt_one (e : K →+* ℂ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ}
    (c : OrthonormalBasis (Fin n) ℂ W) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (fun _ => 1) (InfinitePlace.mk e) x = ‖coordMap e c x‖ := by
  have h1 : coordMap e c x = c.repr.symm (WithLp.toLp 2 (fun i => e (x i))) := by
    rw [← c.sum_repr_symm]; rfl
  rw [h1, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  simp [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

end Std

section WithRRDef

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]

def rrLat (S : RowSide D EE) : Submodule (𝓞 D.what₂.LL) S.RR.V where
  carrier := {x | ∀ w : D.what₂.places.Pl, ∃ d : 𝓞 D.what₂.LL, d ∉ (D.plEq w).asIdeal ∧
    d • x ∈ Submodule.span (𝓞 D.what₂.LL) {y | S.jEE y ∈ S.RRset (D.what₂.muAt w)}}
  zero_mem' := fun w => ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  add_mem' := by
    intro x y hx hy w
    obtain ⟨d, hd, hdx⟩ := hx w
    obtain ⟨d', hd', hdy⟩ := hy w
    refine ⟨d * d', fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hd hd', ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hdx
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hdy
  smul_mem' := by
    intro a x hx w
    obtain ⟨d, hd, hdx⟩ := hx w
    refine ⟨d, hd, ?_⟩
    rw [smul_comm]; exact Submodule.smul_mem _ _ hdx

def withRRDef (S : RowSide D EE) : RowSide D EE :=
  { S with RR := { S.RR with L := rrLat S } }

theorem downTo_withRRDef (S : RowSide D EE) (μ : D.what₂.Tup) :
    ∀ j, (withRRDef S).downTo μ j = S.downTo μ j
  | 0 => rfl
  | j + 1 => by
    show ((withRRDef S).downTo μ j).comp (S.io μ j) = (S.downTo μ j).comp (S.io μ j)
    rw [downTo_withRRDef S μ j]; rfl

theorem iota_withRRDef (S : RowSide D EE) (μ : D.what₂.Tup) : (withRRDef S).iota μ = S.iota μ := by
  unfold RowSide.iota
  rw [downTo_withRRDef]; rfl

theorem RRset_withRRDef (S : RowSide D EE) (μ : D.what₂.Tup) : (withRRDef S).RRset μ = S.RRset μ := by
  have hQ : (withRRDef S).Qsp μ = S.Qsp μ := by
    unfold RowSide.Qsp RowSide.Usp
    rw [iota_withRRDef]; rfl
  have key : ∀ (Q Q' : Submodule ℂ (S.Amb μ)) (i : Q.HasOrthogonalProjection) (i' : Q'.HasOrthogonalProjection),
      Q = Q' → @Submodule.starProjection ℂ _ _ _ _ Q i = @Submodule.starProjection ℂ _ _ _ _ Q' i' := by
    intro Q Q' i i' h; subst h; rfl
  have hL : (withRRDef S).LamSet μ = S.LamSet μ := by
    unfold RowSide.LamSet
    exact congrArg (fun f : S.Amb μ →L[ℂ] S.Amb μ =>
      (fun x => f x) '' ((S.Mtilde μ).carrier ∩ (S.V0 μ : Set (S.Amb μ)))) (key _ _ _ _ hQ)
  unfold RowSide.RRset
  rw [iota_withRRDef, hL]; rfl

theorem rrDef_withRRDef (S : RowSide D EE) : (withRRDef S).RRDef := by
  intro x
  simp only [RRset_withRRDef]
  exact Iff.rfl

end WithRRDef

section Small

variable (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  {n : ℕ} (c : OrthonormalBasis (Fin n) ℂ EE)

def multDim (n j : ℕ) : ℕ := if j = 0 then n else 0

theorem multDim_top (n : ℕ) : multDim n D.R.m = 0 := by
  have := D.R.two_le_m
  unfold multDim; rw [if_neg (by omega)]

def smallSide : RowSide D EE where
  Amb := fun _ => EuclideanSpace ℂ (Fin 0)
  Mult := fun _ j => EuclideanSpace ℂ (Fin (multDim n j))
  multZero := fun _ => c.repr.symm
  multTop := fun _ => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr (multDim_top D n))
  io := fun _ _ => 0
  Mtilde := fun _ => ⟨∅, Subsingleton.elim _ _⟩
  cen := fun _ =>
    { toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ => Subsingleton.elim _ _
      commutes' := fun _ => Subsingleton.elim _ _ }
  eOp := fun _ => 0
  eOp_idem := fun _ => Subsingleton.elim _ _
  eOp_sa := fun _ => LinearMap.IsSymmetric.zero
  eOp_tie := fun _ => Subsingleton.elim _ _
  RR := stdHLat D.what₂.LL n ⊥
  RR_frames := stdHLat_frames _ _ _
  jEE := coordMap D.what₂.embLL c
  jEE_basis := by
    have h : (fun i : Fin n => coordMap D.what₂.embLL c (Pi.basisFun D.what₂.LL (Fin n) i)) = c.toBasis := by
      funext i; rw [coordMap_basisFun]; simp
    refine ⟨?_, ?_⟩
    · show LinearIndependent ℂ (fun i : Fin n => coordMap D.what₂.embLL c (Pi.basisFun D.what₂.LL (Fin n) i))
      rw [h]; exact c.toBasis.linearIndependent
    · show Submodule.span ℂ (Set.range
        (fun i : Fin n => coordMap D.what₂.embLL c (Pi.basisFun D.what₂.LL (Fin n) i))) = ⊤
      rw [h]; exact c.toBasis.span_eq
  jEE_norm := fun x => normAt_one D.what₂.embLL c x

def smallAmbForm : AmbForm D (withRRDef (smallSide D c)) where
  MtH := fun _ => stdHLat D.what₂.LL 0 ⊤
  jAmb := fun _ => (0 : (Fin 0 → D.what₂.LL) →ₛₗ[D.what₂.embLL] EuclideanSpace ℂ (Fin 0))
  MtH_good := fun _ _ => ⟨stdHLat_frames _ _ _,
    by
      show (⊤ : Submodule (𝓞 D.what₂.LL) (Fin 0 → D.what₂.LL)).FG
      rw [Subsingleton.elim (⊤ : Submodule (𝓞 D.what₂.LL) (Fin 0 → D.what₂.LL)) ⊥]
      exact Submodule.fg_bot,
    Subsingleton.elim (α := Submodule D.what₂.LL (Fin 0 → D.what₂.LL)) _ _⟩
  jAmb_basis := fun _ _ => ⟨linearIndependent_empty_type (ι := Fin 0),
    Subsingleton.elim (α := Submodule ℂ (EuclideanSpace ℂ (Fin 0))) _ _⟩
  jAmb_lat := fun _ _ _ => ⟨fun _ => ⟨fun _ => 0, Subsingleton.elim (α := EuclideanSpace ℂ (Fin 0)) _ _⟩,
    fun _ => trivial⟩
  jAmb_gen := fun _ _ _ _ => ⟨0, Subsingleton.elim (α := EuclideanSpace ℂ (Fin 0)) _ _⟩
  jAmb_norm := fun _ _ x => by
    refine (normAt_one D.what₂.embLL (EuclideanSpace.basisFun (Fin 0) ℂ) x).trans ?_
    exact congrArg norm (Subsingleton.elim (α := EuclideanSpace ℂ (Fin 0)) _ _)

end Small

def smallLevelSide (D : D7) : BaseLevelRowSide D := ⟨withRRDef (smallSide D D.what₂.onb0)⟩

theorem exists_p0Side : ∀ D : D7, ∃ X : BaseLevelRowSide D, X.s.RRDef ∧ Nonempty (AmbForm D X.s) :=
  fun D => ⟨smallLevelSide D, rrDef_withRRDef _, ⟨smallAmbForm D D.what₂.onb0⟩⟩

end GlobalTheory.ProvRowSide

end
