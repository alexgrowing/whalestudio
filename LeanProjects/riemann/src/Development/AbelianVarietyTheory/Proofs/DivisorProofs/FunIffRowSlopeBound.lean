import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientNormSquareData

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.RowSlopeCompare

open Formalism.DivisionValues Formalism.L2.Indef GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Same

variable {Bs : DefBase K} {Df : DefSide Bs} {κ : Bs.Tup → Type} [∀ t, Fintype (κ t)]
  [∀ t, DecidableEq (κ t)] {τ : Type} {m : ℕ}

structure Same (S : IndefData Df) (D : RowData K Bs.Tup κ τ (Fin S.D) Bs.Ix m)
    (e : ∀ t, (Fin (Df.nV t) → K) →ₗ[K] (κ t → K)) (σ : Fin m ≃ Bs.J) : Prop where

  ref : D.t₀ = Bs.μ0

  tup : D.tup = S.μ

  inj : ∀ t, Function.Injective (e t)

  good : ∀ t, LinearMap.range (e t) = D.V₀ t

  lat : ∀ t, (Df.Mt t).map ((e t).restrictScalars (𝓞 K)) = D.M t ⊓ (D.V₀ t).restrictScalars (𝓞 K)

  iota : ∀ t F, D.psi.mulVec ((S.ι t).mulVec ((Df.Pq t).mulVec F)) =
    (((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVec (e t F)

  part : D.part = S.Ep

  lam : ∀ p j c, D.lam p j c = S.lam (σ j) Bs.μ0 c p

  kap : D.kap = S.κ

  frame : D.XE = S.XE

variable {S : IndefData Df} {D : RowData K Bs.Tup κ τ (Fin S.D) Bs.Ix m}
  {e : ∀ t, (Fin (Df.nV t) → K) →ₗ[K] (κ t → K)} {σ : Fin m ≃ Bs.J}

end Same

theorem quotNormSq_eq [IsTotallyComplex K] {n d D : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding)
    (P : Matrix (Fin d) (Fin n) K) (hP : Function.Surjective P.mulVec)
    (XQ : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hQ : IsQuotMetric P H XQ)
    (ι : Matrix (Fin D) (Fin d) K) (hι : Function.Injective ι.mulVec) (v : InfinitePlace K) (y : Fin d → K) :
    quotNormSq X0 ⊤ (ι * P) v (ι.mulVec y) = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) XQ v y ^ 2 := by
  obtain ⟨hle, hrep⟩ := quotMetricRep K n d H X0 hX P hP XQ hQ v
  have hmap : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) K) (x : Fin b → K),
      (fun i => v.embedding (A.mulVec x i)) = (A.map v.embedding).mulVec fun i => v.embedding (x i) := by
    intro a b A x
    funext i
    simp [Matrix.mulVec, dotProduct]
  obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin n) (Fin d) K, P * R = 1 := by
    obtain ⟨g, hg⟩ := P.mulVecLin.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hP)
    refine ⟨LinearMap.toMatrix' g, ?_⟩
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
  have hlow : ∀ s ∈ {s : ℝ | ∃ F ∈ (⊤ : Submodule K (Fin n → K)), (ι * P).mulVec F = ι.mulVec y ∧
      s = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2},
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) XQ v y ^ 2 ≤ s := by
    rintro _ ⟨F, -, hF, rfl⟩
    rw [← Matrix.mulVec_mulVec] at hF
    have hF' := hι hF
    refine pow_le_pow_left₀ (Formalism.BasicNotions.normAt_nonneg _ _ _ _) ?_ 2
    rw [← (fnormRat K d XQ v y y).1, ← (fnormRat K n X0 v F F).1, ← hF', hmap]
    exact hle _
  have hmem : ∀ G : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v
      (G + R.mulVec (y - P.mulVec G)) ^ 2 ∈ {s : ℝ | ∃ F ∈ (⊤ : Submodule K (Fin n → K)),
      (ι * P).mulVec F = ι.mulVec y ∧ s = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2} := by
    intro G
    refine ⟨_, trivial, ?_, rfl⟩
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec (M := P), hR, Matrix.one_mulVec,
      add_sub_cancel]
  refine le_antisymm ?_ (le_csInf ⟨_, hmem 0⟩ hlow)
  obtain ⟨z, hz, hn, -⟩ := hrep fun i => v.embedding (y i)
  let f : (Fin n → ℂ) → ℝ := fun u => fnorm (X0 v) (u + (R.map v.embedding).mulVec
    ((fun i => v.embedding (y i)) - (P.map v.embedding).mulVec u)) ^ 2
  have hf : Continuous f := by
    unfold f fnorm Formalism.HermitianLatticesTheory.cnorm
    fun_prop
  have hd : DenseRange (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ))) :=
    DenseRange.piMap (fun _ => Formalism.BasicNotions.denseRange_embedding_of_isComplex v (IsTotallyComplex.isComplex v))
  have key : quotNormSq X0 ⊤ (ι * P) v (ι.mulVec y) ≤ f z := by
    refine hd.induction_on (p := fun u => quotNormSq X0 ⊤ (ι * P) v (ι.mulVec y) ≤ f u) z
      (isClosed_le continuous_const hf) fun G => ?_
    refine (csInf_le ⟨_, hlow⟩ (hmem G)).trans (le_of_eq ?_)
    rw [← (fnormRat K n X0 v _ 0).1]
    unfold f
    congr 2
    have h1 := hmap R (y - P.mulVec G)
    have h2 := hmap P G
    funext i
    have h3 : (fun i => v.embedding ((y - P.mulVec G) i)) = (fun i => v.embedding (y i)) -
        (P.map v.embedding).mulVec (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)) G) := by
      funext k
      simp only [Pi.sub_apply, map_sub, congrFun h2 k]
      rfl
    rw [Pi.add_apply, map_add, congrFun h1 i, h3]
    rfl
  refine key.trans (le_of_eq ?_)
  unfold f
  rw [hz, sub_self, Matrix.mulVec_zero, add_zero, hn, (fnormRat K d XQ v y y).1]

def PartsOrth {Bs : DefBase K} (Df : DefSide Bs) : Prop :=
  ∀ v p p', p ≠ p' → ∀ x ∈ Df.Qp Bs.μ0 p, ∀ y ∈ Df.Qp Bs.μ0 p',
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Df.XQ Bs.μ0) v x y = 0

section Forward

variable [IsTotallyComplex K] {Bs : DefBase K} {Df : DefSide Bs}

def toRowData (S : IndefRows Df) (wf : Df.WF) (ho : PartsOrth Df) :
    RowData K Bs.Tup (fun t => Fin (Df.nV t)) (Fin S.D) (Fin S.D) Bs.Ix (Fintype.card Bs.J) where
  t₀ := Bs.μ0
  tup := S.μ
  tup_finite := twisted_finite S
  M := Df.Mt
  M_lattice := wf.Mt_lat
  V₀ _ := ⊤
  v t := S.ι t * Df.Pq t
  r _ := 1
  r_ref := rfl
  X₀ := Formalism.L2.DIV.stdFrame (Df.HV Bs.μ0)
  X₀_unit p := (Formalism.L2.DIV.frameOfSpec _ _ (wf.HV_pos _ p)).1
  psi := 1
  psi_injective := by simpa using Function.injective_id
  psi_range := by
    rw [Matrix.mulVecLin_one, LinearMap.range_id, Submodule.map_top, eq_comm, LinearMap.range_eq_top,
      Matrix.mulVecLin_mul]
    exact (S.l1c.1 _).2.comp (wf.Pq_surj _)
  part := S.Ep
  part_span := (S.Ep_decomp wf).2
  lam p j c := S.lam ((Fintype.equivFin Bs.J).symm j) Bs.μ0 c p
  lam_pos p j c := S.l1c.2.2.2.1 _ _ _ _
  kap := S.κ
  kap_pos := S.l1c.2.2.1
  XE := S.XE
  XE_unit := S.frames.1
  XE_norm p c x hx := by
    obtain ⟨y, rfl⟩ := (S.l1c.1 Bs.μ0).2 x
    rw [Matrix.one_mulVec, quotNormSq_eq (Df.HV Bs.μ0) (Formalism.L2.DIV.stdFrame (Df.HV Bs.μ0))
      (fun v => Formalism.L2.DIV.frameOfSpec _ _ (wf.HV_pos _ v)) _ (wf.Pq_surj _) _ (wf.XQ_quot _) _ (S.l1c.1 _).1,
      Formalism.BasicNotions.normAt_sq_eq_majAt, Formalism.BasicNotions.normAt_sq_eq_majAt,
      S.l1c.2.2.2.2.1 Bs.μ0 p (Or.inl rfl) c y hx y, Complex.re_ofReal_mul,
      Equiv.prod_comp (Fintype.equivFin Bs.J).symm (fun j => S.lam j Bs.μ0 c p)]
  XE_orth p c c' hc x hx y hy := by
    obtain ⟨x, rfl⟩ := (S.l1c.1 Bs.μ0).2 x
    obtain ⟨y, rfl⟩ := (S.l1c.1 Bs.μ0).2 y
    rw [S.l1c.2.2.2.2.1 Bs.μ0 p (Or.inl rfl) c x hx y,
      ho p c c' hc x (S.Qpart_base c ▸ hx) y (S.Qpart_base c' ▸ hy), mul_zero]

end Forward

section Backward

variable {T : Type} {κ : T → Type} [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)] {τ C : Type} [Fintype C]
  {n m : ℕ} (D : RowData K T κ τ (Fin n) C m) (v0 : InfinitePlace K)

def OneForm : Prop := ∀ t, (D.V₀ t).map (D.v t).mulVecLin = LinearMap.range D.psi.mulVecLin

abbrev baseOf : DefBase K where
  K0 := cmMax K
  v0 := v0
  Tup := T
  μ0 := D.t₀
  Ix := C
  fIx := inferInstance
  J := Fin m
  fJ := inferInstance

def coords (t : T) : (Fin (finrank K (D.V₀ t)) → K) →ₗ[K] (κ t → K) :=
  (D.V₀ t).subtype ∘ₗ (Module.finBasis K (D.V₀ t)).equivFun.symm.toLinearMap

theorem coords_range (t : T) : LinearMap.range (coords D t) = D.V₀ t := by
  rw [coords, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

theorem exists_proj (h : OneForm D) (t : T) : ∃ P : Matrix (Fin n) (Fin (finrank K (D.V₀ t))) K,
    Function.Surjective P.mulVec ∧ ∀ F, D.psi.mulVec (P.mulVec F) =
      (((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVec (coords D t F) := by
  obtain ⟨g, hg⟩ := D.psi.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 D.psi_injective)
  have hg' : ∀ x, g (D.psi.mulVec x) = x := fun x => LinearMap.congr_fun hg x
  have hs : ∀ F, D.psi.mulVec ((LinearMap.toMatrix'
      (g ∘ₗ ((((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVecLin) ∘ₗ coords D t)).mulVec F) =
      (((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVec (coords D t F) := by
    intro F
    have hF : (((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVec (coords D t F) ∈ LinearMap.range D.psi.mulVecLin := by
      rw [← h t]
      exact Submodule.smul_mem _ _ ⟨_, (coords_range D t).le (LinearMap.mem_range_self _ F), rfl⟩
    obtain ⟨x, hx⟩ := hF
    rw [LinearMap.toMatrix'_mulVec]
    show D.psi.mulVec (g ((((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVec (coords D t F))) = _
    rw [← hx, Matrix.mulVecLin_apply, hg']
  refine ⟨_, fun x => ?_, hs⟩
  have hx : D.psi.mulVecLin (((D.r t : Kˣ) : K) • x) ∈ (D.V₀ t).map (D.v t).mulVecLin :=
    h t ▸ LinearMap.mem_range_self _ _
  obtain ⟨G, hG, hx⟩ := hx
  rw [← coords_range] at hG
  obtain ⟨F, rfl⟩ := hG
  refine ⟨F, D.psi_injective ?_⟩
  rw [Matrix.mulVecLin_apply, hs, ← Matrix.mulVecLin_apply, hx, map_smul, smul_smul, Units.inv_mul, one_smul]

def sideOf (h : OneForm D) : DefSide (baseOf D v0) where
  nV t := finrank K (D.V₀ t)
  HV _ := 1
  Mt t := (D.M t).comap ((coords D t).restrictScalars (𝓞 K))
  dQ _ := n
  Pq t := (exists_proj D h t).choose
  XQ _ := D.XE
  Qp _ := D.part
  dZ _ _ := 0
  HT _ _ := 1
  XT _ _ _ := 1
  Tl _ _ := ⊤
  Zp _ _ _ := ⊤

def dataOf (h : OneForm D) : IndefData (sideOf D v0 h) where
  μ := D.tup
  Tw := D.tup_finite.toFinset
  D := n
  XE := D.XE
  Ep := D.part
  ι _ := (1 : Matrix (Fin n) (Fin n) K)
  dW _ := 0
  XW _ _ := 1
  Wp _ _ := ⊤
  M _ := ⊤
  θ _ _ := (1 : Matrix (Fin 0) (Fin 0) K)
  κ := D.kap
  lam j _ c p := D.lam p j c
  err0 _ _ := 0

end Backward

end GlobalTheory.RowSlopeCompare
