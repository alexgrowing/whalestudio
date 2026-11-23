import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodPairingUnitLattice
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ColumnAvoidanceConditions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MinkowskiBoundComapLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
import Formalism.LocalToGlobal.Columns.ToHLat
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.Divisibility.FramesLemmas

noncomputable section

namespace GlobalTheory.PeriodClassSum

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke
open scoped Matrix ComplexOrder

section Herm

variable {C ι : Type} [Fintype C] [Fintype ι] (w : C → ℕ) (G : Matrix ι ι ℂ)

def wForm (a b : C → ι → ℂ) : ℂ := ∑ c, ((w c : ℕ) : ℂ)⁻¹ * (star (a c) ⬝ᵥ G *ᵥ b c)

variable {G}

theorem wForm_nonneg (hG : G.PosSemidef) (a : C → ι → ℂ) : 0 ≤ wForm w G a a :=
  Finset.sum_nonneg fun c _ => mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (hG.dotProduct_mulVec_nonneg _)

theorem wForm_conj (hG : G.IsHermitian) (a b : C → ι → ℂ) : starRingEnd ℂ (wForm w G b a) = wForm w G a b := by
  unfold wForm
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast, starRingEnd_apply, ← Matrix.star_dotProduct, Matrix.star_mulVec, hG.eq,
    ← Matrix.dotProduct_mulVec]

theorem wForm_le (hG : G.PosSemidef) (a b : C → ι → ℂ) :
    ‖wForm w G a b‖ ^ 2 ≤ (wForm w G a a).re * (wForm w G b b).re := by
  let core : PreInnerProductSpace.Core ℂ (C → ι → ℂ) :=
    { inner := wForm w G
      conj_inner_symm := fun x y => wForm_conj w hG.1 x y
      re_inner_nonneg := fun x => (Complex.nonneg_iff.1 (wForm_nonneg w hG x)).1
      add_left := fun x y z => by
        simp only [wForm, Pi.add_apply, star_add, add_dotProduct, mul_add, Finset.sum_add_distrib]
      smul_left := fun x y r => by
        simp only [wForm, Pi.smul_apply, star_smul, smul_dotProduct, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by rw [starRingEnd_apply]; ring }
  have h : ‖wForm w G a b‖ * ‖wForm w G b a‖ ≤ (wForm w G a a).re * (wForm w G b b).re :=
    @InnerProductSpace.Core.inner_mul_inner_self_le ℂ _ _ _ _ core a b
  rwa [← wForm_conj w hG.1 b a, Complex.norm_conj, ← sq] at h

theorem wForm_star (hG : Gᵀ = G) (a : C → ι → ℂ) :
    wForm w G (fun c => star (a c)) (fun c => star (a c)) = wForm w G a a := by
  unfold wForm
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [star_star, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hG]

theorem wForm_eq_zero (hw : ∀ c, 0 < w c) (hG : G.PosDef) {a : C → ι → ℂ} (h : wForm w G a a = 0) : a = 0 := by
  funext c
  by_contra hc
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun c _ =>
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (hG.posSemidef.dotProduct_mulVec_nonneg (a c))).1 h c (Finset.mem_univ c)
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact (Nat.cast_ne_zero.2 (hw c).ne') (inv_eq_zero.1 h2)
  · exact (hG.dotProduct_mulVec_pos hc).ne' h2

end Herm

section Forms

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok)

def coordAt (v : InfinitePlace K) (φ : S.D → S.V) : S.Cl → S.ιV → ℂ :=
  fun c i => v.embedding (S.bV.repr (φ (S.outSec.rep c)) i)

theorem ipAt_eq (v : InfinitePlace K) (φ ψ : S.D → S.V) :
    S.ipAt h v φ ψ = @wForm _ _ h.fintypeCl _ (S.toCSD h).wt (S.gramV.map v.embedding) (coordAt S v φ) (coordAt S v ψ) := by
  unfold GSD.ipAt wForm GSD.pairAt
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, coordAt, starRingEnd_apply,
    mul_assoc]

def IsFormsOf (N : Submodule (𝓞 K) S.EqFun) (Λ : HLat K) (κ : Λ.V ≃ₗ[K] S.EqFun) : Prop :=
  (∀ x, x ∈ Λ.L ↔ κ x ∈ N) ∧
    ∀ v x, ((Formalism.HermitianLatticesTheory.normAt Λ.b Λ.X v x ^ 2 : ℝ) : ℂ) = S.ipAt h v (κ x : S.D → S.V) (κ x : S.D → S.V)

def gramAt (v : InfinitePlace K) : Matrix (Fin (S.hDim h)) (Fin (S.hDim h)) ℂ :=
  Matrix.of fun i j => S.ipAt h v (S.hB h i : S.D → S.V) (S.hB h j : S.D → S.V)

@[reducible] def formsLat (N : Submodule (𝓞 K) S.EqFun) : HLat K where
  V := S.EqFun
  ι := Fin (S.hDim h)
  b := S.hB h
  X v := frameOf (gramAt S h v)
  L := N

theorem gramAt_form (v : InfinitePlace K) (a b : Fin (S.hDim h) → ℂ) :
    star a ⬝ᵥ gramAt S h v *ᵥ b = @wForm _ _ h.fintypeCl _ (S.toCSD h).wt (S.gramV.map v.embedding)
      (∑ i, a i • coordAt S v (S.hB h i : S.D → S.V)) (∑ i, b i • coordAt S v (S.hB h i : S.D → S.V)) := by
  letI := h.fintypeCl
  have e : ∀ i j, gramAt S h v i j = _ := fun i j => ipAt_eq S h v _ _
  rw [dotProduct]
  simp only [Matrix.mulVec, dotProduct, e, Finset.mul_sum]
  simp only [wForm, Finset.sum_apply, Pi.smul_apply, star_sum, star_smul, sum_dotProduct, smul_dotProduct,
    Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
    Pi.star_apply]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by ring

theorem coordAt_sum (v : InfinitePlace K) (x : S.EqFun) :
    coordAt S v (x : S.D → S.V) = ∑ i, v.embedding ((S.hB h).repr x i) • coordAt S v (S.hB h i : S.D → S.V) := by
  funext c k
  conv_lhs => rw [← (S.hB h).sum_repr x]
  simp only [coordAt, AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum,
    map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, smul_eq_mul, map_mul]

theorem coordAt_indep (v : InfinitePlace K) :
    LinearIndependent ℂ fun i => fun p : S.Cl × S.ιV => coordAt S v (S.hB h i : S.D → S.V) p.1 p.2 := by
  letI := h.fintypeCl
  letI : Algebra K ℂ := v.embedding.toAlgebra
  let f : S.EqFun →ₗ[K] (S.Cl × S.ιV → K) := LinearMap.pi fun p =>
    S.bV.coord p.2 ∘ₗ LinearMap.proj (S.outSec.rep p.1) ∘ₗ S.EqFun.subtype
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro φ hφ
    apply (S.res h).injective
    rw [map_zero]
    apply Subtype.ext
    funext c
    exact S.bV.forall_coord_eq_zero_iff.1 fun k => congrFun hφ (c, k)
  exact (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 ((S.hB h).linearIndependent.map' f hf)

theorem gramAt_posDef (v : InfinitePlace K) (hG : (S.gramV.map v.embedding).PosDef) : (gramAt S h v).PosDef := by
  letI := h.fintypeCl
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun a ha => ?_
  · ext i j
    rw [Matrix.conjTranspose_apply, gramAt, Matrix.of_apply, Matrix.of_apply, ipAt_eq, ipAt_eq]
    exact wForm_conj _ hG.1 _ _
  · rw [gramAt_form]
    refine lt_of_le_of_ne (wForm_nonneg _ hG.posSemidef _) fun h0 => ha ?_
    have h1 := wForm_eq_zero _ (S.toCSD h).wt_pos hG h0.symm
    funext i
    refine Fintype.linearIndependent_iff.1 (coordAt_indep S h v) a ?_ i
    funext p
    simpa using congrFun (congrFun h1 p.1) p.2

theorem isFormsOf_formsLat (hG : ∀ v : InfinitePlace K, (S.gramV.map v.embedding).PosDef) (N : Submodule (𝓞 K) S.EqFun) :
    IsFormsOf S h N (formsLat S h N) (LinearEquiv.refl _ _) := by
  refine ⟨fun _ => Iff.rfl, fun v (x : S.EqFun) => ?_⟩
  have hm := (frameOfSpec _ _ (gramAt_posDef S h v (hG v))).2
  have h1 := gramAt_form S h v (Formalism.HermitianLatticesTheory.vecAt (S.hB h) v x) (Formalism.HermitianLatticesTheory.vecAt (S.hB h) v x)
  rw [← hm, metOf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec] at h1
  show _ = S.ipAt h v x x
  rw [ipAt_eq, coordAt_sum S h v x]
  refine Eq.trans ?_ h1
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rfl

theorem pairAt_eq (v : InfinitePlace K) (x : S.V) :
    S.pairAt v x x = star (fun i => v.embedding (S.bV.repr x i)) ⬝ᵥ
      S.gramV.map v.embedding *ᵥ fun i => v.embedding (S.bV.repr x i) := by
  simp only [GSD.pairAt, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, starRingEnd_apply,
    mul_assoc]

end Forms

section Int

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (w : Pl.Pl)

end Int

section Coeff

open GlobalTheory.TestLat.Compare

theorem pairBDualK : PairBDualK := by
  intro K _ _ ι _ n lam M hM x
  letI : StarRing K := starRingOfComm
  have h := GlobalTheory.TransDual.nabDelDual K ι n lam (fun _ => 1) M (fun _ => Matrix.conjTranspose_one) (fun _ => by simp) hM
  have e : (fun τ => hdualFr (1 : Matrix (Fin n) (Fin n) K) (M τ)) = fun τ => dualFr (M τ) := by
    funext τ
    ext y
    rw [hdualFr_triv, Matrix.one_mulVec]
  have e2 : ∀ y, pairK lam (fun _ => 1) y x = pairBK lam x y := fun y => by
    rw [pairK_apply, pairBK_apply, pairP_trivial]
    exact pairingBSymm_holds K ι n lam _ _
  rw [e] at h
  rw [← h.1, ← h.2]
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, e2]

theorem pairBDual : PairBDual := fun E K _ _ _ _ ι _ n emb lam L hL x =>
  pairBDualK K ι n lam _ (fun τ => GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L hL) x

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

theorem pairK_one_basis [StarRing K] (i j : VVIdx lam) :
    pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) (bVV K lam i) (bVV K lam j) = gramB K lam i j := by
  have h := pairK_basis (K := K) lam 1 i j
  rw [map_one] at h
  exact h

theorem gramB_posDef (φ : K →+* ℂ) : ((gramB K lam).map φ).PosDef := by
  letI : StarRing K := starRingOfComm
  have h := pairingPositive_holds K ι n lam (fun _ => 1) φ fun τ => by
    rw [Matrix.map_one _ (map_zero _) (map_one _)]; exact Matrix.PosDef.one
  simp only [pairK_one_basis] at h
  exact h

theorem map_pairBK (φ : K →+* ℂ) (x y : VV K lam) :
    φ (pairBK lam x y) = (fun i => φ ((bVV K lam).repr x i)) ⬝ᵥ (gramB K lam).map φ *ᵥ fun i => φ ((bVV K lam).repr y i) := by
  conv_lhs => rw [← (bVV K lam).sum_repr x, ← (bVV K lam).sum_repr y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, dotProduct,
    Matrix.mulVec, Matrix.map_apply, gramB, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Coeff

section Level

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (C C' : CoefPk X n (DecoSet X.E n ST SG))
  (Λ : LevFam X.E X.K n SG)

theorem chr_inv (g : Λ.grp) : Λ.inv.chr g = (Λ.chr g)⁻¹ := by
  rw [LevFam.chr_apply Λ g, ← Finset.prod_inv_distrib]
  exact LevFam.chr_apply Λ.inv g

theorem pairBK_smul {K ι : Type} [Field K] [Fintype ι] (lam : ι → DomWeight n) (a b : Kˣ) (e : b = a⁻¹)
    (x y : VV K lam) : pairBK lam ((a : K) • x) ((b : K) • y) = pairBK lam x y := by
  rw [e, map_smul, map_smul, LinearMap.smul_apply, smul_smul, Units.inv_mul, one_smul]

theorem card_stab_inv (d : DecoSet X.E n ST SG) :
    Nat.card (MulAction.stabilizer (formGSD C' Λ.inv).G d) = Nat.card (MulAction.stabilizer (formGSD C Λ).G d) := by
  let e : FormG Λ.inv ≃ FormG Λ := Equiv.refl (FormG Λ)
  refine Nat.card_congr (Equiv.subtypeEquiv e fun a => ?_)
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, formGSD_smul, formGSD_smul]
  rfl

def clInv : (formGSD C' Λ.inv).Cl ≃ (formGSD C Λ).Cl := Equiv.refl (formGSD C Λ).Cl

end Level

section Concrete

open GlobalTheory.TestLat.Compare

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

def dualVal (SG : Finset (HeightOneSpectrum (𝓞 X.E))) : CoefPk X (R.N R.m - 1) (DecoSet X.E (R.N R.m - 1) ∅ SG) :=
  roundPk X W.sgTrue fun d => d.1.N

@[reducible] def dualGSD : GSD X.K := formGSD (dualVal W (rowSG Pr sel mu)) (rowTy Ch sel mu P)

theorem dualOk (hX : X.Ok) : (dualGSD W Ch sel mu P).Ok :=
  formGSD_ok _ _ hX
    { nab_smul := fun a d => roundPk_nab X _ _ (d.1.N_act a.1.1 a.2)
      del_smul := fun a d => roundPk_del X _ _ (d.1.N_act a.1.1 a.2)
      inv := roundPk_inv X _ _ hX.emb_star }

def rowPair : BiPair (dualGSD W Ch sel mu P) (mtildeGSD W Ch sel mu P) where
  tr := MonoidHom.id (FormG (rowTy Ch sel mu P))
  p := id
  B := pairBK W.sgTrue
  hp _ _ := rfl
  inv g x y :=
    (pairBK_smul W.sgTrue _ _ (chr_inv (rowTy Ch sel mu P) g.2) _ _).trans
      (pairingBInvariant_holds X.E X.K X.Tau _ X.emb W.sgTrue (ufGL _ _ g.1) x y)

def classSum (h : (mtildeGSD W Ch sel mu P).Ok) :
    (dualGSD W Ch sel mu P).EqFun →ₗ[X.K] (mtildeGSD W Ch sel mu P).EqFun →ₗ[X.K] X.K :=
  (rowPair W Ch sel mu P).formOf h (mtildeGSD W Ch sel mu P).outSec

theorem dual_gramV : (dualGSD W Ch sel mu P).gramV = gramB X.K W.sgTrue := by
  ext i j
  have e : gramKd X.emb (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) X.E) = fun _ => 1 := by
    funext τ
    rw [gramKd, Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]
  show pairK W.sgTrue (gramKd X.emb 1) (bVV _ _ i) (bVV _ _ j) = _
  rw [e]
  exact pairK_one_basis W.sgTrue i j

theorem row_gramV : (mtildeGSD W Ch sel mu P).gramV = gramB X.K W.sgTrue := by
  ext i j
  have e : gramK X.emb (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) X.E) = fun _ => 1 := by
    funext τ
    rw [gramK, Matrix.map_one _ (map_zero _) (map_one _)]
  show pairK W.sgTrue (gramK X.emb 1) (bVV _ _ i) (bVV _ _ j) = _
  rw [e]
  exact pairK_one_basis W.sgTrue i j

variable (h : (mtildeGSD W Ch sel mu P).Ok) (h' : (dualGSD W Ch sel mu P).Ok)

def IsConcrete (emb : X.K →+* ℂ) (Λ Λ' : HLat X.K) (per : Λ.V → Λ'.V → ℂ) : Prop :=
  ∃ (κ : Λ.V ≃ₗ[X.K] (dualGSD W Ch sel mu P).EqFun) (ι : Λ'.V ≃ₗ[X.K] (mtildeGSD W Ch sel mu P).EqFun),
    IsFormsOf _ h' (dualGSD W Ch sel mu P).intDel Λ κ ∧ IsFormsOf _ h (MtildeL W Ch sel mu P) Λ' ι ∧
      ∀ x z, per x z = emb (classSum W Ch sel mu P h (κ x) (ι z))

variable {W Ch sel mu P h h'}

end Concrete

section Record

open ColumnAvoidanceConditions

variable (D : D7) (EX : ErrX D) (Ch : Chars (fieldsOf D) (primesOf D EX) D.R.m)
  (sel : HeightOneSpectrum (𝓞 (fieldsOf D).F) → HeightOneSpectrum (𝓞 (fieldsOf D).E)) {S : Set ℕ}

def LayerTie (ξ : Tup (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K S) {hc : D.what₂.Tau → HCParam D.R}
    {C : ColumnChain D.R D.what₂.Tau hc} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau hc C A P) (Λ' : HLat D.what₂.LL)
    (per : M.ptLat.V → Λ'.V → ℂ) : Prop :=
  ∃ (h : (mtildeGSD (wtsOf D EX) Ch sel ξ (rPsymF Ch)).Ok) (h' : (dualGSD (wtsOf D EX) Ch sel ξ (rPsymF Ch)).Ok),
    IsConcrete (wtsOf D EX) Ch sel ξ (rPsymF Ch) h h' D.what₂.embLL M.ptLat Λ' per ∧
      ∃ e : M.clsP ≃ (mtildeGSD (wtsOf D EX) Ch sel ξ (rPsymF Ch)).Cl,
        ∀ c, Nat.card (M.stabilizer₂ c) = ((mtildeGSD (wtsOf D EX) Ch sel ξ (rPsymF Ch)).toCSD h).wt (e c)

variable (tw : D.what₂.Tup → Tup (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K S) (Tw : TwForms D)
  (A : AmbForm D (RowSide.sharp D)) (u : D.what₂.Word)

def PeriodTie : Prop :=
  LayerTie D EX Ch sel (1 : Tup (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K S) (D.fm u) (A.MtH D.what₂.mu0)
      (PeriodPairingUnitLattice.per0 D A u) ∧
    ∀ μ, DV.Used D μ → μ ≠ D.what₂.mu0 → LayerTie D EX Ch sel (tw μ) (Tw.fm u μ) (A.MtH μ) (PeriodPairingUnitLattice.perTw D Tw A u μ)

end Record

end GlobalTheory.PeriodClassSum
