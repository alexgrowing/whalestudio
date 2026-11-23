import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataKerP
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns

noncomputable section

namespace Formalism.MainNotions.AlgebraicJets

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

section Ent

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def EntIn (i : ℕ) (S : Set ℂ) : Prop :=
  ∀ a, ∃ t : (M.lat (i + 1)).ι → ℂ, (∀ b, t b ∈ S) ∧
    C.K i (M.emb i ((M.lat i).b a)) = ∑ b, t b • M.emb (i + 1) ((M.lat (i + 1)).b b)

theorem EntIn.mono {i : ℕ} {S S' : Set ℂ} (h : EntIn M i S) (hS : S ⊆ S') : EntIn M i S' := by
  intro a
  obtain ⟨t, ht, he⟩ := h a
  exact ⟨t, fun b => hS (ht b), he⟩

theorem kRat_iff_entIn (i : ℕ) : M.KRat i ↔ EntIn M i (Set.range D.what₂.embLL) := by
  constructor
  · intro h a
    obtain ⟨y, hy⟩ := h ((M.lat i).b a)
    refine ⟨fun b => D.what₂.embLL ((M.lat (i + 1)).b.repr y b), fun b => ⟨_, rfl⟩, ?_⟩
    rw [← hy]
    conv_lhs => rw [← (M.lat (i + 1)).b.sum_repr y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [LinearMap.map_smulₛₗ]
  · intro h x
    choose t ht hK using h
    choose s hs using ht
    refine ⟨∑ a, (M.lat i).b.repr x a • ∑ b, s a b • (M.lat (i + 1)).b b, ?_⟩
    have h1 : C.K i (M.emb i x) = C.Klin i (M.emb i x) := rfl
    rw [h1]
    conv_rhs => rw [← (M.lat i).b.sum_repr x]
    simp only [map_sum, LinearMap.map_smulₛₗ, map_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : C.Klin i (M.emb i ((M.lat i).b a)) = C.K i (M.emb i ((M.lat i).b a)) := rfl
    rw [h2, hK a]
    simp only [hs]

theorem range_embLL_subset (D : D7) : Set.range D.what₂.embLL ⊆ (Qbar : Set ℂ) := by
  haveI := D.nfLL
  rintro z ⟨x, rfl⟩
  exact mem_algebraicClosure_iff'.mpr ((Algebra.IsIntegral.isIntegral x).map D.what₂.embLL.toRatAlgHom)

theorem entAlg_of_kRat {i : ℕ} (h : M.KRat i) : EntIn M i (Qbar : Set ℂ) :=
  EntIn.mono M ((kRat_iff_entIn M i).1 h) (range_embLL_subset D)

end Ent

def kRatTw (D : D7) (Tw : TwForms D) : Prop := ∀ u w, ∀ i < D.R.m, (Tw.fm u (D.what₂.muAt w)).KRat i

def LLKer (D : D7) (Tw : TwForms D) : Prop :=
  (∀ u, ∀ i < D.R.m, EntIn (D.fm u) i (Set.range D.what₂.embLL)) ∧
    ∀ u w, ∀ i < D.R.m, EntIn (Tw.fm u (D.what₂.muAt w)) i (Set.range D.what₂.embLL)

theorem llKer_iff (D : D7) (Tw : TwForms D) : LLKer D Tw ↔ kRat D ∧ kRatTw D Tw := by
  unfold LLKer kRatTw StandardLatticesGL3.kRat
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun u i hi => (kRat_iff_entIn _ i).2 (h1 u i hi), fun u w i hi => (kRat_iff_entIn _ i).2 (h2 u w i hi)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun u i hi => (kRat_iff_entIn _ i).1 (h1 u i hi), fun u w i hi => (kRat_iff_entIn _ i).1 (h2 u w i hi)⟩

theorem ker_alg (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (hc : Crv D cc δ) (h0 : t0Ex D) (ha : useAlg D)
    (ht : natTie D cc δ e) {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) (i : ℕ)
    (hN : Even (D.R.N i)) (hN' : Even (D.R.N (i + 1)))
    (hK : ∀ c c', GL3Theta.IsKer D (tor0 D cc δ) e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')) :
    ∀ c c', CoefIn D (O.Th i c c') Qbar := by
  intro c c'
  obtain ⟨n, r, t, hr, -, ht', hΘ⟩ := hK c c'
  obtain ⟨⟨t0, ht0⟩, -⟩ := h0 cc δ hc
  have hA : admitted D (D.R.N i) (D.R.N (i + 1)) (O.lat i c).1 (O.lat (i + 1) c').1 := ⟨hN, hN', (O.lat i c).2, (O.lat (i + 1) c').2⟩
  rw [hΘ]
  exact (ha cc δ hc t0 ht0 _ _ _ _ (admissible_self_dual_even hA).1 (admissible_self_dual_even hA).2.1 (admissible_self_dual_even hA).2.2 _ (ht t0 ht0 _ _ _ _ hA)).2.2.1
    n r t hr fun k => by
      obtain ⟨a, ha0, -, hat⟩ := ht' k
      exact ⟨a, ha0, hat⟩

theorem jet_alg (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) (hG : CoefIn D G Qbar) (P : MvPolynomial (GL3Theta.Idx D N N') ℂ)
    (hP : ∀ α, MvPolynomial.coeff α P ∈ Qbar) : GL3Theta.applyAt0 D P G ∈ Qbar := by
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem (hP α) ?_) (hG α)
  exact prod_mem fun i _ => natCast_mem _ _

section Alg

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (O : GL3Theta.LiftObj D C)

def RegIn (i : ℕ) (S : Set ℂ) (f : C.Y i → ℂ) : Prop :=
  ∃ (n : D.what₂.Tau → ℕ) (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ), (∀ α, MvPolynomial.coeff α Q ∈ S) ∧
    ∀ y, (∏ τ, C.de i y τ ^ n τ) * f y = GL3Theta.evFr D Q (O.frm i y)

def SrcTie (i : ℕ) (dg : D.what₂.Tau → ℕ) : Prop :=
  ∀ a c, ∃ Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ, (∀ α, MvPolynomial.coeff α Q ∈ Set.range D.what₂.embLL) ∧ GL3Columns.HomDeg D Q dg ∧
    C.sharp i (M.emb i ((M.lat i).b a) c) = fun y => GL3Theta.evFr D Q (O.frm i y)

def TgtTie (j : ℕ) : Prop :=
  ∀ F : IntermediateField ℚ ℂ, Set.range D.what₂.embLL ⊆ (F : Set ℂ) → ∀ φ ∈ M.Fi j, (∀ c, RegIn O j (F : Set ℂ) (φ c)) →
    ∃ t : (M.lat j).ι → ℂ, (∀ b, t b ∈ F) ∧ φ = ∑ b, t b • M.emb j ((M.lat j).b b)

def KFi (i : ℕ) : Prop := ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1)

def RhoAlg (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (i : ℕ) : Prop :=
  (∀ c, C.rhoDet i c ∈ Qbar) ∧ ∀ c', C.rhoDet' i c' ∈ Qbar

def Ties (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (i : ℕ) : Prop :=
  ∃ dg : D.what₂.Tau → ℕ,
    (∀ c c', GL3Theta.IsKer D (tor0 D cc δ) e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')) ∧ GL3Columns.liftTieH D O i dg ∧
    RhoAlg C i ∧ SrcTie M O i dg ∧ TgtTie M O (i + 1) ∧ KFi M i

def StatementJetEntriesAlgebraic (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (i : ℕ) : Prop :=
  Crv D cc δ → t0Ex D → useAlg D → natTie D cc δ e → i < D.R.m → Ties M O cc δ e i → EntIn M i (Qbar : Set ℂ)

end Alg

theorem evenN (R : Ranks) (j : ℕ) : Even (R.N j) := by
  show Even (R.k + j * (R.t + 1))
  exact R.k_even.add (Even.mul_left R.t_odd.add_one j)

theorem exists_map_eq {σ : Type} (F : IntermediateField ℚ ℂ) (Q : MvPolynomial σ ℂ) (h : ∀ α, MvPolynomial.coeff α Q ∈ F) :
    ∃ Q₀ : MvPolynomial σ F, MvPolynomial.map (algebraMap F ℂ) Q₀ = Q := by
  refine ⟨∑ α ∈ Q.support, MvPolynomial.monomial α (⟨MvPolynomial.coeff α Q, h α⟩ : F), ?_⟩
  conv_rhs => rw [Q.as_sum]
  simp only [map_sum, MvPolynomial.map_monomial]
  rfl

theorem coeff_map_mem {σ : Type} (F : IntermediateField ℚ ℂ) (Q₀ : MvPolynomial σ F) (α : σ →₀ ℕ) :
    MvPolynomial.coeff α (MvPolynomial.map (algebraMap F ℂ) Q₀) ∈ F := by
  rw [MvPolynomial.coeff_map]
  exact (MvPolynomial.coeff α Q₀).2

def evF (D : D7) (F : IntermediateField ℚ ℂ) {N : ℕ} (f : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) :
    MvPolynomial (GL3Theta.FrV D N) F →+* ℂ :=
  MvPolynomial.eval₂Hom (algebraMap F ℂ) (fun k : GL3Theta.FrV D N => f k.1 k.2.1 k.2.2)

theorem evFr_map (D : D7) (F : IntermediateField ℚ ℂ) {N : ℕ} (f : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ)
    (R : MvPolynomial (GL3Theta.FrV D N) F) : GL3Theta.evFr D (MvPolynomial.map (algebraMap F ℂ) R) f = evF D F f R := by
  simp only [GL3Theta.evFr, evF, MvPolynomial.eval_map, MvPolynomial.coe_eval₂Hom]

def polG (D : D7) (F : IntermediateField ℚ ℂ) {N N' : ℕ} (s : D.what₂.Tau → F) :
    MvPolynomial (GL3Theta.FrV D N) F →+* MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') F) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) (fun k : GL3Theta.FrV D N => ∑ b : Fin N',
    MvPolynomial.C (MvPolynomial.C (s k.1) * (if h : (k.2.2 : ℕ) < N' then MvPolynomial.X ((k.1, b, ⟨k.2.2, h⟩) : GL3Theta.FrV D N') else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : GL3Theta.Idx D N N'))

theorem polD_eq (D : D7) (F : IntermediateField ℚ ℂ) {N N' : ℕ} (s : D.what₂.Tau → F) (Q₀ : MvPolynomial (GL3Theta.FrV D N) F)
    (f : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    GL3Theta.polD D (fun τ => (s τ : ℂ)) (MvPolynomial.map (algebraMap F ℂ) Q₀) f = MvPolynomial.map (evF D F f) (polG D F s Q₀) := by
  unfold GL3Theta.polD
  induction Q₀ using MvPolynomial.induction_on
  next a =>
    simp [polG, evF]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p n hp =>
    simp only [map_mul] at hp ⊢
    rw [hp]
    refine congrArg₂ (· * ·) rfl ?_
    by_cases hn : (n.2.2 : ℕ) < N'
    · simp [polG, evF, hn]
    · simp [polG, evF, hn]

theorem exists_jetPoly (D : D7) (F : IntermediateField ℚ ℂ) {N N' : ℕ} (s : D.what₂.Tau → F) (Q₀ : MvPolynomial (GL3Theta.FrV D N) F)
    (G : VC D N N' → ℂ) (hG : CoefIn D G F) :
    ∃ R : MvPolynomial (GL3Theta.FrV D N') F, ∀ f : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ,
      evF D F f R = GL3Theta.applyAt0 D (GL3Theta.polD D (fun τ => (s τ : ℂ)) (MvPolynomial.map (algebraMap F ℂ) Q₀) f) G := by
  classical
  have hc : ∀ α : GL3Theta.Idx D N N' →₀ ℕ, (α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α ∈ F :=
    fun α => mul_mem (prod_mem fun i _ => natCast_mem _ _) (hG α)
  refine ⟨∑ α ∈ (polG D F s Q₀).support,
    MvPolynomial.coeff α (polG D F s Q₀) * MvPolynomial.C (⟨_, hc α⟩ : F), fun f => ?_⟩
  rw [polD_eq]
  unfold GL3Theta.applyAt0
  rw [Finset.sum_subset (MvPolynomial.support_map_subset _ _) ?hz]
  · simp only [map_sum, map_mul, MvPolynomial.coeff_map]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [mul_assoc]
    exact congrArg₂ (· * ·) rfl (MvPolynomial.eval₂Hom_C _ _ _)
  · intro α _ hα
    have h0 : MvPolynomial.coeff α (MvPolynomial.map (evF D F f) (polG D F s Q₀)) = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hα
    rw [h0]
    ring

def detP (D : D7) (F : IntermediateField ℚ ℂ) (N : ℕ) (τ : D.what₂.Tau) : MvPolynomial (GL3Theta.FrV D N) F :=
  Matrix.det (Matrix.of fun a b : Fin N => (MvPolynomial.X ((τ, a, b) : GL3Theta.FrV D N) : MvPolynomial (GL3Theta.FrV D N) F))

theorem evF_detP (D : D7) (F : IntermediateField ℚ ℂ) {N : ℕ} (f : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) (τ : D.what₂.Tau) :
    evF D F f (detP D F N τ) = (f τ).det := by
  unfold detP
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [evF, RingHom.mapMatrix_apply]

theorem dgen_alg {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) (τ : D.what₂.Tau) :
    O.dgen τ ∈ Qbar := by
  obtain ⟨M, hM, _, hs⟩ := O.dgen_gen
  haveI := hM
  obtain ⟨s, hs1, _⟩ := hs τ
  rw [← hs1]
  exact mem_algebraicClosure_iff'.mpr ((Algebra.IsIntegral.isIntegral s).map M.val)

theorem stmt_entAlg {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (O : GL3Theta.LiftObj D C)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (i : ℕ) : StatementJetEntriesAlgebraic M O cc δ e i := by
  rintro hc h0 ha ht hi ⟨dg, hKer, hL, hρ, hS, hT, hF⟩ a
  have hΘ := ker_alg D cc δ e hc h0 ha ht O i (evenN D.R i) (evenN D.R (i + 1)) hKer
  have hmem : M.emb i ((M.lat i).b a) ∈ M.Fi i := by
    rw [← (M.emb_basis i).2]; exact Submodule.subset_span ⟨a, rfl⟩
  refine hT Qbar (range_embLL_subset D) _ (hF _ hmem) fun c' => ?_
  choose Q hQL hQH hQ using hS a
  choose Q₀ hQ₀ using fun c => exists_map_eq Qbar (Q c) (fun α => range_embLL_subset D (hQL c α))
  choose R hR using fun c => exists_jetPoly D Qbar (fun τ => ⟨O.dgen τ, dgen_alg O τ⟩) (Q₀ c) (O.Th i c c') (hΘ c c')
  refine ⟨fun τ => (C.sDiv i τ).toNat, MvPolynomial.map (algebraMap Qbar ℂ) ((∏ τ, detP D Qbar _ τ ^ (-(C.sDiv i τ)).toNat) *
    ∑ c, MvPolynomial.C ((((Nat.card (C.stab i c) : ℕ) : Qbar))⁻¹ * (⟨C.rhoDet i c, hρ.1 c⟩ * ⟨C.rhoDet' i c', hρ.2 c'⟩)) * R c),
    fun α => coeff_map_mem _ _ _, fun y' => ?_⟩
  rw [evFr_map, map_mul, map_prod, map_sum]
  have hK : C.K i (M.emb i ((M.lat i).b a)) c' y' = (∏ τ, C.de (i + 1) y' τ ^ C.sDiv i τ)⁻¹ *
      ∑ c, (((Nat.card (C.stab i c) : ℕ) : ℂ))⁻¹ * (C.rhoDet i c * C.rhoDet' i c') * evF D Qbar (O.frm (i + 1) y') (R c) := by
    simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, ColumnChain.wt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ColumnChain.Kmap,
      LinearMap.smul_apply, LinearMap.comp_apply, ColumnChain.divDe, mulFun, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hQ c, hL c c' (Q c) (hQH c) y', hR c, hQ₀ c]
    ring
  rw [hK, ← mul_assoc]
  congr 1
  · rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, evF_detP, ← O.frm_de (i + 1) hi y' τ]
    have hne : C.de (i + 1) y' τ ≠ 0 := C.de_ne (i + 1) y' τ
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hne]
    congr 1
    beta_reduce
    omega
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul]
    congr 1
    simp [evF]

theorem ties_of_liftTie {D : D7} {T : Tor D} {e : FamE D} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)}
    {O : GL3Theta.LiftObj D C} {i : ℕ} (h : GL3Theta.liftTie D T e O i) (dg : D.what₂.Tau → ℕ) :
    (∀ c c', GL3Theta.IsKer D T e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')) ∧ GL3Columns.liftTieH D O i dg := by
  refine ⟨h.1, ?_⟩
  intro c c' Qp _ y'
  exact h.2 c c' Qp y'

theorem ties_of_KJ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : GL3Columns.DtAd D} (hp : GL3Columns.aux₃ D cc δ e Q)
    {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {O : GL3Theta.LiftObj D C} {i : ℕ} (hi : i < D.R.m)
    (A : GL3Columns.AdLift D cc δ e Q O i) (hr : GL3Columns.RankOK D i) (c0 : ℂ) (h0 : A.Θ.IsResidueClassZero c0) (hd : A.IsDef c0) (ht : A.ThIs) :
    (∀ c c', GL3Theta.IsKer D (tor0 D cc δ) e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')) ∧ GL3Columns.liftTieH D O i A.dg :=
  ⟨(hp.1.2.2.2.2.1 u C O i A hr).2.2 ht, hp.liftTieH hi A hr c0 h0 hd ht⟩

def entAlgAll (D : D7) (Tw : TwForms D) : Prop :=
  (∀ u, ∀ i < D.R.m, EntIn (D.fm u) i (Qbar : Set ℂ)) ∧ ∀ u w, ∀ i < D.R.m, EntIn (Tw.fm u (D.what₂.muAt w)) i (Qbar : Set ℂ)

theorem exists_field (D : D7) (S : Set ℂ) (hS : S.Finite) (hA : S ⊆ (Qbar : Set ℂ)) :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ Set.range D.what₂.embLL ⊆ (F : Set ℂ) ∧ S ⊆ (F : Set ℂ) := by
  classical
  haveI := D.nfLL
  haveI : Finite S := hS.to_subtype
  haveI h1 : FiniteDimensional ℚ D.what₂.embLL.toRatAlgHom.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField D.what₂.embLL.toRatAlgHom).toLinearEquiv
  haveI h2 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => mem_algebraicClosure_iff'.mp (hA hx)
  refine ⟨D.what₂.embLL.toRatAlgHom.fieldRange ⊔ IntermediateField.adjoin ℚ S, inferInstance, ?_, ?_⟩
  · rintro z ⟨y, rfl⟩
    exact (le_sup_left : D.what₂.embLL.toRatAlgHom.fieldRange ≤ _) (AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩)
  · intro z hz
    exact (le_sup_right : IntermediateField.adjoin ℚ S ≤ _) (IntermediateField.subset_adjoin ℚ S hz)

def muFin (D : D7) : Prop := (Set.range D.what₂.muAt).Finite

theorem exists_LL (D : D7) (Tw : TwForms D) (hfin : muFin D) (h : entAlgAll D Tw) :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ Set.range D.what₂.embLL ⊆ (F : Set ℂ) ∧
      (∀ u, ∀ i < D.R.m, EntIn (D.fm u) i (F : Set ℂ)) ∧ ∀ u w, ∀ i < D.R.m, EntIn (Tw.fm u (D.what₂.muAt w)) i (F : Set ℂ) := by
  classical
  haveI := D.wordFin
  obtain ⟨h1, h2⟩ := h
  unfold EntIn at h1 h2
  choose t1 ht1 he1 using h1
  choose t2 ht2 he2 using h2
  haveI := hfin.to_subtype
  have hrep : ∀ μ : Set.range D.what₂.muAt, ∃ w, D.what₂.muAt w = μ.1 := fun μ => μ.2
  choose wr hwr using hrep
  let S : Set ℂ := (⋃ (u : D.what₂.Word) (i : Fin D.R.m) (a) (b), {t1 u i i.2 a b}) ∪
    ⋃ (u : D.what₂.Word) (μ : Set.range D.what₂.muAt) (i : Fin D.R.m) (a) (b), {t2 u (wr μ) i i.2 a b}
  have hSfin : S.Finite :=
    (Set.finite_iUnion fun u => Set.finite_iUnion fun i => Set.finite_iUnion fun a =>
      Set.finite_iUnion fun b => Set.finite_singleton _).union
    (Set.finite_iUnion fun u => Set.finite_iUnion fun μ => Set.finite_iUnion fun i =>
      Set.finite_iUnion fun a => Set.finite_iUnion fun b => Set.finite_singleton _)
  have hSA : S ⊆ (Qbar : Set ℂ) := by
    intro z hz
    simp only [S, Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    rcases hz with ⟨u, i, a, b, rfl⟩ | ⟨u, μ, i, a, b, rfl⟩
    · exact ht1 u i i.2 a b
    · exact ht2 u (wr μ) i i.2 a b
  obtain ⟨F, hF, hLL, hSF⟩ := exists_field D S hSfin hSA
  refine ⟨F, hF, hLL, ?_, ?_⟩
  · intro u i hi a
    refine ⟨t1 u i hi a, fun b => hSF ?_, he1 u i hi a⟩
    simp only [S, Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff]
    exact Or.inl ⟨u, ⟨i, hi⟩, a, b, rfl⟩
  · intro u w i hi
    let μ : Set.range D.what₂.muAt := ⟨D.what₂.muAt w, w, rfl⟩
    have e : D.what₂.muAt (wr μ) = D.what₂.muAt w := hwr μ
    rw [← e]
    intro a
    refine ⟨t2 u (wr μ) i hi a, fun b => hSF ?_, he2 u (wr μ) i hi a⟩
    simp only [S, Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff]
    exact Or.inr ⟨u, μ, ⟨i, hi⟩, a, b, rfl⟩

theorem rhoAlg_of {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C)
    (h3 : GL3Theta.rhoThreeOf D C O.mt) (hp : GL3Theta.PowRatAll D) {i : ℕ} (hi : i < D.R.m) : RhoAlg C i := by
  refine ⟨fun c => ?_, fun c' => ?_⟩
  · rw [(O.c13 i hi).1 c]
    obtain ⟨h, z, hz⟩ := hp (O.dt i c)
    obtain ⟨hx, -⟩ := ((h3 i hi).1 _ h z hz).1
    exact hx
  · rw [(O.c13 i hi).2 c']
    obtain ⟨h, z, hz⟩ := hp (O.dt (i + 1) c')
    obtain ⟨hx, -⟩ := ((h3 i hi).1 _ h z hz).2
    exact hx

def TiesMem (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ u, ∃ O : GL3Theta.LiftObj D (D.mem u).C, O.IsMem ∧ ∀ i < D.R.m, Ties (D.fm u) O cc δ e i

def TiesTw (D : D7) (Tw : TwForms D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ u w, ∃ O : GL3Theta.LiftObj D (D.chTw u (D.what₂.muAt w)), ∀ i < D.R.m, Ties (Tw.fm u (D.what₂.muAt w)) O cc δ e i

theorem entAlgAll_of (D : D7) (Tw : TwForms D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (hc : Crv D cc δ) (h0 : t0Ex D)
    (ha : useAlg D) (ht : natTie D cc δ e) (h1 : TiesMem D cc δ e) (h2 : TiesTw D Tw cc δ e) :
    entAlgAll D Tw := by
  refine ⟨fun u i hi => ?_, fun u w i hi => ?_⟩
  · obtain ⟨O, _, hO⟩ := h1 u
    exact stmt_entAlg (D.fm u) O cc δ e i hc h0 ha ht hi (hO i hi)
  · obtain ⟨O, hO⟩ := h2 u w
    exact stmt_entAlg (Tw.fm u (D.what₂.muAt w)) O cc δ e i hc h0 ha ht hi (hO i hi)

theorem choice_possible (D : D7) (Tw : TwForms D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (hc : Crv D cc δ)
    (hg : GaloisThetaProperties D) (ht : natTie D cc δ e) (h1 : TiesMem D cc δ e) (h2 : TiesTw D Tw cc δ e) (hfin : muFin D) :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ Set.range D.what₂.embLL ⊆ (F : Set ℂ) ∧
      (∀ u, ∀ i < D.R.m, EntIn (D.fm u) i (F : Set ℂ)) ∧ ∀ u w, ∀ i < D.R.m, EntIn (Tw.fm u (D.what₂.muAt w)) i (F : Set ℂ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h0, -, ha, -⟩ := hg
  exact exists_LL D Tw hfin (entAlgAll_of D Tw cc δ e hc h0 ha ht h1 h2)

def kRatTwF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Tw : ∀ x (i : Fm.Ix x), TwForms (Fm.D x i)) : Prop :=
  ∀ x (i : Fm.Ix x), kRatTw (Fm.D x i) (Tw x i)

def LLKerF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Tw : ∀ x (i : Fm.Ix x), TwForms (Fm.D x i)) : Prop :=
  ∀ x (i : Fm.Ix x), LLKer (Fm.D x i) (Tw x i)

theorem llKerF_iff {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Tw : ∀ x (i : Fm.Ix x), TwForms (Fm.D x i)) :
    LLKerF Fm Tw ↔ kRatF Fm ∧ kRatTwF Fm Tw := by
  unfold LLKerF kRatTwF StandardLatticesGL3.kRatF GL3Theta.Fam
  constructor
  · intro h
    exact ⟨fun x i => ((llKer_iff _ _).1 (h x i)).1, fun x i => ((llKer_iff _ _).1 (h x i)).2⟩
  · rintro ⟨h1, h2⟩ x i
    exact (llKer_iff _ _).2 ⟨h1 x i, h2 x i⟩

end Formalism.MainNotions.AlgebraicJets
