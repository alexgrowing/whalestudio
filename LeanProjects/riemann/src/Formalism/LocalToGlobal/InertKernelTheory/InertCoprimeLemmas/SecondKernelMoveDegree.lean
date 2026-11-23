import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.K2Hermitian
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelMoveDegree

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelSeries
  Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelHermitian

section Move

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

def gmOf {p : ℕ} [Fact p.Prime] {X : Sys p} (u : D.what₂.Word) (μ : D.what₂.Tup) {σ : D.what₂.LL →+* X.G.Kf}
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (A : ∀ j, X.Lt j → ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v)) :
    ∀ j, X.Lt j → ((ex.tw.fm u μ).lat j).V → (X.Pj j).Xsp :=
  fun j La x => (X.Pj j).natAct (fun v => (A j La v)⁻¹) (cmp j x La.1 La.2)

def CmpVt {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (u : D.what₂.Word) (μ : D.what₂.Tup) {σ : D.what₂.LL →+* X.G.Kf}
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (j : ℕ) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ x : ((ex.tw.fm u μ).lat j).V, cmp j x La.1 La.2 ∈ (X.Pj j).Vtup

end Move

def MoveHOf : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p)
    (Y : Pend X) (σ : D.what₂.LL →+* X.G.Kf) (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (A : ∀ j, X.Lt j → ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v)) (j : ℕ),
    CmpVt Y u μ cmp j → MoveH Y u μ cmp A (gmOf u μ cmp A) j

def NuSumTie {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (u : D.what₂.Word) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (j : ℕ) : Prop :=
  ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)),
    ((∑ r : Fin (D.R.N j), nuT D u j (pos ⟨v, s⟩) r : ℕ) : ℤ) = ∑ i ∈ Icc 1 (NN X.G.P.m X.t (j + 1)), X.nuv v (j + 1) s i

def NuRowTie {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (u : D.what₂.Word) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (j : ℕ) : Prop :=
  ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)) (r : Fin (D.R.N j)), ((nuT D u j (pos ⟨v, s⟩) r : ℕ) : ℤ) = X.nuv v (j + 1) s (r.val + 1)

def NuSumOfRow : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (D : D7) (u : D.what₂.Word) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ),
    RankTie X D j → NuRowTie X D u pos j → NuSumTie X D u pos j

def PolDYDeg : Prop :=
  ∀ (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ),
    Q ∈ WtPol ℂ ν → ∀ α ∈ (polDY D s Q (N' := N')).support, ∀ τ : D.what₂.Tau,
      ∑ b : Fin N', ∑ a : Fin N, α (τ, b, a) = ∑ r : Fin N, ν τ r

def TieDegOf : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (j : ℕ) (hN : RankTie X D j),
    NuSumTie X D u pos j → KernelEntryDegreeCondition (Y := Y) t u μ cls j (eIdx X D pos j hN)

def DelPolM : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : Formalism.L2.G.Pend.FinStab X.Lv) (g : GL3Theta.G1 p)
    (hLT : Formalism.L2.G.Pend.LTIso g) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : Formalism.L2.PairingIndexBounds.F.FData X D)
    (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (lamK : TaylorLogMetric.Qbar →+* ℂ_[p]) (SS : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.E)))
    (cl : ℕ) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (TensorProduct D.host.F D.host.E
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers D.host.F) D.host.F))ˣ → ℂ),
    letI := Formalism.L2.G.Pend.wittFractionAlgebraCp p
    letI := Formalism.L2.G.Pend.algKfC E.toCEmb
    FrInv fd →
    Formalism.L2.G.Pend.StabGeo X ℂ_[p] hfin (Formalism.L2.G.Pend.thFOf X pos
      (Formalism.L2.PairingIndexBounds.F.FrecG E.toCEmb pos fd B χ lamK SS cl Ξ₀ muT (Formalism.L2.PairingIndexBounds.F.ltC g hLT))) →
    Formalism.L2.G.Pend.KapStab X ℂ_[p] →
    let Y := pendG X E hfin hst hLT D pos fd B χ lamK SS cl Ξ₀ muT
    ∀ (σ : D.what₂.LL →+* X.G.Kf) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
      (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
      (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1)) (ι : ℂ →+* Y.Kc)
      (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
      (τ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → XspC (X.Pj (j + 1)) Y.Kc →ₗ[Y.Kc] XspC (X.Pj (j + 1)) Y.Kc)
      (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Y.Kc) (sH : ∀ j, X.Lt j → X.Lt (j + 1) → Y.Kc)
      (j : ℕ) (cK : Y.Kc) (hN : RankTie X D j),
      CmpVt Y u μ cmp j →
      TieOpH (Y := Y) t u μ cls (gmOf u μ cmp (fun j La => glInv X j (BOf fd j La))) j (eIdx X D pos j hN) (Φ₀ j) →
      NuSumTie X D u pos j →
      TieSerH Y t u μ cls κ ι
        (fun j La La' => resV (Formalism.L2.G.Pend.kapOf X pos j) (serG fd B χ lamK SS cl Ξ₀ muT j La La')) sH j
        (eIdx X D pos j hN) →
      TieChiH Y t u μ cls κ ι sc sH (fun j La => Formalism.L2.G.Pend.cA X Y.Kc j (BOf fd j La)) j cK →
      DelYEqH Y (fun j La' => VOf Y.Kc fd (Formalism.L2.PairingIndexBounds.F.ltC g hLT) j La') τ j →
        DelPolAt (Y := Y) t u μ cls cmp κ (phiH D Φ₀ τ sc) (srOf Y) j cK

section Deg

open MvPolynomial

variable {D : D7}

open Classical in

def wF {N : ℕ} (τ : D.what₂.Tau) : GL3Theta.FrV D N → ℕ := fun k => if k.1 = τ then 1 else 0

open Classical in

def wI {N N' : ℕ} (τ : D.what₂.Tau) : GL3Theta.Idx D N N' → ℕ := fun k => if k.1 = τ then 1 else 0

theorem aeval_CX_monomial {σ R : Type} [CommRing R] (c : σ → R) (s : σ →₀ ℕ) (a : R) :
    aeval (fun i => C (c i) * X i) (monomial s a) = monomial s (a * s.prod fun i k => c i ^ k) := by
  rw [aeval_monomial, monomial_eq, Finsupp.prod, Finsupp.prod, Finsupp.prod, algebraMap_eq]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow]
  ring

theorem coeff_aeval_CX {σ R : Type} [CommRing R] (c : σ → R) (Q : MvPolynomial σ R) (n : σ →₀ ℕ) :
    coeff n (aeval (fun i => C (c i) * X i) Q) = (n.prod fun i k => c i ^ k) * coeff n Q := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [aeval_CX_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · rw [mul_zero]
  | add P Q hP hQ => rw [map_add, coeff_add, coeff_add, hP, hQ, mul_add]

theorem colSub_diag {N : ℕ} (d : D.what₂.Tau → ℂ) :
    colSub (fun τ' => Matrix.diagonal fun _ : Fin N => d τ') =
      aeval (fun k : GL3Theta.FrV D N => C (d k.1) * X k) := by
  apply MvPolynomial.algHom_ext
  intro k
  rw [colSub, aeval_X, aeval_X, Finset.sum_eq_single k.2.2]
  · rw [Matrix.diagonal_apply_eq]
  · intro r _ hr
    rw [Matrix.diagonal_apply_ne _ hr, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem two_pow_ite (b : Prop) [Decidable b] (k : ℕ) :
    ((if b then (2 : ℂ) else 1) ^ k) = (2 : ℂ) ^ (if b then k else 0) := by
  split_ifs <;> simp

theorem wt_deg {N : ℕ} (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ) (hQ : Q ∈ WtPol ℂ ν)
    (τ : D.what₂.Tau) (m : GL3Theta.FrV D N →₀ ℕ) (hm : coeff m Q ≠ 0) :
    Finsupp.weight (wF τ) m = ∑ r, ν τ r := by
  classical
  set d : D.what₂.Tau → ℂ := fun τ' => if τ' = τ then 2 else 1 with hd
  have hB : IsBor (fun τ' => Matrix.diagonal fun _ : Fin N => d τ') := by
    intro τ'
    refine ⟨fun r s hsr => Matrix.diagonal_apply_ne _ (ne_of_gt hsr), fun r => ?_⟩
    show Matrix.diagonal (fun _ : Fin N => d τ') r r ≠ 0
    rw [Matrix.diagonal_apply_eq, hd]
    show (if τ' = τ then (2 : ℂ) else 1) ≠ 0
    split_ifs <;> norm_num
  have h1 := hQ (fun τ' => Matrix.diagonal fun _ : Fin N => d τ') hB
  rw [colSub_diag] at h1
  have h2 := congrArg (coeff m) h1
  rw [coeff_aeval_CX, coeff_smul, smul_eq_mul] at h2
  have h3 := mul_right_cancel₀ hm h2
  have hl : (m.prod fun k e => d k.1 ^ e) = (2 : ℂ) ^ Finsupp.weight (wF τ) m := by
    rw [Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, hd]
    simp only [two_pow_ite]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold wF
    split_ifs <;> simp
  have hr : (∏ τ', ∏ r, (Matrix.diagonal fun _ : Fin N => d τ') r r ^ ν τ' r) = (2 : ℂ) ^ ∑ r, ν τ r := by
    simp only [Matrix.diagonal_apply_eq, hd, two_pow_ite]
    simp only [Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Finset.sum_eq_single τ]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hl, hr] at h3
  have h4 : ((2 ^ Finsupp.weight (wF τ) m : ℕ) : ℂ) = ((2 ^ ∑ r, ν τ r : ℕ) : ℂ) := by push_cast; exact h3
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h4)

theorem polDY_wh {N N' : ℕ} (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (hQ : Q ∈ WtPol ℂ ν) (τ : D.what₂.Tau) :
    IsWeightedHomogeneous (wI (N := N) (N' := N') τ) (polDY D s Q (N' := N')) (∑ r, ν τ r) := by
  have hf : ∀ k : GL3Theta.FrV D N, IsWeightedHomogeneous (wI (N := N) (N' := N') τ)
      (∑ b : Fin N', C (C (s k.1) * (if h : (k.2.2 : ℕ) < N' then (X (k.1, b, ⟨k.2.2, h⟩) : MvPolynomial (GL3Theta.FrV D N') ℂ) else 0)) *
        X ((k.1, b, k.2.1) : GL3Theta.Idx D N N')) (wF τ k) := by
    intro k
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    exact (isWeightedHomogeneous_X _ _ _).C_mul _
  unfold polDY
  conv => enter [2]; rw [Q.as_sum]
  rw [map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  rw [aeval_monomial, MvPolynomial.algebraMap_apply, ← wt_deg ν Q hQ τ m (mem_support_iff.1 hm), Finsupp.weight_apply]
  have := (isWeightedHomogeneous_C (wI (N := N) (N' := N') τ) (algebraMap ℂ (MvPolynomial (GL3Theta.FrV D N') ℂ) (coeff m Q))).mul
    (IsWeightedHomogeneous.prod _ _ _ fun x _ => (hf x).pow (m x) : IsWeightedHomogeneous (wI (N := N) (N' := N') τ)
      (m.prod fun x e => (∑ b : Fin N', C (C (s x.1) * (if h : (x.2.2 : ℕ) < N' then (X (x.1, b, ⟨x.2.2, h⟩) : MvPolynomial (GL3Theta.FrV D N') ℂ) else 0)) *
        X ((x.1, b, x.2.1) : GL3Theta.Idx D N N')) ^ e) (m.sum fun x e => e • wF τ x))
  rw [zero_add] at this
  exact this

end Deg

section Deg2

open MvPolynomial

theorem weight_wI {D : D7} {N N' : ℕ} (τ : D.what₂.Tau) (α : GL3Theta.Idx D N N' →₀ ℕ) :
    Finsupp.weight (wI (N := N) (N' := N') τ) α = ∑ b : Fin N', ∑ a : Fin N, α (τ, b, a) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp [wI]
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [wI, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem difference_polynomial_degree : PolDYDeg := by
  intro D N N' s ν Q hQ α hα τ
  rw [← weight_wI τ α]
  exact polDY_wh (N' := N') s ν Q hQ τ (mem_support_iff.1 hα)

end Deg2

theorem eIdx_pos {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ)
    (hN : RankTie X D j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (b : Fin (D.R.N (j + 1))) (a : Fin (D.R.N j)) :
    eIdx X D pos j hN (pos ⟨v, s⟩, b, a) = ⟨v, (s, Fin.cast hN.1 a, Fin.cast hN.2 b)⟩ := by
  have h := pos.symm_apply_apply ⟨v, s⟩
  dsimp only [eIdx]
  generalize pos.symm (pos ⟨v, s⟩) = q at h ⊢
  subst h
  rfl

theorem blk_mapDomain {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (j : ℕ) (hN : RankTie X D j) (α : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) →₀ ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    ∑ a, ∑ b, (α.mapDomain (eIdx X D pos j hN)) ⟨v, (s, a, b)⟩ = ∑ a', ∑ b', α (pos ⟨v, s⟩, b', a') := by
  refine Fintype.sum_equiv (finCongr hN.1).symm _ _ fun a => ?_
  refine Fintype.sum_equiv (finCongr hN.2).symm _ _ fun b => ?_
  have h := eIdx_pos X D pos j hN v s ((finCongr hN.2).symm b) ((finCongr hN.1).symm a)
  simp only [finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self] at h
  rw [← h, Finsupp.mapDomain_apply (eIdx_injective X D pos j hN)]
  rfl

def CmpVtOf : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p)
    (Y : Pend X) (σ : D.what₂.LL →+* X.G.Kf) (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (j : ℕ),
    Submodule.span D.what₂.LL (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V) = ⊤ →
    Submodule.span X.G.O (cmp j '' (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V)) ≤ X.Int j →
    CmpVt Y u μ cmp j

def CmpVtInst : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (j : ℕ), j ≤ D.R.m →
      CmpVt Y u μ KA.cmp j

end Formalism.L2.KerInert.SecondKernelMoveDegree
