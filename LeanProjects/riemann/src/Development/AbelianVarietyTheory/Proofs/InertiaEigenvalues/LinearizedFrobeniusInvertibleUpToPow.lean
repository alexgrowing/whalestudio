import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteProjectiveModuleElementDescentEqualizerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCoverStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LinFrob

open scoped Matrix

section Algebra

variable {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  {f : A →+* B} {u : M →ₛₗ[f] N}

theorem span_range_eq_top (h : SemiBC u) : Submodule.span B (Set.range u) = ⊤ := by
  obtain ⟨w, -, hw⟩ := h (N ⧸ Submodule.span B (Set.range u)) 0
  have h1 := hw (Submodule.mkQ _) fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨x, rfl⟩)
  have h2 := hw 0 fun _ => rfl
  rw [← Submodule.ker_mkQ (Submodule.span B (Set.range u)), h1, ← h2, LinearMap.ker_zero]

theorem induction_bc (h : SemiBC u) (p : N → Prop) (h0 : ∀ x, p (u x)) (h1 : ∀ y z, p y → p z → p (y + z))
    (h2 : ∀ (b : B) y, p y → p (b • y)) (y : N) : p y := by
  have hy : y ∈ Submodule.span B (Set.range u) := by rw [span_range_eq_top h]; trivial
  induction hy using Submodule.span_induction with
  | mem _ hx => obtain ⟨x, rfl⟩ := hx; exact h0 x
  | zero => rw [← map_zero u]; exact h0 0
  | add y z _ _ hy hz => exact h1 y z hy hz
  | smul b y _ hy => exact h2 b y hy

theorem exists_ext {C P : Type} [CommRing C] [AddCommGroup P] [Module C P] (h : SemiBC u) (τ : B →+* C)
    (w : M →+ P) (hw : ∀ (a : A) x, w (a • x) = τ (f a) • w x) :
    ∃ κ : N →ₛₗ[τ] P, ∀ x, κ (u x) = w x := by
  letI : Module B P := Module.compHom P τ
  obtain ⟨W, hW, -⟩ := h P { toFun := w, map_add' := w.map_add, map_smul' := fun a x => hw a x }
  exact ⟨{ toFun := W, map_add' := W.map_add, map_smul' := fun b y => W.map_smul b y }, hW⟩

theorem semiBC_cancel {C P : Type} [CommRing C] [AddCommGroup P] [Module C P] {τ : B →+* C} {ρ : A →+* C}
    (h : SemiBC u) {w : M →ₛₗ[ρ] P} (hw : SemiBC w) (hρ : ∀ a, ρ a = τ (f a)) (κ : N →ₛₗ[τ] P)
    (hκ : ∀ x, κ (u x) = w x) : SemiBC κ := by
  intro Q _ _ m
  obtain ⟨W, hW, hU⟩ := hw Q
    { toFun := fun x => m (u x)
      map_add' := fun x y => by rw [map_add, map_add]
      map_smul' := fun a x => by rw [u.map_smulₛₗ, m.map_smulₛₗ, hρ] }
  refine ⟨W, fun y => ?_, fun W' hW' => hU W' fun x => by rw [← hκ]; exact hW' (u x)⟩
  refine induction_bc h (fun y => W (κ y) = m y) (fun x => ?_) (fun y z hy hz => ?_) (fun b y hy => ?_) y
  · show W (κ (u x)) = m (u x)
    rw [hκ]; exact hW x
  · show W (κ (y + z)) = m (y + z)
    rw [map_add, map_add, map_add, hy, hz]
  · show W (κ (b • y)) = m (b • y)
    rw [κ.map_smulₛₗ, W.map_smul, m.map_smulₛₗ, hy]

def Tw {Q : Type} [CommRing Q] (_σ : Q →+* Q) (Q' : Type) : Type := Q'

instance Tw.addCommGroup {Q Q' : Type} [CommRing Q] [AddCommGroup Q'] (σ : Q →+* Q) : AddCommGroup (Tw σ Q') :=
  inferInstanceAs (AddCommGroup Q')

instance Tw.module {Q Q' : Type} [CommRing Q] [AddCommGroup Q'] [Module Q Q'] (σ : Q →+* Q) : Module Q (Tw σ Q') :=
  Module.compHom Q' σ

theorem semiBC_frob {Q : Type} [CommRing Q] {d : ℕ} {α β : B →+* Q} (σ : Q →+* Q) (hβ : ∀ b, β b = σ (α b))
    {V : N →ₛₗ[α] (Fin d → Q)} (hV : SemiBC V) (w : N →ₛₗ[β] (Fin d → Q)) (hw : ∀ x i, w x i = σ (V x i)) :
    SemiBC w := by
  intro Q' _ _ m
  obtain ⟨W₁, hW₁, hU₁⟩ := hV (Tw σ Q')
    { toFun := fun x => (m x : Tw σ Q')
      map_add' := fun x y => map_add m x y
      map_smul' := fun b x => by
        show m (b • x) = σ (α b) • m x
        rw [m.map_smulₛₗ, hβ] }
  let e : Fin d → Q' := fun i => (W₁ (Pi.single i 1) : Q')
  have he : ∀ z : Fin d → Q, (W₁ z : Q') = ∑ i, σ (z i) • e i := fun z => by
    conv_lhs => rw [pi_eq_sum_univ' z]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => W₁.map_smul (z i) (Pi.single i 1)
  refine ⟨Fintype.linearCombination Q e, fun x => ?_, fun W' hW' => ?_⟩
  · rw [Fintype.linearCombination_apply]
    have h1 := he (V x)
    have h2 : (W₁ (V x) : Q') = m x := hW₁ x
    rw [h2] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => by rw [hw]
  · let W'' : (Fin d → Q) →ₗ[Q] Tw σ Q' :=
      { toFun := fun z => (W' (fun i => σ (z i)) : Tw σ Q')
        map_add' := fun z z' => by
          show W' (fun i => σ ((z + z') i)) = W' (fun i => σ (z i)) + W' (fun i => σ (z' i))
          rw [← map_add]; congr 1; funext i; simp
        map_smul' := fun c z => by
          show W' (fun i => σ ((c • z) i)) = σ c • W' (fun i => σ (z i))
          rw [← map_smul]; congr 1; funext i; simp }
    have h1 : W'' = W₁ := hU₁ W'' fun x => by
      show W' (fun i => σ (V x i)) = m x
      rw [← hW' x]; congr 1; funext i; rw [hw]
    refine LinearMap.pi_ext fun i c => ?_
    rw [Fintype.linearCombination_apply_single]
    have h2 : Pi.single i c = c • (Pi.single i (1 : Q) : Fin d → Q) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [h2, map_smul]
    congr 1
    have h3 : (W'' (Pi.single i 1) : Q') = W' (Pi.single i 1) := by
      show W' (fun j => σ ((Pi.single i (1 : Q) : Fin d → Q) j)) = W' (Pi.single i 1)
      congr 1; funext j; by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    rw [← h3, h1]

end Algebra

theorem smul_cancel_nzd {R n : Type} [CommRing R] {e : R} (he : e ∈ nonZeroDivisors R) {v w : n → R}
    (h : e • v = e • w) : v = w :=
  funext fun i => (mul_cancel_left_mem_nonZeroDivisors he).1 (congrFun h i)

theorem mul_pow_smul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (c e : R) (a : ℕ) (v : M) :
    (c * e) ^ a • v = e ^ a • c ^ a • v := by
  rw [mul_pow, mul_comm, mul_smul]

theorem ker_gen {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {A A' : Matrix n n R} {E c : R} {a b : ℕ}
    (hA : A' * A = E ^ b • 1) {v : n → R} (h : c ^ a • (A *ᵥ v) = 0) : (c * E) ^ (a + b) • v = 0 := by
  have h2 := congrArg (fun w => A' *ᵥ w) h
  simp only [Matrix.mulVec_zero, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.smul_mulVec,
    Matrix.one_mulVec, smul_smul] at h2
  rw [show (c * E) ^ (a + b) = (c ^ b * E ^ a) * (c ^ a * E ^ b) by ring, mul_smul, h2, smul_zero]

theorem img_gen {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {A A' : Matrix n n R} {E c T : R} {a b : ℕ}
    (hA : A * A' = E ^ b • 1) (hT : T = c * E) (v : n → R) :
    c ^ a • (A *ᵥ ((T ^ (a + b) * (E ^ a * c ^ b)) • (A' *ᵥ v))) = T ^ (2 * (a + b)) • v := by
  subst hT
  simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
  congr 1
  ring

theorem smul_pow_two_mul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {t : R} {n : ℕ} {y : M}
    (h : t ^ n • y = 0) : t ^ (2 * n) • y = 0 := by
  rw [two_mul, pow_add, mul_smul, h, smul_zero]

def piMap {R R' n : Type} [CommRing R] [CommRing R'] (g : R →+* R') : (n → R) →ₛₗ[g] (n → R') where
  toFun z i := g (z i)
  map_add' z z' := funext fun i => map_add g _ _
  map_smul' r z := funext fun i => map_mul g _ _

theorem piMap_apply {R R' n : Type} [CommRing R] [CommRing R'] (g : R →+* R') (z : n → R) :
    piMap g z = fun i => g (z i) := rfl

def piMapMul {R R' n : Type} [CommRing R] [CommRing R'] [Fintype n] (g : R →+* R') (M : Matrix n n R') :
    (n → R) →ₛₗ[g] (n → R') where
  toFun z := M *ᵥ (fun i => g (z i))
  map_add' z z' := by
    rw [← Matrix.mulVec_add]; congr 1; funext i; simp
  map_smul' r z := by
    rw [← Matrix.mulVec_smul]; congr 1; funext i; simp

theorem piMapMul_apply {R R' n : Type} [CommRing R] [CommRing R'] [Fintype n] (g : R →+* R') (M : Matrix n n R')
    (z : n → R) : piMapMul g M z = M *ᵥ (fun i => g (z i)) := rfl

theorem mul_eq_smul_comm {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {X Y : Matrix n n R} {s : R}
    (hs : s ∈ nonZeroDivisors R) (h : X * Y = s • 1) : Y * X = s • 1 := by
  have hd : X.det * Y.det = s ^ Fintype.card n := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one]
  have h1 : X * (Y * X - s • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul,
      sub_self]
  have h2 : X.det • (Y * X - s • 1) = 0 := by
    have h5 : X.adjugate * (X * (Y * X - s • 1)) = X.det • (Y * X - s • 1) := by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [← h5, h1, Matrix.mul_zero]
  rw [← sub_eq_zero]
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h3 ⊢
  have h4 : s ^ Fintype.card n * (Y * X - s • 1) i j = s ^ Fintype.card n * 0 := by
    rw [← hd]; linear_combination Y.det * h3
  exact (mul_cancel_left_mem_nonZeroDivisors (pow_mem hs _)).1 h4

theorem descent_identity {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] (Ap A'p Aq A'q ε φε : Matrix n n R)
    (Ep Eq cp cq : R) (a b : ℕ) (w : n → R) (h1 : A'p * Ap = Ep ^ b • 1) (h2 : Aq * A'q = Eq ^ b • 1)
    (h3 : Ap * A'p = Ep ^ b • 1) (hφ : Eq ^ a • (Ap * φε) = Ep ^ a • (ε * Aq)) (hT : cp * Ep = cq * Eq) :
    ((cp * Ep) ^ (a + b) * (Ep ^ a * cp ^ b)) • (A'p *ᵥ (ε *ᵥ w)) =
      φε *ᵥ (((cq * Eq) ^ (a + b) * (Eq ^ a * cq ^ b)) • (A'q *ᵥ w)) := by
  have e1 : Ap * ((Ep ^ a * cp ^ b) • (A'p * ε)) = (Ep ^ a * cp ^ b * Ep ^ b) • ε := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, h3, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  have e2 : Ap * ((Eq ^ a * cq ^ b) • (φε * A'q)) = (cq ^ b * Ep ^ a * Eq ^ b) • ε := by
    have : Ap * ((Eq ^ a * cq ^ b) • (φε * A'q)) = cq ^ b • ((Eq ^ a • (Ap * φε)) * A'q) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm (Eq ^ a)]
    rw [this, hφ, Matrix.smul_mul, Matrix.mul_assoc, h2, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul,
      mul_assoc]
  have e3 : Ap * ((Ep ^ a * cp ^ b) • (A'p * ε) - (Eq ^ a * cq ^ b) • (φε * A'q)) = 0 := by
    rw [Matrix.mul_sub, e1, e2, ← sub_smul]
    have : Ep ^ a * cp ^ b * Ep ^ b - cq ^ b * Ep ^ a * Eq ^ b = Ep ^ a * ((cp * Ep) ^ b - (cq * Eq) ^ b) := by ring
    rw [this, hT, sub_self, mul_zero, zero_smul]
  have e4 : (cp * Ep) ^ (a + b) • ((Ep ^ a * cp ^ b) • (A'p * ε) - (Eq ^ a * cq ^ b) • (φε * A'q)) = 0 := by
    have : (cp * Ep) ^ (a + b) • ((Ep ^ a * cp ^ b) • (A'p * ε) - (Eq ^ a * cq ^ b) • (φε * A'q)) =
        (cp ^ (a + b) * Ep ^ a) • (A'p * (Ap * ((Ep ^ a * cp ^ b) • (A'p * ε) - (Eq ^ a * cq ^ b) • (φε * A'q)))) := by
      rw [← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.one_mul, smul_smul]; congr 1; ring
    rw [this, e3, Matrix.mul_zero, smul_zero]
  rw [smul_sub, sub_eq_zero, smul_smul, smul_smul] at e4
  have l1 : ((cp * Ep) ^ (a + b) * (Ep ^ a * cp ^ b)) • (A'p *ᵥ (ε *ᵥ w)) =
      (((cp * Ep) ^ (a + b) * (Ep ^ a * cp ^ b)) • (A'p * ε)) *ᵥ w := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have l2 : φε *ᵥ (((cq * Eq) ^ (a + b) * (Eq ^ a * cq ^ b)) • (A'q *ᵥ w)) =
      (((cp * Ep) ^ (a + b) * (Eq ^ a * cq ^ b)) • (φε * A'q)) *ᵥ w := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.smul_mulVec, hT]
  rw [l1, l2, e4]

end GlobalTheory.BSP.LinFrob

namespace GlobalTheory.BSP.LinFrob

open scoped Matrix

theorem map_A_mul {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) {R : Type} [CommRing R]
    (g : bk.S →+* R) : S.A.map g * S.A'.map g = g bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) R) := by
  rw [← Matrix.map_mul, S.A_mul]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem exists_kappa {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d}
    {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N) {P : Type} [AddCommGroup P]
    [Module B.A P] {u : N →ₛₗ[B.D.φ] P} (hu : SemiBC u) {Q : Obj l ↥(OL K)} (a : Hom B Q) (g : Hom bk.prism Q) :
    ∃ κ : P →ₛₗ[a.f] (Fin d → Q.A), SemiBC κ ∧ ∀ x i, κ (u x) i = Q.D.φ (V.v a g x i) := by
  let w : N →ₛₗ[a.f.comp B.D.φ] (Fin d → Q.A) :=
    { toFun := fun x i => Q.D.φ (V.v a g x i)
      map_add' := fun x y => funext fun i => by simp
      map_smul' := fun b x => funext fun i => by
        simp [(V.v a g).map_smulₛₗ, a.f_φ] }
  have hw : SemiBC w := semiBC_frob Q.D.φ (fun b => a.f_φ b) (V.bc a g) w fun _ _ => rfl
  obtain ⟨κ, hκ⟩ := exists_ext hu a.f w.toAddMonoidHom fun b x => w.map_smulₛₗ b x
  exact ⟨κ, semiBC_cancel hu hw (fun _ => rfl) κ hκ, fun x i => by rw [hκ]; rfl⟩

theorem map_smul_mulVec {R R' n : Type} [CommRing R] [CommRing R'] [Fintype n] (g : R →+* R') (s : R)
    (M : Matrix n n R) (v : n → R) :
    (fun i => g ((s • (M *ᵥ v)) i)) = g s • ((M.map g) *ᵥ (fun i => g (v i))) := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.map_mulVec]
  rfl

theorem descent_compat {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d)
    {C D : Obj l ↥(OL K)} (f : Hom bk.prism C) (p q : Hom C D) (c T : C.A) (hT : p.f T = q.f T)
    (hc : c * BK.hf f bk.E = T) (v : Fin d → C.A)
    (hv : (fun i => p.f (v i)) = S.ε (p.comp f) (q.comp f) *ᵥ (fun j => q.f (v j))) :
    (fun i => p.f (((T ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) • ((S.A'.map (BK.hf f)) *ᵥ v)) i)) =
      ((S.ε (p.comp f) (q.comp f)).map D.D.φ) *ᵥ
        (fun i => q.f (((T ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) • ((S.A'.map (BK.hf f)) *ᵥ v)) i)) := by
  subst hc
  have hEp := (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk D (p.comp f)).2
  have hT' : p.f c * BK.hf (p.comp f) bk.E = q.f c * BK.hf (q.comp f) bk.E :=
    (map_mul p.f c _).symm.trans (hT.trans (map_mul q.f c _))
  have key := descent_identity (S.A.map (BK.hf (p.comp f))) (S.A'.map (BK.hf (p.comp f)))
    (S.A.map (BK.hf (q.comp f))) (S.A'.map (BK.hf (q.comp f))) (S.ε (p.comp f) (q.comp f))
    ((S.ε (p.comp f) (q.comp f)).map D.D.φ) _ _ (p.f c) (q.f c) S.a S.b (fun j => q.f (v j))
    (mul_eq_smul_comm (pow_mem hEp S.b) (map_A_mul S _)) (map_A_mul S _) (map_A_mul S _)
    (S.ε_φ (p.comp f) (q.comp f)) hT'
  have hmp : (S.A'.map (BK.hf f)).map p.f = S.A'.map (BK.hf (p.comp f)) := Matrix.map_map
  have hmq : (S.A'.map (BK.hf f)).map q.f = S.A'.map (BK.hf (q.comp f)) := Matrix.map_map
  have hsp : p.f ((c * BK.hf f bk.E) ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) =
      (p.f c * BK.hf (p.comp f) bk.E) ^ (S.a + S.b) * (BK.hf (p.comp f) bk.E ^ S.a * p.f c ^ S.b) := by
    simp only [map_mul, map_pow]; rfl
  have hsq : q.f ((c * BK.hf f bk.E) ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) =
      (q.f c * BK.hf (q.comp f) bk.E) ^ (S.a + S.b) * (BK.hf (q.comp f) bk.E ^ S.a * q.f c ^ S.b) := by
    simp only [map_mul, map_pow]; rfl
  refine ((map_smul_mulVec p.f _ _ _).trans ?_).trans
    (congrArg (Matrix.mulVec ((S.ε (p.comp f) (q.comp f)).map D.D.φ)) (map_smul_mulVec q.f _ _ _)).symm
  exact (congrArg₂ (· • ·) hsp (congrArg₂ Matrix.mulVec hmp hv)).trans (key.trans
    (congrArg (Matrix.mulVec ((S.ε (p.comp f) (q.comp f)).map D.D.φ))
      (congrArg₂ (· • ·) hsq (congrArg₂ Matrix.mulVec hmq rfl))).symm)

theorem coord_relation {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d}
    {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N) {t : B.A}
    {Ψ : N →ₛₗ[B.D.φ] N} (hΨ : IsPsi V t Ψ) {P : Type} [AddCommGroup P] [Module B.A P] {u : N →ₛₗ[B.D.φ] P}
    (hu : SemiBC u) (L : P →ₗ[B.A] N) (hL : ∀ x, L (u x) = Ψ x) {C : Obj l ↥(OL K)} (h : Hom B C)
    (f : Hom bk.prism C) (hEnzd : BK.hf f bk.E ∈ nonZeroDivisors C.A) (κ : P →ₛₗ[h.f] (Fin d → C.A))
    (hκu : ∀ x i, κ (u x) i = C.D.φ (V.v h f x i)) (c : C.A) (hc : c * BK.hf f bk.E = h.f t) (y : P) :
    V.v h f (L y) = c ^ S.a • (S.A.map (BK.hf f)) *ᵥ (κ y) := by
  refine induction_bc hu (fun y => V.v h f (L y) = c ^ S.a • (S.A.map (BK.hf f)) *ᵥ (κ y))
    (fun x => ?_) (fun y z (hy : V.v h f (L y) = _) (hz : V.v h f (L z) = _) => ?_)
    (fun b y (hy : V.v h f (L y) = _) => ?_) y
  · show V.v h f (L (u x)) = c ^ S.a • (S.A.map (BK.hf f)) *ᵥ (κ (u x))
    have h2 : (fun i => C.D.φ (V.v h f x i)) = κ (u x) := funext fun i => (hκu x i).symm
    exact smul_cancel_nzd (pow_mem hEnzd S.a)
      ((congrArg (fun v => BK.hf f bk.E ^ S.a • V.v h f v) (hL x)).trans ((hΨ h f x).trans
        ((congrArg (fun v => h.f t ^ S.a • (S.A.map (BK.hf f)) *ᵥ v) h2).trans
          ((congrArg (fun s => s ^ S.a • (S.A.map (BK.hf f)) *ᵥ (κ (u x))) hc.symm).trans
            (mul_pow_smul _ _ _ _)))))
  · exact ((congrArg (V.v h f) (L.map_add y z)).trans ((V.v h f).map_add _ _)).trans
      ((congrArg₂ (· + ·) hy hz).trans
        ((congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)) *ᵥ v) (κ.map_add y z)).trans
          ((congrArg (c ^ S.a • ·) (Matrix.mulVec_add _ _ _)).trans (smul_add _ _ _))).symm)
  · exact ((congrArg (V.v h f) (L.map_smul b y)).trans ((V.v h f).map_smulₛₗ _ _)).trans
      ((congrArg (h.f b • ·) hy).trans
        ((congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)) *ᵥ v) (κ.map_smulₛₗ b y)).trans
          ((congrArg (c ^ S.a • ·) (Matrix.mulVec_smul _ _ _)).trans (smul_comm _ _ _))).symm)

set_option maxHeartbeats 400000 in

theorem linFrob_inv_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (t : B.A), t ∈ B.I →
    ∀ Ψ : N →ₛₗ[B.D.φ] N, IsPsi V t Ψ → ∀ (P : Type) [AddCommGroup P] [Module B.A P] (u : N →ₛₗ[B.D.φ] P),
    SemiBC u → ∀ L : P →ₗ[B.A] N, (∀ x, L (u x) = Ψ x) →
    ∃ n : ℕ, (∀ y, L y = 0 → t ^ n • y = 0) ∧ ∀ x, ∃ y, L y = t ^ n • x := by
  intro l _ K bk d S B N _ _ V t ht Ψ hΨ P _ _ u hu L hL
  haveI := V.fin
  haveI := V.proj
  obtain ⟨hPf, hPp⟩ := hu.finite_projective
  obtain ⟨C, h, ⟨f⟩, hC⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  obtain ⟨D, p, q, hpo⟩ := hC.stable.po C h
  obtain ⟨hinj, heq⟩ := GlobalTheory.T.prism_cover_injective_and_descent l ↥(OL K) B C h hC
  obtain ⟨hEC, hEnzd⟩ := GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C f
  obtain ⟨hVinj, -⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B C N V h f hC
  obtain ⟨κ, hκbc, hκu⟩ := exists_kappa V hu h f
  obtain ⟨κD, hκDbc, hκDu⟩ := exists_kappa V hu (p.comp h) (p.comp f)
  have htC : h.f t ∈ C.I := h.f_I t ht
  rw [hEC] at htC
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 htC
  have hAC := map_A_mul S (BK.hf f)
  have hA'C := mul_eq_smul_comm (pow_mem hEnzd S.b) hAC
  have hR := coord_relation V hΨ hu L hL h f hEnzd κ hκu c hc

  have hV2 : ∀ x, V.v (p.comp h) (q.comp f) x = V.v (q.comp h) (q.comp f) x := fun x =>
    congrArg (fun a : Hom B D => V.v a (q.comp f) x) hpo.comm
  have e1 : ∀ x, V.v (p.comp h) (p.comp f) x =
      (S.ε (p.comp f) (q.comp f)) *ᵥ (fun j => q.f (V.v h f x j)) := fun x =>
    (V.v_ε (p.comp h) (p.comp f) (q.comp f) x).trans (congrArg (Matrix.mulVec (S.ε (p.comp f) (q.comp f)))
      ((hV2 x).trans (funext fun j => V.v_nat q h f x j)))
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : (Fin d → C.A) →ₛₗ[p.f] (Fin d → D.A), ∀ z, u₁ z = fun i => p.f (z i) :=
    ⟨piMap p.f, piMap_apply p.f⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : (Fin d → C.A) →ₛₗ[q.f] (Fin d → D.A),
      ∀ z, u₂ z = ((S.ε (p.comp f) (q.comp f)).map D.D.φ) *ᵥ (fun i => q.f (z i)) :=
    ⟨piMapMul q.f _, piMapMul_apply q.f _⟩
  have hw1 : ∀ y, κD y = u₁ (κ y) := by
    intro y
    refine induction_bc hu (fun y => κD y = u₁ (κ y)) (fun x => ?_)
      (fun y z (hy : κD y = _) (hz : κD z = _) => ?_) (fun b y (hy : κD y = _) => ?_) y
    · exact (funext fun i => (hκDu x i).trans ((congrArg D.D.φ (V.v_nat p h f x i)).trans
        ((p.f_φ _).symm.trans (congrArg p.f (hκu x i).symm)))).trans (hu₁ _).symm
    · exact (κD.map_add y z).trans ((congrArg₂ (· + ·) hy hz).trans
        ((congrArg u₁ (κ.map_add y z)).trans (u₁.map_add _ _)).symm)
    · exact (κD.map_smulₛₗ b y).trans ((congrArg ((p.comp h).f b • ·) hy).trans
        ((congrArg u₁ (κ.map_smulₛₗ b y)).trans (u₁.map_smulₛₗ _ _)).symm)
  have hw2 : ∀ y, κD y = u₂ (κ y) := by
    intro y
    refine induction_bc hu (fun y => κD y = u₂ (κ y)) (fun x => ?_)
      (fun y z (hy : κD y = _) (hz : κD z = _) => ?_) (fun b y (hy : κD y = _) => ?_) y
    · refine (funext fun i => ?_).trans (hu₂ _).symm
      exact (hκDu x i).trans ((congrArg (fun v => D.D.φ (v i)) (e1 x)).trans
        ((RingHom.map_mulVec D.D.φ _ _ i).trans
          (congrArg (fun v => (((S.ε (p.comp f) (q.comp f)).map D.D.φ) *ᵥ v) i)
            (funext fun j => (q.f_φ _).symm.trans (congrArg q.f (hκu x j).symm)))))
    · exact (κD.map_add y z).trans ((congrArg₂ (· + ·) hy hz).trans
        ((congrArg u₂ (κ.map_add y z)).trans (u₂.map_add _ _)).symm)
    · have hb : (p.comp h).f b = q.f (h.f b) := RingHom.congr_fun (congrArg Hom.f hpo.comm) b
      exact (κD.map_smulₛₗ b y).trans ((congrArg ((p.comp h).f b • ·) hy).trans
        ((congrArg (· • u₂ (κ y)) hb).trans ((congrArg u₂ (κ.map_smulₛₗ b y)).trans (u₂.map_smulₛₗ _ _)).symm))
  haveI := hPf
  haveI := hPp
  obtain ⟨hκinj, hdesc⟩ := GlobalTheory.T.finite_projective_module_element_descent_equalizer B.A C.A D.A h.f p.f q.f (congrArg Hom.f hpo.comm) hinj
    (fun b hb => heq D p q hpo b hb) P (Fin d → C.A) (Fin d → D.A) κ u₁ u₂ κD hκbc hκDbc hw1 hw2
  refine ⟨2 * (S.a + S.b), fun y hy => ?_, fun x => ?_⟩
  ·
    have h0 : t ^ (S.a + S.b) • y = 0 := hκinj (((κ.map_smulₛₗ _ _).trans
      ((congrArg (· • κ y) ((map_pow h.f t _).trans (congrArg (· ^ (S.a + S.b)) hc.symm))).trans
        (ker_gen hA'C ((hR y).symm.trans ((congrArg (V.v h f) hy).trans (map_zero _)))))).trans (map_zero κ).symm)
    exact smul_pow_two_mul h0
  ·
    have hcomp : u₁ ((h.f t ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) •
        ((S.A'.map (BK.hf f)) *ᵥ (V.v h f x))) = u₂ ((h.f t ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) •
        ((S.A'.map (BK.hf f)) *ᵥ (V.v h f x))) :=
      (hu₁ _).trans ((descent_compat S f p q c (h.f t) (RingHom.congr_fun (congrArg Hom.f hpo.comm) t) hc
        (V.v h f x) ((funext fun i => (V.v_nat p h f x i).symm).trans (e1 x))).trans (hu₂ _).symm)
    obtain ⟨y, hy⟩ := hdesc _ hcomp
    refine ⟨y, hVinj ?_⟩
    have e3 : c ^ S.a • (S.A.map (BK.hf f)) *ᵥ ((h.f t ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) •
        ((S.A'.map (BK.hf f)) *ᵥ (V.v h f x))) = h.f t ^ (2 * (S.a + S.b)) • V.v h f x :=
      img_gen hAC hc.symm _
    exact (hR y).trans ((congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)) *ᵥ v) hy).trans
      (e3.trans (((V.v h f).map_smulₛₗ _ _).trans (congrArg (· • V.v h f x) (map_pow h.f t _))).symm))
end GlobalTheory.BSP.LinFrob
