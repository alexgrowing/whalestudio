import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordsAlongOrthonormalRealSubfieldBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthoProductThetaMemThetaSpaceOfLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.RatEquiv

variable {D : D7}

theorem hf_add_left (T : Tor D) {N N' : ℕ} (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem hf_add_right (T : Tor D) {N N' : ℕ} (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]

theorem U_U (T : Tor D) {N N' : ℕ} (x a : VC D N N') (c : ℂ) (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (fun w => c * U D T a G w) z =
      c * Complex.exp ((Real.pi : ℂ) * (Hf D T a x - Hf D T x a) / 2) * U D T (x + a) G z := by
  simp only [U, add_assoc]
  have : ∀ a b e g u : ℂ, a + b = e + g →
      c * (u * Complex.exp a) * Complex.exp b = c * Complex.exp e * (u * Complex.exp g) := by
    intro a b e g u hh
    calc _ = c * u * Complex.exp (a + b) := by simp only [Complex.exp_add]; ring
      _ = _ := by rw [hh]; simp only [Complex.exp_add]; ring
  apply this
  simp only [hf_add_left, hf_add_right]
  ring

theorem term_indep (T : Tor D) {N N' : ℕ} {A B : AddSubgroup (VC D N N')} {G H : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T A) (hH : H ∈ ThSp D T B) (h0 : H ≠ 0) {x a : VC D N N'} (hx : x ∈ B) (haB : a ∈ B)
    (haA : a ∈ A) (z : VC D N N') :
    al D T (x + a) * U D T (x + a) G z = al D T x * U D T x G z := by
  have key : ∀ F : VC D N N' → ℂ, (∀ w, al D T a * U D T a F w = F w) → ∀ w, U D T x F w =
      al D T a * Complex.exp ((Real.pi : ℂ) * (Hf D T a x - Hf D T x a) / 2) * U D T (x + a) F w := by
    intro F hF w
    rw [← U_U]
    congr 1
    exact (funext hF).symm
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h0
  have h1 := hH.2 x hx w
  have h2 := hH.2 _ (B.add_mem hx haB) w
  rw [key H (hH.2 a haB)] at h1
  have h3 : U D T (x + a) H w ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2
    exact hw h2.symm
  have h4 : al D T (x + a) = al D T x * (al D T a *
      Complex.exp ((Real.pi : ℂ) * (Hf D T a x - Hf D T x a) / 2)) :=
    mul_right_cancel₀ h3 (by rw [h2, mul_assoc, h1])
  rw [key G (hG.2 a haA), h4]
  ring

theorem iop_transport (T : Tor D) {N N' : ℕ} (φ : VC D N N' ≃+ VC D N N')
    (hφ : ∀ x y, Hf D T (φ x) (φ y) = Hf D T x y) {A B A' B' : AddSubgroup (VC D N N')}
    (hA : ∀ x, φ x ∈ A' ↔ x ∈ A) (hB : ∀ x, φ x ∈ B' ↔ x ∈ B) {G H : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T A) (hH : H ∈ ThSp D T B) (h0 : H ≠ 0) (z : VC D N N') :
    Iop D T A' B' (fun w => G (φ.symm w)) (φ z) = Iop D T A B G z := by
  let e : B ≃+ B' :=
    { toFun := fun x => ⟨φ x, (hB _).2 x.2⟩
      invFun := fun y => ⟨φ.symm y, (hB _).1 (by simpa using y.2)⟩
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_add' := fun x y => by simp }
  have he : (A.addSubgroupOf B).map e.toAddMonoidHom = A'.addSubgroupOf B' := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨x', hx', h⟩
      have : x' = x := e.injective h
      subst this
      exact (hA _).2 hx'
    · intro h
      exact ⟨x, (hA _).1 h, rfl⟩
  let ε := QuotientAddGroup.congr _ _ e he
  have hi : (A'.addSubgroupOf B').index = (A.addSubgroupOf B).index := (Nat.card_congr ε.toEquiv).symm
  have ht : ∀ x, al D T (φ x) * U D T (φ x) (fun w => G (φ.symm w)) (φ z) = al D T x * U D T x G z := by
    intro x
    simp only [al, U, hφ, ← map_add, AddEquiv.symm_apply_apply]
  unfold Iop
  rw [hi]
  congr 1
  symm
  refine finsum_eq_of_bijective ε ε.bijective fun q => ?_
  obtain ⟨y, hy⟩ := e.surjective (ε q).out
  have h1 : (y : B ⧸ A.addSubgroupOf B) = q := by
    apply ε.injective
    rw [← QuotientAddGroup.out_eq' (ε q), ← hy]
    rfl
  have h2 : -(q.out) + y ∈ A.addSubgroupOf B := by
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq', h1]
  rw [← hy]
  change _ = al D T (φ y) * U D T (φ y) (fun w => G (φ.symm w)) (φ z)
  rw [ht, ← term_indep T hG hH h0 q.out.2 (-(q.out) + y).2 h2]
  simp

theorem emb_unit (τ : D.what₂.Tau) {s : D.host.E} (hs : s * D.host.conj s = 1) :
    embT D τ s * starRingEnd ℂ (embT D τ s) = 1 := by
  rw [← GlobalTheory.OnCoord.embT_conj, ← map_mul, hs, map_one]

def sc (N N' : ℕ) (s : D.host.E) (hs : s * D.host.conj s = 1) : VC D N N' ≃+ VC D N N' where
  toFun z := fun τ i j => embT D τ s * z τ i j
  invFun z := fun τ i j => starRingEnd ℂ (embT D τ s) * z τ i j
  left_inv z := by
    funext τ i j
    linear_combination z τ i j * emb_unit τ hs
  right_inv z := by
    funext τ i j
    linear_combination z τ i j * emb_unit τ hs
  map_add' z w := by
    funext τ i j
    simp only [Pi.add_apply, mul_add]

section Scalar

variable {N N' : ℕ} {s : D.host.E} (hs : s * D.host.conj s = 1) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

theorem sc_apply (z : VC D N N') (τ i j) : sc N N' s hs z τ i j = embT D τ s * z τ i j := rfl

theorem sc_symm_apply (z : VC D N N') (τ i j) :
    (sc N N' s hs).symm z τ i j = starRingEnd ℂ (embT D τ s) * z τ i j := rfl

theorem sc_hf (T : Tor D) (x y : VC D N N') : Hf D T (sc N N' s hs x) (sc N N' s hs y) = Hf D T x y := by
  unfold Hf
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sc_apply, sc_apply, map_mul]
  linear_combination x τ i j * starRingEnd ℂ (y τ i j) * emb_unit τ hs

theorem sc_emb (w : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    sc N N' s hs (w • embV D (tor0 D cc δ) A) = w • embV D (tor0 D cc δ) (s • A) := by
  funext τ i j
  simp only [sc_apply, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  ring

theorem sc_symm_emb (w : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    (sc N N' s hs).symm (w • embV D (tor0 D cc δ) A) = w • embV D (tor0 D cc δ) (D.host.conj s • A) := by
  funext τ i j
  simp only [sc_symm_apply, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    GlobalTheory.OnCoord.embT_conj]
  ring

theorem closure_iff {V : Type} [AddCommGroup V] (φ : V ≃+ V) {S S' : Set V}
    (h1 : ∀ x ∈ S, φ x ∈ AddSubgroup.closure S') (h2 : ∀ y ∈ S', φ.symm y ∈ AddSubgroup.closure S) (x : V) :
    φ x ∈ AddSubgroup.closure S' ↔ x ∈ AddSubgroup.closure S := by
  have a : AddSubgroup.closure S ≤ (AddSubgroup.closure S').comap (φ : V →+ V) :=
    (AddSubgroup.closure_le _).2 h1
  have b : AddSubgroup.closure S' ≤ (AddSubgroup.closure S).comap (φ.symm : V →+ V) :=
    (AddSubgroup.closure_le _).2 h2
  exact ⟨fun h => by simpa using b h, fun h => a h⟩

theorem sc_LaB {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (x : VC D N N') :
    sc N N' s hs x ∈ LaB D (tor0 D cc δ) (fun j => s • b j) ↔ x ∈ LaB D (tor0 D cc δ) b := by
  refine closure_iff _ ?_ ?_ x
  · rintro _ ⟨w, hw, j, rfl⟩
    exact AddSubgroup.subset_closure ⟨w, hw, j, sc_emb hs cc δ w _⟩
  · rintro _ ⟨w, hw, j, rfl⟩
    refine AddSubgroup.subset_closure ⟨w, hw, j, ?_⟩
    rw [sc_symm_emb, smul_smul, mul_comm, hs, one_smul]

theorem yy_smul {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {t u : D.host.E}
    (h : ∀ x ∈ L₁, t • x ∈ L) (h' : ∀ x ∈ L', u • x ∈ L₁') {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ YYl D L L') : (u * t) • A ∈ YYl D L₁ L₁' := by
  have hh : ∀ A ∈ homL D L L', (u * t) • A ∈ homL D L₁ L₁' := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA =>
      refine Submodule.subset_span fun x hx => ?_
      have := h' _ (hA _ (h x hx))
      rwa [Matrix.mulVec_smul, smul_smul, ← Matrix.smul_mulVec] at this
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hA
    exact Submodule.subset_span ⟨a, ha, _, hh A hA, smul_comm _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem sc_La {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {d d' : D.host.E}
    (hd : d * D.host.conj d = 1) (hd' : d' * D.host.conj d' = 1) (hsd : s = d' * D.host.conj d)
    (h : ∀ x, x ∈ L ↔ d • x ∈ L₁) (h' : ∀ x, x ∈ L' ↔ d' • x ∈ L₁') (x : VC D N N') :
    sc N N' s hs x ∈ La D (tor0 D cc δ) L₁ L₁' ↔ x ∈ La D (tor0 D cc δ) L L' := by
  refine closure_iff _ ?_ ?_ x
  · rintro _ ⟨w, hw, A, hA, rfl⟩
    refine AddSubgroup.subset_closure ⟨w, hw, _, ?_, sc_emb hs cc δ w _⟩
    rw [hsd]
    refine yy_smul (fun x hx => (h _).2 ?_) (fun x hx => (h' x).1 hx) hA
    rwa [smul_smul, hd, one_smul]
  · rintro _ ⟨w, hw, A, hA, rfl⟩
    refine AddSubgroup.subset_closure ⟨w, hw, _, ?_, sc_symm_emb hs cc δ w _⟩
    rw [hsd, map_mul, VacMove.conj_conj]
    refine yy_smul (fun x hx => (h x).1 hx) (fun x hx => (h' _).2 ?_) hA
    rwa [smul_smul, hd', one_smul]

include hs in
theorem onB_smul {r : ℕ} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b) :
    OnB D (fun j => s • b j) := by
  refine ⟨fun i j => ?_, ?_⟩
  · rw [← hb.1 i j]
    unfold hYY
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    linear_combination b i a c * D.host.conj (b j a c) * hs
  · rw [eq_top_iff]
    intro y _
    have key : ∀ y ∈ Submodule.span D.host.K (Set.range b),
        s • y ∈ Submodule.span D.host.K (Set.range fun j => s • b j) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem A hA =>
        obtain ⟨j, rfl⟩ := hA
        exact Submodule.subset_span ⟨j, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
    have := key (D.host.conj s • y) (hb.2 ▸ Submodule.mem_top)
    rwa [smul_smul, hs, one_smul] at this

theorem pullB_sc {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ) :
    pullB D (tor0 D cc δ) (fun j => s • b j) g =
      fun z => pullB D (tor0 D cc δ) b g ((sc N N' s hs).symm z) := by
  funext z
  unfold pullB
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  unfold coordB
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [sc_symm_apply, tor0, Matrix.smul_apply, smul_eq_mul, map_mul]
  ring

theorem pull_sc {d d' : D.host.E} (hsd : s = d' * D.host.conj d) (G : VC D N N' → ℂ) (z : VC D N N') :
    pull D (tor0 D cc δ) (d • (1 : Matrix (Fin N) (Fin N) D.host.E)) (d' • (1 : Matrix (Fin N') (Fin N') D.host.E)) G z =
      G ((sc N N' s hs).symm z) := by
  unfold pull
  congr 1
  funext τ
  have e : ∀ (n : ℕ) (t : D.host.E), (t • (1 : Matrix (Fin n) (Fin n) D.host.E)).map ((tor0 D cc δ).emb τ) =
      embT D τ t • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    intro n t
    ext i j
    by_cases h : i = j <;> simp [tor0, h]
  rw [e, e]
  funext i j
  rw [sc_symm_apply, hsd, map_mul, map_mul, GlobalTheory.OnCoord.embT_conj]
  simp
  ring

theorem det_smul (hG : admG1 D) (s : D.host.E) {r : ℕ} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b) :
    D.host.φ₀ (((Matrix.of fun i j => hYY D (s • b j) (b i)).det : D.host.K) : D.host.E) =
      ∏ τ, embT D τ s ^ (N * N') := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG ⊤ 1 N N' r b hb
  let B : Matrix (D.what₂.Tau × Fin N' × Fin N) (Fin r) ℂ := Matrix.of fun k j => embT D k.1 (b j k.2.1 k.2.2)
  let C : Matrix (Fin r) (D.what₂.Tau × Fin N' × Fin N) ℂ :=
    Matrix.of fun j k => starRingEnd ℂ (embT D k.1 (b j k.2.1 k.2.2))
  have hCB : C * B = 1 := by
    ext i j
    have := h2 i j
    simp only [coordB, embV, tor0] at this
    simp only [B, C, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Matrix.one_apply]
    simp only [mul_comm] at this ⊢
    rw [this]
    simp only [eq_comm]
  have hBC : B * C = 1 := by
    ext k l
    have := congrFun (congrFun (congrFun (h1 (coordV D l)) k.1) k.2.1) k.2.2
    obtain ⟨k1, k2, k3⟩ := k
    obtain ⟨l1, l2, l3⟩ := l
    simp only [coordB, embV, tor0, coordV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ite_and, ite_mul, one_mul,
      zero_mul] at this
    simp only [B, C, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Prod.mk.injEq, ite_and]
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
  have hM : (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).mapMatrix
      (Matrix.of fun i j => hYY D (s • b j) (b i)) =
      C * Matrix.diagonal (fun k : D.what₂.Tau × Fin N' × Fin N => embT D k.1 s) * B := by
    ext i j
    have := GlobalTheory.OnCoord.coord_emb hG ⊤ 1 b i (s • b j)
    simp only [coordB, embV, tor0, Matrix.smul_apply, smul_eq_mul, map_mul] at this
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, B, C, Matrix.of_apply, Fintype.sum_prod_type]
    refine Eq.trans this.symm ?_
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  refine ((D.host.φ₀.comp (algebraMap D.host.K D.host.E)).map_det _).trans ?_
  rw [hM, Matrix.det_conj_of_mul_eq_one hCB hBC, Matrix.det_diagonal]
  simp only [Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    mul_comm N N']

end Scalar

theorem parity_mod_two : ∀ a b c d s₁ s₂ x₁ x₂ : ZMod 2,
    a * a + b * c = a → a * b + b * d = b → c * a + d * c = c → c * b + d * d = d →
    ¬ (a * s₁ + c * s₂ = 0 ∧ b * s₁ + d * s₂ = 0) →
    ¬ (s₁ - (a * s₁ + c * s₂) = 0 ∧ s₂ - (b * s₁ + d * s₂) = 0) →
    (((a * x₁ + c * x₂) * x₂ - (b * x₁ + d * x₂) * x₁) + (x₁ * s₂ - x₂ * s₁) = 0 ↔ x₁ = 0 ∧ x₂ = 0) := by
  decide

theorem exists_orthonormal_basis_family (Λ : AddSubgroup ℂ) (ω t : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ ω (U1 Λ t G) z =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (gl3FieldFirst Λ ω (2 * t) : ℂ)) * U1 Λ t (U1 Λ ω G) z := by
  have h : ((gl3FieldFirst Λ ω (2 * t) : ℝ) : ℂ) * Complex.I =
      (ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ) := by
    have h2 := Complex.sub_conj (ω * (starRingEnd ℂ) t)
    rw [map_mul, Complex.conj_conj, mul_comm ((starRingEnd ℂ) ω) t] at h2
    have h3 : (ω * (starRingEnd ℂ) (2 * t)).im = 2 * (ω * (starRingEnd ℂ) t).im := by
      simp; ring
    rw [h2, gl3FieldFirst, h3]
    push_cast
    ring
  have h' : -(Real.pi : ℂ) * Complex.I * (gl3FieldFirst Λ ω (2 * t) : ℂ) =
      -(Real.pi : ℂ) * ((ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ)) := by
    rw [← h]; ring
  rw [h']
  simp only [U1]
  rw [add_right_comm z t ω, mul_assoc (G _), mul_assoc (G _), ← Complex.exp_add, ← Complex.exp_add,
    mul_left_comm _ (G _), ← Complex.exp_add]
  congr 2
  ring

theorem even_im_hermitian_sub (Λ : AddSubgroup ℂ) (w₁ w₂ : ℂ) (hi : LinearIndependent ℝ ![w₁, w₂])
    (hΛ : Λ = AddSubgroup.closure {w₁, w₂})
    (hsd : ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, gl3FieldFirst Λ z w = m)
    (θ : ℂ) (N : ℤ) (hN : Even N) (hθ : θ * θ = θ - N) (hst : ∀ w ∈ Λ, θ * w ∈ Λ)
    (t : ℂ) (ht : 2 * t ∈ Λ) (h1 : θ * t ∉ Λ) (h2 : (1 - θ) * t ∉ Λ) (ω : ℂ) (hω : ω ∈ Λ) :
    ∃ m n : ℤ, gl3FieldFirst Λ (θ * ω) ω = m ∧ gl3FieldFirst Λ ω (2 * t) = n ∧ (Even (m + n) ↔ ω / 2 ∈ Λ) := by
  have mem : ∀ z, z ∈ Λ ↔ ∃ x y : ℤ, z = x * w₁ + y * w₂ := by
    intro z
    rw [hΛ, AddSubgroup.mem_closure_pair]
    simp only [zsmul_eq_mul, eq_comm]
  have uniq : ∀ x y : ℤ, (x : ℂ) * w₁ + y * w₂ = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    have := LinearIndependent.pair_iff.1 hi (x : ℝ) (y : ℝ) (by simpa using h)
    exact_mod_cast this
  have half : ∀ x y : ℤ, ((x : ℂ) * w₁ + y * w₂) / 2 ∈ Λ ↔ (x : ZMod 2) = 0 ∧ (y : ZMod 2) = 0 := by
    intro x y
    rw [mem, ZMod.intCast_eq_zero_iff_even, ZMod.intCast_eq_zero_iff_even]
    constructor
    · rintro ⟨u, v, h⟩
      obtain ⟨e1, e2⟩ := uniq (x - 2 * u) (y - 2 * v) (by push_cast; linear_combination 2 * h)
      exact ⟨⟨u, by omega⟩, ⟨v, by omega⟩⟩
    · rintro ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
      exact ⟨u, v, by push_cast; ring⟩
  have hw₁ : w₁ ∈ Λ := (mem _).2 ⟨1, 0, by simp⟩
  have hw₂ : w₂ ∈ Λ := (mem _).2 ⟨0, 1, by simp⟩
  obtain ⟨e, he⟩ := (hsd w₁).1 hw₁ w₂ hw₂
  have EFr : ∀ x y u v : ℝ, gl3FieldFirst Λ (x * w₁ + y * w₂) (u * w₁ + v * w₂) = (x * v - y * u) * e := by
    intro x y u v
    rw [← he]
    simp only [gl3FieldFirst]
    simp
    ring
  have EFi : ∀ x y u v : ℤ, gl3FieldFirst Λ (x * w₁ + y * w₂) (u * w₁ + v * w₂) = (((x * v - y * u) * e : ℤ) : ℝ) := by
    intro x y u v
    have := EFr x y u v
    push_cast at this ⊢
    exact this
  have hodd : (e : ZMod 2) = 1 := by
    rw [ZMod.intCast_eq_one_iff_odd, ← Int.not_even_iff_odd]
    rintro ⟨k, hk⟩
    have : (((1 : ℤ) : ℂ) * w₁ + ((0 : ℤ) : ℂ) * w₂) / 2 ∈ Λ := by
      rw [hsd]
      intro w hw
      obtain ⟨u, v, rfl⟩ := (mem _).1 hw
      refine ⟨v * k, ?_⟩
      have := EFr (1 / 2) 0 u v
      rw [hk] at this
      push_cast at this ⊢
      rw [show (1 * w₁ + 0 * w₂) / 2 = 1 / 2 * w₁ + 0 * w₂ by ring, this]
      ring
    rw [half] at this
    exact absurd this.1 (by decide)
  obtain ⟨a, b, hab⟩ := (mem _).1 (hst _ hw₁)
  obtain ⟨c, d, hcd⟩ := (mem _).1 (hst _ hw₂)
  obtain ⟨s₁, s₂, hs⟩ := (mem _).1 ht
  obtain ⟨x₁, x₂, rfl⟩ := (mem _).1 hω
  have mul : ∀ x y : ℤ, θ * ((x : ℂ) * w₁ + y * w₂) =
      ((a * x + c * y : ℤ) : ℂ) * w₁ + ((b * x + d * y : ℤ) : ℂ) * w₂ := by
    intro x y
    push_cast
    linear_combination (x : ℂ) * hab + (y : ℂ) * hcd
  obtain ⟨r1, r2⟩ := uniq (a * a + b * c - a + N) (a * b + b * d - b) (by
    push_cast
    linear_combination w₁ * hθ - (θ + a - 1) * hab - (b : ℂ) * hcd)
  obtain ⟨r3, r4⟩ := uniq (c * a + d * c - c) (c * b + d * d - d + N) (by
    push_cast
    linear_combination w₂ * hθ - (θ + d - 1) * hcd - (c : ℂ) * hab)
  have hN2 : (N : ZMod 2) = 0 := ZMod.intCast_eq_zero_iff_even.2 hN
  have q1 := congrArg (Int.cast : ℤ → ZMod 2) r1
  have q2 := congrArg (Int.cast : ℤ → ZMod 2) r2
  have q3 := congrArg (Int.cast : ℤ → ZMod 2) r3
  have q4 := congrArg (Int.cast : ℤ → ZMod 2) r4
  push_cast at q1 q2 q3 q4
  have e1 : θ * t = (((a * s₁ + c * s₂ : ℤ) : ℂ) * w₁ + ((b * s₁ + d * s₂ : ℤ) : ℂ) * w₂) / 2 := by
    rw [← mul, ← hs]; ring
  have e2 : (1 - θ) * t = (((s₁ - (a * s₁ + c * s₂) : ℤ) : ℂ) * w₁ + ((s₂ - (b * s₁ + d * s₂) : ℤ) : ℂ) * w₂) / 2 := by
    push_cast at e1 ⊢
    linear_combination (1 / 2) * hs - e1
  rw [e1, half] at h1
  rw [e2, half] at h2
  push_cast at h1 h2
  refine ⟨_, _, by rw [mul, EFi], by rw [hs, EFi], ?_⟩
  rw [half, ← ZMod.intCast_eq_zero_iff_even]
  push_cast
  rw [hodd, mul_one, mul_one]
  exact parity_mod_two _ _ _ _ _ _ _ _ (by linear_combination q1 - hN2) (by linear_combination q2)
    (by linear_combination q3) (by linear_combination q4 - hN2) h1 h2

theorem theta_signed_translation : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) ∧ ∀ ω ∈ lamOf D cc δ, ∃ m : ℤ, q1 D (lamOf D cc δ) ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 (lamOf D cc δ) ω (GL3Theta.th0 (lamOf D cc δ) t0) z = GL3Theta.th0 (lamOf D cc δ) t0 z := by
  intro D hG cc δ hC t0 ht
  have hb : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamOf D cc δ = AddSubgroup.closure {w₁, w₂} := by
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_periodPair_idealCurveLattice D cc δ hC
    refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
    ext z
    rw [hL, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
    simp only [zsmul_eq_mul]
  have hst : ∀ a : 𝓞 D.host.K, ∀ w ∈ lamOf D cc δ, D.host.φ₀ ((a : D.host.K) : D.host.E) * w ∈ lamOf D cc δ :=
    fun a w hw => GlobalTheory.ThetaLine.lam_mul cc δ a hw
  set Λ := lamOf D cc δ
  obtain ⟨⟨hdiff, -, -, hlaw⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hb
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hb
  obtain ⟨-, hsd⟩ := GlobalTheory.PlaneLattice.area_pos_and_selfDual L Λ hL
  obtain ⟨w₁, w₂, hi, hΛ⟩ := hb
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d = 16 * k + 7 := ⟨D.host.d / 16, by omega⟩
  have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) * (Real.sqrt D.host.d : ℝ) = 16 * (k : ℂ) + 7 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), hk]
    push_cast; ring
  refine ⟨?_, fun ω hω => ?_⟩
  · unfold GL3Theta.th0 U1
    refine Differentiable.div_const (Differentiable.mul (hdiff.comp (differentiable_id.add_const _)) ?_) _
    fun_prop
  obtain ⟨m, n, hm, hn, hpar⟩ := even_im_hermitian_sub Λ w₁ w₂ hi hΛ hsd (w0 D) (4 * k + 2) ⟨2 * k + 1, by ring⟩
    (by
      unfold w0
      push_cast
      linear_combination (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_mul_I - (1 / 4) * hsq)
    (fun w hw => ha ▸ hst a w hw) t0 ht.1 ht.2.1
    (by
      have := ht.2.2
      convert this using 3
      unfold w0; ring) ω hω
  refine ⟨m, ?_, fun z => ?_⟩
  · rw [← hm, q1, gl3FieldFirst, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, w0]
    rw [mul_comm ((1 + _) / 2 : ℂ), Complex.im_ofReal_mul]
    simp
    ring
  · have e1 : U1 Λ ω (GL3Theta.th0 Λ t0) z = U1 Λ ω (U1 Λ t0 (sgStar Λ)) z / U1 Λ t0 (sgStar Λ) 0 := by
      conv_lhs => rw [U1]
      conv_rhs => rw [U1]
      simp only [GL3Theta.th0]
      ring
    have e2 : U1 Λ t0 (U1 Λ ω (sgStar Λ)) z = (if ω / 2 ∈ Λ then 1 else -1) * U1 Λ t0 (sgStar Λ) z := by
      conv_lhs => rw [U1]
      rw [hlaw ω hω, mul_assoc]
      rfl
    have e3 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)) = (-1) ^ n := by
      rw [show -(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ) = (n : ℂ) * (-(Real.pi * Complex.I)) by push_cast; ring,
        Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    have e4 : (-1 : ℂ) ^ m * (-1) ^ n * (if ω / 2 ∈ Λ then 1 else -1) = 1 := by
      rw [← zpow_add₀ (by norm_num)]
      split_ifs with h
      · rw [(hpar.2 h).neg_one_zpow]; simp
      · rw [(Int.not_even_iff_odd.1 (mt hpar.1 h)).neg_one_zpow]; simp
    rw [e1, exists_orthonormal_basis_family, hn, e2, e3]
    simp only [GL3Theta.th0]
    linear_combination (U1 Λ t0 (sgStar Λ) z / U1 Λ t0 (sgStar Λ) 0) * e4

theorem Iop_smul (T : Tor D) {N N' : ℕ} (A₁ A₂ : AddSubgroup (VC D N N')) (c : ℂ) (G : VC D N N' → ℂ) :
    Iop D T A₁ A₂ (fun z => c * G z) = fun z => c * Iop D T A₁ A₂ G z := by
  funext z
  simp only [Iop, U]
  rw [mul_left_comm c]
  congr 1
  rw [mul_finsum]
  congr 1; funext q; ring

theorem vac_sc (hG : admG1 D) (hU : IntertwinerUnitary D) (hM : GaussSumTripleConstant D) (hL : LemmaCGaussConstant D) {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ}
    (hC : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {N N' : ℕ} {e0 : VC D N N' → ℂ} (h0 : e0 ≠ 0)
    (hE : ThetaVectorUpToUnits D (tor0 D cc δ) t0 (stdL D N) (stdL D N') e0) (hK0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N'))
    {s : D.host.E} (hs : s * D.host.conj s = 1) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A)
    (hsA : ∀ x, sc N N' s hs x ∈ A ↔ x ∈ La0 D (tor0 D cc δ) N N') :
    ∃ c ζ : ℂ, IsOfFinOrder ζ ∧ c ^ 2 = ζ * ∏ τ, embT D τ s ^ (N * N') ∧ ∀ z,
      e0 ((sc N N' s hs).symm z) = c * Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') A e0 z := by
  obtain ⟨b, κ, hb, -, he⟩ := hE
  have hb' := onB_smul hs hb
  obtain ⟨hd, hth⟩ := theta_signed_translation D hG cc δ hC t0 ht
  have hP : pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ ThSp D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) := by
    obtain ⟨-, -, hpar, hmem, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' _ b hb
    exact GlobalTheory.ProdTheta.pullB_mem_ThSp D _ N N' _ b _ hpar hmem hd hth
  have hKb : KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) := Or.inl ⟨_, b, hb, rfl⟩
  have hKb' : KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) fun j => s • b j) := Or.inl ⟨_, _, hb', rfl⟩
  obtain ⟨c, ζ, m, hm, hζ, hc, hpull⟩ := hL cc δ hC t0 ht N N' _ b _ hb hb'
  rw [det_smul hG s hb] at hc
  obtain ⟨μ, hμ, hI⟩ := hM cc δ hC N N' _ _ _ hKb hKb' hA _ hP
  obtain ⟨μ', hμ', hI'⟩ := hM cc δ hC N N' _ _ _ hKb hK0 hA _ hP
  change e0 = fun z => κ * Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (La0 D (tor0 D cc δ) N N')
    (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) z at he
  have hH := (hU cc δ hC N N' _ _ hKb hK0 _ hP).2.1
  have hH0 : Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (La0 D (tor0 D cc δ) N N')
      (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) ≠ 0 := by
    intro h
    apply h0
    rw [he, h]
    funext z
    simp
  have f1 : IsOfFinOrder μ := isOfFinOrder_iff_pow_eq_one.2 ⟨8, by norm_num, hμ⟩
  have f2 : IsOfFinOrder μ' := isOfFinOrder_iff_pow_eq_one.2 ⟨8, by norm_num, hμ'⟩
  have f3 : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, hζ⟩
  refine ⟨c * μ * μ' ^ 7, ζ * (μ * μ' ^ 7) ^ 2, f3.mul (f1.mul f2.pow).pow, by linear_combination (μ * μ' ^ 7) ^ 2 * hc,
    fun z => ?_⟩
  have h1 := iop_transport (tor0 D cc δ) (sc N N' s hs) (sc_hf hs _) (sc_LaB hs cc δ b) hsA hP hH hH0
    ((sc N N' s hs).symm z)
  rw [← pullB_sc, AddEquiv.apply_symm_apply, hpull, Iop_smul, hI] at h1
  rw [he, Iop_smul, hI']
  beta_reduce at h1 ⊢
  rw [← h1]
  linear_combination (-(c * μ * κ * Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) A
    (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) z)) * hμ'

theorem exists_prime_mem {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsPrime) :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ q : ℕ, q.Prime ∧ (q : R) ∈ P := by
  intro n
  induction n using induction_on_primes with
  | zero => exact fun h => absurd rfl h
  | one => exact fun _ h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) hP.ne_top
  | prime_mul p a hp ih =>
    intro h0 h
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, h⟩
    · exact ih (right_ne_zero_of_mul h0) h

theorem inert_int {d : D.host.E} (hd : d * D.host.conj d = 1) {c : AE D} (hc : c ∈ OhE D)
    (hz : ∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q c) : c * inc D d ∈ OhE D := by
  let J : Ideal (𝓞 D.host.E) :=
    { carrier := {a | inc D (a : D.host.E) * (c * inc D d) ∈ OhE D}
      add_mem' := fun {a b} ha hb => by
        simpa [add_mul] using add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        simpa [mul_assoc] using mul_mem (VacMove.inc_int D a) hb }
  have hJ : ∀ a : 𝓞 D.host.E, a ∈ J ↔ inc D (a : D.host.E) * (c * inc D d) ∈ OhE D := fun a => Iff.rfl
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal J (fun h => hne (by
    simpa using (hJ 1).1 (h ▸ Submodule.mem_top)))
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  obtain ⟨q, hq, hqP⟩ := exists_prime_mem hP.isPrime _ (Ideal.absNorm_eq_zero_iff.not.2 hP0) (Ideal.absNorm_mem P)
  by_cases hi : InertQ D q
  · have hPP := hi P hP.isPrime hP0 hqP
    have key : ∀ t n : 𝓞 D.host.E, d * (t : D.host.E) = n → t ∈ P := by
      intro t n h
      refine hle ((hJ t).2 ?_)
      rw [mul_left_comm, ← map_mul, mul_comm _ d, h]
      exact mul_mem hc (VacMove.inc_int D n)
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP.isPrime, hP0⟩
    rcases le_total (v.valuation D.host.E d) 1 with h | h
    · obtain ⟨n, t, e⟩ := v.exists_primeCompl_mul_eq_of_integer d h
      exact t.2 (key t n e)
    · have h' : v.valuation D.host.E (D.host.conj d) ≤ 1 := by
        have := congrArg (v.valuation D.host.E) hd
        rw [map_mul, map_one] at this
        calc _ = 1 * v.valuation D.host.E (D.host.conj d) := (one_mul _).symm
          _ ≤ _ := mul_le_mul_left h _
          _ = 1 := this
      obtain ⟨n, t, e⟩ := v.exists_primeCompl_mul_eq_of_integer _ h'
      have e' := congrArg D.host.conj e
      rw [map_mul, VacMove.conj_conj] at e'
      have := key (D.host.conj • (t : 𝓞 D.host.E)) (D.host.conj • n) e'
      rw [← hPP, Ideal.smul_mem_pointwise_smul_iff] at this
      exact t.2 this
  · obtain ⟨m, -, hmq, s, hs, h⟩ := VacMove.zeroAt_mul D hq (hz q hq hi) (inc D d) 0
    have hm : (m : 𝓞 D.host.E) ∈ P := hle ((hJ _).2 (by simpa [h] using hs))
    obtain ⟨a, b, hab⟩ : IsCoprime (m : 𝓞 D.host.E) (q : 𝓞 D.host.E) := Nat.Coprime.cast hmq
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (P.mul_mem_left a hm) (P.mul_mem_left b hqP)))

def part {R : Type} [CommRing R] {e a b : R} (he : e * e = e) (hab : a * b = 1) : Rˣ :=
  ⟨(1 - e) + e * a, (1 - e) + e * b, by linear_combination (1 - a - b + a * b) * he + e * hab,
    by linear_combination (1 - a - b + a * b) * he + e * hab⟩

theorem split_char {y : D.host.E} (hy : y ≠ 0) (u : (AE D)ˣ) (hu : (u : AE D) = inc D (y / D.host.conj y)) :
    ∃ z x : (AE D)ˣ, SplitComp D u z ∧ x = z * sgU D x ∧ ∀ (n : ℕ) (χ : HeckeU D n),
      ((χ.f x : ℂˣ) : ℂ) ^ 2 * ∏ τ, embT D τ (y / D.host.conj y) ^ (χ.n τ) = 1 := by
  obtain ⟨ε, hε, h1, h2, h3⟩ := VacMove.exists_half_idem D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  obtain ⟨e, he⟩ : ∃ e, e = ε + sgA D ε := ⟨_, rfl⟩
  rw [← he] at h3
  have hee : e * e = e := by rw [he]; linear_combination h1 + h1' + 2 * h2
  have hee' : (1 - e) * (1 - e) = 1 - e := by linear_combination hee
  have hse : sgA D e = e := by rw [he, map_add, VacMove.sgA_sgA, add_comm]
  have heO : e ∈ OhE D := he ▸ add_mem hε (VacMove.sgA_mem D hε)
  have hy' : D.host.conj y ≠ 0 := by simpa using hy
  set d := y / D.host.conj y with hdd
  have hd : d * D.host.conj d = 1 := by
    rw [hdd, map_div₀, VacMove.conj_conj]; field_simp
  have hd' : D.host.conj d * D.host.conj (D.host.conj d) = 1 := by rw [← map_mul, hd, map_one]
  have hdA : inc D d * inc D (D.host.conj d) = 1 := by rw [← map_mul, hd, map_one]
  have hyA : inc D y * inc D y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hy, map_one]
  have hdy : inc D d * inc D (D.host.conj y) = inc D y := by rw [← map_mul, hdd, div_mul_cancel₀ _ hy']
  refine ⟨part hee hdA, part hee hyA, fun q hq => ⟨fun hi => ?_, fun hi => ?_⟩, ?_, fun n χ => ?_⟩
  · convert VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) (inc D d - 1) using 1
    simp only [part]; ring
  · convert VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) (1 - inc D d) using 1
    simp only [part, hu]; ring
  · ext
    change (1 - e) + e * inc D y = ((1 - e) + e * inc D d) * sgA D ((1 - e) + e * inc D y)
    rw [map_add, map_mul, map_sub, map_one, hse, PtsMem.sgA_inc]
    linear_combination (-(1 - inc D d - inc D (D.host.conj y) + inc D d * inc D (D.host.conj y))) * hee - e * hdy
  · have hk : χ.f (part hee' hdA) = 1 := by
      have hz : ∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q (1 - e) := fun q hq => (h3 q hq).2
      have h1e : 1 - e ∈ OhE D := sub_mem (one_mem _) heO
      refine χ.unr _ ⟨add_mem (sub_mem (one_mem _) h1e) (inert_int hd h1e hz),
        add_mem (sub_mem (one_mem _) h1e) (inert_int hd' h1e hz)⟩ fun q hq hi => ?_
      convert VacMove.zeroAt_mul D hq (hz q hq hi) (inc D d - 1) using 1
      simp only [part]; ring
    have hw : part hee' hyA = part hee' hdA * sgU D (part hee' hyA) := by
      ext
      change (1 - (1 - e)) + (1 - e) * inc D y =
        ((1 - (1 - e)) + (1 - e) * inc D d) * sgA D ((1 - (1 - e)) + (1 - e) * inc D y)
      simp only [map_add, map_mul, map_sub, map_one, hse, PtsMem.sgA_inc]
      linear_combination (-(1 - inc D d - inc D (D.host.conj y) + inc D d * inc D (D.host.conj y))) * hee' -
        (1 - e) * hdy
    have hw2 : χ.f (part hee' hyA) ^ 2 = 1 := by
      have a := χ.norm (part hee' hyA)
      have b := congrArg χ.f hw
      rw [map_mul, hk, one_mul] at b
      rw [map_mul, ← b] at a
      rw [pow_two, a]
    have hxw : Units.map (inc D).toMonoidHom (Units.mk0 y hy) = part hee hyA * part hee' hyA := by
      ext
      change inc D y = ((1 - e) + e * inc D y) * ((1 - (1 - e)) + (1 - e) * inc D y)
      linear_combination (1 - inc D y) ^ 2 * hee
    have ha := congrArg (· ^ 2) (χ.aut (Units.mk0 y hy))
    simp only [hxw, map_mul, mul_pow, one_pow, Units.val_mul, Units.val_mk0] at ha
    rw [← Units.val_pow_eq_pow_val (χ.f (part hee' hyA)), hw2, Units.val_one, mul_one, ← Finset.prod_pow] at ha
    rw [← ha]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    have h0 : embT D τ y ≠ 0 := by simpa using hy
    rw [hdd, map_div₀, GlobalTheory.OnCoord.embT_conj, div_pow, ← Complex.mul_conj', pow_two, mul_div_mul_left _ _ h0]

theorem deriv_prod_one {ι : Type} (s : Finset ι) (f : ι → ℂ → ℂ) (a : ι → ℂ)
    (h : ∀ i, HasDerivAt (f i) (a i) 0) (h1 : ∀ i, f i 0 = 1) :
    HasDerivAt (fun t => ∏ i ∈ s, f i t) (∑ i ∈ s, a i) 0 := by
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const (0 : ℂ) (1 : ℂ)
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact ((h i).fun_mul ih).congr_deriv (by simp [h1])

theorem sum_eq_zero_of_prod {ι : Type} [Fintype ι] (a b : ι → ℂ) (n : ι → ℤ)
    (h : ∀ᶠ k : ℕ in Filter.atTop, ∏ i, ((1 + ((k : ℂ))⁻¹ * a i) / (1 + ((k : ℂ))⁻¹ * b i)) ^ n i = 1) :
    ∑ i, (n i : ℂ) * (a i - b i) = 0 := by
  have hd := deriv_prod_one Finset.univ (fun i t => ((1 + t * a i) / (1 + t * b i)) ^ n i)
    (fun i => (n i : ℂ) * (a i - b i)) (fun i => by
      have h1 : HasDerivAt (fun t : ℂ => (1 + t * a i) / (1 + t * b i)) (a i - b i) 0 := by
        exact ((((hasDerivAt_id (0 : ℂ)).mul_const (a i)).const_add 1).fun_div
          (((hasDerivAt_id (0 : ℂ)).mul_const (b i)).const_add 1) (by simp)).congr_deriv (by simp)
      have h2 := hasDerivAt_zpow (n i) ((fun t : ℂ => (1 + t * a i) / (1 + t * b i)) 0) (Or.inl (by simp))
      have h3 := HasDerivAt.comp (0 : ℂ) h2 h1
      exact h3.congr_deriv (by simp)) (fun i => by simp)
  have ht : Filter.Tendsto (fun k : ℕ => ((k : ℂ))⁻¹) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    simpa using hk.ne'
  have h3 := hd.tendsto_slope_zero.comp ht
  refine tendsto_nhds_unique h3 (tendsto_const_nhds.congr' ?_)
  filter_upwards [h] with k hk
  simp [hk]

theorem exp_eq_zero (hG : admG1 D) (m : D.what₂.Tau → ℤ)
    (h : ∀ y : D.host.E, y ≠ 0 → IsOfFinOrder (∏ τ, embT D τ (y / D.host.conj y) ^ m τ)) (τ : D.what₂.Tau) :
    m τ = 0 := by
  set w := NumberField.Units.torsionOrder D.host.E
  have hw : w ≠ 0 := NumberField.Units.torsionOrder_ne_zero _
  have h1 : ∀ y : D.host.E, y ≠ 0 → ∏ τ, embT D τ (y / D.host.conj y) ^ (m τ * w) = 1 := by
    intro y hy
    have e : ∏ τ, embT D τ (y / D.host.conj y) ^ m τ = D.host.φ₀
        (∏ τ, D.host.sigmaOf (D.eTau τ : D.R.GG) (y / D.host.conj y) ^ m τ) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀]; rfl
    have h2 := h y hy
    simp only [zpow_mul, zpow_natCast, Finset.prod_pow]
    rw [e] at h2 ⊢
    generalize (∏ τ, D.host.sigmaOf (D.eTau τ : D.R.GG) (y / D.host.conj y) ^ m τ) = x at h2 ⊢
    obtain ⟨k, hk, hx⟩ := isOfFinOrder_iff_pow_eq_one.1 h2
    have hx' : x ^ k = 1 := D.host.φ₀.injective (by rw [map_pow, hx, map_one])
    have hint : IsIntegral ℤ x := IsIntegral.of_pow hk (hx' ▸ isIntegral_one)
    have hx'' : (⟨x, hint⟩ : 𝓞 D.host.E) ^ k = 1 := Subtype.ext hx'
    let u : (𝓞 D.host.E)ˣ := Units.ofPowEqOne _ k hx'' hk.ne'
    have hu : u ∈ NumberField.Units.torsion D.host.E :=
      (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, Units.ext hx''⟩)
    rw [← NumberField.Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hu
    have hu' := congrArg (fun v : (𝓞 D.host.E)ˣ => ((v : 𝓞 D.host.E) : D.host.E)) hu
    have : x ^ w = 1 := hu'
    rw [← map_pow, this, map_one]
  have h2 : ∀ y : D.host.E, ∑ τ, embT D τ (y - D.host.conj y) * (m τ : ℂ) = 0 := by
    intro y
    have := sum_eq_zero_of_prod (fun τ => embT D τ y) (fun τ => embT D τ (D.host.conj y)) (fun τ => m τ * w) (by
      obtain ⟨k0, hk0⟩ := exists_nat_gt ‖D.host.φ₀ y‖
      filter_upwards [Filter.eventually_ge_atTop k0] with k hk
      have hk1 : ‖D.host.φ₀ y‖ < k := hk0.trans_le (by exact_mod_cast hk)
      have hk2 : (k : D.host.E) ≠ 0 := by
        have : (0 : ℝ) < k := (norm_nonneg _).trans_lt hk1
        exact_mod_cast this.ne'
      have hne : 1 + (k : D.host.E)⁻¹ * y ≠ 0 := by
        intro h0
        have : y = -k := by field_simp at h0; linear_combination h0
        simp [this] at hk1
      simpa using h1 _ hne)
    apply mul_left_cancel₀ (show (w : ℂ) ≠ 0 by exact_mod_cast hw)
    rw [mul_zero, ← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    push_cast [map_sub]
    ring
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  let s : D.host.K := ⟨D.host.sqrtMinusD, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hs : ∀ τ, embT D τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := fun τ => hG.1 τ s
  have hs2 : D.host.φ₀ D.host.sqrtMinusD ^ 2 = -(D.host.d : ℂ) := by rw [← map_pow, hb]; simp
  have hs0 : D.host.φ₀ D.host.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0] at hs2
    have : D.host.d = 0 := by simpa using hs2
    omega
  have hc : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    have e := congrArg D.host.conj hb
    rw [map_pow, map_neg, map_natCast, ← hb] at e
    refine (sq_eq_sq_iff_eq_or_eq_neg.1 e).resolve_left fun h0 => ?_
    have e2 := GlobalTheory.OnCoord.embT_conj τ D.host.sqrtMinusD
    rw [h0, hs] at e2
    have e3 := Complex.mul_conj' (D.host.φ₀ D.host.sqrtMinusD)
    rw [← e2, ← pow_two, hs2] at e3
    have e4 : -(D.host.d : ℝ) = ‖D.host.φ₀ D.host.sqrtMinusD‖ ^ 2 := by exact_mod_cast e3
    have : (0 : ℝ) < D.host.d := by exact_mod_cast hd
    nlinarith [sq_nonneg ‖D.host.φ₀ D.host.sqrtMinusD‖]
  have := GlobalTheory.OnCoord.indep (fun τ => (m τ : ℂ)) (fun x => by
    have a := h2 x
    have b := h2 (x * D.host.sqrtMinusD)
    simp only [map_sub, map_mul, hc, map_neg, hs] at a b
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hs0)
    have c : D.host.φ₀ D.host.sqrtMinusD * _ + _ = _ := congrArg₂ (fun u v => D.host.φ₀ D.host.sqrtMinusD * u + v) a b
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, mul_zero, add_zero] at c
    rw [mul_zero, ← c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => by ring) τ
  exact_mod_cast this

theorem scalar_unitary (N : ℕ) {d : D.host.E} (hd : d * D.host.conj d = 1) :
    (d • (1 : Matrix (Fin N) (Fin N) D.host.E)) *
      ((d • (1 : Matrix (Fin N) (Fin N) D.host.E)).map D.host.conj).transpose = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [hd]
  · simp [h, Ne.symm h]

theorem div_conj_unit {y : D.host.E} (hy : y ≠ 0) :
    y / D.host.conj y * D.host.conj (y / D.host.conj y) = 1 := by
  have hy' : D.host.conj y ≠ 0 := by simpa using hy
  rw [map_div₀, VacMove.conj_conj]; field_simp

theorem det_scalar {N : ℕ} {g : GL (Fin N) (AE D)} {y : D.host.E}
    (h : IsRat D g ((y / D.host.conj y) • (1 : Matrix (Fin N) (Fin N) D.host.E))) :
    ((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) = inc D (y ^ N / D.host.conj (y ^ N)) := by
  unfold IsRat at h
  rw [Matrix.GeneralLinearGroup.val_det_apply, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, map_pow, ← div_pow]
  simp

theorem oddEq_of (D : D7) (hP : admissible_poisson D) (hG : admG1 D) (hU : IntertwinerUnitary D) (hM : GaussSumTripleConstant D) (hL : LemmaCGaussConstant D)
    (h4 : odd4 D) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) (hC : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (hN : Even (N * N')) (hv : oddE0 D cc δ t0 N N' e0) :
    oddEq D cc δ N N' e0 := by
  intro W γA γA' γ γ' a a' hγ hγ' ha' ha F hF
  obtain ⟨b, b', hb⟩ := hP cc δ hC N N' hN e0 hv.1 W
  obtain ⟨Lt, l1, l2, -, l3, -⟩ := exists_lattice_of_adelic_point D N
  obtain ⟨Lt', l1', l2', -, l3', -⟩ := exists_lattice_of_adelic_point D N'
  have hK0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    Or.inr ⟨_, _, l2 ▸ (l1 1).2, l2' ▸ (l1' 1).2, rfl⟩
  have hT : e0 ∈ TT D (tor0 D cc δ) N N' := ⟨hv.1.1, 1, one_pos, fun x hx => by
    rw [one_smul, (GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' _ hK0).2.1 x hx]
    exact funext (hv.1.2 x hx)⟩
  have key : ∀ y y' : D.host.E, y ≠ 0 → y' ≠ 0 → IsOfFinOrder
      ((∏ τ, embT D τ (y / D.host.conj y) ^ (2 * N * (a τ - b τ))) *
        ∏ τ, embT D τ (y' / D.host.conj y') ^ (2 * N' * (a' τ - b' τ))) := by
    intro y y' hy hy'
    have hd := div_conj_unit hy
    have hd' := div_conj_unit hy'
    obtain ⟨g, hg⟩ := PtsMem.exists_isRat D _ (scalar_unitary N hd)
    obtain ⟨g', hg'⟩ := PtsMem.exists_isRat D _ (scalar_unitary N' hd')
    obtain ⟨z, x, hz, hx, hχ⟩ := split_char (pow_ne_zero N hy) _ (det_scalar hg)
    obtain ⟨z', x', hz', hx', hχ'⟩ := split_char (pow_ne_zero N' hy') _ (det_scalar hg')
    replace hχ := hχ _ W.chV'
    replace hχ' := hχ' _ W.chV
    simp only [map_pow (D.host.conj), ← div_pow] at hχ hχ'
    generalize y / D.host.conj y = d at *
    generalize y' / D.host.conj y' = d' at *
    have hs : d' * D.host.conj d * D.host.conj (d' * D.host.conj d) = 1 := by
      rw [map_mul, VacMove.conj_conj]
      linear_combination (d * D.host.conj d) * hd' + hd
    have hl : ∀ x, x ∈ stdL D N ↔ d • x ∈ Lt g := fun x => by
      simpa [l2, Matrix.smul_mulVec] using l3 g 1 _ hg x
    have hl' : ∀ x, x ∈ stdL D N' ↔ d' • x ∈ Lt' g' := fun x => by
      simpa [l2', Matrix.smul_mulVec] using l3' g' 1 _ hg' x
    obtain ⟨c, ζ, hζ, hc, hvac⟩ := vac_sc hG hU hM hL hC ht W.nz hv.2.2.2.1 hK0 hs
      (Or.inr ⟨_, _, (l1 g).2, (l1' g').2, rfl⟩) (sc_La hs cc δ hd hd' rfl hl hl')
    have hOm := hb g g' _ _ hg hg' e0 hT
    simp only [pull_sc hs cc δ rfl, hvac, ← mul_assoc] at hOm
    obtain ⟨sg, hsg, hsq⟩ := (h4 cc δ hC N N' hN e0 hv.1 W.nz W g g' _ _ _ (l1 g).1 (l1' g').1 hOm).1
      z z' x x' hz hz' hx hx'
    have hd0 : ∀ τ, embT D τ d ≠ 0 := fun τ => left_ne_zero_of_mul_eq_one (emb_unit τ hd)
    have hd0' : ∀ τ, embT D τ d' ≠ 0 := fun τ => left_ne_zero_of_mul_eq_one (emb_unit τ hd')
    have hcd : ∀ τ, embT D τ (D.host.conj d) = (embT D τ d)⁻¹ := fun τ => by
      rw [GlobalTheory.OnCoord.embT_conj]; exact eq_inv_of_mul_eq_one_right (emb_unit τ hd)
    have hζ0 : ζ ≠ 0 := hζ.isUnit.ne_zero
    have hsgf : IsOfFinOrder sg := isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, by rcases hsg with rfl | rfl <;> simp⟩
    have hζi : IsOfFinOrder ζ⁻¹ := by
      obtain ⟨k, hk, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hζ
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by rw [inv_pow, h, inv_one]⟩
    refine Eq.mpr (congrArg IsOfFinOrder (?_ : _ = sg * ζ⁻¹)) (hsgf.mul hζi)
    rw [eq_mul_inv_iff_mul_eq₀ hζ0]
    have e1 := eq_inv_of_mul_eq_one_left hχ
    have e2 := eq_inv_of_mul_eq_one_left hχ'
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val] at hsq
    rw [e1, e2, mul_pow, hc] at hsq
    have hne : (∏ τ, embT D τ (d' ^ N') ^ W.chV.n τ)⁻¹ ^ W.ep * (∏ τ, embT D τ (d ^ N) ^ W.chV'.n τ)⁻¹ ^ W.ep' ≠ 0 := by
      rw [← e1, ← e2]
      exact mul_ne_zero (zpow_ne_zero _ (pow_ne_zero _ (Units.ne_zero _))) (zpow_ne_zero _ (pow_ne_zero _ (Units.ne_zero _)))
    apply mul_right_cancel₀ hne
    rw [← hsq, mul_right_comm, mul_left_comm _ ζ, mul_comm _ ζ]
    refine congrArg (fun t : ℂ => ζ * t) ?_
    simp only [← Finset.prod_inv_distrib, ← Finset.prod_zpow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, map_pow, map_mul, hcd, mul_pow]
    simp only [← zpow_natCast, ← zpow_neg_one, ← zpow_mul]
    have hA : ∀ (u v : ℂ), u ≠ 0 → v ≠ 0 → ∀ i1 i2 i3 i4 j1 j2 j3 j4 : ℤ, i1 + i2 = i3 + i4 → j1 + j2 = j3 + j4 →
        u ^ i1 * v ^ j1 * (v ^ j2 * u ^ i2) = u ^ i3 * v ^ j3 * (v ^ j4 * u ^ i4) := by
      intro u v hu hv i1 i2 i3 i4 j1 j2 j3 j4 hi hj
      calc _ = u ^ (i1 + i2) * v ^ (j1 + j2) := by rw [zpow_add₀ hu, zpow_add₀ hv]; ring
        _ = _ := by rw [hi, hj, zpow_add₀ hu, zpow_add₀ hv]; ring
    apply hA _ _ (hd0 τ) (hd0' τ)
    · push_cast
      linear_combination (N : ℤ) * ha τ
    · push_cast
      linear_combination (N' : ℤ) * ha' τ
  have k1 := exp_eq_zero hG (fun τ => 2 * N * (a τ - b τ)) fun y hy => by simpa using key y 1 hy one_ne_zero
  have k2 := exp_eq_zero hG (fun τ => 2 * N' * (a' τ - b' τ)) fun y hy => by simpa using key 1 y one_ne_zero hy
  rw [hb γA γA' γ γ' hγ hγ' F hF]
  funext z
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  congr 1
  · rcases Nat.eq_zero_or_pos N with rfl | h
    · simp
    · have : a τ = b τ := by simpa [h.ne', sub_eq_zero] using k1 τ
      rw [this]
  · rcases Nat.eq_zero_or_pos N' with rfl | h
    · simp
    · have : a' τ = b' τ := by simpa [h.ne', sub_eq_zero] using k2 τ
      rw [this]

theorem stmt_oddEq (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) :
    StatementOddExactness D cc δ t0 N N' e0 :=
  fun hC ht hN hv hP hG hU hM hL _ h4 => oddEq_of D hP hG hU hM hL h4 cc δ t0 N N' e0 hC ht hN hv

end GlobalTheory.RatEquiv
