import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix Formalism.L2.Pj.FJ Complex
open scoped ComplexConjugate

namespace Formalism.L2.Pj.QAt

theorem max_cusps_rank_one_expand {R : Type} [CommRing R] (σ : R →+* R) {r ρ : ℕ}
    (G : Matrix (Fin r) (Fin r) R) (η : Fin ρ → R) (e : Fin ρ → Fin r → R) (α : R) (a b : Fin r) :
    α * (∑ a', η a' * e a' a) * ∑ k, G b k * σ (∑ b', η b' * e b' k) =
      ∑ a', ∑ b', α * (η a' * σ (η b')) * e a' a * ∑ k, G b k * σ (e b' k) := by
  have hσ : ∀ k, σ (∑ b', η b' * e b' k) = ∑ b', σ (η b') * σ (e b' k) := fun k => by
    simp only [map_sum, map_mul]
  have hin : (∑ k, G b k * σ (∑ b', η b' * e b' k)) =
      ∑ b', σ (η b') * ∑ k, G b k * σ (e b' k) := by
    simp_rw [hσ, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hin, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b' _ => by ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem maxCuspsA_zMatC_add (X : Data E r) (cu : CuspFD X ρ) (τ : E →+* ℂ)
    (β β' : Matrix (Fin ρ) (Fin ρ) ℂ) :
    zMatC X cu.e τ (β + β') = zMatC X cu.e τ β * zMatC X cu.e τ β' := by
  have hτ : ∀ x : E, τ (cc x) = (starRingEnd ℂ) (τ x) := fun x => by
    first
    | exact IsCMField.complexEmbedding_complexConj τ x
    | exact IsCMField.complexEmbedding_complexConj (K := E) τ x
    | simp [cc, IsCMField.complexEmbedding_complexConj]
    | simp [cc]
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin r) (Fin ρ) ℂ, U = Matrix.of fun k a => τ (cu.e a k) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin ρ) (Fin r) ℂ,
      V = Matrix.of fun b l => ∑ k', τ (X.Gm l k') * (starRingEnd ℂ) (τ (cu.e b k')) := ⟨_, rfl⟩
  have hZ : ∀ γ, zMatC X cu.e τ γ = 1 + U * γ * V := by
    intro γ
    ext k l
    simp only [zMatC, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, hU, hV]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hVU : V * U = 0 := by
    ext b c
    have h0 := congrArg τ (cu.3 c b)
    simp only [herm, map_sum, map_mul, hτ, map_zero] at h0
    simp only [Matrix.mul_apply, hU, hV, Matrix.of_apply, Matrix.zero_apply, Finset.sum_mul]
    rw [← h0]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k' _ => by ring
  have key : U * β * V * (U * β' * V) = 0 := by
    calc U * β * V * (U * β' * V) = U * β * (V * U) * β' * V := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hVU]; simp
  rw [hZ, hZ, hZ]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, key, add_zero]
  abel

theorem maxCuspsA_zAct_add (X : Data E r) (cu : CuspFD X ρ) (t u : Fin (nZ X ρ) → ℝ)
    (x : Frame X.Ψ r) : zAct X cu t (zAct X cu u x) = zAct X cu (t + u) x := by
  funext τ
  have hS : (∑ k, (((t + u) k : ℝ) : ℂ) • (zBas X cu k).map τ.1) =
      (∑ k, ((t k : ℝ) : ℂ) • (zBas X cu k).map τ.1) + ∑ k, ((u k : ℝ) : ℂ) • (zBas X cu k).map τ.1 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.add_apply, Complex.ofReal_add, add_smul]
  have hm : mat (zAct X cu u x) τ =
      zMatC X cu.e τ.1 (∑ k, ((u k : ℝ) : ℂ) • (zBas X cu k).map τ.1) * mat x τ := rfl
  show zMatC X cu.e τ.1 (∑ k, ((t k : ℝ) : ℂ) • (zBas X cu k).map τ.1) * mat (zAct X cu u x) τ =
    zMatC X cu.e τ.1 (∑ k, (((t + u) k : ℝ) : ℂ) • (zBas X cu k).map τ.1) * mat x τ
  rw [hm, hS, maxCuspsA_zMatC_add, Matrix.mul_assoc]

theorem maxCuspsA_zMatE_map (X : Data E r) (e : Fin ρ → Fin r → E) (τ : E →+* ℂ)
    (β : Matrix (Fin ρ) (Fin ρ) E) : (zMatE X e β).map τ = zMatC X e τ (β.map τ) := by
  have hτ : ∀ x : E, τ (cc x) = (starRingEnd ℂ) (τ x) := fun x => by
    first
    | exact IsCMField.complexEmbedding_complexConj τ x
    | exact IsCMField.complexEmbedding_complexConj (K := E) τ x
    | simp [cc, IsCMField.complexEmbedding_complexConj]
    | simp [cc]
  ext k l
  simp only [zMatE, zMatC, Matrix.map_apply, Matrix.of_apply, map_add, map_sum, map_mul, hτ]
  split_ifs <;> simp

theorem maxCuspsA_zAct_int (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (n : Fin (nZ X ρ) → ℤ) : ∃ β ∈ zGam X cu, ∃ γ ∈ X.Γ,
      (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β ∧
      ∀ y, zAct X cu (fun i => (n i : ℝ)) y = lact γ y := by
  obtain ⟨-, hb2⟩ := hb
  have hβ : (∑ k, n k • zBas X cu k) ∈ zGam X cu := by
    rw [hb2]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hβ' := hβ
  simp only [zGam, Set.mem_setOf_eq] at hβ'
  obtain ⟨-, γ, hγ, hγe⟩ := hβ'
  refine ⟨_, hβ, γ, hγ, hγe, fun y => ?_⟩
  funext τ
  show zMatC X cu.e τ.1 (∑ k, (((n k : ℝ)) : ℂ) • (zBas X cu k).map τ.1) * mat y τ =
    (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ
  rw [hγe, maxCuspsA_zMatE_map]
  congr 2
  ext i j
  simp only [Matrix.sum_apply, Matrix.map_apply, Matrix.smul_apply, map_sum, map_zsmul, smul_eq_mul]
  simp only [zsmul_eq_mul, Complex.ofReal_intCast]

theorem maxCuspsA_periodic (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (la : Wt X.Ψ r)
    (hchi : ∀ β ∈ zGam X cu, ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β →
      X.χ la γ = 1)
    (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (u : Fin (nZ X ρ) → ℝ) (n : Fin (nZ X ρ) → ℤ) :
    P (zAct X cu (u + fun i => (n i : ℝ)) x) = P (zAct X cu u x) := by
  obtain ⟨β, hβ, γ, hγ, hγe, hact⟩ := maxCuspsA_zAct_int X cu hb n
  have hy : zAct X cu u x ∈ X.dom := zAct_mem_dom X cu (zBas_skew X cu ⟨_, hb⟩) u x hx
  rw [add_comm, ← maxCuspsA_zAct_add, hact, hP.2.2 γ hγ _ hy, hchi β hβ γ hγ hγe, one_mul]

def mcMη (η : Fin ρ → E) : Matrix (Fin ρ) (Fin ρ) E := Matrix.of fun a b => η a * cc (η b)

def mcMηc (τ : E →+* ℂ) (η : Fin ρ → E) : Matrix (Fin ρ) (Fin ρ) ℂ :=
  Matrix.of fun a b => τ (η a) * conj (τ (η b))

theorem maxCuspsA_vec_apply (cu : Fin ρ → Fin r → E) (η : Fin ρ → E) (k : Fin r) :
    (∑ a, η a • cu a) k = ∑ a, η a * cu a k := by
  simp [Finset.sum_apply]

theorem maxCuspsA_transv (X : Data E r) (cu : CuspFD X ρ) (η : Fin ρ → E) (α : E) :
    transvMat X.Gm (∑ a, η a • cu.e a) α = zMatE X cu.e (α • mcMη η) := by
  ext k l
  have hv := maxCuspsA_vec_apply cu.e η
  simp only [transvMat, zMatE, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mcMη, hv]
  congr 1
  exact max_cusps_rank_one_expand (IsCMField.complexConj E : E →+* E) X.Gm η cu.e α k l

theorem maxCuspsA_flowMat (X : Data E r) (cu : CuspFD X ρ) (η : Fin ρ → E) (τ : X.Ψ) (z : ℂ) :
    X.flowMat (∑ a, η a • cu.e a) τ z = zMatC X cu.e τ.1 ((-(I * X.c τ) * z) • mcMηc τ.1 η) := by
  ext k l
  have hv := maxCuspsA_vec_apply cu.e η
  have h1 := max_cusps_rank_one_expand (starRingEnd ℂ) (fun k l => τ.1 (X.Gm k l)) (fun a => τ.1 (η a))
    (fun a k => τ.1 (cu.e a k)) (-(I * X.c τ) * z) k l
  simp only [map_sum, map_mul] at h1
  simp only [Data.flowMat, zMatC, mcMηc, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hv,
    map_sum, map_mul]
  rw [sub_eq_add_neg]
  congr 1
  rw [← h1]
  ring

theorem maxCuspsA_kappa_cc (X : Data E r) : cc X.κ0 = -X.κ0 := by
  have h2 : cc (2 : E) = 2 := by simp [cc]
  have hm : ∀ x y : E, cc (x * y) = cc x * cc y := fun x y => by simp [cc]
  have hn : ∀ x : E, cc (-x) = -cc x := fun x => by simp [cc]
  rcases X.κ0_xi with h | h
  · rw [h, hm, h2, X.ξ0_im, mul_neg]
  · rw [h, hn, hm, h2, X.ξ0_im, mul_neg]

theorem mc_cc_mul (x y : E) : cc (x * y) = cc x * cc y := by
  simp [cc]

theorem mc_cc_add (x y : E) : cc (x + y) = cc x + cc y := by
  simp [cc]

theorem mc_cc_nat (n : ℕ) : cc (n : E) = n := by
  simp [cc]

theorem mc_cc_cc (x : E) : cc (cc x) = x := by
  first
  | simp [cc]
  | exact IsCMField.complexConj_apply_apply x
  | exact IsCMField.complexConj_apply_apply (K := E) x

theorem maxCuspsA_herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem maxCuspsA_herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem maxCuspsA_herm_add_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, Pi.add_apply, mc_cc_add, mul_add, Finset.sum_add_distrib]

theorem maxCuspsA_herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, mc_cc_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem maxCuspsA_herm_sum_left {ι : Type} (G : Matrix (Fin r) (Fin r) E) (s : Finset ι)
    (f : ι → Fin r → E) (y : Fin r → E) :
    herm G (∑ i ∈ s, f i) y = ∑ i ∈ s, herm G (f i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [herm]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, maxCuspsA_herm_add_left, ih]

theorem maxCuspsA_herm_sum_right {ι : Type} (G : Matrix (Fin r) (Fin r) E) (s : Finset ι)
    (f : ι → Fin r → E) (x : Fin r → E) :
    herm G x (∑ i ∈ s, f i) = ∑ i ∈ s, herm G x (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [herm, cc]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, maxCuspsA_herm_add_right, ih]

theorem maxCuspsA_iso (X : Data E r) (cu : CuspFD X ρ) (η : Fin ρ → E) :
    herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) = 0 := by
  rw [maxCuspsA_herm_sum_left]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [maxCuspsA_herm_smul_left, maxCuspsA_herm_sum_right]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b _ => ?_)
  rw [maxCuspsA_herm_smul_right, cu.3 a b, mul_zero]

theorem maxCuspsA_ne (X : Data E r) (cu : CuspFD X ρ) (η : Fin ρ → E) (hη : η ≠ 0) :
    ∑ a, η a • cu.e a ≠ 0 := by
  intro h
  apply hη
  funext a
  exact Fintype.linearIndependent_iff.mp cu.2 η h a

def mcBeta (X : Data E r) (la : Wt X.Ψ r) (η : Fin ρ → E) (a : E) : Matrix (Fin ρ) (Fin ρ) E :=
  ((X.m : E) * ((X.chiOrd la : E) * a) * X.κ0) • mcMη η

theorem maxCuspsA_beta_mem (X : Data E r) (cu : CuspFD X ρ) (la : Wt X.Ψ r) (η : Fin ρ → E)
    (hξΛ : ∑ a, η a • cu.e a ∈ X.Λ) (a : E) (ha : cc a = a) (hai : IsIntegral ℤ a) :
    mcBeta X la η a ∈ zGam X cu := by
  have hn : ∀ n : ℕ, IsIntegral ℤ (n : E) := by
    intro n
    induction n with
    | zero => simpa using (isIntegral_zero : IsIntegral ℤ (0 : E))
    | succ k ih => simpa [Nat.cast_succ] using ih.add (isIntegral_one : IsIntegral ℤ (1 : E))
  have hs : cc ((X.chiOrd la : E) * a) = (X.chiOrd la : E) * a := by rw [mc_cc_mul, mc_cc_nat, ha]
  have hi : IsIntegral ℤ ((X.chiOrd la : E) * a) := (hn _).mul hai
  obtain ⟨γ, hγ, hγe⟩ := X.transv _ hξΛ (maxCuspsA_iso X cu η) _ hs hi
  simp only [zGam, Set.mem_setOf_eq]
  refine ⟨?_, γ, hγ, ?_⟩
  · simp only [IsSkew]
    intro i j
    simp only [mcBeta, mcMη, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mc_cc_mul, mc_cc_nat, ha,
      mc_cc_cc, maxCuspsA_kappa_cc]
    ring
  · rw [hγe, maxCuspsA_transv, mcBeta]

theorem maxCuspsA_beta_map (X : Data E r) (la : Wt X.Ψ r) (η : Fin ρ → E) (a : E)
    (ha : cc a = a) (τ : X.Ψ) :
    (mcBeta X la η a).map τ.1 =
      (((ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.per X la a τ : ℝ) : ℂ) * (-(I * X.c τ))) • mcMηc τ.1 η := by
  have hτ : ∀ x : E, τ.1 (cc x) = (starRingEnd ℂ) (τ.1 x) := fun x => by
    first
    | exact IsCMField.complexEmbedding_complexConj τ.1 x
    | exact IsCMField.complexEmbedding_complexConj (K := E) τ.1 x
    | simp [cc, IsCMField.complexEmbedding_complexConj]
    | simp [cc]
  have gen : ∀ z : ℂ, z.re = 0 → ‖z‖ = |z.im| := fun z hz0 => by
    have hz : z = (z.im : ℂ) * I := Complex.ext (by simp [hz0]) (by simp)
    rw [hz]
    simp
  have hk : τ.1 X.κ0 = -(I * (X.c τ : ℂ)) := by
    have h1 : (starRingEnd ℂ) (τ.1 X.κ0) = -τ.1 X.κ0 := by
      rw [← hτ, maxCuspsA_kappa_cc, map_neg]
    have hre : (τ.1 X.κ0).re = 0 := by
      have h2 := congrArg Complex.re h1
      simp only [Complex.conj_re, Complex.neg_re] at h2
      linarith
    have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
      have h2 : ‖τ.1 (2 * X.ξ0)‖ = X.c τ := by
        rw [map_mul, norm_mul, map_ofNat, Data.c]
        first
        | norm_num
        | simp
      rcases X.κ0_xi with h | h
      · rw [h, h2]
      · rw [h, map_neg, norm_neg, h2]
    have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := Complex.ext (by simp [hre]) (by simp)
    have hn : |(τ.1 X.κ0).im| = X.c τ := by rw [← gen _ hre, hnorm]
    rw [abs_of_neg (X.κ0_sign τ)] at hn
    rw [hz, ← hn]
    push_cast
    ring
  have ha' : (((τ.1 a).re : ℝ) : ℂ) = τ.1 a := Complex.conj_eq_iff_re.mp (by rw [← hτ, ha])
  ext i j
  simp only [mcBeta, mcMη, mcMηc, Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    map_mul, map_natCast, hτ, hk, ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.per]
  push_cast
  rw [ha']
  ring

theorem maxCuspsA_flow_eq (X : Data E r) (cu : CuspFD X ρ) (la : Wt X.Ψ r) (η : Fin ρ → E) {n : ℕ}
    (a : Fin n → E) (ha : ∀ j, cc (a j) = a j) (ω : Fin n → X.Ψ → ℝ)
    (hω : ∀ j, ω j = ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.per X la (a j))
    (c : Fin n → Fin (nZ X ρ) → ℤ) (hc : ∀ j, ∑ k, c j k • zBas X cu k = mcBeta X la η (a j))
    (t : Fin n → ℝ) (x : Frame X.Ψ r) :
    X.flow (∑ a, η a • cu.e a) (fun τ => ∑ j, ((t j : ℝ) : ℂ) * (ω j τ : ℂ)) x =
      zAct X cu (mcT c t) x := by
  funext τ
  have hZ : ∀ j, ∑ k, ((c j k : ℤ) : ℂ) • (zBas X cu k).map τ.1 =
      (((ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.per X la (a j) τ : ℝ) : ℂ) * (-(I * X.c τ))) • mcMηc τ.1 η := by
    intro j
    rw [← maxCuspsA_beta_map X la η (a j) (ha j) τ, ← hc j]
    ext i i'
    simp only [Matrix.sum_apply, Matrix.map_apply, Matrix.smul_apply, map_sum, map_zsmul, smul_eq_mul]
    simp only [zsmul_eq_mul]
  show X.flowMat (∑ a, η a • cu.e a) τ (∑ j, ((t j : ℝ) : ℂ) * (ω j τ : ℂ)) * mat x τ =
    zMatC X cu.e τ.1 (∑ k, ((mcT c t k : ℝ) : ℂ) • (zBas X cu k).map τ.1) * mat x τ
  rw [maxCuspsA_flowMat]
  congr 2
  have hB : (∑ k, ((mcT c t k : ℝ) : ℂ) • (zBas X cu k).map τ.1) =
      ∑ j, ((t j : ℝ) : ℂ) • ∑ k, ((c j k : ℤ) : ℂ) • (zBas X cu k).map τ.1 := by
    simp only [mcT, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast, Finset.sum_smul,
      Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  rw [hB]
  simp only [hZ, smul_smul, ← Finset.sum_smul, hω]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end Formalism.L2.Pj.QAt
