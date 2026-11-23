import Mathlib
import Formalism.GelfandTransference.HadamardGelfand.Hadamard
import Formalism.FlagUnipotentLattices.SignaturePreservingEntryNorms
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.DualOrthSum
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobalAssemblyOfStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.GluingLemmasAndTheorems
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
import Formalism.SharpRestriction.CuspSpanNormBounds.JExistsNatSmulMemL
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MExistsNatSmulMem

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def StarConj (E : Type) [Field E] [StarRing E] : Prop :=
  ∀ (τ : E →+* ℂ) (x : E), τ (star x) = starRingEnd ℂ (τ x)

def PosX {T : E} (F : LFlag S r T) : Prop :=
  ∀ τ : E →+* ℂ, ∀ y ∈ orth S (Xplus F), y ∉ Xsp F → 0 < nrm S τ y

def U2 {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Submodule E S.V := Xplus F ⊔ Xplus F'

def HU (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  UUE Λ F F' = U2 F F'

def HInd {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  LinearIndependent E (Sum.elim (frame F) (frame F'))

def HNd {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  U2 F F' ⊓ orth S (U2 F F') = ⊥

end Gen

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Matrix

theorem p_neg_dim {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] {p q : ℕ} (J : Matrix n n ℂ)
    (Q : Matrix n (Fin p ⊕ Fin q) ℂ) (hQ : Qᴴ * J * Q = Formalism.UG.Jpq p q) (A : Matrix n ι ℂ)
    (hA : Function.Injective A.mulVec)
    (hneg : ∀ x : ι → ℂ, (star (A *ᵥ x) ⬝ᵥ (J *ᵥ (A *ᵥ x))).re ≤ 0) :
    p + Fintype.card ι ≤ Fintype.card n := by
  let M : Matrix n (Fin p ⊕ ι) ℂ :=
    Matrix.of fun i k => Sum.elim (fun a => Q i (Sum.inl a)) (fun b => -A i b) k
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    rw [Matrix.mulVecLin_apply] at hx
    let u : Fin p ⊕ Fin q → ℂ := Sum.elim (x ∘ Sum.inl) 0
    let w : ι → ℂ := x ∘ Sum.inr
    have hM : M *ᵥ x = Q *ᵥ u - A *ᵥ w := by
      funext i
      simp [M, u, w, mulVec, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg]
    rw [hM, sub_eq_zero] at hx
    have h1 := Formalism.UG.P.sig_quad J Q hQ u
    have h2 := hneg w
    rw [← hx, h1] at h2
    simp only [u, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.zero_apply, star_zero,
      mul_zero, Finset.sum_const_zero, sub_zero] at h2
    have hc : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
      intro z; rw [Complex.normSq_eq_conj_mul_self]; rfl
    simp only [hc] at h2
    have h3 : (∑ i, Complex.normSq (x (Sum.inl i))) ≤ 0 := by
      simpa using h2
    have hA0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Complex.normSq_nonneg (x (Sum.inl i)))).1
      (le_antisymm h3 (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)))
    have hu : u = 0 := by
      funext k
      rcases k with a | b
      · exact Complex.normSq_eq_zero.1 (hA0 a (Finset.mem_univ _))
      · rfl
    have hw : w = 0 := by
      apply hA
      rw [← hx, hu]
      simp
    funext k
    rcases k with a | b
    · exact Complex.normSq_eq_zero.1 (hA0 a (Finset.mem_univ _))
    · exact congrFun hw b
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using this

theorem p_map_inj {K L n ι : Type} [Field K] [Field L] [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] (τ : K →+* L) (C : Matrix n ι K) (hC : Function.Injective C.mulVec) :
    Function.Injective (C.map τ).mulVec := by
  have hker : LinearMap.ker C.mulVecLin = ⊥ := LinearMap.ker_eq_bot.2 hC
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective C.mulVecLin hker
  have hB : LinearMap.toMatrix' g * C = 1 := by
    have : LinearMap.toMatrix' (g ∘ₗ C.mulVecLin) = 1 := by rw [hg]; exact LinearMap.toMatrix'_id
    have hC' : LinearMap.toMatrix' C.mulVecLin = C := by
      rw [← Matrix.toLin'_apply']; exact LinearMap.toMatrix'_toLin' C
    rw [LinearMap.toMatrix'_comp, hC'] at this
    exact this
  have hB' : (LinearMap.toMatrix' g).map τ * C.map τ = 1 := by
    rw [← Matrix.map_mul, hB]
    simp
  intro x y hxy
  have := congrArg (fun v => (LinearMap.toMatrix' g).map τ *ᵥ v) hxy
  simpa [Matrix.mulVec_mulVec, hB'] using this

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem p_hT_expand (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ a, ∑ b, star (S.frame.repr x a) * S.gram a b * S.frame.repr y b := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, HSpace.gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [RingHom.id_apply]
  ring

theorem p_gram_family (S : HSpace E) {ι : Type} [Fintype ι] (w : ι → S.V) :
    (Matrix.of fun i j => S.hT (w i) (w j)) =
      (Matrix.of fun a i => S.frame.repr (w i) a)ᴴ * S.gram *
        Matrix.of fun a i => S.frame.repr (w i) a := by
  ext i j
  rw [Matrix.of_apply, p_hT_expand]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem p_map_family (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    {ι : Type} [Fintype ι] (w : ι → S.V) :
    (Matrix.of fun i j => S.hT (w i) (w j)).map τ =
      ((Matrix.of fun a i => S.frame.repr (w i) a).map τ)ᴴ * S.gram.map τ *
        (Matrix.of fun a i => S.frame.repr (w i) a).map τ := by
  rw [p_gram_family, Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ (fun a => hτ a)]

theorem p_family_neg (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → S.V) (hw : LinearIndependent E w) {p q : ℕ}
    (hS : Formalism.UG.HasSignature (S.gram.map τ) p q)
    (hneg : ∀ x : ι → ℂ,
      (star x ⬝ᵥ (((Matrix.of fun i j => S.hT (w i) (w j)).map τ) *ᵥ x)).re ≤ 0) :
    p + Fintype.card ι ≤ S.rank := by
  obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ p q hS
  set C : Matrix (Fin S.rank) ι E := Matrix.of fun a i => S.frame.repr (w i) a with hCdef
  have hC : Function.Injective C.mulVec := by
    have : Function.Injective C.mulVecLin := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      rw [Matrix.mulVecLin_apply] at hx
      have h0 : ∑ i, x i • w i = 0 := by
        apply S.frame.repr.injective
        ext a
        have := congrFun hx a
        simp only [mulVec, dotProduct, hCdef, Matrix.of_apply, Pi.zero_apply] at this
        simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
          Pi.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply]
        rw [← this]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      funext i
      exact Fintype.linearIndependent_iff.1 hw x h0 i
    exact this
  have hA := p_map_inj τ C hC
  have h := p_neg_dim (S.gram.map τ) Q hQ (C.map τ) hA (by
    intro x
    have : star (C.map τ *ᵥ x) ⬝ᵥ (S.gram.map τ *ᵥ (C.map τ *ᵥ x)) =
        star x ⬝ᵥ (((C.map τ)ᴴ * S.gram.map τ * C.map τ) *ᵥ x) := by
      rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec,
        Matrix.mul_assoc]
    rw [this, ← p_map_family S τ hτ w]
    exact hneg x)
  simpa using h

theorem p_mem_orth {S : HSpace E} {U : Submodule E S.V} {y : S.V} :
    y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem p_symm_zero (S : HSpace E) {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [← S.herm.eq x y, h, map_zero]

theorem p_posX_gen (S : HSpace E) (hτ : StarConj E) (hS : S.SigOK) {r : ℕ}
    (hsig : ∀ τ : E →+* ℂ, (S.sig τ).2 = r + 1) {T : ℕ} (hT : 0 < T) (F : LFlag S r (T : E)) :
    PosX F := by
  intro τ y hy hyX
  by_contra hle
  rw [not_lt] at hle
  rw [p_mem_orth] at hy
  have heX : ∀ a, F.fl.e a ∈ Xsp F := fun a => Submodule.subset_span ⟨a, rfl⟩
  have hey : ∀ a, S.hT (F.fl.e a) y = 0 := fun a => hy _ (Submodule.mem_sup_left (heX a))
  have hzy : S.hT F.fl.z y = 0 :=
    hy _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hye : ∀ a, S.hT y (F.fl.e a) = 0 := fun a => p_symm_zero S (hey a)
  have hyz : S.hT y F.fl.z = 0 := p_symm_zero S hzy
  have hez : ∀ a, S.hT (F.fl.e a) F.fl.z = 0 := F.fl.z_orth
  have hze : ∀ a, S.hT F.fl.z (F.fl.e a) = 0 := fun a => p_symm_zero S (hez a)
  have hTE : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne'
  let w : Fin r ⊕ Fin 2 → S.V := Sum.elim F.fl.e ![F.fl.z, y]
  have hw : LinearIndependent E w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, w, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hc
    have hcz : c (Sum.inr 0) = 0 := by
      have := congrArg (S.hT F.fl.z) hc
      simp only [map_add, map_sum, map_smul, hze, hzy, F.fl.z_norm, smul_eq_mul, mul_zero,
        Finset.sum_const_zero, zero_add, add_zero, map_zero] at this
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd (neg_eq_zero.1 h) hTE
    have hcy : c (Sum.inr 1) = 0 := by
      by_contra hne
      apply hyX
      have h2 : c (Sum.inr 1) • y = -∑ a, c (Sum.inl a) • F.fl.e a := by
        rw [hcz, zero_smul, zero_add] at hc
        exact eq_neg_of_add_eq_zero_right hc
      have h3 : c (Sum.inr 1) • y ∈ Xsp F := by
        rw [h2]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (heX a))
      exact (Submodule.smul_mem_iff _ hne).1 h3
    rw [hcz, hcy, zero_smul, zero_smul, add_zero, add_zero] at hc
    have hce := Fintype.linearIndependent_iff.1 F.fl.e_indep (fun a => c (Sum.inl a)) hc
    intro i
    rcases i with a | j
    · exact hce a
    · fin_cases j
      · exact hcz
      · exact hcy
  have hcc : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
    intro z; rw [Complex.normSq_eq_conj_mul_self]; rfl
  have hquad : ∀ x : Fin r ⊕ Fin 2 → ℂ,
      star x ⬝ᵥ (((Matrix.of fun i j => S.hT (w i) (w j)).map τ) *ᵥ x) =
        -(T : ℂ) * ((Complex.normSq (x (Sum.inr 0)) : ℝ) : ℂ) +
          τ (S.hT y y) * ((Complex.normSq (x (Sum.inr 1)) : ℝ) : ℂ) := by
    intro x
    simp only [dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.map_apply,
      Matrix.of_apply, w, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      F.fl.e_iso, hey, hye, hez, hze, hzy, hyz, F.fl.z_norm, map_zero, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, map_neg, map_natCast, Pi.star_apply]
    rw [← hcc, ← hcc]
    ring
  have hp := p_family_neg S τ (hτ τ) w hw (hS τ) (by
    intro x
    rw [hquad x]
    have h1 : 0 ≤ Complex.normSq (x (Sum.inr 0)) := Complex.normSq_nonneg _
    have h2 : 0 ≤ Complex.normSq (x (Sum.inr 1)) := Complex.normSq_nonneg _
    have h3 : (τ (S.hT y y)).re ≤ 0 := hle
    have h4 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.natCast_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith [mul_nonneg h4 h1, mul_nonneg (neg_nonneg.2 h3) h2])
  have hsum : (S.sig τ).1 + (S.sig τ).2 = S.rank := by
    have := (Formalism.UG.P.sig_data _ _ _ (hS τ)).1
    simpa using this.symm
  rw [hsig τ] at hsum
  simp only [Fintype.card_sum, Fintype.card_fin] at hp
  omega

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem p_starConj (D : D7) : StarConj D.host.E := D.sp.cm.cmUnram.2.1

theorem p_posX (D : D7) (T : ℕ) (hT : 0 < T) (F : LFlag (hS D) D.R.rS (T : D.host.E)) : PosX F :=
  p_posX_gen (hS D) (p_starConj D) (D.sp.Y_sig 0)
    (fun τ => by rw [D.sp.baseSpace_signature_eq τ]; rfl) hT F

end D7

section Gen2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem p_X_iso {T : E} (F : LFlag S r T) {x x' : S.V} (hx : x ∈ Xsp F) (hx' : x' ∈ Xsp F) :
    S.hT x x' = 0 := by
  have h1 : ∀ a, S.hT (F.fl.e a) x' = 0 := by
    intro a
    refine Submodule.span_induction (p := fun v _ => S.hT (F.fl.e a) v = 0) ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨b, rfl⟩; exact F.fl.e_iso a b
    · simp
    · intro u v _ _ hu hv; rw [map_add, hu, hv, add_zero]
    · intro c u _ hu; rw [map_smul, hu, smul_zero]
  refine Submodule.span_induction (p := fun v _ => S.hT v x' = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, rfl⟩; exact h1 a
  · simp
  · intro u v _ _ hu hv; rw [map_add, LinearMap.add_apply, hu, hv, add_zero]
  · intro c u _ hu; rw [map_smulₛₗ, LinearMap.smul_apply, hu, smul_zero]

theorem p_nonneg {T : E} {F : LFlag S r T} (hP : PosX F) (τ : E →+* ℂ) {y : S.V}
    (hy : y ∈ orth S (Xplus F)) : 0 ≤ nrm S τ y := by
  by_cases hX : y ∈ Xsp F
  · simp [nrm, p_X_iso F hX hX]
  · exact (hP τ y hy hX).le

theorem radical_positive_each_embedding (Λ : Submodule (𝓞 E) S.V) {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}
    (hU : HU Λ F F') (hNd : HNd F F') (hP : PosX F) :
    ∀ τ : E →+* ℂ, ∀ x ∈ Hp Λ F F', x ≠ 0 → 0 < nrm S τ x := by
  intro τ x hx hx0
  have hx' : x ∈ orth S (U2 F F') := by
    have : Hp Λ F F' = orth S (U2 F F') := by unfold Hp; rw [hU]
    rwa [this] at hx
  refine hP τ x ?_ ?_
  · rw [p_mem_orth] at hx' ⊢
    exact fun v hv => hx' v (Submodule.mem_sup_left hv)
  · intro hX
    apply hx0
    have : x ∈ U2 F F' ⊓ orth S (U2 F F') :=
      ⟨Submodule.mem_sup_left (Submodule.mem_sup_left hX), hx'⟩
    rw [hNd] at this
    exact (Submodule.mem_bot E).1 this

end Gen2

section Gen3

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

end Gen3

section D7b

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem p_rankV (D : D7) : finrank D.host.E (hS D).V = D.R.k + 2 * D.R.rS + 1 := by
  rw [(hS D).rank_eq, D.sp.Y_rank 0 (Nat.zero_le _)]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.rankY, Ranks.r, Ranks.rS, zero_mul, add_zero]
  omega

end D7b

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section A

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem a_mem_orth (U : Submodule E S.V) (y : S.V) : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem a_exists_smul_mem (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (x : S.V) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • x ∈ Λ := by
  first
  | exact Formalism.MainNotions.LatticeGluingRadicals.a_exists_smul_memL
  | (apply Formalism.MainNotions.LatticeGluingRadicals.a_exists_smul_memL <;> assumption)
  | (intros; apply Formalism.MainNotions.LatticeGluingRadicals.a_exists_smul_memL <;> assumption)
  | (intros; exact Formalism.MainNotions.LatticeGluingRadicals.a_exists_smul_memL ‹_› ‹_›)
theorem a_span_inf (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (U : Submodule E S.V) :
    Submodule.span E ((Λ ⊓ toO S U : Submodule (𝓞 E) S.V) : Set S.V) = U := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro x hx
    obtain ⟨c, hc, hcx⟩ := a_exists_smul_mem Λ hΛ x
    have hc1 : algebraMap (𝓞 E) E c ≠ 0 := by simpa using hc
    have h1 : c • x ∈ (Λ ⊓ toO S U : Submodule (𝓞 E) S.V) :=
      ⟨hcx, (toO S U).smul_mem c hx⟩
    have h2 : x = (algebraMap (𝓞 E) E c)⁻¹ • (c • x) := by
      rw [← algebraMap_smul E c, smul_smul, inv_mul_cancel₀ hc1, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem a_span_sup (A B : Submodule (𝓞 E) S.V) :
    Submodule.span E ((A ⊔ B : Submodule (𝓞 E) S.V) : Set S.V) =
      Submodule.span E (A : Set S.V) ⊔ Submodule.span E (B : Set S.V) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ha))
      (Submodule.mem_sup_right (Submodule.subset_span hb))
  · exact sup_le (Submodule.span_mono (by exact_mod_cast (le_sup_left : A ≤ A ⊔ B)))
      (Submodule.span_mono (by exact_mod_cast (le_sup_right : B ≤ A ⊔ B)))

theorem a_HU (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) :
    HU Λ F F' := by
  unfold HU UUE spanE UU U2 XLam
  rw [a_span_sup, a_span_sup, a_span_sup, a_span_inf Λ hΛ, a_span_inf Λ hΛ,
    Submodule.span_span_of_tower, Submodule.span_span_of_tower, hz, hz']
  simp only [Formalism.MainNotions.S.FlagG.Xplus]
  rw [sup_assoc]

theorem a_herm (x y : S.V) : S.hT y x = star (S.hT x y) := by
  exact (S.herm.eq x y).symm

theorem a_frame_castSucc {T : E} (F : LFlag S r T) (i : Fin r) :
    frame F i.castSucc = F.fl.e i := by
  simp [Formalism.MainNotions.S.FlagG.fvec]

theorem a_frame_last {T : E} (F : LFlag S r T) : frame F (Fin.last r) = F.fl.z := by
  simp [Formalism.MainNotions.S.FlagG.fvec]

theorem a_gram_self {T : E} (F : LFlag S r T) (i j : Fin (r + 1)) :
    S.hT (frame F j) (frame F i) =
      Matrix.diagonal (fun i : Fin (r + 1) => if i = Fin.last r then -T else 0) i j := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [a_frame_last, F.fl.z_norm]
    | cast j =>
      rw [a_frame_last, a_frame_castSucc, F.fl.z_orth,
        Matrix.diagonal_apply_ne _ (Fin.castSucc_lt_last j).ne']
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [a_frame_last, a_frame_castSucc, a_herm, F.fl.z_orth, star_zero,
        Matrix.diagonal_apply_ne _ (Fin.castSucc_lt_last i).ne]
    | cast j =>
      rw [a_frame_castSucc, a_frame_castSucc, F.fl.e_iso, Matrix.diagonal_apply]
      simp [(Fin.castSucc_lt_last i).ne]

theorem discriminant_eq_det_lift_alt {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    Dr1 F F' = (ZhatL F F').det := by
  simp [Formalism.MainNotions.S.Dl, Formalism.MainNotions.S.leadMinorE]

theorem a_Dr {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    Dr F F' = ((ZhatL F F').submatrix Fin.castSucc Fin.castSucc).det := by
  simp only [Formalism.MainNotions.S.Dl, Formalism.MainNotions.S.leadMinorE]
  rw [dif_pos (Nat.le_succ r)]
  rfl

theorem a_gram_det {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    (Matrix.of fun i j : Fin (r + 1) ⊕ Fin (r + 1) =>
      S.hT.flip (Sum.elim (frame F) (frame F') i) (Sum.elim (frame F) (frame F') j)).det =
      (-1) ^ (r + 1) * Gval F F' := by
  have h := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.gramDetGen E r (ZhatL F F').transpose
    ((starRingEnd E).mapMatrix (ZhatL F F')) T T'
  have hM : (Matrix.of fun i j : Fin (r + 1) ⊕ Fin (r + 1) =>
      S.hT.flip (Sum.elim (frame F) (frame F') i) (Sum.elim (frame F) (frame F') j)) =
      Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -T else 0)
        ((starRingEnd E).mapMatrix (ZhatL F F')) (ZhatL F F').transpose
        (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.of_apply, Sum.elim_inl, LinearMap.flip_apply, Matrix.fromBlocks_apply₁₁]
      exact a_gram_self F i j
    · simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, LinearMap.flip_apply,
        Matrix.fromBlocks_apply₁₂, RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [a_herm]
      rfl
    · simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, LinearMap.flip_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
      rfl
    · simp only [Matrix.of_apply, Sum.elim_inr, LinearMap.flip_apply, Matrix.fromBlocks_apply₂₂]
      exact a_gram_self F' i j
  rw [hM, h, Matrix.det_transpose, ← RingHom.map_det]
  have h1 : ((ZhatL F F').transpose.submatrix Fin.castSucc Fin.castSucc).det = Dr F F' := by
    rw [a_Dr, ← Matrix.transpose_submatrix, Matrix.det_transpose]
  have h2 : (((starRingEnd E).mapMatrix (ZhatL F F')).submatrix Fin.castSucc Fin.castSucc).det =
      star (Dr F F') := by
    rw [a_Dr, RingHom.mapMatrix_apply, Matrix.submatrix_map, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
    rfl
  rw [h1, h2, ← discriminant_eq_det_lift_alt]
  simp only [Formalism.MainNotions.S.Gflag, starRingEnd_apply]
  ring

theorem a_span_frame {T : E} (F : LFlag S r T) :
    Submodule.span E (Set.range (frame F)) = Xplus F := by
  have h : Set.range (frame F) = Set.range F.fl.e ∪ {F.fl.z} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.lastCases with
      | last => right; rw [a_frame_last]; rfl
      | cast i => left; exact ⟨i, (a_frame_castSucc F i).symm⟩
    · rintro (⟨i, rfl⟩ | h)
      · exact ⟨i.castSucc, a_frame_castSucc F i⟩
      · exact ⟨Fin.last r, by rw [a_frame_last]; exact h.symm⟩
  rw [h, Submodule.span_union]
  rfl

theorem a_span_two {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    Submodule.span E (Set.range (Sum.elim (frame F) (frame F'))) = U2 F F' := by
  rw [Set.Sum.elim_range, Submodule.span_union, a_span_frame, a_span_frame]
  rfl

theorem a_gramNondeg {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hG : Gval F F' ≠ 0) :
    LinearIndependent E (Sum.elim (frame F) (frame F')) ∧
      finrank E (Submodule.span E (Set.range (Sum.elim (frame F) (frame F')))) =
        Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) ∧
      (∀ x ∈ Submodule.span E (Set.range (Sum.elim (frame F) (frame F'))),
        (∀ y ∈ Submodule.span E (Set.range (Sum.elim (frame F) (frame F'))),
          S.hT.flip y x = 0) → x = 0) ∧
      (∀ x ∈ Submodule.span E (Set.range (Sum.elim (frame F) (frame F'))),
        (∀ y ∈ Submodule.span E (Set.range (Sum.elim (frame F) (frame F'))),
          S.hT.flip x y = 0) → x = 0) :=
  Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.gramNondeg E S.V (Fin (r + 1) ⊕ Fin (r + 1)) (starRingEnd E) S.hT.flip
    (Sum.elim (frame F) (frame F'))
    (by rw [a_gram_det]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hG)

theorem a_HInd {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hG : Gval F F' ≠ 0) :
    HInd F F' := (a_gramNondeg F F' hG).1

theorem finrank_double_span {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hG : Gval F F' ≠ 0) :
    finrank E (U2 F F') = 2 * (r + 1) := by
  have h := (a_gramNondeg F F' hG).2.1
  rw [a_span_two] at h
  rw [h, Fintype.card_sum, Fintype.card_fin, two_mul]

theorem a_HNd {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hG : Gval F F' ≠ 0) :
    HNd F F' := by
  unfold HNd
  rw [eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  have h := (a_gramNondeg F F' hG).2.2.2 x (by rw [a_span_two]; exact hx) (fun y hy => by
    rw [a_span_two] at hy
    exact (a_mem_orth _ _).1 hx' y hy)
  simpa using h

theorem a_coef_zero {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'} (hI : HInd F F')
    {c c' : E} {x x' : S.V} (hx : x ∈ Xsp F) (hx' : x' ∈ Xsp F')
    (h : (c • F.fl.z + x) + (c' • F'.fl.z + x') = 0) : c = 0 ∧ c' = 0 := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  obtain ⟨a', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx'
  have key := Fintype.linearIndependent_iff.1 hI
    (Sum.elim (Fin.snoc (α := fun _ => E) a c) (Fin.snoc (α := fun _ => E) a' c')) (by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, a_frame_castSucc, a_frame_last]
      rw [← h]
      abel)
  exact ⟨by simpa using key (Sum.inl (Fin.last r)), by simpa using key (Sum.inr (Fin.last r))⟩

theorem a_e_X {T : E} (F : LFlag S r T) (a : Fin r) : Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a)) :=
  Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact F.fl.e_iso a b)

theorem a_X_X {T : E} (F : LFlag S r T) {x' : S.V} (hx' : x' ∈ Xsp F) :
    Xsp F ≤ LinearMap.ker (S.hT x') :=
  Submodule.span_le.2 (by
    rintro _ ⟨a, rfl⟩
    show S.hT x' (F.fl.e a) = 0
    rw [a_herm, show S.hT (F.fl.e a) x' = 0 from a_e_X F a hx', star_zero])

theorem a_z_X {T : E} (F : LFlag S r T) : Xsp F ≤ LinearMap.ker (S.hT F.fl.z) :=
  Submodule.span_le.2 (by
    rintro _ ⟨a, rfl⟩
    show S.hT F.fl.z (F.fl.e a) = 0
    rw [a_herm, F.fl.z_orth, star_zero])

theorem a_X_le_orth_Xplus {T : E} (F : LFlag S r T) : Xsp F ≤ orth S (Xplus F) := by
  intro ξ hξ
  rw [a_mem_orth]
  intro w hw
  obtain ⟨x, hx, u, hu, rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
  have h1 : S.hT x ξ = 0 := a_X_X F hx hξ
  have h2 : S.hT F.fl.z ξ = 0 := a_z_X F hξ
  simp [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, h1, h2]

theorem flag_span_le_double_span {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Xsp F ≤ U2 F F' :=
  le_trans le_sup_left (le_sup_left : Xplus F ≤ U2 F F')

theorem second_flag_span_le_double_span {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Xsp F' ≤ U2 F F' :=
  le_trans le_sup_left (le_sup_right : Xplus F' ≤ U2 F F')

theorem lemma_two_unique_pair (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z)
    (hG : Gval F F' ≠ 0) :
    ∀ y ∈ Ylift Λ F F', ∀ y' ∈ Ylift' Λ F F', ∃! p : E × E, SgRel F F' y y' p.1 p.2 := by
  intro y hy y' hy'
  have hU : UUE Λ F F' = U2 F F' := a_HU Λ hΛ F F' hz hz'
  have hd : y - y' ∈ U2 F F' := by rw [← hU]; exact Submodule.sub_mem _ hy.1 hy'.1
  obtain ⟨A, hA, A', hA', hAA⟩ := Submodule.mem_sup.1 hd
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.1 hA
  obtain ⟨x', hx', w', hw', rfl⟩ := Submodule.mem_sup.1 hA'
  obtain ⟨al, rfl⟩ := Submodule.mem_span_singleton.1 hw
  obtain ⟨al', rfl⟩ := Submodule.mem_span_singleton.1 hw'
  refine ⟨(al, al'), ⟨x, hx, x', hx', ?_⟩, ?_⟩
  · rw [hz, hz', ← hAA]; abel
  · rintro ⟨bl, bl'⟩ ⟨u, hu, u', hu', h⟩
    simp only at h
    rw [hz, hz', ← hAA] at h
    have h0 := a_coef_zero (a_HInd F F' hG) (c := bl - al) (c' := bl' - al') (x := u - x)
      (x' := u' - x') (Submodule.sub_mem _ hu hx) (Submodule.sub_mem _ hu' hx') (by
        have := sub_eq_zero.2 h.symm
        rw [← this]
        simp only [sub_smul]
        abel)
    ext
    · exact sub_eq_zero.1 h0.1
    · exact sub_eq_zero.1 h0.2

theorem lemma_two_lift_difference (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z)
    (hG : Gval F F' ≠ 0) :
    ∀ y₁ ∈ Ylift Λ F F', ∀ y₂ ∈ Ylift Λ F F', ∀ y₁' ∈ Ylift' Λ F F', ∀ y₂' ∈ Ylift' Λ F F',
      ∀ al al' : E, SgRel F F' y₁ y₁' al al' → SgRel F F' y₂ y₂' al al' →
        y₁ - y₂ ∈ Xsp F ∧ y₁' - y₂' ∈ Xsp F' := by
  intro y₁ h₁ y₂ h₂ y₁' h₁' y₂' h₂' al al' ⟨x₁, hx₁, x₁', hx₁', e₁⟩ ⟨x₂, hx₂, x₂', hx₂', e₂⟩
  have hU : UUE Λ F F' = U2 F F' := a_HU Λ hΛ F F' hz hz'
  have hw' : (y₁ - y₂) - (x₁ - x₂) = (y₁' - y₂') + (x₁' - x₂') := by
    have e : (y₁ - y₁') - (y₂ - y₂') = ((al • F.zt + x₁) + (al' • F'.zt + x₁')) -
        ((al • F.zt + x₂) + (al' • F'.zt + x₂')) := by rw [e₁, e₂]
    rw [← sub_eq_zero] at e ⊢
    rw [← e]
    abel
  have hX := Submodule.sub_mem _ hx₁ hx₂
  have hX' := Submodule.sub_mem _ hx₁' hx₂'
  have hwU : (y₁ - y₂) - (x₁ - x₂) ∈ U2 F F' :=
    Submodule.sub_mem _ (by rw [← hU]; exact Submodule.sub_mem _ h₁.1 h₂.1) (flag_span_le_double_span F F' hX)
  have ho1 : (y₁ - y₂) - (x₁ - x₂) ∈ orth S (Xplus F) :=
    Submodule.sub_mem _ (Submodule.sub_mem _ h₁.2 h₂.2) (a_X_le_orth_Xplus F hX)
  have ho2 : (y₁ - y₂) - (x₁ - x₂) ∈ orth S (Xplus F') := by
    rw [hw']
    exact Submodule.add_mem _ (Submodule.sub_mem _ h₁'.2 h₂'.2) (a_X_le_orth_Xplus F' hX')
  have hwo : (y₁ - y₂) - (x₁ - x₂) ∈ orth S (U2 F F') := by
    rw [a_mem_orth]
    intro u hu
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.1 hu
    rw [map_add, LinearMap.add_apply, (a_mem_orth _ _).1 ho1 a ha, (a_mem_orth _ _).1 ho2 a' ha',
      add_zero]
  have hNd : U2 F F' ⊓ orth S (U2 F F') = ⊥ := a_HNd F F' hG
  have h0 : (y₁ - y₂) - (x₁ - x₂) = 0 := by
    have : (y₁ - y₂) - (x₁ - x₂) ∈ U2 F F' ⊓ orth S (U2 F F') := ⟨hwU, hwo⟩
    rw [hNd] at this
    simpa using this
  constructor
  · rw [sub_eq_zero.1 h0]; exact hX
  · rw [hw'] at h0
    rw [eq_neg_of_add_eq_zero_left h0]
    exact Submodule.neg_mem _ hX'

theorem a_frame_indep {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hI : HInd F F') :
    LinearIndependent E (frame F) ∧ LinearIndependent E (frame F') := by
  constructor
  · have := hI.comp Sum.inl Sum.inl_injective
    rwa [Sum.elim_comp_inl] at this
  · have := hI.comp Sum.inr Sum.inr_injective
    rwa [Sum.elim_comp_inr] at this

theorem a_finrank_Xplus {T : E} (F : LFlag S r T) (hI : LinearIndependent E (frame F)) :
    finrank E (Xplus F) = r + 1 := by
  rw [← a_span_frame, finrank_span_eq_card hI, Fintype.card_fin]

theorem double_span_orth_decomposition {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hG : Gval F F' ≠ 0)
    (u : S.V) (hu : u ∈ U2 F F') :
    ∃ p ∈ U2 F F' ⊓ orth S (Xplus F), ∃ p' ∈ U2 F F' ⊓ orth S (Xplus F'), u = p + p' := by
  have hgn := a_gramNondeg F F' hG
  rw [a_span_two] at hgn
  have hI := a_frame_indep F F' hgn.1
  have hle : Xplus F ≤ U2 F F' := le_sup_left
  have hle' : Xplus F' ≤ U2 F F' := le_sup_right
  have key := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.perpCompl E (U2 F F') (starRingEnd E)
    (fun x => starRingEnd_self_apply x) (S.hT.flip.domRestrict₁₂ (U2 F F') (U2 F F'))
    (fun x hx => Subtype.ext (hgn.2.2.1 x x.2 (fun y hy => hx ⟨y, hy⟩)))
    (fun x hx => Subtype.ext (hgn.2.2.2 x x.2 (fun y hy => hx ⟨y, hy⟩)))
    r ((Xplus F).comap (U2 F F').subtype) ((Xplus F').comap (U2 F F').subtype)
    (finrank_double_span F F' hG)
    (by rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq, a_finrank_Xplus F hI.1])
    (by rw [(Submodule.comapSubtypeEquivOfLe hle').finrank_eq, a_finrank_Xplus F' hI.2])
    (by
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ _
      obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.1 hx
      exact Submodule.mem_sup.2 ⟨⟨a, hle ha⟩, ha, ⟨a', hle' ha'⟩, ha', rfl⟩)
  have htop : (⟨u, hu⟩ : U2 F F') ∈ Formalism.HermitianLatticeCounting.LocalIntegralStructure.perpR (S.hT.flip.domRestrict₁₂ (U2 F F') (U2 F F'))
      ((Xplus F).comap (U2 F F').subtype) ⊔
      Formalism.HermitianLatticeCounting.LocalIntegralStructure.perpR (S.hT.flip.domRestrict₁₂ (U2 F F') (U2 F F'))
      ((Xplus F').comap (U2 F F').subtype) := by
    rw [key.2.2.sup_eq_top]; trivial
  obtain ⟨p, hp, p', hp', hpp⟩ := Submodule.mem_sup.1 htop
  refine ⟨p, ⟨p.2, ?_⟩, p', ⟨p'.2, ?_⟩, ?_⟩
  · refine (a_mem_orth _ _).2 ?_
    intro a ha
    have := (Submodule.mem_iInf _).1 hp ⟨⟨a, hle ha⟩, ha⟩
    have h2 : S.hT (p : S.V) a = 0 := this
    rw [a_herm, h2, star_zero]
  · refine (a_mem_orth _ _).2 ?_
    intro a ha
    have := (Submodule.mem_iInf _).1 hp' ⟨⟨a, hle' ha⟩, ha⟩
    have h2 : S.hT (p' : S.V) a = 0 := this
    rw [a_herm, h2, star_zero]
  · exact (congrArg Subtype.val hpp).symm

theorem lemma_two_exists_lifts (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z)
    (hG : Gval F F' ≠ 0) :
    ∀ al al' : E, ∃ y ∈ Ylift Λ F F', ∃ y' ∈ Ylift' Λ F F', SgRel F F' y y' al al' := by
  intro al al'
  have hU : UUE Λ F F' = U2 F F' := a_HU Λ hΛ F F' hz hz'
  have hzU : F.fl.z ∈ U2 F F' :=
    (le_sup_left : Xplus F ≤ U2 F F') (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hzU' : F'.fl.z ∈ U2 F F' :=
    (le_sup_right : Xplus F' ≤ U2 F F')
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  obtain ⟨p, hp, p', hp', hpp⟩ := double_span_orth_decomposition F F' hG (al • F.fl.z + al' • F'.fl.z)
    (Submodule.add_mem _ (Submodule.smul_mem _ _ hzU) (Submodule.smul_mem _ _ hzU'))
  refine ⟨p, ?_, -p', ?_, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _, ?_⟩
  · unfold Ylift; rw [hU]; exact hp
  · unfold Ylift'; rw [hU]; exact Submodule.neg_mem _ hp'
  · rw [hz, hz', sub_neg_eq_add, ← hpp]; abel

theorem a_orth_of_frame {ι : Type} (v : ι → S.V) (w : S.V) (h : ∀ i, S.hT (v i) w = 0) :
    w ∈ orth S (Submodule.span E (Set.range v)) := by
  rw [a_mem_orth]
  intro y hy
  have hle : Submodule.span E (Set.range v) ≤ LinearMap.ker (S.hT w) :=
    Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      show S.hT w (v i) = 0
      rw [a_herm, h i, star_zero])
  rw [a_herm, show S.hT w y = 0 from hle hy, star_zero]

theorem double_span_is_compl_orth {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hG : Gval F F' ≠ 0) :
    IsCompl (U2 F F') (orth S (U2 F F')) := by
  refine ⟨disjoint_iff.2 (a_HNd F F' hG), codisjoint_iff.2 ?_⟩
  rw [eq_top_iff]
  intro x _
  set v := Sum.elim (frame F) (frame F') with hv
  set M : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.of fun i j => S.hT (v i) (v j) with hM
  have hdet : IsUnit M.det := by
    have h1 : M = (Matrix.of fun i j : Fin (r + 1) ⊕ Fin (r + 1) =>
      S.hT.flip (v i) (v j)).transpose := by
      ext i j; rfl
    rw [h1, Matrix.det_transpose, hv, a_gram_det]
    exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hG).isUnit
  set b : Fin (r + 1) ⊕ Fin (r + 1) → E := fun i => S.hT (v i) x with hb
  set c := M⁻¹.mulVec b with hc
  have hMc : M.mulVec c = b := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hu : (∑ j, c j • v j) ∈ U2 F F' := by
    rw [← a_span_two]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hw : x - ∑ j, c j • v j ∈ orth S (U2 F F') := by
    rw [← a_span_two]
    apply a_orth_of_frame
    intro i
    rw [map_sub, map_sum]
    have : ∑ j, S.hT (v i) (c j • v j) = M.mulVec c i := by
      simp only [Matrix.mulVec, dotProduct, hM, Matrix.of_apply, map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [this, hMc]
    exact sub_self _
  have : x = (∑ j, c j • v j) + (x - ∑ j, c j • v j) := by abel
  rw [this]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hu) (Submodule.mem_sup_right hw)

theorem a_rankHp (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z)
    (hG : Gval F F' ≠ 0) :
    finrank E (Hp Λ F F') + (2 * r + 2) = finrank E S.V := by
  have hU : UUE Λ F F' = U2 F F' := a_HU Λ hΛ F F' hz hz'
  have h := Submodule.finrank_add_eq_of_isCompl (double_span_is_compl_orth F F' hG)
  unfold Hp
  rw [hU, ← h, finrank_double_span F F' hG]
  ring

theorem a_rankHp_k (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z)
    (hG : Gval F F' ≠ 0) (k : ℕ) (hV : finrank E S.V = k + 2 * r + 1) :
    finrank E (Hp Λ F F') = k - 1 := by
  have h := a_rankHp Λ hΛ F F' hz hz' hG
  omega

theorem a_disj {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'} (hI : HInd F F') :
    Xplus F ⊓ Xplus F' = ⊥ := by
  have h := LinearIndependent.disjoint_span_image hI (s := Set.range Sum.inl)
    (t := Set.range Sum.inr) Set.isCompl_range_inl_range_inr.disjoint
  rw [← Set.range_comp, ← Set.range_comp, Sum.elim_comp_inl, Sum.elim_comp_inr, a_span_frame,
    a_span_frame] at h
  exact disjoint_iff.1 h

theorem a_X_le {Λ : Submodule (𝓞 E) S.V} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}
    (hU : HU Λ F F') : Xsp F ≤ UUE Λ F F' ∧ Xsp F' ≤ UUE Λ F F' := by
  unfold HU at hU
  rw [hU]
  exact ⟨flag_span_le_double_span F F', second_flag_span_le_double_span F F'⟩

end A

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section B

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem b_herm (x y : S.V) : S.hT y x = star (S.hT x y) := by
  rw [← starRingEnd_apply]
  exact (S.herm.eq x y).symm

theorem b_mem_orth {U : Submodule E S.V} {y : S.V} :
    y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem b_span {T : E} (F : LFlag S r T) {v : S.V} (h : ∀ a, S.hT (F.fl.e a) v = 0)
    {x : S.V} (hx : x ∈ Xsp F) : S.hT x v = 0 ∧ S.hT v x = 0 := by
  have h1 : Xsp F ≤ LinearMap.ker (S.hT v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    show S.hT v (F.fl.e a) = 0
    rw [b_herm, h a, star_zero]
  have h2 : S.hT v x = 0 := h1 hx
  exact ⟨by rw [b_herm, h2, star_zero], h2⟩

theorem b_X_X {T : E} (F : LFlag S r T) {x x' : S.V} (hx : x ∈ Xsp F) (hx' : x' ∈ Xsp F) :
    S.hT x x' = 0 :=
  (b_span F (fun a => (b_span F (fun b => F.fl.e_iso b a) hx').2) hx).1

theorem flag_span_orth_normal {T : E} (F : LFlag S r T) {x : S.V} (hx : x ∈ Xsp F) :
    S.hT x F.fl.z = 0 ∧ S.hT F.fl.z x = 0 := b_span F F.fl.z_orth hx

theorem b_X_le_orth {T : E} (F : LFlag S r T) : Xsp F ≤ orth S (Xplus F) := by
  intro x hx
  rw [b_mem_orth]
  intro u hu
  obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Submodule.mem_sup.1 hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu2
  simp [b_X_X F hu1 hx, (flag_span_orth_normal F hx).2]

theorem b_AA {T : E} (F : LFlag S r T) {x : S.V} (hx : x ∈ Xsp F) (al : E) :
    S.hT (al • F.fl.z + x) (al • F.fl.z + x) = -(T * (star al * al)) := by
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    b_X_X F hx hx, (flag_span_orth_normal F hx).1, (flag_span_orth_normal F hx).2, F.fl.z_norm, starRingEnd_apply, RingHom.id_apply]
  ring

theorem b_A_mem {T : E} (F : LFlag S r T) {x : S.V} (hx : x ∈ Xsp F) (al : E) :
    al • F.fl.z + x ∈ Xplus F :=
  Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    (Submodule.mem_sup_left hx)

theorem b_iv_E {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z)
    (hz' : F'.zt = F'.fl.z) {y y' : S.V} (hy : y ∈ orth S (Xplus F)) (hy' : y' ∈ orth S (Xplus F'))
    {al al' : E} (h : SgRel F F' y y' al al') :
    S.hT y y - S.hT y' y' = T * (star al * al) - T' * (star al' * al') := by
  obtain ⟨x, hx, x', hx', e⟩ := h
  rw [hz, hz'] at e
  have h1 : S.hT (al • F.fl.z + x) y = 0 := b_mem_orth.1 hy _ (b_A_mem F hx al)
  have h2 : S.hT y (al • F.fl.z + x) = 0 := by rw [b_herm, h1, star_zero]
  have h3 : S.hT (al' • F'.fl.z + x') y' = 0 := b_mem_orth.1 hy' _ (b_A_mem F' hx' al')
  have h4 : S.hT y' (al' • F'.fl.z + x') = 0 := by rw [b_herm, h3, star_zero]
  have h5 := b_AA F hx al
  have h6 := b_AA F' hx' al'
  generalize al • F.fl.z + x = A at *
  generalize al' • F'.fl.z + x' = A' at *
  have e' : y - A = y' + A' := by rw [sub_eq_iff_eq_add] at e ⊢; rw [e]; abel
  have := congrArg (fun v => S.hT v v) e'
  simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, h1, h2, h3, h4, h5, h6] at this
  linear_combination this

theorem b_tau_norm (hc : StarConj E) (τ : E →+* ℂ) (a : E) :
    τ (star a * a) = ((‖τ a‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_mul, hc, Complex.conj_mul']
  push_cast
  rfl

theorem lemma_two_norm_difference (hc : StarConj E) {T T' : ℕ} (F : LFlag S r (T : E)) (F' : LFlag S r (T' : E))
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (τ : E →+* ℂ) {y y' : S.V}
    (hy : y ∈ orth S (Xplus F)) (hy' : y' ∈ orth S (Xplus F')) {al al' : E}
    (h : SgRel F F' y y' al al') :
    nrm S τ y - nrm S τ y' = (T : ℝ) * ‖τ al‖ ^ 2 - (T' : ℝ) * ‖τ al'‖ ^ 2 := by
  have h1 := congrArg τ (b_iv_E F F' hz hz' hy hy' h)
  rw [map_sub, map_sub, map_mul τ (T : E), map_mul τ (T' : E), b_tau_norm hc, b_tau_norm hc, map_natCast,
    map_natCast] at h1
  have h2 : τ (S.hT y y) - τ (S.hT y' y') =
      (((T : ℝ) * ‖τ al‖ ^ 2 - (T' : ℝ) * ‖τ al'‖ ^ 2 : ℝ) : ℂ) := by
    rw [h1]; push_cast; ring
  have h3 := congrArg Complex.re h2
  rw [Complex.sub_re, Complex.ofReal_re] at h3
  exact h3

theorem b_Zhat_apply {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (a b : Fin (r + 1)) :
    ZhatL F F' a b = S.hT (frame F a) (frame F' b) := rfl

theorem discriminant_eq_det_lift {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Dr1 F F' = (ZhatL F F').det := by
  show Formalism.MainNotions.S.leadMinorE (ZhatL F F') (r + 1) = _
  unfold Formalism.MainNotions.S.leadMinorE
  rw [dif_pos le_rfl]
  congr 1

theorem b_Dr {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    Dr F F' = ((ZhatL F F').submatrix Fin.castSucc Fin.castSucc).det := by
  show Formalism.MainNotions.S.leadMinorE (ZhatL F F') r = _
  unfold Formalism.MainNotions.S.leadMinorE
  rw [dif_pos (Nat.le_succ r)]
  congr 1

theorem b_frame_last {T : E} (F : LFlag S r T) : frame F (Fin.last r) = F.fl.z := by
  simp [Formalism.MainNotions.S.FlagG.fvec]

theorem b_frame_castSucc {T : E} (F : LFlag S r T) (a : Fin r) : frame F a.castSucc = F.fl.e a := by
  simp [Formalism.MainNotions.S.FlagG.fvec]

theorem b_Gval {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    Gval F F' = Dr1 F F' * star (Dr1 F F') - T * T' * (Dr F F' * star (Dr F F')) := rfl

theorem b_tauG (hc : StarConj E) {T T' : ℕ} (F : LFlag S r (T : E)) (F' : LFlag S r (T' : E))
    (τ : E →+* ℂ) :
    τ (Gval F F') = ((‖τ (Dr1 F F')‖ ^ 2 - (T : ℝ) * T' * ‖τ (Dr F F')‖ ^ 2 : ℝ) : ℂ) := by
  rw [b_Gval, map_sub, map_mul τ (_ * _), mul_comm (Dr1 F F'), mul_comm (Dr F F'), b_tau_norm hc,
    b_tau_norm hc, map_mul, map_natCast, map_natCast]
  push_cast
  ring

def b_om {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : S.V :=
  ∑ b, (ZhatL F F').adjugate b (Fin.last r) • frame F' b

theorem b_om_pair {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (a : Fin (r + 1)) :
    S.hT (frame F a) (b_om F F') = if a = Fin.last r then Dr1 F F' else 0 := by
  have h := congrFun (congrFun (Matrix.mul_adjugate (ZhatL F F')) a) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    ← discriminant_eq_det_lift] at h
  rw [← h]
  unfold b_om
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul, b_Zhat_apply, mul_comm]

theorem b_om_eq {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    b_om F F' = Dr F F' • F'.fl.z +
      ∑ b : Fin r, (ZhatL F F').adjugate b.castSucc (Fin.last r) • F'.fl.e b := by
  unfold b_om
  rw [Fin.sum_univ_castSucc, b_frame_last, (Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.cofactorVec E r (ZhatL F F')).2, ← b_Dr,
    add_comm]
  simp only [b_frame_castSucc]

def normalLiftBaseVector {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : S.V :=
  (Dr1 F F' / T) • F.fl.z + b_om F F'

theorem base_vector_mem_orth {T T' : E} (hT : T ≠ 0) (F : LFlag S r T) (F' : LFlag S r T') :
    normalLiftBaseVector F F' ∈ orth S (Xplus F) := by
  have hz : S.hT F.fl.z (normalLiftBaseVector F F') = 0 := by
    have := b_om_pair F F' (Fin.last r)
    rw [b_frame_last, if_pos rfl] at this
    unfold normalLiftBaseVector
    rw [map_add, map_smul, this, F.fl.z_norm, smul_eq_mul]
    field_simp
    ring
  have he : ∀ a, S.hT (F.fl.e a) (normalLiftBaseVector F F') = 0 := by
    intro a
    have := b_om_pair F F' a.castSucc
    rw [b_frame_castSucc, if_neg (Fin.castSucc_lt_last a).ne] at this
    unfold normalLiftBaseVector
    rw [map_add, map_smul, this, F.fl.z_orth a]
    simp
  rw [b_mem_orth]
  intro u hu
  obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Submodule.mem_sup.1 hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu2
  simp [(b_span F he hu1).1, hz]

theorem base_vector_sign_relation {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z)
    (hz' : F'.zt = F'.fl.z) : SgRel F F' (normalLiftBaseVector F F') 0 (Dr1 F F' / T) (Dr F F') := by
  refine ⟨0, Submodule.zero_mem _,
    ∑ b : Fin r, (ZhatL F F').adjugate b.castSucc (Fin.last r) • F'.fl.e b,
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩), ?_⟩
  rw [hz, hz', sub_zero, add_zero, ← b_om_eq]
  rfl

theorem base_vector_norm_eq_gram {T T' : ℕ} (hT : 0 < T) (F : LFlag S r (T : E)) (F' : LFlag S r (T' : E))
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) :
    (T : E) * S.hT (normalLiftBaseVector F F') (normalLiftBaseVector F F') = Gval F F' := by
  have hT' : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne'
  have h := b_iv_E F F' hz hz' (base_vector_mem_orth hT' F F') (Submodule.zero_mem _) (base_vector_sign_relation F F' hz hz')
  rw [map_zero, sub_zero] at h
  rw [h, b_Gval, star_div₀, star_natCast]
  field_simp

theorem b_G_pos (hc : StarConj E) {T T' : ℕ} (hT : 0 < T) (F : LFlag S r (T : E))
    (F' : LFlag S r (T' : E)) (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hG : Gval F F' ≠ 0)
    (hP : PosX F) (τ : E →+* ℂ) : 0 < (τ (Gval F F')).re ∧ (τ (Gval F F')).im = 0 := by
  have hT' : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne'
  refine ⟨?_, by rw [b_tauG hc]; exact Complex.ofReal_im _⟩
  have hn := base_vector_norm_eq_gram hT F F' hz hz'
  have hX : normalLiftBaseVector F F' ∉ Xsp F := by
    intro h
    rw [b_X_X F h h, mul_zero] at hn
    exact hG hn.symm
  have hp := hP τ _ (base_vector_mem_orth hT' F F') hX
  rw [← hn, map_mul, map_natCast, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  exact mul_pos (Nat.cast_pos.2 hT) hp

theorem b_cramer {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z)
    (hz' : F'.zt = F'.fl.z) {y y' : S.V} (hy : y ∈ orth S (Xplus F)) (hy' : y' ∈ Xsp F')
    {al al' : E} (h : SgRel F F' y y' al al') : Dr1 F F' * al' = Dr F F' * (T * al) := by
  obtain ⟨x, hx, x', hx', e⟩ := h
  rw [hz, hz'] at e
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 (Submodule.add_mem _ hx' hy')
  set c' : Fin (r + 1) → E := Fin.snoc (α := fun _ => E) c al' with hc'
  set w : S.V := ∑ b, c' b • frame F' b with hw
  have hw1 : w = al' • F'.fl.z + (x' + y') := by
    rw [hw, Fin.sum_univ_castSucc, b_frame_last, ← hc, add_comm]
    simp [hc', b_frame_castSucc]
  have hyw : y = al • F.fl.z + x + w := by
    rw [hw1]; rw [sub_eq_iff_eq_add] at e; rw [e]; abel
  have hpair : ∀ a, S.hT (frame F a) w = if a = Fin.last r then T * al else 0 := by
    intro a
    refine Fin.lastCases ?_ (fun a => ?_) a
    · rw [if_pos rfl, b_frame_last]
      have h0 : S.hT F.fl.z y = 0 :=
        b_mem_orth.1 hy _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      rw [hyw, map_add, map_add, map_smul, F.fl.z_norm, (flag_span_orth_normal F hx).2, smul_eq_mul] at h0
      linear_combination h0
    · rw [if_neg (Fin.castSucc_lt_last a).ne, b_frame_castSucc]
      have h0 : S.hT (F.fl.e a) y = 0 :=
        b_mem_orth.1 hy _ (Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩))
      rw [hyw, map_add, map_add, map_smul, F.fl.z_orth a,
        b_X_X F (Submodule.subset_span ⟨a, rfl⟩) hx, smul_eq_mul] at h0
      linear_combination h0
  have hpair2 : ∀ a, S.hT (frame F a) w = ∑ b, ZhatL F F' a b * c' b := by
    intro a
    rw [hw, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, smul_eq_mul, b_Zhat_apply, mul_comm]
  have hcof := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.cofactorVec E r (ZhatL F F')
  have h1 : ∑ a, (ZhatL F F').adjugate (Fin.last r) a * S.hT (frame F a) w = Dr F F' * (T * al) := by
    simp only [hpair, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hcof.2, ← b_Dr]
  have h2 : ∑ a, (ZhatL F F').adjugate (Fin.last r) a * S.hT (frame F a) w = Dr1 F F' * al' := by
    simp only [hpair2, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ a, (ZhatL F F').adjugate (Fin.last r) a * (ZhatL F F' a b * c' b) =
        (if b = Fin.last r then (ZhatL F F').det else 0) * c' b := by
      intro b
      rw [← hcof.1 b, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    simp only [this, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [discriminant_eq_det_lift, hc']
    simp
  rw [← h2, h1]

theorem b_nrm_X {T : E} (F : LFlag S r T) (τ : E →+* ℂ) {x : S.V} (hx : x ∈ Xsp F) :
    nrm S τ x = 0 := by
  simp [nrm, b_X_X F hx hx]

theorem lemma_two_norm_scaling (hc : StarConj E) {T T' : ℕ} (hT : 0 < T) (hT' : 0 < T') (F : LFlag S r (T : E))
    (F' : LFlag S r (T' : E)) (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hG : Gval F F' ≠ 0)
    (hP : PosX F) (τ : E →+* ℂ) {y y' : S.V} (hy : y ∈ orth S (Xplus F)) (hy' : y' ∈ Xsp F')
    {al al' : E} (h : SgRel F F' y y' al al') :
    (T : ℝ) * ‖τ al‖ ^ 2 = chSh T T' F F' τ ^ 2 * nrm S τ y ∧
      (T' : ℝ) * ‖τ al'‖ ^ 2 = invSh T T' F F' τ ^ 2 * nrm S τ y := by
  have hn := lemma_two_norm_difference hc F F' hz hz' τ hy (b_X_le_orth F' hy') h
  rw [b_nrm_X F' τ hy', sub_zero] at hn
  have hcr := b_cramer F F' hz hz' hy hy' h
  have hTr : (0 : ℝ) < T := Nat.cast_pos.2 hT
  have hTr' : (0 : ℝ) < T' := Nat.cast_pos.2 hT'
  by_cases hD : Dr F F' = 0
  · have hD1 : Dr1 F F' ≠ 0 := by
      intro h1
      apply hG
      rw [b_Gval, h1, hD]
      simp
    have hal : al' = 0 := by
      rw [hD, zero_mul] at hcr
      exact (mul_eq_zero.1 hcr).resolve_left hD1
    simp only [chSh, invSh, if_pos hD]
    rw [hn, hal]
    simp
  · have hd : 0 < ‖τ (Dr F F')‖ := norm_pos_iff.2 ((map_ne_zero τ).2 hD)
    have hcr' : ‖τ (Dr1 F F')‖ * ‖τ al'‖ = ‖τ (Dr F F')‖ * ((T : ℝ) * ‖τ al‖) := by
      have := congrArg (fun v => ‖τ v‖) hcr
      simpa [map_mul, norm_mul] using this
    have hGp := (b_G_pos hc hT F F' hz hz' hG hP τ).1
    rw [b_tauG hc, Complex.ofReal_re] at hGp
    have hch : ch T T' F F' τ ^ 2 =
        ‖τ (Dr1 F F')‖ ^ 2 / (‖τ (Dr F F')‖ ^ 2 * ((T : ℝ) * T')) := by
      unfold ch
      rw [map_div₀, norm_div, div_pow, div_pow, Real.sq_sqrt (by positivity), div_div]
    have h1 : 1 < ch T T' F F' τ ^ 2 := by
      rw [hch, lt_div_iff₀ (by positivity)]
      linarith
    have hsh : sh T T' F F' τ ^ 2 = ch T T' F F' τ ^ 2 - 1 := by
      unfold sh
      exact Real.sq_sqrt (by linarith)
    have key : (T : ℝ) * ‖τ al‖ ^ 2 = ch T T' F F' τ ^ 2 * ((T' : ℝ) * ‖τ al'‖ ^ 2) := by
      have ha : ‖τ al‖ = ‖τ (Dr1 F F')‖ * ‖τ al'‖ / (‖τ (Dr F F')‖ * T) := by
        rw [eq_div_iff (by positivity)]
        linarith
      rw [hch, ha]
      field_simp
    have hne : ch T T' F F' τ ^ 2 - 1 ≠ 0 := by linarith
    simp only [chSh, invSh, if_neg hD]
    rw [div_pow, div_pow, one_pow, hsh, hn, key]
    constructor
    · field_simp
    · field_simp

theorem b_sg_symm {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') {y y' : S.V} {al al' : E}
    (h : SgRel F F' y y' al al') : SgRel F' F y' y (-al') (-al) := by
  obtain ⟨x, hx, x', hx', e⟩ := h
  refine ⟨-x', Submodule.neg_mem _ hx', -x, Submodule.neg_mem _ hx, ?_⟩
  rw [← neg_sub y y', e, neg_smul, neg_smul]
  abel

theorem b_Zhat_symm {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    ZhatL F' F = (ZhatL F F').conjTranspose := by
  ext a b
  rw [Matrix.conjTranspose_apply, b_Zhat_apply, b_Zhat_apply, b_herm]

theorem discriminant_conj_symm {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    Dr1 F' F = star (Dr1 F F') := by
  rw [discriminant_eq_det_lift, discriminant_eq_det_lift, b_Zhat_symm, Matrix.det_conjTranspose]

theorem b_Dr_symm {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    Dr F' F = star (Dr F F') := by
  rw [b_Dr, b_Dr, b_Zhat_symm, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]

theorem b_Gval_symm {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    Gval F' F = Gval F F' := by
  rw [b_Gval, b_Gval, discriminant_conj_symm, b_Dr_symm, star_star, star_star]
  ring

theorem b_norm_star (hc : StarConj E) (τ : E →+* ℂ) (x : E) : ‖τ (star x)‖ = ‖τ x‖ := by
  rw [hc, RCLike.norm_conj]

theorem b_ch_symm (hc : StarConj E) {T T' : ℕ} (F : LFlag S r (T : E)) (F' : LFlag S r (T' : E))
    (τ : E →+* ℂ) : ch T' T F' F τ = ch T T' F F' τ := by
  unfold ch
  rw [discriminant_conj_symm, b_Dr_symm, ← star_div₀, b_norm_star hc, mul_comm]

theorem b_sh_symm (hc : StarConj E) {T T' : ℕ} (F : LFlag S r (T : E)) (F' : LFlag S r (T' : E))
    (τ : E →+* ℂ) : sh T' T F' F τ = sh T T' F F' τ := by
  unfold sh
  rw [b_ch_symm hc]

theorem b_Dr_zero_symm {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    Dr F' F = 0 ↔ Dr F F' = 0 := by
  rw [b_Dr_symm, star_eq_zero]

theorem b_chSh_symm (hc : StarConj E) {T T' : ℕ} (F : LFlag S r (T : E)) (F' : LFlag S r (T' : E))
    (τ : E →+* ℂ) : chSh T' T F' F τ = chSh T T' F F' τ := by
  unfold chSh
  rw [b_ch_symm hc F F', b_sh_symm hc F F']
  by_cases h : Dr F F' = 0
  · rw [if_pos h, if_pos ((b_Dr_zero_symm F F').2 h)]
  · rw [if_neg h, if_neg (fun h' => h ((b_Dr_zero_symm F F').1 h'))]

theorem b_invSh_symm (hc : StarConj E) {T T' : ℕ} (F : LFlag S r (T : E)) (F' : LFlag S r (T' : E))
    (τ : E →+* ℂ) : invSh T' T F' F τ = invSh T T' F F' τ := by
  unfold invSh
  rw [b_sh_symm hc F F']
  by_cases h : Dr F F' = 0
  · rw [if_pos h, if_pos ((b_Dr_zero_symm F F').2 h)]
  · rw [if_neg h, if_neg (fun h' => h ((b_Dr_zero_symm F F').1 h'))]

theorem lemma_two_norm_scaling_right (hc : StarConj E) {T T' : ℕ} (hT : 0 < T) (hT' : 0 < T') (F : LFlag S r (T : E))
    (F' : LFlag S r (T' : E)) (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hG : Gval F F' ≠ 0)
    (hP' : PosX F') (τ : E →+* ℂ) {y y' : S.V} (hy : y ∈ Xsp F) (hy' : y' ∈ orth S (Xplus F'))
    {al al' : E} (h : SgRel F F' y y' al al') :
    (T : ℝ) * ‖τ al‖ ^ 2 = invSh T T' F F' τ ^ 2 * nrm S τ y' ∧
      (T' : ℝ) * ‖τ al'‖ ^ 2 = chSh T T' F F' τ ^ 2 * nrm S τ y' := by
  have h1 := lemma_two_norm_scaling hc hT' hT F' F hz' hz (by rw [b_Gval_symm]; exact hG) hP' τ hy' hy
    (b_sg_symm F F' h)
  rw [map_neg, map_neg, norm_neg, norm_neg, b_chSh_symm hc, b_invSh_symm hc] at h1
  exact ⟨h1.2, h1.1⟩

theorem b_ch_sh_one (hc : StarConj E) {T T' : ℕ} (hT : 0 < T) (hT' : 0 < T') (F : LFlag S r (T : E))
    (F' : LFlag S r (T' : E)) (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hG : Gval F F' ≠ 0)
    (hP : PosX F) (τ : E →+* ℂ) : chSh T T' F F' τ ^ 2 - invSh T T' F F' τ ^ 2 = 1 := by
  have hTE : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne'
  have hy := base_vector_mem_orth (T' := (T' : E)) hTE F F'
  have hs := base_vector_sign_relation F F' hz hz'
  have h5 := lemma_two_norm_scaling hc hT hT' F F' hz hz' hG hP τ hy (Submodule.zero_mem _) hs
  have h4 := lemma_two_norm_difference hc F F' hz hz' τ hy (Submodule.zero_mem _) hs
  have hX : normalLiftBaseVector F F' ∉ Xsp F := by
    intro h
    have hn := base_vector_norm_eq_gram hT F F' hz hz'
    rw [b_X_X F h h, mul_zero] at hn
    exact hG hn.symm
  have hp := hP τ _ hy hX
  have h0 : nrm S τ (0 : S.V) = 0 := by simp [nrm]
  rw [h0, sub_zero, h5.1, h5.2, ← sub_mul] at h4
  have h6 : 1 * nrm S τ (normalLiftBaseVector F F') =
      (chSh T T' F F' τ ^ 2 - invSh T T' F F' τ ^ 2) * nrm S τ (normalLiftBaseVector F F') := by
    rw [one_mul]; exact h4
  exact (mul_right_cancel₀ hp.ne' h6).symm

end B

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lemma_two_norm_identities (D : D7) (u : D.what₂.Word) (T' : ℕ) (Λ : VanishingOnXAndXPlusGluing.LatS D) (F : VanishingOnXAndXPlusGluing.FlS D (Tu D u))
    (F' : VanishingOnXAndXPlusGluing.FlS D T') (hF : FixedHyp D Λ F) (hPr : PrimeHyp D u T') (hT : IsTerm Λ (gS D) F F') :
    (∀ τ : D.host.E →+* ℂ, ∀ y ∈ Ylift Λ F F', ∀ y' ∈ Ylift' Λ F F', ∀ al al' : D.host.E,
      SgRel F F' y y' al al' →
        nrm (hS D) τ y - nrm (hS D) τ y' =
          ((Tu D u : ℕ) : ℝ) * ‖τ al‖ ^ 2 - (T' : ℝ) * ‖τ al'‖ ^ 2) ∧
    (∀ τ : D.host.E →+* ℂ, ∀ y ∈ Ylift Λ F F', ∀ y' ∈ Xsp F', ∀ al al' : D.host.E,
      SgRel F F' y y' al al' →
        ((Tu D u : ℕ) : ℝ) * ‖τ al‖ ^ 2 = chSh (Tu D u) T' F F' τ ^ 2 * nrm (hS D) τ y ∧
        (T' : ℝ) * ‖τ al'‖ ^ 2 = invSh (Tu D u) T' F F' τ ^ 2 * nrm (hS D) τ y) ∧
    (∀ τ : D.host.E →+* ℂ, ∀ y ∈ Xsp F, ∀ y' ∈ Ylift' Λ F F', ∀ al al' : D.host.E,
      SgRel F F' y y' al al' →
        ((Tu D u : ℕ) : ℝ) * ‖τ al‖ ^ 2 = invSh (Tu D u) T' F F' τ ^ 2 * nrm (hS D) τ y' ∧
        (T' : ℝ) * ‖τ al'‖ ^ 2 = chSh (Tu D u) T' F F' τ ^ 2 * nrm (hS D) τ y') := by
  have hc := p_starConj D
  have h0 : 0 < Tu D u := lt_of_lt_of_le (by norm_num) hPr.2.1
  have h0' : 0 < T' := lt_of_lt_of_le (by norm_num) hPr.2.2.2.1
  have hz := hF.2.2.1.2
  have hz' := hT.1.2
  refine ⟨fun τ y hy y' hy' al al' h => lemma_two_norm_difference hc F F' hz hz' τ hy.2 hy'.2 h,
    fun τ y hy y' hy' al al' h =>
      lemma_two_norm_scaling hc h0 h0' F F' hz hz' hT.2.2 (p_posX D _ h0 F) τ hy.2 hy' h,
    fun τ y hy y' hy' al al' h =>
      lemma_two_norm_scaling_right hc h0 h0' F F' hz hz' hT.2.2 (p_posX D _ h0' F') τ hy hy'.2 h⟩

theorem lemma_two_of_three_parts (D : D7) (u : D.what₂.Word) (T' : ℕ) (Λ : VanishingOnXAndXPlusGluing.LatS D) (F : VanishingOnXAndXPlusGluing.FlS D (Tu D u))
    (F' : VanishingOnXAndXPlusGluing.FlS D T') (hF : FixedHyp D Λ F) (hPr : PrimeHyp D u T') (hT : IsTerm Λ (gS D) F F')
    (h1 : ∀ y ∈ Ylift Λ F F', ∀ y' ∈ Ylift' Λ F F',
      ∃! p : D.host.E × D.host.E, SgRel F F' y y' p.1 p.2)
    (h2 : ∀ y₁ ∈ Ylift Λ F F', ∀ y₂ ∈ Ylift Λ F F', ∀ y₁' ∈ Ylift' Λ F F', ∀ y₂' ∈ Ylift' Λ F F',
      ∀ al al' : D.host.E, SgRel F F' y₁ y₁' al al' → SgRel F F' y₂ y₂' al al' →
        y₁ - y₂ ∈ Xsp F ∧ y₁' - y₂' ∈ Xsp F')
    (h3 : ∀ al al' : D.host.E, ∃ y ∈ Ylift Λ F F', ∃ y' ∈ Ylift' Λ F F', SgRel F F' y y' al al') :
    VanishingOnXAndXPlusGluing.Lem2 D Λ (Tu D u) T' F F' :=
  ⟨h1, h2, h3, lemma_two_norm_identities D u T' Λ F F' hF hPr hT⟩

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem m_hadamard (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ j : Fin n, Real.sqrt (∑ i : Fin n, ‖A i j‖ ^ 2) := by
  have h := Formalism.HadamardInequality.P.hadamard_inequality_holds n A.transpose
  rw [Matrix.det_transpose] at h
  simp only [Matrix.transpose_apply] at h
  have h2 : Real.sqrt (‖A.det‖ ^ 2) ≤ Real.sqrt (∏ j : Fin n, ∑ i : Fin n, ‖A i j‖ ^ 2) :=
    Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq (norm_nonneg _)] at h2
  refine h2.trans (le_of_eq ?_)
  have : ∀ s : Finset (Fin n), Real.sqrt (∏ j ∈ s, ∑ i : Fin n, ‖A i j‖ ^ 2) =
      ∏ j ∈ s, Real.sqrt (∑ i : Fin n, ‖A i j‖ ^ 2) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Real.sqrt_mul (by positivity), ih]
  exact this _

theorem gluing_hadamard_inequality : VanishingOnXAndXPlusGlobal.adm2 := m_hadamard

theorem lemma_one_det_index_le_gram (D : D7) (Λ : VanishingOnXAndXPlusGluing.LatS D) (g : ℕ) {T T' : ℕ} (F : VanishingOnXAndXPlusGluing.FlS D T) (F' : VanishingOnXAndXPlusGluing.FlS D T')
    (h : VanishingOnXAndXPlusGluing.Lem1 D Λ g F F') :
    latDet (hS D) (La Λ g F F') * (iIdx Λ g F F' : ℝ) ^ 2 ≤ G0 Λ g F F' := by
  obtain ⟨hfin, h1, h2, h3, -⟩ := h
  have hNG : 0 ≤ NG Λ F F' := Real.sqrt_nonneg _
  have hN : 0 ≤ NE (E := D.host.E) g ^ (D.R.rS + 1) := by unfold NE; positivity
  have hB : 0 < (Nat.card (BQ Λ F F') : ℝ) := by exact_mod_cast Nat.card_pos
  rw [h3]
  unfold G0
  rcases Nat.eq_zero_or_pos (iIdx Λ g F F') with hi | hi
  · rw [hi]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact div_nonneg hNG hN
  · have hi' : 0 < (iIdx Λ g F F' : ℝ) := by exact_mod_cast hi
    have hle : (iIdx Λ g F F' : ℝ) ≤
        (Nat.card (BQ Λ F F') : ℝ) / NE (E := D.host.E) g ^ (D.R.rS + 1) := h1.trans h2
    have hNpos : 0 < NE (E := D.host.E) g ^ (D.R.rS + 1) := by
      rcases hN.lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at hle; linarith
    have e1 : NG Λ F F' / ((Nat.card (BQ Λ F F') : ℝ) * (iIdx Λ g F F' : ℝ)) * (iIdx Λ g F F' : ℝ) ^ 2 =
        NG Λ F F' * ((iIdx Λ g F F' : ℝ) / (Nat.card (BQ Λ F F') : ℝ)) := by
      field_simp
    rw [e1, div_eq_mul_inv (NG Λ F F')]
    apply mul_le_mul_of_nonneg_left _ hNG
    rw [div_le_iff₀ hB]
    calc (iIdx Λ g F F' : ℝ) ≤ _ := hle
      _ = (NE (E := D.host.E) g ^ (D.R.rS + 1))⁻¹ * (Nat.card (BQ Λ F F') : ℝ) := by
        rw [div_eq_mul_inv, mul_comm]

def DetBBound (D : D7) (Λ : VanishingOnXAndXPlusGluing.LatS D) (g : ℕ) {T T' : ℕ} (F : VanishingOnXAndXPlusGluing.FlS D T) (F' F'' : VanishingOnXAndXPlusGluing.FlS D T')
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V) (W : Submodule D.host.E (hS D).V) : Prop :=
  (g : ℝ) ^ (2 * D.R.f * (s0 Λ F F' F'' β D.R.k - 1)) ≤
    4 ^ ((s0 Λ F F' F'' β D.R.k - 1) * D.R.f) *
      latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F')) *
      latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F''))

theorem m_thmA_nondeg (D : D7) (Λ : VanishingOnXAndXPlusGluing.LatS D) (g : ℕ) (hg : 0 < g) {T T' : ℕ} (F : VanishingOnXAndXPlusGluing.FlS D T)
    (F' F'' : VanishingOnXAndXPlusGluing.FlS D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V) (W : Submodule D.host.E (hS D).V)
    (h1 : VanishingOnXAndXPlusGluing.Lem1 D Λ g F F') (h2 : VanishingOnXAndXPlusGluing.Lem1 D Λ g F F'') (hA2 : VanishingOnXAndXPlusGluing.LatticeSpanEquality D Λ g F F' F'' β W)
    (hb : DetBBound D Λ g F F' F'' β W) :
    latDet (hS D) (Mlat Λ F F' F'' β g) * (iIdx Λ g F F' : ℝ) * (iIdx Λ g F F'' : ℝ) ≤
      (2 / (g : ℝ)) ^ ((s0 Λ F F' F'' β D.R.k - 1) * D.R.f) *
        Real.sqrt (G0 Λ g F F' * G0 Λ g F F'') := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have ha : 0 ≤ latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F')) := Real.sqrt_nonneg _
  have hc : 0 ≤ latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F'')) := Real.sqrt_nonneg _
  have hpos : 0 < 4 ^ ((s0 Λ F F' F'' β D.R.k - 1) * D.R.f) *
      latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F')) *
      latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F'')) := lt_of_lt_of_le (by positivity) hb
  have ha' : 0 < latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F')) := by
    rcases ha.lt_or_eq with h | h
    · exact h
    · rw [← h] at hpos; simp at hpos
  have hc' : 0 < latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F'')) := by
    rcases hc.lt_or_eq with h | h
    · exact h
    · rw [← h] at hpos; simp at hpos
  exact Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.arithmetic_square_bound_fourth _ _ _ _ _ _ _ _ _ (g : ℝ) _ _ ha' hc' hg' (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hA2.2.2.2.1
    (lemma_one_det_index_le_gram D Λ g F F' h1) (lemma_one_det_index_le_gram D Λ g F F'' h2) hb

theorem m_thmA_deg (D : D7) (Λ : VanishingOnXAndXPlusGluing.LatS D) (g : ℕ) (hg : 0 < g) {T T' : ℕ} (hT : 0 < T) (F : VanishingOnXAndXPlusGluing.FlS D T)
    (F' F'' : VanishingOnXAndXPlusGluing.FlS D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V) (W : Submodule D.host.E (hS D).V)
    (hA2 : VanishingOnXAndXPlusGluing.LatticeSpanEquality D Λ g F F' F'' β W)
    (hK₁ : ∀ τ : D.host.E →+* ℂ, 0 < onePlusChSh T T' F F' τ)
    (hK₂ : ∀ τ : D.host.E →+* ℂ, 0 < onePlusChSh T T' F F'' τ)
    (P₁ P₂ dQ₁ dQ₂ Nr₁ Nr₂ : ℝ) (hP₁ : 0 < P₁) (hP₂ : 0 < P₂) (hQ₁ : 0 < dQ₁) (hQ₂ : 0 < dQ₂)
    (hN₁ : 0 < Nr₁) (hN₂ : 0 < Nr₂)
    (e₁ : latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F')) = P₁ * dQ₁)
    (e₂ : latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F'')) = P₂ * dQ₂)
    (l₁ : latDet (hS D) (La Λ g F F') * (iIdx Λ g F F' : ℝ) ^ 2 ≤ G0 Λ g F F' / Nr₁)
    (l₂ : latDet (hS D) (La Λ g F F'') * (iIdx Λ g F F'' : ℝ) ^ 2 ≤ G0 Λ g F F'' / Nr₂)
    (p₁ : (T : ℝ) ^ D.R.f / (Nr₂ * placeProd (fun τ : D.host.E →+* ℂ => onePlusChSh T T' F F'' τ) ^ 2) ≤ P₁)
    (p₂ : (T : ℝ) ^ D.R.f / (Nr₁ * placeProd (fun τ : D.host.E →+* ℂ => onePlusChSh T T' F F' τ) ^ 2) ≤ P₂)
    (q : (g : ℝ) ^ (2 * D.R.f * (s0 Λ F F' F'' β D.R.k - 2)) ≤
      4 ^ ((s0 Λ F F' F'' β D.R.k - 2) * D.R.f) * dQ₁ * dQ₂) :
    latDet (hS D) (Mlat Λ F F' F'' β g) * (iIdx Λ g F F' : ℝ) * (iIdx Λ g F F'' : ℝ) ≤
      (2 / (g : ℝ)) ^ ((s0 Λ F F' F'' β D.R.k - 2) * D.R.f) *
        Real.sqrt (G0 Λ g F F' * G0 Λ g F F'') * ((T : ℝ) ^ D.R.f)⁻¹ *
        placeProd (fun τ : D.host.E →+* ℂ => onePlusChSh T T' F F' τ * onePlusChSh T T' F F'' τ) := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hT' : (0 : ℝ) < (T : ℝ) ^ D.R.f := by positivity
  have k₁ : 0 < placeProd (fun τ : D.host.E →+* ℂ => onePlusChSh T T' F F' τ) :=
    Real.sqrt_pos.2 (Finset.prod_pos fun τ _ => hK₁ τ)
  have k₂ : 0 < placeProd (fun τ : D.host.E →+* ℂ => onePlusChSh T T' F F'' τ) :=
    Real.sqrt_pos.2 (Finset.prod_pos fun τ _ => hK₂ τ)
  have hmul : placeProd (fun τ : D.host.E →+* ℂ => onePlusChSh T T' F F' τ * onePlusChSh T T' F F'' τ) =
      placeProd (fun τ : D.host.E →+* ℂ => onePlusChSh T T' F F' τ) *
        placeProd (fun τ : D.host.E →+* ℂ => onePlusChSh T T' F F'' τ) := by
    unfold placeProd
    rw [Finset.prod_mul_distrib, Real.sqrt_mul (Finset.prod_nonneg fun τ _ => (hK₁ τ).le)]
  have h := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.arithmetic_square_bound_fifth _ _ _ _ _ P₁ P₂ dQ₁ dQ₂ _ _ _ _ (g : ℝ) ((T : ℝ) ^ D.R.f) _ _ Nr₁ Nr₂
    (s0 Λ F F' F'' β D.R.k - 2) D.R.f hP₁ hP₂ hQ₁ hQ₂ hg' (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hT' k₁ k₂ hN₁ hN₂ hA2.2.2.2.1 e₁ e₂ l₁ l₂ p₁ p₂ q
  refine h.trans (le_of_eq ?_)
  rw [hmul]
  field_simp

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem m_exists_smul_mem (M : Submodule (𝓞 E) S.V) {x : S.V} (hx : x ∈ Submodule.span E (M : Set S.V)) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact Formalism.MainNotions.LatticeGluingRadicals.m_exists_smul_memL
  | (apply Formalism.MainNotions.LatticeGluingRadicals.m_exists_smul_memL <;> assumption)
  | (intros; apply Formalism.MainNotions.LatticeGluingRadicals.m_exists_smul_memL <;> assumption)
  | (intros; exact Formalism.MainNotions.LatticeGluingRadicals.m_exists_smul_memL ‹_› ‹_›)

theorem m_exists_nat_smul_mem (M : Submodule (𝓞 E) S.V) {x : S.V}
    (hx : x ∈ Submodule.span E (M : Set S.V)) : ∃ n : ℕ, 0 < n ∧ n • x ∈ M := by
  first | exact UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem .. | (apply UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem E ‹_› ‹_› ‹_› S M x hx | exact @UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem E ‹_› ‹_› ‹_› S M x | exact @UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem E ‹_› ‹_› ‹_› S M | exact @UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem E ‹_› ‹_› ‹_› S | exact @UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem E ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem E ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem E ‹_› | exact @UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem E

omit [StarRing E] in

theorem m_fin_quot {M : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    (N : Submodule (𝓞 E) M) (h : ∀ w : M, ∃ n : ℕ, 0 < n ∧ n • w ∈ N) : Finite (M ⧸ N) := by
  have : Module.Finite ℤ (M ⧸ N) := Module.Finite.trans (𝓞 E) _
  apply Module.finite_of_fg_torsion
  intro c
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ c
  obtain ⟨n, hn, hnw⟩ := h w
  refine ⟨⟨(n : ℤ), ?_⟩, ?_⟩
  · rw [mem_nonZeroDivisors_iff_ne_zero]; exact_mod_cast hn.ne'
  · show (n : ℤ) • N.mkQ w = 0
    rw [natCast_zsmul, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hnw

variable (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T')

theorem m_BQ_finite (hΛ : Submodule.IsLattice E Λ) : Finite (BQ Λ F F') := by
  have h1 : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ.fg
  have h2 : IsNoetherian (𝓞 E) Λ := isNoetherian_of_isNoetherianRing_of_finite (𝓞 E) Λ
  have hfg : (BLat Λ F F').FG := (isNoetherian_submodule.1 h2) (BLat Λ F F') inf_le_left
  have h3 : Module.Finite (𝓞 E) (BLat Λ F F') := Module.Finite.iff_fg.2 hfg
  apply m_fin_quot
  intro w
  obtain ⟨n, hn, hnw⟩ := m_exists_nat_smul_mem (UU Λ F F') (x := (w : S.V)) w.2.2
  exact ⟨n, hn, by simpa using hnw⟩

theorem m_i_le_gB (g : ℕ) (hfin : Finite (BQ Λ F F'))
    (φ : (La Λ g F F' ⧸ (Thp Λ F F').comap (La Λ g F F').subtype) →ₗ[𝓞 E] gB Λ g F F')
    (hφ : Function.Injective φ) :
    ((iIdx Λ g F F' : ℕ) : ℝ) ≤ (Nat.card (gB Λ g F F') : ℝ) := by
  have : iIdx Λ g F F' ≤ Nat.card (gB Λ g F F') := Nat.card_le_card_of_injective φ hφ
  exact_mod_cast this

theorem m_gB_card (g : ℕ) :
    Nat.card (gB Λ g F F') = Nat.card (nsmulAddMonoidHom g : BQ Λ F F' →+ BQ Λ F F').range := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  unfold gB
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, by simp [Nat.cast_smul_eq_nsmul]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, trivial, by simp [Nat.cast_smul_eq_nsmul]⟩

theorem m_gB_le (g : ℕ) (hg : 0 < g) (hfin : Finite (BQ Λ F F')) (K : AddSubgroup (BQ Λ F F'))
    (hK : ∀ x ∈ K, g • x = 0) (hc : (Nat.card K : ℝ) = NE (E := E) g ^ (r + 1)) :
    (Nat.card (gB Λ g F F') : ℝ) ≤ (Nat.card (BQ Λ F F') : ℝ) / NE (E := E) g ^ (r + 1) := by
  have h := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.torsionIndex (BQ Λ F F') g K hK
  rw [← m_gB_card] at h
  have hpos : 0 < NE (E := E) g ^ (r + 1) := by
    unfold NE; have : (0 : ℝ) < g := by exact_mod_cast hg
    positivity
  rw [le_div_iff₀ hpos, ← hc]
  exact_mod_cast h

end Gen

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (g : ℕ)

theorem m_La_mem {x : S.V} (hx : x ∈ La Λ g F F') :
    x ∈ Hp Λ F F' ∧ x ∈ L0sub Λ F ∧ x ∈ L0sub Λ F' ∧ IotaRel Λ g F F' x := by
  unfold La at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨zero_mem _, zero_mem _, zero_mem _, 0, zero_mem _, by simp, 0, zero_mem _, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a1, a2, a3, l, hl, hxl, l', hl', hxl', hll⟩ := hx
    obtain ⟨b1, b2, b3, m, hm, hym, m', hm', hym', hmm⟩ := hy
    refine ⟨add_mem a1 b1, add_mem a2 b2, add_mem a3 b3, l + m, add_mem hl hm, ?_, l' + m',
      add_mem hl' hm', ?_, ?_⟩
    · rw [add_sub_add_comm]; exact add_mem hxl hym
    · rw [add_sub_add_comm]; exact add_mem hxl' hym'
    · rw [add_sub_add_comm]; exact add_mem hll hmm
  | smul c x _ hx =>
    obtain ⟨a1, a2, a3, l, hl, hxl, l', hl', hxl', hll⟩ := hx
    refine ⟨(toO S (Hp Λ F F')).smul_mem c a1, Submodule.smul_mem _ c a2, Submodule.smul_mem _ c a3,
      c • l, Submodule.smul_mem _ c hl, ?_, c • l', Submodule.smul_mem _ c hl', ?_, ?_⟩
    · rw [← smul_sub]; exact (toO S (Xsp F)).smul_mem c hxl
    · rw [← smul_sub]; exact (toO S (Xsp F')).smul_mem c hxl'
    · rw [← smul_sub]; exact Submodule.smul_mem _ c hll

def m_Tr : Submodule (𝓞 E) (S.V × S.V × S.V) :=
  (La Λ g F F').comap (LinearMap.fst (𝓞 E) S.V (S.V × S.V)) ⊓
  (Lrep Λ F).comap (LinearMap.fst (𝓞 E) S.V S.V ∘ₗ LinearMap.snd (𝓞 E) S.V (S.V × S.V)) ⊓
  (Lrep Λ F').comap (LinearMap.snd (𝓞 E) S.V S.V ∘ₗ LinearMap.snd (𝓞 E) S.V (S.V × S.V)) ⊓
  (toO S (Xsp F)).comap (LinearMap.fst (𝓞 E) S.V (S.V × S.V) -
    LinearMap.fst (𝓞 E) S.V S.V ∘ₗ LinearMap.snd (𝓞 E) S.V (S.V × S.V)) ⊓
  (toO S (Xsp F')).comap (LinearMap.fst (𝓞 E) S.V (S.V × S.V) -
    LinearMap.snd (𝓞 E) S.V S.V ∘ₗ LinearMap.snd (𝓞 E) S.V (S.V × S.V))

theorem m_mem_Tr {t : S.V × S.V × S.V} : t ∈ m_Tr Λ F F' g ↔
    t.1 ∈ La Λ g F F' ∧ t.2.1 ∈ Lrep Λ F ∧ t.2.2 ∈ Lrep Λ F' ∧ t.1 - t.2.1 ∈ Xsp F ∧
      t.1 - t.2.2 ∈ Xsp F' := by
  simp [m_Tr, Submodule.mem_inf, and_assoc]

variable {Λ F F' g}

theorem m_diff_mem (hX : Xsp F ≤ UUE Λ F F') (hX' : Xsp F' ≤ UUE Λ F F') {x l l' : S.V}
    (hl : l ∈ Lrep Λ F) (hl' : l' ∈ Lrep Λ F') (h : x - l ∈ Xsp F) (h' : x - l' ∈ Xsp F') :
    l - l' ∈ BLat Λ F F' := by
  refine ⟨sub_mem hl.1 hl'.1, ?_⟩
  have : l - l' = (x - l') - (x - l) := by abel
  show l - l' ∈ UUE Λ F F'
  rw [this]
  exact sub_mem (hX' h') (hX h)

def boundaryClassMap (hX : Xsp F ≤ UUE Λ F F') (hX' : Xsp F' ≤ UUE Λ F F') : m_Tr Λ F F' g →ₗ[𝓞 E] BQ Λ F F' :=
  ((UU Λ F F').comap (BLat Λ F F').subtype).mkQ ∘ₗ
    LinearMap.codRestrict (BLat Λ F F')
      ((LinearMap.fst (𝓞 E) S.V S.V ∘ₗ LinearMap.snd (𝓞 E) S.V (S.V × S.V) -
        LinearMap.snd (𝓞 E) S.V S.V ∘ₗ LinearMap.snd (𝓞 E) S.V (S.V × S.V)) ∘ₗ (m_Tr Λ F F' g).subtype)
      (fun t => by
        obtain ⟨-, h2, h3, h4, h5⟩ := (m_mem_Tr Λ F F' g).1 t.2
        exact m_diff_mem hX hX' h2 h3 h4 h5)

def m_pi : m_Tr Λ F F' g →ₗ[𝓞 E] La Λ g F F' :=
  LinearMap.codRestrict (La Λ g F F')
    (LinearMap.fst (𝓞 E) S.V (S.V × S.V) ∘ₗ (m_Tr Λ F F' g).subtype)
    (fun t => ((m_mem_Tr Λ F F' g).1 t.2).1)

theorem m_pi_surj : Function.Surjective (m_pi (Λ := Λ) (F := F) (F' := F') (g := g)) := by
  intro x
  obtain ⟨-, -, -, l, hl, hxl, l', hl', hxl', -⟩ := m_La_mem Λ F F' g x.2
  exact ⟨⟨(x, l, l'), (m_mem_Tr Λ F F' g).2 ⟨x.2, hl, hl', hxl, hxl'⟩⟩, rfl⟩

theorem m_ker_le (hX : Xsp F ≤ UUE Λ F F') (hX' : Xsp F' ≤ UUE Λ F F') :
    LinearMap.ker (m_pi (Λ := Λ) (F := F) (F' := F') (g := g)) ≤ LinearMap.ker (boundaryClassMap hX hX') := by
  intro t ht
  obtain ⟨-, h2, h3, h4, h5⟩ := (m_mem_Tr Λ F F' g).1 t.2
  have h0 : (t : S.V × S.V × S.V).1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 ht)
  rw [h0, zero_sub] at h4 h5
  rw [LinearMap.mem_ker]
  show ((UU Λ F F').comap (BLat Λ F F').subtype).mkQ _ = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  show (t : S.V × S.V × S.V).2.1 - (t : S.V × S.V × S.V).2.2 ∈ UU Λ F F'
  have a1 : (t : S.V × S.V × S.V).2.1 ∈ XLam Λ F := ⟨h2.1, by simpa using (Xsp F).neg_mem h4⟩
  have a2 : (t : S.V × S.V × S.V).2.2 ∈ XLam Λ F' := ⟨h3.1, by simpa using (Xsp F').neg_mem h5⟩
  unfold UU
  refine sub_mem ?_ ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left a1))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right a2)

def m_psi (hX : Xsp F ≤ UUE Λ F F') (hX' : Xsp F' ≤ UUE Λ F F') : La Λ g F F' →ₗ[𝓞 E] BQ Λ F F' :=
  (Submodule.liftQ _ (boundaryClassMap hX hX') (m_ker_le hX hX')) ∘ₗ
    ((m_pi (Λ := Λ) (F := F) (F' := F') (g := g)).quotKerEquivOfSurjective m_pi_surj).symm.toLinearMap

theorem m_psi_pi (hX : Xsp F ≤ UUE Λ F F') (hX' : Xsp F' ≤ UUE Λ F F') (t : m_Tr Λ F F' g) :
    m_psi hX hX' (m_pi t) = boundaryClassMap hX hX' t := by
  have : ((m_pi (Λ := Λ) (F := F) (F' := F') (g := g)).quotKerEquivOfSurjective m_pi_surj).symm (m_pi t) =
      Submodule.Quotient.mk t := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [m_psi, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
  rfl

theorem m_psi_apply (hX : Xsp F ≤ UUE Λ F F') (hX' : Xsp F' ≤ UUE Λ F F') (x : La Λ g F F') {l l' : S.V}
    (hl : l ∈ Lrep Λ F) (hl' : l' ∈ Lrep Λ F') (h : (x : S.V) - l ∈ Xsp F) (h' : (x : S.V) - l' ∈ Xsp F') :
    m_psi hX hX' x = Submodule.Quotient.mk ⟨l - l', m_diff_mem hX hX' hl hl' h h'⟩ :=
  m_psi_pi hX hX' ⟨((x : S.V), l, l'), (m_mem_Tr Λ F F' g).2 ⟨x.2, hl, hl', h, h'⟩⟩

theorem m_psi_mem_gB (hg : 0 < g) (hX : Xsp F ≤ UUE Λ F F') (hX' : Xsp F' ≤ UUE Λ F F')
    (x : La Λ g F F') : m_psi hX hX' x ∈ gB Λ g F F' := by
  obtain ⟨-, -, -, l, hl, hxl, l', hl', hxl', hll⟩ := m_La_mem Λ F F' g x.2
  rw [m_psi_apply hX hX' x hl hl' hxl hxl']
  unfold NgX at hll
  obtain ⟨p, hp, ξ', hξ', e1⟩ := Submodule.mem_sup.1 hll
  obtain ⟨u, hu, ξ, hξ, e2⟩ := Submodule.mem_sup.1 hp
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hu
  obtain ⟨lam, hlam, rfl⟩ := hu
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  have hd := m_diff_mem hX hX' hl hl' hxl hxl'
  have hglam : ((g : 𝓞 E)) • lam ∈ UUE Λ F F' := by
    have : ((g : 𝓞 E)) • lam = (l - l') - ξ - ξ' := by rw [← e1, ← e2]; abel
    rw [this]
    exact sub_mem (sub_mem hd.2 (hX hξ.2)) (hX' hξ'.2)
  have hlamU : lam ∈ UUE Λ F F' := by
    have h2 : (g : E)⁻¹ • (((g : 𝓞 E)) • lam) = lam := by
      rw [← IsScalarTower.algebraMap_smul E (g : 𝓞 E) lam, smul_smul]
      simp [hgE]
    rw [← h2]
    exact (UUE Λ F F').smul_mem _ hglam
  have key : (Submodule.Quotient.mk ⟨l - l', hd⟩ : BQ Λ F F') =
      (g : 𝓞 E) • (Submodule.Quotient.mk ⟨lam, ⟨hlam, hlamU⟩⟩ : BQ Λ F F') := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    show (l - l') - (g : 𝓞 E) • lam ∈ UU Λ F F'
    have : (l - l') - (g : 𝓞 E) • lam = ξ + ξ' := by rw [← e1, ← e2]; abel
    rw [this]
    unfold UU
    exact add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hξ)))
      (Submodule.mem_sup_left (Submodule.mem_sup_right hξ'))
  rw [key]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial

theorem m_psi_noZ (hX : Xsp F ≤ UUE Λ F F') (hX' : Xsp F' ≤ UUE Λ F F') (x : La Λ g F F') :
    m_psi hX hX' x ∈ noZ Λ F F' := by
  obtain ⟨-, -, -, l, hl, hxl, l', hl', hxl', -⟩ := m_La_mem Λ F F' g x.2
  rw [m_psi_apply hX hX' x hl hl' hxl hxl']
  refine ⟨⟨l - l', m_diff_mem hX hX' hl hl' hxl hxl'⟩, ?_, rfl⟩
  have : l - l' = -((x : S.V) - l) + ((x : S.V) - l') := by abel
  show l - l' ∈ Xsp F ⊔ Xsp F'
  rw [this]
  exact add_mem (Submodule.mem_sup_left (neg_mem hxl)) (Submodule.mem_sup_right hxl')

theorem m_UU_le (hz : IsLift Λ F) (hz' : IsLift Λ F') :
    UU Λ F F' ≤ (Λ ⊓ toO S (Xplus F)) ⊔ (Λ ⊓ toO S (Xplus F')) := by
  have hzX : F.fl.z ∈ Xplus F := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hzX' : F'.fl.z ∈ Xplus F' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  unfold UU
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · exact le_sup_of_le_left (fun v hv => ⟨hv.1, Submodule.mem_sup_left hv.2⟩)
  · refine le_sup_of_le_left ?_
    rw [Submodule.span_singleton_le_iff_mem, hz.2]
    exact ⟨hz.1, hzX⟩
  · exact le_sup_of_le_right (fun v hv => ⟨hv.1, Submodule.mem_sup_left hv.2⟩)
  · refine le_sup_of_le_right ?_
    rw [Submodule.span_singleton_le_iff_mem, hz'.2]
    exact ⟨hz'.1, hzX'⟩

theorem m_psi_ker (hz : IsLift Λ F) (hz' : IsLift Λ F') (hdisj : Xplus F ⊓ Xplus F' = ⊥)
    (hX : Xsp F ≤ UUE Λ F F') (hX' : Xsp F' ≤ UUE Λ F F') (x : La Λ g F F') :
    m_psi hX hX' x = 0 ↔ (x : S.V) ∈ Thp Λ F F' := by
  obtain ⟨hH, -, -, l, hl, hxl, l', hl', hxl', -⟩ := m_La_mem Λ F F' g x.2
  constructor
  · intro h0
    rw [m_psi_apply hX hX' x hl hl' hxl hxl', Submodule.Quotient.mk_eq_zero] at h0
    have h1 : l - l' ∈ UU Λ F F' := h0
    obtain ⟨p, hp, q, hq, e⟩ := Submodule.mem_sup.1 (m_UU_le hz hz' h1)
    have hmem : ((x : S.V) - l) + p ∈ Xplus F ⊓ Xplus F' := by
      refine ⟨add_mem (Submodule.mem_sup_left hxl) hp.2, ?_⟩
      have : ((x : S.V) - l) + p = ((x : S.V) - l') - q := by
        have : p = (l - l') - q := by rw [← e]; abel
        rw [this]; abel
      rw [this]
      exact sub_mem (Submodule.mem_sup_left hxl') hq.2
    rw [hdisj, Submodule.mem_bot] at hmem
    have hx : (x : S.V) = l - p := by
      have : (x : S.V) = ((x : S.V) - l + p) + (l - p) := by abel
      rw [this, hmem, zero_add]
    exact ⟨by rw [hx]; exact sub_mem hl.1 hp.1, hH⟩
  · intro hx
    have hoX : (x : S.V) ∈ orth S (Xsp F) :=
      p_mem_orth.2 fun v hv => p_mem_orth.1 hx.2 v (hX hv)
    have hoX' : (x : S.V) ∈ orth S (Xsp F') :=
      p_mem_orth.2 fun v hv => p_mem_orth.1 hx.2 v (hX' hv)
    rw [m_psi_apply hX hX' x (l := x) (l' := x) ⟨hx.1, hoX⟩ ⟨hx.1, hoX'⟩ (by simp) (by simp),
      Submodule.Quotient.mk_eq_zero]
    show (x : S.V) - x ∈ UU Λ F F'
    simp

theorem lemma_one_quotient_embedding (hg : 0 < g) (hz : IsLift Λ F) (hz' : IsLift Λ F') (hdisj : Xplus F ⊓ Xplus F' = ⊥)
    (hX : Xsp F ≤ UUE Λ F F') (hX' : Xsp F' ≤ UUE Λ F F') :
    ∃ φ : (La Λ g F F' ⧸ (Thp Λ F F').comap (La Λ g F F').subtype) →ₗ[𝓞 E] gB Λ g F F',
      Function.Injective φ ∧ (∀ c, ((φ c : BQ Λ F F') ∈ noZ Λ F F')) ∧
      ∀ (x : La Λ g F F'), ∀ l ∈ Lrep Λ F, ∀ l' ∈ Lrep Λ F',
        (x : S.V) - l ∈ Xsp F → (x : S.V) - l' ∈ Xsp F' →
          ∃ h : l - l' ∈ BLat Λ F F',
            (φ (Submodule.Quotient.mk x) : BQ Λ F F') = Submodule.Quotient.mk ⟨l - l', h⟩ := by
  let ψ : La Λ g F F' →ₗ[𝓞 E] gB Λ g F F' :=
    LinearMap.codRestrict _ (m_psi hX hX') (m_psi_mem_gB hg hX hX')
  have hker : ∀ x : La Λ g F F', ψ x = 0 ↔ x ∈ (Thp Λ F F').comap (La Λ g F F').subtype := by
    intro x
    have h1 : x ∈ (Thp Λ F F').comap (La Λ g F F').subtype ↔ m_psi hX hX' x = 0 :=
      (m_psi_ker hz hz' hdisj hX hX' x).symm
    rw [h1]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  refine ⟨Submodule.liftQ _ ψ (fun x hx => LinearMap.mem_ker.2 ((hker x).2 hx)), ?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot']
    ext x
    rw [LinearMap.mem_ker, hker]
  · intro c
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ c
    exact m_psi_noZ hX hX' x
  · intro x l hl l' hl' h h'
    exact ⟨m_diff_mem hX hX' hl hl' h h', m_psi_apply hX hX' x hl hl' h h'⟩

end Gen

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section C

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem c_mem_orth {U : Submodule E S.V} {y : S.V} :
    y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem c_herm (x y : S.V) : star (S.hT x y) = S.hT y x := S.herm.eq x y

theorem c_symm0 {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [← c_herm x y, h, star_zero]

theorem c_orth_anti {U U' : Submodule E S.V} (h : U ≤ U') : orth S U' ≤ orth S U := by
  intro y hy
  rw [c_mem_orth] at hy ⊢
  exact fun x hx => hy x (h hx)

variable {T T' : E}

theorem c_X_le_Xplus (F : LFlag S r T) : Xsp F ≤ Xplus F := le_sup_left

theorem c_z_mem_Xplus (F : LFlag S r T) : F.fl.z ∈ Xplus F :=
  (le_sup_right : Submodule.span E {F.fl.z} ≤ Xplus F) (Submodule.mem_span_singleton_self _)

theorem c_X_iso (F : LFlag S r T) : Xsp F ≤ orth S (Xsp F) := by
  intro y hy
  rw [c_mem_orth]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨b, rfl⟩ := hy; exact F.fl.e_iso a b
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem flag_span_orth_normal_left (F : LFlag S r T) {x : S.V} (hx : x ∈ Xsp F) : S.hT x F.fl.z = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact F.fl.z_orth a
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem c_X_le_orthXplus (F : LFlag S r T) : Xsp F ≤ orth S (Xplus F) := by
  intro y hy
  rw [c_mem_orth]
  intro x hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  have h1 : S.hT u y = 0 := (c_mem_orth.1 (c_X_iso F hy)) u hu
  have h2 : S.hT F.fl.z y = 0 := c_symm0 (flag_span_orth_normal_left F hy)
  simp [h1, h2]

theorem c_Xflag_r (F : LFlag S r T) : Xflag F r = Xsp F := by
  show Submodule.span E (F.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range F.fl.e)
  congr 1
  ext x
  constructor
  · rintro ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩

variable (Λ : Submodule (𝓞 E) S.V) (g : ℕ)

theorem c_La_le (F : LFlag S r T) (F' : LFlag S r T') :
    La Λ g F F' ≤ toO S (Hp Λ F F') ⊓ L0sub Λ F ⊓ L0sub Λ F' := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨h1, h2, h3, _⟩
  exact ⟨⟨h1, h2⟩, h3⟩

theorem c_L0sub_orth (F : LFlag S r T) {x : S.V} (hx : x ∈ L0sub Λ F) : x ∈ orth S (Xsp F) :=
  hx.1.2

theorem c_La_Hp {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} (hx : x ∈ La Λ g F F') :
    x ∈ Hp Λ F F' := (c_La_le Λ g F F' hx).1.1

theorem c_La_orthX {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} (hx : x ∈ La Λ g F F') :
    x ∈ orth S (Xsp F) := c_L0sub_orth Λ F (c_La_le Λ g F F' hx).1.2

theorem c_La_orthX' {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} (hx : x ∈ La Λ g F F') :
    x ∈ orth S (Xsp F') := c_L0sub_orth Λ F' (c_La_le Λ g F F' hx).2

theorem c_Hp_orthXplus {F : LFlag S r T} {F' : LFlag S r T'} (hU : HU Λ F F') :
    Hp Λ F F' ≤ orth S (Xplus F) := by
  unfold Hp; rw [hU]; exact c_orth_anti le_sup_left

theorem c_Hp_orthXplus' {F : LFlag S r T} {F' : LFlag S r T'} (hU : HU Λ F F') :
    Hp Λ F F' ≤ orth S (Xplus F') := by
  unfold Hp; rw [hU]; exact c_orth_anti le_sup_right

theorem c_Hp_orthX {F : LFlag S r T} {F' : LFlag S r T'} (hU : HU Λ F F') :
    Hp Λ F F' ≤ orth S (Xsp F) :=
  (c_Hp_orthXplus Λ hU).trans (c_orth_anti (c_X_le_Xplus F))

theorem c_Hp_orthX' {F : LFlag S r T} {F' : LFlag S r T'} (hU : HU Λ F F') :
    Hp Λ F F' ≤ orth S (Xsp F') :=
  (c_Hp_orthXplus' Λ hU).trans (c_orth_anti (c_X_le_Xplus F'))

theorem c_Hp_X {F : LFlag S r T} {F' : LFlag S r T'} (hU : HU Λ F F') (hN : HNd F F')
    {x : S.V} (h1 : x ∈ Hp Λ F F') (h2 : x ∈ Xsp F) : x = 0 := by
  have h3 : x ∈ U2 F F' ⊓ orth S (U2 F F') := by
    refine ⟨(le_sup_left : Xplus F ≤ U2 F F') (c_X_le_Xplus F h2), ?_⟩
    have := h1; unfold Hp at this; rwa [hU] at this
  rw [hN] at h3
  exact (Submodule.mem_bot E).1 h3

section Pair

variable {Λ g}
variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem c_iso (hP : IsPair Λ F F' F'' β g) (x y : S.V) : S.hT (β x) (β y) = S.hT x y :=
  hP.1.1 x y

theorem c_beta_X (hP : IsPair Λ F F' F'' β g) :
    (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'' := by
  have := hP.2.1 r
  rwa [c_Xflag_r, c_Xflag_r] at this

theorem c_beta_mem_X (hP : IsPair Λ F F' F'' β g) {x : S.V} (hx : x ∈ Xsp F') :
    β x ∈ Xsp F'' := by
  rw [← c_beta_X hP]; exact Submodule.mem_map_of_mem hx

theorem c_beta_orthX (hP : IsPair Λ F F' F'' β g) {x : S.V} (hx : x ∈ orth S (Xsp F')) :
    β x ∈ orth S (Xsp F'') := by
  rw [c_mem_orth] at hx ⊢
  intro y hy
  rw [← c_beta_X hP] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact (c_iso hP w x).trans (hx w hw)

theorem c_beta_orthXplus (hP : IsPair Λ F F' F'' β g) {x : S.V} (hx : x ∈ orth S (Xplus F')) :
    β x ∈ orth S (Xplus F'') := by
  have h1 : β x ∈ orth S (Xsp F'') := c_beta_orthX hP (c_orth_anti (c_X_le_Xplus F') hx)
  have h2 : S.hT F''.fl.z (β x) = 0 := by
    rw [← hP.2.2.1, c_iso hP]
    exact (c_mem_orth.1 hx) _ (c_z_mem_Xplus F')
  rw [c_mem_orth]
  intro y hy
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  simp [(c_mem_orth.1 h1) u hu, h2]

theorem c_mem_ThPairs {p : S.V × S.V} : p ∈ ThPairs Λ F F' F'' β ↔
    (p.1 ∈ Hp Λ F F' ∧ p.2 ∈ Hp Λ F F'') ∧ p.1 - p.2 ∈ Xsp F ∧ β p.1 - p.2 ∈ Xsp F'' := by
  simp [ThPairs, Submodule.mem_inf, Submodule.mem_prod, and_assoc]

theorem c_mem_Th {x : S.V} : x ∈ Th Λ F F' F'' β ↔
    ∃ x₂, (x ∈ Hp Λ F F' ∧ x₂ ∈ Hp Λ F F'') ∧ x - x₂ ∈ Xsp F ∧ β x - x₂ ∈ Xsp F'' := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, c_mem_ThPairs.1 hp⟩
  · rintro ⟨x₂, h⟩
    exact ⟨(x, x₂), c_mem_ThPairs.2 h, rfl⟩

theorem c_mem_Th'' {x : S.V} : x ∈ Th'' Λ F F' F'' β ↔
    ∃ x₁, (x₁ ∈ Hp Λ F F' ∧ x ∈ Hp Λ F F'') ∧ x₁ - x ∈ Xsp F ∧ β x₁ - x ∈ Xsp F'' := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, c_mem_ThPairs.1 hp⟩
  · rintro ⟨x₁, h⟩
    exact ⟨(x₁, x), c_mem_ThPairs.2 h, rfl⟩

theorem c_Th_le_Hp : Th Λ F F' F'' β ≤ Hp Λ F F' := fun _ hx => by
  obtain ⟨_, h, _⟩ := c_mem_Th.1 hx; exact h.1

theorem c_Th''_le_Hp : Th'' Λ F F' F'' β ≤ Hp Λ F F'' := fun _ hx => by
  obtain ⟨_, h, _⟩ := c_mem_Th''.1 hx; exact h.2

theorem c_bForm_sub_left (x y w : S.V) : bForm β (x - y) w = bForm β x w - bForm β y w := by
  simp only [bForm, map_sub, LinearMap.sub_apply]; ring

theorem c_bForm_sub_right (x y w : S.V) : bForm β w (x - y) = bForm β w x - bForm β w y := by
  simp only [bForm, map_sub]; ring

theorem c_b_vanish_left {x' x'' : S.V} (h' : x' ∈ Th Λ F F' F'' β)
    (h1 : x'' ∈ orth S (Xsp F)) (h2 : x'' ∈ orth S (Xsp F'')) : bForm β x' x'' = 0 := by
  obtain ⟨x₂, _, ha, hb⟩ := c_mem_Th.1 h'
  have e1 := (c_mem_orth.1 h1) _ ha
  have e2 := (c_mem_orth.1 h2) _ hb
  simp only [map_sub, LinearMap.sub_apply] at e1 e2
  unfold bForm
  linear_combination e1 - e2

theorem c_b_vanish_right (hP : IsPair Λ F F' F'' β g) {x' x'' : S.V}
    (h'' : x'' ∈ Th'' Λ F F' F'' β)
    (h1 : x' ∈ orth S (Xsp F)) (h2 : x' ∈ orth S (Xsp F')) : bForm β x' x'' = 0 := by
  obtain ⟨x₁, _, ha, hb⟩ := c_mem_Th''.1 h''
  have e1 := c_symm0 ((c_mem_orth.1 h1) _ ha)
  have e2 := c_symm0 ((c_mem_orth.1 (c_beta_orthX hP h2)) _ hb)
  have e3 := c_iso hP x' x₁
  simp only [map_sub] at e1 e2
  unfold bForm
  linear_combination e2 - e1 - e3

theorem c_b_vanish (hP : IsPair Λ F F' F'' β g) :
    ∀ x' ∈ La Λ g F F', ∀ x'' ∈ La Λ g F F'',
      (x' ∈ Th Λ F F' F'' β ∨ x'' ∈ Th'' Λ F F' F'' β) → bForm β x' x'' = 0 := by
  intro x' hx' x'' hx'' h
  rcases h with h | h
  · exact c_b_vanish_left h (c_La_orthX Λ g hx'') (c_La_orthX' Λ g hx'')
  · exact c_b_vanish_right hP h (c_La_orthX Λ g hx') (c_La_orthX' Λ g hx')

theorem c_Th_of_sup (hU : HU Λ F F') (hN : HNd F F') {x : S.V} (h1 : x ∈ Hp Λ F F')
    (h2 : x ∈ Th Λ F F' F'' β ⊔ Xsp F) : x ∈ Th Λ F F' F'' β := by
  obtain ⟨θ, hθ, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 h2
  have h3 : ξ ∈ Hp Λ F F' := by
    have := (Hp Λ F F').sub_mem h1 (c_Th_le_Hp hθ)
    simpa using this
  rw [c_Hp_X Λ hU hN h3 hξ, add_zero]; exact hθ

theorem c_Th''_of_sup (hU : HU Λ F F'') (hN : HNd F F'') {x : S.V} (h1 : x ∈ Hp Λ F F'')
    (h2 : x ∈ Th Λ F F' F'' β ⊔ Xsp F) : x ∈ Th'' Λ F F' F'' β := by
  obtain ⟨θ, hθ, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 h2
  obtain ⟨θ₂, hh, ha, hb⟩ := c_mem_Th.1 hθ
  have hθ₂ : θ₂ ∈ Th'' Λ F F' F'' β := c_mem_Th''.2 ⟨θ, hh, ha, hb⟩
  have h3 : θ + ξ - θ₂ ∈ Hp Λ F F'' := (Hp Λ F F'').sub_mem h1 hh.2
  have h4 : θ + ξ - θ₂ ∈ Xsp F := by
    have := (Xsp F).add_mem ha hξ
    convert this using 1; abel
  have h5 := c_Hp_X Λ hU hN h3 h4
  rw [sub_eq_zero.1 h5]; exact hθ₂

theorem c_b_descend_left (hU : HU Λ F F') (hN : HNd F F') (W : Submodule E S.V) :
    ∀ x'₁ ∈ La Λ g F F', ∀ x'₂ ∈ La Λ g F F', ∀ s' : S.V,
      IsProjS Λ F F' F'' β W x'₁ s' → IsProjS Λ F F' F'' β W x'₂ s' →
        ∀ x'' ∈ La Λ g F F'', bForm β x'₁ x'' = bForm β x'₂ x'' := by
  intro x₁ h₁ x₂ h₂ s' p₁ p₂ x'' hx''
  have h3 : x₁ - x₂ ∈ Th Λ F F' F'' β ⊔ Xsp F := by
    have := (Th Λ F F' F'' β ⊔ Xsp F).sub_mem p₁.2 p₂.2
    convert this using 1; abel
  have h4 := c_Th_of_sup hU hN ((Hp Λ F F').sub_mem (c_La_Hp Λ g h₁) (c_La_Hp Λ g h₂)) h3
  have h5 := c_b_vanish_left h4 (c_La_orthX Λ g hx'') (c_La_orthX' Λ g hx'')
  rw [c_bForm_sub_left] at h5
  exact sub_eq_zero.1 h5

theorem c_b_descend_right (hP : IsPair Λ F F' F'' β g) (hU : HU Λ F F'') (hN : HNd F F'')
    (W : Submodule E S.V) :
    ∀ x''₁ ∈ La Λ g F F'', ∀ x''₂ ∈ La Λ g F F'', ∀ s'' : S.V,
      IsProjS Λ F F' F'' β W x''₁ s'' → IsProjS Λ F F' F'' β W x''₂ s'' →
        ∀ x' ∈ La Λ g F F', bForm β x' x''₁ = bForm β x' x''₂ := by
  intro x₁ h₁ x₂ h₂ s'' p₁ p₂ x' hx'
  have h3 : x₁ - x₂ ∈ Th Λ F F' F'' β ⊔ Xsp F := by
    have := (Th Λ F F' F'' β ⊔ Xsp F).sub_mem p₁.2 p₂.2
    convert this using 1; abel
  have h4 := c_Th''_of_sup hU hN ((Hp Λ F F'').sub_mem (c_La_Hp Λ g h₁) (c_La_Hp Λ g h₂)) h3
  have h5 := c_b_vanish_right hP h4 (c_La_orthX Λ g hx') (c_La_orthX' Λ g hx')
  rw [c_bForm_sub_right] at h5
  exact sub_eq_zero.1 h5

end Pair

section A3

variable {Λ g}
variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem c_finrank_Th (hU : HU Λ F F'') (hN : HNd F F'') :
    finrank E (Th Λ F F' F'' β) = finrank E (ThPairs Λ F F' F'' β) := by
  have inj : Function.Injective
      ((LinearMap.fst E S.V S.V).domRestrict (ThPairs Λ F F' F'' β)) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨p, hp⟩ h
    have h0 : p.1 = 0 := h
    obtain ⟨⟨_, hb⟩, hc, _⟩ := c_mem_ThPairs.1 hp
    have h2 : p.2 ∈ Xsp F := by
      have := (Xsp F).neg_mem hc
      rw [h0] at this; simpa using this
    have h3 := c_Hp_X Λ hU hN hb h2
    exact Subtype.ext (Prod.ext h0 h3)
  have := LinearMap.finrank_range_of_inj inj
  rw [LinearMap.range_domRestrict] at this
  exact this

theorem c_finrank_Th'' (hU : HU Λ F F') (hN : HNd F F') :
    finrank E (Th'' Λ F F' F'' β) = finrank E (ThPairs Λ F F' F'' β) := by
  have inj : Function.Injective
      ((LinearMap.snd E S.V S.V).domRestrict (ThPairs Λ F F' F'' β)) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨p, hp⟩ h
    have h0 : p.2 = 0 := h
    obtain ⟨⟨ha, _⟩, hc, _⟩ := c_mem_ThPairs.1 hp
    have h2 : p.1 ∈ Xsp F := by
      rw [h0] at hc; simpa using hc
    have h3 := c_Hp_X Λ hU hN ha h2
    exact Subtype.ext (Prod.ext h3 h0)
  have := LinearMap.finrank_range_of_inj inj
  rw [LinearMap.range_domRestrict] at this
  exact this

theorem radicals_eq_theta_at_unit_index (hU' : HU Λ F F') (hN' : HNd F F') (hU'' : HU Λ F F'') (hN'' : HNd F F'')
    (k : ℕ) (h1 : finrank E (Hp Λ F F') = k - 1) (h2 : finrank E (Hp Λ F F'') = k - 1)
    (hs : s0 Λ F F' F'' β k = 1) :
    Hp Λ F F' = Th Λ F F' F'' β ∧ Hp Λ F F'' = Th'' Λ F F' F'' β := by
  have e1 : finrank E (Th Λ F F' F'' β) = k - 1 := by
    unfold s0 at hs; omega
  have e2 : finrank E (Th'' Λ F F' F'' β) = k - 1 := by
    rw [c_finrank_Th'' hU' hN', ← c_finrank_Th hU'' hN'', e1]
  exact ⟨(Submodule.eq_of_le_of_finrank_eq c_Th_le_Hp (e1.trans h1.symm)).symm,
    (Submodule.eq_of_le_of_finrank_eq c_Th''_le_Hp (e2.trans h2.symm)).symm⟩

end A3

section CS

theorem c_nrm_real (hS : StarConj E) (τ : E →+* ℂ) (x : S.V) :
    τ (S.hT x x) = ((nrm S τ x : ℝ) : ℂ) := by
  have h : starRingEnd ℂ (τ (S.hT x x)) = τ (S.hT x x) := by rw [← hS, c_herm]
  apply Complex.ext
  · simp [nrm]
  · simpa using Complex.conj_eq_iff_im.1 h

theorem c_nrm_X (F : LFlag S r T) (τ : E →+* ℂ) {x : S.V} (hx : x ∈ Xsp F) : nrm S τ x = 0 := by
  have : S.hT x x = 0 := (c_mem_orth.1 (c_X_iso F hx)) x hx
  simp [nrm, this]

theorem c_nrm_nonneg {F : LFlag S r T} (hPos : PosX F) (τ : E →+* ℂ) {y : S.V}
    (hy : y ∈ orth S (Xplus F)) : 0 ≤ nrm S τ y := by
  by_cases h : y ∈ Xsp F
  · exact (c_nrm_X F τ h).ge
  · exact (hPos τ y hy h).le

theorem c_hT_add_X (F : LFlag S r T) {s ξ : S.V} (hs : s ∈ orth S (Xsp F)) (hξ : ξ ∈ Xsp F) :
    S.hT (s + ξ) (s + ξ) = S.hT s s := by
  have e1 : S.hT ξ s = 0 := (c_mem_orth.1 hs) ξ hξ
  have e2 : S.hT s ξ = 0 := c_symm0 e1
  have e3 : S.hT ξ ξ = 0 := (c_mem_orth.1 (c_X_iso F hξ)) ξ hξ
  simp [e1, e2, e3]

theorem c_CS_sq (hS : StarConj E) {F : LFlag S r T} (hPos : PosX F) (τ : E →+* ℂ) {u v : S.V}
    (hu : u ∈ orth S (Xplus F)) (hv : v ∈ orth S (Xplus F)) :
    ‖τ (S.hT u v)‖ ^ 2 ≤ nrm S τ u * nrm S τ v := by
  by_cases hvX : v ∈ Xsp F
  · have e1 : S.hT u v = 0 :=
      c_symm0 ((c_mem_orth.1 (c_orth_anti (c_X_le_Xplus F) hu)) v hvX)
    rw [e1, c_nrm_X F τ hvX]; simp
  · have hc : 0 < nrm S τ v := hPos τ v hv hvX
    set w : S.V := (S.hT v v) • u - (S.hT v u) • v with hw
    have hwm : w ∈ orth S (Xplus F) :=
      (orth S (Xplus F)).sub_mem ((orth S (Xplus F)).smul_mem _ hu)
        ((orth S (Xplus F)).smul_mem _ hv)
    have h0 : 0 ≤ nrm S τ w := c_nrm_nonneg hPos τ hwm
    have e : S.hT w w = S.hT v v * (S.hT v v * S.hT u u - S.hT u v * S.hT v u) := by
      simp only [hw, map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, starRingEnd_apply, c_herm, RingHom.id_apply]
      ring
    have e2 : ((nrm S τ w : ℝ) : ℂ) =
        ((nrm S τ v * (nrm S τ v * nrm S τ u - ‖τ (S.hT u v)‖ ^ 2) : ℝ) : ℂ) := by
      rw [← c_nrm_real hS, e, map_mul, map_sub, map_mul, map_mul, c_nrm_real hS, c_nrm_real hS,
        ← c_herm u v, hS, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    have e3 : nrm S τ w = nrm S τ v * (nrm S τ v * nrm S τ u - ‖τ (S.hT u v)‖ ^ 2) := by
      exact_mod_cast e2
    rw [e3] at h0
    have := nonneg_of_mul_nonneg_right h0 hc
    nlinarith

theorem c_CS (hS : StarConj E) {F : LFlag S r T} (hPos : PosX F) (τ : E →+* ℂ) {u v : S.V}
    (hu : u ∈ orth S (Xplus F)) (hv : v ∈ orth S (Xplus F)) :
    ‖τ (S.hT u v)‖ ≤ Real.sqrt (nrm S τ u) * Real.sqrt (nrm S τ v) := by
  rw [← Real.sqrt_mul (c_nrm_nonneg hPos τ hu)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (c_CS_sq hS hPos τ hu hv))

variable {Λ g}
variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem c_b_bound (hS : StarConj E) (hP : IsPair Λ F F' F'' β g)
    (hU' : HU Λ F F') (hU'' : HU Λ F F'')
    (hPos : PosX F) (hPos'' : PosX F'') (W : Submodule E S.V) (hW : W ≤ orth S (Xplus F)) :
    ∀ τ : E →+* ℂ, ∀ x' ∈ La Λ g F F', ∀ x'' ∈ La Λ g F F'', ∀ s' s'' : S.V,
      IsProjS Λ F F' F'' β W x' s' → IsProjS Λ F F' F'' β W x'' s'' →
        ‖τ (bForm β x' x'')‖ ≤
          2 * Real.sqrt (nrm S τ s') * Real.sqrt (nrm S τ s'') := by
  intro τ x' hx' x'' hx'' s' s'' p' p''
  obtain ⟨θ', hθ', ξ', hξ', e'⟩ := Submodule.mem_sup.1 p'.2
  obtain ⟨θ, hθ, ξ, hξ, e''⟩ := Submodule.mem_sup.1 p''.2
  obtain ⟨θ₂, hh, ha, hb⟩ := c_mem_Th.1 hθ
  have hθ₂ : θ₂ ∈ Th'' Λ F F' F'' β := c_mem_Th''.2 ⟨θ, hh, ha, hb⟩
  have hs' : s' ∈ orth S (Xsp F) := c_orth_anti (c_X_le_Xplus F) (hW p'.1.1)
  have hs'' : s'' ∈ orth S (Xsp F) := c_orth_anti (c_X_le_Xplus F) (hW p''.1.1)

  have hp : x' - θ' = s' + ξ' := by
    have hx : x' = θ' + ξ' + s' := by rw [e']; abel
    rw [hx]; abel
  have hq : x'' - θ₂ = s'' + ((θ - θ₂) + ξ) := by
    have hx : x'' = θ + ξ + s'' := by rw [e'']; abel
    rw [hx]; abel
  have hpH : x' - θ' ∈ Hp Λ F F' := (Hp Λ F F').sub_mem (c_La_Hp Λ g hx') (c_Th_le_Hp hθ')
  have hqH : x'' - θ₂ ∈ Hp Λ F F'' := (Hp Λ F F'').sub_mem (c_La_Hp Λ g hx'') hh.2
  have b1 : bForm β x' x'' = bForm β (x' - θ') (x'' - θ₂) := by
    rw [c_bForm_sub_right, c_bForm_sub_left,
      c_b_vanish_left hθ' (c_La_orthX Λ g hx'') (c_La_orthX' Λ g hx''),
      c_b_vanish_right hP hθ₂ (c_Hp_orthX Λ hU' hpH) (c_Hp_orthX' Λ hU' hpH)]
    ring
  have n1 : nrm S τ (x' - θ') = nrm S τ s' := by
    unfold nrm; rw [hp, c_hT_add_X F hs' hξ']
  have n2 : nrm S τ (x'' - θ₂) = nrm S τ s'' := by
    unfold nrm; rw [hq, c_hT_add_X F hs'' ((Xsp F).add_mem ha hξ)]
  have n3 : nrm S τ (β (x' - θ')) = nrm S τ s' := by
    rw [← n1]; unfold nrm; rw [c_iso hP]
  have c1 := c_CS hS hPos τ (c_Hp_orthXplus Λ hU' hpH) (c_Hp_orthXplus Λ hU'' hqH)
  have c2 := c_CS hS hPos'' τ (c_beta_orthXplus hP (c_Hp_orthXplus' Λ hU' hpH))
    (c_Hp_orthXplus' Λ hU'' hqH)
  rw [n1, n2] at c1
  rw [n3, n2] at c2
  rw [b1]
  unfold bForm
  rw [map_sub]
  calc ‖τ (S.hT (x' - θ') (x'' - θ₂)) - τ (S.hT (β (x' - θ')) (x'' - θ₂))‖
      ≤ ‖τ (S.hT (x' - θ') (x'' - θ₂))‖ + ‖τ (S.hT (β (x' - θ')) (x'' - θ₂))‖ := norm_sub_le _ _
    _ ≤ 2 * Real.sqrt (nrm S τ s') * Real.sqrt (nrm S τ s'') := by linarith

end CS

section Lat

variable {Λ g}

theorem c_IotaRel_add {F : LFlag S r T} {F' : LFlag S r T'} {x y : S.V}
    (hx : IotaRel Λ g F F' x) (hy : IotaRel Λ g F F' y) : IotaRel Λ g F F' (x + y) := by
  obtain ⟨l, hl, h1, l', hl', h2, h3⟩ := hx
  obtain ⟨m, hm, k1, m', hm', k2, k3⟩ := hy
  refine ⟨l + m, add_mem hl hm, ?_, l' + m', add_mem hl' hm', ?_, ?_⟩
  · have := (Xsp F).add_mem h1 k1; convert this using 1; abel
  · have := (Xsp F').add_mem h2 k2; convert this using 1; abel
  · have := add_mem h3 k3; convert this using 1; abel

theorem c_IotaRel_smul {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} (o : 𝓞 E)
    (hx : IotaRel Λ g F F' x) : IotaRel Λ g F F' (o • x) := by
  obtain ⟨l, hl, h1, l', hl', h2, h3⟩ := hx
  refine ⟨o • l, Submodule.smul_mem _ o hl, ?_, o • l', Submodule.smul_mem _ o hl', ?_, ?_⟩
  · have := (toO S (Xsp F)).smul_mem o h1; rwa [smul_sub] at this
  · have := (toO S (Xsp F')).smul_mem o h2; rwa [smul_sub] at this
  · have := Submodule.smul_mem _ o h3; rwa [smul_sub] at this

theorem c_mem_La {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} :
    x ∈ La Λ g F F' ↔
      x ∈ Hp Λ F F' ∧ x ∈ L0sub Λ F ∧ x ∈ L0sub Λ F' ∧ IotaRel Λ g F F' x := by
  constructor
  · intro hx
    refine ⟨c_La_Hp Λ g hx, (c_La_le Λ g F F' hx).1.2, (c_La_le Λ g F F' hx).2, ?_⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact hx.2.2.2
    | zero => exact ⟨0, zero_mem _, by simp, 0, zero_mem _, by simp, by simp⟩
    | add u v _ _ hu hv => exact c_IotaRel_add hu hv
    | smul o u _ hu => exact c_IotaRel_smul o hu
  · intro hx
    exact Submodule.subset_span hx

theorem c_X_le_L0sub (F : LFlag S r T) : toO S (Xsp F) ≤ L0sub Λ F := by
  intro x hx
  refine ⟨⟨(le_sup_right : toO S (Xsp F) ≤ Lrep Λ F ⊔ toO S (Xsp F)) hx, c_X_iso F hx⟩, ?_⟩
  exact c_symm0 (flag_span_orth_normal_left F hx)

def c_Mv (Λ : Submodule (𝓞 E) S.V) (G G' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) : Prop :=
  (∀ x y, S.hT (γ x) (γ y) = S.hT x y) ∧ (∀ x ∈ Λ, γ x ∈ Λ) ∧ (∀ x ∈ Xsp G, γ x ∈ Xsp G') ∧
    (∀ x ∈ Xsp G', γ.symm x ∈ Xsp G) ∧ γ G.fl.z = G'.fl.z

theorem c_Mv_orthX {G G' : LFlag S r T'} {γ : S.V ≃ₗ[E] S.V} (h : c_Mv Λ G G' γ) {x : S.V}
    (hx : x ∈ orth S (Xsp G)) : γ x ∈ orth S (Xsp G') := by
  rw [c_mem_orth] at hx ⊢
  intro y hy
  have := hx _ (h.2.2.2.1 y hy)
  rw [← h.1, LinearEquiv.apply_symm_apply] at this
  exact this

theorem c_Mv_Lrep {G G' : LFlag S r T'} {γ : S.V ≃ₗ[E] S.V} (h : c_Mv Λ G G' γ) {x : S.V}
    (hx : x ∈ Lrep Λ G) : γ x ∈ Lrep Λ G' := ⟨h.2.1 x hx.1, c_Mv_orthX h hx.2⟩

theorem c_Mv_L0sub {G G' : LFlag S r T'} {γ : S.V ≃ₗ[E] S.V} (h : c_Mv Λ G G' γ) {x : S.V}
    (hx : x ∈ L0sub Λ G) : γ x ∈ L0sub Λ G' := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  refine ⟨⟨?_, c_Mv_orthX h h2⟩, ?_⟩
  · obtain ⟨l, hl, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 h1
    rw [map_add]
    exact Submodule.add_mem_sup (c_Mv_Lrep h hl) (h.2.2.1 ξ hξ)
  · show S.hT G'.fl.z (γ x) = 0
    rw [← h.2.2.2.2, h.1]; exact h3

variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem c_Mv_beta (hP : IsPair Λ F F' F'' β g) : c_Mv Λ F' F'' β := by
  refine ⟨c_iso hP, ?_, fun x hx => c_beta_mem_X hP hx, ?_, hP.2.2.1⟩
  · intro x hx
    rw [← hP.1.2]
    exact ⟨x, hx, rfl⟩
  · intro x hx
    rw [← c_beta_X hP] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    simpa using hw

theorem c_Mv_beta_symm (hP : IsPair Λ F F' F'' β g) : c_Mv Λ F'' F' β.symm := by
  have h := c_Mv_beta hP
  refine ⟨?_, ?_, h.2.2.2.1, ?_, ?_⟩
  · intro x y
    rw [← h.1, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · intro x hx
    rw [← hP.1.2] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    simpa using hw
  · intro x hx
    simpa using h.2.2.1 x hx
  · rw [← h.2.2.2.2]; simp

theorem c_La_partner (hP : IsPair Λ F F' F'' β g) {x x₂ : S.V} (hx : x ∈ La Λ g F F')
    (h2 : x₂ ∈ Hp Λ F F'') (ha : x - x₂ ∈ Xsp F) (hb : β x - x₂ ∈ Xsp F'') :
    x₂ ∈ La Λ g F F'' := by
  obtain ⟨_, k1, k2, l, hl, m1, l', hl', m2, m3⟩ := c_mem_La.1 hx
  refine c_mem_La.2 ⟨h2, ?_, ?_, l, hl, ?_, β l', c_Mv_Lrep (c_Mv_beta hP) hl', ?_, ?_⟩
  · have := (L0sub Λ F).sub_mem k1 (c_X_le_L0sub F ha)
    simpa using this
  · have := (L0sub Λ F'').sub_mem (c_Mv_L0sub (c_Mv_beta hP) k2) (c_X_le_L0sub F'' hb)
    simpa using this
  · have := (Xsp F).sub_mem m1 ha
    convert this using 1; abel
  · have := (Xsp F'').sub_mem (c_beta_mem_X hP m2) hb
    rw [map_sub] at this
    convert this using 1; abel
  · exact (hP.2.2.2 l' hl' l hl).1 m3

theorem c_La_partner' (hP : IsPair Λ F F' F'' β g) {x₁ x : S.V} (hx : x ∈ La Λ g F F'')
    (h1 : x₁ ∈ Hp Λ F F') (ha : x₁ - x ∈ Xsp F) (hb : β x₁ - x ∈ Xsp F'') :
    x₁ ∈ La Λ g F F' := by
  obtain ⟨_, k1, k2, l, hl, m1, l'', hl'', m2, m3⟩ := c_mem_La.1 hx
  have hs := c_Mv_beta_symm hP
  refine c_mem_La.2 ⟨h1, ?_, ?_, l, hl, ?_, β.symm l'', c_Mv_Lrep hs hl'', ?_, ?_⟩
  · have := (L0sub Λ F).add_mem k1 (c_X_le_L0sub F ha)
    simpa using this
  · have := c_Mv_L0sub hs ((L0sub Λ F'').add_mem k2 (c_X_le_L0sub F'' hb))
    simpa using this
  · have := (Xsp F).add_mem m1 ha
    convert this using 1; abel
  · have := hs.2.2.1 _ ((Xsp F'').add_mem m2 hb)
    simp only [map_add, map_sub, LinearEquiv.symm_apply_apply] at this
    convert this using 1; abel
  · refine (hP.2.2.2 (β.symm l'') (c_Mv_Lrep hs hl'') l hl).2 ?_
    rwa [LinearEquiv.apply_symm_apply]

theorem c_M_eq (hP : IsPair Λ F F' F'' β g) :
    Mlat Λ F F' F'' β g ⊔ toO S (Xsp F) = Mlat'' Λ F F' F'' β g ⊔ toO S (Xsp F) := by
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro x ⟨hx, hθ⟩
    obtain ⟨x₂, hh, ha, hb⟩ := c_mem_Th.1 hθ
    have h2 : x₂ ∈ Mlat'' Λ F F' F'' β g :=
      ⟨c_La_partner hP hx hh.2 ha hb, c_mem_Th''.2 ⟨x, hh, ha, hb⟩⟩
    have : x = x₂ + (x - x₂) := by abel
    rw [this]
    exact Submodule.add_mem_sup h2 ha
  · refine sup_le ?_ le_sup_right
    rintro x ⟨hx, hθ⟩
    obtain ⟨x₁, hh, ha, hb⟩ := c_mem_Th''.1 hθ
    have h2 : x₁ ∈ Mlat Λ F F' F'' β g :=
      ⟨c_La_partner' hP hx hh.1 ha hb, c_mem_Th.2 ⟨x, hh, ha, hb⟩⟩
    have : x = x₁ + -(x₁ - x) := by abel
    rw [this]
    exact Submodule.add_mem_sup h2 ((toO S (Xsp F)).neg_mem ha)

end Lat

section GO

variable {Λ g}

theorem c_int_of_unimod (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) :
    ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 E, S.hT x y = (o : E) := by
  intro x hx y hy
  have hy' : y ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    have h : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hΛ
    rw [h]; exact hy
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hy'
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hy' x hx)
  exact ⟨o, ho.symm⟩

theorem c_mem_NgX {F : LFlag S r T} {G : LFlag S r T'} {w : S.V} (hw : w ∈ NgX Λ g F G) :
    ∃ lam ∈ Λ, ∃ ξ ∈ XLam Λ F, ∃ ξ' ∈ XLam Λ G, w = (g : E) • lam + ξ + ξ' := by
  obtain ⟨a, ha, ξ', hξ', rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨gl, hgl, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 ha
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hgl
  obtain ⟨lam, hlam, rfl⟩ := hgl
  refine ⟨lam, hlam, ξ, hξ, ξ', hξ', ?_⟩
  rw [← algebraMap_smul E (g : 𝓞 E) lam, map_natCast]

theorem c_hT_modX (G : LFlag S r T) {u v a c : S.V} (hu : u ∈ orth S (Xsp G))
    (hv : v ∈ orth S (Xsp G)) (ha : a ∈ Xsp G) (hc : c ∈ Xsp G) :
    S.hT (u + a) (v + c) = S.hT u v := by
  have e1 : S.hT a v = 0 := (c_mem_orth.1 hv) a ha
  have e2 : S.hT u c = 0 := c_symm0 ((c_mem_orth.1 hu) c hc)
  have e3 : S.hT a c = 0 := (c_mem_orth.1 (c_X_iso G hc)) a ha
  simp [e1, e2, e3]

variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem c_b_gO (hP : IsPair Λ F F' F'' β g)
    (hInt : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 E, S.hT x y = (o : E)) :
    ∀ x' ∈ La Λ g F F', ∀ x'' ∈ La Λ g F F'',
      ∃ o : 𝓞 E, bForm β x' x'' = (g : E) * (o : E) := by
  intro x' hx' x'' hx''
  obtain ⟨_, _, _, l, hl, m1, l', hl', m2, m3⟩ := c_mem_La.1 hx'
  obtain ⟨_, _, _, m, hm, n1, m'', hm'', n2, n3⟩ := c_mem_La.1 hx''
  have hL' : β l' ∈ Lrep Λ F'' := c_Mv_Lrep (c_Mv_beta hP) hl'
  obtain ⟨lam, hlam, ξ, hξ, ξ'', hξ'', el⟩ := c_mem_NgX ((hP.2.2.2 l' hl' l hl).1 m3)
  obtain ⟨mu, hmu, η, hη, η'', hη'', em⟩ := c_mem_NgX n3
  have E1 : S.hT x' x'' = S.hT l m := by
    have := c_hT_modX F hl.2 hm.2 m1 n1
    simpa using this
  have E2 : S.hT (β x') x'' = S.hT (β l') m'' := by
    have := c_hT_modX F'' hL'.2 hm''.2 (c_beta_mem_X hP m2) n2
    simpa using this
  have hl_eq : l = β l' + ((g : E) • lam + ξ + ξ'') := by rw [← el]; abel
  have hm_eq : m = m'' + ((g : E) • mu + η + η'') := by rw [← em]; abel
  have z1 : S.hT ξ m = 0 := (c_mem_orth.1 hm.2) ξ hξ.2
  have z2 : S.hT ξ'' m'' = 0 := (c_mem_orth.1 hm''.2) ξ'' hξ''.2
  have z3 : S.hT (β l') η'' = 0 := c_symm0 ((c_mem_orth.1 hL'.2) η'' hη''.2)
  have z4 : S.hT l η = 0 := c_symm0 ((c_mem_orth.1 hl.2) η hη.2)
  have z5 : S.hT ξ η = 0 := (c_mem_orth.1 (c_X_iso F hη.2)) ξ hξ.2
  have z6 : S.hT ξ'' η'' = 0 := (c_mem_orth.1 (c_X_iso F'' hη''.2)) ξ'' hξ''.2
  have A : S.hT l m = S.hT (β l') m + (g : E) * S.hT lam m + S.hT ξ m + S.hT ξ'' m := by
    conv_lhs => rw [hl_eq]
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      map_natCast]
    ring
  have B : S.hT (β l') m = S.hT (β l') m'' + (g : E) * S.hT (β l') mu + S.hT (β l') η
      + S.hT (β l') η'' := by
    conv_lhs => rw [hm_eq]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have Cc : S.hT ξ'' m = S.hT ξ'' m'' + (g : E) * S.hT ξ'' mu + S.hT ξ'' η + S.hT ξ'' η'' := by
    conv_lhs => rw [hm_eq]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have Dd : S.hT l η = S.hT (β l') η + (g : E) * S.hT lam η + S.hT ξ η + S.hT ξ'' η := by
    conv_lhs => rw [hl_eq]
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      map_natCast]
    ring
  obtain ⟨o1, h1⟩ := hInt lam hlam m hm.1
  obtain ⟨o2, h2⟩ := hInt ξ'' hξ''.1 mu hmu
  obtain ⟨o3, h3⟩ := hInt (β l') hL'.1 mu hmu
  obtain ⟨o4, h4⟩ := hInt lam hlam η hη.1
  refine ⟨o1 + o2 + o3 - o4, ?_⟩
  unfold bForm
  rw [E1, E2]
  have hc : ((o1 + o2 + o3 - o4 : 𝓞 E) : E) =
      S.hT lam m + S.hT ξ'' mu + S.hT (β l') mu - S.hT lam η := by
    rw [h1, h2, h3, h4]; push_cast; ring
  rw [hc]
  linear_combination A + B + Cc - Dd + z4 - z5 + z3 + z1 + z2 + z6

end GO

section Rank

variable {Λ g}

theorem c_lat_mult (hΛ : Submodule.IsLattice E Λ) (v : S.V) :
    ∃ n : 𝓞 E, n ≠ 0 ∧ n • v ∈ Λ := by
  first
  | exact Formalism.MainNotions.LatticeGluingRadicals.c_lat_multL
  | (apply Formalism.MainNotions.LatticeGluingRadicals.c_lat_multL <;> assumption)
  | (intros; apply Formalism.MainNotions.LatticeGluingRadicals.c_lat_multL <;> assumption)
  | (intros; exact Formalism.MainNotions.LatticeGluingRadicals.c_lat_multL ‹_› ‹_›)
theorem c_Thp_le_La {F : LFlag S r T} {F' : LFlag S r T'} (hU : HU Λ F F') :
    Thp Λ F F' ≤ La Λ g F F' := by
  intro x hx
  have h1 : x ∈ orth S (Xsp F) := c_Hp_orthX Λ hU hx.2
  have h2 : x ∈ orth S (Xsp F') := c_Hp_orthX' Λ hU hx.2
  have z1 : S.hT F.fl.z x = 0 := (c_mem_orth.1 (c_Hp_orthXplus Λ hU hx.2)) _ (c_z_mem_Xplus F)
  have z2 : S.hT F'.fl.z x = 0 := (c_mem_orth.1 (c_Hp_orthXplus' Λ hU hx.2)) _ (c_z_mem_Xplus F')
  refine c_mem_La.2 ⟨hx.2, ⟨⟨?_, h1⟩, z1⟩, ⟨⟨?_, h2⟩, z2⟩,
    x, ⟨hx.1, h1⟩, by simp, x, ⟨hx.1, h2⟩, by simp, by simp⟩
  · exact (le_sup_left : Lrep Λ F ≤ Lrep Λ F ⊔ toO S (Xsp F)) ⟨hx.1, h1⟩
  · exact (le_sup_left : Lrep Λ F' ≤ Lrep Λ F' ⊔ toO S (Xsp F')) ⟨hx.1, h2⟩

theorem c_La_mult {F : LFlag S r T} {F' : LFlag S r T'} (hΛ : Submodule.IsLattice E Λ)
    (hU : HU Λ F F') {x : S.V} (hx : x ∈ Hp Λ F F') :
    ∃ n : 𝓞 E, n ≠ 0 ∧ n • x ∈ La Λ g F F' := by
  obtain ⟨n, hn, h⟩ := c_lat_mult hΛ x
  exact ⟨n, hn, c_Thp_le_La hU ⟨h, (toO S (Hp Λ F F')).smul_mem n hx⟩⟩

theorem c_orth_sup (A B : Submodule E S.V) : orth S (A ⊔ B) = orth S A ⊓ orth S B := by
  apply le_antisymm
  · exact le_inf (c_orth_anti le_sup_left) (c_orth_anti le_sup_right)
  · rintro y ⟨h1, h2⟩
    have h1 := c_mem_orth.1 h1
    have h2 := c_mem_orth.1 h2
    rw [c_mem_orth]
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    simp [h1 a ha, h2 b hb]

theorem c_finrank_orth_ge (U : Submodule E S.V) :
    finrank E S.V ≤ finrank E U + finrank E (orth S U) := by
  classical
  let b := Module.finBasis E U
  let φ : S.V →ₗ[E] (Fin (finrank E U) → E) := LinearMap.pi (fun i => S.hT (b i : S.V))
  have hk : LinearMap.ker φ ≤ orth S U := by
    intro y hy
    rw [c_mem_orth]
    intro x hx
    have hy' : ∀ i, S.hT (b i : S.V) y = 0 := fun i => congrFun (LinearMap.mem_ker.1 hy) i
    have hx'' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : S.V) := by
      calc x = ((⟨x, hx⟩ : U) : S.V) := rfl
        _ = ((∑ i, b.repr ⟨x, hx⟩ i • b i : U) : S.V) := by rw [b.sum_repr]
        _ = ∑ i, b.repr ⟨x, hx⟩ i • (b i : S.V) := by
          simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [hx'', map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [hy' i]
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : finrank E (LinearMap.range φ) ≤ finrank E U := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  have h3 : finrank E (LinearMap.ker φ) ≤ finrank E (orth S U) := Submodule.finrank_mono hk
  omega

theorem c_sup_orth_top (U : Submodule E S.V) (h : U ⊓ orth S U = ⊥) : U ⊔ orth S U = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (orth S U)
  rw [h, finrank_bot] at h1
  have h2 := c_finrank_orth_ge U
  have h3 := Submodule.finrank_le (U ⊔ orth S U)
  omega

variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem c_rank_Psi_gen (hPos : PosX F) {W : Submodule E S.V} {k : ℕ} (hW : WHypG F W k)
    (H ΘH : Submodule E S.V) (M : Submodule (𝓞 E) S.V)
    (h1 : M ≤ toO S H) (h2 : ∀ x ∈ H, ∃ n : 𝓞 E, n ≠ 0 ∧ n • x ∈ M) (h3 : ΘH ≤ H)
    (h4 : ΘH ⊔ Xsp F = Th Λ F F' F'' β ⊔ Xsp F) (h5 : H ≤ orth S (Xplus F))
    (h6 : ∀ x ∈ H, x ∈ Xsp F → x = 0) :
    finrank E (spanE S (Psi Λ F F' F'' β W M)) + finrank E ΘH = finrank E H := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hHX : H ≤ orth S (Xsp F) := h5.trans (c_orth_anti (c_X_le_Xplus F))
  have hWX : W ≤ orth S (Xsp F) := by
    refine le_trans ?_ (c_orth_anti (c_X_le_Xplus F))
    rw [← hW.1]; exact le_sup_left

  have hoo : orth S ΘH ⊓ orth S (Xsp F) = orth S (Th Λ F F' F'' β) ⊓ orth S (Xsp F) := by
    rw [← c_orth_sup, ← c_orth_sup, h4]
  have hXΘ : Xsp F ≤ orth S ΘH := by
    intro ξ hξ
    rw [c_mem_orth]
    intro x hx
    exact c_symm0 ((c_mem_orth.1 (hHX (h3 hx))) ξ hξ)
  have haniso : ΘH ⊓ orth S ΘH = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx'⟩
    have e : S.hT x x = 0 := (c_mem_orth.1 hx') x hx
    have hxX : x ∈ Xsp F := by
      by_contra hc
      have := hPos τ x (h5 (h3 hx)) hc
      simp [nrm, e] at this
    exact (Submodule.mem_bot E).2 (h6 x (h3 hx) hxX)
  set Q : Submodule E S.V := H ⊓ orth S ΘH with hQ
  have hQdim : finrank E Q + finrank E ΘH = finrank E H := by
    have e1 : ΘH ⊔ Q = H := by
      rw [hQ, inf_comm, ← sup_inf_assoc_of_le _ h3, c_sup_orth_top ΘH haniso, top_inf_eq]
    have e2 : ΘH ⊓ Q = ⊥ := by
      rw [eq_bot_iff, ← haniso]
      exact fun x hx => ⟨hx.1, hx.2.2⟩
    have := Submodule.finrank_sup_add_finrank_inf_eq ΘH Q
    rw [e1, e2, finrank_bot] at this
    omega
  set P : Submodule E S.V := spanE S (Psi Λ F F' F'' β W M) with hP
  have hPW : P ≤ W := by
    refine Submodule.span_le.2 ?_
    have : Psi Λ F F' F'' β W M ≤ toO S W := by
      refine Submodule.span_le.2 ?_
      rintro s ⟨x, _, hs⟩
      exact hs.1.1
    exact this
  have hPX : P ⊓ Xsp F = ⊥ := by
    rw [eq_bot_iff, ← hW.2.1]
    exact fun x hx => ⟨hPW hx.1, hx.2⟩
  have hQX : Q ⊓ Xsp F = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx'⟩
    exact (Submodule.mem_bot E).2 (h6 x hx.1 hx')
  have hle1 : P ≤ Q ⊔ Xsp F := by
    refine Submodule.span_le.2 ?_
    have : Psi Λ F F' F'' β W M ≤ toO S (Q ⊔ Xsp F) := by
      refine Submodule.span_le.2 ?_
      rintro s ⟨x, hx, hs⟩
      have hs2 := hs.2
      rw [← h4] at hs2
      obtain ⟨θ, hθ, ξ, hξ, e⟩ := Submodule.mem_sup.1 hs2
      have hsΘ : s ∈ orth S ΘH := by
        have : s ∈ orth S ΘH ⊓ orth S (Xsp F) := by rw [hoo]; exact ⟨hs.1.2, hWX hs.1.1⟩
        exact this.1
      have es : s = (x - θ) + -ξ := by
        have hx' : x = θ + ξ + s := by rw [e]; abel
        rw [hx']; abel
      have hq : x - θ ∈ Q := by
        refine ⟨H.sub_mem (h1 hx) (h3 hθ), ?_⟩
        have : x - θ = s + ξ := by rw [es]; abel
        rw [this]
        exact (orth S ΘH).add_mem hsΘ (hXΘ hξ)
      show s ∈ Q ⊔ Xsp F
      rw [es]
      exact Submodule.add_mem_sup hq ((Xsp F).neg_mem hξ)
    exact this
  have hle2 : Q ≤ P ⊔ Xsp F := by
    intro q hq
    have hq' : q ∈ W ⊔ Xsp F := by rw [hW.1]; exact h5 hq.1
    obtain ⟨s, hs, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 hq'
    obtain ⟨n, hn, hnM⟩ := h2 _ hq.1
    have hsΘ : s ∈ orth S (Th Λ F F' F'' β) := by
      have h7 : s ∈ orth S ΘH := by
        have := (orth S ΘH).sub_mem hq.2 (hXΘ hξ)
        simpa using this
      have : s ∈ orth S (Th Λ F F' F'' β) ⊓ orth S (Xsp F) := by rw [← hoo]; exact ⟨h7, hWX hs⟩
      exact this.1
    have hproj : IsProjS Λ F F' F'' β W (n • (s + ξ)) (n • s) := by
      refine ⟨⟨(toO S W).smul_mem n hs, (toO S (orth S (Th Λ F F' F'' β))).smul_mem n hsΘ⟩, ?_⟩
      have : n • (s + ξ) - n • s = n • ξ := by rw [smul_add]; abel
      rw [this]
      exact (le_sup_right : Xsp F ≤ Th Λ F F' F'' β ⊔ Xsp F) ((toO S (Xsp F)).smul_mem n hξ)
    have hns : n • s ∈ P :=
      Submodule.subset_span (Submodule.subset_span ⟨_, hnM, hproj⟩)
    have hn1 : algebraMap (𝓞 E) E n ≠ 0 := by
      simpa using (map_ne_zero_iff (algebraMap (𝓞 E) E) (IsFractionRing.injective (𝓞 E) E)).2 hn
    have hsP : s ∈ P := by
      have := P.smul_mem (algebraMap (𝓞 E) E n)⁻¹ hns
      rwa [← algebraMap_smul E n s, smul_smul, inv_mul_cancel₀ hn1, one_smul] at this
    exact Submodule.add_mem_sup hsP hξ
  have hsup : P ⊔ Xsp F = Q ⊔ Xsp F :=
    le_antisymm (sup_le hle1 le_sup_right) (sup_le hle2 le_sup_right)
  have d1 := Submodule.finrank_sup_add_finrank_inf_eq P (Xsp F)
  have d2 := Submodule.finrank_sup_add_finrank_inf_eq Q (Xsp F)
  rw [hPX, finrank_bot] at d1
  rw [hQX, finrank_bot, ← hsup] at d2
  omega

end Rank

section Rank2

variable {Λ g}
variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem c_Th''_sup_X : Th'' Λ F F' F'' β ⊔ Xsp F = Th Λ F F' F'' β ⊔ Xsp F := by
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    intro x hx
    obtain ⟨x₁, hh, ha, hb⟩ := c_mem_Th''.1 hx
    have : x = x₁ + -(x₁ - x) := by abel
    rw [this]
    exact Submodule.add_mem_sup (c_mem_Th.2 ⟨x, hh, ha, hb⟩) ((Xsp F).neg_mem ha)
  · refine sup_le ?_ le_sup_right
    intro x hx
    obtain ⟨x₂, hh, ha, hb⟩ := c_mem_Th.1 hx
    have : x = x₂ + (x - x₂) := by abel
    rw [this]
    exact Submodule.add_mem_sup (c_mem_Th''.2 ⟨x, hh, ha, hb⟩) ha

theorem c_rank_Psi' (hΛ : Submodule.IsLattice E Λ) (hU' : HU Λ F F') (hN' : HNd F F')
    (hPos : PosX F) {W : Submodule E S.V} {k : ℕ} (hW : WHypG F W k)
    (h1 : finrank E (Hp Λ F F') = k - 1) :
    finrank E (spanE S (Psi Λ F F' F'' β W (La Λ g F F'))) = s0 Λ F F' F'' β k - 1 := by
  have := c_rank_Psi_gen (Λ := Λ) (F' := F') (F'' := F'') (β := β) hPos hW (Hp Λ F F')
    (Th Λ F F' F'' β) (La Λ g F F') (fun x hx => c_La_Hp Λ g hx)
    (fun x hx => c_La_mult hΛ hU' hx) c_Th_le_Hp rfl (c_Hp_orthXplus Λ hU')
    (fun x hx hx' => c_Hp_X Λ hU' hN' hx hx')
  unfold s0
  omega

theorem c_rank_Psi'' (hΛ : Submodule.IsLattice E Λ) (hU' : HU Λ F F') (hN' : HNd F F')
    (hU'' : HU Λ F F'') (hN'' : HNd F F'')
    (hPos : PosX F) {W : Submodule E S.V} {k : ℕ} (hW : WHypG F W k)
    (h2 : finrank E (Hp Λ F F'') = k - 1) :
    finrank E (spanE S (Psi Λ F F' F'' β W (La Λ g F F''))) = s0 Λ F F' F'' β k - 1 := by
  have := c_rank_Psi_gen (Λ := Λ) (F' := F') (F'' := F'') (β := β) hPos hW (Hp Λ F F'')
    (Th'' Λ F F' F'' β) (La Λ g F F'') (fun x hx => c_La_Hp Λ g hx)
    (fun x hx => c_La_mult hΛ hU'' hx) c_Th''_le_Hp c_Th''_sup_X (c_Hp_orthXplus Λ hU'')
    (fun x hx hx' => c_Hp_X Λ hU'' hN'' hx hx')
  have e : finrank E (Th'' Λ F F' F'' β) = finrank E (Th Λ F F' F'' β) := by
    rw [c_finrank_Th'' hU' hN', ← c_finrank_Th hU'' hN'']
  unfold s0
  omega

theorem c_mem_radL {x' : S.V} : x' ∈ radL Λ F F' F'' β ↔
    x' ∈ Hp Λ F F' ∧ ∀ x'' ∈ Hp Λ F F'', bForm β x' x'' = 0 := by
  simp [radL, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, bForm]

theorem c_mem_radR {x'' : S.V} : x'' ∈ radR Λ F F' F'' β ↔
    x'' ∈ Hp Λ F F'' ∧ ∀ x' ∈ Hp Λ F F', bForm β x' x'' = 0 := by
  simp [radR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, bForm]

theorem c_Th_le_radL (hU'' : HU Λ F F'') : Th Λ F F' F'' β ≤ radL Λ F F' F'' β := by
  intro x hx
  exact c_mem_radL.2 ⟨c_Th_le_Hp hx, fun x'' hx'' =>
    c_b_vanish_left hx (c_Hp_orthX Λ hU'' hx'') (c_Hp_orthX' Λ hU'' hx'')⟩

theorem c_Th''_le_radR (hP : IsPair Λ F F' F'' β g) (hU' : HU Λ F F') :
    Th'' Λ F F' F'' β ≤ radR Λ F F' F'' β := by
  intro x hx
  exact c_mem_radR.2 ⟨c_Th''_le_Hp hx, fun x' hx' =>
    c_b_vanish_right hP hx (c_Hp_orthX Λ hU' hx') (c_Hp_orthX' Λ hU' hx')⟩

theorem c_BNondeg_of_rad (h1 : radL Λ F F' F'' β = Th Λ F F' F'' β)
    (h2 : radR Λ F F' F'' β = Th'' Λ F F' F'' β) : BNondeg Λ F F' F'' β := by
  constructor
  · intro x' hx' h
    rw [← h1]; exact c_mem_radL.2 ⟨hx', h⟩
  · intro x'' hx'' h
    rw [← h2]; exact c_mem_radR.2 ⟨hx'', h⟩

end Rank2

section Rad

theorem c_finrank_orth_le (U : Submodule E S.V) :
    finrank E U + finrank E (orth S U) ≤ finrank E S.V := by
  classical
  let b := Module.finBasis E U
  let φ : S.V →ₗ[E] (Fin (finrank E U) → E) := LinearMap.pi (fun i => S.hT (b i : S.V))
  have hk : orth S U ≤ LinearMap.ker φ := by
    intro y hy
    rw [LinearMap.mem_ker]
    funext i
    exact (c_mem_orth.1 hy) _ (b i).2
  have hr : LinearMap.range φ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne)
      inferInstance
    have hfy : ∀ y, f (φ y) = 0 := by
      intro y
      have : f (φ y) ∈ (LinearMap.range φ).map f := ⟨φ y, ⟨y, rfl⟩, rfl⟩
      rw [hf] at this
      exact (Submodule.mem_bot E).1 this
    set c : Fin (finrank E U) → E := fun i => f (fun j => if i = j then 1 else 0) with hc
    have hsum : ∀ v, f v = ∑ i, v i * c i := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      rfl
    have hx0 : (∑ i, star (c i) • (b i : S.V)) = 0 := by
      apply S.nondeg.1
      intro y
      rw [map_sum, LinearMap.sum_apply]
      have := hfy y
      rw [hsum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      exact mul_comm _ _
    have hx1 : (∑ i, star (c i) • b i) = 0 := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] using hx0
    have hci : ∀ i, c i = 0 := by
      intro i
      have := Fintype.linearIndependent_iff.1 b.linearIndependent (fun i => star (c i)) hx1 i
      simpa using this
    apply hf0
    refine LinearMap.ext fun v => ?_
    rw [hsum]
    simp [hci]
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  rw [hr, finrank_top] at h1
  have h2 : finrank E (Fin (finrank E U) → E) = finrank E U := by simp
  have h3 : finrank E (orth S U) ≤ finrank E (LinearMap.ker φ) := Submodule.finrank_mono hk
  omega

theorem c_finrank_X (F : LFlag S r T) : finrank E (Xsp F) = r := by
  have h := finrank_span_eq_card F.fl.e_indep
  rw [Fintype.card_fin] at h
  exact h

theorem c_finrank_Xplus (F : LFlag S r T) (hT : T ≠ 0) : r + 1 ≤ finrank E (Xplus F) := by
  have hlt : Xsp F < Xplus F := by
    refine lt_of_le_of_ne (c_X_le_Xplus F) ?_
    intro h
    have hz : F.fl.z ∈ Xsp F := by rw [h]; exact c_z_mem_Xplus F
    have : S.hT F.fl.z F.fl.z = 0 := flag_span_orth_normal_left F hz
    rw [F.fl.z_norm] at this
    exact hT (neg_eq_zero.1 this)
  have := Submodule.finrank_lt_finrank_of_lt hlt
  rw [c_finrank_X] at this
  omega

theorem c_rad_le {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (p q : V → (V →ₗ[E] E)) (hpq : ∀ x y, p x y = 0 ↔ q y x = 0) (A B : Submodule E V) :
    finrank E B + finrank E (A ⊓ ⨅ y ∈ B, LinearMap.ker (q y) : Submodule E V) ≤
      finrank E A + finrank E (B ⊓ ⨅ x ∈ A, LinearMap.ker (p x) : Submodule E V) := by
  classical
  set LA : Submodule E V := A ⊓ ⨅ y ∈ B, LinearMap.ker (q y) with hLA
  set RB : Submodule E V := B ⊓ ⨅ x ∈ A, LinearMap.ker (p x) with hRB
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LA.comap A.subtype)
  have hdim := Submodule.finrank_add_eq_of_isCompl hC
  have hLAdim : finrank E (LA.comap A.subtype) = finrank E LA := by
    have h := Submodule.finrank_map_subtype_eq A (LA.comap A.subtype)
    rw [Submodule.map_comap_subtype, inf_eq_right.2 (inf_le_left : LA ≤ A)] at h
    exact h.symm
  let b := Module.finBasis E C
  let φ : V →ₗ[E] (Fin (finrank E C) → E) := LinearMap.pi (fun i => p ((b i : A) : V))
  let ψ : B →ₗ[E] (Fin (finrank E C) → E) := φ.domRestrict B
  have hker : (LinearMap.ker ψ).map B.subtype ≤ RB := by
    rintro _ ⟨⟨y, hy⟩, hyk, rfl⟩
    refine ⟨hy, ?_⟩
    refine (Submodule.mem_iInf _).2 fun x => (Submodule.mem_iInf _).2 fun hx =>
      LinearMap.mem_ker.2 ?_
    show p x y = 0
    rw [hpq]
    have hyi : ∀ i, q y ((b i : A) : V) = 0 := by
      intro i
      rw [← hpq]
      exact congrFun (LinearMap.mem_ker.1 hyk) i
    have hCk : C ≤ (LinearMap.ker (q y)).comap A.subtype := by
      intro c hc
      have hc' : (⟨c, hc⟩ : C) = ∑ i, b.repr ⟨c, hc⟩ i • b i := (b.sum_repr _).symm
      have hc'' : (c : V) = ∑ i, b.repr ⟨c, hc⟩ i • ((b i : A) : V) := by
        calc (c : V) = (((⟨c, hc⟩ : C) : A) : V) := rfl
          _ = (((∑ i, b.repr ⟨c, hc⟩ i • b i : C) : A) : V) := by rw [b.sum_repr]
          _ = ∑ i, b.repr ⟨c, hc⟩ i • ((b i : A) : V) := by
            simp only [Submodule.coe_sum, Submodule.coe_smul]
      show q y (c : V) = 0
      rw [hc'', map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [hyi i]
    have hLk : LA.comap A.subtype ≤ (LinearMap.ker (q y)).comap A.subtype := by
      intro a ha
      have h2 : (a : V) ∈ ⨅ y ∈ B, LinearMap.ker (q y) := (Submodule.mem_inf.1 ha).2
      simp only [Submodule.mem_iInf] at h2
      exact h2 y hy
    have htop : (⊤ : Submodule E A) ≤ (LinearMap.ker (q y)).comap A.subtype := by
      rw [← hC.sup_eq_top]
      exact sup_le hLk hCk
    exact htop (Submodule.mem_top : (⟨x, hx⟩ : A) ∈ ⊤)
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  have h2 : finrank E (LinearMap.range ψ) ≤ finrank E C := by
    have := Submodule.finrank_le (LinearMap.range ψ)
    simpa using this
  have h3 : finrank E (LinearMap.ker ψ) ≤ finrank E RB := by
    rw [← Submodule.finrank_map_subtype_eq B (LinearMap.ker ψ)]
    exact Submodule.finrank_mono hker
  omega

end Rad

section Rad2

variable {Λ g}
variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem c_radL_inf_le (hP : IsPair Λ F F' F'' β g) (hU' : HU Λ F F') (hU'' : HU Λ F F'')
    (hPos'' : PosX F'') :
    radL Λ F F' F'' β ⊓ (Hp Λ F F'' ⊔ Xsp F) ≤ Th Λ F F' F'' β := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  rintro x ⟨hx, hK⟩
  obtain ⟨hxH, hb⟩ := c_mem_radL.1 hx
  obtain ⟨h, hh, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 hK
  refine c_mem_Th.2 ⟨h, ⟨hxH, hh⟩, by simpa using hξ, ?_⟩
  have hu : β (h + ξ) - h ∈ orth S (Xplus F'') :=
    (orth S (Xplus F'')).sub_mem (c_beta_orthXplus hP (c_Hp_orthXplus' Λ hU' hxH))
      (c_Hp_orthXplus' Λ hU'' hh)
  have hhX : h ∈ orth S (Xsp F) := c_Hp_orthX Λ hU'' hh
  have e1 : S.hT (β (h + ξ)) (β (h + ξ)) = S.hT h h :=
    (c_iso hP _ _).trans (c_hT_add_X F hhX hξ)
  have e2 := hb h hh
  have e5 : S.hT (h + ξ) h = S.hT h h := by
    have : S.hT ξ h = 0 := (c_mem_orth.1 hhX) ξ hξ
    simp [this]
  have e3 : S.hT (β (h + ξ)) h = S.hT h h := by
    unfold bForm at e2
    rw [e5] at e2
    exact (sub_eq_zero.1 e2).symm
  have e4 : S.hT h (β (h + ξ)) = S.hT h h := by
    rw [← c_herm, e3, c_herm]
  by_contra hc
  have hpos := hPos'' τ _ hu hc
  have e6 : S.hT (β (h + ξ) - h) (β (h + ξ) - h) = 0 := by
    generalize β (h + ξ) = y at e1 e3 e4
    simp only [map_sub, LinearMap.sub_apply, e1, e3, e4]
    ring
  unfold nrm at hpos
  rw [e6] at hpos
  simp at hpos

theorem c_radL_rank (hP : IsPair Λ F F' F'' β g) (hU' : HU Λ F F') (hU'' : HU Λ F F'')
    (hN'' : HNd F F'') (hPos'' : PosX F'') (hT : T ≠ 0) (k : ℕ)
    (hV : finrank E S.V = k + 2 * r + 1) (h2 : finrank E (Hp Λ F F'') = k - 1) (hk : 1 ≤ k) :
    finrank E (radL Λ F F' F'' β) ≤ finrank E (Th Λ F F' F'' β) + 1 := by
  have d1 := c_finrank_orth_le (Xplus F)
  have d2 := c_finrank_Xplus F hT
  have hinf : Hp Λ F F'' ⊓ Xsp F = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx'⟩
    exact (Submodule.mem_bot E).2 (c_Hp_X Λ hU'' hN'' hx hx')
  have d3 := Submodule.finrank_sup_add_finrank_inf_eq (Hp Λ F F'') (Xsp F)
  rw [hinf, finrank_bot, c_finrank_X, h2] at d3
  have hle : radL Λ F F' F'' β ⊔ (Hp Λ F F'' ⊔ Xsp F) ≤ orth S (Xplus F) := by
    refine sup_le ?_ (sup_le (c_Hp_orthXplus Λ hU'') (c_X_le_orthXplus F))
    exact fun x hx => c_Hp_orthXplus Λ hU' (c_mem_radL.1 hx).1
  have d4 := Submodule.finrank_mono hle
  have d5 := Submodule.finrank_sup_add_finrank_inf_eq (radL Λ F F' F'' β) (Hp Λ F F'' ⊔ Xsp F)
  have d6 := Submodule.finrank_mono (c_radL_inf_le hP hU' hU'' hPos'')
  omega

theorem c_rad_eq :
    finrank E (radL Λ F F' F'' β) + finrank E (Hp Λ F F'') =
      finrank E (radR Λ F F' F'' β) + finrank E (Hp Λ F F') := by
  let p : S.V → (S.V →ₗ[E] E) := fun x => S.hT x - S.hT (β x)
  let q : S.V → (S.V →ₗ[E] E) := fun y => S.hT y - (S.hT y).comp (β : S.V →ₗ[E] S.V)
  have hstar : ∀ x y, q y x = star (p x y) := by
    intro x y
    simp only [p, q, LinearMap.sub_apply, LinearMap.comp_apply, star_sub, c_herm]
    rfl
  have hpq : ∀ x y, p x y = 0 ↔ q y x = 0 := by
    intro x y
    rw [hstar, star_eq_zero]
  have hL : radL Λ F F' F'' β =
      (Hp Λ F F' ⊓ ⨅ y ∈ Hp Λ F F'', LinearMap.ker (q y) : Submodule E S.V) := by
    ext x
    rw [c_mem_radL, Submodule.mem_inf]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    refine and_congr_right fun _ => forall₂_congr fun y _ => ?_
    exact hpq x y
  have hR : radR Λ F F' F'' β =
      (Hp Λ F F'' ⊓ ⨅ x ∈ Hp Λ F F', LinearMap.ker (p x) : Submodule E S.V) := rfl
  have a1 := c_rad_le p q hpq (Hp Λ F F') (Hp Λ F F'')
  have a2 := c_rad_le q p (fun y x => (hpq x y).symm) (Hp Λ F F'') (Hp Λ F F')
  rw [← hL, ← hR] at a1 a2
  omega

theorem c_thmA_ranks (hP : IsPair Λ F F' F'' β g) (hU' : HU Λ F F') (hN' : HNd F F')
    (hU'' : HU Λ F F'') (hN'' : HNd F F'') (hPos'' : PosX F'') (hT : T ≠ 0) (k : ℕ)
    (hV : finrank E S.V = k + 2 * r + 1) (h1 : finrank E (Hp Λ F F') = k - 1)
    (h2 : finrank E (Hp Λ F F'') = k - 1) (hk : 1 ≤ k) (hnd : ¬ BNondeg Λ F F' F'' β) :
    finrank E (radL Λ F F' F'' β) = finrank E (Th Λ F F' F'' β) + 1 ∧
      finrank E (radR Λ F F' F'' β) = finrank E (Th Λ F F' F'' β) + 1 := by
  have eTh : finrank E (Th'' Λ F F' F'' β) = finrank E (Th Λ F F' F'' β) := by
    rw [c_finrank_Th'' hU' hN', ← c_finrank_Th hU'' hN'']
  have u1 := c_radL_rank hP hU' hU'' hN'' hPos'' hT k hV h2 hk
  have l1 := Submodule.finrank_mono (c_Th_le_radL (F' := F') (β := β) hU'')
  have eq := c_rad_eq (Λ := Λ) (F := F) (F' := F') (F'' := F'') (β := β)
  rw [h1, h2] at eq
  have hne : finrank E (radL Λ F F' F'' β) ≠ finrank E (Th Λ F F' F'' β) := by
    intro h
    apply hnd
    refine c_BNondeg_of_rad ?_ ?_
    · exact (Submodule.eq_of_le_of_finrank_eq (c_Th_le_radL hU'') h.symm).symm
    · refine (Submodule.eq_of_le_of_finrank_eq (c_Th''_le_radR hP hU') ?_).symm
      omega
  omega

end Rad2

end C

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem radical_setting_second_of (D : D7) (Λ : VanishingOnXAndXPlusGluing.LatS D) (g : ℕ) {T T' : ℕ} (F : VanishingOnXAndXPlusGluing.FlS D T)
    (F' F'' : VanishingOnXAndXPlusGluing.FlS D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (W : Submodule D.host.E (hS D).V)
    (hSt : StarConj D.host.E) (hΛ : Submodule.IsLattice D.host.E Λ)
    (hUni : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) (hP : IsPair Λ F F' F'' β g)
    (hU' : HU Λ F F') (hN' : HNd F F') (hU'' : HU Λ F F'') (hN'' : HNd F F'')
    (hPos : PosX F) (hPos'' : PosX F'') (hW : WHyp D F W)
    (h1 : finrank D.host.E (Hp Λ F F') = D.R.k - 1)
    (h2 : finrank D.host.E (Hp Λ F F'') = D.R.k - 1)
    (h4 : latDet (hS D) (Mlat Λ F F' F'' β g) ^ 2 =
      latDet (hS D) (La Λ g F F') * latDet (hS D) (La Λ g F F'') /
        (latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F')) *
          latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F'')))) :
    VanishingOnXAndXPlusGluing.LatticeSpanEquality D Λ g F F' F'' β W :=
  ⟨c_M_eq hP, c_rank_Psi' hΛ hU' hN' hPos hW h1, c_rank_Psi'' hΛ hU' hN' hU'' hN'' hPos hW h2, h4,
    c_b_gO hP (c_int_of_unimod hUni), c_b_vanish hP,
    c_b_bound hSt hP hU' hU'' hPos hPos'' W (by rw [← hW.1]; exact le_sup_left),
    c_b_descend_left hU' hN' W, c_b_descend_right hP hU'' hN'' W⟩

theorem radical_setting_third_of (D : D7) (Λ : VanishingOnXAndXPlusGluing.LatS D) {T T' : ℕ} (F : VanishingOnXAndXPlusGluing.FlS D T)
    (F' F'' : VanishingOnXAndXPlusGluing.FlS D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (hU' : HU Λ F F') (hN' : HNd F F') (hU'' : HU Λ F F'') (hN'' : HNd F F'')
    (h1 : finrank D.host.E (Hp Λ F F') = D.R.k - 1)
    (h2 : finrank D.host.E (Hp Λ F F'') = D.R.k - 1)
    (hs : s0 Λ F F' F'' β D.R.k = 1) : VanishingOnXAndXPlusGluing.HyperplaneEquality D Λ F F' F'' β :=
  radicals_eq_theta_at_unit_index hU' hN' hU'' hN'' D.R.k h1 h2 hs

end D7

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem d_starConj (D : D7) : StarConj D.host.E := by
  intro τ x
  have := D.host.isCMField_hostE
  change τ (NumberField.IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj]

theorem d_isComplex (D : D7) (w : InfinitePlace D.host.E) : w.IsComplex := by
  have := D.host.isCMField_hostE
  exact NumberField.IsTotallyComplex.isComplex w

theorem d_card (D : D7) : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  have := D.host.isCMField_hostE
  have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord :=
    D.host.finrank_cmField
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
  have h3 : NumberField.InfinitePlace.nrRealPlaces D.host.E = 0 :=
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E
  have h4 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E
  simp only [Ranks.f, Ranks.n]
  rw [h1] at h2
  omega

theorem d_form_ext (A B C Dd ε : ℂ) (T T' : ℝ) (hε : ε.im ≠ 0)
    (h10 : T * ‖A * 1 + B * 0‖ ^ 2 - T' * ‖C * 1 + Dd * 0‖ ^ 2 = T * ‖(1 : ℂ)‖ ^ 2 - T' * ‖(0 : ℂ)‖ ^ 2)
    (h01 : T * ‖A * 0 + B * 1‖ ^ 2 - T' * ‖C * 0 + Dd * 1‖ ^ 2 = T * ‖(0 : ℂ)‖ ^ 2 - T' * ‖(1 : ℂ)‖ ^ 2)
    (h11 : T * ‖A * 1 + B * 1‖ ^ 2 - T' * ‖C * 1 + Dd * 1‖ ^ 2 = T * ‖(1 : ℂ)‖ ^ 2 - T' * ‖(1 : ℂ)‖ ^ 2)
    (hε1 : T * ‖A * ε + B * 1‖ ^ 2 - T' * ‖C * ε + Dd * 1‖ ^ 2 = T * ‖ε‖ ^ 2 - T' * ‖(1 : ℂ)‖ ^ 2)
    (u v : ℂ) :
    T * ‖A * u + B * v‖ ^ 2 - T' * ‖C * u + Dd * v‖ ^ 2 = T * ‖u‖ ^ 2 - T' * ‖v‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im] at *
  have hXre : T * (A.re * B.re + A.im * B.im) - T' * (C.re * Dd.re + C.im * Dd.im) = 0 := by
    linear_combination (h11 - h10 - h01) / 2
  have hXim' : (T * (A.im * B.re - A.re * B.im) - T' * (C.im * Dd.re - C.re * Dd.im)) * ε.im = 0 := by
    linear_combination ε.re * hXre - (1 / 2) * (hε1 - (ε.re * ε.re + ε.im * ε.im) * h10 - h01)
  have hXim : T * (A.im * B.re - A.re * B.im) - T' * (C.im * Dd.re - C.re * Dd.im) = 0 :=
    (mul_eq_zero.1 hXim').resolve_right hε
  linear_combination (u.re * u.re + u.im * u.im) * h10 + (v.re * v.re + v.im * v.im) * h01 +
    2 * (u.re * v.re + u.im * v.im) * hXre - 2 * (u.im * v.re - u.re * v.im) * hXim

theorem d_pq (T p q C S : ℝ) (h : p - q = T) (hCS : C ^ 2 - S ^ 2 = 1) (hx : S ^ 2 * p = C ^ 2 * q) :
    p = T * C ^ 2 ∧ q = T * S ^ 2 := by
  have h1 : p = T * C ^ 2 := by linear_combination (-p) * hCS - hx + C ^ 2 * h
  exact ⟨h1, by linear_combination h1 - h + T * hCS⟩

theorem d_place_real (T T' p q C' S' C'' S'' A1 A2 : ℝ) (hT : 0 < T) (hT' : 0 < T')
    (hC' : 0 ≤ C') (hS' : 0 ≤ S') (hC'' : 0 ≤ C'') (hS'' : 0 ≤ S'') (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hp : p = T * C' ^ 2) (hq : q = T * S' ^ 2) (h1 : T' * A1 ^ 2 = S'' ^ 2 * p)
    (h2 : T' * A2 ^ 2 = C'' ^ 2 * q) :
    T' * (A1 + A2) ^ 2 / T = (C' * S'' + S' * C'') ^ 2 := by
  subst hp hq
  have hsq : (T' * A1 * A2) ^ 2 = (T * (S'' * C') * (C'' * S')) ^ 2 := by
    linear_combination (T' * A2 ^ 2) * h1 + (S'' ^ 2 * (T * C' ^ 2)) * h2
  have hx : T' * A1 * A2 = T * (S'' * C') * (C'' * S') :=
    (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  rw [div_eq_iff hT.ne']
  linear_combination h1 + h2 + 2 * hx

theorem d_prod_emb {K : Type} [Field K] [NumberField K] (hc : ∀ w : InfinitePlace K, w.IsComplex)
    (X : (K →+* ℂ) → ℝ) (hX : ∀ τ, X (ComplexEmbedding.conjugate τ) = X τ) (h0 : ∀ τ, 0 ≤ X τ) :
    Real.sqrt (∏ τ : K →+* ℂ, X τ) = ∏ w : InfinitePlace K, X w.embedding := by
  classical
  have h1 : ∀ τ, X τ = X (InfinitePlace.mk τ).embedding := by
    intro τ
    rcases InfinitePlace.embedding_mk_eq τ with h | h <;> rw [h]
    exact (hX τ).symm
  have h2 : ∏ τ : K →+* ℂ, X τ = ∏ w : InfinitePlace K, (X w.embedding) ^ 2 := by
    rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk X]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => X w.embedding)
      (fun τ hτ => by rw [h1 τ, (Finset.mem_filter.1 hτ).2]), Finset.prod_const,
      InfinitePlace.card_filter_mk_eq, InfinitePlace.mult,
      if_neg (InfinitePlace.not_isReal_iff_isComplex.2 (hc w))]
  rw [h2, Finset.prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun w _ => h0 _)]

section Vec

variable {D : D7} {Λ : Formalism.MainNotions.S.UnitaryVolumeMass.Lt D} {T T' : ℕ}

theorem d_sg_add {F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T} {F' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T'} {y₁ y₂ y₁' y₂' : (hS D).V}
    {a₁ a₂ a₁' a₂' : D.host.E} (h₁ : SgRel F F' y₁ y₁' a₁ a₁') (h₂ : SgRel F F' y₂ y₂' a₂ a₂') :
    SgRel F F' (y₁ + y₂) (y₁' + y₂') (a₁ + a₂) (a₁' + a₂') := by
  obtain ⟨x, hx, x', hx', e⟩ := h₁
  obtain ⟨w, hw, w', hw', e2⟩ := h₂
  refine ⟨x + w, add_mem hx hw, x' + w', add_mem hx' hw', ?_⟩
  have : (y₁ + y₂) - (y₁' + y₂') = (y₁ - y₁') + (y₂ - y₂') := by abel
  rw [this, e, e2, add_smul, add_smul]
  abel

theorem d_nrm_zero (τ : D.host.E →+* ℂ) : nrm (hS D) τ 0 = 0 := by simp [nrm]

theorem d_chSh_nonneg (F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T) (F' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T') (τ : D.host.E →+* ℂ) :
    0 ≤ chSh T T' F F' τ := by
  unfold chSh
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem d_invSh_nonneg (F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T) (F' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T') (τ : D.host.E →+* ℂ) :
    0 ≤ invSh T T' F F' τ := by
  unfold invSh
  split_ifs
  · exact le_rfl
  · exact div_nonneg zero_le_one (Real.sqrt_nonneg _)

theorem d_split {F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T} {F' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T'} (h2 : Formalism.MainNotions.S.UnitaryVolumeMass.Lem2 D Λ T T' F F')
    (τ : D.host.E →+* ℂ) {y y' : (hS D).V} (hy : y ∈ Ylift Λ F F') (hy' : y' ∈ Ylift' Λ F F')
    {al al' : D.host.E} (h : SgRel F F' y y' al al') :
    ∃ a₁ a₁' a₂ a₂' : D.host.E, al = a₁ + a₂ ∧ al' = a₁' + a₂' ∧
      (T : ℝ) * ‖τ a₁‖ ^ 2 = chSh T T' F F' τ ^ 2 * nrm (hS D) τ y ∧
      (T' : ℝ) * ‖τ a₁'‖ ^ 2 = invSh T T' F F' τ ^ 2 * nrm (hS D) τ y ∧
      (T : ℝ) * ‖τ a₂‖ ^ 2 = invSh T T' F F' τ ^ 2 * nrm (hS D) τ y' ∧
      (T' : ℝ) * ‖τ a₂'‖ ^ 2 = chSh T T' F F' τ ^ 2 * nrm (hS D) τ y' ∧
      nrm (hS D) τ y = (T : ℝ) * ‖τ a₁‖ ^ 2 - (T' : ℝ) * ‖τ a₁'‖ ^ 2 ∧
      - nrm (hS D) τ y' = (T : ℝ) * ‖τ a₂‖ ^ 2 - (T' : ℝ) * ‖τ a₂'‖ ^ 2 := by
  obtain ⟨hi, -, -, hiv, hv1, hv2⟩ := h2
  obtain ⟨p1, hp1, -⟩ := hi y hy 0 (zero_mem _)
  obtain ⟨p2, hp2, -⟩ := hi 0 (zero_mem _) y' hy'
  have hadd := d_sg_add hp1 hp2
  rw [add_zero, zero_add] at hadd
  have huniq := (hi y hy y' hy').unique (y₁ := (al, al')) (y₂ := (p1.1 + p2.1, p1.2 + p2.2)) h hadd
  have e1 : al = p1.1 + p2.1 := congrArg Prod.fst huniq
  have e2 : al' = p1.2 + p2.2 := congrArg Prod.snd huniq
  have v1 := hv1 τ y hy 0 (zero_mem _) p1.1 p1.2 hp1
  have v2 := hv2 τ 0 (zero_mem _) y' hy' p2.1 p2.2 hp2
  have iv1 := hiv τ y hy 0 (zero_mem _) p1.1 p1.2 hp1
  have iv2 := hiv τ 0 (zero_mem _) y' hy' p2.1 p2.2 hp2
  rw [d_nrm_zero, sub_zero] at iv1
  rw [d_nrm_zero, zero_sub] at iv2
  exact ⟨p1.1, p1.2, p2.1, p2.2, e1, e2, v1.1, v1.2, v2.1, v2.2, iv1, iv2⟩

theorem d_norms {F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T} {F' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T'} (hT : 0 < T) (h2 : Formalism.MainNotions.S.UnitaryVolumeMass.Lem2 D Λ T T' F F')
    (τ : D.host.E →+* ℂ) {y y' : (hS D).V} (hy : y ∈ Ylift Λ F F') (hy' : y' ∈ Ylift' Λ F F')
    (h : SgRel F F' y y' 1 0) :
    nrm (hS D) τ y = (T : ℝ) * chSh T T' F F' τ ^ 2 ∧
      nrm (hS D) τ y' = (T : ℝ) * invSh T T' F F' τ ^ 2 := by
  obtain ⟨a₁, a₁', a₂, a₂', e1, e2, v1, v2, v3, v4, i1, i2⟩ := d_split h2 τ hy hy' h
  have iv0 := h2.2.2.2.1 τ y hy y' hy' 1 0 h
  simp only [map_one, map_zero, norm_one, norm_zero, one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, sub_zero] at iv0
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have e3 : ‖τ a₁'‖ = ‖τ a₂'‖ := by
    have : a₁' = - a₂' := by linear_combination -e2
    rw [this, map_neg, norm_neg]
  have hx : invSh T T' F F' τ ^ 2 * nrm (hS D) τ y = chSh T T' F F' τ ^ 2 * nrm (hS D) τ y' := by
    rw [← v2, ← v4, e3]
  have hCS : chSh T T' F F' τ ^ 2 - invSh T T' F F' τ ^ 2 = 1 := by
    by_cases hp : nrm (hS D) τ y = 0
    · have hq : nrm (hS D) τ y' ≠ 0 := by
        intro hq
        rw [hp, hq] at iv0
        linarith
      have : (chSh T T' F F' τ ^ 2 - invSh T T' F F' τ ^ 2 - 1) * nrm (hS D) τ y' = 0 := by
        linear_combination i2 + v3 - v4
      have := (mul_eq_zero.1 this).resolve_right hq
      linarith
    · have : (chSh T T' F F' τ ^ 2 - invSh T T' F F' τ ^ 2 - 1) * nrm (hS D) τ y = 0 := by
        linear_combination (-1 : ℝ) * i1 - v1 + v2
      have := (mul_eq_zero.1 this).resolve_right hp
      linarith
  exact d_pq _ _ _ _ _ iv0 hCS hx

end Vec

section ThmB

variable {D : D7} {Λ : Formalism.MainNotions.S.UnitaryVolumeMass.Lt D} {T T' : ℕ}

def d_IsGamma (Λ : Formalism.MainNotions.S.UnitaryVolumeMass.Lt D) (F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T) (F' F'' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T')
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V) (a b c d : D.host.E) : Prop :=
  ∀ y1 ∈ Ylift Λ F F', ∀ y2 ∈ Ylift Λ F F'', ∀ y1' ∈ Ylift' Λ F F', ∀ y2'' ∈ Ylift' Λ F F'',
    y1 - y2 ∈ Xsp F → y2'' - β y1' ∈ Xsp F'' →
      ∀ al al' : D.host.E, SgRel F F' y1 y1' al al' →
        SgRel F F'' y2 y2'' (a * al + b * al') (c * al + d * al')

def d_NormalsAgree (Λ : Formalism.MainNotions.S.UnitaryVolumeMass.Lt D) (F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T) (F' F'' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T')
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V) : Prop :=
  (∀ y ∈ Ylift Λ F F', y ∈ Ylift Λ F F'') ∧ (∀ y' ∈ Ylift' Λ F F', β y' ∈ Ylift' Λ F F'')

theorem d_ch_conj (F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T) (F' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T') (τ : D.host.E →+* ℂ) :
    ch T T' F F' (ComplexEmbedding.conjugate τ) = ch T T' F F' τ := by
  unfold ch
  rw [ComplexEmbedding.conjugate_coe_eq, RCLike.norm_conj]

theorem d_chSh_conj (F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T) (F' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T') (τ : D.host.E →+* ℂ) :
    chSh T T' F F' (ComplexEmbedding.conjugate τ) = chSh T T' F F' τ := by
  unfold chSh sh
  rw [d_ch_conj]

theorem d_invSh_conj (F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T) (F' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T') (τ : D.host.E →+* ℂ) :
    invSh T T' F F' (ComplexEmbedding.conjugate τ) = invSh T T' F F' τ := by
  unfold invSh sh
  rw [d_ch_conj]

theorem d_exists_nonreal (D : D7) (φ : D.host.E →+* ℂ) : ∃ x : D.host.E, (φ x).im ≠ 0 := by
  have h := d_isComplex D (InfinitePlace.mk φ)
  rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff] at h
  by_contra hcon
  push Not at hcon
  apply h
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hcon x)

theorem d_gamma_form {F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T} {F' F'' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T'}
    {β : (hS D).V ≃ₗ[D.host.E] (hS D).V}
    (h2' : Formalism.MainNotions.S.UnitaryVolumeMass.Lem2 D Λ T T' F F') (h2'' : Formalism.MainNotions.S.UnitaryVolumeMass.Lem2 D Λ T T' F F'')
    (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT) (hN : d_NormalsAgree Λ F F' F'' β)
    {a b c d : D.host.E} (G1 : d_IsGamma Λ F F' F'' β a b c d)
    (τ : D.host.E →+* ℂ) (al al' : D.host.E) :
    (T : ℝ) * ‖τ (a * al + b * al')‖ ^ 2 - (T' : ℝ) * ‖τ (c * al + d * al')‖ ^ 2 =
      (T : ℝ) * ‖τ al‖ ^ 2 - (T' : ℝ) * ‖τ al'‖ ^ 2 := by
  obtain ⟨y, hy, y', hy', h⟩ := h2'.2.2.1 al al'
  have h'' := G1 y hy y (hN.1 y hy) y' hy' (β y') (hN.2 y' hy') (by simp) (by simp) al al' h
  have e1 := h2'.2.2.2.1 τ y hy y' hy' al al' h
  have e2 := h2''.2.2.2.1 τ y (hN.1 y hy) (β y') (hN.2 y' hy') _ _ h''
  have e3 : nrm (hS D) τ (β y') = nrm (hS D) τ y' := by
    unfold nrm
    rw [hβ y' y']
  rw [e3] at e2
  rw [← e2, e1]

theorem d_gamma_place {F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T} {F' F'' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T'}
    {β : (hS D).V ≃ₗ[D.host.E] (hS D).V} (hT : 0 < T) (hT' : 0 < T')
    (h2' : Formalism.MainNotions.S.UnitaryVolumeMass.Lem2 D Λ T T' F F') (h2'' : Formalism.MainNotions.S.UnitaryVolumeMass.Lem2 D Λ T T' F F'')
    (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT) (hN : d_NormalsAgree Λ F F' F'' β)
    {a b c d : D.host.E} (G1 : d_IsGamma Λ F F' F'' β a b c d) (τ : D.host.E →+* ℂ) :
    (T' : ℝ) * ‖τ c‖ ^ 2 / T ≤
      (chSh T T' F F' τ * invSh T T' F F'' τ + invSh T T' F F' τ * chSh T T' F F'' τ) ^ 2 := by
  obtain ⟨y, hy, y', hy', h⟩ := h2'.2.2.1 1 0
  have h'' := G1 y hy y (hN.1 y hy) y' hy' (β y') (hN.2 y' hy') (by simp) (by simp) 1 0 h
  obtain ⟨hp, hq⟩ := d_norms hT h2' τ hy hy' h
  have e3 : nrm (hS D) τ (β y') = nrm (hS D) τ y' := by
    unfold nrm
    rw [hβ y' y']
  obtain ⟨a₁, c₁, a₂, c₂, -, ec, -, v2, -, v4, -, -⟩ :=
    d_split h2'' τ (hN.1 y hy) (hN.2 y' hy') h''
  rw [e3] at v4
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hTr' : (0 : ℝ) < T' := by exact_mod_cast hT'
  have hc : c = c₁ + c₂ := by rw [← ec]; ring
  have hle : ‖τ c‖ ≤ ‖τ c₁‖ + ‖τ c₂‖ := by
    rw [hc, map_add]
    exact norm_add_le _ _
  rw [← d_place_real T T' _ _ _ _ _ _ ‖τ c₁‖ ‖τ c₂‖ hTr hTr' (d_chSh_nonneg F F' τ)
    (d_invSh_nonneg F F' τ) (d_chSh_nonneg F F'' τ) (d_invSh_nonneg F F'' τ) (norm_nonneg _)
    (norm_nonneg _) hp hq v2 v4]
  have : ‖τ c‖ ^ 2 ≤ (‖τ c₁‖ + ‖τ c₂‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  gcongr

theorem d_scalar_of_one {F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T} {F' F'' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T'}
    {β : (hS D).V ≃ₗ[D.host.E] (hS D).V}
    (h2' : Formalism.MainNotions.S.UnitaryVolumeMass.Lem2 D Λ T T' F F') (h2'' : Formalism.MainNotions.S.UnitaryVolumeMass.Lem2 D Λ T T' F F'')
    (G1 : d_IsGamma Λ F F' F'' β 1 0 0 1) : IsScalar Λ F F' F'' β := by
  intro y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hx hx'' al al'
  constructor
  · intro h
    have := G1 y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hx hx'' al al' h
    simpa using this
  · intro h
    obtain ⟨p, hp, -⟩ := h2'.1 y1 hy1 y1' hy1'
    have h3 := G1 y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hx hx'' p.1 p.2 hp
    simp only [one_mul, zero_mul, add_zero, zero_add] at h3
    have h4 := (h2''.1 y2 hy2 y2'' hy2'').unique (y₁ := p) (y₂ := (al, al')) h3 h
    rw [h4] at hp
    exact hp

theorem d_thmB_of_gamma (D : D7) (Λ : Formalism.MainNotions.S.UnitaryVolumeMass.Lt D) (T T' g : ℕ) (F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T)
    (F' F'' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (hT : 3 ≤ T) (hT' : 3 ≤ T') (hg : 1 ≤ g)
    (h2' : Formalism.MainNotions.S.UnitaryVolumeMass.Lem2 D Λ T T' F F') (h2'' : Formalism.MainNotions.S.UnitaryVolumeMass.Lem2 D Λ T T' F F'')
    (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT) (hN : d_NormalsAgree Λ F F' F'' β)
    (a b c d : D.host.E) (G1 : d_IsGamma Λ F F' F'' β a b c d)
    (G2 : ∀ p ∈ (Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZ g : Set (D.host.E × D.host.E)),
      (a * p.1 + b * p.2, c * p.1 + d * p.2) ∈ (Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZ g : Set (D.host.E × D.host.E)))
    (G3 : ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → ((T : 𝓞 D.host.E) ∈ P ∨ (T' : 𝓞 D.host.E) ∈ P) →
      Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P (a - 1) T ∧ Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P c T ∧ Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P b T' ∧
        Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P (d - 1) T') :
    Formalism.MainNotions.S.UnitaryVolumeMass.ThmB D Λ T T' g F F' F'' β := by
  set X : (D.host.E →+* ℂ) → ℝ := fun τ =>
    chSh T T' F F' τ * invSh T T' F F'' τ + invSh T T' F F' τ * chSh T T' F F'' τ with hX
  have hX0 : ∀ τ, 0 ≤ X τ := fun τ =>
    add_nonneg (mul_nonneg (d_chSh_nonneg F F' τ) (d_invSh_nonneg F F'' τ))
      (mul_nonneg (d_invSh_nonneg F F' τ) (d_chSh_nonneg F F'' τ))
  have hXc : ∀ τ, X (ComplexEmbedding.conjugate τ) = X τ := by
    intro τ
    simp only [hX, d_chSh_conj, d_invSh_conj]
  have hform : ∀ (φ : D.host.E →+* ℂ) (u v : ℂ),
      (T : ℝ) * ‖φ a * u + φ b * v‖ ^ 2 - (T' : ℝ) * ‖φ c * u + φ d * v‖ ^ 2 =
        (T : ℝ) * ‖u‖ ^ 2 - (T' : ℝ) * ‖v‖ ^ 2 := by
    intro φ u v
    obtain ⟨ε, hε⟩ := d_exists_nonreal D φ
    have hE := d_gamma_form h2' h2'' hβ hN G1 φ
    refine d_form_ext (φ a) (φ b) (φ c) (φ d) (φ ε) T T' hε ?_ ?_ ?_ ?_ u v
    · simpa only [map_add, map_mul, map_one, map_zero] using hE 1 0
    · simpa only [map_add, map_mul, map_one, map_zero] using hE 0 1
    · simpa only [map_add, map_mul, map_one, map_zero] using hE 1 1
    · simpa only [map_add, map_mul, map_one, map_zero] using hE ε 1
  have hcore := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.thmB D.host.E (starRingEnd D.host.E)
    (fun φ x => d_starConj D φ x) (d_isComplex D) T T' g a b c d (fun w => X w.embedding) hT hT' hg
    hform G2 G3 (fun w => hX0 _)
    (fun w => by
      rw [← InfinitePlace.norm_embedding_eq w c]
      exact d_gamma_place (by omega) (by omega) h2' h2'' hβ hN G1 w.embedding)
  rcases hcore with ⟨ha, hb, hc, hd⟩ | hbig
  · left
    subst ha hb hc hd
    exact d_scalar_of_one h2' h2'' G1
  · right
    rw [d_card D] at hbig
    unfold placeProd
    rw [d_prod_emb (d_isComplex D) X hXc hX0]
    exact hbig

end ThmB

section Gen2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem d_symm_zero {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [a_herm x y, h, star_zero]

theorem d_orth_orth (U : Submodule E S.V) (hc : IsCompl U (orth S U)) : orth S (orth S U) = U := by
  have hle : U ≤ orth S (orth S U) := by
    intro u hu
    rw [a_mem_orth]
    intro x hx
    exact d_symm_zero ((a_mem_orth U x).1 hx u hu)
  refine le_antisymm ?_ hle
  intro y hy
  have hy' : y ∈ U ⊔ orth S U := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, h, hh, rfl⟩ := Submodule.mem_sup.1 hy'
  have hh2 : h ∈ orth S (orth S U) := by
    have := Submodule.sub_mem _ hy (hle hu)
    simpa using this
  have h0 : h = 0 := by
    apply S.nondeg.2 h
    intro v
    have hv : v ∈ U ⊔ orth S U := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u', hu', h', hh', rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, LinearMap.add_apply, (a_mem_orth U h).1 hh u' hu',
      (a_mem_orth (orth S U) h).1 hh2 h' hh', add_zero]
  rw [h0, add_zero]
  exact hu

theorem d_Xflag_r {T : E} (F : LFlag S r T) : Xflag F r = Xsp F := by
  change Submodule.span E (F.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range F.fl.e)
  congr 1
  ext v
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩

variable {Λ : Submodule (𝓞 E) S.V} {T T' : E} {F : LFlag S r T} {F' F'' : LFlag S r T'}
  {β : S.V ≃ₗ[E] S.V} {g : ℕ}

theorem d_map_X (hp : IsPair Λ F F' F'' β g) : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'' := by
  rw [← d_Xflag_r F', ← d_Xflag_r F'']
  exact hp.2.1 r

theorem d_map_Xplus (hp : IsPair Λ F F' F'' β g) :
    (Xplus F').map (β : S.V →ₗ[E] S.V) = Xplus F'' := by
  change (Xsp F' ⊔ Submodule.span E {F'.fl.z}).map (β : S.V →ₗ[E] S.V) =
    Xsp F'' ⊔ Submodule.span E {F''.fl.z}
  rw [Submodule.map_sup, d_map_X hp, Submodule.map_span, Set.image_singleton]
  congr 3
  exact hp.2.2.1

theorem d_beta_orth (hp : IsPair Λ F F' F'' β g) {y' : S.V} (hy' : y' ∈ orth S (Xplus F')) :
    β y' ∈ orth S (Xplus F'') := by
  rw [a_mem_orth]
  intro x hx
  rw [← d_map_Xplus hp] at hx
  obtain ⟨x0, hx0, rfl⟩ := hx
  have := hp.1.1 x0 y'
  change S.hT (β x0) (β y') = 0
  rw [this]
  exact (a_mem_orth _ _).1 hy' x0 hx0

theorem d_Th''_cases {x₂ : S.V} (h : x₂ ∈ Th'' Λ F F' F'' β) :
    ∃ x₁ ∈ Hp Λ F F', x₁ - x₂ ∈ Xsp F ∧ β x₁ - x₂ ∈ Xsp F'' := by
  obtain ⟨pr, hpr, rfl⟩ := h
  obtain ⟨⟨h1, h2⟩, h3⟩ := hpr
  exact ⟨pr.1, h1.1, h2, h3⟩

theorem d_normals_gen (hp : IsPair Λ F F' F'' β g) (hc : IsCompl (UUE Λ F F'') (Hp Λ F F''))
    (hA3 : Hp Λ F F'' = Th'' Λ F F' F'' β) :
    (∀ y ∈ Ylift Λ F F', y ∈ Ylift Λ F F'') ∧ (∀ y' ∈ Ylift' Λ F F', β y' ∈ Ylift' Λ F F'') := by
  have hoo : orth S (Hp Λ F F'') = UUE Λ F F'' := d_orth_orth _ hc
  constructor
  · intro y hy
    refine ⟨?_, hy.2⟩
    change y ∈ UUE Λ F F''
    rw [← hoo, a_mem_orth]
    intro x₂ hx₂
    rw [hA3] at hx₂
    obtain ⟨x₁, hx₁, h1, -⟩ := d_Th''_cases hx₂
    have e1 : S.hT x₁ y = 0 := d_symm_zero ((a_mem_orth _ _).1 hx₁ y hy.1)
    have e2 : S.hT (x₁ - x₂) y = 0 :=
      (a_mem_orth _ _).1 hy.2 _ (Submodule.mem_sup_left h1)
    rw [map_sub, LinearMap.sub_apply, e1, zero_sub, neg_eq_zero] at e2
    exact e2
  · intro y' hy'
    have hb := d_beta_orth hp hy'.2
    refine ⟨?_, hb⟩
    change β y' ∈ UUE Λ F F''
    rw [← hoo, a_mem_orth]
    intro x₂ hx₂
    rw [hA3] at hx₂
    obtain ⟨x₁, hx₁, -, h2⟩ := d_Th''_cases hx₂
    have e1 : S.hT (β x₁) (β y') = 0 := by
      rw [hp.1.1 x₁ y']
      exact d_symm_zero ((a_mem_orth _ _).1 hx₁ y' hy'.1)
    have e2 : S.hT (β x₁ - x₂) (β y') = 0 :=
      (a_mem_orth _ _).1 hb _ (Submodule.mem_sup_left h2)
    rw [map_sub, LinearMap.sub_apply, e1, zero_sub, neg_eq_zero] at e2
    exact e2

end Gen2

section Final

variable {D : D7} {Λ : Formalism.MainNotions.S.UnitaryVolumeMass.Lt D} {T T' : ℕ}

theorem d_sg_smul {F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T} {F' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T'} {y y' : (hS D).V} {a a' : D.host.E}
    (t : D.host.E) (h : SgRel F F' y y' a a') : SgRel F F' (t • y) (t • y') (t * a) (t * a') := by
  obtain ⟨x, hx, x', hx', e⟩ := h
  refine ⟨t • x, Submodule.smul_mem _ _ hx, t • x', Submodule.smul_mem _ _ hx', ?_⟩
  rw [← smul_sub, e]
  simp only [smul_add, smul_smul]

theorem d_sg_shift {F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T} {F' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T'} {y y' w w' : (hS D).V} {a a' : D.host.E}
    (h : SgRel F F' y y' a a') (hw : w ∈ Xsp F) (hw' : w' ∈ Xsp F') :
    SgRel F F' (y + w) (y' + w') a a' := by
  obtain ⟨x, hx, x', hx', e⟩ := h
  refine ⟨x + w, add_mem hx hw, x' - w', sub_mem hx' hw', ?_⟩
  have : (y + w) - (y' + w') = (y - y') + (w - w') := by abel
  rw [this, e]
  abel

theorem d_gamma_exists {F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T} {F' F'' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T'}
    {β : (hS D).V ≃ₗ[D.host.E] (hS D).V} {g : ℕ}
    (h2' : Formalism.MainNotions.S.UnitaryVolumeMass.Lem2 D Λ T T' F F') (h2'' : Formalism.MainNotions.S.UnitaryVolumeMass.Lem2 D Λ T T' F F'')
    (hp : IsPair Λ F F' F'' β g) (hN : d_NormalsAgree Λ F F' F'' β) :
    ∃ a b c d : D.host.E, d_IsGamma Λ F F' F'' β a b c d := by
  obtain ⟨u, hu, u', hu', h10⟩ := h2'.2.2.1 1 0
  obtain ⟨w, hw, w', hw', h01⟩ := h2'.2.2.1 0 1
  obtain ⟨p, hp1, -⟩ := h2''.1 u (hN.1 u hu) (β u') (hN.2 u' hu')
  obtain ⟨q, hq1, -⟩ := h2''.1 w (hN.1 w hw) (β w') (hN.2 w' hw')
  refine ⟨p.1, q.1, p.2, q.2, ?_⟩
  intro y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hx hx'' al al' h
  have hlin' := d_sg_add (d_sg_smul al h10) (d_sg_smul al' h01)
  simp only [mul_one, mul_zero, add_zero, zero_add] at hlin'
  have hii := h2'.2.1 y1 hy1 (al • u + al' • w)
    (add_mem (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hw)) y1' hy1' (al • u' + al' • w')
    (add_mem (Submodule.smul_mem _ _ hu') (Submodule.smul_mem _ _ hw')) al al' h hlin'
  have hlin'' := d_sg_add (d_sg_smul al hp1) (d_sg_smul al' hq1)
  have hX : y2 - (al • u + al' • w) ∈ Xsp F := by
    have := Submodule.sub_mem _ hii.1 hx
    have e : y1 - (al • u + al' • w) - (y1 - y2) = y2 - (al • u + al' • w) := by abel
    rwa [e] at this
  have hX'' : y2'' - (al • β u' + al' • β w') ∈ Xsp F'' := by
    have h1 : β (y1' - (al • u' + al' • w')) ∈ Xsp F'' := by
      rw [← d_map_X hp]
      exact ⟨_, hii.2, rfl⟩
    have := Submodule.add_mem _ hx'' h1
    have e : y2'' - β y1' + β (y1' - (al • u' + al' • w')) = y2'' - (al • β u' + al' • β w') := by
      simp only [map_sub, map_add, map_smul]
      abel
    rwa [e] at this
  have hfin := d_sg_shift hlin'' hX hX''
  have e1 : al • u + al' • w + (y2 - (al • u + al' • w)) = y2 := by abel
  have e2 : al • β u' + al' • β w' + (y2'' - (al • β u' + al' • β w')) = y2'' := by abel
  rw [e1, e2] at hfin
  have e3 : p.1 * al + q.1 * al' = al * p.1 + al' * q.1 := by ring
  have e4 : p.2 * al + q.2 * al' = al * p.2 + al' * q.2 := by ring
  rw [e3, e4]
  exact hfin

def TheoremBFirstTwoSteps (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (T' : ℕ) (Λ : Formalism.MainNotions.S.UnitaryVolumeMass.Lt D) (F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D (Tu D u)) (F' F'' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T')
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → s0 Λ F F' F'' β D.R.k = 1 →
    IsGeneric Λ (gS D) F F' → IsGeneric Λ (gS D) F F'' →
    ∀ a b c d : D.host.E, d_IsGamma Λ F F' F'' β a b c d →
      (∀ p ∈ (Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZ (gS D) : Set (D.host.E × D.host.E)),
        (a * p.1 + b * p.2, c * p.1 + d * p.2) ∈
          (Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZ (gS D) : Set (D.host.E × D.host.E))) ∧
      (∀ P : Ideal (𝓞 D.host.E), P.IsPrime →
        (((Tu D u : ℕ) : 𝓞 D.host.E) ∈ P ∨ (T' : 𝓞 D.host.E) ∈ P) →
        Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P (a - 1) (Tu D u) ∧ Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P c (Tu D u) ∧
          Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P b T' ∧ Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P (d - 1) T')

theorem d_gS_pos (D : D7) : 1 ≤ gS D :=
  Nat.succ_le_of_lt (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)

theorem d_normals {u : D.what₂.Word} {T' : ℕ} {F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D (Tu D u)} {F' F'' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T'}
    {β : (hS D).V ≃ₗ[D.host.E] (hS D).V}
    (hF : FixedHyp D Λ F) (hT'' : IsTerm Λ (gS D) F F'') (hp : IsPair Λ F F' F'' β (gS D))
    (hA3 : Formalism.MainNotions.S.UnitaryVolumeMass.HyperplaneEquality D Λ F F' F'' β) : d_NormalsAgree Λ F F' F'' β := by
  have hU : UUE Λ F F'' = U2 F F'' := a_HU Λ hF.1 F F'' hF.2.2.1.2 hT''.1.2
  have hc : IsCompl (UUE Λ F F'') (Hp Λ F F'') := by
    unfold Hp
    rw [hU]
    exact double_span_is_compl_orth F F'' hT''.2.2
  exact d_normals_gen hp hc hA3.2

theorem theorem_B_of_lemma_two_steps (D : D7) (h2 : VanishingOnXAndXPlusGluing.Conclusion2 D) (hA3 : VanishingOnXAndXPlusGluing.DefiniteRankOne D) (h12 : TheoremBFirstTwoSteps D) :
    VanishingOnXAndXPlusGluing.Conclusion4 D := by
  intro u T' Λ F F' F'' β hF hPr hT' hT'' hp hs hG' hG''
  have h2' := h2 u T' Λ F F' hF hPr hT'
  have h2'' := h2 u T' Λ F F'' hF hPr hT''
  have hN := d_normals hF hT'' hp (hA3 u T' Λ F F' F'' β hF hPr hT' hT'' hp hs)
  obtain ⟨a, b, c, d, G1⟩ := d_gamma_exists h2' h2'' hp hN
  obtain ⟨G2, G3⟩ := h12 u T' Λ F F' F'' β hF hPr hT' hT'' hp hs hG' hG'' a b c d G1
  exact d_thmB_of_gamma D Λ (Tu D u) T' (gS D) F F' F'' β hPr.2.1 hPr.2.2.2.1 (d_gS_pos D) h2' h2''
    hp.1.1 hN a b c d G1 G2 G3

end Final

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def d_sO (E : Type) [Field E] [NumberField E] [StarRing E] : 𝓞 E →+* 𝓞 E :=
  RingOfIntegers.mapRingHom (starRingEnd E)

theorem d_sO_coe (c : 𝓞 E) : ((d_sO E c : 𝓞 E) : E) = star (c : E) := rfl

theorem d_sO_sO (c : 𝓞 E) : d_sO E (d_sO E c) = c := by
  apply RingOfIntegers.ext
  rw [d_sO_coe, d_sO_coe, star_star]

def d_bar (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := Ideal.comap (d_sO E) P.asIdeal
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have h1 : d_sO E x ∈ Ideal.comap (d_sO E) P.asIdeal := by
      rw [Ideal.mem_comap, d_sO_sO]; exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0
    rw [← d_sO_sO x, h1, map_zero]

theorem d_mem_bar (P : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E) :
    s ∈ (d_bar P).asIdeal ↔ d_sO E s ∈ P.asIdeal := Iff.rfl

theorem d_nat_mem_bar (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) :
    (g : 𝓞 E) ∈ (d_bar P).asIdeal ↔ (g : 𝓞 E) ∈ P.asIdeal := by
  rw [d_mem_bar, map_natCast]

theorem d_int_of_local (x : E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : 𝓞 E, (s : E) * x = c) :
    ∃ c : 𝓞 E, (c : E) = x := by
  let I : Ideal (𝓞 E) :=
    { carrier := {s | ∃ c : 𝓞 E, (s : E) * x = c}
      add_mem' := by
        rintro a b ⟨c, hc⟩ ⟨d, hd⟩
        exact ⟨c + d, by push_cast; rw [add_mul, hc, hd]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro t a ⟨c, hc⟩
        exact ⟨t * c, by rw [smul_eq_mul]; push_cast; rw [mul_assoc, hc]⟩ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
    obtain ⟨s, hs, c, hc⟩ := h ⟨M, hM.isPrime, hM0⟩
    exact hs (hIM ⟨c, hc⟩)
  have h1 : (1 : 𝓞 E) ∈ I := by rw [hI]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, by rw [← hc]; simp⟩

end Loc

section Comp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def d_Comp {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (v : S.V) (a a' : E) : Prop :=
  ∃ x ∈ Xsp F, ∃ x' ∈ Xsp F', v = (a • F.fl.z + x) + (a' • F'.fl.z + x')

variable {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}

theorem d_comp_add {v w : S.V} {a a' b b' : E} (h₁ : d_Comp F F' v a a') (h₂ : d_Comp F F' w b b') :
    d_Comp F F' (v + w) (a + b) (a' + b') := by
  obtain ⟨x, hx, x', hx', e⟩ := h₁
  obtain ⟨y, hy, y', hy', e2⟩ := h₂
  refine ⟨x + y, add_mem hx hy, x' + y', add_mem hx' hy', ?_⟩
  rw [e, e2, add_smul, add_smul]
  abel

theorem d_comp_smul {v : S.V} {a a' : E} (t : E) (h : d_Comp F F' v a a') :
    d_Comp F F' (t • v) (t * a) (t * a') := by
  obtain ⟨x, hx, x', hx', e⟩ := h
  refine ⟨t • x, Submodule.smul_mem _ _ hx, t • x', Submodule.smul_mem _ _ hx', ?_⟩
  rw [e]
  simp only [smul_add, smul_smul]

theorem d_comp_X {x : S.V} (hx : x ∈ Xsp F) : d_Comp F F' x 0 0 :=
  ⟨x, hx, 0, zero_mem _, by simp⟩

theorem d_comp_X' {x : S.V} (hx : x ∈ Xsp F') : d_Comp F F' x 0 0 :=
  ⟨0, zero_mem _, x, hx, by simp⟩

theorem d_comp_alt : d_Comp F F' F.fl.z 1 0 := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩

theorem d_comp_alt_alt : d_Comp F F' F'.fl.z 0 1 := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩

theorem d_comp_mem {v : S.V} {a a' : E} (h : d_Comp F F' v a a') : v ∈ U2 F F' := by
  obtain ⟨x, hx, x', hx', rfl⟩ := h
  refine Submodule.add_mem_sup ?_ ?_
  · exact add_mem (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
      (Submodule.mem_sup_left hx)
  · exact add_mem (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
      (Submodule.mem_sup_left hx')

end Comp

section Comp2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'} {Λ : Submodule (𝓞 E) S.V}

theorem d_comp_unique (hI : HInd F F') {v : S.V} {a a' b b' : E} (h₁ : d_Comp F F' v a a')
    (h₂ : d_Comp F F' v b b') : a = b ∧ a' = b' := by
  obtain ⟨x, hx, x', hx', e⟩ := h₁
  obtain ⟨y, hy, y', hy', e2⟩ := h₂
  have h0 := a_coef_zero hI (c := a - b) (c' := a' - b') (x := x - y) (x' := x' - y')
    (Submodule.sub_mem _ hx hy) (Submodule.sub_mem _ hx' hy') (by
      have := sub_eq_zero.2 (e.symm.trans e2)
      rw [← this]
      simp only [sub_smul]
      abel)
  exact ⟨sub_eq_zero.1 h0.1, sub_eq_zero.1 h0.2⟩

theorem d_comp_neg {v : S.V} {a a' : E} (h : d_Comp F F' v a a') : d_Comp F F' (-v) (-a) (-a') := by
  have := d_comp_smul (-1 : E) h
  simpa using this

theorem d_comp_sub {v w : S.V} {a a' b b' : E} (h₁ : d_Comp F F' v a a') (h₂ : d_Comp F F' w b b') :
    d_Comp F F' (v - w) (a - b) (a' - b') := by
  have := d_comp_add h₁ (d_comp_neg h₂)
  simpa [sub_eq_add_neg] using this

theorem d_comp_osmul {v : S.V} {a a' : E} (t : 𝓞 E) (h : d_Comp F F' v a a') :
    d_Comp F F' (t • v) ((t : E) * a) ((t : E) * a') := by
  have := d_comp_smul (t : E) h
  rwa [show ((t : E) • v) = t • v from algebraMap_smul E t v] at this

theorem d_compUU (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) {m : S.V} (hm : m ∈ UU Λ F F') :
    ∃ c t : 𝓞 E, d_Comp F F' m c t := by
  unfold UU at hm
  obtain ⟨m1, hm1, w', hw', rfl⟩ := Submodule.mem_sup.1 hm
  obtain ⟨m2, hm2, x', hx', rfl⟩ := Submodule.mem_sup.1 hm1
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.1 hm2
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hw'
  refine ⟨c, t, ?_⟩
  rw [hz, hz']
  have h1 := d_comp_add (d_comp_add (d_comp_add (d_comp_X (F' := F') hx.2)
    (d_comp_osmul c (d_comp_alt (F := F) (F' := F')))) (d_comp_X' (F := F) hx'.2))
    (d_comp_osmul t (d_comp_alt_alt (F := F) (F' := F')))
  simpa using h1

theorem d_comp_frameAct (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (b : Fin (r + 1)) :
    d_Comp F F' (frameAct (frame F) ξ b) ((ξ (Fin.last r) b : 𝓞 E) : E) 0 := by
  refine ⟨∑ i : Fin r, ((ξ i.castSucc b : 𝓞 E) : E) • F.fl.e i, ?_, 0, zero_mem _, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · unfold frameAct
    rw [Fin.sum_univ_castSucc]
    simp only [a_frame_castSucc, a_frame_last, zero_smul, add_zero]
    abel

theorem d_comp_frame' (b : Fin (r + 1)) :
    d_Comp F F' (frame F' b) 0 (if b = Fin.last r then 1 else 0) := by
  refine Fin.lastCases ?_ (fun i => ?_) b
  · rw [a_frame_last, if_pos rfl]
    exact d_comp_alt_alt
  · rw [a_frame_castSucc, if_neg (Fin.castSucc_lt_last i).ne]
    exact d_comp_X' (Submodule.subset_span ⟨i, rfl⟩)

theorem d_compMplus (hz : F.zt = F.fl.z) {g : ℕ} (hg : g ≠ 0)
    {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)} (hξ : AdmWit Λ g F F' ξ) {m : S.V}
    (hm : m ∈ Mplus Λ g F F' ξ) :
    ∃ c t : 𝓞 E, d_Comp F F' ((g : E) • m) ((g : E) * c - t) t := by
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  unfold Mplus at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    rcases hx with (hx | hx) | hx
    · exact ⟨0, 0, by simpa using d_comp_smul (g : E) (d_comp_X (F' := F') hx.2)⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [hz]
      exact ⟨1, 0, by simpa using d_comp_smul (g : E) (d_comp_alt (F := F) (F' := F'))⟩
    · obtain ⟨b, rfl⟩ := hx
      rw [smul_smul, mul_inv_cancel₀ hgE, one_smul]
      have h1 := fun b => d_comp_sub (d_comp_frame' (F := F) (F' := F') b)
        (d_comp_frameAct (F := F) (F' := F') ξ b)
      refine Fin.lastCases ?_ (fun i => ?_) b
      · have h1 := h1 (Fin.last r)
        rw [hξ.2.1, if_pos rfl] at h1
        exact ⟨0, 1, by simpa using h1⟩
      · have h1 := h1 i.castSucc
        rw [hξ.1 _ _ (Fin.castSucc_lt_last i), if_neg (Fin.castSucc_lt_last i).ne] at h1
        exact ⟨0, 0, by simpa using h1⟩
  | zero => exact ⟨0, 0, by simpa using d_comp_X (F := F) (F' := F') (zero_mem _)⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, t, h⟩ := hx
    obtain ⟨c', t', h'⟩ := hy
    refine ⟨c + c', t + t', ?_⟩
    have := d_comp_add h h'
    rw [← smul_add] at this
    convert this using 1 <;> push_cast <;> ring
  | smul a x _ hx =>
    obtain ⟨c, t, h⟩ := hx
    refine ⟨a * c, a * t, ?_⟩
    have := d_comp_osmul a h
    rw [smul_comm] at this
    convert this using 1 <;> push_cast <;> ring

end Comp2

section NN

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

abbrev d_lp (P : HeightOneSpectrum (𝓞 E)) (L : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) S.V :=
  haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L

theorem d_mem_lp {P : HeightOneSpectrum (𝓞 E)} {L : Submodule (𝓞 E) S.V} {x : S.V} :
    x ∈ d_lp P L ↔ ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ L :=
  ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩⟩

theorem d_le_lp (P : HeightOneSpectrum (𝓞 E)) (L : Submodule (𝓞 E) S.V) : L ≤ d_lp P L :=
  fun x hx => d_mem_lp.2 ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hx⟩

theorem d_lp_mono (P : HeightOneSpectrum (𝓞 E)) {L M : Submodule (𝓞 E) S.V} (h : L ≤ M) :
    d_lp P L ≤ d_lp P M := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := d_mem_lp.1 hx
  exact d_mem_lp.2 ⟨s, hs, h hx⟩

theorem d_mul_notMem {P : HeightOneSpectrum (𝓞 E)} {s t : 𝓞 E} (hs : s ∉ P.asIdeal)
    (ht : t ∉ P.asIdeal) : s * t ∉ P.asIdeal := fun h =>
  (P.isPrime.mem_or_mem h).elim hs ht

def d_PInt (P : HeightOneSpectrum (𝓞 E)) (x : E) : Prop :=
  ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : 𝓞 E, (s : E) * x = c

theorem d_PInt_add {P : HeightOneSpectrum (𝓞 E)} {x y : E} (hx : d_PInt P x) (hy : d_PInt P y) :
    d_PInt P (x + y) := by
  obtain ⟨s, hs, c, hc⟩ := hx
  obtain ⟨t, ht, d, hd⟩ := hy
  refine ⟨s * t, d_mul_notMem hs ht, t * c + s * d, ?_⟩
  push_cast
  linear_combination (t : E) * hc + (s : E) * hd

theorem d_PInt_mul {P : HeightOneSpectrum (𝓞 E)} {x y : E} (hx : d_PInt P x) (hy : d_PInt P y) :
    d_PInt P (x * y) := by
  obtain ⟨s, hs, c, hc⟩ := hx
  obtain ⟨t, ht, d, hd⟩ := hy
  refine ⟨s * t, d_mul_notMem hs ht, c * d, ?_⟩
  push_cast
  linear_combination (t : E) * y * hc + (c : E) * hd

theorem d_PInt_int (P : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) : d_PInt P (c : E) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), c, by simp⟩

theorem d_PInt_zero (P : HeightOneSpectrum (𝓞 E)) : d_PInt P (0 : E) := by
  simpa using d_PInt_int P 0

theorem d_PInt_neg {P : HeightOneSpectrum (𝓞 E)} {x : E} (hx : d_PInt P x) : d_PInt P (-x) := by
  have := d_PInt_mul (d_PInt_int P (-1)) hx
  simpa using this

theorem d_PInt_cancel {P : HeightOneSpectrum (𝓞 E)} {x : E} {s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (hx : d_PInt P ((s : E) * x)) : d_PInt P x := by
  obtain ⟨t, ht, c, hc⟩ := hx
  exact ⟨t * s, d_mul_notMem ht hs, c, by push_cast; rw [← hc]; ring⟩

variable {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'} {Λ : Submodule (𝓞 E) S.V}

theorem d_osmul (t : 𝓞 E) (v : S.V) : t • v = (t : E) • v := (algebraMap_smul E t v).symm

theorem d_generic_int (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hI : HInd F F')
    (hU : HU Λ F F') {g : ℕ} (hg : g ≠ 0) (hgen : IsGeneric Λ g F F')
    (P : HeightOneSpectrum (𝓞 E)) {l₀ : S.V} (hl : l₀ ∈ Λ) {a a' : E}
    (hc : d_Comp F F' ((g : E) • l₀) a a') :
    d_PInt P a ∧ d_PInt P a' ∧ d_PInt P ((a + a') / g) := by
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  obtain ⟨ξ, hξ, hloc⟩ := hgen
  have hlU : l₀ ∈ UUE Λ F F' := by
    rw [hU]
    have := Submodule.smul_mem _ ((g : E)⁻¹) (d_comp_mem hc)
    rwa [smul_smul, inv_mul_cancel₀ hgE, one_smul] at this
  have hlB : l₀ ∈ d_lp P (BLat Λ F F') := d_le_lp P _ ⟨hl, hlU⟩
  by_cases hgP : (g : 𝓞 E) ∈ P.asIdeal
  · have e := (hloc P).1 hgP
    have hlM : l₀ ∈ d_lp P (Mplus Λ g F F' ξ) := by
      have h := hlB
      change l₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal _ at h
      rw [e] at h
      exact h
    obtain ⟨s, hs, hsm⟩ := d_mem_lp.1 hlM
    obtain ⟨c, t, h⟩ := d_compMplus hz hg hξ hsm
    have h2 := d_comp_osmul s hc
    rw [smul_comm] at h2
    obtain ⟨e1, e2⟩ := d_comp_unique hI h2 h
    refine ⟨⟨s, hs, (g : 𝓞 E) * c - t, by rw [e1]; push_cast; ring⟩, ⟨s, hs, t, e2⟩,
      ⟨s, hs, c, ?_⟩⟩
    field_simp
    linear_combination e1 + e2
  · have e := (hloc P).2 hgP
    have hlM : l₀ ∈ d_lp P (UU Λ F F') := by
      have h := hlB
      change l₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal _ at h
      rw [e] at h
      exact h
    obtain ⟨s, hs, hsm⟩ := d_mem_lp.1 hlM
    obtain ⟨c, t, h⟩ := d_compUU hz hz' hsm
    have h3 := d_comp_smul (g : E) h
    have h2 := d_comp_osmul s hc
    rw [smul_comm] at h2
    obtain ⟨e1, e2⟩ := d_comp_unique hI h2 h3
    refine ⟨⟨s, hs, (g : 𝓞 E) * c, by rw [e1]; push_cast; ring⟩,
      ⟨s, hs, (g : 𝓞 E) * t, by rw [e2]; push_cast; ring⟩, ⟨s, hs, c + t, ?_⟩⟩
    field_simp
    push_cast
    linear_combination e1 + e2

def d_NN (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T')
    (P : HeightOneSpectrum (𝓞 E)) (ta ta' : E) (y y' : S.V) : Prop :=
  ∃ θ ∈ Hp Λ F F', ∃ l ∈ d_lp P Λ, ∃ l' ∈ d_lp P Λ,
    θ + y + ta • F.fl.z - l ∈ Xsp F ∧ θ + y' + ta' • F'.fl.z - l' ∈ Xsp F' ∧
      l - l' ∈ d_lp P (NgX Λ g F F')

theorem d_NN_int (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hI : HInd F F')
    (hU : HU Λ F F') {g : ℕ} (hg : g ≠ 0) (hgen : IsGeneric Λ g F F')
    (P : HeightOneSpectrum (𝓞 E)) {ta ta' : E} {y y' : S.V} (hN : d_NN Λ g F F' P ta ta' y y')
    {a a' : E} (hc : d_Comp F F' (y - y') a a') :
    d_PInt P (a + ta) ∧ d_PInt P (a' - ta') ∧ d_PInt P ((a + ta + (a' - ta')) / g) := by
  obtain ⟨θ, -, l, -, l', -, h1, h2, h3⟩ := hN
  have hll : d_Comp F F' (l - l') (a + ta) (a' - ta') := by
    have e : l - l' = (y - y') + ta • F.fl.z - ta' • F'.fl.z - (θ + y + ta • F.fl.z - l) +
        (θ + y' + ta' • F'.fl.z - l') := by abel
    rw [e]
    have := d_comp_add (d_comp_sub (d_comp_sub (d_comp_add hc
      (d_comp_smul ta (d_comp_alt (F := F) (F' := F'))))
      (d_comp_smul ta' (d_comp_alt_alt (F := F) (F' := F')))) (d_comp_X (F' := F') h1))
      (d_comp_X' (F := F) h2)
    simpa using this
  obtain ⟨s, hs, hsm⟩ := d_mem_lp.1 h3
  unfold NgX at hsm
  obtain ⟨m1, hm1, x', hx', e1⟩ := Submodule.mem_sup.1 hsm
  obtain ⟨m2, hm2, x, hx, e2⟩ := Submodule.mem_sup.1 hm1
  rw [Submodule.ideal_span_singleton_smul] at hm2
  obtain ⟨l₀, hl₀, e3⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm2
  have hgl : d_Comp F F' ((g : E) • l₀) ((s : E) * (a + ta)) ((s : E) * (a' - ta')) := by
    have e : (g : E) • l₀ = s • (l - l') - x - x' := by
      rw [← e1, ← e2, ← e3, d_osmul]
      push_cast
      abel
    rw [e]
    have := d_comp_sub (d_comp_sub (d_comp_osmul s hll) (d_comp_X (F' := F') hx.2))
      (d_comp_X' (F := F) hx'.2)
    simpa using this
  obtain ⟨i1, i2, i3⟩ := d_generic_int hz hz' hI hU hg hgen P hl₀ hgl
  refine ⟨d_PInt_cancel hs i1, d_PInt_cancel hs i2, d_PInt_cancel hs ?_⟩
  have e : (s : E) * ((a + ta + (a' - ta')) / g) = ((s : E) * (a + ta) + (s : E) * (a' - ta')) / g := by
    ring
  rw [e]
  exact i3

end NN

section Transfer

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem d_orth_anti {U W : Submodule E S.V} (h : U ≤ W) : orth S W ≤ orth S U := by
  intro y hy
  rw [a_mem_orth] at hy ⊢
  exact fun x hx => hy x (h hx)

theorem d_z_orthX {T : E} (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  rw [a_mem_orth]
  intro x hx
  exact d_symm_zero (LinearMap.mem_ker.1 (a_z_X F hx))

theorem d_X_orthX {T : E} (F : LFlag S r T) : Xsp F ≤ orth S (Xsp F) :=
  (a_X_le_orth_Xplus F).trans (d_orth_anti le_sup_left)

variable {T T' : E} {F : LFlag S r T} {F' F'' : LFlag S r T'} {Λ : Submodule (𝓞 E) S.V}
  {β : S.V ≃ₗ[E] S.V} {g : ℕ}

theorem d_beta_osmul (s : 𝓞 E) (v : S.V) : β (s • v) = s • β v := by
  rw [d_osmul, d_osmul, map_smul]

theorem d_beta_Lam (hp : IsPair Λ F F' F'' β g) {v : S.V} (hv : v ∈ Λ) : β v ∈ Λ := by
  have h := hp.1.2
  rw [← h]
  exact ⟨v, hv, rfl⟩

theorem d_NN_transfer (hp : IsPair Λ F F' F'' β g) (hU' : HU Λ F F')
    (hA3 : Hp Λ F F' = Th Λ F F' F'' β) (P : HeightOneSpectrum (𝓞 E)) {ta ta' : E} {y y' : S.V}
    (hy : y ∈ orth S (Xplus F)) (hy' : y' ∈ orth S (Xplus F'))
    (hN : d_NN Λ g F F' P ta ta' y y') : d_NN Λ g F F'' P ta ta' y (β y') := by
  obtain ⟨θ, hθ, l, hl, l', hl', h1, h2, h3⟩ := hN
  have hθX : θ ∈ orth S (Xsp F) := d_orth_anti (a_X_le hU').1 hθ
  have hθX' : θ ∈ orth S (Xsp F') := d_orth_anti (a_X_le hU').2 hθ
  have hlX : l ∈ orth S (Xsp F) := by
    have e : l = θ + y + ta • F.fl.z - (θ + y + ta • F.fl.z - l) := by abel
    rw [e]
    exact sub_mem (add_mem (add_mem hθX (d_orth_anti le_sup_left hy))
      (Submodule.smul_mem _ _ (d_z_orthX F))) (d_X_orthX F h1)
  have hlX' : l' ∈ orth S (Xsp F') := by
    have e : l' = θ + y' + ta' • F'.fl.z - (θ + y' + ta' • F'.fl.z - l') := by abel
    rw [e]
    exact sub_mem (add_mem (add_mem hθX' (d_orth_anti le_sup_left hy'))
      (Submodule.smul_mem _ _ (d_z_orthX F'))) (d_X_orthX F' h2)
  rw [hA3] at hθ
  obtain ⟨pr, hpr, rfl⟩ := hθ
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hpr
  obtain ⟨s₁, hs₁, hl⟩ := d_mem_lp.1 hl
  obtain ⟨s₂, hs₂, hl'⟩ := d_mem_lp.1 hl'
  obtain ⟨s₃, hs₃, h3⟩ := d_mem_lp.1 h3
  refine ⟨pr.2, hp1.2, l, d_mem_lp.2 ⟨s₁, hs₁, hl⟩, β l',
    d_mem_lp.2 ⟨s₂, hs₂, by rw [← d_beta_osmul]; exact d_beta_Lam hp hl'⟩, ?_, ?_, ?_⟩
  · have e : pr.2 + y + ta • F.fl.z - l =
        (LinearMap.fst E S.V S.V pr + y + ta • F.fl.z - l) - (pr.1 - pr.2) := by
      simp only [LinearMap.fst_apply]
      abel
    rw [e]
    exact sub_mem h1 hp2
  · have hb : β (LinearMap.fst E S.V S.V pr + y' + ta' • F'.fl.z - l') ∈ Xsp F'' := by
      rw [← d_map_X hp]
      exact ⟨_, h2, rfl⟩
    have e : pr.2 + β y' + ta' • F''.fl.z - β l' =
        β (LinearMap.fst E S.V S.V pr + y' + ta' • F'.fl.z - l') - (β pr.1 - pr.2) := by
      simp only [LinearMap.fst_apply, map_sub, map_add, map_smul, hp.2.2.1]
      abel
    rw [e]
    exact sub_mem hb hp3
  · refine d_mem_lp.2 ⟨s₁ * s₂ * s₃, d_mul_notMem (d_mul_notMem hs₁ hs₂) hs₃, ?_⟩
    have a1 : (s₁ * s₂ * s₃) • l ∈ Lrep Λ F := by
      refine ⟨?_, Submodule.smul_mem _ _ hlX⟩
      have : (s₁ * s₂ * s₃) • l = (s₂ * s₃) • (s₁ • l) := by rw [smul_smul]; congr 1; ring
      rw [this]
      exact Submodule.smul_mem _ _ hl
    have a2 : (s₁ * s₂ * s₃) • l' ∈ Lrep Λ F' := by
      refine ⟨?_, Submodule.smul_mem _ _ hlX'⟩
      have : (s₁ * s₂ * s₃) • l' = (s₁ * s₃) • (s₂ • l') := by rw [smul_smul]; congr 1; ring
      rw [this]
      exact Submodule.smul_mem _ _ hl'
    have a3 : (s₁ * s₂ * s₃) • l - (s₁ * s₂ * s₃) • l' ∈ NgX Λ g F F' := by
      have : (s₁ * s₂ * s₃) • l - (s₁ * s₂ * s₃) • l' = (s₁ * s₂) • (s₃ • (l - l')) := by
        rw [smul_smul, smul_sub]
      rw [this]
      exact Submodule.smul_mem _ _ h3
    have := (hp.2.2.2 _ a2 _ a1).1 a3
    rwa [d_beta_osmul, ← smul_sub] at this

end Transfer

section Glue

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def d_Glue (Λ : Submodule (𝓞 E) S.V) : Prop :=
  ∀ U : Submodule E S.V, U ⊓ orth S U = ⊥ →
    {m | m ∈ U ∧ ∃ l ∈ Λ, l - m ∈ orth S U} = (dualIn S (Λ ⊓ toO S U) : Set S.V)

theorem d_one_notMem (P : HeightOneSpectrum (𝓞 E)) : (1 : 𝓞 E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem d_common (P : HeightOneSpectrum (𝓞 E)) (f : S.V → E) (G : Finset S.V)
    (h : ∀ m ∈ G, d_PInt P (f m)) :
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∀ m ∈ G, ∃ c : 𝓞 E, (s : E) * f m = c := by
  classical
  induction G using Finset.induction_on with
  | empty => exact ⟨1, d_one_notMem P, by simp⟩
  | insert a G ha ih =>
    obtain ⟨s, hs, hsG⟩ := ih (fun m hm => h m (Finset.mem_insert_of_mem hm))
    obtain ⟨t, ht, c, hc⟩ := h a (Finset.mem_insert_self _ _)
    refine ⟨s * t, d_mul_notMem hs ht, ?_⟩
    intro m hm
    rcases Finset.mem_insert.1 hm with rfl | hm
    · exact ⟨s * c, by push_cast; linear_combination (s : E) * hc⟩
    · obtain ⟨d, hd⟩ := hsG m hm
      exact ⟨t * d, by push_cast; linear_combination (t : E) * hd⟩

theorem d_hT_osmul (a : 𝓞 E) (x Y : S.V) :
    S.hT (a • x) Y = ((d_sO E a : 𝓞 E) : E) * S.hT x Y := by
  rw [d_osmul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, d_sO_coe, starRingEnd_apply]

theorem d_hT_osmul_right (a : 𝓞 E) (x Y : S.V) : S.hT x (a • Y) = (a : E) * S.hT x Y := by
  rw [d_osmul, map_smul, smul_eq_mul]

theorem d_PInt_span (P : HeightOneSpectrum (𝓞 E)) (Y : S.V) (G : Set S.V)
    (h : ∀ m ∈ G, d_PInt P (S.hT m Y)) : ∀ m ∈ Submodule.span (𝓞 E) G, d_PInt P (S.hT m Y) := by
  intro m hm
  induction hm using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simpa using d_PInt_zero P
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply]
    exact d_PInt_add hx hy
  | smul a x _ hx =>
    rw [d_hT_osmul]
    exact d_PInt_mul (d_PInt_int P _) hx

theorem d_mem_dual {L : Submodule (𝓞 E) S.V} {x : S.V} :
    x ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ ∀ m ∈ L, ∃ c : 𝓞 E, (c : E) = S.hT m x := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    Submodule.mem_one, LinearMap.restrictScalars_apply]

variable {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'} {Λ : Submodule (𝓞 E) S.V}

theorem d_glue (hΛ : Submodule.IsLattice E Λ) (hGl : d_Glue Λ)
    (hNd : UUE Λ F F' ⊓ orth S (UUE Λ F F') = ⊥) (P : HeightOneSpectrum (𝓞 E)) {Y : S.V}
    (hY : Y ∈ UUE Λ F F') (hint : ∀ m ∈ BLat Λ F F', d_PInt P (S.hT m Y)) :
    ∃ θ ∈ Hp Λ F F', θ + Y ∈ d_lp P Λ := by
  have hfg : (BLat Λ F F').FG := by
    have : IsNoetherian (𝓞 E) Λ := isNoetherian_of_fg_of_noetherian Λ hΛ.fg
    exact isNoetherian_submodule.1 this _ inf_le_left
  obtain ⟨G, hG⟩ := hfg
  obtain ⟨s, hs, hsG⟩ := d_common P (fun m => S.hT m Y) G (fun m hm => hint m (by
    rw [← hG]; exact Submodule.subset_span hm))
  have hall : ∀ m ∈ BLat Λ F F', ∃ c : 𝓞 E, (s : E) * S.hT m Y = c := by
    intro m hm
    rw [← hG] at hm
    induction hm using Submodule.span_induction with
    | mem x hx => exact hsG x hx
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, by rw [map_add, LinearMap.add_apply]; push_cast; linear_combination hc + hd⟩
    | smul a x _ hx =>
      obtain ⟨c, hc⟩ := hx
      exact ⟨d_sO E a * c, by
        rw [d_hT_osmul]; push_cast; linear_combination ((d_sO E a : 𝓞 E) : E) * hc⟩
  have hs0 : (s : E) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := RingOfIntegers.ext (by rw [h0]; rfl)
    rw [this]
    exact zero_mem _
  have hdual : s • Y ∈ dualIn S (Λ ⊓ toO S (UUE Λ F F')) := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [d_mem_dual]
      intro m hm
      obtain ⟨c, hc⟩ := hall m hm
      exact ⟨c, by rw [d_hT_osmul_right, hc]⟩
    · change s • Y ∈ Submodule.span E _
      rw [a_span_inf Λ hΛ, d_osmul]
      exact Submodule.smul_mem _ _ hY
  have hmem : s • Y ∈ {m | m ∈ UUE Λ F F' ∧ ∃ l ∈ Λ, l - m ∈ orth S (UUE Λ F F')} := by
    rw [hGl _ hNd]
    exact hdual
  obtain ⟨-, l₀, hl₀, hd⟩ := hmem
  refine ⟨(s : E)⁻¹ • (l₀ - s • Y), Submodule.smul_mem _ _ hd, d_mem_lp.2 ⟨s, hs, ?_⟩⟩
  have : s • ((s : E)⁻¹ • (l₀ - s • Y) + Y) = l₀ := by
    rw [d_osmul, d_osmul, smul_add, smul_smul, mul_inv_cancel₀ hs0, one_smul]
    abel
  rw [this]
  exact hl₀

theorem d_NN_of_int (hΛ : Submodule.IsLattice E Λ) (hGl : d_Glue Λ)
    (hNd : UUE Λ F F' ⊓ orth S (UUE Λ F F') = ⊥) (P : HeightOneSpectrum (𝓞 E)) {g : ℕ}
    {ta ta' : E} {y y' Y Y' : S.V}
    (hY : Y ∈ UUE Λ F F') (hint : ∀ m ∈ BLat Λ F F', d_PInt P (S.hT m Y))
    (hu : Y - Y' ∈ d_lp P (Ideal.span {(g : 𝓞 E)} • Λ))
    (h1 : y + ta • F.fl.z - Y ∈ Xsp F) (h2 : y' + ta' • F'.fl.z - Y' ∈ Xsp F') :
    d_NN Λ g F F' P ta ta' y y' := by
  obtain ⟨θ, hθ, hl⟩ := d_glue hΛ hGl hNd P hY hint
  refine ⟨θ, hθ, θ + Y, hl, θ + Y', ?_, ?_, ?_, ?_⟩
  · have e : θ + Y' = (θ + Y) - (Y - Y') := by abel
    rw [e]
    exact sub_mem hl (d_lp_mono P Submodule.smul_le_right hu)
  · have e : θ + y + ta • F.fl.z - (θ + Y) = y + ta • F.fl.z - Y := by abel
    rw [e]; exact h1
  · have e : θ + y' + ta' • F'.fl.z - (θ + Y') = y' + ta' • F'.fl.z - Y' := by abel
    rw [e]; exact h2
  · have e : θ + Y - (θ + Y') = Y - Y' := by abel
    rw [e]
    exact d_lp_mono P (le_trans le_sup_left le_sup_left) hu

theorem d_int_BLat {g : ℕ} (hgen : IsGeneric Λ g F F') (P : HeightOneSpectrum (𝓞 E)) {Y : S.V}
    (hM : (g : 𝓞 E) ∈ P.asIdeal → ∀ ξ, AdmWit Λ g F F' ξ →
      ∀ m ∈ Mplus Λ g F F' ξ, d_PInt P (S.hT m Y))
    (hUU : (g : 𝓞 E) ∉ P.asIdeal → ∀ m ∈ UU Λ F F', d_PInt P (S.hT m Y)) :
    ∀ m ∈ BLat Λ F F', d_PInt P (S.hT m Y) := by
  intro m hm
  obtain ⟨ξ, hξ, hloc⟩ := hgen
  have hmB : m ∈ d_lp (d_bar P) (BLat Λ F F') := d_le_lp _ _ hm
  by_cases hgP : (g : 𝓞 E) ∈ P.asIdeal
  · have e := (hloc (d_bar P)).1 ((d_nat_mem_bar P g).2 hgP)
    change m ∈ Formalism.HermitianLatticesTheory.localization₂ (d_bar P).asIdeal _ at hmB
    rw [e] at hmB
    obtain ⟨s, hs, hsm⟩ := hmB
    have := hM hgP ξ hξ _ hsm
    rw [d_hT_osmul] at this
    exact d_PInt_cancel hs this
  · have e := (hloc (d_bar P)).2 (fun h => hgP ((d_nat_mem_bar P g).1 h))
    change m ∈ Formalism.HermitianLatticesTheory.localization₂ (d_bar P).asIdeal _ at hmB
    rw [e] at hmB
    obtain ⟨s, hs, hsm⟩ := hmB
    have := hUU hgP _ hsm
    rw [d_hT_osmul] at this
    exact d_PInt_cancel hs this

end Glue

section Step1

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'} {Λ : Submodule (𝓞 E) S.V}

theorem d_Lam_int (hun : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {a b : S.V} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    ∃ c : 𝓞 E, (c : E) = S.hT a b := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at hun
  have : b ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hun]; exact hb
  exact d_mem_dual.1 this a ha

theorem d_pair_int (hun : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (P : HeightOneSpectrum (𝓞 E)) {g : ℕ}
    (hg : g ≠ 0) {m u : S.V} (hm : m ∈ d_lp (d_bar P) Λ)
    (hu : u ∈ d_lp P (Ideal.span {(g : 𝓞 E)} • Λ)) : d_PInt P (S.hT m u / g) := by
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  obtain ⟨s, hs, hsm⟩ := d_mem_lp.1 hm
  obtain ⟨t, ht, htu⟩ := d_mem_lp.1 hu
  rw [Submodule.ideal_span_singleton_smul] at htu
  obtain ⟨l₀, hl₀, e⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 htu
  obtain ⟨c, hc⟩ := d_Lam_int hun hsm hl₀
  have key : ((d_sO E s : 𝓞 E) : E) * ((t : E) * S.hT m u) = (g : E) * c := by
    rw [← d_hT_osmul_right, ← d_hT_osmul, ← e, d_hT_osmul_right, hc]
    push_cast
    rfl
  refine ⟨d_sO E s * t, d_mul_notMem hs ht, c, ?_⟩
  push_cast
  field_simp
  linear_combination key

theorem d_frame_mem {T : E} (F : LFlag S r T) (a : Fin (r + 1)) : frame F a ∈ Xplus F := by
  rw [← a_span_frame]
  exact Submodule.subset_span ⟨a, rfl⟩

theorem d_frameAct_mem {T : E} (F : LFlag S r T) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (b : Fin (r + 1)) : frameAct (frame F) ξ b ∈ Xplus F :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (d_frame_mem F a)

theorem d_frame_lp {g : ℕ} (hFix : IsFixedConv Λ g F) (hzΛ : F.fl.z ∈ Λ)
    (Q : HeightOneSpectrum (𝓞 E)) (hgQ : (g : 𝓞 E) ∈ Q.asIdeal) (a : Fin (r + 1)) :
    frame F a ∈ d_lp Q Λ := by
  refine Fin.lastCases ?_ (fun i => ?_) a
  · rw [a_frame_last]
    exact d_le_lp Q Λ hzΛ
  · rw [a_frame_castSucc]
    obtain ⟨c, -, hc1, hc⟩ := hFix.1 Q
    have h1 : F.fl.e i ∈ d_lp Q (Submodule.span (𝓞 E) (Set.range fun a => c a • F.fl.e a)) :=
      d_le_lp Q _ (Submodule.subset_span ⟨i, by simp [hc1 hgQ i]⟩)
    change F.fl.e i ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal _ at h1
    rw [← hc] at h1
    exact d_lp_mono Q inf_le_left h1

theorem d_frame'_lp {g : ℕ} (hFix : IsFixedConv Λ g F) (hzΛ : F.fl.z ∈ Λ)
    {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)} (hξ : AdmWit Λ g F F' ξ)
    (Q : HeightOneSpectrum (𝓞 E)) (hgQ : (g : 𝓞 E) ∈ Q.asIdeal) (b : Fin (r + 1)) :
    frame F' b ∈ d_lp Q Λ := by
  have e : frame F' b = (frame F' b - frameAct (frame F) ξ b) + frameAct (frame F) ξ b := by abel
  rw [e]
  refine add_mem (d_lp_mono Q Submodule.smul_le_right (hξ.2.2 b Q hgQ)) ?_
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [← d_osmul]
  exact Submodule.smul_mem _ _ (d_frame_lp hFix hzΛ Q hgQ a)

theorem d_int_prime (hun : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (P : HeightOneSpectrum (𝓞 E)) {g : ℕ}
    (hg : g ≠ 0) {Y Y' m : S.V} (hY' : Y' ∈ orth S (Xplus F'))
    (hu : Y - Y' ∈ d_lp P (Ideal.span {(g : 𝓞 E)} • Λ)) (hm : m ∈ Xplus F')
    (hmΛ : m ∈ d_lp (d_bar P) Λ) : d_PInt P (S.hT m Y / g) := by
  have e : S.hT m Y = S.hT m (Y - Y') := by
    rw [map_sub, (a_mem_orth _ _).1 hY' m hm, sub_zero]
  rw [e]
  exact d_pair_int hun P hg hmΛ hu

theorem d_PInt_of_div {P : HeightOneSpectrum (𝓞 E)} {g : ℕ} (hg : g ≠ 0) {x : E}
    (h : d_PInt P (x / g)) : d_PInt P x := by
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have := d_PInt_mul (d_PInt_int P (g : 𝓞 E)) h
  have e : (((g : 𝓞 E) : 𝓞 E) : E) * (x / g) = x := by
    push_cast
    field_simp
  rwa [e] at this

theorem d_int_Mplus (hun : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hz : F.zt = F.fl.z) {g : ℕ} (hg : g ≠ 0)
    (hFix : IsFixedConv Λ g F) (hzΛ : F.fl.z ∈ Λ) (P : HeightOneSpectrum (𝓞 E))
    (hgP : (g : 𝓞 E) ∈ P.asIdeal) {Y Y' : S.V} (hY : Y ∈ orth S (Xplus F))
    (hY' : Y' ∈ orth S (Xplus F')) (hu : Y - Y' ∈ d_lp P (Ideal.span {(g : 𝓞 E)} • Λ))
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (hξ : AdmWit Λ g F F' ξ) :
    ∀ m ∈ Mplus Λ g F F' ξ, d_PInt P (S.hT m Y) := by
  refine d_PInt_span P Y _ ?_
  rintro m ((hm | hm) | hm)
  · rw [(a_mem_orth _ _).1 hY m (Submodule.mem_sup_left hm.2)]
    exact d_PInt_zero P
  · rw [Set.mem_singleton_iff] at hm
    rw [hm, hz, (a_mem_orth _ _).1 hY _
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))]
    exact d_PInt_zero P
  · obtain ⟨b, rfl⟩ := hm
    have e : S.hT (((g : E)⁻¹) • (frame F' b - frameAct (frame F) ξ b)) Y =
        S.hT (frame F' b) Y / g := by
      rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_sub, LinearMap.sub_apply,
        (a_mem_orth _ _).1 hY _ (d_frameAct_mem F ξ b), sub_zero, starRingEnd_apply, star_inv₀,
        star_natCast]
      ring
    rw [e]
    exact d_int_prime hun P hg hY' hu (d_frame_mem F' b)
      (d_frame'_lp hFix hzΛ hξ (d_bar P) ((d_nat_mem_bar P g).2 hgP) b)

theorem d_int_UU (P : HeightOneSpectrum (𝓞 E)) {Y : S.V}
    (h1 : ∀ m ∈ XLam Λ F, d_PInt P (S.hT m Y)) (h2 : d_PInt P (S.hT F.zt Y))
    (h3 : ∀ m ∈ XLam Λ F', d_PInt P (S.hT m Y)) (h4 : d_PInt P (S.hT F'.zt Y)) :
    ∀ m ∈ UU Λ F F', d_PInt P (S.hT m Y) := by
  intro m hm
  unfold UU at hm
  obtain ⟨m1, hm1, w', hw', rfl⟩ := Submodule.mem_sup.1 hm
  obtain ⟨m2, hm2, x', hx', rfl⟩ := Submodule.mem_sup.1 hm1
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.1 hm2
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hw'
  simp only [map_add, LinearMap.add_apply, d_hT_osmul]
  exact d_PInt_add (d_PInt_add (d_PInt_add (h1 x hx) (d_PInt_mul (d_PInt_int P _) h2)) (h3 x' hx'))
    (d_PInt_mul (d_PInt_int P _) h4)

end Step1

section Step1b

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {T T' : E}

structure d_TermHyp (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') :
    Prop where
  lat : Submodule.IsLattice E Λ
  unim : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ
  glue : d_Glue Λ
  g0 : g ≠ 0
  zt : F.zt = F.fl.z
  zΛ : F.fl.z ∈ Λ
  fix : IsFixedConv Λ g F
  zt' : F'.zt = F'.fl.z
  zΛ' : F'.fl.z ∈ Λ
  G : Gval F F' ≠ 0
  gen : IsGeneric Λ g F F'

variable {F : LFlag S r T} {F' : LFlag S r T'} {Λ : Submodule (𝓞 E) S.V} {g : ℕ}

theorem d_TermHyp.hU (H : d_TermHyp Λ g F F') : HU Λ F F' := a_HU Λ H.lat F F' H.zt H.zt'

theorem d_TermHyp.hNd (H : d_TermHyp Λ g F F') : UUE Λ F F' ⊓ orth S (UUE Λ F F') = ⊥ := by
  rw [show UUE Λ F F' = U2 F F' from H.hU]
  exact a_HNd F F' H.G

theorem local_lift_at_prime (H : d_TermHyp Λ g F F') (P : HeightOneSpectrum (𝓞 E)) {al al' : E}
    (hZ : (al, al') ∈ (Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZ g : Set (E × E))) :
    ∃ u₀ ∈ d_lp P (Ideal.span {(g : 𝓞 E)} • Λ), d_Comp F F' u₀ al al' := by
  obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩, w, hw⟩ := hZ
  simp only at hc hc' hw
  by_cases hgP : (g : 𝓞 E) ∈ P.asIdeal
  · obtain ⟨ξ, hξ, -⟩ := H.gen
    refine ⟨(al + al') • F.fl.z +
      al' • (frame F' (Fin.last r) - frameAct (frame F) ξ (Fin.last r)), add_mem ?_ ?_, ?_⟩
    · apply d_le_lp
      have e : (al + al') • F.fl.z = (g : 𝓞 E) • (w • F.fl.z) := by
        rw [hw, d_osmul, d_osmul, smul_smul]
        push_cast
        rfl
      rw [e]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (Λ.smul_mem w H.zΛ)
    · rw [← hc', ← d_osmul]
      exact Submodule.smul_mem _ _ (hξ.2.2 (Fin.last r) P hgP)
    · have h1 := d_comp_add (d_comp_smul (al + al') (d_comp_alt (F := F) (F' := F')))
        (d_comp_smul al' (d_comp_sub (d_comp_frame' (F := F) (F' := F') (Fin.last r))
          (d_comp_frameAct (F := F) (F' := F') ξ (Fin.last r))))
      rw [hξ.2.1, if_pos rfl] at h1
      convert h1 using 1
      · push_cast; ring
      · ring
  · refine ⟨al • F.fl.z + al' • F'.fl.z, d_mem_lp.2 ⟨(g : 𝓞 E), hgP, ?_⟩, ?_⟩
    · refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (add_mem ?_ ?_)
      · rw [← hc, ← d_osmul]; exact Λ.smul_mem c H.zΛ
      · rw [← hc', ← d_osmul]; exact Λ.smul_mem c' H.zΛ'
    · have h1 := d_comp_add (d_comp_smul al (d_comp_alt (F := F) (F' := F')))
        (d_comp_smul al' (d_comp_alt_alt (F := F) (F' := F')))
      simpa using h1

theorem d_sg_comp (H : d_TermHyp Λ g F F') {y y' : S.V} {al al' : E} :
    SgRel F F' y y' al al' ↔ d_Comp F F' (y - y') al al' := by
  unfold SgRel d_Comp
  rw [H.zt, H.zt']

theorem d_step1_NN (H : d_TermHyp Λ g F F') (P : HeightOneSpectrum (𝓞 E)) {al al' : E}
    (hZ : (al, al') ∈ (Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZ g : Set (E × E))) {y y' : S.V}
    (hy : y ∈ Ylift Λ F F') (hy' : y' ∈ Ylift' Λ F F') (h : SgRel F F' y y' al al') :
    d_NN Λ g F F' P 0 0 y y' := by
  obtain ⟨u₀, hu₀, w, hw, w', hw', e0⟩ := local_lift_at_prime H P hZ
  obtain ⟨x, hx, x', hx', e⟩ := (d_sg_comp H).1 h
  have hXU := a_X_le H.hU
  have hYY : (y - x + w) - (y' + x' - w') = u₀ := by
    have e1 : (y - x + w) - (y' + x' - w') = (y - y') - x - x' + w + w' := by abel
    rw [e1, e, e0]
    abel
  have hYo : y - x + w ∈ orth S (Xplus F) :=
    add_mem (sub_mem hy.2 (a_X_le_orth_Xplus F hx)) (a_X_le_orth_Xplus F hw)
  have hYo' : y' + x' - w' ∈ orth S (Xplus F') :=
    sub_mem (add_mem hy'.2 (a_X_le_orth_Xplus F' hx')) (a_X_le_orth_Xplus F' hw')
  have hu : (y - x + w) - (y' + x' - w') ∈ d_lp P (Ideal.span {(g : 𝓞 E)} • Λ) := by
    rw [hYY]; exact hu₀
  refine d_NN_of_int H.lat H.glue H.hNd P (Y := y - x + w) (Y' := y' + x' - w')
    (add_mem (sub_mem hy.1 (hXU.1 hx)) (hXU.1 hw)) ?_ hu ?_ ?_
  · refine d_int_BLat H.gen P ?_ ?_
    · intro hgP ξ hξ
      exact d_int_Mplus H.unim H.zt H.g0 H.fix H.zΛ P hgP hYo hYo' hu ξ hξ
    · intro _
      refine d_int_UU P ?_ ?_ ?_ ?_
      · intro m hm
        rw [(a_mem_orth _ _).1 hYo m (Submodule.mem_sup_left hm.2)]
        exact d_PInt_zero P
      · rw [H.zt, (a_mem_orth _ _).1 hYo _
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))]
        exact d_PInt_zero P
      · intro m hm
        exact d_PInt_of_div H.g0 (d_int_prime H.unim P H.g0 hYo' hu (Submodule.mem_sup_left hm.2)
          (d_le_lp _ _ hm.1))
      · rw [H.zt']
        exact d_PInt_of_div H.g0 (d_int_prime H.unim P H.g0 hYo' hu
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) (d_le_lp _ _ H.zΛ'))
  · have e1 : y + (0 : E) • F.fl.z - (y - x + w) = x - w := by rw [zero_smul]; abel
    rw [e1]; exact sub_mem hx hw
  · have e1 : y' + (0 : E) • F'.fl.z - (y' + x' - w') = w' - x' := by rw [zero_smul]; abel
    rw [e1]; exact sub_mem hw' hx'

variable {F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem d_step1 (H' : d_TermHyp Λ g F F') (H'' : d_TermHyp Λ g F F'')
    (hp : IsPair Λ F F' F'' β g) (hA3' : Hp Λ F F' = Th Λ F F' F'' β)
    (hA3'' : Hp Λ F F'' = Th'' Λ F F' F'' β) {a b c d : E}
    (G1 : ∀ y1 ∈ Ylift Λ F F', ∀ y2 ∈ Ylift Λ F F'', ∀ y1' ∈ Ylift' Λ F F',
      ∀ y2'' ∈ Ylift' Λ F F'', y1 - y2 ∈ Xsp F → y2'' - β y1' ∈ Xsp F'' →
      ∀ al al' : E, SgRel F F' y1 y1' al al' →
        SgRel F F'' y2 y2'' (a * al + b * al') (c * al + d * al')) :
    ∀ p ∈ (Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZ g : Set (E × E)),
      (a * p.1 + b * p.2, c * p.1 + d * p.2) ∈ (Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZ g : Set (E × E)) := by
  rintro ⟨al, al'⟩ hZ
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 H'.g0
  obtain ⟨y, hy, y', hy', h⟩ := lemma_two_exists_lifts Λ H'.lat F F' H'.zt H'.zt' H'.G al al'
  have hc'' : IsCompl (UUE Λ F F'') (Hp Λ F F'') := by
    unfold Hp
    rw [show UUE Λ F F'' = U2 F F'' from H''.hU]
    exact double_span_is_compl_orth F F'' H''.G
  have hN := d_normals_gen hp hc'' hA3''
  have h'' := G1 y hy y (hN.1 y hy) y' hy' (β y') (hN.2 y' hy') (by simp) (by simp) al al' h
  have hloc : ∀ P : HeightOneSpectrum (𝓞 E), _ := fun P =>
    d_NN_int H''.zt H''.zt' (a_HInd F F'' H''.G) H''.hU H''.g0 H''.gen P
      (d_NN_transfer hp H'.hU hA3' P hy.2 hy'.2 (d_step1_NN H' P hZ hy hy' h))
      ((d_sg_comp H'').1 h'')
  simp only [add_zero, sub_zero] at hloc
  obtain ⟨c1, hc1⟩ := d_int_of_local _ (fun P => (hloc P).1)
  obtain ⟨c2, hc2⟩ := d_int_of_local _ (fun P => (hloc P).2.1)
  obtain ⟨c3, hc3⟩ := d_int_of_local _ (fun P => (hloc P).2.2)
  refine ⟨⟨c1, hc1⟩, ⟨c2, hc2⟩, c3, ?_⟩
  rw [hc3]
  field_simp

end Step1b

section Step2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {Tn Tn' : ℕ} {F : LFlag S r (Tn : E)} {F' F'' : LFlag S r (Tn' : E)}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {β : S.V ≃ₗ[E] S.V}

theorem d_step2_NN (H : d_TermHyp Λ g F F') (P : HeightOneSpectrum (𝓞 E))
    (hgP : (g : 𝓞 E) ∉ P.asIdeal) {al al' : E} (hal : d_PInt P ((Tn : E) * al))
    (hal' : d_PInt P ((Tn' : E) * al')) {y y' : S.V}
    (hy : y ∈ Ylift Λ F F') (hy' : y' ∈ Ylift' Λ F F') (h : SgRel F F' y y' al al') :
    d_NN Λ g F F' P (-al) al' y y' := by
  obtain ⟨x, hx, x', hx', e⟩ := (d_sg_comp H).1 h
  have hXU := a_X_le H.hU
  have hzU : F.fl.z ∈ UUE Λ F F' := by
    rw [show UUE Λ F F' = U2 F F' from H.hU]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hYY : y - al • F.fl.z - x = y' + al' • F'.fl.z + x' := by
    have e1 : y - al • F.fl.z - x = (y - y') + y' - al • F.fl.z - x := by abel
    rw [e1, e]
    abel
  have hYX : y - al • F.fl.z - x ∈ orth S (Xsp F) :=
    sub_mem (sub_mem (d_orth_anti le_sup_left hy.2) (Submodule.smul_mem _ _ (d_z_orthX F)))
      (d_X_orthX F hx)
  have hYX' : y' + al' • F'.fl.z + x' ∈ orth S (Xsp F') :=
    add_mem (add_mem (d_orth_anti le_sup_left hy'.2) (Submodule.smul_mem _ _ (d_z_orthX F')))
      (d_X_orthX F' hx')
  have hz1 : S.hT F.fl.z (y - al • F.fl.z - x) = (Tn : E) * al := by
    rw [map_sub, map_sub, map_smul, F.fl.z_norm, LinearMap.mem_ker.1 (a_z_X F hx),
      (a_mem_orth _ _).1 hy.2 _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)),
      smul_eq_mul]
    ring
  have hz2 : S.hT F'.fl.z (y' + al' • F'.fl.z + x') = -((Tn' : E) * al') := by
    rw [map_add, map_add, map_smul, F'.fl.z_norm, LinearMap.mem_ker.1 (a_z_X F' hx'),
      (a_mem_orth _ _).1 hy'.2 _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)),
      smul_eq_mul]
    ring
  refine d_NN_of_int H.lat H.glue H.hNd P (Y := y - al • F.fl.z - x) (Y' := y - al • F.fl.z - x)
    (sub_mem (sub_mem hy.1 (Submodule.smul_mem _ _ hzU)) (hXU.1 hx)) ?_ (by simp) ?_ ?_
  · refine d_int_BLat H.gen P (fun h => absurd h hgP) (fun _ => d_int_UU P ?_ ?_ ?_ ?_)
    · intro m hm
      rw [(a_mem_orth _ _).1 hYX m hm.2]
      exact d_PInt_zero P
    · rw [H.zt, hz1]
      exact hal
    · intro m hm
      rw [hYY, (a_mem_orth _ _).1 hYX' m hm.2]
      exact d_PInt_zero P
    · rw [H.zt', hYY, hz2]
      exact d_PInt_neg hal'
  · have e1 : y + (-al) • F.fl.z - (y - al • F.fl.z - x) = x := by rw [neg_smul]; abel
    rw [e1]; exact hx
  · rw [hYY]
    have e1 : y' + al' • F'.fl.z - (y' + al' • F'.fl.z + x') = -x' := by abel
    rw [e1]; exact neg_mem hx'

theorem d_step2 (H' : d_TermHyp Λ g F F') (H'' : d_TermHyp Λ g F F'')
    (hp : IsPair Λ F F' F'' β g) (hA3' : Hp Λ F F' = Th Λ F F' F'' β)
    (hA3'' : Hp Λ F F'' = Th'' Λ F F' F'' β) {a b c d : E}
    (G1 : ∀ y1 ∈ Ylift Λ F F', ∀ y2 ∈ Ylift Λ F F'', ∀ y1' ∈ Ylift' Λ F F',
      ∀ y2'' ∈ Ylift' Λ F F'', y1 - y2 ∈ Xsp F → y2'' - β y1' ∈ Xsp F'' →
      ∀ al al' : E, SgRel F F' y1 y1' al al' →
        SgRel F F'' y2 y2'' (a * al + b * al') (c * al + d * al'))
    (P : HeightOneSpectrum (𝓞 E)) (hgP : (g : 𝓞 E) ∉ P.asIdeal) (al al' : E)
    (hal : d_PInt P ((Tn : E) * al)) (hal' : d_PInt P ((Tn' : E) * al')) :
    d_PInt P ((a - 1) * al + b * al') ∧ d_PInt P (c * al + (d - 1) * al') := by
  obtain ⟨y, hy, y', hy', h⟩ := lemma_two_exists_lifts Λ H'.lat F F' H'.zt H'.zt' H'.G al al'
  have hc'' : IsCompl (UUE Λ F F'') (Hp Λ F F'') := by
    unfold Hp
    rw [show UUE Λ F F'' = U2 F F'' from H''.hU]
    exact double_span_is_compl_orth F F'' H''.G
  have hN := d_normals_gen hp hc'' hA3''
  have h'' := G1 y hy y (hN.1 y hy) y' hy' (β y') (hN.2 y' hy') (by simp) (by simp) al al' h
  have hloc := d_NN_int H''.zt H''.zt' (a_HInd F F'' H''.G) H''.hU H''.g0 H''.gen P
    (d_NN_transfer hp H'.hU hA3' P hy.2 hy'.2 (d_step2_NN H' P hgP hal hal' hy hy' h))
    ((d_sg_comp H'').1 h'')
  refine ⟨?_, ?_⟩
  · have e : (a - 1) * al + b * al' = a * al + b * al' + -al := by ring
    rw [e]; exact hloc.1
  · have e : c * al + (d - 1) * al' = c * al + d * al' - al' := by ring
    rw [e]; exact hloc.2.1

theorem d_locIn_one {P : HeightOneSpectrum (𝓞 E)} {x : E} :
    Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P.asIdeal x 1 ↔ d_PInt P x := by
  unfold Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn d_PInt
  constructor
  · rintro ⟨y, z, hy, h⟩
    exact ⟨y, hy, z, by rw [h]; simp⟩
  · rintro ⟨y, hy, z, h⟩
    exact ⟨y, z, hy, by rw [h]; simp⟩

theorem d_step2_congr (H' : d_TermHyp Λ g F F') (H'' : d_TermHyp Λ g F F'')
    (hp : IsPair Λ F F' F'' β g) (hA3' : Hp Λ F F' = Th Λ F F' F'' β)
    (hA3'' : Hp Λ F F'' = Th'' Λ F F' F'' β) {a b c d : E}
    (G1 : ∀ y1 ∈ Ylift Λ F F', ∀ y2 ∈ Ylift Λ F F'', ∀ y1' ∈ Ylift' Λ F F',
      ∀ y2'' ∈ Ylift' Λ F F'', y1 - y2 ∈ Xsp F → y2'' - β y1' ∈ Xsp F'' →
      ∀ al al' : E, SgRel F F' y1 y1' al al' →
        SgRel F F'' y2 y2'' (a * al + b * al') (c * al + d * al'))
    (hT : 0 < Tn) (hT' : 0 < Tn') (hcop : Nat.Coprime g (Tn * Tn'))
    (P : Ideal (𝓞 E)) (hP : P.IsPrime) (hTP : (Tn : 𝓞 E) ∈ P ∨ (Tn' : 𝓞 E) ∈ P) :
    Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P (a - 1) Tn ∧ Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P c Tn ∧ Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P b Tn' ∧
      Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocIn P (d - 1) Tn' := by
  have hTT : ((Tn * Tn' : ℕ) : 𝓞 E) ∈ P := by
    push_cast
    rcases hTP with h | h
    · exact P.mul_mem_right _ h
    · exact P.mul_mem_left _ h
  have hP0 : P ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hTT
    exact (Nat.mul_pos hT hT').ne' (Nat.cast_eq_zero.1 hTT)
  have hgP : (g : 𝓞 E) ∉ P := by
    intro hg
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : ((u : ℤ) : 𝓞 E) * (g : 𝓞 E) + ((v : ℤ) : 𝓞 E) * ((Tn * Tn' : ℕ) : 𝓞 E) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huv
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one, ← h1]
    exact P.add_mem (P.mul_mem_left _ hg) (P.mul_mem_left _ hTT)
  let Q : HeightOneSpectrum (𝓞 E) := ⟨P, hP, hP0⟩
  refine Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.localCongr E P Tn Tn' a b c d hP hT hT' ?_
  intro u v hu hv
  have := d_step2 H' H'' hp hA3' hA3'' G1 Q hgP u v ((d_locIn_one (P := Q)).1 hu)
    ((d_locIn_one (P := Q)).1 hv)
  exact ⟨(d_locIn_one (P := Q)).2 this.1, (d_locIn_one (P := Q)).2 this.2⟩

end Step2

section FinalB

theorem d_termHyp {D : D7} (hGl : Formalism.MainNotions.S.UnitaryVolumeMass.stGlue D) {Λ : Formalism.MainNotions.S.UnitaryVolumeMass.Lt D} {T T' : ℕ}
    {F : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T} {F' : Formalism.MainNotions.S.UnitaryVolumeMass.Fl D T'} (hF : FixedHyp D Λ F)
    (hT' : IsTerm Λ (gS D) F F') (hG' : IsGeneric Λ (gS D) F F') : d_TermHyp Λ (gS D) F F' where
  lat := hF.1
  unim := hF.2.1
  glue := fun U hU => (hGl Λ hF.1 hF.2.1 U hU).1
  g0 := Nat.one_le_iff_ne_zero.1 (d_gS_pos D)
  zt := hF.2.2.1.2
  zΛ := hF.2.2.1.1
  fix := hF.2.2.2
  zt' := hT'.1.2
  zΛ' := hT'.1.1
  G := hT'.2.2
  gen := hG'

theorem theorem_B_first_two_steps (D : D7) (hGl : Formalism.MainNotions.S.UnitaryVolumeMass.stGlue D) (hA3 : Formalism.MainNotions.S.UnitaryVolumeMass.DefiniteRankOneAllWords D) :
    TheoremBFirstTwoSteps D := by
  intro u T' Λ F F' F'' β hF hPr hT' hT'' hp hs hG' hG'' a b c d G1
  have H' := d_termHyp hGl hF hT' hG'
  have H'' := d_termHyp hGl hF hT'' hG''
  have h3 := hA3 u T' Λ F F' F'' β hF hPr hT' hT'' hp hs
  refine ⟨d_step1 H' H'' hp h3.1 h3.2 G1, ?_⟩
  intro P hP hTP
  exact d_step2_congr H' H'' hp h3.1 h3.2 G1 (by have := hPr.2.1; omega)
    (by have := hPr.2.2.2.1; omega) hPr.2.2.2.2.2.2.2.1 P hP hTP

end FinalB

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module IsDedekindDomain

section Den

variable {E : Type} [Field E] [NumberField E]

theorem e_den {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (g : ℕ) (hg : 0 < g)
    (M : Submodule (𝓞 E) W) (x : W)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), ((g : 𝓞 E) ∈ P.asIdeal) →
      x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M)) :
    ∃ s : 𝓞 E, s - 1 ∈ Ideal.span {(g : 𝓞 E)} ∧ s • x ∈ M := by
  let I : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hI : ∀ s, s ∈ I ↔ s • x ∈ M := fun s => by
    simp [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  have htop : I ⊔ Ideal.span {(g : 𝓞 E)} = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have hgP : (g : 𝓞 E) ∈ P := hle (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hg0 : (g : 𝓞 E) ≠ 0 := by exact_mod_cast hg.ne'
    have hPne : P ≠ ⊥ := by
      intro hb
      rw [hb] at hgP
      exact hg0 (by simpa using hgP)
    obtain ⟨s, hs, hsx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.1 (h ⟨P, hP.isPrime, hPne⟩ hgP)
    exact hs (hle (Submodule.mem_sup_left ((hI s).2 hsx)))
  have h1 : (1 : 𝓞 E) ∈ I ⊔ Ideal.span {(g : 𝓞 E)} := by rw [htop]; trivial
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1
  refine ⟨s, ?_, (hI s).1 hs⟩
  have : s - 1 = -t := by rw [← hst]; ring
  rw [this]
  exact neg_mem ht

theorem e_den_fin {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (g : ℕ) (hg : 0 < g) {ι : Type*}
    [Fintype ι] (M : ι → Submodule (𝓞 E) W) (x : ι → W)
    (h : ∀ i, ∀ P : HeightOneSpectrum (𝓞 E), ((g : 𝓞 E) ∈ P.asIdeal) →
      x i ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (M i))) :
    ∃ s : 𝓞 E, s - 1 ∈ Ideal.span {(g : 𝓞 E)} ∧ ∀ i, s • x i ∈ M i := by
  choose s hs1 hs2 using fun i => e_den g hg (M i) (x i) (h i)
  refine ⟨∏ i, s i, ?_, fun i => ?_⟩
  · rw [← Ideal.Quotient.eq, map_prod, map_one]
    apply Finset.prod_eq_one
    intro i _
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(g : 𝓞 E)})), Ideal.Quotient.eq]
    exact hs1 i
  · obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ i)
    rw [ht, mul_comm, mul_smul]
    exact (M i).smul_mem _ (hs2 i)

theorem e_mem_span (g : ℕ) (hg : 0 < g) (d : 𝓞 E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), ((g : 𝓞 E) ∈ P.asIdeal) →
      ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ t * d ∈ Ideal.span {(g : 𝓞 E)}) :
    d ∈ Ideal.span {(g : 𝓞 E)} := by
  obtain ⟨s, hs1, hs2⟩ := e_den (W := 𝓞 E) g hg (Ideal.span {(g : 𝓞 E)}) d (fun P hP => by
    obtain ⟨t, ht, htd⟩ := h P hP
    exact Formalism.HermitianLatticesTheory.locBasic_mem_locS.2 ⟨t, ht, htd⟩)
  have : d = s • d - (s - 1) * d := by rw [smul_eq_mul]; ring
  rw [this]
  exact sub_mem hs2 (Ideal.mul_mem_right _ _ hs1)

theorem e_card_pi (g : ℕ) (n : ℕ) :
    (Nat.card ((Fin n → 𝓞 E) ⧸
      Submodule.pi Set.univ (fun _ : Fin n => (Ideal.span {(g : 𝓞 E)} : Submodule (𝓞 E) (𝓞 E)))) : ℝ) =
      NE (E := E) g ^ n := by
  rw [Nat.card_congr (Submodule.quotientPi
    (fun _ : Fin n => (Ideal.span {(g : 𝓞 E)} : Submodule (𝓞 E) (𝓞 E)))).toEquiv, Nat.card_fun]
  have h1 : Nat.card (𝓞 E ⧸ (Ideal.span {(g : 𝓞 E)} : Submodule (𝓞 E) (𝓞 E))) =
      g ^ finrank ℚ E := by
    have := Ideal.absNorm_span_singleton (g : 𝓞 E)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    rw [this]
    have h2 : (g : 𝓞 E) = algebraMap ℤ (𝓞 E) (g : ℤ) := by simp
    rw [h2, Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]
  rw [h1]
  simp [NE]

end Den

section Main

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {Λ : Submodule (𝓞 E) S.V} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'} {g : ℕ}

def frameDifference (F : LFlag S r T) (F' : LFlag S r T') (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (b : Fin (r + 1)) : S.V := frame F' b - frameAct (frame F) ξ b

theorem e_frameAct {n : ℕ} (f : Fin n → S.V) (ξ : Matrix (Fin n) (Fin n) (𝓞 E)) (b : Fin n) :
    frameAct f ξ b = ∑ a, ξ a b • f a :=
  Finset.sum_congr rfl fun a _ => IsScalarTower.algebraMap_smul E (ξ a b) (f a)

theorem e_frame_loc (hz : IsLift Λ F) (hc : IsFixedConv Λ g F) (P : HeightOneSpectrum (𝓞 E))
    (hP : (g : 𝓞 E) ∈ P.asIdeal) (a : Fin (r + 1)) :
    frame F a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  induction a using Fin.lastCases with
  | last =>
    rw [a_frame_last]
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hz.1
  | cast i =>
    rw [a_frame_castSucc]
    obtain ⟨c, -, hc1, heq⟩ := hc.1 P
    have h1 : F.fl.e i ∈ Submodule.span (𝓞 E) (Set.range fun a => c a • F.fl.e a) :=
      Submodule.subset_span ⟨i, by simp [hc1 hP i]⟩
    have h2 : F.fl.e i ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F)) := by
      rw [heq]
      exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ h1
    exact Formalism.HermitianLatticesTheory.locBasic_locS_mono _ inf_le_left h2

theorem exists_congruent_unit_scalar (hg : 0 < g) (hz : IsLift Λ F) (hc : IsFixedConv Λ g F)
    {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)} (hξ : AdmWit Λ g F F' ξ) :
    ∃ s : 𝓞 E, s - 1 ∈ Ideal.span {(g : 𝓞 E)} ∧
      (∀ b, s • frameDifference F F' ξ b ∈ Ideal.span {(g : 𝓞 E)} • Λ) ∧ (∀ a, s • frame F a ∈ Λ) ∧
      (∀ b, s • frame F' b ∈ Λ) := by
  obtain ⟨s, hs1, hs2⟩ := e_den_fin (W := S.V) g hg
    (ι := Fin (r + 1) ⊕ (Fin (r + 1) ⊕ Fin (r + 1)))
    (Sum.elim (fun _ => Ideal.span {(g : 𝓞 E)} • Λ) (fun _ => Λ))
    (Sum.elim (frameDifference F F' ξ) (Sum.elim (frame F) (frame F'))) (by
      rintro (b | a | b) P hP
      · exact hξ.2.2 b P hP
      · exact e_frame_loc hz hc P hP a
      · have h1 : frameDifference F F' ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) :=
          Formalism.HermitianLatticesTheory.locBasic_locS_mono _ Submodule.smul_le_right (hξ.2.2 b P hP)
        have h2 : frameAct (frame F) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
          rw [e_frameAct]
          exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (e_frame_loc hz hc P hP a)
        have h3 : frame F' b = frameDifference F F' ξ b + frameAct (frame F) ξ b := by
          unfold frameDifference; abel
        show frame F' b ∈ _
        rw [h3]
        exact add_mem h1 h2)
  exact ⟨s, hs1, fun b => hs2 (Sum.inl b), fun a => hs2 (Sum.inr (Sum.inl a)),
    fun b => hs2 (Sum.inr (Sum.inr b))⟩

theorem e_s_frame_UU (hz : IsLift Λ F) {s : 𝓞 E} (h : ∀ a, s • frame F a ∈ Λ) (a : Fin (r + 1)) :
    s • frame F a ∈ UU Λ F F' := by
  have ha := h a
  unfold UU
  induction a using Fin.lastCases with
  | last =>
    rw [a_frame_last, ← hz.2]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))))
  | cast i =>
    rw [a_frame_castSucc] at ha ⊢
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
      ⟨ha, (toO S (Xsp F)).smul_mem s (Submodule.subset_span ⟨i, rfl⟩)⟩))

theorem e_s_frame_UU' (hz' : IsLift Λ F') {s : 𝓞 E} (h : ∀ a, s • frame F' a ∈ Λ) (a : Fin (r + 1)) :
    s • frame F' a ∈ UU Λ F F' := by
  have ha := h a
  unfold UU
  induction a using Fin.lastCases with
  | last =>
    rw [a_frame_last, ← hz'.2]
    exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  | cast i =>
    rw [a_frame_castSucc] at ha ⊢
    exact Submodule.mem_sup_left (Submodule.mem_sup_right
      ⟨ha, (toO S (Xsp F')).smul_mem s (Submodule.subset_span ⟨i, rfl⟩)⟩)

theorem e_s_x_UU (hz : IsLift Λ F) (hz' : IsLift Λ F') {s : 𝓞 E} (h : ∀ a, s • frame F a ∈ Λ)
    (h' : ∀ a, s • frame F' a ∈ Λ) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (b : Fin (r + 1)) :
    s • frameDifference F F' ξ b ∈ UU Λ F F' := by
  unfold frameDifference
  rw [smul_sub, e_frameAct, Finset.smul_sum]
  refine sub_mem (e_s_frame_UU' hz' h' b) (Submodule.sum_mem _ fun a _ => ?_)
  rw [smul_comm]
  exact Submodule.smul_mem _ _ (e_s_frame_UU hz h a)

theorem frame_difference_mem_double_span (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (b : Fin (r + 1)) :
    frameDifference F F' ξ b ∈ U2 F F' := by
  unfold frameDifference U2
  refine sub_mem (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left ?_)
  · rw [← a_span_frame]; exact Submodule.subset_span ⟨b, rfl⟩
  · rw [← a_span_frame]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem e_sum_alt (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (c : Fin (r + 1) → 𝓞 E) :
    ∑ b, c b • frameDifference F F' ξ b = ∑ b, c b • frame F' b - ∑ a, (ξ.mulVec c) a • frame F a := by
  unfold frameDifference
  simp_rw [smul_sub, Finset.sum_sub_distrib, e_frameAct, Finset.smul_sum, smul_smul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul]
  exact Finset.sum_congr rfl fun b _ => by rw [mul_comm]

theorem e_sum_mem_Xplus (F : LFlag S r T) (d : Fin (r + 1) → 𝓞 E) :
    ∑ a, d a • frame F a ∈ Xplus F := by
  have : ∑ a, d a • frame F a ∈ toO S (Xplus F) :=
    Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (by
      show frame F a ∈ Xplus F
      rw [← a_span_frame]; exact Submodule.subset_span ⟨a, rfl⟩)
  exact this

theorem e_key (hg : 0 < g) (hz : IsLift Λ F) (hz' : IsLift Λ F') (hc : IsFixedConv Λ g F)
    (hI : HInd F F') (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) {s : 𝓞 E}
    (hs1 : s - 1 ∈ Ideal.span {(g : 𝓞 E)}) (c : Fin (r + 1) → 𝓞 E) (u : S.V) (hu : u ∈ UU Λ F F')
    (h : s • ∑ b, c b • frameDifference F F' ξ b = (g : 𝓞 E) • u) (a : Fin (r + 1)) :
    (ξ.mulVec c) a ∈ Ideal.span {(g : 𝓞 E)} := by
  unfold UU at hu
  obtain ⟨p1, hp1, q1, hq1, rfl⟩ := Submodule.mem_sup.1 hu
  obtain ⟨p2, hp2, x0', hx0', rfl⟩ := Submodule.mem_sup.1 hp1
  obtain ⟨x0, hx0, q2, hq2, rfl⟩ := Submodule.mem_sup.1 hp2
  obtain ⟨o', rfl⟩ := Submodule.mem_span_singleton.1 hq1
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hq2
  rw [hz.2, hz'.2, e_sum_alt] at h
  set A := ∑ a, (ξ.mulVec c) a • frame F a with hA
  set A' := ∑ b, c b • frame F' b with hA'
  have hzX : F.fl.z ∈ Xplus F := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hzX' : F'.fl.z ∈ Xplus F' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hmem : s • A + (g : 𝓞 E) • (x0 + o • F.fl.z) ∈ Xplus F ⊓ Xplus F' := by
    constructor
    · exact (toO S (Xplus F)).add_mem
        ((toO S (Xplus F)).smul_mem _ (e_sum_mem_Xplus F _))
        ((toO S (Xplus F)).smul_mem _ ((toO S (Xplus F)).add_mem (Submodule.mem_sup_left hx0.2)
          ((toO S (Xplus F)).smul_mem _ hzX)))
    · have e : s • A + (g : 𝓞 E) • (x0 + o • F.fl.z) =
          s • A' - (g : 𝓞 E) • (x0' + o' • F'.fl.z) := by
        have h2 : s • A' - s • A = (g : 𝓞 E) • (x0 + o • F.fl.z) + (g : 𝓞 E) • (x0' + o' • F'.fl.z) := by
          rw [← smul_sub, h, ← smul_add]; congr 1; abel
        have h3 : s • A' = s • A + ((g : 𝓞 E) • (x0 + o • F.fl.z) + (g : 𝓞 E) • (x0' + o' • F'.fl.z)) := by
          rw [← h2]; abel
        rw [h3]; abel
      rw [e]
      exact (toO S (Xplus F')).sub_mem
        ((toO S (Xplus F')).smul_mem _ (e_sum_mem_Xplus F' _))
        ((toO S (Xplus F')).smul_mem _ ((toO S (Xplus F')).add_mem (Submodule.mem_sup_left hx0'.2)
          ((toO S (Xplus F')).smul_mem _ hzX')))
  rw [a_disj hI, Submodule.mem_bot] at hmem
  apply e_mem_span g hg
  intro P hP
  obtain ⟨c', -, hc1, heq⟩ := hc.1 P
  have hloc : x0 ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F)) :=
    Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hx0
  rw [heq] at hloc
  obtain ⟨t, ht, htx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.1 hloc
  obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 htx
  simp only [hc1 hP, one_smul] at hk
  have hsP : s ∉ P.asIdeal := by
    intro hs
    have h1 : (1 : 𝓞 E) ∈ P.asIdeal := by
      have : (1 : 𝓞 E) = s - (s - 1) := by ring
      rw [this]
      exact sub_mem hs ((Ideal.span_singleton_le_iff_mem _).2 hP hs1)
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  refine ⟨t * s, fun hts => (P.isPrime.mem_or_mem hts).elim ht hsP, ?_⟩
  let k' : Fin (r + 1) → 𝓞 E := Fin.snoc (α := fun _ => 𝓞 E) k (t * o)
  have hk' : ∑ a, k' a • frame F a = t • x0 + (t * o) • F.fl.z := by
    rw [Fin.sum_univ_castSucc, ← hk]
    simp [k', a_frame_castSucc, a_frame_last]
  have hsum : ∑ a, (t * s * (ξ.mulVec c) a + (g : 𝓞 E) * k' a) • frame F a = 0 := by
    simp_rw [add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum]
    rw [hk', ← hA]
    have : t • (s • A + (g : 𝓞 E) • (x0 + o • F.fl.z)) = 0 := by rw [hmem, smul_zero]
    rw [← this]
    simp only [smul_add, mul_smul]
    rw [smul_comm (g : 𝓞 E) t x0, smul_comm (g : 𝓞 E) t (o • F.fl.z)]
  have hind := (a_frame_indep F F' hI).1
  have h0 := Fintype.linearIndependent_iff.1 hind
    (fun a => ((t * s * (ξ.mulVec c) a + (g : 𝓞 E) * k' a : 𝓞 E) : E)) (by
      rw [← hsum]
      exact Finset.sum_congr rfl fun a _ => IsScalarTower.algebraMap_smul E _ _) a
  have h1 : t * s * (ξ.mulVec c) a + (g : 𝓞 E) * k' a = 0 :=
    RingOfIntegers.coe_injective (by simpa using h0)
  rw [Ideal.mem_span_singleton']
  exact ⟨-k' a, by linear_combination -h1⟩

omit [StarRing E] in
theorem e_unitri {n : ℕ} (ξ : Matrix (Fin n) (Fin n) (𝓞 E)) (h1 : ∀ a b, b < a → ξ a b = 0)
    (h2 : ∀ a, ξ a a = 1) (I : Ideal (𝓞 E)) (c : Fin n → 𝓞 E) (h : ∀ a, (ξ.mulVec c) a ∈ I)
    (b : Fin n) : c b ∈ I := by
  have hdet : ξ.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => h1 i j hij)]
    simp [h2]
  have hc : c = ξ.adjugate.mulVec (ξ.mulVec c) := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet, one_smul, Matrix.one_mulVec]
  rw [hc]
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (h a)

theorem e_exists_K (hΛ : Submodule.IsLattice E Λ) (hg : 0 < g) (hz : IsLift Λ F)
    (hc : IsFixedConv Λ g F) (hT : IsTerm Λ g F F') :
    ∃ K : AddSubgroup (BQ Λ F F'), (∀ x ∈ K, g • x = 0) ∧
      (Nat.card K : ℝ) = NE (E := E) g ^ (r + 1) := by
  obtain ⟨hz', ⟨ξ, hξ⟩, hG⟩ := hT
  have hI : HInd F F' := a_HInd F F' hG
  have hU : UUE Λ F F' = U2 F F' := a_HU Λ hΛ F F' hz.2 hz'.2
  obtain ⟨s, hs1, hsx, hsf, hsf'⟩ := exists_congruent_unit_scalar hg hz hc hξ
  have hex : ∀ b, ∃ lam ∈ Λ, (g : 𝓞 E) • lam = s • frameDifference F F' ξ b := by
    intro b
    have := hsx b
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at this
    exact this
  choose lam hlamΛ hlam using hex
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  have hlamU : ∀ b, lam b ∈ UUE Λ F F' := by
    intro b
    have h2 : (g : E)⁻¹ • (((g : 𝓞 E)) • lam b) = lam b := by
      rw [← IsScalarTower.algebraMap_smul E (g : 𝓞 E) (lam b), smul_smul]
      simp [hgE]
    rw [← h2, hlam, hU]
    exact (U2 F F').smul_mem _ ((toO S (U2 F F')).smul_mem s (frame_difference_mem_double_span ξ b))
  let w : Fin (r + 1) → BLat Λ F F' := fun b => ⟨lam b, hlamΛ b, hlamU b⟩
  let Φ : (Fin (r + 1) → 𝓞 E) →ₗ[𝓞 E] BQ Λ F F' :=
    Fintype.linearCombination (𝓞 E) (fun b => ((UU Λ F F').comap (BLat Λ F F').subtype).mkQ (w b))
  have hΦ : ∀ c, Φ c = 0 ↔ ∑ b, c b • lam b ∈ UU Λ F F' := by
    intro c
    have e1 : Φ c = ((UU Λ F F').comap (BLat Λ F F').subtype).mkQ (∑ b, c b • w b) := by
      simp only [Φ, Fintype.linearCombination_apply, map_sum, map_smul]
    rw [e1, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    simp [w]
  have hker : LinearMap.ker Φ =
      Submodule.pi Set.univ
        (fun _ : Fin (r + 1) => (Ideal.span {(g : 𝓞 E)} : Submodule (𝓞 E) (𝓞 E))) := by
    ext c
    rw [LinearMap.mem_ker, hΦ, Submodule.mem_pi]
    constructor
    · intro hu b _
      refine e_unitri ξ hξ.1 hξ.2.1 _ c (fun a => e_key hg hz hz' hc hI ξ hs1 c _ hu ?_ a) b
      simp_rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_comm (g : 𝓞 E), hlam, smul_comm s]
    · intro h
      refine Submodule.sum_mem _ fun b _ => ?_
      obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 (h b trivial)
      rw [← hc', mul_smul, hlam]
      exact Submodule.smul_mem _ _ (e_s_x_UU hz hz' hsf hsf' ξ b)
  refine ⟨(LinearMap.range Φ).toAddSubgroup, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    rw [← map_nsmul, ← LinearMap.mem_ker, hker, Submodule.mem_pi]
    intro b _
    rw [Ideal.mem_span_singleton']
    exact ⟨c b, by simp [mul_comm]⟩
  · rw [← e_card_pi (E := E) g (r + 1)]
    congr 1
    exact Nat.card_congr
      ((Φ.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hker)).toEquiv)

theorem conv_lift_card_le_norm_pow (hΛ : Submodule.IsLattice E Λ) (hg : 0 < g) (hz : IsLift Λ F)
    (hc : IsFixedConv Λ g F) (hT : IsTerm Λ g F F') :
    (Nat.card (gB Λ g F F') : ℝ) ≤ (Nat.card (BQ Λ F F') : ℝ) / NE (E := E) g ^ (r + 1) := by
  obtain ⟨K, hK, hcard⟩ := e_exists_K hΛ hg hz hc hT
  exact m_gB_le Λ F F' g hg (m_BQ_finite Λ F F' hΛ) K hK hcard

end Main

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem e_gS_pos (D : D7) : 0 < gS D :=
  Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem lemma_one_card_bound_local (D : D7) (Λ : VanishingOnXAndXPlusGluing.LatS D) {T T' : ℕ} (F : VanishingOnXAndXPlusGluing.FlS D T) (F' : VanishingOnXAndXPlusGluing.FlS D T')
    (hF : FixedHyp D Λ F) (hT : IsTerm Λ (gS D) F F') :
    (Nat.card (gB Λ (gS D) F F') : ℝ) ≤
      (Nat.card (BQ Λ F F') : ℝ) / NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) :=
  conv_lift_card_le_norm_pow hF.1 (e_gS_pos D) hF.2.2.1 hF.2.2.2 hT

end D7

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section I

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem i_star_int (o : 𝓞 E) : star (algebraMap (𝓞 E) E o) ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E o)) :=
    map_isIntegral_int (starRingEnd E) o.isIntegral_coe
  exact ⟨⟨_, h⟩, rfl⟩

theorem i_mem_dual (L : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ ∀ y ∈ L, S.hT y x ∈ (1 : Submodule (𝓞 E) E) :=
  Formalism.HermitianLatticesTheory.dualBasic_mem_dual S.hT L x

theorem i_isCompl (U : Submodule E S.V) (h : U ⊓ orth S U = ⊥) : IsCompl U (orth S U) := by
  refine ⟨disjoint_iff.2 h, codisjoint_iff.2 ?_⟩
  set b := Module.finBasis E U with hb
  set φ : S.V →ₗ[E] (Fin (finrank E U) → E) := LinearMap.pi (fun i => S.hT (b i : S.V)) with hφ
  have hker : LinearMap.ker φ ≤ orth S U := by
    intro y hy
    have h1 : ∀ i, S.hT ((b i : U) : S.V) y = 0 := fun i => congrFun (LinearMap.mem_ker.1 hy) i
    have h2 := a_orth_of_frame (fun i => ((b i : U) : S.V)) y h1
    have h3 : Submodule.span E (Set.range fun i => ((b i : U) : S.V)) = U := by
      have : (Set.range fun i => ((b i : U) : S.V)) = U.subtype '' (Set.range b) := by
        rw [← Set.range_comp]; rfl
      rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
    rwa [h3] at h2
  have h4 := LinearMap.finrank_range_add_finrank_ker φ
  have h5 : finrank E (LinearMap.range φ) ≤ finrank E U := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  have h6 : finrank E (LinearMap.ker φ) ≤ finrank E (orth S U) := Submodule.finrank_mono hker
  have h7 := Submodule.finrank_sup_add_finrank_inf_eq U (orth S U)
  rw [h, finrank_bot, add_zero] at h7
  apply Submodule.eq_top_of_finrank_eq
  have h8 := Submodule.finrank_le (U ⊔ orth S U)
  omega

theorem i_cancel {U U' : Submodule E S.V} (hd : U ⊓ U' = ⊥) {A A' B B' : Submodule (𝓞 E) S.V}
    (hA : A ≤ toO S U) (hA' : A' ≤ toO S U) (hB' : B' ≤ toO S U')
    (h : A ⊔ B = A' ⊔ B') : A ≤ A' := by
  intro a ha
  have h1 : a ∈ A' ⊔ B' := h ▸ Submodule.mem_sup_left ha
  obtain ⟨a', ha', b', hb', e⟩ := Submodule.mem_sup.1 h1
  have h2 : b' ∈ U ⊓ U' := by
    refine ⟨?_, hB' hb'⟩
    have : b' = a - a' := by rw [← e]; abel
    rw [this]
    exact sub_mem (hA ha) (hA' ha')
  rw [hd, Submodule.mem_bot] at h2
  rw [← e, h2, add_zero]
  exact ha'

section Pair

variable (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ)
  (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {U U' : Submodule E S.V} (hc : IsCompl U U')
  (ho : ∀ x ∈ U, ∀ y ∈ U', S.hT x y = 0)

include ho in
theorem i_ho' : ∀ x ∈ U', ∀ y ∈ U, S.hT x y = 0 := by
  intro x hx y hy
  rw [a_herm, ho y hy x hx, star_zero]

include hu in
theorem i_int {x y : S.V} (hx : x ∈ Λ) (hy : y ∈ Λ) : S.hT x y ∈ (1 : Submodule (𝓞 E) E) := by
  have : y ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hu]; exact hy
  exact (i_mem_dual Λ y).1 this x hx

def i_P (Λ : Submodule (𝓞 E) S.V) (U U' : Submodule E S.V) : Submodule (𝓞 E) S.V :=
  (Λ ⊔ toO S U') ⊓ toO S U

theorem i_mem_P {m : S.V} : m ∈ i_P Λ U U' ↔ m ∈ U ∧ ∃ l ∈ Λ, l - m ∈ U' := by
  unfold i_P
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨l, hl, w, hw, e⟩ := Submodule.mem_sup.1 h1
    refine ⟨h2, l, hl, ?_⟩
    have : l - m = -w := by rw [← e]; abel
    rw [this]; exact neg_mem hw
  · rintro ⟨h2, l, hl, hw⟩
    refine ⟨?_, h2⟩
    have : m = l + -(l - m) := by abel
    rw [this]
    exact Submodule.add_mem_sup hl (neg_mem (S := Submodule (𝓞 E) S.V) (s := toO S U') hw)

include hc in
theorem i_exists_P {l : S.V} (hl : l ∈ Λ) : ∃ p ∈ i_P Λ U U', l - p ∈ U' := by
  have h1 : l ∈ U ⊔ U' := by rw [hc.sup_eq_top]; trivial
  obtain ⟨p, hp, w, hw, e⟩ := Submodule.mem_sup.1 h1
  have h2 : l - p = w := by rw [← e]; abel
  exact ⟨p, (i_mem_P Λ).2 ⟨hp, l, hl, h2 ▸ hw⟩, h2 ▸ hw⟩

include hu hc ho in
theorem i_dualP : Formalism.HermitianLatticesTheory.dual S.hT (i_P Λ U U') ⊓ toO S U = Λ ⊓ toO S U := by
  have ho' := i_ho' ho
  ext u
  rw [Submodule.mem_inf, Submodule.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have hu' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hu
    rw [← hu', i_mem_dual]
    intro l hl
    obtain ⟨p, hp, hw⟩ := i_exists_P Λ hc hl
    have : S.hT l u = S.hT p u := by
      have e : l = p + (l - p) := by abel
      rw [e, map_add, LinearMap.add_apply, ho' _ hw u h2, add_zero]
    rw [this]
    exact (i_mem_dual _ u).1 h1 p hp
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [i_mem_dual]
    intro p hp
    obtain ⟨hpU, l, hl, hw⟩ := (i_mem_P Λ).1 hp
    have : S.hT p u = S.hT l u := by
      have e : l = p + (l - p) := by abel
      rw [e, map_add, LinearMap.add_apply, ho' _ hw u h2, add_zero]
    rw [this]
    exact i_int Λ hu hl h1

theorem i_fg_of_le {L A : Submodule (𝓞 E) S.V} (hL : L.FG) (h : A ≤ L) : A.FG := by
  have h1 : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  have h2 : IsNoetherian (𝓞 E) L := isNoetherian_of_isNoetherianRing_of_finite (𝓞 E) L
  exact (isNoetherian_submodule.1 h2) _ h

include hΛ hc in
theorem sum_of_intersections_is_lattice : Submodule.IsLattice E ((Λ ⊓ toO S U) ⊔ (Λ ⊓ toO S U')) := by
  refine ⟨i_fg_of_le hΛ.fg (sup_le inf_le_left inf_le_left), ?_⟩
  rw [a_span_sup, a_span_inf Λ hΛ U, a_span_inf Λ hΛ U', hc.sup_eq_top]

theorem i_M_le_P : Λ ⊓ toO S U ≤ i_P Λ U U' :=
  fun m hm => (i_mem_P Λ).2 ⟨hm.2, m, hm.1, by simp⟩

include hu ho in
theorem i_PN_le : i_P Λ U U' ⊔ (Λ ⊓ toO S U') ≤
    Formalism.HermitianLatticesTheory.dual S.hT ((Λ ⊓ toO S U) ⊔ (Λ ⊓ toO S U')) := by
  have ho' := i_ho' ho
  intro x hx
  rw [i_mem_dual]
  intro y hy
  obtain ⟨p, hp, n, hn, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨m, hm, n', hn', rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨hpU, l, hl, hw⟩ := (i_mem_P Λ).1 hp
  have e1 : S.hT m n = 0 := ho m hm.2 n hn.2
  have e2 : S.hT n' p = 0 := ho' n' hn'.2 p hpU
  have e3 : S.hT m p = S.hT m l := by
    have e : l = p + (l - p) := by abel
    rw [e, map_add, ho m hm.2 _ hw, add_zero]
  simp only [map_add, LinearMap.add_apply, e1, e2, e3, add_zero, zero_add]
  exact add_mem (i_int Λ hu hm.1 hl) (i_int Λ hu hn'.1 hn.1)

include hΛ hu hc ho in
theorem i_PN_lat : Submodule.IsLattice E (i_P Λ U U' ⊔ (Λ ⊓ toO S U')) := by
  have h0 := sum_of_intersections_is_lattice Λ hΛ hc
  have hD := (Formalism.HermitianLatticesTheory.dualLattice (𝓞 E) E S.V S.hT S.herm S.nondeg i_star_int _ h0).1
  refine ⟨i_fg_of_le hD.fg (i_PN_le Λ hu ho), ?_⟩
  rw [eq_top_iff, ← h0.span_eq_top]
  exact Submodule.span_mono (sup_le_sup_right (i_M_le_P Λ) _)

include hΛ hu hc ho in

theorem i_proj_eq : i_P Λ U U' = dualIn S (Λ ⊓ toO S U) := by
  have ho' := i_ho' ho
  have hd : U ⊓ U' = ⊥ := hc.inf_eq_bot
  have DOS := Formalism.HermitianLatticesTheory.dualOrthSum (𝓞 E) E S.V S.hT U U' hc ho ho'
  have e1 := DOS (i_P Λ U U') (Λ ⊓ toO S U') (fun x hx => hx.2) (fun x hx => hx.2)
  rw [i_dualP Λ hu hc ho] at e1
  have e2 := DOS (Λ ⊓ toO S U) (Formalism.HermitianLatticesTheory.dual S.hT (Λ ⊓ toO S U') ⊓ toO S U') (fun x hx => hx.2)
    (fun x hx => hx.2)
  have e3 := (Formalism.HermitianLatticesTheory.dualLattice (𝓞 E) E S.V S.hT S.herm S.nondeg i_star_int _
    (i_PN_lat Λ hΛ hu hc ho)).2.1
  rw [e1, e2] at e3
  have e4 : dualIn S (Λ ⊓ toO S U) = Formalism.HermitianLatticesTheory.dual S.hT (Λ ⊓ toO S U) ⊓ toO S U := by
    show Formalism.HermitianLatticesTheory.dual S.hT (Λ ⊓ toO S U) ⊓
      (Submodule.span E ((Λ ⊓ toO S U : Submodule (𝓞 E) S.V) : Set S.V)).restrictScalars (𝓞 E) = _
    rw [a_span_inf Λ hΛ U]
  rw [e4]
  exact le_antisymm (i_cancel hd inf_le_right inf_le_right inf_le_right e3.symm)
    (i_cancel hd inf_le_right inf_le_right inf_le_right e3)

include hc in
theorem i_sub_proj (x : S.V) : x - U.projection U' hc x ∈ U' := by
  rw [← Submodule.projection_apply_eq_zero_iff hc, map_sub,
    Submodule.projection_apply_of_mem_left hc (Submodule.projection_apply_mem hc x), sub_self]

def projectionToDualIntersection : Λ →ₗ[𝓞 E] dualIn S (Λ ⊓ toO S U) :=
  LinearMap.codRestrict _ (((U.projection U' hc).restrictScalars (𝓞 E)) ∘ₗ Λ.subtype)
    (fun l => by
      rw [← i_proj_eq Λ hΛ hu hc ho]
      exact (i_mem_P Λ).2 ⟨Submodule.projection_apply_mem hc _, l, l.2, i_sub_proj hc _⟩)

theorem projection_dual_coe (l : Λ) : ((projectionToDualIntersection Λ hΛ hu hc ho l : dualIn S (Λ ⊓ toO S U)) : S.V) =
    U.projection U' hc (l : S.V) := rfl

include hΛ hu hc ho in

theorem i_glue : Nonempty
    ((Λ ⧸ ((Λ ⊓ toO S U) ⊔ (Λ ⊓ toO S U')).comap Λ.subtype) ≃ₗ[𝓞 E]
      (dualIn S (Λ ⊓ toO S U) ⧸ (Λ ⊓ toO S U).comap (dualIn S (Λ ⊓ toO S U)).subtype)) := by
  set f : Λ →ₗ[𝓞 E] (dualIn S (Λ ⊓ toO S U) ⧸ (Λ ⊓ toO S U).comap (dualIn S (Λ ⊓ toO S U)).subtype) :=
    ((Λ ⊓ toO S U).comap (dualIn S (Λ ⊓ toO S U)).subtype).mkQ ∘ₗ projectionToDualIntersection Λ hΛ hu hc ho with hf
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ c
    have hm : (m : S.V) ∈ i_P Λ U U' := by rw [i_proj_eq Λ hΛ hu hc ho]; exact m.2
    obtain ⟨hmU, l, hl, hw⟩ := (i_mem_P Λ).1 hm
    refine ⟨⟨l, hl⟩, ?_⟩
    have : projectionToDualIntersection Λ hΛ hu hc ho ⟨l, hl⟩ = m := by
      apply Subtype.ext
      rw [projection_dual_coe]
      have e : l = (m : S.V) + (l - m) := by abel
      show U.projection U' hc l = m
      rw [e, map_add, Submodule.projection_apply_of_mem_left hc hmU,
        (Submodule.projection_apply_eq_zero_iff hc).2 hw, add_zero]
    rw [hf, LinearMap.comp_apply, this]
  have hker : LinearMap.ker f = ((Λ ⊓ toO S U) ⊔ (Λ ⊓ toO S U')).comap Λ.subtype := by
    ext l
    rw [LinearMap.mem_ker, hf, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.mem_comap]
    show U.projection U' hc (l : S.V) ∈ Λ ⊓ toO S U ↔ (l : S.V) ∈ _
    constructor
    · intro h
      have e : (l : S.V) = U.projection U' hc (l : S.V) + ((l : S.V) - U.projection U' hc (l : S.V)) := by
        abel
      rw [e]
      exact Submodule.add_mem_sup h ⟨sub_mem l.2 h.1, i_sub_proj hc _⟩
    · intro h
      obtain ⟨m, hm, n, hn, e⟩ := Submodule.mem_sup.1 h
      rw [← e, map_add, Submodule.projection_apply_of_mem_left hc hm.2,
        (Submodule.projection_apply_eq_zero_iff hc).2 hn.2, add_zero]
      exact hm
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)⟩

include hΛ hu hc ho in

theorem i_glue3 : Nonempty
    ((dualIn S (Λ ⊓ toO S U) ⧸ (Λ ⊓ toO S U).comap (dualIn S (Λ ⊓ toO S U)).subtype) ≃ₗ[𝓞 E]
      (dualIn S (Λ ⊓ toO S U') ⧸ (Λ ⊓ toO S U').comap (dualIn S (Λ ⊓ toO S U')).subtype)) := by
  obtain ⟨e1⟩ := i_glue Λ hΛ hu hc ho
  obtain ⟨e2⟩ := i_glue Λ hΛ hu hc.symm (i_ho' ho)
  exact ⟨e1.symm.trans ((Submodule.quotEquivOfEq _ _ (by rw [sup_comm])).trans e2)⟩

end Pair

section Loc

variable (p : Ideal (𝓞 E)) [p.IsPrime] (A B : Submodule (𝓞 E) S.V)

theorem i_mem_locP {L : Submodule (𝓞 E) S.V} {x : S.V} :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

theorem i_le_locP (L : Submodule (𝓞 E) S.V) : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L :=
  Formalism.HermitianLatticesTheory.locBasic_le_locS _ L

def i_g : (A ⧸ B.comap A.subtype) →ₗ[𝓞 E]
    (Formalism.HermitianLatticesTheory.localization₂ p A ⧸ (Formalism.HermitianLatticesTheory.localization₂ p B).comap (Formalism.HermitianLatticesTheory.localization₂ p A).subtype) :=
  Submodule.mapQ _ _ (Submodule.inclusion (i_le_locP p A)) (fun _ hx => i_le_locP p B hx)

theorem i_g_mk (a : A) : i_g p A B (Submodule.Quotient.mk a) =
    Submodule.Quotient.mk ⟨(a : S.V), i_le_locP p A a.2⟩ := rfl

instance i_isLoc : IsLocalizedModule p.primeCompl (i_g p A B) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hs0 : (algebraMap (𝓞 E) E (s : 𝓞 E)) ≠ 0 := by
      have : (s : 𝓞 E) ≠ 0 := fun h => s.2 (h ▸ p.zero_mem)
      simpa using this
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
      rw [Module.algebraMap_end_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      obtain ⟨t, ht, h⟩ := (i_mem_locP p).1 (show (s : 𝓞 E) • (x : S.V) ∈ Formalism.HermitianLatticesTheory.localization₂ p B from hq)
      exact (i_mem_locP p).2 ⟨t * s, p.primeCompl.mul_mem ht s.2, by rw [mul_smul]; exact h⟩
    · intro q
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
      obtain ⟨t, ht, h⟩ := (i_mem_locP p).1 x.2
      have e : (s : 𝓞 E) • ((algebraMap (𝓞 E) E (s : 𝓞 E))⁻¹ • (x : S.V)) = x := by
        rw [← IsScalarTower.algebraMap_smul E (s : 𝓞 E), smul_smul, mul_inv_cancel₀ hs0, one_smul]
      have hy : (algebraMap (𝓞 E) E (s : 𝓞 E))⁻¹ • (x : S.V) ∈ Formalism.HermitianLatticesTheory.localization₂ p A :=
        (i_mem_locP p).2 ⟨t * s, p.primeCompl.mul_mem ht s.2, by rw [mul_smul, e]; exact h⟩
      refine ⟨Submodule.Quotient.mk ⟨_, hy⟩, ?_⟩
      rw [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.mkQ_apply]
      congr 1
      exact Subtype.ext e
  surj y := by
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨t, ht, h⟩ := (i_mem_locP p).1 x.2
    exact ⟨(Submodule.Quotient.mk ⟨t • (x : S.V), h⟩, ⟨t, ht⟩), rfl⟩
  exists_of_eq := by
    intro x₁ x₂ h
    obtain ⟨a₁, rfl⟩ := Submodule.mkQ_surjective _ x₁
    obtain ⟨a₂, rfl⟩ := Submodule.mkQ_surjective _ x₂
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, i_g_mk, i_g_mk, Submodule.Quotient.eq] at h
    obtain ⟨t, ht, h'⟩ := (i_mem_locP p).1 (show (a₁ : S.V) - a₂ ∈ Formalism.HermitianLatticesTheory.localization₂ p B from h)
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [Submonoid.mk_smul, Submonoid.mk_smul, Submodule.mkQ_apply, Submodule.mkQ_apply,
      ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    show t • (a₁ : S.V) - t • (a₂ : S.V) ∈ B
    rw [← smul_sub]; exact h'

variable {A B}

theorem i_locLen_congr {A' B' : Submodule (𝓞 E) S.V}
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (A' ⧸ B'.comap A'.subtype)) :
    Formalism.HermitianLatticesTheory.locLen p A B = Formalism.HermitianLatticesTheory.locLen p A' B' := by
  unfold Formalism.HermitianLatticesTheory.locLen
  have := IsLocalizedModule.linearEquiv p.primeCompl (i_g p A B) (i_g p A' B' ∘ₗ e.toLinearMap)
  rw [this.length_eq]

theorem i_lidx_of_le (h : B ≤ A) : Formalism.HermitianLatticesTheory.lidx p A B = Formalism.HermitianLatticesTheory.locLen p A B := by
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [inf_eq_right.2 h, Formalism.HermitianLatticesTheory.indexBasic_locLen_self, Nat.cast_zero, sub_zero]

end Loc

theorem i_genIdx_congr {A B A' B' : Submodule (𝓞 E) S.V} (h : B ≤ A) (h' : B' ≤ A')
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (A' ⧸ B'.comap A'.subtype)) :
    genIdx S A B = genIdx S A' B' := by
  unfold genIdx genIdxH
  apply finprod_congr
  intro P
  have := P.isPrime
  rw [i_lidx_of_le P.asIdeal h, i_lidx_of_le P.asIdeal h', i_locLen_congr P.asIdeal e]

theorem i_le_dualIn (Λ : Submodule (𝓞 E) S.V) (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (U : Submodule E S.V) : Λ ⊓ toO S U ≤ dualIn S (Λ ⊓ toO S U) := by
  intro m hm
  refine ⟨(i_mem_dual _ m).2 fun y hy => i_int Λ hu hy.1 hm.1, ?_⟩
  exact Submodule.subset_span hm

theorem i_det_eq (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {U U' : Submodule E S.V} (hc : IsCompl U U')
    (ho : ∀ x ∈ U, ∀ y ∈ U', S.hT x y = 0) :
    latDet S (Λ ⊓ toO S U) = latDet S (Λ ⊓ toO S U') := by
  obtain ⟨e⟩ := i_glue3 Λ hΛ hu hc ho
  unfold latDet latDetH
  congr 1
  exact i_genIdx_congr (i_le_dualIn Λ hu U) (i_le_dualIn Λ hu U') e

theorem i_gluing (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (U : Submodule E S.V) (hU : U ⊓ orth S U = ⊥) :
    {m | m ∈ U ∧ ∃ l ∈ Λ, l - m ∈ orth S U} = (dualIn S (Λ ⊓ toO S U) : Set S.V) ∧
    Nonempty
      ((Λ ⧸ ((Λ ⊓ toO S U) ⊔ (Λ ⊓ toO S (orth S U))).comap Λ.subtype) ≃ₗ[𝓞 E]
        (dualIn S (Λ ⊓ toO S U) ⧸ (Λ ⊓ toO S U).comap (dualIn S (Λ ⊓ toO S U)).subtype)) ∧
    Nonempty
      ((dualIn S (Λ ⊓ toO S U) ⧸ (Λ ⊓ toO S U).comap (dualIn S (Λ ⊓ toO S U)).subtype) ≃ₗ[𝓞 E]
        (dualIn S (Λ ⊓ toO S (orth S U)) ⧸
          (Λ ⊓ toO S (orth S U)).comap (dualIn S (Λ ⊓ toO S (orth S U))).subtype)) ∧
    latDet S (Λ ⊓ toO S U) = latDet S (Λ ⊓ toO S (orth S U)) := by
  have hc := i_isCompl U hU
  have ho : ∀ x ∈ U, ∀ y ∈ orth S U, S.hT x y = 0 := fun x hx y hy => (a_mem_orth U y).1 hy x hx
  refine ⟨?_, i_glue Λ hΛ hu hc ho, i_glue3 Λ hΛ hu hc ho, i_det_eq Λ hΛ hu hc ho⟩
  rw [← i_proj_eq Λ hΛ hu hc ho]
  ext m
  exact (i_mem_P Λ).symm

end I

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem i_stGlue (D : D7) : Formalism.MainNotions.S.UnitaryVolumeMass.stGlue D :=
  fun Λ hΛ hu U hU => i_gluing Λ hΛ hu U hU

theorem gluing_unimodular_first (D : D7) : VanishingOnXAndXPlusGlobal.adm1 D := i_stGlue D

end D7

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open NumberField Module IsDedekindDomain Formalism.HermitianLatticesTheory

section Loc

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

def g_Comm (A B : Submodule (𝓞 E) W) : Prop := ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ x ∈ A, d • x ∈ B

theorem g_Comm_mono {A A' B B' : Submodule (𝓞 E) W} (h : g_Comm A B) (hA : A' ≤ A) (hB : B ≤ B') :
    g_Comm A' B' := by
  obtain ⟨d, hd, h⟩ := h
  exact ⟨d, hd, fun x hx => hB (h x (hA hx))⟩

def g_idx (A B : Submodule (𝓞 E) W) : ℕ := Nat.card (A ⧸ B.comap A.subtype)

theorem g_idx_mul {A B C : Submodule (𝓞 E) W} (hCB : C ≤ B) (hBA : B ≤ A) :
    g_idx B C * g_idx A B = g_idx A C :=
  AddSubgroup.relIndex_mul_relIndex C.toAddSubgroup B.toAddSubgroup A.toAddSubgroup hCB hBA

theorem g_fin {A B : Submodule (𝓞 E) W} (hA : A.FG) (h : g_Comm A B) :
    Finite (A ⧸ B.comap A.subtype) := by
  have h3 : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.2 hA
  obtain ⟨d, hd, h⟩ := h
  apply m_fin_quot
  intro w
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero (by simpa using hd), ?_⟩
  have hmem : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : 𝓞 E) ∈ Ideal.span {d} := Ideal.absNorm_mem _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  show ((Ideal.absNorm (Ideal.span {d}) • w : A) : W) ∈ B
  rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← hc, mul_smul]
  exact B.smul_mem _ (h _ w.2)

theorem g_idx_pos {A B : Submodule (𝓞 E) W} (hA : A.FG) (h : g_Comm A B) : 0 < g_idx A B := by
  have := g_fin hA h
  exact Nat.card_pos

theorem g_fg_le {A B : Submodule (𝓞 E) W} (hA : A.FG) (h : B ≤ A) : B.FG := by
  have h1 : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.2 hA
  have h2 : IsNoetherian (𝓞 E) A := isNoetherian_of_isNoetherianRing_of_finite (𝓞 E) A
  exact (isNoetherian_submodule.1 h2) B h

theorem g_len_ne_top (p : Ideal (𝓞 E)) [p.IsPrime] {A B : Submodule (𝓞 E) W} (hA : A.FG)
    (h : g_Comm A B) :
    Module.length (𝓞 E) (↥(localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype) ≠ ⊤ := by
  obtain ⟨d, hd, h⟩ := h
  exact Module.length_ne_top_iff.2
    (indexBasic_finLen p A B hA (mem_nonZeroDivisors_iff_ne_zero.2 hd) h)

theorem g_locLen_add (p : Ideal (𝓞 E)) [p.IsPrime] {A B C : Submodule (𝓞 E) W} (hA : A.FG)
    (hCB : C ≤ B) (hBA : B ≤ A) (h : g_Comm A C) :
    locLen p A C = locLen p B C + locLen p A B := by
  have e := indexBasic_len_add (localization₂ p C) (localization₂ p B) (localization₂ p A) (locBasic_locS_mono _ hCB)
    (locBasic_locS_mono _ hBA)
  unfold locLen
  rw [e, ENat.toNat_add (g_len_ne_top p (g_fg_le hA hBA) (g_Comm_mono h hBA le_rfl))
    (g_len_ne_top p hA (g_Comm_mono h le_rfl hCB))]

theorem g_locLen_zero (p : Ideal (𝓞 E)) [p.IsPrime] {A B : Submodule (𝓞 E) W} {s : 𝓞 E} (hs : s ∉ p)
    (h : ∀ x ∈ A, s • x ∈ B) : locLen p A B = 0 := by
  have hle : localization₂ p A ≤ localization₂ p B := by
    rintro x ⟨t, ht, htx⟩
    refine ⟨s * t, ?_, by rw [mul_smul]; exact h _ htx⟩
    exact (Ideal.primeCompl p).mul_mem hs ht
  unfold locLen
  rw [Submodule.comap_subtype_eq_top.2 hle]
  simp

theorem g_support (A B : Submodule (𝓞 E) W) (h : g_Comm A B) :
    {P : HeightOneSpectrum (𝓞 E) | locLen P.asIdeal A B ≠ 0}.Finite := by
  obtain ⟨d, hd, h⟩ := h
  have hI : Ideal.span {d} ≠ 0 := by simpa using hd
  refine (Ideal.finite_factors hI).subset ?_
  intro P hP
  rw [Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  by_contra hdP
  exact hP (g_locLen_zero P.asIdeal hdP h)

theorem g_simple_kill {A B : Submodule (𝓞 E) W} {P₀ : Ideal (𝓞 E)}
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ P₀)) {p : 𝓞 E} (hp : p ∈ P₀) {x : W} (hx : x ∈ A) :
    p • x ∈ B := by
  have h0 : p • (Submodule.Quotient.mk ⟨x, hx⟩ : A ⧸ B.comap A.subtype) = 0 := by
    apply e.injective
    rw [map_smul, map_zero]
    obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk ⟨x, hx⟩))
    rw [← ho]
    show Ideal.Quotient.mk P₀ (p * o) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (P₀.mul_mem_right _ hp)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
  exact h0

theorem g_simple_len {A B : Submodule (𝓞 E) W} {P₀ : Ideal (𝓞 E)} (hP : P₀.IsMaximal) [P₀.IsPrime]
    (hBA : B ≤ A) (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ P₀)) : locLen P₀ A B = 1 := by
  have hA : A ≤ localization₂ P₀ A := locBasic_le_locS _ A
  have hB : B ≤ localization₂ P₀ B := locBasic_le_locS _ B
  let φ : (A ⧸ B.comap A.subtype) →ₗ[𝓞 E] (↥(localization₂ P₀ A) ⧸ (localization₂ P₀ B).comap (localization₂ P₀ A).subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hA) (fun x hx => hB hx)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H a =>
      rw [LinearMap.mem_ker] at hy
      dsimp only [φ] at hy
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨s, hs, hsa⟩ : (a : W) ∈ localization₂ P₀ B := hy
      obtain ⟨t, p, hp, h1⟩ := hP.exists_inv hs
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      show (a : W) ∈ B
      have : (a : W) = t • (s • (a : W)) + p • (a : W) := by
        rw [← mul_smul, ← add_smul, h1, one_smul]
      rw [this]
      exact B.add_mem (B.smul_mem _ hsa) (g_simple_kill e hp a.2)
  have hsurj : Function.Surjective φ := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨s, hs, hsx⟩ : (x : W) ∈ localization₂ P₀ A := x.2
      obtain ⟨t, p, hp, h1⟩ := hP.exists_inv hs
      refine ⟨Submodule.Quotient.mk ⟨t • (s • (x : W)), A.smul_mem _ hsx⟩, ?_⟩
      dsimp only [φ]
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
      show t • (s • (x : W)) - (x : W) ∈ localization₂ P₀ B
      have : t • (s • (x : W)) - (x : W) = -(p • (x : W)) := by
        have h2 : (x : W) = t • (s • (x : W)) + p • (x : W) := by
          rw [← mul_smul, ← add_smul, h1, one_smul]
        nth_rewrite 2 [h2]
        abel
      rw [this]
      refine neg_mem ⟨s, hs, ?_⟩
      rw [smul_comm]
      exact g_simple_kill e hp hsx
  have h1 : Module.length (𝓞 E) (𝓞 E ⧸ P₀) = 1 :=
    Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 hP))
  unfold locLen
  rw [← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).length_eq, e.length_eq, h1]
  rfl

theorem g_simple_len_ne {A B : Submodule (𝓞 E) W} {P₀ : Ideal (𝓞 E)} (hP : P₀.IsMaximal)
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ P₀)) (p : Ideal (𝓞 E)) [hp : p.IsPrime] (hne : p ≠ P₀) :
    locLen p A B = 0 := by
  have : ∃ s ∈ P₀, s ∉ p := by
    by_contra hcon
    push_neg at hcon
    exact hne (hP.eq_of_le hp.ne_top hcon).symm
  obtain ⟨s, hs, hsp⟩ := this
  exact g_locLen_zero p hsp (fun x hx => g_simple_kill e hs hx)

theorem g_chain_ind (motive : Submodule (𝓞 E) W → Submodule (𝓞 E) W → Prop) (h0 : ∀ A, motive A A)
    (hs : ∀ A B' B : Submodule (𝓞 E) W, A.FG → g_Comm A B → B ≤ B' → B' ≤ A → ∀ P₀ : Ideal (𝓞 E),
      P₀.IsMaximal → ((A ⧸ B'.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ P₀)) → motive B' B → motive A B) :
    ∀ A B : Submodule (𝓞 E) W, A.FG → g_Comm A B → B ≤ A → motive A B := by
  intro A B hA hC hBA
  induction hn : g_idx A B using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    have hfin : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.2 hA
    rcases eq_top_or_exists_le_coatom (B.comap A.subtype) with htop | ⟨m, hm, hle⟩
    · have : A = B := le_antisymm (Submodule.comap_subtype_eq_top.1 htop) hBA
      subst this
      exact h0 _
    · have hcm : (m.map A.subtype).comap A.subtype = m :=
        Submodule.comap_map_eq_of_injective A.injective_subtype m
      have hB' : B ≤ m.map A.subtype := fun x hx => ⟨⟨x, hBA hx⟩, hle hx, rfl⟩
      have hB'A : m.map A.subtype ≤ A := Submodule.map_subtype_le A m
      have hsimple : IsSimpleModule (𝓞 E) (A ⧸ (m.map A.subtype).comap A.subtype) := by
        rw [hcm]; exact isSimpleModule_iff_isCoatom.2 hm
      obtain ⟨P₀, hP₀, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hsimple
      refine hs A (m.map A.subtype) B hA hC hB' hB'A P₀ hP₀ e ?_
      have hmul := g_idx_mul hB' hB'A
      have hpos : 0 < g_idx (m.map A.subtype) B :=
        g_idx_pos (g_fg_le hA hB'A) (g_Comm_mono hC hB'A le_rfl)
      have hgt : 1 < g_idx A (m.map A.subtype) := by
        have hf : Finite (A ⧸ (m.map A.subtype).comap A.subtype) := g_fin hA (g_Comm_mono hC le_rfl hB')
        have hnt : Nontrivial (A ⧸ (m.map A.subtype).comap A.subtype) := IsSimpleModule.nontrivial (𝓞 E) _
        exact Finite.one_lt_card
      refine ih (g_idx (m.map A.subtype) B) ?_ _ (g_fg_le hA hB'A) (g_Comm_mono hC hB'A le_rfl) hB' rfl
      rw [← hn, ← hmul]
      exact lt_mul_of_one_lt_right hpos hgt

def g_Psi (A B : Submodule (𝓞 E) W) : ℝ :=
  ∏ᶠ P : HeightOneSpectrum (𝓞 E), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (locLen P.asIdeal A B)

theorem g_fms (A B : Submodule (𝓞 E) W) (h : g_Comm A B) :
    Function.HasFiniteMulSupport (fun P : HeightOneSpectrum (𝓞 E) =>
      ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (locLen P.asIdeal A B)) := by
  refine (g_support A B h).subset ?_
  intro P hP h0
  apply hP
  show ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (locLen P.asIdeal A B) = 1
  rw [h0, pow_zero]

theorem g_Psi_mul {A B C : Submodule (𝓞 E) W} (hA : A.FG) (hCB : C ≤ B) (hBA : B ≤ A)
    (h : g_Comm A C) : g_Psi A C = g_Psi B C * g_Psi A B := by
  unfold g_Psi
  rw [← finprod_mul_distrib (g_fms B C (g_Comm_mono h hBA le_rfl)) (g_fms A B (g_Comm_mono h le_rfl hCB))]
  congr 1
  funext P
  rw [g_locLen_add P.asIdeal hA hCB hBA h, pow_add]

theorem g_Psi_eq : ∀ A B : Submodule (𝓞 E) W, A.FG → g_Comm A B → B ≤ A →
    g_Psi A B = (g_idx A B : ℝ) := by
  apply g_chain_ind
  · intro A
    have h1 : g_idx A A = 1 := by
      unfold g_idx
      rw [Submodule.comap_subtype_self]
      exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩
    unfold g_Psi
    rw [h1]
    simp [indexBasic_locLen_self]
  · intro A B' B hA hC hBB' hB'A P₀ hP₀ e ih
    rw [g_Psi_mul hA hBB' hB'A hC, ih, ← g_idx_mul hBB' hB'A]
    push_cast
    congr 1
    have hne : P₀ ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP₀ (RingOfIntegers.not_isField E)
    let Q : HeightOneSpectrum (𝓞 E) := ⟨P₀, hP₀.isPrime, hne⟩
    unfold g_Psi
    rw [finprod_eq_single _ Q]
    · have : locLen Q.asIdeal A B' = 1 := g_simple_len (P₀ := Q.asIdeal) hP₀ hB'A e
      rw [this, pow_one]
      have hc : g_idx A B' = Nat.card (𝓞 E ⧸ P₀) := Nat.card_congr e.toEquiv
      rw [hc, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    · intro P hP
      have hne' : P.asIdeal ≠ P₀ := fun h => hP (HeightOneSpectrum.ext h)
      rw [g_simple_len_ne hP₀ e P.asIdeal hne', pow_zero]

end Loc

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module IsDedekindDomain Formalism.HermitianLatticesTheory

section Idx

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem g_Comm_inf {A B C : Submodule (𝓞 E) S.V} (h : g_Comm A B) (h' : g_Comm A C) :
    g_Comm A (B ⊓ C) := by
  obtain ⟨d, hd, h⟩ := h
  obtain ⟨e, he, h'⟩ := h'
  refine ⟨d * e, mul_ne_zero hd he, fun x hx => ⟨?_, ?_⟩⟩
  · rw [mul_comm, mul_smul]; exact B.smul_mem _ (h x hx)
  · rw [mul_smul]; exact C.smul_mem _ (h' x hx)

theorem g_Comm_of_span {A B : Submodule (𝓞 E) S.V} (hA : A.FG) (h : spanE S A ≤ spanE S B) :
    g_Comm A B := by
  have hle : A ≤ locS (nonZeroDivisors (𝓞 E)) B := by
    intro x hx
    obtain ⟨d, hd, hdx⟩ := m_exists_smul_mem B (h (Submodule.subset_span hx))
    exact ⟨d, mem_nonZeroDivisors_iff_ne_zero.2 hd, hdx⟩
  obtain ⟨d, hd, h⟩ := indexBasic_denom _ A B hA hle
  exact ⟨d, nonZeroDivisors.ne_zero hd, h⟩

theorem g_span_eq {A B : Submodule (𝓞 E) S.V} (h : g_Comm A B) (hBA : B ≤ A) :
    spanE S A = spanE S B := by
  apply le_antisymm
  · unfold spanE
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨d, hd, h⟩ := h
    have hd' : (algebraMap (𝓞 E) E d) ≠ 0 := by
      simpa using (map_ne_zero_iff (algebraMap (𝓞 E) E) (IsFractionRing.injective (𝓞 E) E)).2 hd
    have : x = (algebraMap (𝓞 E) E d)⁻¹ • (d • x) := by
      rw [← IsScalarTower.algebraMap_smul E d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (h x hx))
  · exact Submodule.span_mono hBA

theorem g_genIdx_via {A B D : Submodule (𝓞 E) S.V} (hA : A.FG) (hB : B.FG) (hDA : D ≤ A) (hDB : D ≤ B)
    (cA : g_Comm A D) (cB : g_Comm B D) :
    genIdx S A B = (g_idx A D : ℝ) / (g_idx B D : ℝ) := by
  rw [← g_Psi_eq A D hA cA hDA, ← g_Psi_eq B D hB cB hDB]
  unfold g_Psi
  rw [← finprod_div_distrib (g_fms A D cA) (g_fms B D cB)]
  unfold genIdx genIdxH
  congr 1
  funext P
  have hN : ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ≠ 0 := by
    have : Ideal.absNorm P.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
    exact_mod_cast this
  rw [indexBasic_lidx_via P.asIdeal A B D hDA hDB (g_len_ne_top _ hA cA) (g_len_ne_top _ hB cB),
    zpow_sub₀ hN, zpow_natCast, zpow_natCast]

omit [StarRing E] in

theorem g_locPrincipal {P₀ : Ideal (𝓞 E)} (hP : P₀.IsMaximal) :
    ∃ a ∈ P₀, a ≠ 0 ∧ ∃ j, j ∉ P₀ ∧ ∀ p ∈ P₀, ∃ o, j * p = a * o := by
  have hne : P₀ ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  obtain ⟨a, ha1, ha2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P₀ hne hP.ne_top 1
  rw [pow_one] at ha1
  obtain ⟨J, hJ⟩ := Ideal.dvd_span_singleton.2 ha1
  have hJP : ¬ J ≤ P₀ := by
    intro hle
    apply ha2
    have : Ideal.span {a} ≤ P₀ ^ (1 + 1) := by
      rw [hJ, pow_succ, pow_one]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self a)
  obtain ⟨j, hjJ, hjP⟩ := SetLike.not_le_iff_exists.1 hJP
  refine ⟨a, ha1, ?_, j, hjP, ?_⟩
  · rintro rfl
    exact ha2 (zero_mem _)
  · intro p hp
    have : p * j ∈ Ideal.span {a} := by rw [hJ]; exact Ideal.mul_mem_mul hp hjJ
    obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨o, by rw [mul_comm j p, ← ho, mul_comm]⟩

def g_StarInt (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ o : 𝓞 E, ∃ o' : 𝓞 E, (o' : E) = star (o : E)

theorem g_mem_dualIn {M : Submodule (𝓞 E) S.V} {x : S.V} :
    x ∈ dualIn S M ↔ (∀ y ∈ M, ∃ o : 𝓞 E, (o : E) = S.hT y x) ∧ x ∈ spanE S M := by
  unfold dualIn dualInH
  rw [Submodule.mem_inf, dualBasic_mem_dual]
  simp only [Submodule.mem_one]
  rfl

theorem g_dualIn_anti {A B : Submodule (𝓞 E) S.V} (hBA : B ≤ A) (hs : spanE S A = spanE S B) :
    dualIn S A ≤ dualIn S B := by
  intro x hx
  obtain ⟨h1, h2⟩ := g_mem_dualIn.1 hx
  exact g_mem_dualIn.2 ⟨fun y hy => h1 y (hBA hy), hs ▸ h2⟩

theorem g_card_quot_le {M X : Type} [AddCommGroup M] [Module (𝓞 E) M] (N : Submodule (𝓞 E) M) [Finite X]
    (f : M → X) (h : ∀ x x', f x = f x' → x - x' ∈ N) : Nat.card (M ⧸ N) ≤ Nat.card X := by
  apply Nat.card_le_card_of_injective (fun q : M ⧸ N => f (Quotient.out q))
  intro q q' hq
  have := h _ _ hq
  rw [← Submodule.Quotient.eq] at this
  have e1 : (Submodule.Quotient.mk (Quotient.out q) : M ⧸ N) = q := Quotient.out_eq q
  have e2 : (Submodule.Quotient.mk (Quotient.out q') : M ⧸ N) = q' := Quotient.out_eq q'
  rw [← e1, ← e2, this]

theorem g_hT_smul_right (x y : S.V) (c : 𝓞 E) : S.hT x (c • y) = (c : E) * S.hT x y := by
  rw [← IsScalarTower.algebraMap_smul E c y, map_smul, smul_eq_mul]

theorem g_hT_smul_left (x y : S.V) (c : 𝓞 E) : S.hT (c • x) y = star (c : E) * S.hT x y := by
  rw [← IsScalarTower.algebraMap_smul E c x, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]; rfl

theorem g_hT_swap_int (hst : g_StarInt E) {x y : S.V} (h : ∃ o : 𝓞 E, (o : E) = S.hT x y) :
    ∃ o : 𝓞 E, (o : E) = S.hT y x := by
  obtain ⟨o, ho⟩ := h
  obtain ⟨o', ho'⟩ := hst o
  refine ⟨o', ?_⟩
  rw [ho', ho]
  exact S.herm.eq x y

theorem g_dual_step (hst : g_StarInt E) {A B' : Submodule (𝓞 E) S.V}
    (hs : spanE S A = spanE S B') {P₀ : Ideal (𝓞 E)} (hP : P₀.IsMaximal)
    (e : (A ⧸ B'.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ P₀)) [Finite (𝓞 E ⧸ P₀)] :
    g_idx (dualIn S B') (dualIn S A) ≤ Nat.card (𝓞 E ⧸ P₀) := by
  obtain ⟨a, haP, ha0, j, hjP, hj⟩ := g_locPrincipal hP
  obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective _ (e.symm 1)
  have hey₀ : e (Submodule.Quotient.mk y₀) = 1 := by rw [hy₀, LinearEquiv.apply_symm_apply]
  have hdec : ∀ y ∈ A, ∃ c : 𝓞 E, y - c • (y₀ : S.V) ∈ B' := by
    intro y hy
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk ⟨y, hy⟩))
    refine ⟨c, ?_⟩
    have h0 : (Submodule.Quotient.mk (⟨y, hy⟩ - c • y₀) : A ⧸ B'.comap A.subtype) = 0 := by
      apply e.injective
      rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, map_sub, map_smul, hey₀, ← hc, map_zero,
        sub_eq_zero]
      show Ideal.Quotient.mk P₀ c = Ideal.Quotient.mk P₀ (c * 1)
      rw [mul_one]
    rw [Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  have hint : ∀ x ∈ dualIn S B', ∀ p ∈ P₀, ∃ o : 𝓞 E, (o : E) = S.hT x (p • (y₀ : S.V)) := by
    intro x hx p hp
    exact g_hT_swap_int hst ((g_mem_dualIn.1 hx).1 _ (g_simple_kill e hp y₀.2))
  let f : ↥(dualIn S B') → 𝓞 E ⧸ P₀ := fun x => Ideal.Quotient.mk P₀ (Classical.choose (hint x x.2 a haP))
  refine g_card_quot_le _ f ?_
  intro x x' hxx
  have ho := Classical.choose_spec (hint x x.2 a haP)
  have ho' := Classical.choose_spec (hint x' x'.2 a haP)
  have hmem : Classical.choose (hint x x.2 a haP) - Classical.choose (hint x' x'.2 a haP) ∈ P₀ :=
    Ideal.Quotient.eq.1 hxx
  set o := Classical.choose (hint x x.2 a haP)
  set o' := Classical.choose (hint x' x'.2 a haP)
  have hw : (x : S.V) - x' ∈ dualIn S B' := sub_mem x.2 x'.2
  set w : S.V := (x : S.V) - x' with hwdef
  have haE : (a : E) ≠ 0 := by
    simpa using (map_ne_zero_iff (algebraMap (𝓞 E) E) (IsFractionRing.injective (𝓞 E) E)).2 ha0
  have h1 : (a : E) * S.hT w y₀ = ((o - o' : 𝓞 E) : E) := by
    rw [← g_hT_smul_right, hwdef, map_sub, LinearMap.sub_apply, ← ho, ← ho']
    simp
  obtain ⟨o2, ho2⟩ := hj _ hmem
  have h2 : (j : E) * S.hT w y₀ = (o2 : E) := by
    have : (a : E) * ((j : E) * S.hT w y₀) = (a : E) * (o2 : E) := by
      have h3 : (j : E) * ((o - o' : 𝓞 E) : E) = (a : E) * (o2 : E) := by
        exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) ho2
      rw [← h1] at h3
      linear_combination h3
    exact mul_left_cancel₀ haE this
  obtain ⟨u, p, hp, hup⟩ := hP.exists_inv hjP
  obtain ⟨o3, ho3⟩ := hint w hw p hp
  rw [g_hT_smul_right] at ho3
  have h4 : ∃ o4 : 𝓞 E, (o4 : E) = S.hT w y₀ := by
    refine ⟨u * o2 + o3, ?_⟩
    have h5 : (u : E) * (j : E) + (p : E) = 1 := by
      exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hup
    have h6 : ((u * o2 + o3 : 𝓞 E) : E) = (u : E) * (o2 : E) + (o3 : E) := by push_cast; rfl
    rw [h6, ho3, ← h2]
    linear_combination (S.hT w y₀) * h5
  obtain ⟨o5, ho5⟩ := g_hT_swap_int hst h4
  show ((x - x' : ↥(dualIn S B')) : S.V) ∈ dualIn S A
  rw [Submodule.coe_sub, ← hwdef]
  refine g_mem_dualIn.2 ⟨?_, hs ▸ (g_mem_dualIn.1 hw).2⟩
  intro y hy
  obtain ⟨c, hc⟩ := hdec y hy
  obtain ⟨ob, hob⟩ := (g_mem_dualIn.1 hw).1 _ hc
  obtain ⟨c', hc'⟩ := hst c
  refine ⟨ob + c' * o5, ?_⟩
  have : y = (y - c • (y₀ : S.V)) + c • (y₀ : S.V) := by abel
  rw [this, map_add, LinearMap.add_apply, g_hT_smul_left, ← hob, ← ho5, ← hc']
  simp

theorem g_dual_le (hst : g_StarInt E) : ∀ A B : Submodule (𝓞 E) S.V, A.FG → g_Comm A B → B ≤ A →
    g_idx (dualIn S B) (dualIn S A) ≤ g_idx A B := by
  apply g_chain_ind (fun A B => g_idx (dualIn S B) (dualIn S A) ≤ g_idx A B)
  · intro A
    have h1 : ∀ X : Submodule (𝓞 E) S.V, g_idx X X = 1 := by
      intro X
      unfold g_idx
      rw [Submodule.comap_subtype_self]
      exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩
    show g_idx (dualIn S A) (dualIn S A) ≤ g_idx A A
    rw [h1, h1]
  · intro A B' B hA hC hBB' hB'A P₀ hP₀ e ih
    have s1 : spanE S A = spanE S B' := g_span_eq (g_Comm_mono hC le_rfl hBB') hB'A
    have s2 : spanE S B' = spanE S B := g_span_eq (g_Comm_mono hC hB'A le_rfl) hBB'
    have hf : Finite (A ⧸ B'.comap A.subtype) := g_fin hA (g_Comm_mono hC le_rfl hBB')
    have hf' : Finite (𝓞 E ⧸ P₀) := Finite.of_equiv _ e.toEquiv
    rw [← g_idx_mul hBB' hB'A, ← g_idx_mul (g_dualIn_anti hB'A s1) (g_dualIn_anti hBB' s2), mul_comm]
    refine Nat.mul_le_mul ih ?_
    have hc : g_idx A B' = Nat.card (𝓞 E ⧸ P₀) := Nat.card_congr e.toEquiv
    rw [hc]
    exact g_dual_step hst s1 hP₀ e

end Idx

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section Tr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

def g_hU (S : HSpace E) (U : Submodule E S.V) : U →ₗ⋆[E] U →ₗ[E] E := S.hT.domRestrict₁₂ U U

theorem g_hU_symm (U : Submodule E S.V) : (g_hU S U).IsSymm := ⟨fun x y => S.herm.eq x y⟩

theorem g_hU_nondeg (U : Submodule E S.V) (hU : U ⊓ orth S U = ⊥) : (g_hU S U).Nondegenerate := by
  have key : ∀ y : U, (∀ x : U, S.hT x y = 0) → y = 0 := by
    intro y hy
    have : (y : S.V) ∈ U ⊓ orth S U := ⟨y.2, p_mem_orth.2 fun x hx => hy ⟨x, hx⟩⟩
    rw [hU, Submodule.mem_bot] at this
    exact Subtype.ext this
  refine ⟨?_, ?_⟩
  · intro x hx
    exact key x fun y => p_symm_zero S (hx y)
  · intro y hy
    exact key y hy

def g_iota (U : Submodule E S.V) : U →ₗ[𝓞 E] S.V := U.subtype.restrictScalars (𝓞 E)

theorem g_iota_inj (U : Submodule E S.V) : Function.Injective (g_iota U) := Subtype.val_injective

theorem g_map_comap {U : Submodule E S.V} {M : Submodule (𝓞 E) S.V} (h : M ≤ toO S U) :
    (M.comap (g_iota U)).map (g_iota U) = M := by
  rw [Submodule.map_comap_eq, inf_eq_right]
  intro x hx
  exact ⟨⟨x, h hx⟩, rfl⟩

theorem g_span_map (U : Submodule E S.V) (N : Submodule (𝓞 E) U) :
    spanE S (N.map (g_iota U)) = (Submodule.span E (N : Set U)).map U.subtype := by
  unfold spanE
  rw [Submodule.map_span]
  rfl

theorem g_le_span (M : Submodule (𝓞 E) S.V) : M ≤ toO S (spanE S M) := fun _ hx => Submodule.subset_span hx

theorem g_comap_lattice {U : Submodule E S.V} {M : Submodule (𝓞 E) S.V} (hM : M.FG) (hs : spanE S M = U) :
    Submodule.IsLattice E (M.comap (g_iota U)) := by
  have hle : M ≤ toO S U := hs ▸ g_le_span M
  refine ⟨?_, ?_⟩
  · apply Submodule.fg_of_fg_map_injective (g_iota U) (g_iota_inj U)
    rw [g_map_comap hle]; exact hM
  · apply Submodule.map_injective_of_injective U.injective_subtype
    rw [← g_span_map, g_map_comap hle, hs, Submodule.map_top, Submodule.range_subtype]

theorem g_dualIn_eq {U : Submodule E S.V} {M : Submodule (𝓞 E) S.V} (hs : spanE S M = U) :
    dualIn S M = (dual (g_hU S U) (M.comap (g_iota U))).map (g_iota U) := by
  have hle : M ≤ toO S U := hs ▸ g_le_span M
  ext x
  unfold dualIn dualInH
  rw [Submodule.mem_inf, dualBasic_mem_dual]
  constructor
  · rintro ⟨h1, h2⟩
    have hxU : x ∈ U := by rw [← hs]; exact h2
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, dualBasic_mem_dual]
    intro y hy
    exact h1 y hy
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, dualBasic_mem_dual] at hu
    refine ⟨fun y hy => hu ⟨y, hle hy⟩ hy, ?_⟩
    show (u : S.V) ∈ spanE S M
    rw [hs]; exact u.2

end Tr

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def g_DetIndexG (S : HSpace E) : Prop :=
  ∀ M₁ M₂ : Submodule (𝓞 E) S.V, M₂ ≤ M₁ → M₁.FG → spanE S M₁ = spanE S M₂ →
    spanE S M₁ ⊓ orth S (spanE S M₁) = ⊥ →
    latDet S M₂ = latDet S M₁ * (Nat.card (M₁ ⧸ M₂.comap M₁.subtype) : ℝ)

variable (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (g : ℕ)

theorem g_fg_of_le (hΛ : Submodule.IsLattice E Λ) {M : Submodule (𝓞 E) S.V} (h : M ≤ Λ) : M.FG := by
  have h1 : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ.fg
  have h2 : IsNoetherian (𝓞 E) Λ := isNoetherian_of_isNoetherianRing_of_finite (𝓞 E) Λ
  exact (isNoetherian_submodule.1 h2) M h

theorem g_UU_le_BLat (hz : IsLift Λ F) (hz' : IsLift Λ F') : UU Λ F F' ≤ BLat Λ F F' := by
  refine le_inf ?_ ?_
  · unfold UU
    refine sup_le (sup_le (sup_le inf_le_left ?_) inf_le_left) ?_
    · rw [Submodule.span_singleton_le_iff_mem, hz.2]; exact hz.1
    · rw [Submodule.span_singleton_le_iff_mem, hz'.2]; exact hz'.1
  · intro x hx
    exact Submodule.subset_span hx

theorem g_span_BLat (hz : IsLift Λ F) (hz' : IsLift Λ F') :
    spanE S (BLat Λ F F') = UUE Λ F F' := by
  apply le_antisymm
  · unfold spanE
    rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · exact Submodule.span_mono (g_UU_le_BLat Λ F F' hz hz')

theorem g_Thp_le_La (hX : Xsp F ≤ UUE Λ F F') (hX' : Xsp F' ≤ UUE Λ F F')
    (hzU : F.fl.z ∈ UUE Λ F F') (hzU' : F'.fl.z ∈ UUE Λ F F') : Thp Λ F F' ≤ La Λ g F F' := by
  intro x hx
  have hoX : x ∈ orth S (Xsp F) := p_mem_orth.2 fun v hv => p_mem_orth.1 hx.2 v (hX hv)
  have hoX' : x ∈ orth S (Xsp F') := p_mem_orth.2 fun v hv => p_mem_orth.1 hx.2 v (hX' hv)
  apply Submodule.subset_span
  refine ⟨hx.2, ⟨⟨Submodule.mem_sup_left ⟨hx.1, hoX⟩, hoX⟩, ?_⟩,
    ⟨⟨Submodule.mem_sup_left ⟨hx.1, hoX'⟩, hoX'⟩, ?_⟩,
    x, ⟨hx.1, hoX⟩, by simp, x, ⟨hx.1, hoX'⟩, by simp, by simp⟩
  · exact LinearMap.mem_ker.2 (p_mem_orth.1 hx.2 _ hzU)
  · exact LinearMap.mem_ker.2 (p_mem_orth.1 hx.2 _ hzU')

theorem g_span_La (hΛ : Submodule.IsLattice E Λ) (hle : Thp Λ F F' ≤ La Λ g F F') :
    spanE S (La Λ g F F') = Hp Λ F F' ∧ spanE S (Thp Λ F F') = Hp Λ F F' := by
  have h2 : spanE S (Thp Λ F F') = Hp Λ F F' := a_span_inf Λ hΛ _
  refine ⟨le_antisymm ?_ ?_, h2⟩
  · unfold spanE
    rw [Submodule.span_le]
    intro x hx
    exact (m_La_mem Λ F F' g hx).1
  · rw [← h2]; exact Submodule.span_mono hle

theorem g_orth_nondeg (U : Submodule E S.V) (hc : IsCompl U (orth S U)) :
    orth S U ⊓ orth S (orth S U) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  apply S.nondeg.2 x
  intro v
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ (Submodule.mem_top : v ∈ ⊤))
  rw [map_add, LinearMap.add_apply, p_mem_orth.1 hx.1 u hu, p_mem_orth.1 hx.2 w hw, add_zero]

theorem lemma_one_det_general_lattice (hΛ : Submodule.IsLattice E Λ) (hg : 0 < g) (hz : IsLift Λ F) (hz' : IsLift Λ F')
    (hG : Gval F F' ≠ 0) (hDI : g_DetIndexG S)
    (hglue : latDet S (Λ ⊓ toO S (UUE Λ F F')) = latDet S (Λ ⊓ toO S (orth S (UUE Λ F F')))) :
    latDet S (La Λ g F F') =
      NG Λ F F' / ((Nat.card (BQ Λ F F') : ℝ) * (iIdx Λ g F F' : ℝ)) := by
  have hU : HU Λ F F' := a_HU Λ hΛ F F' hz.2 hz'.2
  have hU' : UUE Λ F F' = U2 F F' := hU
  obtain ⟨hX, hX'⟩ := a_X_le hU
  have hzU : F.fl.z ∈ UUE Λ F F' := by
    rw [hU']; exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hzU' : F'.fl.z ∈ UUE Λ F F' := by
    rw [hU']; exact Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hfinB : Finite (BQ Λ F F') := m_BQ_finite Λ F F' hΛ
  have hle : Thp Λ F F' ≤ La Λ g F F' := g_Thp_le_La Λ F F' g hX hX' hzU hzU'
  obtain ⟨φ, hφ, -⟩ := lemma_one_quotient_embedding (g := g) hg hz hz' (a_disj (a_HInd F F' hG)) hX hX'
  have hfinQ : Finite (La Λ g F F' ⧸ (Thp Λ F F').comap (La Λ g F F').subtype) :=
    Finite.of_injective φ hφ

  have hThfg : (Thp Λ F F').FG := g_fg_of_le Λ hΛ inf_le_left
  have hLafg : (La Λ g F F').FG := by
    have e : ((Thp Λ F F').comap (La Λ g F F').subtype) ≃ₗ[𝓞 E] Thp Λ F F' :=
      Submodule.comapSubtypeEquivOfLe hle
    have h1 : Module.Finite (𝓞 E) (Thp Λ F F') := Module.Finite.iff_fg.2 hThfg
    have h2 : Module.Finite (𝓞 E) ((Thp Λ F F').comap (La Λ g F F').subtype) :=
      Module.Finite.equiv e.symm
    have h3 : Module.Finite (𝓞 E) (La Λ g F F' ⧸ (Thp Λ F F').comap (La Λ g F F').subtype) :=
      Module.Finite.of_finite
    have h4 : Module.Finite (𝓞 E) (La Λ g F F') :=
      Module.Finite.of_submodule_quotient ((Thp Λ F F').comap (La Λ g F F').subtype)
    exact Module.Finite.iff_fg.1 h4
  have hc : IsCompl (UUE Λ F F') (orth S (UUE Λ F F')) := by rw [hU']; exact double_span_is_compl_orth F F' hG

  have e1 : NG Λ F F' = latDet S (BLat Λ F F') * (Nat.card (BQ Λ F F') : ℝ) := by
    refine hDI (BLat Λ F F') (UU Λ F F') (g_UU_le_BLat Λ F F' hz hz') (g_fg_of_le Λ hΛ inf_le_left) ?_ ?_
    · rw [g_span_BLat Λ F F' hz hz']; rfl
    · rw [g_span_BLat Λ F F' hz hz']; exact hc.inf_eq_bot
  obtain ⟨s1, s2⟩ := g_span_La Λ F F' g hΛ hle
  have e2 : latDet S (Thp Λ F F') = latDet S (La Λ g F F') * (iIdx Λ g F F' : ℝ) := by
    refine hDI (La Λ g F F') (Thp Λ F F') hle hLafg (by rw [s1, s2]) ?_
    rw [s1]; exact g_orth_nondeg _ hc
  have e3 : latDet S (BLat Λ F F') = latDet S (Thp Λ F F') := hglue
  have hB : 0 < (Nat.card (BQ Λ F F') : ℝ) := by exact_mod_cast Nat.card_pos
  have hi : 0 < (iIdx Λ g F F' : ℝ) := by
    have : 0 < Nat.card (La Λ g F F' ⧸ (Thp Λ F F').comap (La Λ g F F').subtype) := Nat.card_pos
    exact_mod_cast this
  rw [e1, e3, e2]
  field_simp

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def g_DetIndex (D : D7) : Prop := g_DetIndexG (hS D)

def g_GlueDet (D : D7) : Prop :=
  ∀ Λ : Submodule (𝓞 D.host.E) (hS D).V, Submodule.IsLattice D.host.E Λ →
    Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ → ∀ U : Submodule D.host.E (hS D).V, U ⊓ orth (hS D) U = ⊥ →
      latDet (hS D) (Λ ⊓ toO (hS D) U) = latDet (hS D) (Λ ⊓ toO (hS D) (orth (hS D) U))

theorem lattice_det_eq_index_quotient (D : D7) (h1 : g_GlueDet D) (hDI : g_DetIndex D)
    (Λ : Submodule (𝓞 D.host.E) (hS D).V) {T T' : ℕ}
    (F : LFlag (hS D) D.R.rS ((T : ℕ) : D.host.E)) (F' : LFlag (hS D) D.R.rS ((T' : ℕ) : D.host.E))
    (hF : FixedHyp D Λ F) (hg : 0 < gS D) (hT : IsTerm Λ (gS D) F F') :
    latDet (hS D) (La Λ (gS D) F F') =
      NG Λ F F' / ((Nat.card (BQ Λ F F') : ℝ) * (iIdx Λ (gS D) F F' : ℝ)) := by
  have hU' : UUE Λ F F' = U2 F F' := a_HU Λ hF.1 F F' hF.2.2.1.2 hT.1.2
  refine lemma_one_det_general_lattice Λ F F' (gS D) hF.1 hg hF.2.2.1 hT.1 hT.2.2 hDI ?_
  refine h1 Λ hF.1 hF.2.1 (UUE Λ F F') ?_
  rw [hU']; exact a_HNd F F' hT.2.2

end D7

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section Fin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem g_dual_facts (hst : g_StarInt E) {U : Submodule E S.V} (hU : U ⊓ orth S U = ⊥)
    {M : Submodule (𝓞 E) S.V} (hM : M.FG) (hs : spanE S M = U) :
    (dualIn S M).FG ∧ spanE S (dualIn S M) = U ∧ dualIn S (dualIn S M) = M := by
  have hst' : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
    intro r
    obtain ⟨o', ho'⟩ := hst r
    exact ⟨o', ho'⟩
  obtain ⟨hlat, hdd, -⟩ := Formalism.HermitianLatticesTheory.dualLattice (𝓞 E) E U (g_hU S U) (g_hU_symm U) (g_hU_nondeg U hU) hst'
    (M.comap (g_iota U)) (g_comap_lattice hM hs)
  have hle : M ≤ toO S U := hs ▸ g_le_span M
  have e1 := g_dualIn_eq (S := S) hs
  have s1 : spanE S (dualIn S M) = U := by
    rw [e1, g_span_map, hlat.span_eq_top, Submodule.map_top, Submodule.range_subtype]
  refine ⟨?_, s1, ?_⟩
  · rw [e1]; exact hlat.fg.map _
  · rw [g_dualIn_eq (S := S) s1, e1, Submodule.comap_map_eq_of_injective (g_iota_inj U), hdd, g_map_comap hle]

theorem g_detIndexG (hst : g_StarInt E) : g_DetIndexG S := by
  intro M₁ M₂ hle hfg hspan hnd
  have hfg2 : M₂.FG := g_fg_le hfg hle
  obtain ⟨f1, s1, d1⟩ := g_dual_facts hst hnd hfg rfl
  obtain ⟨f2, s2, d2⟩ := g_dual_facts hst hnd hfg2 hspan.symm
  have cM : g_Comm M₁ M₂ := g_Comm_of_span hfg (le_of_eq hspan)
  have hanti : dualIn S M₁ ≤ dualIn S M₂ := g_dualIn_anti hle hspan
  have le1 : g_idx (dualIn S M₂) (dualIn S M₁) ≤ g_idx M₁ M₂ := g_dual_le hst M₁ M₂ hfg cM hle
  have le2 := g_dual_le hst (dualIn S M₂) (dualIn S M₁) f2 (g_Comm_of_span f2 (by rw [s2, s1])) hanti
  rw [d1, d2] at le2
  have heq : g_idx (dualIn S M₂) (dualIn S M₁) = g_idx M₁ M₂ := le_antisymm le1 le2
  have hD1 : M₂ ⊓ dualIn S M₁ ≤ dualIn S M₁ := inf_le_right
  have hD2 : M₂ ⊓ dualIn S M₁ ≤ M₂ := inf_le_left
  have c1 : g_Comm (dualIn S M₂) (M₂ ⊓ dualIn S M₁) :=
    g_Comm_inf (g_Comm_of_span f2 (by rw [s2, hspan])) (g_Comm_of_span f2 (by rw [s2, s1]))
  have c2 : g_Comm M₁ (M₂ ⊓ dualIn S M₁) :=
    g_Comm_inf cM (g_Comm_of_span hfg (by rw [s1]))
  have g2 := g_genIdx_via f2 hfg2 (hD1.trans hanti) hD2 c1 (g_Comm_mono c2 hle le_rfl)
  have g1 := g_genIdx_via f1 hfg hD1 (hD2.trans hle) (g_Comm_mono c1 hanti le_rfl) c2
  have m1 := g_idx_mul hD1 hanti
  have m2 := g_idx_mul hD2 hle
  have hn : 0 < g_idx M₁ M₂ := g_idx_pos hfg cM
  have hb : 0 < g_idx M₂ (M₂ ⊓ dualIn S M₁) := g_idx_pos hfg2 (g_Comm_mono c2 hle le_rfl)
  have hn' : (0 : ℝ) < (g_idx M₁ M₂ : ℝ) := by exact_mod_cast hn
  have hb' : (0 : ℝ) < (g_idx M₂ (M₂ ⊓ dualIn S M₁) : ℝ) := by exact_mod_cast hb
  have key : genIdx S (dualIn S M₂) M₂ = genIdx S (dualIn S M₁) M₁ * (g_idx M₁ M₂ : ℝ) ^ 2 := by
    rw [g2, g1, ← m1, ← m2, heq]
    push_cast
    field_simp
  show Real.sqrt (genIdx S (dualIn S M₂) M₂) = Real.sqrt (genIdx S (dualIn S M₁) M₁) * (g_idx M₁ M₂ : ℝ)
  rw [key, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hn'.le]

theorem g_starInt : g_StarInt E := by
  intro o
  obtain ⟨o', ho'⟩ := i_star_int o
  exact ⟨o', ho'⟩

end Fin

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem g_detIndex (D : D7) : g_DetIndex D := g_detIndexG g_starInt

theorem g_glueDet (D : D7) : g_GlueDet D :=
  fun Λ hΛ hu U hU => (i_gluing Λ hΛ hu U hU).2.2.2

theorem g_gS_pos (D : D7) : 0 < gS D :=
  Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem lemma_one_det_eq_index_quotient (D : D7) (Λ : Submodule (𝓞 D.host.E) (hS D).V) {T T' : ℕ}
    (F : LFlag (hS D) D.R.rS ((T : ℕ) : D.host.E)) (F' : LFlag (hS D) D.R.rS ((T' : ℕ) : D.host.E))
    (hF : FixedHyp D Λ F) (hT : IsTerm Λ (gS D) F F') :
    latDet (hS D) (La Λ (gS D) F F') =
      NG Λ F F' / ((Nat.card (BQ Λ F F') : ℝ) * (iIdx Λ (gS D) F F' : ℝ)) :=
  lattice_det_eq_index_quotient D (g_glueDet D) (g_detIndex D) Λ F F' hF (g_gS_pos D) hT

end D7

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section H1

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem h_quot_equiv {A B A' B' : Submodule (𝓞 E) S.V} (hle : A ≤ A') (hB : B ≤ B')
    (hsurj : A' ≤ A ⊔ B') (hker : A ⊓ B' ≤ B) :
    Nonempty ((A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (A' ⧸ B'.comap A'.subtype)) := by
  let f : (A ⧸ B.comap A.subtype) →ₗ[𝓞 E] (A' ⧸ B'.comap A'.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hle) (fun x hx => hB hx)
  refine ⟨LinearEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [Submodule.mkQ_apply] at hq ⊢
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact hker ⟨x.2, hq⟩
  · intro q
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hsurj y.2)
    refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
    rw [Submodule.mapQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show a - (y : S.V) ∈ B'
    have : a - (y : S.V) = -b := by rw [← e]; abel
    rw [this]; exact neg_mem hb

theorem h_idx_congr {A B A' B' : Submodule (𝓞 E) S.V} (hle : A ≤ A') (hB : B ≤ B')
    (hsurj : A' ≤ A ⊔ B') (hker : A ⊓ B' ≤ B) : g_idx A B = g_idx A' B' := by
  obtain ⟨e⟩ := h_quot_equiv hle hB hsurj hker
  exact Nat.card_congr e.toEquiv

theorem h_span_toO (X : Submodule E S.V) : spanE S (toO S X) = X := by
  unfold spanE
  exact Submodule.span_eq X

theorem h_span_le {L : Submodule (𝓞 E) S.V} {U : Submodule E S.V} (h : L ≤ toO S U) : spanE S L ≤ U := by
  unfold spanE
  rw [Submodule.span_le]
  exact h

theorem h_span_sup (A B : Submodule (𝓞 E) S.V) : spanE S (A ⊔ B) = spanE S A ⊔ spanE S B :=
  a_span_sup A B

theorem h_sat_cancel {U X : Submodule E S.V} (hUX : U ⊓ X = ⊥) {a b ξ η : S.V} (ha : a ∈ U) (hb : b ∈ U)
    (hξ : ξ ∈ X) (hη : η ∈ X) (e : a + ξ = b + η) : a = b := by
  have h1 : a - b ∈ U ⊓ X := by
    refine ⟨sub_mem ha hb, ?_⟩
    have : a - b = η - ξ := by
      have : a = b + η - ξ := by rw [← e]; abel
      rw [this]; abel
    rw [this]; exact sub_mem hη hξ
  rw [hUX, Submodule.mem_bot] at h1
  exact sub_eq_zero.1 h1

theorem h_inf_sat {U X : Submodule E S.V} (hUX : U ⊓ X = ⊥) {A B : Submodule (𝓞 E) S.V}
    (hA : A ≤ toO S U) (hB : B ≤ toO S U) :
    (A ⊔ toO S X) ⊓ (B ⊔ toO S X) = (A ⊓ B) ⊔ toO S X := by
  apply le_antisymm
  · rintro x ⟨h1, h2⟩
    obtain ⟨a, ha, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 h1
    obtain ⟨b, hb, η, hη, e⟩ := Submodule.mem_sup.1 h2
    have hab : a = b := h_sat_cancel hUX (hA ha) (hB hb) hξ hη e.symm
    exact Submodule.add_mem_sup ⟨ha, hab ▸ hb⟩ hξ
  · exact sup_le (le_inf (le_sup_of_le_left inf_le_left) (le_sup_of_le_left inf_le_right))
      (le_inf le_sup_right le_sup_right)

theorem h_locLen_sat (p : Ideal (𝓞 E)) [p.IsPrime] {U X : Submodule E S.V} (hUX : U ⊓ X = ⊥)
    {A C : Submodule (𝓞 E) S.V} (hA : A ≤ toO S U) (hC : C ≤ A) :
    locLen p (A ⊔ toO S X) (C ⊔ toO S X) = locLen p A C := by
  obtain ⟨e⟩ := h_quot_equiv (A := A) (B := C) (A' := A ⊔ toO S X) (B' := C ⊔ toO S X) le_sup_left
    le_sup_left (sup_le le_sup_left (le_sup_of_le_right le_sup_right)) (by
      rintro x ⟨h1, h2⟩
      obtain ⟨c, hc, ξ, hξ, e⟩ := Submodule.mem_sup.1 h2
      have : x = c := h_sat_cancel hUX (hA h1) (hA (hC hc)) (zero_mem X) hξ (by rw [add_zero, e])
      rw [this]; exact hc)
  exact (i_locLen_congr p e).symm

theorem h_lidx_sat (p : Ideal (𝓞 E)) [p.IsPrime] {U X : Submodule E S.V} (hUX : U ⊓ X = ⊥)
    {A B : Submodule (𝓞 E) S.V} (hA : A ≤ toO S U) (hB : B ≤ toO S U) :
    lidx p (A ⊔ toO S X) (B ⊔ toO S X) = lidx p A B := by
  unfold lidx
  rw [h_inf_sat hUX hA hB, h_locLen_sat p hUX hA inf_le_left, h_locLen_sat p hUX hB inf_le_right]

theorem h_dualIn_sat {X : Submodule E S.V} (hiso : X ≤ orth S X) {L : Submodule (𝓞 E) S.V}
    (hL : L ≤ toO S (orth S X)) : dualIn S (L ⊔ toO S X) = dualIn S L ⊔ toO S X := by
  have hsp : spanE S L ≤ orth S X := h_span_le hL
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := g_mem_dualIn.1 hx
    rw [h_span_sup, h_span_toO] at h2
    obtain ⟨u, hu, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 h2
    refine Submodule.add_mem_sup (g_mem_dualIn.2 ⟨fun y hy => ?_, hu⟩) hξ
    obtain ⟨o, ho⟩ := h1 y (Submodule.mem_sup_left hy)
    refine ⟨o, ?_⟩
    have h0 : S.hT y ξ = 0 := c_symm0 (c_mem_orth.1 (hL hy) ξ hξ)
    rw [ho, map_add, h0, add_zero]
  · refine sup_le ?_ ?_
    · intro d hd
      obtain ⟨h1, h2⟩ := g_mem_dualIn.1 hd
      refine g_mem_dualIn.2 ⟨fun y hy => ?_, ?_⟩
      · obtain ⟨l, hl, η, hη, rfl⟩ := Submodule.mem_sup.1 hy
        obtain ⟨o, ho⟩ := h1 l hl
        refine ⟨o, ?_⟩
        have h0 : S.hT η d = 0 := c_mem_orth.1 (hsp h2) η hη
        rw [ho, map_add, LinearMap.add_apply, h0, add_zero]
      · rw [h_span_sup]; exact Submodule.mem_sup_left h2
    · intro ξ hξ
      refine g_mem_dualIn.2 ⟨fun y hy => ?_, ?_⟩
      · obtain ⟨l, hl, η, hη, rfl⟩ := Submodule.mem_sup.1 hy
        refine ⟨0, ?_⟩
        have h0 : S.hT η ξ = 0 := c_mem_orth.1 (hiso hξ) η hη
        have h1 : S.hT l ξ = 0 := c_symm0 (c_mem_orth.1 (hL hl) ξ hξ)
        rw [map_add, LinearMap.add_apply, h0, h1, add_zero]
        simp
      · rw [h_span_sup, h_span_toO]; exact Submodule.mem_sup_right hξ

theorem h_latDet_sat {X : Submodule E S.V} (hiso : X ≤ orth S X) {L : Submodule (𝓞 E) S.V}
    (hL : L ≤ toO S (orth S X)) (hd : spanE S L ⊓ X = ⊥) :
    latDet S (L ⊔ toO S X) = latDet S L := by
  show Real.sqrt (genIdx S (dualIn S (L ⊔ toO S X)) (L ⊔ toO S X)) = Real.sqrt (genIdx S (dualIn S L) L)
  rw [h_dualIn_sat hiso hL]
  congr 1
  unfold genIdx genIdxH
  apply finprod_congr
  intro P
  have := P.isPrime
  rw [h_lidx_sat P.asIdeal hd (fun x hx => (g_mem_dualIn.1 hx).2) (g_le_span L)]

theorem h_latDet_shift {X : Submodule E S.V} (hiso : X ≤ orth S X) {L L' : Submodule (𝓞 E) S.V}
    (hL : L ≤ toO S (orth S X)) (hd : spanE S L ⊓ X = ⊥)
    (hL' : L' ≤ toO S (orth S X)) (hd' : spanE S L' ⊓ X = ⊥)
    (h : L ⊔ toO S X = L' ⊔ toO S X) : latDet S L = latDet S L' := by
  rw [← h_latDet_sat hiso hL hd, h, h_latDet_sat hiso hL' hd']

theorem h_genIdx_pos (A B : Submodule (𝓞 E) S.V) : 0 < genIdx S A B := by
  unfold genIdx genIdxH
  apply finprod_induction (fun x : ℝ => 0 < x) zero_lt_one (fun _ _ => mul_pos)
  intro P
  have hN : 0 < ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) := by
    have : Ideal.absNorm P.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  exact zpow_pos hN _

theorem h_latDet_pos (M : Submodule (𝓞 E) S.V) : 0 < latDet S M :=
  Real.sqrt_pos.2 (h_genIdx_pos _ _)

end H1

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section H2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem h_idx_sup {U₁ U₂ : Submodule E S.V} (hd : U₁ ⊓ U₂ = ⊥) {A A' B B' : Submodule (𝓞 E) S.V}
    (hA : A ≤ toO S U₁) (hA' : A' ≤ A) (hB : B ≤ toO S U₂) (hB' : B' ≤ B) :
    g_idx (A ⊔ B) (A' ⊔ B') = g_idx A A' * g_idx B B' := by
  have hd' : U₂ ⊓ U₁ = ⊥ := by rw [inf_comm]; exact hd
  have e1 : g_idx A A' = g_idx (A ⊔ B') (A' ⊔ B') :=
    h_idx_congr le_sup_left le_sup_left (sup_le le_sup_left (le_sup_of_le_right le_sup_right)) (by
      rintro x ⟨h1, h2⟩
      obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 h2
      have : x = a := h_sat_cancel hd (hA h1) (hA (hA' ha)) (zero_mem U₂) (hB (hB' hb))
        (by rw [add_zero, e])
      rw [this]; exact ha)
  have e2 : g_idx B B' = g_idx (A ⊔ B) (A ⊔ B') :=
    h_idx_congr le_sup_right le_sup_right (sup_le (le_sup_of_le_right le_sup_left) le_sup_left) (by
      rintro x ⟨h1, h2⟩
      obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 h2
      have : x = b := h_sat_cancel hd' (hB h1) (hB (hB' hb)) (zero_mem U₁) (hA ha)
        (by rw [add_zero, ← e, add_comm])
      rw [this]; exact hb)
  rw [e1, e2]
  exact (g_idx_mul (sup_le_sup_right hA' B') (sup_le_sup_left hB' A)).symm

theorem h_dualIn_sup {U₁ U₂ : Submodule E S.V} (ho : ∀ x ∈ U₁, ∀ y ∈ U₂, S.hT x y = 0)
    {M N : Submodule (𝓞 E) S.V} (hM : spanE S M = U₁) (hN : spanE S N = U₂) :
    dualIn S (M ⊔ N) = dualIn S M ⊔ dualIn S N := by
  have hMU : M ≤ toO S U₁ := hM ▸ g_le_span M
  have hNU : N ≤ toO S U₂ := hN ▸ g_le_span N
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := g_mem_dualIn.1 hx
    rw [h_span_sup, hM, hN] at h2
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h2
    refine Submodule.add_mem_sup (g_mem_dualIn.2 ⟨fun y hy => ?_, hM ▸ ha⟩)
      (g_mem_dualIn.2 ⟨fun y hy => ?_, hN ▸ hb⟩)
    · obtain ⟨o, ho'⟩ := h1 y (Submodule.mem_sup_left hy)
      refine ⟨o, ?_⟩
      rw [ho', map_add, ho y (hMU hy) b hb, add_zero]
    · obtain ⟨o, ho'⟩ := h1 y (Submodule.mem_sup_right hy)
      refine ⟨o, ?_⟩
      rw [ho', map_add, c_symm0 (ho a ha y (hNU hy)), zero_add]
  · refine sup_le ?_ ?_
    · intro a ha
      obtain ⟨h1, h2⟩ := g_mem_dualIn.1 ha
      refine g_mem_dualIn.2 ⟨fun y hy => ?_, ?_⟩
      · obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.1 hy
        obtain ⟨o, ho'⟩ := h1 m hm
        refine ⟨o, ?_⟩
        rw [ho', map_add, LinearMap.add_apply, c_symm0 (ho a (hM ▸ h2) n (hNU hn)), add_zero]
      · rw [h_span_sup]; exact Submodule.mem_sup_left h2
    · intro b hb
      obtain ⟨h1, h2⟩ := g_mem_dualIn.1 hb
      refine g_mem_dualIn.2 ⟨fun y hy => ?_, ?_⟩
      · obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.1 hy
        obtain ⟨o, ho'⟩ := h1 n hn
        refine ⟨o, ?_⟩
        rw [ho', map_add, LinearMap.add_apply, ho m (hMU hm) b (hN ▸ h2), zero_add]
      · rw [h_span_sup]; exact Submodule.mem_sup_right h2

theorem h_genIdx_self {U : Submodule E S.V} (hU : U ⊓ orth S U = ⊥) {M : Submodule (𝓞 E) S.V}
    (hfg : M.FG) (hM : spanE S M = U) :
    g_Comm (dualIn S M) (dualIn S M ⊓ M) ∧ g_Comm M (dualIn S M ⊓ M) ∧
      genIdx S (dualIn S M) M =
        (g_idx (dualIn S M) (dualIn S M ⊓ M) : ℝ) / (g_idx M (dualIn S M ⊓ M) : ℝ) := by
  obtain ⟨f, s, -⟩ := g_dual_facts g_starInt hU hfg hM
  have cA : g_Comm (dualIn S M) (dualIn S M ⊓ M) :=
    g_Comm_inf (g_Comm_of_span f le_rfl) (g_Comm_of_span f (by rw [s, hM]))
  have cB : g_Comm M (dualIn S M ⊓ M) :=
    g_Comm_inf (g_Comm_of_span hfg (by rw [s, hM])) (g_Comm_of_span hfg le_rfl)
  exact ⟨cA, cB, g_genIdx_via f hfg inf_le_left inf_le_right cA cB⟩

theorem h_latDet_sup {U₁ U₂ : Submodule E S.V} (hd : U₁ ⊓ U₂ = ⊥)
    (ho : ∀ x ∈ U₁, ∀ y ∈ U₂, S.hT x y = 0) (h1 : U₁ ⊓ orth S U₁ = ⊥) (h2 : U₂ ⊓ orth S U₂ = ⊥)
    {M N : Submodule (𝓞 E) S.V} (fM : M.FG) (fN : N.FG) (hM : spanE S M = U₁) (hN : spanE S N = U₂) :
    latDet S (M ⊔ N) = latDet S M * latDet S N := by
  obtain ⟨fM', sM', -⟩ := g_dual_facts g_starInt h1 fM hM
  obtain ⟨fN', sN', -⟩ := g_dual_facts g_starInt h2 fN hN
  obtain ⟨cA, cB, gM⟩ := h_genIdx_self h1 fM hM
  obtain ⟨cA', cB', gN⟩ := h_genIdx_self h2 fN hN
  have hMU : M ≤ toO S U₁ := hM ▸ g_le_span M
  have hNU : N ≤ toO S U₂ := hN ▸ g_le_span N
  have hMU' : dualIn S M ≤ toO S U₁ := sM' ▸ g_le_span _
  have hNU' : dualIn S N ≤ toO S U₂ := sN' ▸ g_le_span _
  have sD : spanE S ((dualIn S M ⊓ M) ⊔ (dualIn S N ⊓ N)) = U₁ ⊔ U₂ := by
    rw [h_span_sup, ← g_span_eq cB inf_le_right, ← g_span_eq cB' inf_le_right, hM, hN]
  have c1 : g_Comm (dualIn S M ⊔ dualIn S N) ((dualIn S M ⊓ M) ⊔ (dualIn S N ⊓ N)) :=
    g_Comm_of_span (fM'.sup fN') (by rw [sD, h_span_sup, sM', sN'])
  have c2 : g_Comm (M ⊔ N) ((dualIn S M ⊓ M) ⊔ (dualIn S N ⊓ N)) :=
    g_Comm_of_span (fM.sup fN) (by rw [sD, h_span_sup, hM, hN])
  have g := g_genIdx_via (fM'.sup fN') (fM.sup fN) (sup_le_sup inf_le_left inf_le_left)
    (sup_le_sup inf_le_right inf_le_right) c1 c2
  rw [h_idx_sup hd hMU' inf_le_left hNU' inf_le_left, h_idx_sup hd hMU inf_le_right hNU inf_le_right] at g
  show Real.sqrt (genIdx S (dualIn S (M ⊔ N)) (M ⊔ N)) =
    Real.sqrt (genIdx S (dualIn S M) M) * Real.sqrt (genIdx S (dualIn S N) N)
  rw [h_dualIn_sup ho hM hN, g, gM, gN, ← Real.sqrt_mul (by positivity)]
  congr 1
  push_cast
  rw [mul_div_mul_comm]

theorem h_span_inf {L : Submodule (𝓞 E) S.V} {U : Submodule E S.V} (h : U ≤ spanE S L) :
    spanE S (L ⊓ toO S U) = U := by
  apply le_antisymm (h_span_le inf_le_right)
  intro x hx
  obtain ⟨d, hd, hdx⟩ := m_exists_smul_mem L (h hx)
  have hd' : (algebraMap (𝓞 E) E d) ≠ 0 := by
    simpa using (map_ne_zero_iff (algebraMap (𝓞 E) E) (IsFractionRing.injective (𝓞 E) E)).2 hd
  have e : x = (algebraMap (𝓞 E) E d)⁻¹ • (d • x) := by
    rw [← IsScalarTower.algebraMap_smul E d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hdx, (toO S U).smul_mem d hx⟩)

theorem h_aniso_nd {Hs U : Submodule E S.V} (han : ∀ x ∈ Hs, S.hT x x = 0 → x = 0) (hU : U ≤ Hs) :
    U ⊓ orth S U = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨h1, h2⟩
  exact han x (hU h1) (c_mem_orth.1 h2 x h1)

end H2

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section H3

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

def h_Pr (L : Submodule (𝓞 E) S.V) (Hs Θ : Submodule E S.V) : Submodule (𝓞 E) S.V :=
  (L ⊔ toO S Θ) ⊓ toO S (Hs ⊓ orth S Θ)

theorem h_smul_inj (d : 𝓞 E) (hd : d ≠ 0) :
    Function.Injective (LinearMap.lsmul (𝓞 E) S.V d) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hd' : (algebraMap (𝓞 E) E d) ≠ 0 := by
    simpa using (map_ne_zero_iff (algebraMap (𝓞 E) E) (IsFractionRing.injective (𝓞 E) E)).2 hd
  have h1 : d • x = 0 := hx
  rw [← IsScalarTower.algebraMap_smul E d x] at h1
  exact (smul_eq_zero.1 h1).resolve_left hd'

theorem h_det_proj {Hs Θ : Submodule E S.V} (hΘ : Θ ≤ Hs) (ndH : Hs ⊓ orth S Hs = ⊥)
    (ndΘ : Θ ⊓ orth S Θ = ⊥)
    {L : Submodule (𝓞 E) S.V} (hfg : L.FG) (hspan : spanE S L = Hs) :
    latDet S L = latDet S (L ⊓ toO S Θ) * latDet S (h_Pr L Hs Θ) := by
  have hSpH : Hs ⊓ orth S Θ ≤ Hs := inf_le_left
  have hdisj : Θ ⊓ (Hs ⊓ orth S Θ) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨h1, h2⟩
    have : x ∈ Θ ⊓ orth S Θ := ⟨h1, h2.2⟩
    rwa [ndΘ] at this
  have hdisj' : (Hs ⊓ orth S Θ) ⊓ Θ = ⊥ := by rw [inf_comm]; exact hdisj
  have hsum : Θ ⊔ (Hs ⊓ orth S Θ) = Hs := by
    apply le_antisymm (sup_le hΘ hSpH)
    intro x hx
    have hc := i_isCompl Θ ndΘ
    have hx' : x ∈ Θ ⊔ orth S Θ := by rw [hc.sup_eq_top]; trivial
    obtain ⟨t, ht, s, hs, rfl⟩ := Submodule.mem_sup.1 hx'
    refine Submodule.add_mem_sup ht ⟨?_, hs⟩
    have : s = (t + s) - t := by abel
    rw [this]; exact sub_mem hx (hΘ ht)
  have ho : ∀ x ∈ Θ, ∀ y ∈ Hs ⊓ orth S Θ, S.hT x y = 0 := fun x hx y hy => c_mem_orth.1 hy.2 x hx
  have ndS : (Hs ⊓ orth S Θ) ⊓ orth S (Hs ⊓ orth S Θ) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨h1, h2⟩
    have : x ∈ Hs ⊓ orth S Hs := by
      refine ⟨h1.1, c_mem_orth.2 fun y hy => ?_⟩
      rw [← hsum] at hy
      obtain ⟨t, ht, s, hs, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add, LinearMap.add_apply, c_mem_orth.1 h1.2 t ht, c_mem_orth.1 h2 s hs, add_zero]
    rwa [ndH] at this
  have hLH : L ≤ toO S Hs := hspan ▸ g_le_span L

  have sM : spanE S (L ⊓ toO S Θ) = Θ := h_span_inf (by rw [hspan]; exact hΘ)
  have sN : spanE S (L ⊓ toO S (Hs ⊓ orth S Θ)) = Hs ⊓ orth S Θ := h_span_inf (by rw [hspan]; exact hSpH)
  have fM : (L ⊓ toO S Θ).FG := g_fg_le hfg inf_le_left
  have fN : (L ⊓ toO S (Hs ⊓ orth S Θ)).FG := g_fg_le hfg inf_le_left
  have hNP : L ⊓ toO S (Hs ⊓ orth S Θ) ≤ h_Pr L Hs Θ := fun x hx => ⟨Submodule.mem_sup_left hx.1, hx.2⟩
  have sMN : spanE S ((L ⊓ toO S Θ) ⊔ (L ⊓ toO S (Hs ⊓ orth S Θ))) = Hs := by
    rw [h_span_sup, sM, sN, hsum]
  have hMNL : (L ⊓ toO S Θ) ⊔ (L ⊓ toO S (Hs ⊓ orth S Θ)) ≤ L := sup_le inf_le_left inf_le_left
  have cL : g_Comm L ((L ⊓ toO S Θ) ⊔ (L ⊓ toO S (Hs ⊓ orth S Θ))) :=
    g_Comm_of_span hfg (by rw [sMN, hspan])
  have sP : spanE S (h_Pr L Hs Θ) = Hs ⊓ orth S Θ :=
    le_antisymm (h_span_le inf_le_right) (by rw [← sN]; exact Submodule.span_mono hNP)
  have fP : (h_Pr L Hs Θ).FG := by
    obtain ⟨d, hd, hdL⟩ := cL
    apply Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) S.V d) (h_smul_inj d hd)
    refine g_fg_le fN ?_
    rintro _ ⟨s, hs, rfl⟩
    show d • s ∈ L ⊓ toO S (Hs ⊓ orth S Θ)
    obtain ⟨x, hx, θ, hθ, e⟩ := Submodule.mem_sup.1 hs.1
    obtain ⟨m, hm, n, hn, e2⟩ := Submodule.mem_sup.1 (hdL x hx)
    have h1 : d • s = n := by
      apply h_sat_cancel hdisj' ((toO S (Hs ⊓ orth S Θ)).smul_mem d hs.2) hn.2 (zero_mem Θ)
        (add_mem hm.2 ((toO S Θ).smul_mem d hθ) : m + d • θ ∈ Θ)
      rw [add_zero, ← e, smul_add, ← e2]; abel
    rw [h1]; exact hn

  have j1 : g_idx L ((L ⊓ toO S Θ) ⊔ (L ⊓ toO S (Hs ⊓ orth S Θ))) =
      g_idx (L ⊔ toO S Θ) ((L ⊓ toO S (Hs ⊓ orth S Θ)) ⊔ toO S Θ) :=
    h_idx_congr le_sup_left (sup_le (le_sup_of_le_right inf_le_right) le_sup_left)
      (sup_le le_sup_left (le_sup_of_le_right le_sup_right)) (by
        rintro x ⟨h1, h2⟩
        obtain ⟨n, hn, θ, hθ, e⟩ := Submodule.mem_sup.1 h2
        have hθL : θ ∈ L := by
          have : θ = x - n := by rw [← e]; abel
          rw [this]; exact sub_mem h1 hn.1
        rw [← e, add_comm]
        exact Submodule.add_mem_sup ⟨hθL, hθ⟩ hn)
  have j2 : g_idx (h_Pr L Hs Θ) (L ⊓ toO S (Hs ⊓ orth S Θ)) =
      g_idx (L ⊔ toO S Θ) ((L ⊓ toO S (Hs ⊓ orth S Θ)) ⊔ toO S Θ) :=
    h_idx_congr inf_le_left le_sup_left (by
        refine sup_le ?_ (le_sup_of_le_right le_sup_right)
        intro x hx
        have hxH : x ∈ Θ ⊔ (Hs ⊓ orth S Θ) := by rw [hsum]; exact hLH hx
        obtain ⟨t, ht, s, hs, e⟩ := Submodule.mem_sup.1 hxH
        have hsP : s ∈ h_Pr L Hs Θ := by
          refine ⟨?_, hs⟩
          have : s = x + -t := by rw [← e]; abel
          rw [this]; exact Submodule.add_mem_sup hx (neg_mem ht : -t ∈ Θ)
        rw [← e, add_comm]
        exact Submodule.add_mem_sup hsP (Submodule.mem_sup_right ht)) (by
        rintro y ⟨h1, h2⟩
        obtain ⟨n, hn, θ, hθ, e⟩ := Submodule.mem_sup.1 h2
        have : y = n := h_sat_cancel hdisj' h1.2 hn.2 (zero_mem Θ) hθ (by rw [add_zero, e])
        rw [this]; exact hn)
  have hj : 0 < g_idx L ((L ⊓ toO S Θ) ⊔ (L ⊓ toO S (Hs ⊓ orth S Θ))) := g_idx_pos hfg cL
  have hj' : (0 : ℝ) < (g_idx L ((L ⊓ toO S Θ) ⊔ (L ⊓ toO S (Hs ⊓ orth S Θ))) : ℝ) := by exact_mod_cast hj

  have d1 : latDet S ((L ⊓ toO S Θ) ⊔ (L ⊓ toO S (Hs ⊓ orth S Θ))) =
      latDet S L * (g_idx L ((L ⊓ toO S Θ) ⊔ (L ⊓ toO S (Hs ⊓ orth S Θ))) : ℝ) :=
    g_detIndexG g_starInt L _ hMNL hfg (by rw [sMN, hspan]) (by rw [hspan]; exact ndH)
  have d2 : latDet S (L ⊓ toO S (Hs ⊓ orth S Θ)) =
      latDet S (h_Pr L Hs Θ) * (g_idx (h_Pr L Hs Θ) (L ⊓ toO S (Hs ⊓ orth S Θ)) : ℝ) :=
    g_detIndexG g_starInt _ _ hNP fP (by rw [sP, sN]) (by rw [sP]; exact ndS)
  have d3 := h_latDet_sup hdisj ho ndΘ ndS fM fN sM sN
  rw [j2, ← j1] at d2
  rw [d3, d2] at d1
  have : (latDet S (L ⊓ toO S Θ) * latDet S (h_Pr L Hs Θ)) *
      (g_idx L ((L ⊓ toO S Θ) ⊔ (L ⊓ toO S (Hs ⊓ orth S Θ))) : ℝ) =
      latDet S L * (g_idx L ((L ⊓ toO S Θ) ⊔ (L ⊓ toO S (Hs ⊓ orth S Θ))) : ℝ) := by
    rw [← d1]; ring
  exact (mul_right_cancel₀ hj'.ne' this).symm

theorem h_det_proj_aniso {Hs Θ : Submodule E S.V} (hΘ : Θ ≤ Hs) (han : ∀ x ∈ Hs, S.hT x x = 0 → x = 0)
    {L : Submodule (𝓞 E) S.V} (hfg : L.FG) (hspan : spanE S L = Hs) :
    latDet S L = latDet S (L ⊓ toO S Θ) * latDet S (h_Pr L Hs Θ) :=
  h_det_proj hΘ (h_aniso_nd han le_rfl) (h_aniso_nd han hΘ) hfg hspan

end H3

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section H4

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {Λ : Submodule (𝓞 E) S.V} {T T' : E} {g : ℕ}
variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem h_Psi_sat {W : Submodule E S.V} {k : ℕ} (hW : WHypG F W k) {Hs Θs : Submodule E S.V}
    (hH : Hs ≤ orth S (Xplus F)) (hΘ : Θs ≤ Hs)
    (hΘX : Θs ⊔ Xsp F = Th Λ F F' F'' β ⊔ Xsp F) {L : Submodule (𝓞 E) S.V} (hL : L ≤ toO S Hs) :
    Psi Λ F F' F'' β W L ⊔ toO S (Xsp F) = h_Pr L Hs Θs ⊔ toO S (Xsp F) := by
  have hHX : Hs ≤ orth S (Xsp F) := hH.trans (c_orth_anti (c_X_le_Xplus F))
  have hWX : W ≤ orth S (Xsp F) := by
    refine le_trans ?_ (c_orth_anti (c_X_le_Xplus F))
    rw [← hW.1]; exact le_sup_left
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    unfold Psi
    rw [Submodule.span_le]
    rintro s ⟨x, hx, hs, hxs⟩
    rw [← hΘX] at hxs
    obtain ⟨θ, hθ, ξ, hξ, e⟩ := Submodule.mem_sup.1 hxs
    have e1 : s + ξ = x + -θ := by
      have : x = s + (θ + ξ) := by rw [e]; abel
      rw [this]; abel
    have hsH : s + ξ ∈ h_Pr L Hs Θs := by
      refine ⟨?_, ?_, ?_⟩
      · rw [e1]; exact Submodule.add_mem_sup hx (neg_mem hθ : -θ ∈ Θs)
      · rw [e1]; exact add_mem (hL hx) (neg_mem (hΘ hθ))
      · refine c_mem_orth.2 fun t ht => ?_
        have h1 : S.hT t ξ = 0 := c_symm0 (c_mem_orth.1 (hHX (hΘ ht)) ξ hξ)
        have h2 : t ∈ Th Λ F F' F'' β ⊔ Xsp F := by rw [← hΘX]; exact Submodule.mem_sup_left ht
        obtain ⟨t₁, ht₁, η, hη, rfl⟩ := Submodule.mem_sup.1 h2
        have h3 : S.hT t₁ s = 0 := c_mem_orth.1 hs.2 t₁ ht₁
        have h4 : S.hT η s = 0 := c_mem_orth.1 (hWX hs.1) η hη
        rw [map_add, h1, add_zero, map_add, LinearMap.add_apply, h3, h4, add_zero]
    have : s = (s + ξ) + -ξ := by abel
    show s ∈ h_Pr L Hs Θs ⊔ toO S (Xsp F)
    rw [this]
    exact Submodule.add_mem_sup hsH (neg_mem hξ : -ξ ∈ Xsp F)
  · refine sup_le ?_ le_sup_right
    rintro sH ⟨h1, h2, h3⟩
    obtain ⟨x, hx, θ, hθ, e⟩ := Submodule.mem_sup.1 h1
    have h4 : sH ∈ W ⊔ Xsp F := by rw [hW.1]; exact hH h2
    obtain ⟨w, hw, ξ, hξ, e2⟩ := Submodule.mem_sup.1 h4
    have hwTh : w ∈ orth S (Th Λ F F' F'' β) := by
      refine c_mem_orth.2 fun t₁ ht₁ => ?_
      have h5 : t₁ ∈ Θs ⊔ Xsp F := by rw [hΘX]; exact Submodule.mem_sup_left ht₁
      obtain ⟨t, ht, η, hη, rfl⟩ := Submodule.mem_sup.1 h5
      have k1 : S.hT η w = 0 := c_mem_orth.1 (hWX hw) η hη
      have k2 : S.hT t sH = 0 := c_mem_orth.1 h3 t ht
      have k3 : S.hT t ξ = 0 := c_symm0 (c_mem_orth.1 (hHX (hΘ ht)) ξ hξ)
      rw [← e2, map_add, k3, add_zero] at k2
      rw [map_add, LinearMap.add_apply, k1, k2, add_zero]
    have hwP : w ∈ Psi Λ F F' F'' β W L := by
      apply Submodule.subset_span
      refine ⟨x, hx, ⟨hw, hwTh⟩, ?_⟩
      rw [← hΘX]
      have : x - w = -θ + ξ := by
        have : x = sH - θ := by rw [← e]; abel
        rw [this, ← e2]; abel
      rw [this]
      exact Submodule.add_mem_sup (neg_mem hθ) hξ
    rw [← e2]
    exact Submodule.add_mem_sup hwP hξ

theorem h_latDet_Psi {W : Submodule E S.V} {k : ℕ} (hW : WHypG F W k) {Hs Θs : Submodule E S.V}
    (hH : Hs ≤ orth S (Xplus F)) (hHX0 : Hs ⊓ Xsp F = ⊥) (hΘ : Θs ≤ Hs)
    (hΘX : Θs ⊔ Xsp F = Th Λ F F' F'' β ⊔ Xsp F) {L : Submodule (𝓞 E) S.V} (hL : L ≤ toO S Hs) :
    latDet S (Psi Λ F F' F'' β W L) = latDet S (h_Pr L Hs Θs) := by
  have hHX : Hs ≤ orth S (Xsp F) := hH.trans (c_orth_anti (c_X_le_Xplus F))
  have hWX : W ≤ orth S (Xsp F) := by
    refine le_trans ?_ (c_orth_anti (c_X_le_Xplus F))
    rw [← hW.1]; exact le_sup_left
  have hPW : Psi Λ F F' F'' β W L ≤ toO S W := by
    unfold Psi
    rw [Submodule.span_le]
    rintro s ⟨x, -, hs, -⟩
    exact hs.1
  have hPrH : h_Pr L Hs Θs ≤ toO S Hs := fun x hx => hx.2.1
  refine h_latDet_shift (c_X_iso F) (hPW.trans hWX) ?_ (hPrH.trans hHX) ?_ (h_Psi_sat hW hH hΘ hΘX hL)
  · rw [eq_bot_iff, ← hW.2.1]
    exact inf_le_inf_right _ (h_span_le hPW)
  · rw [eq_bot_iff, ← hHX0]
    exact inf_le_inf_right _ (h_span_le hPrH)

theorem h_La_fg (hΛ : Submodule.IsLattice E Λ) (hg : 0 < g) (hz : IsLift Λ F) (hz' : IsLift Λ F')
    (hG : Gval F F' ≠ 0) : (La Λ g F F').FG := by
  have hU : HU Λ F F' := a_HU Λ hΛ F F' hz.2 hz'.2
  obtain ⟨hX, hX'⟩ := a_X_le hU
  have hfinB : Finite (BQ Λ F F') := m_BQ_finite Λ F F' hΛ
  have hle : Thp Λ F F' ≤ La Λ g F F' := c_Thp_le_La hU
  obtain ⟨φ, hφ, -⟩ := lemma_one_quotient_embedding (g := g) hg hz hz' (a_disj (a_HInd F F' hG)) hX hX'
  have hfinQ : Finite (La Λ g F F' ⧸ (Thp Λ F F').comap (La Λ g F F').subtype) :=
    Finite.of_injective φ hφ
  have hThfg : (Thp Λ F F').FG := g_fg_of_le Λ hΛ inf_le_left
  have e : ((Thp Λ F F').comap (La Λ g F F').subtype) ≃ₗ[𝓞 E] Thp Λ F F' :=
    Submodule.comapSubtypeEquivOfLe hle
  have h1 : Module.Finite (𝓞 E) (Thp Λ F F') := Module.Finite.iff_fg.2 hThfg
  have h2 : Module.Finite (𝓞 E) ((Thp Λ F F').comap (La Λ g F F').subtype) :=
    Module.Finite.equiv e.symm
  have h3 : Module.Finite (𝓞 E) (La Λ g F F' ⧸ (Thp Λ F F').comap (La Λ g F F').subtype) :=
    Module.Finite.of_finite
  have h4 : Module.Finite (𝓞 E) (La Λ g F F') :=
    Module.Finite.of_submodule_quotient ((Thp Λ F F').comap (La Λ g F F').subtype)
  exact Module.Finite.iff_fg.1 h4

theorem h_Hp_aniso (hU : HU Λ F F') (hN : HNd F F') (hPos : PosX F) :
    ∀ x ∈ Hp Λ F F', S.hT x x = 0 → x = 0 := by
  intro x hx h0
  by_contra hne
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := radical_positive_each_embedding Λ hU hN hPos τ x hx hne
  simp [nrm, h0] at this

theorem h_Hp_inf_X (hU : HU Λ F F') (hN : HNd F F') : Hp Λ F F' ⊓ Xsp F = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨h1, h2⟩
  exact c_Hp_X Λ hU hN h1 h2

theorem h_a2det_gen (hΛ : Submodule.IsLattice E Λ) (hg : 0 < g) (hz : IsLift Λ F) (hz' : IsLift Λ F')
    (hz'' : IsLift Λ F'') (hG' : Gval F F' ≠ 0) (hG'' : Gval F F'' ≠ 0)
    (hP : IsPair Λ F F' F'' β g) (hPos : PosX F) {W : Submodule E S.V} {k : ℕ} (hW : WHypG F W k) :
    latDet S (Mlat Λ F F' F'' β g) ^ 2 =
      latDet S (La Λ g F F') * latDet S (La Λ g F F'') /
        (latDet S (Psi Λ F F' F'' β W (La Λ g F F')) * latDet S (Psi Λ F F' F'' β W (La Λ g F F''))) := by
  have hU' : HU Λ F F' := a_HU Λ hΛ F F' hz.2 hz'.2
  have hU'' : HU Λ F F'' := a_HU Λ hΛ F F'' hz.2 hz''.2
  have hN' : HNd F F' := a_HNd F F' hG'
  have hN'' : HNd F F'' := a_HNd F F'' hG''
  have s' := (g_span_La Λ F F' g hΛ (c_Thp_le_La hU')).1
  have s'' := (g_span_La Λ F F'' g hΛ (c_Thp_le_La hU'')).1
  have hL' : La Λ g F F' ≤ toO S (Hp Λ F F') := s' ▸ g_le_span _
  have hL'' : La Λ g F F'' ≤ toO S (Hp Λ F F'') := s'' ▸ g_le_span _
  have A : latDet S (La Λ g F F') = latDet S (Mlat Λ F F' F'' β g) *
      latDet S (h_Pr (La Λ g F F') (Hp Λ F F') (Th Λ F F' F'' β)) :=
    h_det_proj_aniso c_Th_le_Hp (h_Hp_aniso hU' hN' hPos) (h_La_fg hΛ hg hz hz' hG') s'
  have B : latDet S (La Λ g F F'') = latDet S (Mlat'' Λ F F' F'' β g) *
      latDet S (h_Pr (La Λ g F F'') (Hp Λ F F'') (Th'' Λ F F' F'' β)) :=
    h_det_proj_aniso c_Th''_le_Hp (h_Hp_aniso hU'' hN'' hPos) (h_La_fg hΛ hg hz hz'' hG'') s''
  have hM' : Mlat Λ F F' F'' β g ≤ toO S (Hp Λ F F') := inf_le_left.trans hL'
  have hM'' : Mlat'' Λ F F' F'' β g ≤ toO S (Hp Λ F F'') := inf_le_left.trans hL''
  have C : latDet S (Mlat Λ F F' F'' β g) = latDet S (Mlat'' Λ F F' F'' β g) := by
    refine h_latDet_shift (c_X_iso F) (hM'.trans (c_Hp_orthX Λ hU')) ?_ (hM''.trans (c_Hp_orthX Λ hU'')) ?_
      (c_M_eq hP)
    · rw [eq_bot_iff, ← h_Hp_inf_X hU' hN']
      exact inf_le_inf_right _ (h_span_le hM')
    · rw [eq_bot_iff, ← h_Hp_inf_X hU'' hN'']
      exact inf_le_inf_right _ (h_span_le hM'')
  have D' := h_latDet_Psi (Λ := Λ) (F' := F') (F'' := F'') (β := β) hW (c_Hp_orthXplus Λ hU')
    (h_Hp_inf_X hU' hN') c_Th_le_Hp rfl hL'
  have D'' := h_latDet_Psi (Λ := Λ) (F' := F') (F'' := F'') (β := β) hW (c_Hp_orthXplus Λ hU'')
    (h_Hp_inf_X hU'' hN'') c_Th''_le_Hp c_Th''_sup_X hL''
  rw [D', D'', A, B, ← C]
  have p1 := h_latDet_pos (h_Pr (La Λ g F F') (Hp Λ F F') (Th Λ F F' F'' β))
  have p2 := h_latDet_pos (h_Pr (La Λ g F F'') (Hp Λ F F'') (Th'' Λ F F' F'' β))
  field_simp

end H4

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem h_a2det (D : D7) (u : D.what₂.Word) (T' : ℕ) (Λ : Submodule (𝓞 D.host.E) (hS D).V)
    (F : LFlag (hS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' F'' : LFlag (hS D) D.R.rS ((T' : ℕ) : D.host.E))
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (hF : FixedHyp D Λ F) (hPr : PrimeHyp D u T') (hT' : IsTerm Λ (gS D) F F')
    (hT'' : IsTerm Λ (gS D) F F'') (hP : IsPair Λ F F' F'' β (gS D))
    (W : Submodule D.host.E (hS D).V) (hW : WHyp D F W) :
    latDet (hS D) (Mlat Λ F F' F'' β (gS D)) ^ 2 =
      latDet (hS D) (La Λ (gS D) F F') * latDet (hS D) (La Λ (gS D) F F'') /
        (latDet (hS D) (Psi Λ F F' F'' β W (La Λ (gS D) F F')) *
          latDet (hS D) (Psi Λ F F' F'' β W (La Λ (gS D) F F''))) :=
  h_a2det_gen hF.1 (g_gS_pos D) hF.2.2.1 hT'.1 hT''.1 hT'.2.2 hT''.2.2 hP
    (p_posX D _ (lt_of_lt_of_le (by norm_num) hPr.2.1) F) hW

end D7

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section H5

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem h_existsW_gen (F : LFlag S r T) (hT : T ≠ 0) (k : ℕ) (hV : finrank E S.V = k + 2 * r + 1) :
    ∃ W : Submodule E S.V, WHypG F W k := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Xsp F)
  have hXO : Xsp F ≤ orth S (Xplus F) := c_X_le_orthXplus F
  have h1 : (q ⊓ orth S (Xplus F)) ⊔ Xsp F = orth S (Xplus F) := by
    rw [sup_comm, ← sup_inf_assoc_of_le q hXO, hq.sup_eq_top, top_inf_eq]
  have h2 : (q ⊓ orth S (Xplus F)) ⊓ Xsp F = ⊥ := by
    rw [eq_bot_iff, ← hq.inf_eq_bot]
    rintro x ⟨⟨a, -⟩, b⟩
    exact ⟨b, a⟩
  refine ⟨q ⊓ orth S (Xplus F), h1, h2, ?_⟩
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (q ⊓ orth S (Xplus F)) (Xsp F)
  rw [h1, h2, finrank_bot, c_finrank_X F] at e1
  have e2 := c_finrank_orth_le (Xplus F)
  have e3 := c_finrank_orth_ge (Xplus F)
  have e4 := c_finrank_Xplus F hT
  have e5 : finrank E (Xplus F) ≤ r + 1 := by
    have a1 := Submodule.finrank_add_le_finrank_add_finrank (Xsp F) (Submodule.span E {F.fl.z})
    have a2 := finrank_span_le_card (R := E) ({F.fl.z} : Set S.V)
    rw [c_finrank_X F] at a1
    simp only [Set.toFinset_singleton, Finset.card_singleton] at a2
    exact a1.trans (by omega)
  omega

end H5

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem h_existsW (D : D7) (T : ℕ) (F : LFlag (hS D) D.R.rS ((T : ℕ) : D.host.E)) (hT : 0 < T) :
    ∃ W : Submodule D.host.E (hS D).V, WHyp D F W :=
  h_existsW_gen F (by exact_mod_cast hT.ne') D.R.k (p_rankV D)

end D7

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lattice_lemma_two (D : D7) : VanishingOnXAndXPlusGluing.Conclusion2 D := by
  intro u T' Λ F F' hF hPr hT
  exact lemma_two_of_three_parts D u T' Λ F F' hF hPr hT
    (lemma_two_unique_pair Λ hF.1 F F' hF.2.2.1.2 hT.1.2 hT.2.2)
    (lemma_two_lift_difference Λ hF.1 F F' hF.2.2.1.2 hT.1.2 hT.2.2)
    (lemma_two_exists_lifts Λ hF.1 F F' hF.2.2.1.2 hT.1.2 hT.2.2)

theorem radical_positive_definite (D : D7) : VanishingOnXAndXPlusGluing.GlobalIntegralModelCondition D := by
  intro u T' Λ F F' hF hPr hT
  have h0 : 0 < Tu D u := lt_of_lt_of_le (by norm_num) hPr.2.1
  exact ⟨a_rankHp_k Λ hF.1 F F' hF.2.2.1.2 hT.1.2 hT.2.2 D.R.k (p_rankV D),
    radical_positive_each_embedding Λ (a_HU Λ hF.1 F F' hF.2.2.1.2 hT.1.2) (a_HNd F F' hT.2.2) (p_posX D _ h0 F)⟩

def Lem1Det (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (T' : ℕ) (Λ : VanishingOnXAndXPlusGluing.LatS D) (F : VanishingOnXAndXPlusGluing.FlS D (Tu D u)) (F' : VanishingOnXAndXPlusGluing.FlS D T'),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' →
      latDet (hS D) (La Λ (gS D) F F') =
        NG Λ F F' / ((Nat.card (BQ Λ F F') : ℝ) * (iIdx Λ (gS D) F F' : ℝ))

theorem z_gS_pos (D : D7) : 0 < gS D :=
  Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem lemma_one_of_determinant (D : D7) (h : Lem1Det D) : VanishingOnXAndXPlusGluing.Conclusion1 D := by
  intro u T' Λ F F' hF hPr hT
  have hU := a_HU Λ hF.1 F F' hF.2.2.1.2 hT.1.2
  have hfin : Finite (BQ Λ F F') := m_BQ_finite Λ F F' hF.1
  obtain ⟨φ, h1, h2, h3⟩ := lemma_one_quotient_embedding (z_gS_pos D) hF.2.2.1 hT.1 (a_disj (a_HInd F F' hT.2.2))
    (a_X_le hU).1 (a_X_le hU).2
  exact ⟨hfin, m_i_le_gB Λ F F' (gS D) hfin φ h1, lemma_one_card_bound_local D Λ F F' hF hT,
    h u T' Λ F F' hF hPr hT, φ, h1, h2, h3⟩

theorem z_Lem1Det (D : D7) : Lem1Det D :=
  fun _ _ Λ F F' hF _ hT => lemma_one_det_eq_index_quotient D Λ F F' hF hT

theorem lattice_lemma_one (D : D7) : VanishingOnXAndXPlusGluing.Conclusion1 D := lemma_one_of_determinant D (z_Lem1Det D)

theorem radicals_eq_theta (D : D7) : VanishingOnXAndXPlusGluing.DefiniteRankOne D := by
  intro u T' Λ F F' F'' β hF hPr hT' hT'' hP hs
  exact radical_setting_third_of D Λ F F' F'' β (a_HU Λ hF.1 F F' hF.2.2.1.2 hT'.1.2) (a_HNd F F' hT'.2.2)
    (a_HU Λ hF.1 F F'' hF.2.2.1.2 hT''.1.2) (a_HNd F F'' hT''.2.2)
    (radical_positive_definite D u T' Λ F F' hF hPr hT').1 (radical_positive_definite D u T' Λ F F'' hF hPr hT'').1 hs

def RadicalDeterminantIdentity (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (T' : ℕ) (Λ : VanishingOnXAndXPlusGluing.LatS D) (F : VanishingOnXAndXPlusGluing.FlS D (Tu D u)) (F' F'' : VanishingOnXAndXPlusGluing.FlS D T')
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → 2 ≤ s0 Λ F F' F'' β D.R.k →
      ∀ W : Submodule D.host.E (hS D).V, WHyp D F W →
        latDet (hS D) (Mlat Λ F F' F'' β (gS D)) ^ 2 =
          latDet (hS D) (La Λ (gS D) F F') * latDet (hS D) (La Λ (gS D) F F'') /
            (latDet (hS D) (Psi Λ F F' F'' β W (La Λ (gS D) F F')) *
              latDet (hS D) (Psi Λ F F' F'' β W (La Λ (gS D) F F'')))

theorem radical_second_of_determinant (D : D7) (h : RadicalDeterminantIdentity D) : VanishingOnXAndXPlusGluing.HyperplaneRank D := by
  intro u T' Λ F F' F'' β hF hPr hT' hT'' hP hs W hW
  have h0 : 0 < Tu D u := lt_of_lt_of_le (by norm_num) hPr.2.1
  have h0' : 0 < T' := lt_of_lt_of_le (by norm_num) hPr.2.2.2.1
  exact radical_setting_second_of D Λ (gS D) F F' F'' β W (p_starConj D) hF.1 hF.2.1 hP
    (a_HU Λ hF.1 F F' hF.2.2.1.2 hT'.1.2) (a_HNd F F' hT'.2.2)
    (a_HU Λ hF.1 F F'' hF.2.2.1.2 hT''.1.2) (a_HNd F F'' hT''.2.2)
    (p_posX D _ h0 F) (p_posX D _ h0' F'') hW
    (radical_positive_definite D u T' Λ F F' hF hPr hT').1 (radical_positive_definite D u T' Λ F F'' hF hPr hT'').1
    (h u T' Λ F F' F'' β hF hPr hT' hT'' hP hs W hW)

theorem z_A2Det (D : D7) : RadicalDeterminantIdentity D :=
  fun u T' Λ F F' F'' β hF hPr hT' hT'' hP _ W hW => h_a2det D u T' Λ F F' F'' β hF hPr hT' hT'' hP W hW

theorem radical_second_claim (D : D7) : VanishingOnXAndXPlusGluing.HyperplaneRank D := radical_second_of_determinant D (z_A2Det D)

def ExistsW (D : D7) : Prop :=
  ∀ (T : ℕ) (F : VanishingOnXAndXPlusGluing.FlS D T), 0 < T → ∃ W : Submodule D.host.E (hS D).V, WHyp D F W

def ThmAIneq (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (T' : ℕ) (Λ : VanishingOnXAndXPlusGluing.LatS D) (F : VanishingOnXAndXPlusGluing.FlS D (Tu D u)) (F' F'' : VanishingOnXAndXPlusGluing.FlS D T')
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → 2 ≤ s0 Λ F F' F'' β D.R.k →
    (BNondeg Λ F F' F'' β →
      latDet (hS D) (Mlat Λ F F' F'' β (gS D)) * (iIdx Λ (gS D) F F' : ℝ) * (iIdx Λ (gS D) F F'' : ℝ) ≤
        (2 / ((gS D : ℕ) : ℝ)) ^ ((s0 Λ F F' F'' β D.R.k - 1) * D.R.f) *
          Real.sqrt (G0 Λ (gS D) F F' * G0 Λ (gS D) F F'')) ∧
    (¬ BNondeg Λ F F' F'' β →
      latDet (hS D) (Mlat Λ F F' F'' β (gS D)) * (iIdx Λ (gS D) F F' : ℝ) * (iIdx Λ (gS D) F F'' : ℝ) ≤
        (2 / ((gS D : ℕ) : ℝ)) ^ ((s0 Λ F F' F'' β D.R.k - 2) * D.R.f) *
          Real.sqrt (G0 Λ (gS D) F F' * G0 Λ (gS D) F F'') * (((Tu D u : ℕ) : ℝ) ^ D.R.f)⁻¹ *
          placeProd (fun τ : D.host.E →+* ℂ =>
            onePlusChSh (Tu D u) T' F F' τ * onePlusChSh (Tu D u) T' F F'' τ))

theorem theorem_A_of_inequalities (D : D7) (h : ThmAIneq D) : VanishingOnXAndXPlusGluing.PointsLemma D := by
  intro u T' Λ F F' F'' β hF hPr hT' hT'' hP hs
  have h0 : 0 < Tu D u := lt_of_lt_of_le (by norm_num) hPr.2.1
  have h0' : 0 < T' := lt_of_lt_of_le (by norm_num) hPr.2.2.2.1
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨i1, i2⟩ := h u T' Λ F F' F'' β hF hPr hT' hT'' hP hs
  refine ⟨i1, fun hnd => ?_⟩
  obtain ⟨r1, r2⟩ := c_thmA_ranks hP (a_HU Λ hF.1 F F' hF.2.2.1.2 hT'.1.2) (a_HNd F F' hT'.2.2)
    (a_HU Λ hF.1 F F'' hF.2.2.1.2 hT''.1.2) (a_HNd F F'' hT''.2.2) (p_posX D _ h0' F'')
    (by exact_mod_cast h0.ne') D.R.k (p_rankV D)
    (radical_positive_definite D u T' Λ F F' hF hPr hT').1 (radical_positive_definite D u T' Λ F F'' hF hPr hT'').1 hk hnd
  exact ⟨r1, r2, i2 hnd⟩

theorem lattice_theorem_B_of_steps (D : D7) (h : TheoremBFirstTwoSteps D) : VanishingOnXAndXPlusGluing.Conclusion4 D :=
  theorem_B_of_lemma_two_steps D (lattice_lemma_two D) (radicals_eq_theta D) h

theorem lattice_theorem_B (D : D7) : VanishingOnXAndXPlusGluing.Conclusion4 D :=
  lattice_theorem_B_of_steps D (theorem_B_first_two_steps D (gluing_unimodular_first D) (radicals_eq_theta D))

theorem hadamard_section : Formalism.MainNotions.S.UnitaryVolumeMass.stBRhad := gluing_hadamard_inequality
theorem lattice_lemma_two_section (D : D7) : Formalism.MainNotions.S.UnitaryVolumeMass.stLem2 D := lattice_lemma_two D
theorem lemma_one_section (D : D7) : Formalism.MainNotions.S.UnitaryVolumeMass.stLem1 D := lattice_lemma_one D
theorem radical_second_section (D : D7) : Formalism.MainNotions.S.UnitaryVolumeMass.HyperplaneRankAllWords D := radical_second_claim D
theorem theorem_B_section (D : D7) : Formalism.MainNotions.S.UnitaryVolumeMass.stThmB D := lattice_theorem_B D

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Fam

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open NumberField Module

section Del

variable {E : Type} [Field E] [NumberField E]

theorem j_exists_nat_smul_mem {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (M : Submodule (𝓞 E) V) {x : V}
    (hx : x ∈ Submodule.span E (M : Set V)) : ∃ n : ℕ, 0 < n ∧ n • x ∈ M := by
  first
  | exact Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_memL
  | (apply Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_memL <;> assumption)
  | (intros; apply Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_memL <;> assumption)
  | (intros; exact Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_memL ‹_› ‹_›)
variable {e : ℕ}

def j_Lat (A : Submodule (𝓞 E) (Fin e → E)) : Prop :=
  A.FG ∧ Submodule.span E (A : Set (Fin e → E)) = ⊤

def j_IsBasisOf (A : Submodule (𝓞 E) (Fin e → E))
    (a : Basis (Fin (finrank ℚ (Fin e → E))) ℚ (Fin e → E)) : Prop :=
  A.toAddSubgroup = AddSubgroup.closure (Set.range a)

theorem j_exists_basis {A : Submodule (𝓞 E) (Fin e → E)} (hA : j_Lat A) : ∃ a, j_IsBasisOf A a := by
  let Az : Submodule ℤ (Fin e → E) := A.restrictScalars ℤ
  have h1 : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.2 hA.1
  have h2 : Module.Finite ℤ A := Module.Finite.trans (𝓞 E) _
  have h3 : Module.Finite ℤ Az :=
    Module.Finite.equiv ((Submodule.restrictScalarsEquiv ℤ (𝓞 E) (Fin e → E) A).restrictScalars ℤ).symm
  have hlat : Submodule.IsLattice ℚ Az := by
    refine ⟨Module.Finite.iff_fg.1 h3, ?_⟩
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span E (A : Set (Fin e → E)) := by rw [hA.2]; trivial
    obtain ⟨n, hn, hnx⟩ := j_exists_nat_smul_mem A hx
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have : x = (n : ℚ)⁻¹ • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hnx)
  have hr : finrank ℤ Az = finrank ℚ (Fin e → E) :=
    Module.finrank_eq_of_rank_eq
      ((Submodule.IsLattice.rank' ℚ Az).trans (Module.finrank_eq_rank ℚ (Fin e → E)).symm)
  let b : Basis (Fin (finrank ℚ (Fin e → E))) ℤ Az := Module.finBasisOfFinrankEq ℤ Az hr
  refine ⟨b.extendOfIsLattice ℚ, ?_⟩
  unfold j_IsBasisOf
  have hrange : Set.range (b.extendOfIsLattice ℚ) = Az.subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp
  have hspan : Submodule.span ℤ (Set.range (b.extendOfIsLattice ℚ)) = Az := by
    rw [hrange, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  ext x
  have key : ∀ s : Set (Fin e → E), Submodule.span ℤ s = Az → (x ∈ Az ↔ x ∈ AddSubgroup.closure s) := by
    intro s hs
    rw [← hs, ← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]
  exact key _ hspan

theorem j_det_mul (b₀ a b : Basis (Fin (finrank ℚ (Fin e → E))) ℚ (Fin e → E)) :
    b₀.det b = a.det b * b₀.det a := by
  have hb : (b : Fin _ → (Fin e → E)) = (a.constr ℚ b : (Fin e → E) →ₗ[ℚ] (Fin e → E)) ∘ a := by
    funext i; simp
  have e1 := b₀.det_comp (a.constr ℚ b : (Fin e → E) →ₗ[ℚ] (Fin e → E)) a
  have e2 := a.det_comp (a.constr ℚ b : (Fin e → E) →ₗ[ℚ] (Fin e → E)) a
  rw [← hb] at e1 e2
  rw [e1, e2, a.det_self, mul_one]

theorem j_relIndex {A B : Submodule (𝓞 E) (Fin e → E)} (hBA : B ≤ A) {a b} (ha : j_IsBasisOf A a)
    (hb : j_IsBasisOf B b) : ((B.toAddSubgroup.relIndex A.toAddSubgroup : ℕ) : ℚ) = |a.det b| :=
  AddSubgroup.relIndex_eq_abs_det B.toAddSubgroup A.toAddSubgroup hBA b a hb ha

def j_del (A : Submodule (𝓞 E) (Fin e → E)) : ℚ := by
  classical
  exact if h : ∃ a, j_IsBasisOf A a then |(Module.finBasis ℚ (Fin e → E)).det (fun i => Classical.choose h i)| else 0

theorem j_del_mul {A B : Submodule (𝓞 E) (Fin e → E)} (hBA : B ≤ A) {a b} (ha : j_IsBasisOf A a)
    (hb : j_IsBasisOf B b) :
    |(Module.finBasis ℚ (Fin e → E)).det b| =
      ((B.toAddSubgroup.relIndex A.toAddSubgroup : ℕ) : ℚ) * |(Module.finBasis ℚ (Fin e → E)).det a| := by
  rw [j_relIndex hBA ha hb, j_det_mul _ a b, abs_mul]

theorem j_del_eq {A : Submodule (𝓞 E) (Fin e → E)} {a} (ha : j_IsBasisOf A a) :
    j_del A = |(Module.finBasis ℚ (Fin e → E)).det a| := by
  have h : ∃ a, j_IsBasisOf A a := ⟨a, ha⟩
  unfold j_del
  rw [dif_pos h]
  have := j_del_mul (le_refl A) ha (Classical.choose_spec h)
  rw [this, AddSubgroup.relIndex_self]
  simp

theorem j_del_pos {A : Submodule (𝓞 E) (Fin e → E)} (hA : j_Lat A) : 0 < j_del A := by
  obtain ⟨a, ha⟩ := j_exists_basis hA
  rw [j_del_eq ha, abs_pos]
  exact ((Module.finBasis ℚ (Fin e → E)).isUnit_det a).ne_zero

theorem j_del_nested {A B : Submodule (𝓞 E) (Fin e → E)} (hA : j_Lat A) (hB : j_Lat B) (hBA : B ≤ A) :
    j_del B = ((B.toAddSubgroup.relIndex A.toAddSubgroup : ℕ) : ℚ) * j_del A := by
  obtain ⟨a, ha⟩ := j_exists_basis hA
  obtain ⟨b, hb⟩ := j_exists_basis hB
  rw [j_del_eq ha, j_del_eq hb, j_del_mul hBA ha hb]

theorem j_relIndex_pos {A B : Submodule (𝓞 E) (Fin e → E)} (hA : j_Lat A) (hB : j_Lat B) (hBA : B ≤ A) :
    0 < B.toAddSubgroup.relIndex A.toAddSubgroup := by
  have h := j_del_nested hA hB hBA
  have h1 := j_del_pos hB
  rcases Nat.eq_zero_or_pos (B.toAddSubgroup.relIndex A.toAddSubgroup) with h0 | h0
  · rw [h0] at h; simp at h; linarith
  · exact h0

theorem j_del_le {A B : Submodule (𝓞 E) (Fin e → E)} (hA : j_Lat A) (hB : j_Lat B) (hBA : B ≤ A) :
    j_del A ≤ j_del B := by
  rw [j_del_nested hA hB hBA]
  have h1 : (1 : ℚ) ≤ ((B.toAddSubgroup.relIndex A.toAddSubgroup : ℕ) : ℚ) := by
    exact_mod_cast j_relIndex_pos hA hB hBA
  nlinarith [j_del_pos hA]

theorem j_Lat_map {A : Submodule (𝓞 E) (Fin e → E)} (hA : j_Lat A) (C : (Fin e → E) ≃ₗ[E] (Fin e → E)) :
    j_Lat (A.map ((C : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars (𝓞 E))) := by
  refine ⟨hA.1.map _, ?_⟩
  have : ((A.map ((C : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars (𝓞 E)) :
      Submodule (𝓞 E) (Fin e → E)) : Set (Fin e → E)) = (C : (Fin e → E) →ₗ[E] (Fin e → E)) '' A := rfl
  rw [this, ← Submodule.map_span, hA.2, Submodule.map_top, LinearMap.range_eq_top]
  exact C.surjective

theorem j_del_map {A : Submodule (𝓞 E) (Fin e → E)} (hA : j_Lat A) (C : (Fin e → E) ≃ₗ[E] (Fin e → E)) :
    j_del (A.map ((C : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars (𝓞 E))) =
      |Algebra.norm ℚ (LinearMap.det (C : (Fin e → E) →ₗ[E] (Fin e → E)))| * j_del A := by
  obtain ⟨a, ha⟩ := j_exists_basis hA
  let Cq : (Fin e → E) ≃ₗ[ℚ] (Fin e → E) := C.restrictScalars ℚ
  have hb : j_IsBasisOf (A.map ((C : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars (𝓞 E))) (a.map Cq) := by
    unfold j_IsBasisOf at ha ⊢
    have h1 : Set.range (a.map Cq) = (Cq : (Fin e → E) →+ (Fin e → E)) '' Set.range a := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← AddMonoidHom.map_closure, ← ha]
    rfl
  rw [j_del_eq hb, j_del_eq ha]
  have h2 : ((a.map Cq : Basis _ ℚ (Fin e → E)) : Fin _ → (Fin e → E)) =
      ((C : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars ℚ) ∘ a := rfl
  rw [h2, Basis.det_comp, LinearMap.det_restrictScalars, abs_mul]

end Del

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open NumberField Module

section Chain

variable {E : Type} [Field E] [NumberField E] {e : ℕ}

def j_smulEquiv (e : ℕ) (c : E) (hc : c ≠ 0) : (Fin e → E) ≃ₗ[E] (Fin e → E) :=
  LinearEquiv.smulOfNeZero E (Fin e → E) c hc

theorem j_det_smul (c : E) (hc : c ≠ 0) :
    LinearMap.det ((j_smulEquiv e c hc : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)) = c ^ e := by
  have : ((j_smulEquiv e c hc : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)) =
      c • LinearMap.id := by
    ext x i; simp [j_smulEquiv]
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  simp

theorem j_step {L D : Submodule (𝓞 E) (Fin e → E)} (hL : j_Lat L) (hD : j_Lat D)
    (A : (Fin e → E) ≃ₗ[E] (Fin e → E)) (g : ℕ) (hg : 0 < g)
    (h : ∀ y ∈ L, ∃ d ∈ D, A y = (g : E) • d) :
    (g : ℚ) ^ (e * finrank ℚ E) * j_del D ≤
      |Algebra.norm ℚ (LinearMap.det (A : (Fin e → E) →ₗ[E] (Fin e → E)))| * j_del L := by
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  rw [← j_del_map hL A]
  have e1 := j_del_map hD (j_smulEquiv e (g : E) hgE)
  rw [j_det_smul] at e1
  have e2 : |Algebra.norm ℚ ((g : E) ^ e)| = (g : ℚ) ^ (e * finrank ℚ E) := by
    have : ((g : E)) = algebraMap ℚ E (g : ℚ) := by simp
    rw [map_pow, this, Algebra.norm_algebraMap, ← pow_mul, mul_comm, abs_of_nonneg (by positivity)]
  rw [e2] at e1
  rw [← e1]
  apply j_del_le (j_Lat_map hD _) (j_Lat_map hL _)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨d, hd, hAd⟩ := h y hy
  exact ⟨d, hd, by simpa [j_smulEquiv] using hAd.symm⟩

theorem j_chain {L₁ L₂ D₁ D₂ : Submodule (𝓞 E) (Fin e → E)} (hL₁ : j_Lat L₁) (hL₂ : j_Lat L₂)
    (hD₁ : j_Lat D₁) (hD₂ : j_Lat D₂) (A A' : (Fin e → E) ≃ₗ[E] (Fin e → E)) (g : ℕ) (hg : 0 < g)
    (h : ∀ y ∈ L₂, ∃ d ∈ D₁, A y = (g : E) • d) (h' : ∀ y ∈ L₁, ∃ d ∈ D₂, A' y = (g : E) • d) :
    ((g : ℚ) ^ (e * finrank ℚ E)) ^ 2 ≤
      |Algebra.norm ℚ (LinearMap.det (A : (Fin e → E) →ₗ[E] (Fin e → E)))| *
        |Algebra.norm ℚ (LinearMap.det (A' : (Fin e → E) →ₗ[E] (Fin e → E)))| *
        ((j_del L₁ / j_del D₁) * (j_del L₂ / j_del D₂)) := by
  have s1 := j_step hL₂ hD₁ A g hg h
  have s2 := j_step hL₁ hD₂ A' g hg h'
  have p1 := j_del_pos hD₁
  have p2 := j_del_pos hD₂
  have q1 := j_del_pos hL₁
  have q2 := j_del_pos hL₂
  have hG : (0 : ℚ) ≤ (g : ℚ) ^ (e * finrank ℚ E) := by positivity
  have hm := mul_le_mul s1 s2 (by positivity) (le_trans (by positivity) s1)
  have e1 : |Algebra.norm ℚ (LinearMap.det (A : (Fin e → E) →ₗ[E] (Fin e → E)))| *
        |Algebra.norm ℚ (LinearMap.det (A' : (Fin e → E) →ₗ[E] (Fin e → E)))| *
        ((j_del L₁ / j_del D₁) * (j_del L₂ / j_del D₂)) =
      (|Algebra.norm ℚ (LinearMap.det (A : (Fin e → E) →ₗ[E] (Fin e → E)))| * j_del L₂ *
        (|Algebra.norm ℚ (LinearMap.det (A' : (Fin e → E) →ₗ[E] (Fin e → E)))| * j_del L₁)) /
        (j_del D₁ * j_del D₂) := by
    field_simp
  rw [e1, le_div_iff₀ (by positivity)]
  calc ((g : ℚ) ^ (e * finrank ℚ E)) ^ 2 * (j_del D₁ * j_del D₂) =
      (g : ℚ) ^ (e * finrank ℚ E) * j_del D₁ * ((g : ℚ) ^ (e * finrank ℚ E) * j_del D₂) := by ring
    _ ≤ _ := hm

end Chain

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section Tr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {e : ℕ}

theorem j_dualIn_lat {M : Submodule (𝓞 E) S.V} (hM : M.FG)
    (hU : spanE S M ⊓ orth S (spanE S M) = ⊥) :
    (dualIn S M).FG ∧ spanE S (dualIn S M) = spanE S M := by
  have hL := g_comap_lattice (U := spanE S M) hM rfl
  have hd := (Formalism.HermitianLatticesTheory.dualLattice (𝓞 E) E (spanE S M) (g_hU S (spanE S M)) (g_hU_symm _)
    (g_hU_nondeg _ hU) i_star_int _ hL).1
  rw [g_dualIn_eq (U := spanE S M) rfl]
  refine ⟨hd.fg.map _, ?_⟩
  rw [g_span_map, hd.span_eq_top, Submodule.map_top, Submodule.range_subtype]

def j_iota (u : Fin e → S.V) : (Fin e → E) →ₗ[E] S.V := Fintype.linearCombination E u

theorem j_iota_apply (u : Fin e → S.V) (x : Fin e → E) : j_iota u x = ∑ i, x i • u i :=
  Fintype.linearCombination_apply E u x

theorem j_iota_range (u : Fin e → S.V) :
    LinearMap.range (j_iota u) = Submodule.span E (Set.range u) :=
  Fintype.range_linearCombination E u

theorem j_iota_inj {u : Fin e → S.V} (hu : LinearIndependent E u) : Function.Injective (j_iota u) :=
  linearIndependent_iff_injective_fintypeLinearCombination.1 hu

def j_iotaO (u : Fin e → S.V) : (Fin e → E) →ₗ[𝓞 E] S.V := (j_iota u).restrictScalars (𝓞 E)

theorem j_span_map (u : Fin e → S.V) (X : Submodule (𝓞 E) (Fin e → E)) :
    spanE S (X.map (j_iotaO u)) = (Submodule.span E (X : Set (Fin e → E))).map (j_iota u) := by
  unfold spanE
  rw [Submodule.map_span]
  rfl

theorem j_map_comap {u : Fin e → S.V} {M : Submodule (𝓞 E) S.V}
    (h : spanE S M = Submodule.span E (Set.range u)) : (M.comap (j_iotaO u)).map (j_iotaO u) = M := by
  rw [Submodule.map_comap_eq, inf_eq_right]
  intro x hx
  have : x ∈ LinearMap.range (j_iota u) := by
    rw [j_iota_range, ← h]; exact Submodule.subset_span hx
  exact this

theorem j_comap_lat {u : Fin e → S.V} (hu : LinearIndependent E u) {M : Submodule (𝓞 E) S.V} (hM : M.FG)
    (h : spanE S M = Submodule.span E (Set.range u)) : j_Lat (M.comap (j_iotaO u)) := by
  refine ⟨?_, ?_⟩
  · apply Submodule.fg_of_fg_map_injective (j_iotaO u) (j_iota_inj hu)
    rw [j_map_comap h]; exact hM
  · apply Submodule.map_injective_of_injective (j_iota_inj hu)
    rw [← j_span_map, j_map_comap h, h, Submodule.map_top, j_iota_range]

omit [StarRing E] in
theorem j_Lat_inf {A B : Submodule (𝓞 E) (Fin e → E)} (hA : j_Lat A) (hB : j_Lat B) : j_Lat (A ⊓ B) := by
  refine ⟨g_fg_le hA.1 inf_le_left, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, hn, hnx⟩ := j_exists_nat_smul_mem A (x := x) (by rw [hA.2]; trivial)
  obtain ⟨m, hm, hmx⟩ := j_exists_nat_smul_mem B (x := x) (by rw [hB.2]; trivial)
  have h1 : (n * m) • x ∈ A ⊓ B := by
    refine ⟨?_, ?_⟩
    · rw [mul_comm, mul_smul]; exact A.toAddSubmonoid.nsmul_mem hnx m
    · rw [mul_smul]; exact B.toAddSubmonoid.nsmul_mem hmx n
  have h0 : ((n * m : ℕ) : E) ≠ 0 := by exact_mod_cast (Nat.mul_pos hn hm).ne'
  have : x = ((n * m : ℕ) : E)⁻¹ • ((n * m) • x) := by
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ h0, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem j_idx_map {u : Fin e → S.V} (hu : LinearIndependent E u) (A D : Submodule (𝓞 E) (Fin e → E)) :
    g_idx (A.map (j_iotaO u)) (D.map (j_iotaO u)) = D.toAddSubgroup.relIndex A.toAddSubgroup :=
  AddSubgroup.relIndex_map_map_of_injective (f := (j_iotaO u).toAddMonoidHom) D.toAddSubgroup
    A.toAddSubgroup (j_iota_inj hu)

theorem j_genIdx_map {u : Fin e → S.V} (hu : LinearIndependent E u) {A B : Submodule (𝓞 E) (Fin e → E)}
    (hA : j_Lat A) (hB : j_Lat B) :
    genIdx S (A.map (j_iotaO u)) (B.map (j_iotaO u)) = (j_del B : ℝ) / (j_del A : ℝ) := by
  have hD := j_Lat_inf hA hB
  have sp : ∀ X : Submodule (𝓞 E) (Fin e → E), j_Lat X →
      spanE S (X.map (j_iotaO u)) = LinearMap.range (j_iota u) := by
    intro X hX
    rw [j_span_map, hX.2, Submodule.map_top]
  rw [g_genIdx_via (D := (A ⊓ B).map (j_iotaO u)) (hA.1.map _) (hB.1.map _)
    (Submodule.map_mono inf_le_left) (Submodule.map_mono inf_le_right)
    (g_Comm_of_span (hA.1.map _) (by rw [sp A hA, sp _ hD]))
    (g_Comm_of_span (hB.1.map _) (by rw [sp B hB, sp _ hD])), j_idx_map hu, j_idx_map hu]
  have e1 := j_del_nested hA hD inf_le_left
  have e2 := j_del_nested hB hD inf_le_right
  have pA : (0 : ℝ) < (j_del A : ℝ) := by exact_mod_cast j_del_pos hA
  have pB : (0 : ℝ) < (j_del B : ℝ) := by exact_mod_cast j_del_pos hB
  have pD : (0 : ℝ) < (j_del (A ⊓ B) : ℝ) := by exact_mod_cast j_del_pos hD
  have e1' : (j_del (A ⊓ B) : ℝ) =
      (((A ⊓ B).toAddSubgroup.relIndex A.toAddSubgroup : ℕ) : ℝ) * (j_del A : ℝ) := by exact_mod_cast e1
  have e2' : (j_del (A ⊓ B) : ℝ) =
      (((A ⊓ B).toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) * (j_del B : ℝ) := by exact_mod_cast e2
  have r1 : (((A ⊓ B).toAddSubgroup.relIndex A.toAddSubgroup : ℕ) : ℝ) = (j_del (A ⊓ B) : ℝ) / (j_del A : ℝ) := by
    rw [e1']; field_simp
  have r2 : (((A ⊓ B).toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) = (j_del (A ⊓ B) : ℝ) / (j_del B : ℝ) := by
    rw [e2']; field_simp
  rw [r1, r2]
  field_simp

theorem j_genIdx_dual {u : Fin e → S.V} (hu : LinearIndependent E u) {M : Submodule (𝓞 E) S.V} (hM : M.FG)
    (h : spanE S M = Submodule.span E (Set.range u)) (hU : spanE S M ⊓ orth S (spanE S M) = ⊥) :
    j_Lat (M.comap (j_iotaO u)) ∧ j_Lat ((dualIn S M).comap (j_iotaO u)) ∧
    genIdx S (dualIn S M) M =
      (j_del (M.comap (j_iotaO u)) : ℝ) / (j_del ((dualIn S M).comap (j_iotaO u)) : ℝ) := by
  obtain ⟨d1, d2⟩ := j_dualIn_lat hM hU
  have l1 := j_comap_lat hu hM h
  have l2 := j_comap_lat hu d1 (d2.trans h)
  refine ⟨l1, l2, ?_⟩
  rw [← j_genIdx_map hu l2 l1, j_map_comap h, j_map_comap (d2.trans h)]

end Tr

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Module

section Arch

theorem j_hadamard2 (e : ℕ) (K : Matrix (Fin e) (Fin e) ℂ) (h : ∀ j, ∑ i, ‖K i j‖ ^ 2 ≤ 4) :
    ‖K.det‖ ^ 2 ≤ 4 ^ e := by
  have h1 := Formalism.HadamardInequality.P.hadamard_inequality_holds e K.transpose
  rw [Matrix.det_transpose] at h1
  simp only [Matrix.transpose_apply] at h1
  refine h1.trans ?_
  calc ∏ j : Fin e, ∑ i, ‖K i j‖ ^ 2 ≤ ∏ _j : Fin e, (4 : ℝ) :=
        Finset.prod_le_prod (fun j _ => Finset.sum_nonneg fun i _ => by positivity) (fun j _ => h j)
    _ = 4 ^ e := by simp

variable {E : Type} [Field E] [StarRing E]

theorem j_arch (τ : E →+* ℂ) (hτ : ∀ x : E, τ (star x) = starRingEnd ℂ (τ x)) {e : ℕ}
    (a c : Fin e → E) (ra rc : Fin e → ℝ) (ha : ∀ i, τ (a i) = (ra i : ℂ)) (hc : ∀ i, τ (c i) = (rc i : ℂ))
    (pa : ∀ i, 0 < ra i) (pc : ∀ i, 0 < rc i) (B : Matrix (Fin e) (Fin e) E)
    (hb : ∀ (x : Fin e → E) (j : Fin e), ‖τ (∑ i, star (x i) * B i j)‖ ≤
      2 * Real.sqrt (∑ i, ‖τ (x i)‖ ^ 2 * ra i) * Real.sqrt (rc j)) :
    ‖τ B.det‖ ^ 2 ≤ 4 ^ e * (∏ i, ra i) * ∏ j, rc j := by

  have hcol : ∀ j, ∑ i, ‖τ (B i j)‖ ^ 2 / ra i ≤ 4 * rc j := by
    intro j
    have ha0 : ∀ i, a i ≠ 0 := by
      intro i h0
      have := ha i
      rw [h0, map_zero] at this
      have h1 : (ra i : ℂ) ≠ 0 := by exact_mod_cast (pa i).ne'
      exact h1 this.symm
    have h := hb (fun i => B i j / a i) j
    set σ : ℝ := ∑ i, ‖τ (B i j)‖ ^ 2 / ra i with hσ
    have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun i _ => div_nonneg (by positivity) (pa i).le
    have e1 : τ (∑ i, star (B i j / a i) * B i j) = (σ : ℂ) := by
      rw [map_sum, hσ]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, hτ, map_div₀, ha, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div,
        mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    have e2 : ∑ i, ‖τ (B i j / a i)‖ ^ 2 * ra i = σ := by
      rw [hσ]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_div₀, ha, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pa i)]
      have := (pa i).ne'
      field_simp
    rw [e1, e2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ0] at h
    by_contra hlt
    rw [not_le] at hlt
    have hσpos : 0 < σ := lt_trans (by have := pc j; positivity) hlt
    have h2 : σ ^ 2 ≤ (2 * Real.sqrt σ * Real.sqrt (rc j)) ^ 2 := pow_le_pow_left₀ hσ0 h 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hσ0, Real.sq_sqrt (pc j).le] at h2
    nlinarith

  let K : Matrix (Fin e) (Fin e) ℂ :=
    Matrix.diagonal (fun i => ((Real.sqrt (ra i))⁻¹ : ℂ)) * B.map τ *
      Matrix.diagonal (fun j => ((Real.sqrt (rc j))⁻¹ : ℂ))
  have hK : ∀ i j, K i j = ((Real.sqrt (ra i))⁻¹ : ℂ) * τ (B i j) * ((Real.sqrt (rc j))⁻¹ : ℂ) := by
    intro i j
    simp [K, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hKcol : ∀ j, ∑ i, ‖K i j‖ ^ 2 ≤ 4 := by
    intro j
    have : ∑ i, ‖K i j‖ ^ 2 = (∑ i, ‖τ (B i j)‖ ^ 2 / ra i) / rc j := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [hK, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, inv_pow, inv_pow,
        Real.sq_sqrt (pa i).le, Real.sq_sqrt (pc j).le]
      field_simp
    rw [this, div_le_iff₀ (pc j)]
    exact hcol j
  have hdet := j_hadamard2 e K hKcol
  have hKdet : K.det = (∏ i, ((Real.sqrt (ra i))⁻¹ : ℂ)) * τ B.det * ∏ j, ((Real.sqrt (rc j))⁻¹ : ℂ) := by
    simp only [K, Matrix.det_mul, Matrix.det_diagonal]
    rw [RingHom.map_det]
    rfl
  rw [hKdet, norm_mul, norm_mul, norm_prod, norm_prod, mul_pow, mul_pow] at hdet
  have n1 : (∏ i, ‖((Real.sqrt (ra i))⁻¹ : ℂ)‖) ^ 2 = (∏ i, ra i)⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (pa i).le]
  have n2 : (∏ i, ‖((Real.sqrt (rc i))⁻¹ : ℂ)‖) ^ 2 = (∏ i, rc i)⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (pc i).le]
  rw [n1, n2] at hdet
  have P1 : 0 < ∏ i, ra i := Finset.prod_pos fun i _ => pa i
  have P2 : 0 < ∏ i, rc i := Finset.prod_pos fun i _ => pc i
  have : ‖τ B.det‖ ^ 2 = ((∏ i, ra i)⁻¹ * ‖τ B.det‖ ^ 2 * (∏ i, rc i)⁻¹) * ((∏ i, ra i) * ∏ j, rc j) := by
    field_simp
  rw [this, mul_assoc (4 ^ e : ℝ)]
  exact mul_le_mul_of_nonneg_right hdet (by positivity)

end Arch

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section Norm

variable {E : Type} [Field E] [NumberField E]

theorem j_norm_prod (x : E) : ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ∏ τ : E →+* ℂ, ‖τ x‖ := by
  have h := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [norm_prod] at h
  have e1 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
    simp
  rw [← e1, h]
  exact (Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun τ : E →+* ℂ => ‖τ x‖)
    (fun σ : E →ₐ[ℚ] ℂ => ‖σ x‖) (fun τ => rfl)).symm

def j_matEquiv {e : ℕ} (M : Matrix (Fin e) (Fin e) E) (h : M.det ≠ 0) : (Fin e → E) ≃ₗ[E] (Fin e → E) :=
  LinearMap.equivOfDetNeZero (Matrix.toLin' M) (by rwa [LinearMap.det_toLin'])

theorem j_matEquiv_coe {e : ℕ} (M : Matrix (Fin e) (Fin e) E) (h : M.det ≠ 0) :
    ((j_matEquiv M h : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)) = Matrix.toLin' M := by
  ext x i
  rfl

theorem j_matEquiv_apply {e : ℕ} (d : Fin e → E) (B : Matrix (Fin e) (Fin e) E)
    (h : (Matrix.diagonal d * B).det ≠ 0) (y : Fin e → E) (i : Fin e) :
    j_matEquiv (Matrix.diagonal d * B) h y i = d i * ∑ j, B i j * y j := by
  have : j_matEquiv (Matrix.diagonal d * B) h y = Matrix.toLin' (Matrix.diagonal d * B) y := rfl
  rw [this, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.diagonal_mul, mul_assoc]

end Norm

section Main

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {e : ℕ}

theorem j_hT_iota {u : Fin e → S.V} (hou : ∀ i j, i ≠ j → S.hT (u i) (u j) = 0) (x y : Fin e → E) :
    S.hT (j_iota u x) (j_iota u y) = ∑ i, star (x i) * S.hT (u i) (u i) * y i := by
  rw [j_iota_apply, j_iota_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
  · rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    simp only [starRingEnd_apply]
    ring
  · intro i _ hi
    rw [map_smulₛₗ, LinearMap.smul_apply, hou i j hi, smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem j_orth_nondeg {u : Fin e → S.V} (hou : ∀ i j, i ≠ j → S.hT (u i) (u j) = 0)
    (ha : ∀ i, S.hT (u i) (u i) ≠ 0) :
    Submodule.span E (Set.range u) ⊓ orth S (Submodule.span E (Set.range u)) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨h1, h2⟩
  rw [SetLike.mem_coe, ← j_iota_range] at h1
  obtain ⟨x, rfl⟩ := h1
  have hx : x = 0 := by
    funext i
    have h3 := c_mem_orth.1 h2 (u i) (Submodule.subset_span ⟨i, rfl⟩)
    have h4 : u i = j_iota u (Pi.single i 1) := by
      rw [j_iota_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [h4, j_hT_iota hou, Finset.sum_eq_single i] at h3
    · simpa [ha i] using h3
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hx, map_zero]
  exact zero_mem _

theorem j_incl {u w : Fin e → S.V} (hou : ∀ i j, i ≠ j → S.hT (u i) (u j) = 0)
    (ha : ∀ i, S.hT (u i) (u i) ≠ 0) {L₁ L₂ : Submodule (𝓞 E) S.V}
    (hs₁ : spanE S L₁ = Submodule.span E (Set.range u)) (B : Matrix (Fin e) (Fin e) E) (g : ℕ) (hg : 0 < g)
    (hint : ∀ x y : Fin e → E, j_iota u x ∈ L₁ → j_iota w y ∈ L₂ →
      ∃ o : 𝓞 E, ∑ i, star (x i) * ∑ j, B i j * y j = (g : E) * (o : E))
    (hd : (Matrix.diagonal (fun i => (S.hT (u i) (u i))⁻¹) * B).det ≠ 0) :
    ∀ y ∈ L₂.comap (j_iotaO w), ∃ d ∈ (dualIn S L₁).comap (j_iotaO u),
      j_matEquiv (Matrix.diagonal (fun i => (S.hT (u i) (u i))⁻¹) * B) hd y = (g : E) • d := by
  intro y hy
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  refine ⟨(g : E)⁻¹ • j_matEquiv _ hd y, ?_, by rw [smul_smul, mul_inv_cancel₀ hgE, one_smul]⟩
  show j_iota u _ ∈ dualIn S L₁
  refine g_mem_dualIn.2 ⟨?_, ?_⟩
  · intro v hv
    have hv' : v ∈ LinearMap.range (j_iota u) := by
      rw [j_iota_range, ← hs₁]; exact Submodule.subset_span hv
    obtain ⟨x, rfl⟩ := hv'
    obtain ⟨o, ho⟩ := hint x y hv hy
    refine ⟨o, ?_⟩
    rw [j_hT_iota hou]
    have : ∑ i, star (x i) * S.hT (u i) (u i) *
        ((g : E)⁻¹ • j_matEquiv (Matrix.diagonal (fun i => (S.hT (u i) (u i))⁻¹) * B) hd y) i =
        (g : E)⁻¹ * ∑ i, star (x i) * ∑ j, B i j * y j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Pi.smul_apply, j_matEquiv_apply, smul_eq_mul]
      have := ha i
      field_simp
    rw [this, ho]
    field_simp
  · rw [hs₁, ← j_iota_range]
    exact ⟨_, rfl⟩

end Main

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section Main

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {e : ℕ}

theorem j_norm_ne {u : Fin e → S.V} (hS : StarConj E) (hpu : ∀ (τ : E →+* ℂ) i, 0 < nrm S τ (u i)) (i : Fin e) :
    S.hT (u i) (u i) ≠ 0 := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  intro h
  have h1 := c_nrm_real hS τ (u i)
  rw [h, map_zero] at h1
  have h2 : (nrm S τ (u i) : ℂ) ≠ 0 := by exact_mod_cast (hpu τ i).ne'
  exact h2 h1.symm

theorem j_factor (hS : StarConj E) {u w : Fin e → S.V}
    (hpu : ∀ (τ : E →+* ℂ) i, 0 < nrm S τ (u i)) (hpw : ∀ (τ : E →+* ℂ) i, 0 < nrm S τ (w i))
    (B : Matrix (Fin e) (Fin e) E)
    (hbd : ∀ (τ : E →+* ℂ) (x : Fin e → E) (j : Fin e), ‖τ (∑ i, star (x i) * B i j)‖ ≤
      2 * Real.sqrt (∑ i, ‖τ (x i)‖ ^ 2 * nrm S τ (u i)) * Real.sqrt (nrm S τ (w j))) (τ : E →+* ℂ) :
    ‖τ (Matrix.diagonal (fun i => (S.hT (u i) (u i))⁻¹) * B).det‖ *
      ‖τ (Matrix.diagonal (fun i => (S.hT (w i) (w i))⁻¹) * B.conjTranspose).det‖ ≤ 4 ^ e := by
  have h := j_arch τ (hS τ) (fun i => S.hT (u i) (u i)) (fun i => S.hT (w i) (w i))
    (fun i => nrm S τ (u i)) (fun i => nrm S τ (w i)) (fun i => c_nrm_real hS τ (u i))
    (fun i => c_nrm_real hS τ (w i)) (hpu τ) (hpw τ) B (hbd τ)
  have P1 : 0 < ∏ i, nrm S τ (u i) := Finset.prod_pos fun i _ => hpu τ i
  have P2 : 0 < ∏ i, nrm S τ (w i) := Finset.prod_pos fun i _ => hpw τ i
  have n1 : ∀ v : Fin e → S.V, (∀ i, 0 < nrm S τ (v i)) →
      ‖τ (∏ i, (S.hT (v i) (v i))⁻¹)‖ = (∏ i, nrm S τ (v i))⁻¹ := by
    intro v hv
    rw [map_prod, norm_prod, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_inv₀, c_nrm_real hS, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hv i)]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Matrix.det_conjTranspose,
    map_mul, map_mul, norm_mul, norm_mul, n1 u (hpu τ), n1 w (hpw τ), hS τ, RCLike.norm_conj]
  have : (∏ i, nrm S τ (u i))⁻¹ * ‖τ B.det‖ * ((∏ i, nrm S τ (w i))⁻¹ * ‖τ B.det‖) =
      ‖τ B.det‖ ^ 2 / ((∏ i, nrm S τ (u i)) * ∏ i, nrm S τ (w i)) := by
    field_simp
  rw [this, div_le_iff₀ (by positivity), ← mul_assoc]
  exact h

theorem j_main_abs (hS : StarConj E) {u w : Fin e → S.V}
    (hou : ∀ i j, i ≠ j → S.hT (u i) (u j) = 0) (how : ∀ i j, i ≠ j → S.hT (w i) (w j) = 0)
    (hpu : ∀ (τ : E →+* ℂ) i, 0 < nrm S τ (u i)) (hpw : ∀ (τ : E →+* ℂ) i, 0 < nrm S τ (w i))
    {L₁ L₂ : Submodule (𝓞 E) S.V} (hL₁ : L₁.FG) (hL₂ : L₂.FG)
    (hs₁ : spanE S L₁ = Submodule.span E (Set.range u)) (hs₂ : spanE S L₂ = Submodule.span E (Set.range w))
    (B : Matrix (Fin e) (Fin e) E) (hB : B.det ≠ 0) (g : ℕ) (hg : 0 < g)
    (hint : ∀ x y : Fin e → E, j_iota u x ∈ L₁ → j_iota w y ∈ L₂ →
      ∃ o : 𝓞 E, ∑ i, star (x i) * ∑ j, B i j * y j = (g : E) * (o : E))
    (hbd : ∀ (τ : E →+* ℂ) (x : Fin e → E) (j : Fin e), ‖τ (∑ i, star (x i) * B i j)‖ ≤
      2 * Real.sqrt (∑ i, ‖τ (x i)‖ ^ 2 * nrm S τ (u i)) * Real.sqrt (nrm S τ (w j))) :
    (g : ℝ) ^ (e * finrank ℚ E) ≤ 2 ^ (e * finrank ℚ E) * latDet S L₁ * latDet S L₂ := by
  have ha := j_norm_ne hS hpu
  have hc := j_norm_ne hS hpw
  have hlu : LinearIndependent E u :=
    LinearMap.linearIndependent_of_isOrthoᵢ (B := S.hT) (LinearMap.isOrthoᵢ_def.2 hou) ha
  have hlw : LinearIndependent E w :=
    LinearMap.linearIndependent_of_isOrthoᵢ (B := S.hT) (LinearMap.isOrthoᵢ_def.2 how) hc
  have hU₁ : spanE S L₁ ⊓ orth S (spanE S L₁) = ⊥ := by rw [hs₁]; exact j_orth_nondeg hou ha
  have hU₂ : spanE S L₂ ⊓ orth S (spanE S L₂) = ⊥ := by rw [hs₂]; exact j_orth_nondeg how hc
  obtain ⟨l1, d1, X1⟩ := j_genIdx_dual hlu hL₁ hs₁ hU₁
  obtain ⟨l2, d2, X2⟩ := j_genIdx_dual hlw hL₂ hs₂ hU₂
  have hdA : (Matrix.diagonal (fun i => (S.hT (u i) (u i))⁻¹) * B).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (ha i)) hB
  have hdA' : (Matrix.diagonal (fun i => (S.hT (w i) (w i))⁻¹) * B.conjTranspose).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (hc i)) (star_ne_zero.2 hB)
  have hint' : ∀ y x : Fin e → E, j_iota w y ∈ L₂ → j_iota u x ∈ L₁ →
      ∃ o : 𝓞 E, ∑ j, star (y j) * ∑ i, B.conjTranspose j i * x i = (g : E) * (o : E) := by
    intro y x hy hx
    obtain ⟨o, ho⟩ := hint x y hx hy
    obtain ⟨o', ho'⟩ := i_star_int o
    refine ⟨o', ?_⟩
    have key : ∑ j, star (y j) * ∑ i, B.conjTranspose j i * x i =
        star (∑ i, star (x i) * ∑ j, B i j * y j) := by
      simp only [star_sum, star_mul', star_star, Matrix.conjTranspose_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [key, ho, star_mul', star_natCast]
    congr 1
    exact ho'.symm
  have hch := j_chain l1 l2 d1 d2 (j_matEquiv _ hdA) (j_matEquiv _ hdA') g hg
    (j_incl hou ha hs₁ B g hg hint hdA) (j_incl how hc hs₂ B.conjTranspose g hg hint' hdA')
  rw [j_matEquiv_coe, j_matEquiv_coe, LinearMap.det_toLin', LinearMap.det_toLin'] at hch
  have hchR : ((g : ℝ) ^ (e * finrank ℚ E)) ^ 2 ≤
      ((|Algebra.norm ℚ (Matrix.diagonal (fun i => (S.hT (u i) (u i))⁻¹) * B).det| : ℚ) : ℝ) *
        ((|Algebra.norm ℚ (Matrix.diagonal (fun i => (S.hT (w i) (w i))⁻¹) * B.conjTranspose).det| : ℚ) : ℝ) *
        (genIdx S (dualIn S L₁) L₁ * genIdx S (dualIn S L₂) L₂) := by
    rw [X1, X2]
    exact_mod_cast hch
  have hν : ((|Algebra.norm ℚ (Matrix.diagonal (fun i => (S.hT (u i) (u i))⁻¹) * B).det| : ℚ) : ℝ) *
      ((|Algebra.norm ℚ (Matrix.diagonal (fun i => (S.hT (w i) (w i))⁻¹) * B.conjTranspose).det| : ℚ) : ℝ) ≤
      4 ^ (e * finrank ℚ E) := by
    rw [j_norm_prod, j_norm_prod, ← Finset.prod_mul_distrib]
    calc _ ≤ ∏ _τ : E →+* ℂ, (4 : ℝ) ^ e :=
          Finset.prod_le_prod (fun τ _ => by positivity) (fun τ _ => j_factor hS hpu hpw B hbd τ)
      _ = 4 ^ (e * finrank ℚ E) := by
          rw [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card E ℂ, ← pow_mul]
  have permutedRowProductSplitSum : 0 ≤ genIdx S (dualIn S L₁) L₁ := by
    rw [X1]; exact div_nonneg (by exact_mod_cast (j_del_pos l1).le) (by exact_mod_cast (j_del_pos d1).le)
  have permutedRowProductSplit : 0 ≤ genIdx S (dualIn S L₂) L₂ := by
    rw [X2]; exact div_nonneg (by exact_mod_cast (j_del_pos l2).le) (by exact_mod_cast (j_del_pos d2).le)
  have h2 : ((g : ℝ) ^ (e * finrank ℚ E)) ^ 2 ≤
      4 ^ (e * finrank ℚ E) * (genIdx S (dualIn S L₁) L₁ * genIdx S (dualIn S L₂) L₂) :=
    hchR.trans (mul_le_mul_of_nonneg_right hν (mul_nonneg permutedRowProductSplitSum permutedRowProductSplit))
  have h3 := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul permutedRowProductSplitSum] at h3
  have h4 : Real.sqrt ((4 : ℝ) ^ (e * finrank ℚ E)) = 2 ^ (e * finrank ℚ E) := by
    have : ∀ N : ℕ, (4 : ℝ) ^ N = (2 ^ N) ^ 2 := fun N => by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this, Real.sqrt_sq (by positivity)]
  rw [h4, ← mul_assoc] at h3
  exact h3

end Main

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section Orth

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem j_exists_orth : ∀ (n : ℕ) (P : Submodule E S.V), finrank E P = n →
    (∀ x ∈ P, x ≠ 0 → S.hT x x ≠ 0) →
    ∃ u : Fin n → S.V, (∀ i j, i ≠ j → S.hT (u i) (u j) = 0) ∧ (∀ i, u i ≠ 0) ∧ (∀ i, u i ∈ P) ∧
      Submodule.span E (Set.range u) = P := by
  intro n
  induction n with
  | zero =>
    intro P hP _
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    rw [Submodule.finrank_eq_zero] at hP
    rw [hP]
    simp
  | succ n ih =>
    intro P hP han
    have hne : P ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hP
      omega
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hxx := han x hxP hx0
    set P' : Submodule E S.V := P ⊓ orth S (Submodule.span E {x}) with hP'
    have hsup : Submodule.span E {x} ⊔ P' = P := by
      apply le_antisymm
      · exact sup_le ((Submodule.span_singleton_le_iff_mem x P).2 hxP) inf_le_left
      · intro y hy
        have hdec : y = (S.hT x y / S.hT x x) • x + (y - (S.hT x y / S.hT x x) • x) := by abel
        rw [hdec]
        refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) ⟨?_, ?_⟩
        · exact P.sub_mem hy (P.smul_mem _ hxP)
        · rw [SetLike.mem_coe, c_mem_orth]
          intro v hv
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
          rw [map_smulₛₗ, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, smul_eq_mul]
          have : S.hT x y - S.hT x y / S.hT x x * S.hT x x = 0 := by field_simp; ring
          rw [this, mul_zero]
    have hinf : Submodule.span E {x} ⊓ P' = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨h1, h2⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 h1
      have h3 := c_mem_orth.1 h2.2 x (Submodule.mem_span_singleton_self x)
      rw [map_smul, smul_eq_mul] at h3
      have hc : c = 0 := by
        rcases mul_eq_zero.1 h3 with h | h
        · exact h
        · exact absurd h hxx
      rw [hc, zero_smul]
      exact zero_mem _
    have hdim : finrank E P' = n := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span E {x}) P'
      rw [hsup, hinf, finrank_bot, finrank_span_singleton hx0, hP] at h
      omega
    obtain ⟨u', o', z', m', s'⟩ := ih P' hdim (fun y hy => han y hy.1)
    have hxu : ∀ j, S.hT x (u' j) = 0 := fun j =>
      c_mem_orth.1 (m' j).2 x (Submodule.mem_span_singleton_self x)
    refine ⟨Fin.cons x u', ?_, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j' => simpa using hxu j'
      | succ i' =>
        induction j using Fin.cases with
        | zero => simpa using c_symm0 (hxu i')
        | succ j' => simpa using o' i' j' (fun h => hij (by rw [h]))
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · simpa using hx0
      · simpa using z' i'
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · simpa using hxP
      · simpa using (m' i').1
    · rw [Fin.range_cons, Submodule.span_insert, s', hsup]

end Orth

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section J8

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem j_split {Hs Θ : Submodule E S.V} (hΘ : Θ ≤ Hs) (han : ∀ x ∈ Hs, S.hT x x = 0 → x = 0) :
    Θ ⊔ (Hs ⊓ orth S Θ) = Hs ∧ Θ ⊓ (Hs ⊓ orth S Θ) = ⊥ := by
  have haniso : Θ ⊓ orth S Θ = ⊥ := h_aniso_nd han hΘ
  refine ⟨?_, ?_⟩
  · rw [inf_comm, ← sup_inf_assoc_of_le _ hΘ, c_sup_orth_top Θ haniso, top_inf_eq]
  · rw [eq_bot_iff, ← haniso]
    exact fun x hx => ⟨hx.1, hx.2.2⟩

theorem j_finrank_Q {Hs Θ : Submodule E S.V} (hΘ : Θ ≤ Hs) (han : ∀ x ∈ Hs, S.hT x x = 0 → x = 0) :
    finrank E ↥(Hs ⊓ orth S Θ) + finrank E Θ = finrank E Hs := by
  obtain ⟨e1, e2⟩ := j_split hΘ han
  have := Submodule.finrank_sup_add_finrank_inf_eq Θ (Hs ⊓ orth S Θ)
  rw [e1, e2, finrank_bot] at this
  omega

theorem j_Pr_lat {Hs Θ : Submodule E S.V} (hΘ : Θ ≤ Hs) (han : ∀ x ∈ Hs, S.hT x x = 0 → x = 0)
    {L : Submodule (𝓞 E) S.V} (hfg : L.FG) (hspan : spanE S L = Hs) :
    (h_Pr L Hs Θ).FG ∧ spanE S (h_Pr L Hs Θ) = Hs ⊓ orth S Θ := by
  obtain ⟨hsum, hdisj⟩ := j_split hΘ han
  have hdisj' : (Hs ⊓ orth S Θ) ⊓ Θ = ⊥ := by rw [inf_comm]; exact hdisj
  have hSpH : Hs ⊓ orth S Θ ≤ Hs := inf_le_left
  have sM : spanE S (L ⊓ toO S Θ) = Θ := h_span_inf (by rw [hspan]; exact hΘ)
  have sN : spanE S (L ⊓ toO S (Hs ⊓ orth S Θ)) = Hs ⊓ orth S Θ := h_span_inf (by rw [hspan]; exact hSpH)
  have fN : (L ⊓ toO S (Hs ⊓ orth S Θ)).FG := g_fg_le hfg inf_le_left
  have hNP : L ⊓ toO S (Hs ⊓ orth S Θ) ≤ h_Pr L Hs Θ := fun x hx => ⟨Submodule.mem_sup_left hx.1, hx.2⟩
  have sMN : spanE S ((L ⊓ toO S Θ) ⊔ (L ⊓ toO S (Hs ⊓ orth S Θ))) = Hs := by
    rw [h_span_sup, sM, sN, hsum]
  have cL : g_Comm L ((L ⊓ toO S Θ) ⊔ (L ⊓ toO S (Hs ⊓ orth S Θ))) :=
    g_Comm_of_span hfg (by rw [sMN, hspan])
  refine ⟨?_, le_antisymm (h_span_le inf_le_right) (by rw [← sN]; exact Submodule.span_mono hNP)⟩
  obtain ⟨d, hd, hdL⟩ := cL
  apply Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) S.V d) (h_smul_inj d hd)
  refine g_fg_le fN ?_
  rintro _ ⟨s, hs, rfl⟩
  show d • s ∈ L ⊓ toO S (Hs ⊓ orth S Θ)
  obtain ⟨x, hx, θ, hθ, e⟩ := Submodule.mem_sup.1 hs.1
  obtain ⟨m, hm, n, hn, e2⟩ := Submodule.mem_sup.1 (hdL x hx)
  have h1 : d • s = n := by
    apply h_sat_cancel hdisj' ((toO S (Hs ⊓ orth S Θ)).smul_mem d hs.2) hn.2 (zero_mem Θ)
      (add_mem hm.2 ((toO S Θ).smul_mem d hθ) : m + d • θ ∈ Θ)
    rw [add_zero, ← e, smul_add, ← e2]; abel
  rw [h1]; exact hn

variable {e : ℕ}

theorem j_nrm_iota (hS : StarConj E) {u : Fin e → S.V} (hou : ∀ i j, i ≠ j → S.hT (u i) (u j) = 0)
    (τ : E →+* ℂ) (x : Fin e → E) :
    nrm S τ (j_iota u x) = ∑ i, ‖τ (x i)‖ ^ 2 * nrm S τ (u i) := by
  unfold nrm
  rw [j_hT_iota hou, map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_mul, hS, c_nrm_real hS]
  have : (starRingEnd ℂ) (τ (x i)) * ((nrm S τ (u i) : ℝ) : ℂ) * τ (x i) =
      ((‖τ (x i)‖ ^ 2 * nrm S τ (u i) : ℝ) : ℂ) := by
    rw [mul_right_comm, mul_comm ((starRingEnd ℂ) (τ (x i))), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [this, Complex.ofReal_re]
  rfl

theorem j_bForm_iota_left {β : S.V ≃ₗ[E] S.V} (u : Fin e → S.V) (x : Fin e → E) (v : S.V) :
    bForm β (j_iota u x) v = ∑ i, star (x i) * bForm β (u i) v := by
  unfold bForm
  rw [j_iota_apply, map_sum, map_sum, map_sum, LinearMap.sum_apply, LinearMap.sum_apply,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hβ : β (x i • u i) = x i • β (u i) := map_smul β _ _
  rw [hβ, map_smulₛₗ, map_smulₛₗ, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  simp only [starRingEnd_apply]
  ring

theorem j_bForm_iota_right {β : S.V ≃ₗ[E] S.V} (w : Fin e → S.V) (y : Fin e → E) (v : S.V) :
    bForm β v (j_iota w y) = ∑ j, bForm β v (w j) * y j := by
  unfold bForm
  rw [j_iota_apply, map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

end J8

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section modelEmbedding

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {e : ℕ}

def j_bLin (S : HSpace E) (β : S.V ≃ₗ[E] S.V) : S.V →ₗ⋆[E] S.V →ₗ[E] E :=
  S.hT - S.hT.comp (β : S.V →ₗ[E] S.V)

theorem j_bLin_apply (β : S.V ≃ₗ[E] S.V) (x y : S.V) : j_bLin S β x y = bForm β x y := rfl

theorem j_form_left (bb : S.V →ₗ⋆[E] S.V →ₗ[E] E) (u : Fin e → S.V) (x : Fin e → E) (v : S.V) :
    bb (j_iota u x) v = ∑ i, star (x i) * bb (u i) v := by
  rw [j_iota_apply, map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  rfl

theorem j_form_right (bb : S.V →ₗ⋆[E] S.V →ₗ[E] E) (w : Fin e → S.V) (y : Fin e → E) (v : S.V) :
    bb v (j_iota w y) = ∑ j, bb v (w j) * y j := by
  rw [j_iota_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul, mul_comm]

theorem j_main_form (hS : StarConj E) {Q₁ Q₂ : Submodule E S.V} (e1 : finrank E Q₁ = e) (e2 : finrank E Q₂ = e)
    (p1 : ∀ τ : E →+* ℂ, ∀ x ∈ Q₁, x ≠ 0 → 0 < nrm S τ x)
    (p2 : ∀ τ : E →+* ℂ, ∀ x ∈ Q₂, x ≠ 0 → 0 < nrm S τ x)
    {L₁ L₂ : Submodule (𝓞 E) S.V} (f1 : L₁.FG) (f2 : L₂.FG) (sp1 : spanE S L₁ = Q₁) (sp2 : spanE S L₂ = Q₂)
    (bb : S.V →ₗ⋆[E] S.V →ₗ[E] E) (hnd : ∀ y ∈ Q₂, (∀ x ∈ Q₁, bb x y = 0) → y = 0) (g : ℕ) (hg : 0 < g)
    (hint : ∀ x ∈ L₁, ∀ y ∈ L₂, ∃ o : 𝓞 E, bb x y = (g : E) * (o : E))
    (hbd : ∀ τ : E →+* ℂ, ∀ x ∈ Q₁, ∀ y ∈ Q₂,
      ‖τ (bb x y)‖ ≤ 2 * Real.sqrt (nrm S τ x) * Real.sqrt (nrm S τ y)) :
    (g : ℝ) ^ (e * finrank ℚ E) ≤ 2 ^ (e * finrank ℚ E) * latDet S L₁ * latDet S L₂ := by
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have an : ∀ (Q : Submodule E S.V), (∀ τ : E →+* ℂ, ∀ x ∈ Q, x ≠ 0 → 0 < nrm S τ x) →
      ∀ x ∈ Q, x ≠ 0 → S.hT x x ≠ 0 := by
    intro Q hQ x hx hx0 h
    have := hQ τ₀ x hx hx0
    simp [nrm, h] at this
  obtain ⟨u, hou, hu0, huQ, hus⟩ := j_exists_orth e Q₁ e1 (an Q₁ p1)
  obtain ⟨w, how, hw0, hwQ, hws⟩ := j_exists_orth e Q₂ e2 (an Q₂ p2)
  have hpu : ∀ (τ : E →+* ℂ) i, 0 < nrm S τ (u i) := fun τ i => p1 τ (u i) (huQ i) (hu0 i)
  have hpw : ∀ (τ : E →+* ℂ) i, 0 < nrm S τ (w i) := fun τ i => p2 τ (w i) (hwQ i) (hw0 i)
  have hιu : ∀ x, j_iota u x ∈ Q₁ := fun x => by rw [← hus, ← j_iota_range]; exact ⟨x, rfl⟩
  have hιw : ∀ y, j_iota w y ∈ Q₂ := fun y => by rw [← hws, ← j_iota_range]; exact ⟨y, rfl⟩
  have hlw : LinearIndependent E w :=
    LinearMap.linearIndependent_of_isOrthoᵢ (B := S.hT) (LinearMap.isOrthoᵢ_def.2 how) (j_norm_ne hS hpw)
  have hsum : ∀ (x y : Fin e → E),
      ∑ i, star (x i) * ∑ j, (Matrix.of fun i j => bb (u i) (w j)) i j * y j =
        bb (j_iota u x) (j_iota w y) := by
    intro x y
    rw [j_form_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [j_form_right]
    rfl
  refine j_main_abs hS hou how hpu hpw f1 f2 (sp1.trans hus.symm) (sp2.trans hws.symm)
    (Matrix.of fun i j => bb (u i) (w j)) ?_ g hg ?_ ?_
  · intro h0
    obtain ⟨y, hy0, hBy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hall : ∀ X ∈ Q₁, bb X (j_iota w y) = 0 := by
      intro X hX
      have hq' : X ∈ LinearMap.range (j_iota u) := by rw [j_iota_range, hus]; exact hX
      obtain ⟨x, rfl⟩ := hq'
      rw [← hsum]
      apply Finset.sum_eq_zero
      intro i _
      have := congrFun hBy i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      rw [this, mul_zero]
    have hY0 : j_iota w y = 0 := hnd _ (hιw y) hall
    exact hy0 (j_iota_inj hlw (by rw [hY0, map_zero]))
  · intro x y hx hy
    rw [hsum]
    exact hint _ hx _ hy
  · intro τ x j
    have : ∑ i, star (x i) * (Matrix.of fun i j => bb (u i) (w j)) i j = bb (j_iota u x) (w j) :=
      (j_form_left bb u x (w j)).symm
    rw [this, ← j_nrm_iota hS hou τ x]
    exact hbd τ _ (hιu x) _ (hwQ j)

end modelEmbedding

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module Formalism.HermitianLatticesTheory

section J9

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {Λ : Submodule (𝓞 E) S.V} {T T' : E} {g : ℕ}
variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem j_bForm_add_left (x y v : S.V) : bForm β (x + y) v = bForm β x v + bForm β y v := by
  simp only [bForm, map_add, LinearMap.add_apply]; ring

theorem j_b_bound_H (hS : StarConj E) (hP : IsPair Λ F F' F'' β g) (hU' : HU Λ F F') (hU'' : HU Λ F F'')
    (hPos : PosX F) (hPos'' : PosX F'') (τ : E →+* ℂ) {X Y : S.V} (hX : X ∈ Hp Λ F F')
    (hY : Y ∈ Hp Λ F F'') :
    ‖τ (bForm β X Y)‖ ≤ 2 * Real.sqrt (nrm S τ X) * Real.sqrt (nrm S τ Y) := by
  have c1 := c_CS hS hPos τ (c_Hp_orthXplus Λ hU' hX) (c_Hp_orthXplus Λ hU'' hY)
  have c2 := c_CS hS hPos'' τ (c_beta_orthXplus hP (c_Hp_orthXplus' Λ hU' hX)) (c_Hp_orthXplus' Λ hU'' hY)
  have n3 : nrm S τ (β X) = nrm S τ X := by unfold nrm; rw [c_iso hP]
  rw [n3] at c2
  unfold bForm
  rw [map_sub]
  calc ‖τ (S.hT X Y) - τ (S.hT (β X) Y)‖ ≤ ‖τ (S.hT X Y)‖ + ‖τ (S.hT (β X) Y)‖ := norm_sub_le _ _
    _ ≤ 2 * Real.sqrt (nrm S τ X) * Real.sqrt (nrm S τ Y) := by linarith

theorem j_detB_gen (hS : StarConj E) (hΛ : Submodule.IsLattice E Λ) (hUni : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hg : 0 < g) (hz : IsLift Λ F) (hz' : IsLift Λ F') (hz'' : IsLift Λ F'') (hG' : Gval F F' ≠ 0)
    (hG'' : Gval F F'' ≠ 0) (hP : IsPair Λ F F' F'' β g) (hPos : PosX F) (hPos'' : PosX F'')
    {W : Submodule E S.V} {k : ℕ} (hW : WHypG F W k) (h1 : finrank E (Hp Λ F F') = k - 1)
    (h2 : finrank E (Hp Λ F F'') = k - 1) (hnd : BNondeg Λ F F' F'' β) :
    (g : ℝ) ^ ((s0 Λ F F' F'' β k - 1) * finrank ℚ E) ≤
      2 ^ ((s0 Λ F F' F'' β k - 1) * finrank ℚ E) *
        latDet S (Psi Λ F F' F'' β W (La Λ g F F')) * latDet S (Psi Λ F F' F'' β W (La Λ g F F'')) := by
  have hU' : HU Λ F F' := a_HU Λ hΛ F F' hz.2 hz'.2
  have hU'' : HU Λ F F'' := a_HU Λ hΛ F F'' hz.2 hz''.2
  have hN' : HNd F F' := a_HNd F F' hG'
  have hN'' : HNd F F'' := a_HNd F F'' hG''
  have s' := (g_span_La Λ F F' g hΛ (c_Thp_le_La hU')).1
  have s'' := (g_span_La Λ F F'' g hΛ (c_Thp_le_La hU'')).1
  have hL' : La Λ g F F' ≤ toO S (Hp Λ F F') := s' ▸ g_le_span _
  have hL'' : La Λ g F F'' ≤ toO S (Hp Λ F F'') := s'' ▸ g_le_span _
  have an' := h_Hp_aniso hU' hN' hPos
  have an'' := h_Hp_aniso hU'' hN'' hPos
  have D' := h_latDet_Psi (Λ := Λ) (F' := F') (F'' := F'') (β := β) hW (c_Hp_orthXplus Λ hU')
    (h_Hp_inf_X hU' hN') c_Th_le_Hp rfl hL'
  have D'' := h_latDet_Psi (Λ := Λ) (F' := F') (F'' := F'') (β := β) hW (c_Hp_orthXplus Λ hU'')
    (h_Hp_inf_X hU'' hN'') c_Th''_le_Hp c_Th''_sup_X hL''
  rw [D', D'']
  obtain ⟨f1, sp1⟩ := j_Pr_lat (c_Th_le_Hp (β := β) (F'' := F'')) an' (h_La_fg hΛ hg hz hz' hG') s'
  obtain ⟨f2, sp2⟩ := j_Pr_lat (c_Th''_le_Hp (β := β) (F' := F')) an'' (h_La_fg hΛ hg hz hz'' hG'') s''
  have q1 := j_finrank_Q (c_Th_le_Hp (β := β) (F'' := F'')) an'
  have q2 := j_finrank_Q (c_Th''_le_Hp (β := β) (F' := F')) an''
  have eTh : finrank E (Th'' Λ F F' F'' β) = finrank E (Th Λ F F' F'' β) := by
    rw [c_finrank_Th'' hU' hN', ← c_finrank_Th hU'' hN'']
  have e1 : finrank E ↥(Hp Λ F F' ⊓ orth S (Th Λ F F' F'' β)) = s0 Λ F F' F'' β k - 1 := by
    unfold s0; omega
  have e2 : finrank E ↥(Hp Λ F F'' ⊓ orth S (Th'' Λ F F' F'' β)) = s0 Λ F F' F'' β k - 1 := by
    unfold s0; omega
  obtain ⟨u, hou, hu0, huQ, hus⟩ := j_exists_orth _ _ e1 (fun x hx hx0 h => hx0 (an' x hx.1 h))
  obtain ⟨w, how, hw0, hwQ, hws⟩ := j_exists_orth _ _ e2 (fun x hx hx0 h => hx0 (an'' x hx.1 h))
  have hpu : ∀ (τ : E →+* ℂ) i, 0 < nrm S τ (u i) :=
    fun τ i => radical_positive_each_embedding Λ hU' hN' hPos τ (u i) (huQ i).1 (hu0 i)
  have hpw : ∀ (τ : E →+* ℂ) i, 0 < nrm S τ (w i) :=
    fun τ i => radical_positive_each_embedding Λ hU'' hN'' hPos τ (w i) (hwQ i).1 (hw0 i)
  have hιu : ∀ x, j_iota u x ∈ Hp Λ F F' ⊓ orth S (Th Λ F F' F'' β) := fun x => by
    rw [← hus, ← j_iota_range]; exact ⟨x, rfl⟩
  have hιw : ∀ y, j_iota w y ∈ Hp Λ F F'' ⊓ orth S (Th'' Λ F F' F'' β) := fun y => by
    rw [← hws, ← j_iota_range]; exact ⟨y, rfl⟩
  have hlw : LinearIndependent E w :=
    LinearMap.linearIndependent_of_isOrthoᵢ (B := S.hT) (LinearMap.isOrthoᵢ_def.2 how) (j_norm_ne hS hpw)
  have hsum : ∀ (x y : Fin (s0 Λ F F' F'' β k - 1) → E),
      ∑ i, star (x i) * ∑ j, (Matrix.of fun i j => bForm β (u i) (w j)) i j * y j =
        bForm β (j_iota u x) (j_iota w y) := by
    intro x y
    rw [j_bForm_iota_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [j_bForm_iota_right]
    rfl
  refine j_main_abs hS hou how hpu hpw f1 f2 (sp1.trans hus.symm) (sp2.trans hws.symm)
    (Matrix.of fun i j => bForm β (u i) (w j)) ?_ g hg ?_ ?_
  ·
    intro h0
    obtain ⟨y, hy0, hBy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hYH := (hιw y).1
    have hall : ∀ X ∈ Hp Λ F F', bForm β X (j_iota w y) = 0 := by
      intro X hX
      rw [← (j_split (c_Th_le_Hp (β := β) (F'' := F'')) an').1] at hX
      obtain ⟨θ, hθ, q, hq, rfl⟩ := Submodule.mem_sup.1 hX
      have hq' : q ∈ LinearMap.range (j_iota u) := by rw [j_iota_range, hus]; exact hq
      obtain ⟨x, rfl⟩ := hq'
      have v1 : bForm β θ (j_iota w y) = 0 :=
        c_b_vanish_left hθ (c_Hp_orthX Λ hU'' hYH) (c_Hp_orthX' Λ hU'' hYH)
      have v2 : bForm β (j_iota u x) (j_iota w y) = 0 := by
        rw [← hsum]
        apply Finset.sum_eq_zero
        intro i _
        have := congrFun hBy i
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
        rw [this, mul_zero]
      rw [j_bForm_add_left, v1, v2, add_zero]
    have hYT : j_iota w y ∈ Th'' Λ F F' F'' β := hnd.2 _ hYH hall
    have hY0 : j_iota w y = 0 := an'' _ hYH (c_mem_orth.1 (hιw y).2 _ hYT)
    exact hy0 (j_iota_inj hlw (by rw [hY0, map_zero]))
  ·
    intro x y hx hy
    obtain ⟨x', hx', θ, hθ, ex⟩ := Submodule.mem_sup.1 hx.1
    obtain ⟨x'', hx'', θ'', hθ'', ey⟩ := Submodule.mem_sup.1 hy.1
    obtain ⟨o, ho⟩ := c_b_gO hP (c_int_of_unimod hUni) x' hx' x'' hx''
    refine ⟨o, ?_⟩
    rw [hsum, ← ho]
    have a1 : x' = j_iota u x - θ := by rw [← ex]; abel
    have a2 : x'' = j_iota w y - θ'' := by rw [← ey]; abel
    have v1 : bForm β θ x'' = 0 := c_b_vanish_left hθ (c_La_orthX Λ g hx'') (c_La_orthX' Λ g hx'')
    have v2 : bForm β (j_iota u x) θ'' = 0 :=
      c_b_vanish_right hP hθ'' (c_Hp_orthX Λ hU' (hιu x).1) (c_Hp_orthX' Λ hU' (hιu x).1)
    have t1 : bForm β x' x'' = bForm β (j_iota u x) x'' - bForm β θ x'' := by
      rw [← c_bForm_sub_left, ← a1]
    have t2 : bForm β (j_iota u x) x'' = bForm β (j_iota u x) (j_iota w y) - bForm β (j_iota u x) θ'' := by
      rw [← c_bForm_sub_right, ← a2]
    rw [t1, t2, v1, v2]
    ring
  ·
    intro τ x j
    have : ∑ i, star (x i) * (Matrix.of fun i j => bForm β (u i) (w j)) i j = bForm β (j_iota u x) (w j) :=
      (j_bForm_iota_left u x (w j)).symm
    rw [this, ← j_nrm_iota hS hou τ x]
    exact j_b_bound_H hS hP hU' hU'' hPos hPos'' τ (hιu x).1 (hwQ j).1

end J9

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem j_finrank (D : D7) : finrank ℚ D.host.E = 2 * D.R.f := by
  have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord :=
    D.host.finrank_cmField
  rw [h1]
  unfold Ranks.f Ranks.n
  ring

theorem j_DetBBound (D : D7) (u : D.what₂.Word) (T' : ℕ) (Λ : VanishingOnXAndXPlusGluing.LatS D) (F : VanishingOnXAndXPlusGluing.FlS D (Tu D u))
    (F' F'' : VanishingOnXAndXPlusGluing.FlS D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (hF : FixedHyp D Λ F) (hPr : PrimeHyp D u T') (hT' : IsTerm Λ (gS D) F F') (hT'' : IsTerm Λ (gS D) F F'')
    (hP : IsPair Λ F F' F'' β (gS D)) (W : Submodule D.host.E (hS D).V) (hW : WHyp D F W)
    (hnd : BNondeg Λ F F' F'' β) : DetBBound D Λ (gS D) F F' F'' β W := by
  have h0 : 0 < Tu D u := lt_of_lt_of_le (by norm_num) hPr.2.1
  have h0' : 0 < T' := lt_of_lt_of_le (by norm_num) hPr.2.2.2.1
  have hg : 0 < gS D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have h := j_detB_gen (p_starConj D) hF.1 hF.2.1 hg hF.2.2.1 hT'.1 hT''.1 hT'.2.2 hT''.2.2 hP
    (p_posX D _ h0 F) (p_posX D _ h0' F'') hW
    (a_rankHp_k Λ hF.1 F F' hF.2.2.1.2 hT'.1.2 hT'.2.2 D.R.k (p_rankV D))
    (a_rankHp_k Λ hF.1 F F'' hF.2.2.1.2 hT''.1.2 hT''.2.2 D.R.k (p_rankV D)) hnd
  rw [j_finrank] at h
  unfold DetBBound
  have e1 : 2 * D.R.f * (s0 Λ F F' F'' β D.R.k - 1) = (s0 Λ F F' F'' β D.R.k - 1) * (2 * D.R.f) := by ring
  have e2 : (4 : ℝ) ^ ((s0 Λ F F' F'' β D.R.k - 1) * D.R.f) =
      2 ^ ((s0 Λ F F' F'' β D.R.k - 1) * (2 * D.R.f)) := by
    have : (s0 Λ F F' F'' β D.R.k - 1) * (2 * D.R.f) = 2 * ((s0 Λ F F' F'' β D.R.k - 1) * D.R.f) := by ring
    have gen : ∀ N : ℕ, (4 : ℝ) ^ N = 2 ^ (2 * N) := fun N => by rw [pow_mul]; norm_num
    rw [this, gen]
  rw [e1, e2]
  exact h

theorem j_thmA_nondeg (D : D7) (h1 : VanishingOnXAndXPlusGluing.Conclusion1 D) (hA2 : VanishingOnXAndXPlusGluing.HyperplaneRank D)
    (u : D.what₂.Word) (T' : ℕ) (Λ : VanishingOnXAndXPlusGluing.LatS D) (F : VanishingOnXAndXPlusGluing.FlS D (Tu D u))
    (F' F'' : VanishingOnXAndXPlusGluing.FlS D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (hF : FixedHyp D Λ F) (hPr : PrimeHyp D u T') (hT' : IsTerm Λ (gS D) F F') (hT'' : IsTerm Λ (gS D) F F'')
    (hP : IsPair Λ F F' F'' β (gS D)) (hs : 2 ≤ s0 Λ F F' F'' β D.R.k) (hnd : BNondeg Λ F F' F'' β) :
    latDet (hS D) (Mlat Λ F F' F'' β (gS D)) * (iIdx Λ (gS D) F F' : ℝ) * (iIdx Λ (gS D) F F'' : ℝ) ≤
      (2 / ((gS D : ℕ) : ℝ)) ^ ((s0 Λ F F' F'' β D.R.k - 1) * D.R.f) *
        Real.sqrt (G0 Λ (gS D) F F' * G0 Λ (gS D) F F'') := by
  have h0 : 0 < Tu D u := lt_of_lt_of_le (by norm_num) hPr.2.1
  have hg : 0 < gS D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨W, hW⟩ := h_existsW D (Tu D u) F h0
  exact m_thmA_nondeg D Λ (gS D) hg F F' F'' β W (h1 u T' Λ F F' hF hPr hT') (h1 u T' Λ F F'' hF hPr hT'')
    (hA2 u T' Λ F F' F'' β hF hPr hT' hT'' hP hs W hW)
    (j_DetBBound D u T' Λ F F' F'' β hF hPr hT' hT'' hP W hW hnd)

end D7

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ThmADeg (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (T' : ℕ) (Λ : VanishingOnXAndXPlusGluing.LatS D) (F : VanishingOnXAndXPlusGluing.FlS D (Tu D u)) (F' F'' : VanishingOnXAndXPlusGluing.FlS D T')
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → 2 ≤ s0 Λ F F' F'' β D.R.k → ¬ BNondeg Λ F F' F'' β →
      latDet (hS D) (Mlat Λ F F' F'' β (gS D)) * (iIdx Λ (gS D) F F' : ℝ) * (iIdx Λ (gS D) F F'' : ℝ) ≤
        (2 / ((gS D : ℕ) : ℝ)) ^ ((s0 Λ F F' F'' β D.R.k - 2) * D.R.f) *
          Real.sqrt (G0 Λ (gS D) F F' * G0 Λ (gS D) F F'') * (((Tu D u : ℕ) : ℝ) ^ D.R.f)⁻¹ *
          placeProd (fun τ : D.host.E →+* ℂ =>
            onePlusChSh (Tu D u) T' F F' τ * onePlusChSh (Tu D u) T' F F'' τ)

theorem z_thmA_nondeg (D : D7) (u : D.what₂.Word) (T' : ℕ) (Λ : VanishingOnXAndXPlusGluing.LatS D) (F : VanishingOnXAndXPlusGluing.FlS D (Tu D u))
    (F' F'' : VanishingOnXAndXPlusGluing.FlS D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (hF : FixedHyp D Λ F) (hPr : PrimeHyp D u T') (hT' : IsTerm Λ (gS D) F F') (hT'' : IsTerm Λ (gS D) F F'')
    (hP : IsPair Λ F F' F'' β (gS D)) (hs : 2 ≤ s0 Λ F F' F'' β D.R.k) (hnd : BNondeg Λ F F' F'' β) :
    latDet (hS D) (Mlat Λ F F' F'' β (gS D)) * (iIdx Λ (gS D) F F' : ℝ) * (iIdx Λ (gS D) F F'' : ℝ) ≤
      (2 / ((gS D : ℕ) : ℝ)) ^ ((s0 Λ F F' F'' β D.R.k - 1) * D.R.f) *
        Real.sqrt (G0 Λ (gS D) F F' * G0 Λ (gS D) F F'') :=
  j_thmA_nondeg D (lattice_lemma_one D) (radical_second_claim D) u T' Λ F F' F'' β hF hPr hT' hT'' hP hs hnd

theorem z_ThmAIneq_of_deg (D : D7) (h : ThmADeg D) : ThmAIneq D :=
  fun u T' Λ F F' F'' β hF hPr hT' hT'' hP hs =>
    ⟨z_thmA_nondeg D u T' Λ F F' F'' β hF hPr hT' hT'' hP hs,
      h u T' Λ F F' F'' β hF hPr hT' hT'' hP hs⟩

theorem theorem_A_of_degenerate_case (D : D7) (h : ThmADeg D) : VanishingOnXAndXPlusGluing.PointsLemma D :=
  theorem_A_of_inequalities D (z_ThmAIneq_of_deg D h)

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section K1

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {T T' : E}

def k_IsZc (F : LFlag S r T) (F'' : LFlag S r T') (f : S.V →ₗ[E] E) : Prop :=
  f F.fl.z = 1 ∧ (∀ x ∈ Xsp F, f x = 0) ∧ (∀ x ∈ Xplus F'', f x = 0)

theorem k_zc_exists {F : LFlag S r T} {F'' : LFlag S r T'} (hI : HInd F F'') :
    ∃ f : S.V →ₗ[E] E, k_IsZc F F'' f := by
  unfold HInd at hI
  let f₀ : Submodule.span E (Set.range (Sum.elim (frame F) (frame F''))) →ₗ[E] E :=
    (Finsupp.lapply (Sum.inl (Fin.last r))) ∘ₗ hI.repr
  obtain ⟨f, hf⟩ := LinearMap.exists_extend f₀
  have key : ∀ i, f (Sum.elim (frame F) (frame F'') i) = if i = Sum.inl (Fin.last r) then 1 else 0 := by
    intro i
    have h1 : f (Sum.elim (frame F) (frame F'') i) =
        f₀ ⟨Sum.elim (frame F) (frame F'') i, Submodule.subset_span ⟨i, rfl⟩⟩ := by
      rw [← hf]; rfl
    rw [h1]
    show (hI.repr ⟨Sum.elim (frame F) (frame F'') i, _⟩) (Sum.inl (Fin.last r)) = _
    rw [hI.repr_eq_single i _ rfl, Finsupp.single_apply]
  refine ⟨f, ?_, ?_, ?_⟩
  · have := key (Sum.inl (Fin.last r))
    simpa [a_frame_last] using this
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have := key (Sum.inl a.castSucc)
      rw [Sum.elim_inl, a_frame_castSucc] at this
      rw [this, if_neg]
      intro h
      exact (Fin.castSucc_lt_last a).ne (Sum.inl.inj h)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  · intro x hx
    rw [← a_span_frame] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have := key (Sum.inr a)
      rw [Sum.elim_inr] at this
      rw [this, if_neg (by simp)]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]

def k_al (f : S.V →ₗ[E] E) (β : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] E :=
  f ∘ₗ (LinearMap.id - (β : S.V →ₗ[E] S.V))

theorem k_al_apply (f : S.V →ₗ[E] E) (β : S.V ≃ₗ[E] S.V) (x : S.V) : k_al f β x = f (x - β x) := rfl

theorem k_zc_sg {F : LFlag S r T} {F'' : LFlag S r T'} {f : S.V →ₗ[E] E} (hf : k_IsZc F F'' f)
    (hz : F.zt = F.fl.z) (hz'' : F''.zt = F''.fl.z) {y y'' : S.V} {al al' : E}
    (h : SgRel F F'' y y'' al al') : f (y - y'') = al := by
  obtain ⟨x, hx, x'', hx'', e⟩ := h
  rw [e, hz, hz'', map_add, map_add, map_smul, hf.1, hf.2.1 x hx,
    hf.2.2 (al' • F''.fl.z + x'') (add_mem (Submodule.smul_mem _ _ (c_z_mem_Xplus F''))
      (c_X_le_Xplus F'' hx''))]
  simp

variable {Λ : Submodule (𝓞 E) S.V} {g : ℕ}
variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem k_bForm (x x'' : S.V) : bForm β x x'' = S.hT (x - β x) x'' := by
  simp [bForm, map_sub, LinearMap.sub_apply]

theorem k_rad_sub (hU'' : HU Λ F F'') (hG'' : Gval F F'' ≠ 0) {x : S.V} (hx : x ∈ radL Λ F F' F'' β) :
    x - β x ∈ UUE Λ F F'' := by
  have hc := double_span_is_compl_orth F F'' hG''
  have h2 : orth S (orth S (UUE Λ F F'')) = UUE Λ F F'' := by
    rw [hU'']; exact d_orth_orth _ hc
  rw [← h2, c_mem_orth]
  intro x'' hx''
  have := (c_mem_radL.1 hx).2 x'' hx''
  rw [k_bForm] at this
  exact c_symm0 this

theorem k_decomp (hP : IsPair Λ F F' F'' β g) (hU' : HU Λ F F') (hU'' : HU Λ F F'')
    (hG'' : Gval F F'' ≠ 0) {x : S.V} (hx : x ∈ radL Λ F F' F'' β) :
    ∃ th ∈ Hp Λ F F'', ∃ y ∈ Ylift Λ F F'', ∃ y'' ∈ Ylift' Λ F F'', x = th + y ∧ β x = th + y'' := by
  have hc := double_span_is_compl_orth F F'' hG''
  have htop : x ∈ U2 F F'' ⊔ orth S (U2 F F'') := by rw [hc.sup_eq_top]; trivial
  obtain ⟨y, hy, th, hth, e⟩ := Submodule.mem_sup.1 htop
  have hyU : y ∈ UUE Λ F F'' := by rw [hU'']; exact hy
  have hthH : th ∈ Hp Λ F F'' := by unfold Hp; rw [hU'']; exact hth
  have hxH : x ∈ Hp Λ F F' := (c_mem_radL.1 hx).1
  have hy1 : y ∈ orth S (Xplus F) := by
    have : y = x - th := by rw [← e]; abel
    rw [this]
    exact sub_mem (c_Hp_orthXplus Λ hU' hxH) (c_Hp_orthXplus Λ hU'' hthH)
  refine ⟨th, hthH, y, ⟨hyU, hy1⟩, β x - th, ⟨?_, ?_⟩, by rw [← e]; abel, by abel⟩
  · have : β x - th = y - (x - β x) := by rw [← e]; abel
    rw [this]
    exact sub_mem hyU (k_rad_sub hU'' hG'' hx)
  · exact sub_mem (c_beta_orthXplus hP (c_Hp_orthXplus' Λ hU' hxH)) (c_Hp_orthXplus' Λ hU'' hthH)

theorem k_nrm_add (τ : E →+* ℂ) {a b : S.V} (h : S.hT a b = 0) :
    nrm S τ (a + b) = nrm S τ a + nrm S τ b := by
  have h' := c_symm0 h
  simp [nrm, map_add, LinearMap.add_apply, h, h']

end K1

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section K2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {T T' : ℕ}

theorem k_kappa_eq (F : LFlag S r (T : E)) (F'' : LFlag S r (T' : E)) (τ : E →+* ℂ) :
    onePlusChSh T T' F F'' τ = chSh T T' F F'' τ + invSh T T' F F'' τ := by
  unfold onePlusChSh chSh invSh
  split_ifs
  · simp
  · rw [add_comm (1 : ℝ), add_div]

theorem k_chSh_nonneg (F : LFlag S r (T : E)) (F'' : LFlag S r (T' : E)) (τ : E →+* ℂ) :
    0 ≤ chSh T T' F F'' τ := by
  unfold chSh
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem k_invSh_nonneg (F : LFlag S r (T : E)) (F'' : LFlag S r (T' : E)) (τ : E →+* ℂ) :
    0 ≤ invSh T T' F F'' τ := by
  unfold invSh
  split_ifs
  · exact le_rfl
  · exact div_nonneg zero_le_one (Real.sqrt_nonneg _)

theorem k_kappa_ge (hc : StarConj E) (hT : 0 < T) (hT' : 0 < T') (F : LFlag S r (T : E))
    (F'' : LFlag S r (T' : E)) (hz : F.zt = F.fl.z) (hz'' : F''.zt = F''.fl.z) (hG : Gval F F'' ≠ 0)
    (hPos : PosX F) (τ : E →+* ℂ) : 1 ≤ onePlusChSh T T' F F'' τ := by
  have h1 := b_ch_sh_one hc hT hT' F F'' hz hz'' hG hPos τ
  have h2 := k_chSh_nonneg F F'' τ
  have h3 := k_invSh_nonneg F F'' τ
  rw [k_kappa_eq]
  nlinarith

variable {Λ : Submodule (𝓞 E) S.V} {g : ℕ}
variable {F : LFlag S r (T : E)} {F' F'' : LFlag S r (T' : E)} {β : S.V ≃ₗ[E] S.V}

theorem k_real (Tr A B C Sx n a : ℝ) (hT : 0 ≤ Tr) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hS : 0 ≤ Sx)
    (hn : 0 ≤ n) (ha0 : 0 ≤ a) (ha : a ≤ A + B) (h1 : Tr * A ^ 2 = C ^ 2 * n) (h2 : Tr * B ^ 2 = Sx ^ 2 * n) :
    Tr * a ^ 2 ≤ (C + Sx) ^ 2 * n := by
  have h3 : (Tr * A * B) ^ 2 = (C * Sx * n) ^ 2 := by
    calc (Tr * A * B) ^ 2 = (Tr * A ^ 2) * (Tr * B ^ 2) := by ring
      _ = (C * Sx * n) ^ 2 := by rw [h1, h2]; ring
  have h4 : Tr * A * B = C * Sx * n :=
    (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 h3
  have h5 : a ^ 2 ≤ (A + B) ^ 2 := pow_le_pow_left₀ ha0 ha 2
  calc Tr * a ^ 2 ≤ Tr * (A + B) ^ 2 := mul_le_mul_of_nonneg_left h5 hT
    _ = Tr * A ^ 2 + Tr * B ^ 2 + 2 * (Tr * A * B) := by ring
    _ = (C + Sx) ^ 2 * n := by rw [h1, h2, h4]; ring

theorem k_normal (_hc : StarConj E) (hΛ : Submodule.IsLattice E Λ) (hz : F.zt = F.fl.z)
    (hz' : F'.zt = F'.fl.z) (hz'' : F''.zt = F''.fl.z) (hG'' : Gval F F'' ≠ 0)
    (hP : IsPair Λ F F' F'' β g) (hPos : PosX F) {x : S.V} (hx : x ∈ radL Λ F F' F'' β) :
    ∃ th ∈ Hp Λ F F'', ∃ y ∈ Ylift Λ F F'', ∃ y'' ∈ Ylift' Λ F F'', x = th + y ∧ β x = th + y'' ∧
      ∀ τ : E →+* ℂ, nrm S τ y = nrm S τ y'' ∧ nrm S τ y ≤ nrm S τ x := by
  have hU' := a_HU Λ hΛ F F' hz hz'
  have hU'' := a_HU Λ hΛ F F'' hz hz''
  obtain ⟨th, hth, y, hy, y'', hy'', e1, e2⟩ := k_decomp hP hU' hU'' hG'' hx
  refine ⟨th, hth, y, hy, y'', hy'', e1, e2, fun τ => ?_⟩
  have o1 : S.hT th y = 0 := c_symm0 (c_mem_orth.1 hth y hy.1)
  have o2 : S.hT th y'' = 0 := c_symm0 (c_mem_orth.1 hth y'' hy''.1)
  have n1 : nrm S τ x = nrm S τ th + nrm S τ y := by rw [e1]; exact k_nrm_add τ o1
  have n2 : nrm S τ (β x) = nrm S τ th + nrm S τ y'' := by rw [e2]; exact k_nrm_add τ o2
  have n3 : nrm S τ (β x) = nrm S τ x := by unfold nrm; rw [c_iso hP]
  have n4 : 0 ≤ nrm S τ th := p_nonneg hPos τ (c_Hp_orthXplus Λ hU'' hth)
  constructor <;> linarith

theorem k_arch (hc : StarConj E) (hΛ : Submodule.IsLattice E Λ) (hT : 0 < T) (hT' : 0 < T')
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hz'' : F''.zt = F''.fl.z) (hG'' : Gval F F'' ≠ 0)
    (hP : IsPair Λ F F' F'' β g) (hPos : PosX F) (hPos'' : PosX F'') {f : S.V →ₗ[E] E}
    (hf : k_IsZc F F'' f) {x : S.V} (hx : x ∈ radL Λ F F' F'' β) (τ : E →+* ℂ) :
    (T : ℝ) * ‖τ (k_al f β x)‖ ^ 2 ≤ onePlusChSh T T' F F'' τ ^ 2 * nrm S τ x := by
  obtain ⟨th, hth, y, hy, y'', hy'', e1, e2, hn⟩ := k_normal hc hΛ hz hz' hz'' hG'' hP hPos hx
  obtain ⟨hn1, hn2⟩ := hn τ
  obtain ⟨p1, hp1, -⟩ := lemma_two_unique_pair Λ hΛ F F'' hz hz'' hG'' y hy 0 (zero_mem _)
  obtain ⟨p2, hp2, -⟩ := lemma_two_unique_pair Λ hΛ F F'' hz hz'' hG'' 0 (zero_mem _) y'' hy''
  have v1 := (lemma_two_norm_scaling hc hT hT' F F'' hz hz'' hG'' hPos τ hy.2 (zero_mem _) hp1).1
  have v2 := (lemma_two_norm_scaling_right hc hT hT' F F'' hz hz'' hG'' hPos'' τ (zero_mem _) hy''.2 hp2).1
  have a1 := k_zc_sg hf hz hz'' hp1
  have a2 := k_zc_sg hf hz hz'' hp2
  have ea : k_al f β x = p1.1 + p2.1 := by
    rw [k_al_apply, ← a1, ← a2, ← map_add]
    congr 1
    rw [e2]
    nth_rewrite 1 [e1]
    abel
  have hny : 0 ≤ nrm S τ y := p_nonneg hPos τ hy.2
  rw [← hn1] at v2
  have key := k_real (T : ℝ) ‖τ p1.1‖ ‖τ p2.1‖ (chSh T T' F F'' τ) (invSh T T' F F'' τ) (nrm S τ y)
    ‖τ (k_al f β x)‖ (Nat.cast_nonneg _) (norm_nonneg _) (norm_nonneg _) (k_chSh_nonneg F F'' τ)
    (k_invSh_nonneg F F'' τ) hny (norm_nonneg _) (by rw [ea, map_add]; exact norm_add_le _ _) v1 v2
  rw [k_kappa_eq]
  exact key.trans (mul_le_mul_of_nonneg_left hn2 (sq_nonneg _))

theorem k_ker (hc : StarConj E) (hΛ : Submodule.IsLattice E Λ) (hT' : 0 < T')
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hz'' : F''.zt = F''.fl.z) (hG'' : Gval F F'' ≠ 0)
    (hP : IsPair Λ F F' F'' β g) (hPos : PosX F) (hPos'' : PosX F'') {f : S.V →ₗ[E] E}
    (hf : k_IsZc F F'' f) {x : S.V} (hx : x ∈ radL Λ F F' F'' β) (h0 : k_al f β x = 0) :
    x ∈ Th Λ F F' F'' β := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hU' := a_HU Λ hΛ F F' hz hz'
  have hU'' := a_HU Λ hΛ F F'' hz hz''
  obtain ⟨th, hth, y, hy, y'', hy'', e1, e2, hn⟩ := k_normal hc hΛ hz hz' hz'' hG'' hP hPos hx
  obtain ⟨p, hp, -⟩ := lemma_two_unique_pair Λ hΛ F F'' hz hz'' hG'' y hy y'' hy''
  have a1 := k_zc_sg hf hz hz'' hp
  have exy : x - β x = y - y'' := by
    rw [e2]; nth_rewrite 1 [e1]; abel
  have hp1 : p.1 = 0 := by rw [← a1, ← exy, ← k_al_apply, h0]
  have iv := lemma_two_norm_difference hc F F'' hz hz'' τ hy.2 hy''.2 hp
  rw [(hn τ).1, hp1] at iv
  have hp2 : p.2 = 0 := by
    have hT'' : (0 : ℝ) < T' := by exact_mod_cast hT'
    have : ‖τ p.2‖ ^ 2 = 0 := by
      simp only [map_zero, norm_zero] at iv
      nlinarith
    have h3 : τ p.2 = 0 := by simpa using this
    exact (map_eq_zero τ).1 h3
  rw [hp1, hp2] at hp
  have h00 : SgRel F F'' (0 : S.V) 0 0 0 := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  have hii := lemma_two_lift_difference Λ hΛ F F'' hz hz'' hG'' y hy 0 (zero_mem _) y'' hy'' 0 (zero_mem _) 0 0 hp h00
  apply c_radL_inf_le hP hU' hU'' hPos''
  refine ⟨hx, ?_⟩
  rw [e1]
  exact Submodule.add_mem_sup hth (by simpa using hii.1)

end K2

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section K3

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {T T' : E}
variable {Λ : Submodule (𝓞 E) S.V} {g : ℕ}
variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

omit [StarRing E] in
theorem k_card_ker_range {A Q : Type} [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup Q] [Module (𝓞 E) Q]
    (π : A →ₗ[𝓞 E] Q) :
    Nat.card A = Nat.card (LinearMap.ker π) * Nat.card (LinearMap.range π) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker π),
    Nat.card_congr π.quotKerEquivRange.toEquiv]

abbrev k_O (E : Type) [Field E] [NumberField E] : Submodule (𝓞 E) E := 1

theorem k_f_UU {f : S.V →ₗ[E] E} (hf : k_IsZc F F'' f) (hz : F.zt = F.fl.z) (hz'' : F''.zt = F''.fl.z) :
    UU Λ F F'' ≤ (k_O E).comap (f.restrictScalars (𝓞 E)) := by
  unfold UU
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · intro x hx
    show f x ∈ k_O E
    rw [hf.2.1 x hx.2]; exact zero_mem _
  · rw [Submodule.span_singleton_le_iff_mem, hz]
    show f F.fl.z ∈ k_O E
    rw [hf.1]; exact Submodule.one_le.1 le_rfl
  · intro x hx
    show f x ∈ k_O E
    rw [hf.2.2 x (c_X_le_Xplus F'' hx.2)]; exact zero_mem _
  · rw [Submodule.span_singleton_le_iff_mem, hz'']
    show f F''.fl.z ∈ k_O E
    rw [hf.2.2 _ (c_z_mem_Xplus F'')]; exact zero_mem _

def k_fbar {f : S.V →ₗ[E] E} (hf : k_IsZc F F'' f) (hz : F.zt = F.fl.z) (hz'' : F''.zt = F''.fl.z) :
    BQ Λ F F'' →ₗ[𝓞 E] (E ⧸ k_O E) :=
  Submodule.liftQ _ ((k_O E).mkQ ∘ₗ (f.restrictScalars (𝓞 E)) ∘ₗ (BLat Λ F F'').subtype)
    (fun w hw => by
      rw [LinearMap.mem_ker]
      show (k_O E).mkQ (f (w : S.V)) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact k_f_UU hf hz hz'' hw)

theorem k_fbar_mk {f : S.V →ₗ[E] E} (hf : k_IsZc F F'' f) (hz : F.zt = F.fl.z) (hz'' : F''.zt = F''.fl.z)
    (w : BLat Λ F F'') :
    k_fbar (Λ := Λ) hf hz hz'' (Submodule.Quotient.mk w) = Submodule.Quotient.mk (f (w : S.V)) := rfl

theorem k_fbar_noZ {f : S.V →ₗ[E] E} (hf : k_IsZc F F'' f) (hz : F.zt = F.fl.z) (hz'' : F''.zt = F''.fl.z)
    {c : BQ Λ F F''} (hc : c ∈ noZ Λ F F'') : k_fbar (Λ := Λ) hf hz hz'' c = 0 := by
  obtain ⟨w, hw, rfl⟩ := hc
  rw [k_fbar_mk]
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 hw
  rw [← e, map_add, hf.2.1 a ha, hf.2.2 b (c_X_le_Xplus F'' hb)]
  simp

theorem k_mem_gB (hg : 0 < g) (hX : Xsp F ≤ UUE Λ F F'') (hX'' : Xsp F'' ≤ UUE Λ F F'') {w : S.V}
    (hw : w ∈ BLat Λ F F'') (hn : w ∈ NgX Λ g F F'') :
    (Submodule.Quotient.mk ⟨w, hw⟩ : BQ Λ F F'') ∈ gB Λ g F F'' := by
  unfold NgX at hn
  obtain ⟨p, hp, ξ', hξ', e1⟩ := Submodule.mem_sup.1 hn
  obtain ⟨u, hu, ξ, hξ, e2⟩ := Submodule.mem_sup.1 hp
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hu
  obtain ⟨lam, hlam, rfl⟩ := hu
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  have hglam : ((g : 𝓞 E)) • lam ∈ UUE Λ F F'' := by
    have : ((g : 𝓞 E)) • lam = w - ξ - ξ' := by rw [← e1, ← e2]; abel
    rw [this]
    exact sub_mem (sub_mem hw.2 (hX hξ.2)) (hX'' hξ'.2)
  have hlamU : lam ∈ UUE Λ F F'' := by
    have h2 : (g : E)⁻¹ • (((g : 𝓞 E)) • lam) = lam := by
      rw [← IsScalarTower.algebraMap_smul E (g : 𝓞 E) lam, smul_smul]
      simp [hgE]
    rw [← h2]
    exact (UUE Λ F F'').smul_mem _ hglam
  have key : (Submodule.Quotient.mk ⟨w, hw⟩ : BQ Λ F F'') =
      (g : 𝓞 E) • (Submodule.Quotient.mk ⟨lam, ⟨hlam, hlamU⟩⟩ : BQ Λ F F'') := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    show w - (g : 𝓞 E) • lam ∈ UU Λ F F''
    have : w - (g : 𝓞 E) • lam = ξ + ξ' := by rw [← e1, ← e2]; abel
    rw [this]
    unfold UU
    exact add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hξ)))
      (Submodule.mem_sup_left (Submodule.mem_sup_right hξ'))
  rw [key]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial

theorem k_class (hg : 0 < g) (hP : IsPair Λ F F' F'' β g) (hU'' : HU Λ F F'') (hG'' : Gval F F'' ≠ 0)
    {f : S.V →ₗ[E] E} (hf : k_IsZc F F'' f) (hz : F.zt = F.fl.z) (hz'' : F''.zt = F''.fl.z)
    {x : S.V} (hx : x ∈ La Λ g F F') (hr : x ∈ radL Λ F F' F'' β) :
    ∃ c ∈ gB Λ g F F'', k_fbar (Λ := Λ) hf hz hz'' c = Submodule.Quotient.mk (k_al f β x) := by
  obtain ⟨hX, hX''⟩ := a_X_le hU''
  obtain ⟨-, -, -, l, hl, ha, l', hl', ha', hn⟩ := m_La_mem Λ F F' g hx
  have hu : l - β l' ∈ NgX Λ g F F'' := (hP.2.2.2 l' hl' l hl).1 hn
  have hpΛ : β l' ∈ Λ := by
    have h := hP.1.2
    rw [← h]
    exact Submodule.mem_map_of_mem hl'.1
  have hb : β (x - l') ∈ Xsp F'' := c_beta_mem_X hP ha'
  have e : l - β l' = (x - β x) - (x - l) + β (x - l') := by rw [map_sub]; abel
  have hw : l - β l' ∈ BLat Λ F F'' := by
    refine ⟨sub_mem hl.1 hpΛ, ?_⟩
    show l - β l' ∈ UUE Λ F F''
    rw [e]
    exact add_mem (sub_mem (k_rad_sub hU'' hG'' hr) (hX ha)) (hX'' hb)
  refine ⟨Submodule.Quotient.mk ⟨l - β l', hw⟩, k_mem_gB hg hX hX'' hw hu, ?_⟩
  rw [k_fbar_mk]
  congr 1
  show f (l - β l') = _
  rw [e, map_add, map_sub, hf.2.1 _ ha, hf.2.2 _ (c_X_le_Xplus F'' hb), k_al_apply]
  simp

def integralPartOfModule (f : S.V →ₗ[E] E) (β : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) S.V :=
  L ⊓ (k_O E).comap ((k_al f β).restrictScalars (𝓞 E))

theorem k_count (hΛ : Submodule.IsLattice E Λ) (hg : 0 < g) (hP : IsPair Λ F F' F'' β g)
    (hz : IsLift Λ F) (hz'' : IsLift Λ F'') (hG'' : Gval F F'' ≠ 0)
    {f : S.V →ₗ[E] E} (hf : k_IsZc F F'' f) (L : Submodule (𝓞 E) S.V)
    (hL : ∀ s ∈ L, ∃ x ∈ La Λ g F F', x ∈ radL Λ F F' F'' β ∧ k_al f β s = k_al f β x) :
    iIdx Λ g F F'' * g_idx L (integralPartOfModule f β L) ≤ Nat.card (gB Λ g F F'') := by
  have hU'' := a_HU Λ hΛ F F'' hz.2 hz''.2
  have hfin : Finite (BQ Λ F F'') := m_BQ_finite Λ F F'' hΛ
  obtain ⟨φ, h1, h2, -⟩ := lemma_one_quotient_embedding hg hz hz'' (a_disj (a_HInd F F'' hG''))
    (a_X_le hU'').1 (a_X_le hU'').2
  let π : gB Λ g F F'' →ₗ[𝓞 E] (E ⧸ k_O E) :=
    (k_fbar (Λ := Λ) hf hz.2 hz''.2) ∘ₗ (gB Λ g F F'').subtype
  rw [k_card_ker_range π]
  apply Nat.mul_le_mul
  ·
    have : iIdx Λ g F F'' ≤ Nat.card (LinearMap.ker π) :=
      Nat.card_le_card_of_injective
        (fun c => (⟨φ c, LinearMap.mem_ker.2 (k_fbar_noZ hf hz.2 hz''.2 (h2 c))⟩ : LinearMap.ker π))
        (fun a b hab => h1 (congrArg Subtype.val hab))
    exact this
  ·
    have hfr : Finite (LinearMap.range π) :=
      Finite.of_surjective π.rangeRestrict π.surjective_rangeRestrict
    unfold g_idx
    apply g_card_quot_le _ (fun s : L => (⟨Submodule.Quotient.mk (k_al f β (s : S.V)), by
      obtain ⟨x, hx, hr, e⟩ := hL s s.2
      obtain ⟨c, hc, hc'⟩ := k_class hg hP hU'' hG'' hf hz.2 hz''.2 hx hr
      exact ⟨⟨c, hc⟩, by rw [e]; exact hc'⟩⟩ : LinearMap.range π))
    intro s s' hss
    have h3 : (Submodule.Quotient.mk (k_al f β (s : S.V)) : E ⧸ k_O E) =
        Submodule.Quotient.mk (k_al f β (s' : S.V)) := congrArg Subtype.val hss
    rw [Submodule.Quotient.eq] at h3
    refine ⟨(s - s').2, ?_⟩
    show k_al f β ((s : S.V) - (s' : S.V)) ∈ k_O E
    rw [map_sub]
    exact h3

end K3

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section InfinitePlaceStep

variable {E : Type} [Field E] [NumberField E]

theorem k_norm_prod (x : E) : ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ∏ τ : E →+* ℂ, ‖τ x‖ := by
  have h := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [norm_prod] at h
  have e1 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
    simp
  rw [← e1, h]
  exact (Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun τ : E →+* ℂ => ‖τ x‖)
    (fun σ : E →ₐ[ℚ] ℂ => ‖σ x‖) (fun τ => rfl)).symm

theorem k_absNorm (p : 𝓞 E) :
    ((Ideal.absNorm (Ideal.span {p}) : ℕ) : ℝ) = ∏ τ : E →+* ℂ, ‖τ (p : E)‖ := by
  rw [← k_norm_prod, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp [Nat.cast_natAbs]

variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem k_idx_cyc {v : W} (hv : v ≠ 0) (d : 𝓞 E) :
    g_idx (Submodule.span (𝓞 E) {v}) (Submodule.span (𝓞 E) {d • v}) = Ideal.absNorm (Ideal.span {d}) := by
  have hinj : ∀ o : 𝓞 E, o • v = 0 → o = 0 := by
    intro o ho
    rw [← IsScalarTower.algebraMap_smul E o v] at ho
    rcases smul_eq_zero.1 ho with h | h
    · exact (map_eq_zero_iff (algebraMap (𝓞 E) E) (IsFractionRing.injective (𝓞 E) E)).1 h
    · exact absurd h hv
  let φ : 𝓞 E →ₗ[𝓞 E] (Submodule.span (𝓞 E) {v}) :=
    LinearMap.codRestrict _ (LinearMap.toSpanSingleton (𝓞 E) W v)
      (fun o => Submodule.smul_mem _ o (Submodule.mem_span_singleton_self v))
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨o, rfl⟩
  have hφi : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro o ho
    exact hinj o (congrArg Subtype.val ho)
  let e : 𝓞 E ≃ₗ[𝓞 E] (Submodule.span (𝓞 E) {v}) := LinearEquiv.ofBijective φ ⟨hφi, hφs⟩
  have hmap : Submodule.map (e : 𝓞 E →ₗ[𝓞 E] (Submodule.span (𝓞 E) {v})) (Ideal.span {d}) =
      (Submodule.span (𝓞 E) {d • v}).comap (Submodule.span (𝓞 E) {v}).subtype := by
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨o, ho, h⟩
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 ho
      have : x = (t * d) • v := (congrArg Subtype.val h).symm
      show x ∈ Submodule.span (𝓞 E) {d • v}
      rw [this, mul_smul]
      exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _)
    · intro h
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (show x ∈ Submodule.span (𝓞 E) {d • v} from h)
      refine ⟨t * d, Ideal.mem_span_singleton'.2 ⟨t, rfl⟩, ?_⟩
      apply Subtype.ext
      show (t * d) • v = x
      rw [mul_smul, ht]
  unfold g_idx
  rw [← hmap]
  have q := Submodule.Quotient.equiv (Ideal.span {d} : Submodule (𝓞 E) (𝓞 E)) _ e rfl
  rw [← Nat.card_congr q.toEquiv]
  rfl

end InfinitePlaceStep

section FinitePlaceStep

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem k_spanE_cyc (s : S.V) : spanE S (Submodule.span (𝓞 E) {s}) = Submodule.span E {s} := by
  unfold spanE
  exact Submodule.span_span_of_tower (𝓞 E) E {s}

theorem k_Comm_cyc (v : S.V) {d : 𝓞 E} (hd : d ≠ 0) :
    g_Comm (Submodule.span (𝓞 E) {v}) (Submodule.span (𝓞 E) {d • v}) := by
  refine ⟨d, hd, fun x hx => ?_⟩
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [smul_comm]
  exact Submodule.smul_mem _ o (Submodule.mem_span_singleton_self _)

theorem k_cyc_le (v : S.V) (d : 𝓞 E) :
    Submodule.span (𝓞 E) {d • v} ≤ Submodule.span (𝓞 E) {v} := by
  rw [Submodule.span_singleton_le_iff_mem]
  exact Submodule.smul_mem _ d (Submodule.mem_span_singleton_self _)

theorem k_dual_cyc {s : S.V} (hc : S.hT s s ≠ 0) :
    dualIn S (Submodule.span (𝓞 E) {s}) = Submodule.span (𝓞 E) {(S.hT s s)⁻¹ • s} := by
  ext x
  rw [g_mem_dualIn, k_spanE_cyc]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 h2
    obtain ⟨o, ho⟩ := h1 s (Submodule.mem_span_singleton_self _)
    rw [map_smul, smul_eq_mul] at ho
    rw [Submodule.mem_span_singleton]
    refine ⟨o, ?_⟩
    rw [← IsScalarTower.algebraMap_smul E o, smul_smul]
    congr 1
    show (o : E) * _ = t
    rw [ho]
    field_simp
  · intro hx
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hx
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨o', rfl⟩ := Submodule.mem_span_singleton.1 hy
      obtain ⟨o'', ho''⟩ := (g_starInt : g_StarInt E) o'
      refine ⟨o'' * o, ?_⟩
      rw [← IsScalarTower.algebraMap_smul E o', ← IsScalarTower.algebraMap_smul E o]
      simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
      have hcc : ∀ a : E, (S.hT s s)⁻¹ * (a * S.hT s s) = a := fun a => by field_simp
      rw [hcc]
      have h2 : algebraMap (𝓞 E) E o'' = star (algebraMap (𝓞 E) E o') := ho''
      show algebraMap (𝓞 E) E (o'' * o) = _
      rw [map_mul, h2, mul_comm]
    · rw [← IsScalarTower.algebraMap_smul E o, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem k_latDet_cyc {s : S.V} (hc : S.hT s s ≠ 0) :
    latDet S (Submodule.span (𝓞 E) {s}) = Real.sqrt (∏ τ : E →+* ℂ, ‖τ (S.hT s s)‖) := by
  have hs : s ≠ 0 := by rintro rfl; simp at hc
  obtain ⟨p₀, q₀, hq, e⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (S.hT s s)
  have hq0 : q₀ ≠ 0 := nonZeroDivisors.ne_zero hq
  have hq1 : (algebraMap (𝓞 E) E q₀) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 E) E) (IsFractionRing.injective (𝓞 E) E)).2 hq0
  have hp1 : (algebraMap (𝓞 E) E p₀) ≠ 0 := by
    intro h; rw [h, zero_div] at e; exact hc e.symm
  have hp0 : p₀ ≠ 0 := by rintro rfl; simp at hp1
  have hv : (S.hT s s)⁻¹ • s ≠ 0 := smul_ne_zero (inv_ne_zero hc) hs
  have hD : p₀ • ((S.hT s s)⁻¹ • s) = q₀ • s := by
    rw [← IsScalarTower.algebraMap_smul E p₀, ← IsScalarTower.algebraMap_smul E q₀, smul_smul]
    congr 1
    rw [← e]
    field_simp
  show Real.sqrt (genIdx S (dualIn S (Submodule.span (𝓞 E) {s})) (Submodule.span (𝓞 E) {s})) = _
  congr 1
  rw [k_dual_cyc hc]
  have hvia := g_genIdx_via (S := S) (A := Submodule.span (𝓞 E) {(S.hT s s)⁻¹ • s})
    (B := Submodule.span (𝓞 E) {s}) (D := Submodule.span (𝓞 E) {q₀ • s})
    (Submodule.fg_span_singleton _) (Submodule.fg_span_singleton _)
    (by rw [← hD]; exact k_cyc_le _ _) (k_cyc_le _ _)
    (by rw [← hD]; exact k_Comm_cyc _ hp0) (k_Comm_cyc _ hq0)
  rw [hvia]
  have i1 : g_idx (Submodule.span (𝓞 E) {(S.hT s s)⁻¹ • s}) (Submodule.span (𝓞 E) {q₀ • s}) =
      Ideal.absNorm (Ideal.span {p₀}) := by rw [← hD]; exact k_idx_cyc hv p₀
  rw [i1, k_idx_cyc hs q₀, k_absNorm, k_absNorm, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro τ _
  rw [← e, map_div₀, norm_div]

end FinitePlaceStep

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section K5

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem k_rank1_real (dL dM idx i5 Nr P Kp sR : ℝ) (hdL : 0 ≤ dL) (hP : 0 < P) (hK : 0 < Kp) (hNr : 0 < Nr)
    (h1 : dM = dL * idx) (h2 : idx = i5 * Nr) (h3 : i5 ≤ P) (h4 : sR * P / Kp ≤ dM) :
    sR / (Nr * Kp) ≤ dL := by
  have h5 : dL * idx ≤ dL * (P * Nr) := by
    rw [h2]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hNr.le) hdL
  have h6 : sR * P / Kp ≤ dL * (P * Nr) := by linarith
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hK] at h6
  have h7 : sR * P ≤ (dL * (Nr * Kp)) * P := by nlinarith
  exact le_of_mul_le_mul_right h7 hP

theorem k_rank1 (hc : StarConj E) (a : S.V →ₗ[E] E) {l : Submodule E S.V} (hnd : l ⊓ orth S l = ⊥)
    (hinj : ∀ x ∈ l, a x = 0 → x = 0) (hne : l ≠ ⊥) {L : Submodule (𝓞 E) S.V} (hfg : L.FG)
    (hspan : spanE S L = l) (κ : (E →+* ℂ) → ℝ) (hκ : ∀ τ, 0 < κ τ) (Tr : ℝ) (hT : 0 < Tr)
    (harch : ∀ x ∈ l, ∀ τ : E →+* ℂ, Tr * ‖τ (a x)‖ ^ 2 ≤ κ τ ^ 2 * nrm S τ x) :
    Real.sqrt (∏ _τ : E →+* ℂ, Tr) /
      ((g_idx L (L ⊓ (k_O E).comap (a.restrictScalars (𝓞 E))) : ℝ) * ∏ τ : E →+* ℂ, κ τ) ≤ latDet S L := by
  have hLne : L ≠ ⊥ := by
    rintro rfl
    apply hne
    rw [← hspan]
    unfold spanE
    simp
  obtain ⟨s₁, hs₁, hs₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLne
  obtain ⟨p, q, hq, e⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (a s₁)
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hq1 : (algebraMap (𝓞 E) E q) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 E) E) (IsFractionRing.injective (𝓞 E) E)).2 hq0
  set s₀ : S.V := q • s₁ with hs₀def
  have hs₀L : s₀ ∈ L := L.smul_mem q hs₁
  have hs₀E : s₀ = (algebraMap (𝓞 E) E q) • s₁ := (IsScalarTower.algebraMap_smul E q s₁).symm
  have hs₀0 : s₀ ≠ 0 := by rw [hs₀E]; exact smul_ne_zero hq1 hs₁0
  have has₀ : a s₀ = algebraMap (𝓞 E) E p := by
    rw [hs₀E, map_smul, smul_eq_mul, ← e]; field_simp
  have hs₀l : s₀ ∈ l := by rw [← hspan]; exact g_le_span L hs₀L
  have hp1 : (algebraMap (𝓞 E) E p) ≠ 0 := by
    intro h; rw [h] at has₀; exact hs₀0 (hinj s₀ hs₀l has₀)
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp1
  have hnrm : ∀ τ : E →+* ℂ, 0 < nrm S τ s₀ := by
    intro τ
    have h := harch s₀ hs₀l τ
    have h1 : 0 < Tr * ‖τ (a s₀)‖ ^ 2 := by
      have : τ (a s₀) ≠ 0 := by rw [has₀]; exact (map_ne_zero τ).2 hp1
      positivity
    have h2 : 0 < κ τ ^ 2 * nrm S τ s₀ := lt_of_lt_of_le h1 h
    exact (pos_iff_pos_of_mul_pos h2).1 (by have := hκ τ; positivity)
  have hc₀ : S.hT s₀ s₀ ≠ 0 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro h
    have := hnrm τ
    simp [nrm, h] at this
  have hle : Submodule.span (𝓞 E) {s₀} ≤ L := (Submodule.span_singleton_le_iff_mem _ _).2 hs₀L
  have hrep : ∀ x ∈ l, x = (a x / algebraMap (𝓞 E) E p) • s₀ := by
    intro x hx
    have h1 : x - (a x / algebraMap (𝓞 E) E p) • s₀ ∈ l := sub_mem hx (l.smul_mem _ hs₀l)
    have h2 : a (x - (a x / algebraMap (𝓞 E) E p) • s₀) = 0 := by
      rw [map_sub, map_smul, has₀, smul_eq_mul]; field_simp; ring
    exact sub_eq_zero.1 (hinj _ h1 h2)
  have hsp : spanE S L = spanE S (Submodule.span (𝓞 E) {s₀}) := by
    rw [hspan, k_spanE_cyc]
    apply le_antisymm
    · intro x hx
      rw [hrep x hx]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · exact (Submodule.span_singleton_le_iff_mem _ _).2 hs₀l
  have hdi := g_detIndexG (S := S) g_starInt L (Submodule.span (𝓞 E) {s₀}) hle hfg hsp
    (by rw [hspan]; exact hnd)
  set L₀ : Submodule (𝓞 E) S.V := L ⊓ (k_O E).comap (a.restrictScalars (𝓞 E)) with hL₀
  have hML₀ : Submodule.span (𝓞 E) {s₀} ≤ L₀ := by
    rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨hs₀L, ?_⟩
    show a s₀ ∈ k_O E
    rw [has₀]
    exact Submodule.mem_one.2 ⟨p, rfl⟩
  have hmul := g_idx_mul hML₀ (inf_le_left : L₀ ≤ L)
  have hpos : 0 < g_idx L (Submodule.span (𝓞 E) {s₀}) := g_idx_pos hfg (g_Comm_of_span hfg (le_of_eq hsp))
  have hNr : 0 < g_idx L L₀ := by
    rcases Nat.eq_zero_or_pos (g_idx L L₀) with h | h
    · rw [h, mul_zero] at hmul; omega
    · exact h
  have hbot : Ideal.span {p} ≠ ⊥ := by simpa using hp0
  have hfinq : Finite (𝓞 E ⧸ Ideal.span {p}) := Ideal.finiteQuotientOfFreeOfNeBot _ hbot
  have h5 : g_idx L₀ (Submodule.span (𝓞 E) {s₀}) ≤ Ideal.absNorm (Ideal.span {p}) := by
    have hch : ∀ s : L₀, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = a (s : S.V) := fun s => Submodule.mem_one.1 s.2.2
    choose y hy using hch
    have := g_card_quot_le ((Submodule.span (𝓞 E) {s₀}).comap L₀.subtype)
      (fun s : L₀ => (Ideal.Quotient.mk (Ideal.span {p}) (y s))) (by
        intro s s' hss
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hss
        obtain ⟨t, ht⟩ := hss
        show (s : S.V) - (s' : S.V) ∈ Submodule.span (𝓞 E) {s₀}
        have hl1 : (s : S.V) - (s' : S.V) - t • s₀ ∈ l := by
          refine sub_mem (sub_mem ?_ ?_) ?_
          · rw [← hspan]; exact g_le_span L s.2.1
          · rw [← hspan]; exact g_le_span L s'.2.1
          · rw [← hspan]; exact g_le_span L (L.smul_mem t hs₀L)
        have hz : a ((s : S.V) - (s' : S.V) - t • s₀) = 0 := by
          rw [map_sub, map_sub, ← hy s, ← hy s', ← IsScalarTower.algebraMap_smul E t s₀, map_smul, has₀,
            smul_eq_mul, ← map_sub, ← map_mul, ht, sub_self]
        have := sub_eq_zero.1 (hinj _ hl1 hz)
        rw [this]
        exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _))
    exact this
  have hM : latDet S (Submodule.span (𝓞 E) {s₀}) = Real.sqrt (∏ τ : E →+* ℂ, nrm S τ s₀) := by
    rw [k_latDet_cyc hc₀]
    congr 1
    apply Finset.prod_congr rfl
    intro τ _
    rw [c_nrm_real hc τ s₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hnrm τ)]
  have hPpos : 0 < ∏ τ : E →+* ℂ, ‖τ (p : E)‖ :=
    Finset.prod_pos fun τ _ => norm_pos_iff.2 ((map_ne_zero τ).2 hp1)
  have hKpos : 0 < ∏ τ : E →+* ℂ, κ τ := Finset.prod_pos fun τ _ => hκ τ
  have hlow : Real.sqrt (∏ _τ : E →+* ℂ, Tr) * (∏ τ : E →+* ℂ, ‖τ (p : E)‖) / (∏ τ : E →+* ℂ, κ τ) ≤
      latDet S (Submodule.span (𝓞 E) {s₀}) := by
    rw [hM]
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, mul_pow, Real.sq_sqrt (Finset.prod_nonneg fun _ _ => hT.le), ← Finset.prod_pow,
      ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    apply Finset.prod_le_prod
    · intro τ _
      have := hκ τ
      positivity
    · intro τ _
      have h := harch s₀ hs₀l τ
      rw [has₀] at h
      rw [div_le_iff₀ (by have := hκ τ; positivity), mul_comm (nrm S τ s₀)]
      exact h
  refine k_rank1_real (latDet S L) (latDet S (Submodule.span (𝓞 E) {s₀}))
    (g_idx L (Submodule.span (𝓞 E) {s₀}) : ℝ) (g_idx L₀ (Submodule.span (𝓞 E) {s₀}) : ℝ) (g_idx L L₀ : ℝ)
    (∏ τ : E →+* ℂ, ‖τ (p : E)‖) (∏ τ : E →+* ℂ, κ τ) (Real.sqrt (∏ _τ : E →+* ℂ, Tr))
    (Real.sqrt_nonneg _) hPpos hKpos (by exact_mod_cast hNr) hdi (by exact_mod_cast hmul.symm) ?_ hlow
  rw [← k_absNorm]
  exact_mod_cast h5

end K5

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section Defs

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
variable (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)

def k_Psi : Submodule (𝓞 E) S.V := h_Pr (La Λ g F F') (Hp Λ F F') (Th Λ F F' F'' β)

def k_Sp : Submodule E S.V := Hp Λ F F' ⊓ orth S (Th Λ F F' F'' β)

def k_ln : Submodule E S.V := radL Λ F F' F'' β ⊓ orth S (Th Λ F F' F'' β)

def rankOnePart : Submodule (𝓞 E) S.V := k_Psi Λ g F F' F'' β ⊓ toO S (k_ln Λ F F' F'' β)

def k_Q : Submodule (𝓞 E) S.V := h_Pr (k_Psi Λ g F F' F'' β) (k_Sp Λ F F' F'' β) (k_ln Λ F F' F'' β)

end Defs

section K6

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {T T' : ℕ}
variable {Λ : Submodule (𝓞 E) S.V} {g : ℕ}
variable {F : LFlag S r (T : E)} {F' F'' : LFlag S r (T' : E)} {β : S.V ≃ₗ[E] S.V}

theorem k_radL_le : radL Λ F F' F'' β ≤ Hp Λ F F' := fun _ hx => (c_mem_radL.1 hx).1

theorem k_ln_le_Sp : k_ln Λ F F' F'' β ≤ k_Sp Λ F F' F'' β := inf_le_inf_right _ k_radL_le

theorem k_al_Th {f : S.V →ₗ[E] E} (hf : k_IsZc F F'' f) {θ : S.V} (hθ : θ ∈ Th Λ F F' F'' β) :
    k_al f β θ = 0 := by
  obtain ⟨x₂, -, ha, hb⟩ := c_mem_Th.1 hθ
  have : θ - β θ = (θ - x₂) - (β θ - x₂) := by abel
  rw [k_al_apply, this, map_sub, hf.2.1 _ ha, hf.2.2 _ (c_X_le_Xplus F'' hb), sub_zero]

theorem k_Psi_lat (hΛ : Submodule.IsLattice E Λ) (hg : 0 < g) (hz : IsLift Λ F) (hz' : IsLift Λ F')
    (hG' : Gval F F' ≠ 0) (hPos : PosX F) :
    (k_Psi Λ g F F' F'' β).FG ∧ spanE S (k_Psi Λ g F F' F'' β) = k_Sp Λ F F' F'' β := by
  have hU' : HU Λ F F' := a_HU Λ hΛ F F' hz.2 hz'.2
  exact j_Pr_lat c_Th_le_Hp (h_Hp_aniso hU' (a_HNd F F' hG') hPos) (h_La_fg hΛ hg hz hz' hG')
    (g_span_La Λ F F' g hΛ (c_Thp_le_La hU')).1

theorem k_dec (hΛ : Submodule.IsLattice E Λ) (hg : 0 < g) (hz : IsLift Λ F) (hz' : IsLift Λ F')
    (hG' : Gval F F' ≠ 0) (hPos : PosX F) :
    latDet S (k_Psi Λ g F F' F'' β) = latDet S (rankOnePart Λ g F F' F'' β) * latDet S (k_Q Λ g F F' F'' β) := by
  have hU' : HU Λ F F' := a_HU Λ hΛ F F' hz.2 hz'.2
  obtain ⟨f1, s1⟩ := k_Psi_lat (F'' := F'') (β := β) hΛ hg hz hz' hG' hPos
  exact h_det_proj_aniso k_ln_le_Sp
    (fun x hx => h_Hp_aniso hU' (a_HNd F F' hG') hPos x hx.1) f1 s1

theorem k_ln_ne (hΛ : Submodule.IsLattice E Λ) (hz : IsLift Λ F) (hz' : IsLift Λ F') (hz'' : IsLift Λ F'')
    (hG' : Gval F F' ≠ 0) (hPos : PosX F)
    (hrk : finrank E (radL Λ F F' F'' β) = finrank E (Th Λ F F' F'' β) + 1) :
    k_ln Λ F F' F'' β ≠ ⊥ := by
  have hU' : HU Λ F F' := a_HU Λ hΛ F F' hz.2 hz'.2
  have hU'' : HU Λ F F'' := a_HU Λ hΛ F F'' hz.2 hz''.2
  intro h
  have hs := (j_split (c_Th_le_radL (F' := F') (β := β) hU'')
    (fun x hx => h_Hp_aniso hU' (a_HNd F F' hG') hPos x (k_radL_le hx))).1
  unfold k_ln at h
  rw [h, sup_bot_eq] at hs
  rw [← hs] at hrk
  omega

omit [StarRing E] in
theorem k_fin_quot' {M X : Type} [AddCommGroup M] [Module (𝓞 E) M] (N : Submodule (𝓞 E) M) [Finite X]
    (f : M → X) (h : ∀ x x', f x = f x' → x - x' ∈ N) : Finite (M ⧸ N) := by
  apply Finite.of_injective (fun q : M ⧸ N => f (Quotient.out q))
  intro q q' hq
  have := h _ _ hq
  rw [← Submodule.Quotient.eq] at this
  have e1 : (Submodule.Quotient.mk (Quotient.out q) : M ⧸ N) = q := Quotient.out_eq q
  have e2 : (Submodule.Quotient.mk (Quotient.out q') : M ⧸ N) = q' := Quotient.out_eq q'
  rw [← e1, ← e2, this]

theorem k_count_pos (hΛ : Submodule.IsLattice E Λ) (hg : 0 < g) (hP : IsPair Λ F F' F'' β g)
    (hz : IsLift Λ F) (hz'' : IsLift Λ F'') (hG'' : Gval F F'' ≠ 0)
    {f : S.V →ₗ[E] E} (hf : k_IsZc F F'' f) (L : Submodule (𝓞 E) S.V)
    (hL : ∀ s ∈ L, ∃ x ∈ La Λ g F F', x ∈ radL Λ F F' F'' β ∧ k_al f β s = k_al f β x) :
    0 < g_idx L (integralPartOfModule f β L) := by
  have hU'' := a_HU Λ hΛ F F'' hz.2 hz''.2
  have hfin : Finite (BQ Λ F F'') := m_BQ_finite Λ F F'' hΛ
  let π : gB Λ g F F'' →ₗ[𝓞 E] (E ⧸ k_O E) :=
    (k_fbar (Λ := Λ) hf hz.2 hz''.2) ∘ₗ (gB Λ g F F'').subtype
  have hfr : Finite (LinearMap.range π) :=
    Finite.of_surjective π.rangeRestrict π.surjective_rangeRestrict
  have hq : Finite (L ⧸ (integralPartOfModule f β L).comap L.subtype) := by
    apply k_fin_quot' _ (fun s : L => (⟨Submodule.Quotient.mk (k_al f β (s : S.V)), by
      obtain ⟨x, hx, hr, e⟩ := hL s s.2
      obtain ⟨c, hc, hc'⟩ := k_class hg hP hU'' hG'' hf hz.2 hz''.2 hx hr
      exact ⟨⟨c, hc⟩, by rw [e]; exact hc'⟩⟩ : LinearMap.range π))
    intro s s' hss
    have h3 : (Submodule.Quotient.mk (k_al f β (s : S.V)) : E ⧸ k_O E) =
        Submodule.Quotient.mk (k_al f β (s' : S.V)) := congrArg Subtype.val hss
    rw [Submodule.Quotient.eq] at h3
    refine ⟨(s - s').2, ?_⟩
    show k_al f β ((s : S.V) - (s' : S.V)) ∈ k_O E
    rw [map_sub]
    exact h3
  unfold g_idx
  exact Nat.card_pos

theorem k_oneside (hc : StarConj E) (hΛ : Submodule.IsLattice E Λ) (hT : 0 < T) (hT' : 0 < T') (hg : 0 < g)
    (hz : IsLift Λ F) (hz' : IsLift Λ F') (hz'' : IsLift Λ F'') (hG' : Gval F F' ≠ 0)
    (hG'' : Gval F F'' ≠ 0) (hP : IsPair Λ F F' F'' β g) (hPos : PosX F) (hPos'' : PosX F'')
    (hrk : finrank E (radL Λ F F' F'' β) = finrank E (Th Λ F F' F'' β) + 1) :
    ∃ Nr : ℕ, 0 < Nr ∧ iIdx Λ g F F'' * Nr ≤ Nat.card (gB Λ g F F'') ∧
      Real.sqrt (∏ _τ : E →+* ℂ, (T : ℝ)) / ((Nr : ℝ) * ∏ τ : E →+* ℂ, onePlusChSh T T' F F'' τ) ≤
        latDet S (rankOnePart Λ g F F' F'' β) := by
  have hU' : HU Λ F F' := a_HU Λ hΛ F F' hz.2 hz'.2
  have hU'' : HU Λ F F'' := a_HU Λ hΛ F F'' hz.2 hz''.2
  have an' := h_Hp_aniso hU' (a_HNd F F' hG') hPos
  obtain ⟨f, hf⟩ := k_zc_exists (a_HInd F F'' hG'')
  obtain ⟨f1, s1⟩ := k_Psi_lat (F'' := F'') (β := β) hΛ hg hz hz' hG' hPos
  have hL : ∀ s ∈ rankOnePart Λ g F F' F'' β,
      ∃ x ∈ La Λ g F F', x ∈ radL Λ F F' F'' β ∧ k_al f β s = k_al f β x := by
    intro s hs
    obtain ⟨x, hx, θ, hθ, e⟩ := Submodule.mem_sup.1 hs.1.1
    have hθr : θ ∈ radL Λ F F' F'' β := c_Th_le_radL hU'' hθ
    refine ⟨x, hx, ?_, ?_⟩
    · have : x = s - θ := by rw [← e]; abel
      rw [this]
      exact sub_mem hs.2.1 hθr
    · rw [← e, map_add, k_al_Th hf hθ, add_zero]
  refine ⟨g_idx (rankOnePart Λ g F F' F'' β) (integralPartOfModule f β (rankOnePart Λ g F F' F'' β)),
    k_count_pos hΛ hg hP hz hz'' hG'' hf _ hL, k_count hΛ hg hP hz hz'' hG'' hf _ hL, ?_⟩
  · refine k_rank1 hc (k_al f β) (l := k_ln Λ F F' F'' β)
      (h_aniso_nd an' (k_ln_le_Sp.trans inf_le_left)) ?_ (k_ln_ne hΛ hz hz' hz'' hG' hPos hrk)
      (g_fg_le f1 inf_le_left) (h_span_inf (by rw [s1]; exact k_ln_le_Sp))
      (fun τ => onePlusChSh T T' F F'' τ)
      (fun τ => lt_of_lt_of_le zero_lt_one (k_kappa_ge hc hT hT' F F'' hz.2 hz''.2 hG'' hPos τ))
      (T : ℝ) (by exact_mod_cast hT) ?_
    · intro x hx h0
      have hxT := k_ker hc hΛ hT' hz.2 hz'.2 hz''.2 hG'' hP hPos hPos'' hf hx.1 h0
      exact an' x (k_radL_le hx.1) (c_mem_orth.1 hx.2 x hxT)
    · intro x hx τ
      exact k_arch hc hΛ hT hT' hz.2 hz'.2 hz''.2 hG'' hP hPos hPos'' hf hx.1 τ

end K6

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section K7

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {T T' : E}
variable {Λ : Submodule (𝓞 E) S.V} {g : ℕ}
variable {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

theorem k_iso_symm (hP : IsPair Λ F F' F'' β g) (x y : S.V) : S.hT (β.symm x) y = S.hT x (β y) := by
  have := c_iso hP (β.symm x) y
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem k_beta_Lam (hP : IsPair Λ F F' F'' β g) (x : S.V) : β x ∈ Λ ↔ x ∈ Λ := by
  have h : Formalism.HermitianLatticesTheory.gmap β Λ = Λ := hP.1.2
  constructor
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, e⟩ := hx
    have : y = x := β.injective e
    rwa [← this]
  · intro hx
    rw [← h]
    exact Submodule.mem_map_of_mem hx

theorem k_symm_mem_X (hP : IsPair Λ F F' F'' β g) {x : S.V} (hx : x ∈ Xsp F'') : β.symm x ∈ Xsp F' := by
  rw [← c_beta_X hP] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem k_pair_symm (hP : IsPair Λ F F' F'' β g) : IsPair Λ F F'' F' β.symm g := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x y
    rw [k_iso_symm hP, LinearEquiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply (k_beta_Lam hP _).1
      show β (β.symm y) ∈ Λ
      rw [LinearEquiv.apply_symm_apply]; exact hy
    · intro hx
      exact ⟨β x, (k_beta_Lam hP x).2 hx, by simp⟩
  · intro j
    rw [← hP.2.1 j, ← Submodule.map_comp]
    have : ((β.symm : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) ∘ₗ (β : S.V →ₗ[E] S.V) = LinearMap.id := by
      ext x; simp
    rw [this, Submodule.map_id]
  · rw [← hP.2.2.1]; simp
  · intro x'' hx'' l hl
    have hmem : β.symm x'' ∈ Lrep Λ F' := by
      refine ⟨(k_beta_Lam hP _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hx''.1), ?_⟩
      show β.symm x'' ∈ orth S (Xsp F')
      rw [c_mem_orth]
      intro v hv
      have h1 := c_iso hP v (β.symm x'')
      rw [LinearEquiv.apply_symm_apply] at h1
      rw [← h1]
      exact c_mem_orth.1 hx''.2 _ (c_beta_mem_X hP hv)
    have := hP.2.2.2 (β.symm x'') hmem l hl
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm

theorem k_Th_swap (hP : IsPair Λ F F' F'' β g) : Th Λ F F'' F' β.symm = Th'' Λ F F' F'' β := by
  ext x
  rw [c_mem_Th, c_mem_Th'']
  constructor
  · rintro ⟨x₂, ⟨h1, h2⟩, ha, hb⟩
    refine ⟨x₂, ⟨h2, h1⟩, by simpa using (Xsp F).neg_mem ha, ?_⟩
    have := c_beta_mem_X hP hb
    rw [map_sub, LinearEquiv.apply_symm_apply] at this
    simpa using (Xsp F'').neg_mem this
  · rintro ⟨x₁, ⟨h1, h2⟩, ha, hb⟩
    refine ⟨x₁, ⟨h2, h1⟩, by simpa using (Xsp F).neg_mem ha, ?_⟩
    have := k_symm_mem_X hP hb
    rw [map_sub, LinearEquiv.symm_apply_apply] at this
    simpa using (Xsp F').neg_mem this

theorem k_bForm_swap (hP : IsPair Λ F F' F'' β g) (x x' : S.V) :
    bForm β.symm x x' = star (bForm β x' x) := by
  unfold bForm
  rw [star_sub, c_herm, c_herm, k_iso_symm hP]

theorem k_radL_swap (hP : IsPair Λ F F' F'' β g) : radL Λ F F'' F' β.symm = radR Λ F F' F'' β := by
  ext x
  rw [c_mem_radL, c_mem_radR]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x' hx' => ?_⟩
    have := h2 x' hx'
    rw [k_bForm_swap hP] at this
    simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x' hx' => ?_⟩
    rw [k_bForm_swap hP, h2 x' hx', star_zero]

end K7

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

section K8

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {T T' : ℕ}
variable {Λ : Submodule (𝓞 E) S.V} {g : ℕ}
variable {F : LFlag S r (T : E)} {F' F'' : LFlag S r (T' : E)} {β : S.V ≃ₗ[E] S.V}

theorem k_Q_lat (hΛ : Submodule.IsLattice E Λ) (hg : 0 < g) (hz : IsLift Λ F) (hz' : IsLift Λ F')
    (hz'' : IsLift Λ F'') (hG' : Gval F F' ≠ 0) (hPos : PosX F) :
    (k_Q Λ g F F' F'' β).FG ∧
      spanE S (k_Q Λ g F F' F'' β) = k_Sp Λ F F' F'' β ⊓ orth S (k_ln Λ F F' F'' β) ∧
      finrank E ↥(k_Sp Λ F F' F'' β ⊓ orth S (k_ln Λ F F' F'' β)) + finrank E (radL Λ F F' F'' β) =
        finrank E (Hp Λ F F') := by
  have hU' : HU Λ F F' := a_HU Λ hΛ F F' hz.2 hz'.2
  have hU'' : HU Λ F F'' := a_HU Λ hΛ F F'' hz.2 hz''.2
  have an' := h_Hp_aniso hU' (a_HNd F F' hG') hPos
  obtain ⟨f1, s1⟩ := k_Psi_lat (F'' := F'') (β := β) hΛ hg hz hz' hG' hPos
  obtain ⟨f2, s2⟩ := j_Pr_lat (k_ln_le_Sp (Λ := Λ) (F := F) (F' := F') (F'' := F'') (β := β))
    (fun x hx => an' x hx.1) f1 s1
  refine ⟨f2, s2, ?_⟩
  have d1 := j_finrank_Q (c_Th_le_Hp (Λ := Λ) (F := F) (F' := F') (F'' := F'') (β := β)) an'
  have d2 := j_finrank_Q (c_Th_le_radL (F' := F') (β := β) hU'') (fun x hx => an' x (k_radL_le hx))
  have d3 := j_finrank_Q (k_ln_le_Sp (Λ := Λ) (F := F) (F' := F') (F'' := F'') (β := β))
    (fun x hx => an' x hx.1)
  unfold k_Sp k_ln at *
  omega

theorem k_qbound (hc : StarConj E) (hΛ : Submodule.IsLattice E Λ) (hUni : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hg : 0 < g) (hz : IsLift Λ F) (hz' : IsLift Λ F') (hz'' : IsLift Λ F'') (hG' : Gval F F' ≠ 0)
    (hG'' : Gval F F'' ≠ 0) (hP : IsPair Λ F F' F'' β g) (hPos : PosX F) (hPos'' : PosX F'') (k : ℕ)
    (h1 : finrank E (Hp Λ F F') = k - 1) (h2 : finrank E (Hp Λ F F'') = k - 1)
    (r1 : finrank E (radL Λ F F' F'' β) = finrank E (Th Λ F F' F'' β) + 1)
    (r2 : finrank E (radR Λ F F' F'' β) = finrank E (Th Λ F F' F'' β) + 1) :
    (g : ℝ) ^ ((s0 Λ F F' F'' β k - 2) * finrank ℚ E) ≤
      2 ^ ((s0 Λ F F' F'' β k - 2) * finrank ℚ E) * latDet S (k_Q Λ g F F' F'' β) *
        latDet S (k_Q Λ g F F'' F' β.symm) := by
  have hU' : HU Λ F F' := a_HU Λ hΛ F F' hz.2 hz'.2
  have hU'' : HU Λ F F'' := a_HU Λ hΛ F F'' hz.2 hz''.2
  have hN' : HNd F F' := a_HNd F F' hG'
  have hN'' : HNd F F'' := a_HNd F F'' hG''
  have an' := h_Hp_aniso hU' hN' hPos
  have an'' := h_Hp_aniso hU'' hN'' hPos
  obtain ⟨f1, s1, d1⟩ := k_Q_lat (F'' := F'') (β := β) hΛ hg hz hz' hz'' hG' hPos
  obtain ⟨f2, s2, d2⟩ := k_Q_lat (F' := F'') (F'' := F') (β := β.symm) hΛ hg hz hz'' hz' hG'' hPos
  have hRs := k_radL_swap hP
  have hTs := k_Th_swap hP
  rw [hRs] at d2
  have e1 : finrank E ↥(k_Sp Λ F F' F'' β ⊓ orth S (k_ln Λ F F' F'' β)) = s0 Λ F F' F'' β k - 2 := by
    unfold s0; omega
  have e2 : finrank E ↥(k_Sp Λ F F'' F' β.symm ⊓ orth S (k_ln Λ F F'' F' β.symm)) =
      s0 Λ F F' F'' β k - 2 := by
    unfold s0; omega
  have radL0 : ∀ x ∈ radL Λ F F' F'' β, ∀ y ∈ Hp Λ F F'', j_bLin S β x y = 0 :=
    fun x hx y hy => (c_mem_radL.1 hx).2 y hy
  have inversePRadius : ∀ y ∈ radL Λ F F'' F' β.symm, ∀ x ∈ Hp Λ F F', j_bLin S β x y = 0 := by
    intro y hy x hx
    rw [hRs] at hy
    exact (c_mem_radR.1 hy).2 x hx
  have hTh_sw : Th Λ F F'' F' β.symm ≤ radL Λ F F'' F' β.symm := c_Th_le_radL hU'
  refine j_main_form hc e1 e2
    (fun τ x hx hx0 => radical_positive_each_embedding Λ hU' hN' hPos τ x hx.1.1 hx0)
    (fun τ x hx hx0 => radical_positive_each_embedding Λ hU'' hN'' hPos τ x hx.1.1 hx0)
    f1 f2 s1 s2 (j_bLin S β) ?_ g hg ?_ ?_
  ·
    intro y hy hall
    have hyH : y ∈ Hp Λ F F'' := hy.1.1
    have hrad : y ∈ radR Λ F F' F'' β := by
      refine c_mem_radR.2 ⟨hyH, fun X hX => ?_⟩
      rw [← (j_split (c_Th_le_Hp (Λ := Λ) (F := F) (F' := F') (F'' := F'') (β := β)) an').1] at hX
      obtain ⟨θ, hθ, q, hq, rfl⟩ := Submodule.mem_sup.1 hX
      have hq' : q ∈ k_Sp Λ F F' F'' β := hq
      rw [← (j_split (k_ln_le_Sp (Λ := Λ) (F := F) (F' := F') (F'' := F'') (β := β))
        (fun x hx => an' x hx.1)).1] at hq'
      obtain ⟨ρ, hρ, q₁, hq₁, rfl⟩ := Submodule.mem_sup.1 hq'
      have v1 := radL0 θ (c_Th_le_radL hU'' hθ) y hyH
      have v2 := radL0 ρ hρ.1 y hyH
      have v3 := hall q₁ hq₁
      rw [← j_bLin_apply, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, v1, v2, v3]
      simp
    rw [← hRs] at hrad
    have hln : y ∈ k_ln Λ F F'' F' β.symm := ⟨hrad, hy.1.2⟩
    exact an'' y hyH (c_mem_orth.1 hy.2 y hln)
  ·
    intro x hx y hy
    obtain ⟨ψ, hψ, ρ, hρ, ex⟩ := Submodule.mem_sup.1 hx.1
    obtain ⟨x', hx', θ, hθ, eψ⟩ := Submodule.mem_sup.1 hψ.1
    obtain ⟨ψ'', hψ'', ρ'', hρ'', ey⟩ := Submodule.mem_sup.1 hy.1
    obtain ⟨x'', hx'', θ'', hθ'', eψ''⟩ := Submodule.mem_sup.1 hψ''.1
    obtain ⟨o, ho⟩ := c_b_gO hP (c_int_of_unimod hUni) x' hx' x'' hx''
    refine ⟨o, ?_⟩
    rw [← ho, ← j_bLin_apply]
    have hyH : y ∈ Hp Λ F F'' := hy.2.1.1
    have hx'H : x' ∈ Hp Λ F F' := c_La_Hp Λ g hx'
    have v1 := radL0 θ (c_Th_le_radL hU'' hθ) y hyH
    have v2 := radL0 ρ hρ.1 y hyH
    have v3 := inversePRadius θ'' (hTh_sw hθ'') x' hx'H
    have v4 := inversePRadius ρ'' hρ''.1 x' hx'H
    have t1 : j_bLin S β x y = j_bLin S β x' y := by
      rw [← ex, ← eψ, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, v1, v2]
      simp
    have t2 : j_bLin S β x' y = j_bLin S β x' x'' := by
      rw [← ey, ← eψ'', map_add, map_add, v3, v4]
      simp
    rw [t1, t2]
  ·
    intro τ x hx y hy
    exact j_b_bound_H hc hP hU' hU'' hPos hPos'' τ hx.1.1 hy.1.1

end K8

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lemma_one_det_index_le_gram_div (D : D7) (Λ : VanishingOnXAndXPlusGluing.LatS D) (g : ℕ) {T T' : ℕ} (F : VanishingOnXAndXPlusGluing.FlS D T) (F' : VanishingOnXAndXPlusGluing.FlS D T')
    (h : VanishingOnXAndXPlusGluing.Lem1 D Λ g F F') (Nr : ℕ) (hNr : 0 < Nr) (hc : iIdx Λ g F F' * Nr ≤ Nat.card (gB Λ g F F')) :
    latDet (hS D) (La Λ g F F') * (iIdx Λ g F F' : ℝ) ^ 2 ≤ G0 Λ g F F' / (Nr : ℝ) := by
  obtain ⟨hfin, -, h2, h3, -⟩ := h
  have hNG : 0 ≤ NG Λ F F' := Real.sqrt_nonneg _
  have hN : 0 ≤ NE (E := D.host.E) g ^ (D.R.rS + 1) := by unfold NE; positivity
  have hB : 0 < (Nat.card (BQ Λ F F') : ℝ) := by exact_mod_cast Nat.card_pos
  have hNr' : (0 : ℝ) < Nr := by exact_mod_cast hNr
  have hc' : (iIdx Λ g F F' : ℝ) * (Nr : ℝ) ≤ (Nat.card (gB Λ g F F') : ℝ) := by exact_mod_cast hc
  rw [h3]
  unfold G0
  rcases Nat.eq_zero_or_pos (iIdx Λ g F F') with hi | hi
  · rw [hi]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact div_nonneg (div_nonneg hNG hN) hNr'.le
  · have hi' : 0 < (iIdx Λ g F F' : ℝ) := by exact_mod_cast hi
    have hle : (iIdx Λ g F F' : ℝ) * (Nr : ℝ) ≤
        (Nat.card (BQ Λ F F') : ℝ) / NE (E := D.host.E) g ^ (D.R.rS + 1) := hc'.trans h2
    have hNpos : 0 < NE (E := D.host.E) g ^ (D.R.rS + 1) := by
      rcases hN.lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at hle
        have : 0 < (iIdx Λ g F F' : ℝ) * (Nr : ℝ) := mul_pos hi' hNr'
        linarith
    have e1 : NG Λ F F' / ((Nat.card (BQ Λ F F') : ℝ) * (iIdx Λ g F F' : ℝ)) * (iIdx Λ g F F' : ℝ) ^ 2 =
        NG Λ F F' * ((iIdx Λ g F F' : ℝ) / (Nat.card (BQ Λ F F') : ℝ)) := by
      field_simp
    have e2 : NG Λ F F' / NE (E := D.host.E) g ^ (D.R.rS + 1) / (Nr : ℝ) =
        NG Λ F F' * (1 / (NE (E := D.host.E) g ^ (D.R.rS + 1) * (Nr : ℝ))) := by
      field_simp
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ hNG
    rw [div_le_div_iff₀ hB (by positivity), one_mul]
    rw [le_div_iff₀ hNpos] at hle
    nlinarith

theorem k_sqrt_prod (D : D7) (T : ℕ) :
    Real.sqrt (∏ _τ : D.host.E →+* ℂ, (T : ℝ)) = (T : ℝ) ^ D.R.f := by
  rw [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card, j_finrank, pow_mul', ]
  exact Real.sqrt_sq (by positivity)

theorem k_A2Det (D : D7) : RadicalDeterminantIdentity D :=
  fun u T' Λ F F' F'' β hF hPr hT' hT'' hP _ W hW => h_a2det D u T' Λ F F' F'' β hF hPr hT' hT'' hP W hW

theorem radical_setting_second (D : D7) : VanishingOnXAndXPlusGluing.HyperplaneRank D := radical_second_of_determinant D (k_A2Det D)

theorem k_thmA_deg (D : D7) (u : D.what₂.Word) (T' : ℕ) (Λ : VanishingOnXAndXPlusGluing.LatS D) (F : VanishingOnXAndXPlusGluing.FlS D (Tu D u))
    (F' F'' : VanishingOnXAndXPlusGluing.FlS D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (hF : FixedHyp D Λ F) (hPr : PrimeHyp D u T') (hT' : IsTerm Λ (gS D) F F') (hT'' : IsTerm Λ (gS D) F F'')
    (hP : IsPair Λ F F' F'' β (gS D)) (hs : 2 ≤ s0 Λ F F' F'' β D.R.k) (hnd : ¬ BNondeg Λ F F' F'' β) :
    latDet (hS D) (Mlat Λ F F' F'' β (gS D)) * (iIdx Λ (gS D) F F' : ℝ) * (iIdx Λ (gS D) F F'' : ℝ) ≤
      (2 / ((gS D : ℕ) : ℝ)) ^ ((s0 Λ F F' F'' β D.R.k - 2) * D.R.f) *
        Real.sqrt (G0 Λ (gS D) F F' * G0 Λ (gS D) F F'') * (((Tu D u : ℕ) : ℝ) ^ D.R.f)⁻¹ *
        placeProd (fun τ : D.host.E →+* ℂ =>
          onePlusChSh (Tu D u) T' F F' τ * onePlusChSh (Tu D u) T' F F'' τ) := by
  have h0 : 0 < Tu D u := lt_of_lt_of_le (by norm_num) hPr.2.1
  have h0' : 0 < T' := lt_of_lt_of_le (by norm_num) hPr.2.2.2.1
  have hg : 0 < gS D := z_gS_pos D
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hc := p_starConj D
  have hΛ := hF.1
  have hz := hF.2.2.1
  have hU' : HU Λ F F' := a_HU Λ hΛ F F' hz.2 hT'.1.2
  have hU'' : HU Λ F F'' := a_HU Λ hΛ F F'' hz.2 hT''.1.2
  have hN' : HNd F F' := a_HNd F F' hT'.2.2
  have hN'' : HNd F F'' := a_HNd F F'' hT''.2.2
  have hPos := p_posX D _ h0 F
  have hPos' := p_posX D _ h0' F'
  have hPos'' := p_posX D _ h0' F''
  have rk' := (radical_positive_definite D u T' Λ F F' hF hPr hT').1
  have rk'' := (radical_positive_definite D u T' Λ F F'' hF hPr hT'').1
  obtain ⟨W, hW⟩ := h_existsW D (Tu D u) F h0
  have hA2 := radical_setting_second D u T' Λ F F' F'' β hF hPr hT' hT'' hP hs W hW
  obtain ⟨r1, r2⟩ := c_thmA_ranks hP hU' hN' hU'' hN'' hPos'' (by exact_mod_cast h0.ne') D.R.k (p_rankV D)
    rk' rk'' hk hnd
  have eTh : finrank D.host.E (Th'' Λ F F' F'' β) = finrank D.host.E (Th Λ F F' F'' β) := by
    rw [c_finrank_Th'' hU' hN', ← c_finrank_Th hU'' hN'']
  have hP' := k_pair_symm hP
  obtain ⟨Nr₂, n2, c2, b1⟩ := k_oneside hc hΛ h0 h0' hg hz hT'.1 hT''.1 hT'.2.2 hT''.2.2 hP hPos hPos'' r1
  obtain ⟨Nr₁, n1, c1, b2⟩ := k_oneside hc hΛ h0 h0' hg hz hT''.1 hT'.1 hT''.2.2 hT'.2.2 hP' hPos hPos'
    (by rw [k_radL_swap hP, k_Th_swap hP, r2, eTh])
  have s' := (g_span_La Λ F F' (gS D) hΛ (c_Thp_le_La hU')).1
  have s'' := (g_span_La Λ F F'' (gS D) hΛ (c_Thp_le_La hU'')).1
  have hL' : La Λ (gS D) F F' ≤ toO (hS D) (Hp Λ F F') := s' ▸ g_le_span _
  have hL'' : La Λ (gS D) F F'' ≤ toO (hS D) (Hp Λ F F'') := s'' ▸ g_le_span _
  have e₁ : latDet (hS D) (Psi Λ F F' F'' β W (La Λ (gS D) F F')) =
      latDet (hS D) (rankOnePart Λ (gS D) F F' F'' β) * latDet (hS D) (k_Q Λ (gS D) F F' F'' β) := by
    rw [← k_dec hΛ hg hz hT'.1 hT'.2.2 hPos]
    exact h_latDet_Psi (Λ := Λ) (F' := F') (F'' := F'') (β := β) hW (c_Hp_orthXplus Λ hU')
      (h_Hp_inf_X hU' hN') c_Th_le_Hp rfl hL'
  have e₂ : latDet (hS D) (Psi Λ F F' F'' β W (La Λ (gS D) F F'')) =
      latDet (hS D) (rankOnePart Λ (gS D) F F'' F' β.symm) * latDet (hS D) (k_Q Λ (gS D) F F'' F' β.symm) := by
    rw [← k_dec hΛ hg hz hT''.1 hT''.2.2 hPos]
    exact h_latDet_Psi (Λ := Λ) (F' := F') (F'' := F'') (β := β) hW (c_Hp_orthXplus Λ hU'')
      (h_Hp_inf_X hU'' hN'') (c_Th_le_Hp (F' := F'') (F'' := F') (β := β.symm))
      (by rw [k_Th_swap hP]; exact c_Th''_sup_X) hL''
  have hK₁ : ∀ τ : D.host.E →+* ℂ, 0 < onePlusChSh (Tu D u) T' F F' τ := fun τ =>
    lt_of_lt_of_le zero_lt_one (k_kappa_ge hc h0 h0' F F' hz.2 hT'.1.2 hT'.2.2 hPos τ)
  have hK₂ : ∀ τ : D.host.E →+* ℂ, 0 < onePlusChSh (Tu D u) T' F F'' τ := fun τ =>
    lt_of_lt_of_le zero_lt_one (k_kappa_ge hc h0 h0' F F'' hz.2 hT''.1.2 hT''.2.2 hPos τ)
  have sq₁ : placeProd (fun τ : D.host.E →+* ℂ => onePlusChSh (Tu D u) T' F F' τ) ^ 2 =
      ∏ τ : D.host.E →+* ℂ, onePlusChSh (Tu D u) T' F F' τ :=
    Real.sq_sqrt (Finset.prod_nonneg fun τ _ => (hK₁ τ).le)
  have sq₂ : placeProd (fun τ : D.host.E →+* ℂ => onePlusChSh (Tu D u) T' F F'' τ) ^ 2 =
      ∏ τ : D.host.E →+* ℂ, onePlusChSh (Tu D u) T' F F'' τ :=
    Real.sq_sqrt (Finset.prod_nonneg fun τ _ => (hK₂ τ).le)
  rw [k_sqrt_prod] at b1 b2
  have q := k_qbound hc hΛ hF.2.1 hg hz hT'.1 hT''.1 hT'.2.2 hT''.2.2 hP hPos hPos'' D.R.k rk' rk'' r1 r2
  rw [j_finrank] at q
  have q' : ((gS D : ℕ) : ℝ) ^ (2 * D.R.f * (s0 Λ F F' F'' β D.R.k - 2)) ≤
      4 ^ ((s0 Λ F F' F'' β D.R.k - 2) * D.R.f) * latDet (hS D) (k_Q Λ (gS D) F F' F'' β) *
        latDet (hS D) (k_Q Λ (gS D) F F'' F' β.symm) := by
    have e1 : 2 * D.R.f * (s0 Λ F F' F'' β D.R.k - 2) = (s0 Λ F F' F'' β D.R.k - 2) * (2 * D.R.f) := by ring
    have e2 : (4 : ℝ) ^ ((s0 Λ F F' F'' β D.R.k - 2) * D.R.f) =
        2 ^ ((s0 Λ F F' F'' β D.R.k - 2) * (2 * D.R.f)) := by
      have : (s0 Λ F F' F'' β D.R.k - 2) * (2 * D.R.f) = 2 * ((s0 Λ F F' F'' β D.R.k - 2) * D.R.f) := by ring
      have gen : ∀ N : ℕ, (4 : ℝ) ^ N = 2 ^ (2 * N) := fun N => by rw [pow_mul]; norm_num
      rw [this, gen]
    rw [e1, e2]
    exact q
  exact m_thmA_deg D Λ (gS D) hg h0 F F' F'' β W hA2 hK₁ hK₂ _ _ _ _ (Nr₁ : ℝ) (Nr₂ : ℝ)
    (h_latDet_pos _) (h_latDet_pos _) (h_latDet_pos _) (h_latDet_pos _)
    (by exact_mod_cast n1) (by exact_mod_cast n2) e₁ e₂
    (lemma_one_det_index_le_gram_div D Λ (gS D) F F' (lattice_lemma_one D u T' Λ F F' hF hPr hT') Nr₁ n1 c1)
    (lemma_one_det_index_le_gram_div D Λ (gS D) F F'' (lattice_lemma_one D u T' Λ F F'' hF hPr hT'') Nr₂ n2 c2)
    (by rw [sq₂]; exact b1) (by rw [sq₁]; exact b2) q'

end Formalism.MainNotions.LatticeGluingRadicals

end

noncomputable section

namespace Formalism.MainNotions.LatticeGluingRadicals

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem z_ThmADeg (D : D7) : ThmADeg D :=
  fun u T' Λ F F' F'' β hF hPr hT' hT'' hP hs hnd => k_thmA_deg D u T' Λ F F' F'' β hF hPr hT' hT'' hP hs hnd

theorem lattice_theorem_A_from_degenerate (D : D7) : VanishingOnXAndXPlusGluing.PointsLemma D := theorem_A_of_degenerate_case D (z_ThmADeg D)

theorem theorem_A_section (D : D7) : Formalism.MainNotions.S.UnitaryVolumeMass.stThmA D := lattice_theorem_A_from_degenerate D

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Fam

end Formalism.MainNotions.LatticeGluingRadicals

end
