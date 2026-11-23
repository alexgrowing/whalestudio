import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTauComponentFrameOfLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulMemOfTwistedInvariantModLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMemOL

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.InvKilled

variable {l : ℕ} [Fact l.Prime]

theorem exists_pow_smul_mem (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (v : T.V) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.IntegerRingPowers.main
  | exact _root_.GlobalTheory.IntegerRingPowers.main
  | (apply _root_.GlobalTheory.IntegerRingPowers.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerRingPowers.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerRingPowers.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerRingPowers.main ..)

theorem killed_of_coordinates {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [CharZero LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) [Module ℤ_[l] ↥T.L.T]
    (hsm : ∀ (k : ℕ) (t : ↥T.L.T),
      ((((l : ℤ_[l]) ^ k) • t : ↥T.L.T) : T.V) = (l : LL) ^ k • (t : T.V))
    (ac : G → (↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T)) (hac : ∀ g t, ((ac g t : ↥T.L.T) : T.V) = T.ρ g t)
    {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] ↥T.L.T)
    (M : G → Matrix (Fin d) (Fin d) (PadicComplex l))
    (hb : ∀ g i j, M g i j = zC (b.repr (ac g (b j)) i)) (c : ℕ)
    (H : ∀ y : Fin d → ℚ_[l], (∀ σ,
      (M σ).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) -
        (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ ball l d) →
      ∀ a, ‖(l : ℚ_[l]) ^ c * y a‖ ≤ 1)
    (v : T.V) (hw : ∀ g, T.ρ g v - v ∈ T.L.T) (n : ℕ) (hn : (l : LL) ^ n • v ∈ T.L.T) :
    (l : LL) ^ c • v ∈ T.L.T := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlL : (l : LL) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set t : ↥T.L.T := ⟨_, hn⟩ with ht
  have hy := H (fun a => ((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l])) (by
    intro σ a
    have e1 : ac σ t - t = (l : ℤ_[l]) ^ n • (⟨_, hw σ⟩ : ↥T.L.T) := by
      apply Subtype.ext
      rw [hsm, Submodule.coe_sub, hac]
      change T.ρ σ ((l : LL) ^ n • v) - (l : LL) ^ n • v = _
      rw [map_smul, smul_sub]
    have e2 : b.repr (ac σ t) a =
        ∑ j, b.repr (ac σ (b j)) a * b.repr t j := by
      conv_lhs => rw [← b.sum_repr t]
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
        smul_eq_mul, mul_comm]
    have e3 := congrArg (fun z => ((b.repr z a : ℤ_[l]) : ℚ_[l])) e1
    simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, e2] at e3
    push_cast at e3
    have e4 : ((M σ).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l)
          (((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l]))) -
        (fun a => algebraMap ℚ_[l] (PadicComplex l) (((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l])))) a =
        algebraMap ℚ_[l] (PadicComplex l) ((b.repr (⟨_, hw σ⟩ : ↥T.L.T) a : ℤ_[l]) : ℚ_[l]) := by
      have hb' : ∀ i j, M σ i j = zC (b.repr (ac σ (b j)) i) := hb σ
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, hb', zC, ← map_mul, ← map_sum, ← map_sub]
      congr 1
      have hp : (l : ℚ_[l]) ^ n ≠ 0 := pow_ne_zero _ hl
      rw [← inv_mul_cancel_left₀ hp (((b.repr (⟨_, hw σ⟩ : ↥T.L.T) a : ℤ_[l]) : ℚ_[l])), ← e3,
        mul_sub, PadicInt.coe_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [PadicInt.coe_mul]; ring
    rw [e4, norm_algebraMap']
    exact PadicInt.norm_le_one _)
  let z : Fin d → ℤ_[l] := fun a => ⟨_, hy a⟩
  let t' : ↥T.L.T := ∑ a, z a • b a
  have e5 : (l : ℤ_[l]) ^ c • t = (l : ℤ_[l]) ^ n • t' := by
    apply b.repr.injective
    ext a
    have : b.repr t' a = z a := congrFun (b.repr_sum_self z) a
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, this]
    apply Subtype.ext
    have hz : ((z a : ℤ_[l]) : ℚ_[l]) = (l : ℚ_[l]) ^ c * (((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l])) := rfl
    rw [PadicInt.coe_mul, PadicInt.coe_mul, hz]
    push_cast
    field_simp
  have e6 := congrArg Subtype.val e5
  rw [hsm, hsm] at e6
  change (l : LL) ^ c • (l : LL) ^ n • v = _ at e6
  rw [smul_comm] at e6
  have e7 := smul_right_injective _ (pow_ne_zero n hlL) e6
  rw [e7]
  exact t'.2

theorem pow_smul_compHom {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) (φ : ℤ_[l] →+* O) :
    letI : Module ℤ_[l] ↥T.L.T := Module.compHom ↥T.L.T φ
    ∀ (k : ℕ) (t : ↥T.L.T),
      ((((l : ℤ_[l]) ^ k) • t : ↥T.L.T) : T.V) = (l : LL) ^ k • (t : T.V) := by
  intro k t
  change (φ ((l : ℤ_[l]) ^ k)) • (t : T.V) = _
  rw [← algebraMap_smul LL, map_pow, map_natCast, map_pow, map_natCast]

theorem killed_of_coord (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (hM : IsMat K LL T M A) (c : ℕ)
    (H : ∀ y : Fin d → ℚ_[l], (∀ σ ∈ GK K,
      (M σ).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) -
        (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ ball l d) →
      ∀ a, ‖(l : ℚ_[l]) ^ c * y a‖ ≤ 1)
    (v : T.V) (hw : ∀ g : ↥(GK K), T.ρ g v - v ∈ T.L.T) : (l : ↥LL.1) ^ c • v ∈ T.L.T := by
  obtain ⟨b, hb, -⟩ := hM
  obtain ⟨n, hn⟩ := exists_pow_smul_mem K LL T v
  refine @killed_of_coordinates l _ _ _ _ _ _ _ _ _ _ _ _ _ _ T (zlMod LL T) ?_
    (fun g => actTZ LL T g) (fun _ _ => rfl) d b (fun g => M g) hb c
    (fun y hy => H y fun σ hσ => hy ⟨σ, hσ⟩) v hw n hn
  exact pow_smul_compHom T (algebraMap ℤ_[l] ↥(OL LL))

theorem killed_quot {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O)
    (p c : ℕ) (H : ∀ v : T.V, (∀ g, T.ρ g v - v ∈ T.L.T) → (p : LL) ^ c • v ∈ T.L.T)
    (x : T.V ⧸ T.L.T) (hx : ∀ g, actD T.L g x = x) : ((p : O) ^ c) • x = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL, map_pow,
    map_natCast]
  exact H v fun g => (Submodule.Quotient.eq _).1 (hx g)

def imBall {r d : ℕ} (P : Matrix (Fin r) (Fin d) (PadicComplex l)) :
    AddSubgroup (Fin r → PadicComplex l) where
  carrier := P.mulVec '' ball l d
  zero_mem' := ⟨0, fun a => by simp, Matrix.mulVec_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, fun a => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx a) (hy a)),
      Matrix.mulVec_add _ _ _⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, fun a => by simpa using hx a, Matrix.mulVec_neg _ _⟩

theorem Ks_mono' (K : FinExt l) {i j : ℕ} (h : i ≤ j) : Ks K i ≤ Ks K j := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
  intro x hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [pow_add, pow_mul, hx, one_pow]

theorem act_algebraMap' {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (g : GQ l) (x : ℚ_[l]) :
    act g (algebraMap ℚ_[l] (PadicComplex l) x) = algebraMap ℚ_[l] (PadicComplex l) x := by
  have := ha.1 g (algebraMap ℚ_[l] (Om l) x)
  rw [AlgEquiv.commutes] at this
  exact this

theorem invariants_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; H0at S E := by
  intro D HW F h7 l _ K s LL h S E M0 h0 T τ hW hj x hx
  have hell : ell S = l := (D.loc l).PD_p K
  have hs : S.W.s = s := (HW l).W_s K s LL h
  obtain ⟨d, M, A, hM⟩ := (GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral l K LL T).1
  obtain ⟨r, P, U, g, J, hJ, hfin, hFr, hHT, hPM, hb1, hb2, hint⟩ :=
    GlobalTheory.T.exists_tau_component_frame_of_lattice D HW F h7 l K s LL h T M0 h0 τ hW d M A hM
  have hact : IsActC (D.locA l).actC := ⟨(D.locA l).actC_ext, (D.locA l).actC_norm⟩
  have hχ : IsCyc (D.loc l).χQ := (D.loc l).χQ_cyc
  set m := mN l s (M0 + h0) with hm
  have hsm : s + 1 ≤ m := by rw [hm, mN]; omega
  have hs1 := h.1
  have hLev : Lev l m := ⟨by omega, fun _ => by omega⟩
  have hG : Gj K m ≤ GK K :=
    IntermediateField.fixingSubgroup_le (h.2.2.1.trans (Ks_mono' K (by omega)))
  have h0J : (0 : ℤ) ∉ J := fun hh => hj (hJ 0 hh)
  have hc0 : c0 S T τ M0 h0 = 2 + ∑ u ∈ hfin.toFinset, (m + padicValInt l u) := by
    rw [c0, hell, hs]
    congr 1
    exact finsum_mem_eq_finite_toFinset_sum (fun u => m + vZ l u) hfin
  rw [hell]
  refine killed_quot T l _ (killed_of_coord K LL T M A hM _ ?_) x hx
  intro y hy
  have hl1 : ‖(l : ℚ_[l])‖ ≤ 1 := (Padic.norm_p_lt_one).le
  rcases J.eq_empty_or_nonempty with rfl | ⟨u0, hu0⟩
  · obtain ⟨e, u, -, hu, -⟩ := hHT
    have : IsEmpty (Fin r) := ⟨fun k => by simpa using hu k⟩
    intro a
    have := hint y ⟨0, fun a => by simp, Subsingleton.elim _ _⟩ a
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1) (norm_nonneg _) this
  · have key := GlobalTheory.T.prime_pow_smul_mem_of_twistedInvariant_mod_lattice l _ _ hact hχ K m r hLev U g hFr J hHT 0 h0J (imBall P) hb1
      (by rintro _ ⟨z, hz, rfl⟩; exact hb2 z hz)
      (P.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a))) (by
        intro σ hσ
        refine ⟨_, hy σ (hG hσ), ?_⟩
        have e1 : (fun a => (D.locA l).actC σ
            (P.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) a)) =
            (P.map ((D.locA l).actC σ)).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) := by
          funext a
          simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
            act_algebraMap' hact]
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPM σ hσ, twAct, e1, Matrix.mulVec_mulVec]
        simp [chiC])
    rw [Finset.erase_eq_of_notMem h0J] at key
    simp only [sub_zero] at key
    have hle1 : 1 ≤ ∑ u ∈ J, (m + padicValInt l u) :=
      le_trans (by omega) (Finset.single_le_sum (f := fun u => m + padicValInt l u)
        (fun _ _ => Nat.zero_le _) hu0)
    have hle2 : ∑ u ∈ J, (m + padicValInt l u) ≤ ∑ u ∈ hfin.toFinset, (m + padicValInt l u) :=
      Finset.sum_le_sum_of_subset fun u hu => hfin.mem_toFinset.2 (hJ u hu)
    rw [max_eq_right hle1] at key
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle2
    have hi := hint (fun a => (l : ℚ_[l]) ^ (2 + ∑ u ∈ J, (m + padicValInt l u)) * y a) (by
      have e : (fun a => algebraMap ℚ_[l] (PadicComplex l)
          ((l : ℚ_[l]) ^ (2 + ∑ u ∈ J, (m + padicValInt l u)) * y a)) =
          (l : PadicComplex l) ^ (2 + ∑ u ∈ J, (m + padicValInt l u)) •
            (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) := by
        funext a
        simp only [map_mul, map_pow, map_natCast, Pi.smul_apply, smul_eq_mul]
      rw [e, Matrix.mulVec_smul]
      exact key)
    intro a
    rw [hc0, hk, ← add_assoc, add_comm _ k, pow_add, mul_assoc, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1) (norm_nonneg _) (hi a)

end GlobalTheory.Cyc.InvKilled
