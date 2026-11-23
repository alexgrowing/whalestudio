import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.TopProdD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequences
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNontrivialDerivative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetIteratedPhiEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.Pos2

section Gen

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem nontrivial_of_irr (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have h2 : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.toSubmodule_injective
    (Submodule.ext fun x => ⟨fun _ => Submodule.mem_top, fun _ => (Submodule.mem_bot ℂ).2 (Subsingleton.elim _ _)⟩)
  exact bot_ne_top h2

theorem norm_eig_of_unit (hu : IsUnitarisable ρ) (g : G) {c : ℂ} {v : V} (hv : v ≠ 0) (h : ρ g v = c • v) :
    ‖c‖ = 1 := by
  obtain ⟨B, -, hpos, hinv⟩ := hu
  have h1 := hinv g v v
  have e1 : B (c • v) = c • B v := map_smul B c v
  have e2 : (B v) (c • v) = starRingEnd ℂ c • B v v := LinearMap.map_smulₛₗ (B v) c v
  rw [h, e1, LinearMap.smul_apply, e2, smul_eq_mul, smul_eq_mul] at h1
  have hB : B v v ≠ 0 := fun h0 => by have := hpos v hv; rw [h0] at this; simp at this
  have h3 : (c * starRingEnd ℂ c) * B v v = 1 * B v v := by rw [one_mul, mul_assoc]; exact h1
  have h4 := mul_right_cancel₀ hB h3
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h4
  have h5 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h4
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 h5

theorem isUnitarisable_twist_one (hu : IsUnitarisable ρ) (χ : G →* ℂˣ) (hχ : ∀ g, χ g = 1) :
    IsUnitarisable (twist ρ χ) := by
  obtain ⟨B, h1, h2, h3⟩ := hu
  refine ⟨B, h1, h2, fun g v w => ?_⟩
  rw [twist_apply, twist_apply, hχ g, Units.val_one, one_smul, one_smul]
  exact h3 g v w

theorem equiv_eig {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} (E : ρ.Equiv σ) (g : G)
    (c : ℂ) (v : V) (hv : v ≠ 0) (h : ρ g v = c • v) :
    E.toLinearEquiv v ≠ 0 ∧ σ g (E.toLinearEquiv v) = c • E.toLinearEquiv v := by
  refine ⟨(LinearEquiv.map_ne_zero_iff _).2 hv, ?_⟩
  have := LinearMap.congr_fun (E.isIntertwining' g) v
  simp only [LinearMap.comp_apply] at this
  have e1 : E.toLinearEquiv (ρ g v) = σ g (E.toLinearEquiv v) := this
  rw [← e1, h, map_smul]

theorem subQuot_eq_zero_of_eq {S T : Subrepresentation ρ} (h : S = T)
    (w : S.toSubmodule ⧸ Submodule.comap S.toSubmodule.subtype T.toSubmodule) : w = 0 := by
  subst h
  induction w using Submodule.Quotient.induction_on with
  | H x => exact (Submodule.Quotient.mk_eq_zero _).2 (by simp)

theorem le_of_subsingleton_subQuot {S T : Subrepresentation ρ}
    [Subsingleton (S.toSubmodule ⧸ Submodule.comap S.toSubmodule.subtype T.toSubmodule)] : S ≤ T := by
  rw [SetLike.le_def]
  intro x hx
  have hx' : x ∈ S.toSubmodule := hx
  have := (Submodule.Quotient.mk_eq_zero
    (Submodule.comap S.toSubmodule.subtype T.toSubmodule) (x := ⟨x, hx'⟩)).1 (Subsingleton.elim _ _)
  exact this

theorem filt_const {F : ℕ → Subrepresentation ρ} {ℓ : ℕ} (h : ∀ i ≤ ℓ, F i = F (i + 1)) :
    ∀ i ≤ ℓ + 1, F i = F 0
  | 0, _ => rfl
  | i + 1, hi => (h i (by omega)).symm.trans (filt_const h i (by omega))

theorem subsingleton_of_filt {F : ℕ → Subrepresentation ρ} {ℓ : ℕ} (h0 : F 0 = ⊤) (hl : F (ℓ + 1) = ⊥)
    (h : ∀ i ≤ ℓ, F i = F (i + 1)) : Subsingleton V := by
  have h1 := filt_const h (ℓ + 1) le_rfl
  rw [hl, h0] at h1
  have h2 : (⊥ : Submodule ℂ V) = ⊤ := congrArg Subrepresentation.toSubmodule h1
  constructor
  intro a b
  have ha : a ∈ (⊥ : Submodule ℂ V) := h2 ▸ Submodule.mem_top
  have hb : b ∈ (⊥ : Submodule ℂ V) := h2 ▸ Submodule.mem_top
  rw [(Submodule.mem_bot ℂ).1 ha, (Submodule.mem_bot ℂ).1 hb]

theorem filt_single {F : ℕ → Subrepresentation ρ} {ℓ i₀ : ℕ} (hi₀ : i₀ ≤ ℓ) (h0 : F 0 = ⊤) (hl : F (ℓ + 1) = ⊥)
    (h : ∀ i ≤ ℓ, i ≠ i₀ → F i = F (i + 1)) : F i₀ = ⊤ ∧ F (i₀ + 1) = ⊥ := by
  have up : ∀ i ≤ i₀, F i = ⊤ := by
    intro i
    induction i with
    | zero => intro _; exact h0
    | succ i ih => intro hi; rw [← h i (by omega) (by omega)]; exact ih (by omega)
  have down : ∀ d ≤ ℓ - i₀, F (ℓ + 1 - d) = ⊥ := by
    intro d
    induction d with
    | zero => intro _; exact hl
    | succ d ih =>
      intro hd
      rw [show ℓ + 1 - (d + 1) = ℓ - d by omega, h (ℓ - d) (by omega) (by omega),
        show ℓ - d + 1 = ℓ + 1 - d by omega]
      exact ih (by omega)
  refine ⟨up i₀ le_rfl, ?_⟩
  have := down (ℓ - i₀) le_rfl
  rwa [show ℓ + 1 - (ℓ - i₀) = i₀ + 1 by omega] at this

def topBotMap : V →ₗ[ℂ] ((⊤ : Subrepresentation ρ).toSubmodule ⧸
    Submodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype (⊥ : Subrepresentation ρ).toSubmodule) :=
  (Submodule.mkQ _).comp (LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id
    (fun _ => Submodule.mem_top))

theorem topBotMap_bij : Function.Bijective (topBotMap (ρ := ρ)) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    have h1 : (Submodule.mkQ _) (⟨v, Submodule.mem_top⟩ : (⊤ : Subrepresentation ρ).toSubmodule) = 0 := hv
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    exact h1
  · intro w
    induction w using Submodule.Quotient.induction_on with
    | H x => exact ⟨x.1, rfl⟩

theorem equiv_subQuot {S T : Subrepresentation ρ} (hS : S = ⊤) (hT : T = ⊥) :
    Nonempty (ρ.Equiv (subQuot S T)) := by
  subst hS; subst hT
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective topBotMap topBotMap_bij) (fun g => by ext v; rfl)⟩

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Cast

theorem cast_cast {a b c : ℕ} (e : a = b) (e' : b = c) (π : GRep k a) :
    (π.cast e).cast e' = π.cast (e.trans e') := by
  subst e; subst e'; rfl

theorem cast_self {a : ℕ} (e : a = a) (π : GRep k a) : π.cast e = π := rfl

theorem nontrivial_cast_iff {a b : ℕ} (e : a = b) (π : GRep k a) : Nontrivial (π.cast e).V ↔ Nontrivial π.V := by
  subst e; rfl

theorem subsingleton_cast_iff {a b : ℕ} (e : a = b) (π : GRep k a) :
    Subsingleton (π.cast e).V ↔ Subsingleton π.V := by
  subst e; rfl

theorem isSmooth_cast {a b : ℕ} (e : a = b) {π : GRep k a} (h : IsSmooth π.ρ) : IsSmooth (π.cast e).ρ := by
  subst e; exact h

theorem isIrr_cast {a b : ℕ} (e : a = b) {π : GRep k a} (h : π.ρ.IsIrreducible) : (π.cast e).ρ.IsIrreducible := by
  subst e; exact h

theorem isUnit_cast {a b : ℕ} (e : a = b) {π : GRep k a} (h : IsUnitarisable π.ρ) :
    IsUnitarisable (π.cast e).ρ := by
  subst e; exact h

theorem isAdm_cast {a b : ℕ} (e : a = b) {π : GRep k a} (h : IsAdmissible π.ρ) : IsAdmissible (π.cast e).ρ := by
  subst e; exact h

theorem eig_cast {a b : ℕ} (h : a = b) (X : GRep k a) (x : kˣ) (c : ℂ) (y : (X.cast h).V) (hy : y ≠ 0)
    (hey : (X.cast h).ρ (sc b x) y = c • y) : ∃ y' : X.V, y' ≠ 0 ∧ X.ρ (sc a x) y' = c • y' := by
  subst h; exact ⟨y, hy, hey⟩

theorem derivB_nontrivial_congr (ψ : AddChar k Circle) {r n n' h : ℕ} (π : GRep k r) (e : r = n + h)
    (e' : r = n' + h) : Nontrivial (derivB ψ h (π.cast e)).V ↔ Nontrivial (derivB ψ h (π.cast e')).V := by
  obtain rfl : n = n' := by omega
  rfl

end Cast

section Tw

theorem isSmooth_derivB (ψ : AddChar k Circle) : ∀ (i : ℕ) {n : ℕ} {π : GRep k (n + i)}, IsSmooth π.ρ →
    IsSmooth (derivB ψ i π).ρ
  | 0, _, _, h => h
  | j + 1, _, _, h => GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j h

theorem isSmooth_tw {n : ℕ} {A : GRep k n} (h : IsSmooth A.ρ) (s : ℝ) : IsSmooth (A.tw s).ρ :=
  isSmooth_twist h (GlobalTheory.CompanionTheory.LeibPhi.isOpen_ker_dpow k n s)

theorem tw_apply {n : ℕ} (A : GRep k n) (s : ℝ) (g : GL (Fin n) k) (v : A.V) :
    (A.tw s).ρ g v = ((dpow n s g : ℂˣ) : ℂ) • A.ρ g v := twist_apply _ _ _ _

theorem lfin_tw {n : ℕ} {A : GRep k n} (h : LFin A) (s : ℝ) : LFin (A.tw s) := by
  intro a
  obtain ⟨U, hU, haU, hst⟩ := h a
  exact ⟨U, hU, haU, fun x u hu => U.smul_mem (((dpow n s (sc n x)) : ℂˣ) : ℂ) (hst x u hu)⟩

theorem nabs_pos' (x : kˣ) : 0 < nabs k x := NNReal.coe_pos.mpr MeasureTheory.distribHaarChar_pos

theorem norm_dpow_sc (n : ℕ) (s : ℝ) (x : kˣ) :
    ‖((dpow n s (sc n x) : ℂˣ) : ℂ)‖ = nabs k x ^ ((n : ℝ) * s) := by
  have hp := nabs_pos' x
  have hd : GeneralLinearGroup.det (sc n x) = x ^ n := by
    rw [sc, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  have hn : nabs k (x ^ n) = nabs k x ^ n := by unfold nabs; simp [map_pow]
  show ‖((absPow k (s : ℂ) (GeneralLinearGroup.det (sc n x)) : ℂˣ) : ℂ)‖ = _
  rw [hd]
  show ‖((nabs k (x ^ n) : ℝ) : ℂ) ^ (s : ℂ)‖ = _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (nabs_pos' _), Complex.ofReal_re, hn, ← Real.rpow_natCast_mul hp.le]

theorem untw_eig {n : ℕ} (A : GRep k n) (s : ℝ) (x : kˣ) (c : ℂ) (a : A.V) (h : (A.tw s).ρ (sc n x) a = c • a) :
    A.ρ (sc n x) a = ((((dpow n s (sc n x))⁻¹ : ℂˣ) : ℂ) * c) • a ∧
      ‖(((dpow n s (sc n x))⁻¹ : ℂˣ) : ℂ) * c‖ * nabs k x ^ ((n : ℝ) * s) = ‖c‖ := by
  rw [tw_apply] at h
  refine ⟨?_, ?_⟩
  · rw [mul_smul, ← h, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  · rw [← norm_dpow_sc, ← norm_mul, mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul]

theorem tw_eig {n : ℕ} (A : GRep k n) (s : ℝ) (x : kˣ) (d : ℂ) (a : A.V) (h : A.ρ (sc n x) a = d • a) :
    (A.tw s).ρ (sc n x) a = (((dpow n s (sc n x) : ℂˣ) : ℂ) * d) • a ∧
      ‖((dpow n s (sc n x) : ℂˣ) : ℂ) * d‖ = ‖d‖ * nabs k x ^ ((n : ℝ) * s) := by
  refine ⟨by rw [tw_apply, h, smul_smul], by rw [norm_mul, norm_dpow_sc, mul_comm]⟩

theorem tw_eig_move {n : ℕ} (A : GRep k n) (s s' : ℝ) (x : kˣ) (c : ℂ) (a : A.V)
    (h : (A.tw s).ρ (sc n x) a = c • a) :
    ∃ d : ℂ, (A.tw s').ρ (sc n x) a = d • a ∧ ‖c‖ = ‖d‖ * nabs k x ^ ((n : ℝ) * (s - s')) := by
  obtain ⟨h1, h2⟩ := untw_eig A s x c a h
  obtain ⟨h3, h4⟩ := tw_eig A s' x _ a h1
  refine ⟨_, h3, ?_⟩
  rw [h4, ← h2, mul_assoc, ← Real.rpow_add (nabs_pos' x)]
  congr 2
  ring

end Tw

section Prod

theorem subsingleton_piTwo {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (h : Subsingleton V ∨ Subsingleton W) : Subsingleton (PiTensorProduct ℂ (TwoT V W)) := by
  constructor
  have key : ∀ z : PiTensorProduct ℂ (TwoT V W), z = 0 := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rcases h with h | h
      · rw [MultilinearMap.map_coord_zero (PiTensorProduct.tprod ℂ) false
          (show f false = 0 from @Subsingleton.elim V h _ _), smul_zero]
      · rw [MultilinearMap.map_coord_zero (PiTensorProduct.tprod ℂ) true
          (show f true = 0 from @Subsingleton.elim W h _ _), smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  intro a b
  rw [key a, key b]

theorem subsingleton_prod {r t : ℕ} (A : GRep k r) (B : GRep k t) (h : Subsingleton A.V ∨ Subsingleton B.V) :
    Subsingleton (A.prod B).V := by
  haveI := subsingleton_piTwo h
  show Subsingleton (IndSp _ _)
  infer_instance

theorem nontrivial_prod {r t : ℕ} (A : GRep k r) (B : GRep k t) (hA : IsSmooth A.ρ) (hB : IsSmooth B.ρ)
    [Nontrivial A.V] [Nontrivial B.V] : Nontrivial (A.prod B).V := by
  haveI : ∀ x, Nontrivial (TwoT A.V B.V x) := fun x => by cases x <;> assumption
  haveI := GlobalTheory.CompanionTheory.AdjQuot.nontrivial_piTensorProduct (X := TwoT A.V B.V)
  exact GlobalTheory.CompanionTheory.AdjQuot.nontrivial_indSp _ (isSmooth_piTensor fun x => by cases x; exacts [hA, hB])

end Prod

section Top

def IsTop (ψ : AddChar k Circle) {r : ℕ} (π : GRep k r) (h : ℕ) : Prop :=
  h ≤ r ∧ (∀ (n : ℕ) (e : r = n + h), Nontrivial (derivB ψ h (π.cast e)).V) ∧
    ∀ (n h' : ℕ) (e : r = n + h'), h < h' → Subsingleton (derivB ψ h' (π.cast e)).V

theorem exists_isTop (ψ : AddChar k Circle) {r : ℕ} (π : GRep k r) [Nontrivial π.V] : ∃ h, IsTop ψ π h := by
  classical
  let P : ℕ → Prop := fun h => ∃ (n : ℕ) (e : r = n + h), Nontrivial (derivB ψ h (π.cast e)).V
  have hP0 : P 0 := ⟨r, (Nat.add_zero r).symm, (nontrivial_cast_iff (Nat.add_zero r).symm π).2 inferInstance⟩
  refine ⟨Nat.findGreatest P r, Nat.findGreatest_le r, fun n e => ?_, fun n h' e hlt => ?_⟩
  · obtain ⟨n0, e0, h0⟩ := Nat.findGreatest_spec (Nat.zero_le r) hP0
    exact (derivB_nontrivial_congr ψ π e0 e).1 h0
  · have hn := Nat.findGreatest_is_greatest hlt (by omega)
    exact not_nontrivial_iff_subsingleton.1 fun hh => hn ⟨n, e, hh⟩

theorem isTop_pos (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {r : ℕ} (π : GRep k r)
    (hs : IsSmooth π.ρ) [Nontrivial π.V] {h : ℕ} (T : IsTop ψ π h) (hr : 0 < r) : 1 ≤ h := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨n0, hn0, hnt⟩ := GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial k ψ hc h1 m π.V
    (resM k π.ρ).ρ (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_resM hs) inferInstance
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn0
  obtain ⟨E⟩ := GlobalTheory.T.twisted_jacquet_iterated_phi_equiv k ψ n0 j (resM k π.ρ)
  by_contra hlt
  have hsub := T.2.2 n0 (j + 1) rfl (by omega)
  have : Nontrivial (TwJacquet (iterPhi k ψ j (resM k π.ρ)).ρ (MirUin k n0) 1) := @Equiv.nontrivial _ _ E.toEquiv hnt
  exact not_nontrivial_iff_subsingleton.2 hsub this

end Top

section Leib

variable (ψ : AddChar k Circle)

theorem piece_sub {r t : ℕ} (π₁ : GRep k r) (π₂ : GRep k t) {h₁ h₂ : ℕ} (T₁ : IsTop ψ π₁ h₁) (T₂ : IsTop ψ π₂ h₂)
    (ℓ i n : ℕ) (h : i ≤ r ∧ ℓ - i ≤ t) (hsz : (r - i) + (t - (ℓ - i)) = n) (hne : ¬ (i ≤ h₁ ∧ ℓ - i ≤ h₂)) :
    Subsingleton ((((derivB ψ i (π₁.cast (Nat.sub_add_cancel h.1).symm)).tw (((ℓ - i : ℕ) : ℝ) / 2)).prod
      ((derivB ψ (ℓ - i) (π₂.cast (Nat.sub_add_cancel h.2).symm)).tw ((i : ℝ) / 2))).cast hsz).V := by
  rw [subsingleton_cast_iff]
  apply subsingleton_prod
  by_cases hi : i ≤ h₁
  · right; exact T₂.2.2 _ _ _ (by omega)
  · left; exact T₁.2.2 _ _ _ (by omega)

theorem deriv_prod_sub (hc : Continuous ψ) (h1 : ψ ≠ 1) (hL : GlobalTheory.RgGu.Leib.LeibnizOrd k) {r t : ℕ}
    (π₁ : GRep k r) (π₂ : GRep k t) (s₁ : IsSmooth π₁.ρ) (s₂ : IsSmooth π₂.ρ) {h₁ h₂ : ℕ} (T₁ : IsTop ψ π₁ h₁)
    (T₂ : IsTop ψ π₂ h₂) (ℓ n : ℕ) (e : r + t = n + ℓ) (hl : h₁ + h₂ < ℓ) :
    Subsingleton (derivB ψ ℓ ((π₁.prod π₂).cast e)).V := by
  obtain ⟨F, hF, h0, hl', hpc⟩ := hL ψ hc h1 r t ℓ n e π₁ π₂ s₁ s₂
  refine subsingleton_of_filt h0 hl' fun i hi => ?_
  have hp := hpc i hi
  by_cases hcond : i ≤ r ∧ ℓ - i ≤ t
  · rw [dif_pos hcond] at hp
    obtain ⟨hsz, ⟨E⟩⟩ := hp
    have := piece_sub ψ π₁ π₂ T₁ T₂ ℓ i n hcond hsz (by omega)
    have := E.toLinearEquiv.toEquiv.subsingleton
    exact le_antisymm le_of_subsingleton_subQuot (hF (Nat.le_succ i))
  · rw [dif_neg hcond] at hp
    exact hp

theorem piece_iso {r t h₁ n : ℕ} (π₁ : GRep k r) (π₂ : GRep k t) (hh₁ : h₁ ≤ r) (m : ℕ) (hmt : m ≤ t)
    (hsz : (r - h₁) + (t - m) = n) (L : ℝ) (hL : (h₁ : ℝ) + (m : ℝ) = L) :
    GlobalTheory.RgGu.Leib.GIso ((((derivB ψ h₁ (π₁.cast (Nat.sub_add_cancel hh₁).symm)).tw (((m : ℕ) : ℝ) / 2)).prod
                 ((derivB ψ m (π₂.cast (Nat.sub_add_cancel hmt).symm)).tw ((h₁ : ℝ) / 2))).cast hsz)
      (((((derivB ψ h₁ (π₁.cast (Nat.sub_add_cancel hh₁).symm)).tw ((1 - (h₁ : ℝ)) / 2)).prod
        ((derivB ψ m (π₂.cast (Nat.sub_add_cancel hmt).symm)).tw ((1 - (m : ℝ)) / 2))).cast hsz).tw ((L - 1) / 2)) := by
  have e1 : (1 - (h₁ : ℝ)) / 2 + (L - 1) / 2 = ((m : ℕ) : ℝ) / 2 := by rw [← hL]; ring
  have e2 : (1 - (m : ℝ)) / 2 + (L - 1) / 2 = (h₁ : ℝ) / 2 := by rw [← hL]; ring
  have i1 := GlobalTheory.CompanionTheory.LeibOrd.Main.tw_tw (derivB ψ h₁ (π₁.cast (Nat.sub_add_cancel hh₁).symm)) ((1 - (h₁ : ℝ)) / 2)
    ((L - 1) / 2)
  rw [e1] at i1
  have i2 := GlobalTheory.CompanionTheory.LeibOrd.Main.tw_tw (derivB ψ m (π₂.cast (Nat.sub_add_cancel hmt).symm)) ((1 - (m : ℝ)) / 2)
    ((L - 1) / 2)
  rw [e2] at i2
  have iPQ := GlobalTheory.CompanionTheory.LeibOrd.giso_symm (GlobalTheory.CompanionTheory.LeibOrd.giso_trans (GlobalTheory.CompanionTheory.LeibOrd.Main.tw_prod _ _ ((L - 1) / 2))
    (GlobalTheory.CompanionTheory.LeibOrd.giso_prod i1 i2))
  exact GlobalTheory.CompanionTheory.LeibOrd.giso_trans (GlobalTheory.CompanionTheory.LeibOrd.giso_cast hsz iPQ)
    (GlobalTheory.CompanionTheory.LeibOrd.giso_symm (GlobalTheory.CompanionTheory.LeibOrd.tw_cast hsz _ _))

theorem dpow_eq_one {m : ℕ} (hm : m = 0) (s : ℝ) (g : GL (Fin m) k) : dpow m s g = 1 := by
  subst hm
  have : GeneralLinearGroup.det g = 1 := Units.ext (by rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_zero,
    Units.val_one])
  rw [dpow, detChar_apply, this, map_one]

theorem sigma_facts (hT : DerivTop k) (hc : Continuous ψ) (h1 : ψ ≠ 1) {r : ℕ} (π : GRep k r) (hs : IsSmooth π.ρ)
    (hi : π.ρ.IsIrreducible) (hu : IsUnitarisable π.ρ) {h : ℕ} (T : IsTop ψ π h) (hr : 0 < r → 1 ≤ h) (hh : h ≤ r) :
    IsSmooth ((derivB ψ h (π.cast (Nat.sub_add_cancel hh).symm)).tw ((1 - (h : ℝ)) / 2)).ρ ∧
      ((derivB ψ h (π.cast (Nat.sub_add_cancel hh).symm)).tw ((1 - (h : ℝ)) / 2)).ρ.IsIrreducible ∧
      IsUnitarisable ((derivB ψ h (π.cast (Nat.sub_add_cancel hh).symm)).tw ((1 - (h : ℝ)) / 2)).ρ ∧
      Nontrivial ((derivB ψ h (π.cast (Nat.sub_add_cancel hh).symm)).tw ((1 - (h : ℝ)) / 2)).V := by
  set σ := (derivB ψ h (π.cast (Nat.sub_add_cancel hh).symm)).tw ((1 - (h : ℝ)) / 2) with hσ
  suffices hIU : σ.ρ.IsIrreducible ∧ IsUnitarisable σ.ρ by
    exact ⟨isSmooth_tw (isSmooth_derivB ψ h (isSmooth_cast _ hs)) _, hIU.1, hIU.2, T.2.1 _ _⟩
  rw [hσ]
  by_cases h0 : h = 0
  · subst h0
    have hr0 : r - 0 = 0 := by
      by_contra hne
      have := hr (by omega)
      omega
    exact ⟨isIrreducible_twist (isIrr_cast _ hi) _,
      isUnitarisable_twist_one (isUnit_cast _ hu) _ (dpow_eq_one hr0 _)⟩
  · exact hT ψ hc h1 (r - h) h (π.cast (Nat.sub_add_cancel hh).symm) (by omega) (isSmooth_cast _ hs)
      (isIrr_cast _ hi) (isUnit_cast _ hu) (T.2.1 _ _)
      (fun n' h' e2 hlt => by rw [cast_cast]; exact T.2.2 _ _ _ hlt)

end Leib

variable (k) in
theorem topProd_of : DerivTop k → DerivPos k → GlobalTheory.RgGu.Leib.LeibnizOrd k → LFDeriv k → CentralSub k → EigProd k →
    EigFilt k → TopProdD k := by
  intro hT _ hL _ _ _ _ ψ hc h1 r t π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂ hrt
  haveI := nontrivial_of_irr i₁
  haveI := nontrivial_of_irr i₂
  obtain ⟨h₁, T₁⟩ := exists_isTop ψ π₁
  obtain ⟨h₂, T₂⟩ := exists_isTop ψ π₂
  have p₁ : 0 < r → 1 ≤ h₁ := isTop_pos ψ hc h1 π₁ s₁ T₁
  have p₂ : 0 < t → 1 ≤ h₂ := isTop_pos ψ hc h1 π₂ s₂ T₂
  have hm : h₁ + h₂ - h₁ = h₂ := by omega
  have T₂' : IsTop ψ π₂ (h₁ + h₂ - h₁) := by rw [hm]; exact T₂
  have p₂' : 0 < t → 1 ≤ h₁ + h₂ - h₁ := by rw [hm]; exact p₂
  have hh₁ := T₁.1
  have hh₂ := T₂'.1
  have hpos : 0 < h₁ + h₂ := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · have := p₂ (by omega); omega
    · have := p₁ hr; omega
  have e : r + t = ((r - h₁) + (t - (h₁ + h₂ - h₁))) + (h₁ + h₂) := by omega
  obtain ⟨F, hF, h0, hl, hpc⟩ := hL ψ hc h1 r t (h₁ + h₂) _ e π₁ π₂ s₁ s₂
  have key : ∀ i ≤ h₁ + h₂, i ≠ h₁ → F i = F (i + 1) := by
    intro i hi hne
    have hp := hpc i hi
    by_cases hcond : i ≤ r ∧ h₁ + h₂ - i ≤ t
    · rw [dif_pos hcond] at hp
      obtain ⟨hsz, ⟨E⟩⟩ := hp
      have := piece_sub ψ π₁ π₂ T₁ T₂ (h₁ + h₂) i _ hcond hsz (by omega)
      have := E.toLinearEquiv.toEquiv.subsingleton
      exact le_antisymm le_of_subsingleton_subQuot (hF (Nat.le_succ i))
    · rw [dif_neg hcond] at hp
      exact hp
  obtain ⟨hA, hB⟩ := filt_single (by omega : h₁ ≤ h₁ + h₂) h0 hl key
  obtain ⟨E1⟩ := equiv_subQuot hA hB
  have hp := hpc h₁ (by omega)
  rw [dif_pos (⟨hh₁, hh₂⟩ : h₁ ≤ r ∧ h₁ + h₂ - h₁ ≤ t)] at hp
  obtain ⟨hsz, ⟨E2⟩⟩ := hp
  have i3 := piece_iso ψ π₁ π₂ hh₁ (h₁ + h₂ - h₁) hh₂ hsz (((h₁ + h₂ : ℕ) : ℝ)) (by rw [hm]; push_cast; ring)
  obtain ⟨E3⟩ := GlobalTheory.CompanionTheory.LeibOrd.giso_trans ⟨E1.trans E2⟩ i3
  obtain ⟨sm₁, ir₁, un₁, nt₁⟩ := sigma_facts ψ hT hc h1 π₁ s₁ i₁ u₁ T₁ p₁ hh₁
  obtain ⟨sm₂, ir₂, un₂, nt₂⟩ := sigma_facts ψ hT hc h1 π₂ s₂ i₂ u₂ T₂' p₂' hh₂
  have hQ := nontrivial_prod _ _ sm₁ sm₂
  have hQ' := (nontrivial_cast_iff hsz _).2 hQ
  refine ⟨_, h₁ + h₂, e, hpos, ⟨@Equiv.nontrivial _ _ E3.toLinearEquiv.toEquiv hQ', fun n' h' e2 hlt => ?_⟩,
    r - h₁, t - (h₁ + h₂ - h₁), hsz, _, _, _, sm₁, ir₁, un₁, sm₂, ir₂, un₂, ⟨E3⟩⟩
  rw [cast_cast]
  exact deriv_prod_sub ψ hc h1 hL π₁ π₂ s₁ s₂ T₁ T₂ h' n' (e.trans e2) hlt

end PositivityTheory.RgUd.Prod.Pos2
