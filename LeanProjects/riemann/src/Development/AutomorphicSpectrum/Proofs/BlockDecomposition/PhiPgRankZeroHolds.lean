import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemTwKerPolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedBallIndicatorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantFiniteBallSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionBallIndicatorSpanStatement
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.PhiPG0

noncomputable section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier
open scoped Topology
namespace GlobalTheory.CompanionTheory.MirLevi
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

theorem exists_polyBall_subset {n : ℕ} {U : Set (Multiplicative (Fin n → k))} (hU : U ∈ 𝓝 (1 : Multiplicative (Fin n → k))) :
    ∃ s : kˣ, (polyBall (k := k) n s : Set (Multiplicative (Fin n → k))) ⊆ U := by
  have h0 : Multiplicative.ofAdd ⁻¹' U ∈ 𝓝 (0 : Fin n → k) :=
    (continuous_ofAdd (X := Fin n → k)).continuousAt.preimage_mem_nhds (by simpa using hU)
  rw [nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, -, t, ht, hs⟩ := h0
  choose s hs' using fun i => exists_cball_subset (ht i)
  by_cases hn : Nonempty (Fin n)
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min (fun i => ValuativeRel.valuation k (s i : k))
    refine ⟨s i₀, fun x hx => hs ?_⟩
    intro i _
    exact hs' i (show ValuativeRel.valuation k (Multiplicative.toAdd x i) ≤ ValuativeRel.valuation k (s i : k) from le_trans (hx i) (hi₀ i))
  · refine ⟨1, fun x _ => hs ?_⟩
    intro i _
    exact (hn ⟨i⟩).elim

theorem restr_periodic (ρ : Representation ℂ (LH k n) E) (f : cIndSpace (LH k n) ρ) : ∃ s : kˣ, ∀ (v a : Fin n → k),
    Multiplicative.ofAdd a ∈ polyBall (k := k) n s → restr ρ f (v + a) = restr ρ f v := by
  have hopen : IsOpen {g : Mir k n | ind (LH k n) ρ g f.1.1 = f.1.1} := f.1.2
  have hU : (unipIn k n) ⁻¹' {g : Mir k n | ind (LH k n) ρ g f.1.1 = f.1.1} ∈ 𝓝 (1 : Multiplicative (Fin n → k)) :=
    (hopen.preimage (continuous_unipIn n)).mem_nhds (by simp)
  have hs := exists_polyBall_subset hU
  refine ⟨hs.choose, fun v a ha => ?_⟩
  have h1 : ind (LH k n) ρ (uv n a) f.1.1 = f.1.1 := hs.choose_spec ha
  show f.1.1.1 (uv n (v + a)) = f.1.1.1 (uv n v)
  rw [uv_add]
  exact congrFun (congrArg Subtype.val h1) (uv n v)

theorem continuous_mvec (n : ℕ) : Continuous (mvec (k := k) (n := n)) := by
  have h1 : Continuous fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    Units.continuous_val.comp (GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n).inv
  have h2 : Continuous (colv (k := k) (n := n)) := by
    refine continuous_pi fun i => ?_
    have : Continuous fun g : Mir k n => ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      Units.continuous_val.comp continuous_subtype_val
    exact this.matrix_elem _ _
  exact h1.matrix_mulVec h2

theorem exists_compact_polyBall (n : ℕ) {C : Set (Fin n → k)} (hC : IsCompact C) :
    ∃ S : kˣ, ∀ v ∈ C, Multiplicative.ofAdd v ∈ polyBall (k := k) n S := by
  have hC' : IsCompact (Multiplicative.ofAdd '' C) := hC.image continuous_ofAdd
  obtain ⟨t, ht⟩ := hC'.elim_finite_subcover (fun s : kˣ => (polyBall (k := k) n s : Set (Multiplicative (Fin n → k))))
    (fun s => isOpen_polyBall n s) (fun x _ => Set.mem_iUnion.2 (exists_mem_polyBall x))
  classical
  have hb : ∀ t : Finset kˣ, ∃ S : kˣ, ∀ s ∈ t, polyBall (k := k) n s ≤ polyBall n S := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | insert a t _ ih =>
      obtain ⟨S, hS⟩ := ih
      rcases le_total (ValuativeRel.valuation k (a : k)) (ValuativeRel.valuation k (S : k)) with h | h
      · refine ⟨S, fun s hs => ?_⟩
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact polyBall_mono _ h
        · exact hS s hs
      · refine ⟨a, fun s hs => ?_⟩
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact le_rfl
        · exact (hS s hs).trans (polyBall_mono _ h)
  obtain ⟨S, hS⟩ := hb t
  refine ⟨S, fun v hv => ?_⟩
  have := ht ⟨v, hv, rfl⟩
  simp only [Set.mem_iUnion] at this
  obtain ⟨s, hs, hx⟩ := this
  exact hS s hs hx

theorem support_abs (F : Mir k n → E) (C : Set (Mir k n))
    (hF : ∀ g, F g ≠ 0 → ∃ h ∈ LH k n, ∃ c ∈ C, g = h * c) (v : Fin n → k) (hv : F (uv n v) ≠ 0) :
    v ∈ mvec '' C := by
  obtain ⟨h, ⟨m, rfl⟩, c, hc, e⟩ := hF _ hv
  refine ⟨c, hc, ?_⟩
  have := congrArg mvec e
  rw [mvec_uv, mvec_levi_mul] at this
  exact this.symm

theorem restr_support (ρ : Representation ℂ (LH k n) E) (f : cIndSpace (LH k n) ρ) : ∃ S : kˣ, ∀ v : Fin n → k,
    restr ρ f v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S := by
  have hC := f.2
  have hS := exists_compact_polyBall n (hC.choose_spec.1.image (continuous_mvec n))
  exact ⟨hS.choose, fun v hv => hS.choose_spec v (support_abs _ _ hC.choose_spec.2 v hv)⟩

open Classical in
theorem exists_bump (ρ : Representation ℂ (LH k n) E) (hρ : IsSmooth ρ) (s : kˣ) (e : E) :
    ∃ b : cIndSpace (LH k n) ρ, ∀ v : Fin n → k,
      restr ρ b v = if Multiplicative.ofAdd v ∈ polyBall (k := k) n s then e else 0 :=
  GlobalTheory.T.exists_induced_ball_indicator k n E ρ hρ s e

open Classical in
theorem exists_reps (φ : (Fin n → k) → E) (s S : kˣ)
    (hper : ∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → φ (v + a) = φ v)
    (hsupp : ∀ v : Fin n → k, φ v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) :
    ∃ R : Finset (Fin n → k), ∀ v : Fin n → k,
      φ v = ∑ x ∈ R, if Multiplicative.ofAdd (v - x) ∈ polyBall (k := k) n s then φ x else 0 :=
  GlobalTheory.T.locally_constant_finite_ball_sum k n E φ s S hper hsupp

open Classical in
theorem exists_strictHenselian_absolutely_closed_local_ring (ψ : AddChar k Circle) (hψ : Continuous ψ) (N : ℕ) (ρ : Representation ℂ (LH k (N + 1)) E) :
    ∃ T : cIndSpace (LH k (N + 1)) ρ →ₗ[ℂ] E,
      (∀ (a : Fin (N + 1) → k) (f), T (cInd (LH k (N + 1)) ρ (uv (N + 1) a) f) = ((ψ (a (Fin.last N)) : Circle) : ℂ) • T f) ∧
      (∀ (m : GL (Fin (N + 1)) k), m ∈ Mir k N → ∀ f, T (cInd (LH k (N + 1)) ρ (levi k (N + 1) m) f) =
        ((nabs k (Matrix.GeneralLinearGroup.det m) : ℝ) : ℂ) • ρ (lv k (N + 1) m) (T f)) ∧
      (∀ s : kˣ, (∀ a : Fin (N + 1) → k, Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → ψ (a (Fin.last N)) = 1) →
        ∃ c : ℂ, c ≠ 0 ∧ ∀ (b : cIndSpace (LH k (N + 1)) ρ) (e : E),
          (∀ v, restr ρ b v = if Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s then e else 0) → T b = c • e) :=
  GlobalTheory.T.restriction_ball_indicator_span k ψ hψ N _ E (restr ρ) (restr_periodic ρ) (restr_support ρ)
    (fun a f => cInd (LH k (N + 1)) ρ (uv (N + 1) a) f) (fun a f v => restr_uv ρ a f v)
    (fun m f => cInd (LH k (N + 1)) ρ (levi k (N + 1) m) f) (fun m => ρ (lv k (N + 1) m))
    (fun m f v => restr_levi ρ m f v)

theorem uv_mem (N : ℕ) (a : Fin N → k) : uv N a ∈ MirUin k N := by
  show ((uv N a : Mir k N) : GL (Fin (N + 1)) k) ∈ MirU k N
  exact ⟨_, rfl⟩

theorem exists_small (ψ : AddChar k Circle) (hψ : Continuous ψ) (N : ℕ) :
    ∃ s : kˣ, ∀ a : Fin (N + 1) → k, Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → ψ (a (Fin.last N)) = 1 := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  exact ⟨s, fun a ha => hs _ (ha (Fin.last N))⟩

theorem exists_common (n : ℕ) (s₁ s₂ : kˣ) :
    ∃ s : kˣ, polyBall (k := k) n s ≤ polyBall n s₁ ∧ polyBall (k := k) n s ≤ polyBall n s₂ := by
  rcases le_total (ValuativeRel.valuation k (s₁ : k)) (ValuativeRel.valuation k (s₂ : k)) with h | h
  · exact ⟨s₁, le_rfl, polyBall_mono _ h⟩
  · exact ⟨s₂, polyBall_mono _ h, le_rfl⟩

theorem exists_unipIn {N : ℕ} (u : MirUin k N) : ∃ x : Fin N → k, uv N x = (u : Mir k N) := by
  obtain ⟨x, hx⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k N) : GL (Fin (N + 1)) k) ∈ MirU k N)
  exact ⟨x.toAdd, Subtype.ext hx⟩

theorem twKer_le_ker {G X E : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E]
    (π : Representation ℂ G X) (N : Subgroup G) (χ : N →* ℂˣ) (T : X →ₗ[ℂ] E)
    (h : ∀ (n : N) (x : X), T (π (n : G) x) = ((χ n : ℂˣ) : ℂ) • T x) : twKer π N χ ≤ LinearMap.ker T := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, g, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, h, sub_self]

theorem tw_equiv {G M X E : Type} [Group G] [Group M] [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E]
    (π : Representation ℂ G X) (N : Subgroup G) (χ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, χ ⟨_, h⟩ = χ n)
    (T : X →ₗ[ℂ] E) (hsurj : Function.Surjective T) (hker : LinearMap.ker T = twKer π N χ)
    (ρ' : Representation ℂ M E) (hint : ∀ (m : M) (x : X), T (π (s m) x) = ρ' m (T x)) :
    Nonempty ((twAct π N χ s hs).Equiv ρ') := by
  let e : (X ⧸ twKer π N χ) ≃ₗ[ℂ] E :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (T.quotKerEquivOfSurjective hsurj)
  refine ⟨Representation.Equiv.mk e fun m => ?_⟩
  ext x
  show T (π (s m) x) = ρ' m (T x)
  exact hint m x

theorem ker_abs {X E A : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E] [AddCommGroup A]
    (T : X →ₗ[ℂ] E) (r : X →ₗ[ℂ] A → E) (hinj : Function.Injective r) (tr : A → X →ₗ[ℂ] X)
    (hr : ∀ a f v, r (tr a f) v = r f (v + a)) (χ : A → ℂ)
    (hT1 : ∀ a f, T (tr a f) = χ a • T f) (L : A → Prop) [DecidablePred L] (c : ℂ) (hc : c ≠ 0) (b : E → X)
    (hb : ∀ e v, r (b e) v = if L v then e else 0) (hTb : ∀ e, T (b e) = c • e)
    (K : Submodule ℂ X) (key : ∀ x g, tr (-x) g - χ (-x) • g ∈ K) (f : X) (hf : T f = 0) (R : Finset A)
    (hR : ∀ v, r f v = ∑ x ∈ R, if L (v - x) then r f x else 0) : f ∈ K := by
  obtain ⟨w, hw⟩ : ∃ w : E, w = ∑ x ∈ R, χ (-x) • r f x := ⟨_, rfl⟩
  have hf1 : f = ∑ x ∈ R, tr (-x) (b (r f x)) := by
    apply hinj
    funext v
    rw [map_sum, Finset.sum_apply]
    conv_lhs => rw [hR v]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hr, hb, sub_eq_add_neg]
  have hbsum : ∑ x ∈ R, χ (-x) • b (r f x) = b w := by
    apply hinj
    funext v
    rw [map_sum, Finset.sum_apply, hb]
    simp only [map_smul, Pi.smul_apply, hb]
    by_cases hv : L v
    · simp [hv, hw]
    · simp [hv]
  have hTf : T f = c • w := by
    rw [hf1, map_sum]
    simp only [hT1, hTb]
    rw [hw, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_comm]
  have hw0 : w = 0 := by
    rw [hTf] at hf
    exact (smul_eq_zero.1 hf).resolve_left hc
  have hb0 : b w = 0 := by
    apply hinj
    funext v
    rw [hb, hw0, map_zero]
    simp
  have h3 : f = ∑ x ∈ R, (tr (-x) (b (r f x)) - χ (-x) • b (r f x)) := by
    rw [Finset.sum_sub_distrib, hbsum, hb0, sub_zero]
    exact hf1
  rw [h3]
  exact Submodule.sum_mem _ fun x _ => key x _

theorem mirChar_unipotent_vector (ψ : AddChar k Circle) (N : ℕ) (x : Fin (N + 1) → k) :
    (mirChar k ψ N ⟨uv (N + 1) x, uv_mem _ x⟩ : ℂˣ) = Circle.toUnits (ψ (x (Fin.last N))) :=
  mirChar_eq k ψ N _ (Multiplicative.ofAdd x) rfl

theorem mirChar_uv' (ψ : AddChar k Circle) (N : ℕ) (x : Fin (N + 1) → k) :
    ((mirChar k ψ N ⟨uv (N + 1) x, uv_mem _ x⟩ : ℂˣ) : ℂ) = ((ψ (x (Fin.last N)) : Circle) : ℂ) :=
  congrArg Units.val (mirChar_unipotent_vector ψ N x)

theorem T_mirChar (ψ : AddChar k Circle) (N : ℕ) (ρ : Representation ℂ (LH k (N + 1)) E)
    (T : cIndSpace (LH k (N + 1)) ρ →ₗ[ℂ] E)
    (hT1 : ∀ (a : Fin (N + 1) → k) (f), T (cInd (LH k (N + 1)) ρ (uv (N + 1) a) f) = ((ψ (a (Fin.last N)) : Circle) : ℂ) • T f)
    (u : MirUin k (N + 1)) (g : cIndSpace (LH k (N + 1)) ρ) :
    T (cInd (LH k (N + 1)) ρ (u : Mir k (N + 1)) g) = ((mirChar k ψ N u : ℂˣ) : ℂ) • T g := by
  have e : u = ⟨uv (N + 1) (exists_unipIn u).choose, uv_mem _ _⟩ := Subtype.ext (exists_unipIn u).choose_spec.symm
  exact (congrArg (fun w : MirUin k (N + 1) => T (cInd (LH k (N + 1)) ρ (w : Mir k (N + 1)) g)) e).trans
    ((hT1 _ g).trans ((congrArg (· • T g) (mirChar_uv' ψ N _).symm).trans
      (congrArg (fun w : MirUin k (N + 1) => ((mirChar k ψ N w : ℂˣ) : ℂ) • T g) e.symm)))

open Classical in
theorem ker_eq (ψ : AddChar k Circle) (hψ : Continuous ψ) (N : ℕ) (ρ : Representation ℂ (LH k (N + 1)) E) (hρ : IsSmooth ρ)
    (T : cIndSpace (LH k (N + 1)) ρ →ₗ[ℂ] E)
    (hT1 : ∀ (a : Fin (N + 1) → k) (f), T (cInd (LH k (N + 1)) ρ (uv (N + 1) a) f) = ((ψ (a (Fin.last N)) : Circle) : ℂ) • T f)
    (hT3 : ∀ s : kˣ, (∀ a : Fin (N + 1) → k, Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → ψ (a (Fin.last N)) = 1) →
        ∃ c : ℂ, c ≠ 0 ∧ ∀ (b : cIndSpace (LH k (N + 1)) ρ) (e : E),
          (∀ v, restr ρ b v = if Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s then e else 0) → T b = c • e) :
    LinearMap.ker T = twKer (cInd (LH k (N + 1)) ρ) (MirUin k (N + 1)) (mirChar k ψ N) := by
  apply le_antisymm
  · intro f hf
    have hs₁ := (restr_periodic ρ f).choose_spec
    have hs₂ := (exists_small ψ hψ N).choose_spec
    have hS := (restr_support ρ f).choose_spec
    have hs := exists_common (N + 1) (restr_periodic ρ f).choose (exists_small ψ hψ N).choose
    have h1 := hs.choose_spec.1
    have h2 := hs.choose_spec.2
    have hc3 := hT3 hs.choose (fun a ha => hs₂ a (h2 ha))
    have hR := exists_reps (restr ρ f) hs.choose (restr_support ρ f).choose (fun v a ha => hs₁ v a (h1 ha)) hS
    refine ker_abs T (restr ρ) (restr_injective ρ) (fun a => (cInd (LH k (N + 1)) ρ (uv (N + 1) a)))
      (fun a f v => restr_uv ρ a f v) (fun a => ((ψ (a (Fin.last N)) : Circle) : ℂ)) hT1
      (fun v => Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) hs.choose) hc3.choose hc3.choose_spec.1
      (fun e => (exists_bump ρ hρ hs.choose e).choose)
      (fun e => (exists_bump ρ hρ hs.choose e).choose_spec)
      (fun e => hc3.choose_spec.2 _ _ (exists_bump ρ hρ hs.choose e).choose_spec)
      _ (fun x g => ?_) f hf hR.choose hR.choose_spec
    refine Submodule.subset_span ⟨⟨_, uv_mem _ (-x)⟩, g, ?_⟩
    exact congrArg (fun c : ℂ => cInd (LH k (N + 1)) ρ (uv (N + 1) (-x)) g - c • g) (mirChar_uv' ψ N (-x)).symm
  · exact twKer_le_ker _ _ _ T (T_mirChar ψ N ρ T hT1)

open GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.SmGL
open scoped TensorProduct

theorem mem_HPG_zero_iff (n : ℕ) (g : Mir k (0 + n)) :
    g ∈ HPG k 0 n ↔ ∀ b : Fin n, ((g : GL (Fin (0 + n + 1)) k) : Matrix (Fin (0 + n + 1)) (Fin (0 + n + 1)) k)
      (ePG 0 n ⟨true, b⟩) (Fin.last (0 + n)) = 0 := by
  show (g : GL (Fin (0 + n + 1)) k) ∈ parab k (ePG 0 n) ↔ _
  rw [mem_parab_iff]
  constructor
  · intro h b
    have := h true false b (Fin.last 0) (by decide)
    rwa [ePG_false_last] at this
  · intro h a c i j hac
    obtain ⟨rfl, rfl⟩ : a = true ∧ c = false := by
      revert hac; cases a <;> cases c <;> decide
    have hj : j = Fin.last 0 := Fin.ext (by have := j.2; simp only [Fin.val_last]; omega)
    subst hj
    rw [ePG_false_last]
    exact h i

theorem HPG_zero (n : ℕ) : HPG k 0 n = LH k (0 + n) := by
  ext g
  rw [mem_HPG_zero_iff]
  constructor
  · intro h
    have hc : colv g = 0 := by
      funext i
      have hne : Fin.castSucc i ≠ Fin.last (0 + n) := Fin.castSucc_ne_last i
      obtain ⟨⟨a, b⟩, hab⟩ := (ePG 0 n).surjective (Fin.castSucc i)
      cases a with
      | false =>
        exfalso
        apply hne
        rw [← hab]
        exact (ePG_false_eq_last_iff 0 n b).2 (Fin.ext (by have := b.2; simp only [Fin.val_last]; omega))
      | true =>
        have := h b
        rw [hab] at this
        exact this
    have hv : mvec g = 0 := by simp [mvec, hc]
    refine ⟨mirabolicProjection k _ g, ?_⟩
    conv_rhs => rw [decomp g, hv, uv_zero, mul_one]
  · rintro ⟨m, rfl⟩ b
    have hne : ePG 0 n ⟨true, b⟩ ≠ Fin.last (0 + n) := by
      intro e
      have := (ePG 0 n).injective (e.trans (ePG_false_last 0 n).symm)
      simp at this
    obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hne
    rw [← hi]
    show glEmbMat k _ (m : Matrix _ _ k) (Fin.castSucc i) (Fin.last _) = 0
    simp [glEmbMat]

theorem mirabolicParabolic_zero_left_eq_top (t : ℕ) : MirabolicParabolic k 0 t = ⊤ := by
  rw [eq_top_iff]
  intro g _
  show (g : GL (Fin (0 + t + 1)) k) ∈ parab k (eGP 0 t)
  rw [mem_parab_iff]
  intro a c i j hac
  obtain ⟨rfl, rfl⟩ : a = true ∧ c = false := by
    revert hac; cases a <;> cases c <;> decide
  exact j.elim0

theorem smooth_gp {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (m j : ℕ)
    (a : Representation ℂ (GL (Fin m) k) V) (b : Representation ℂ (Mir k j) W) (ha : IsSmooth a) (hb : IsSmooth b) :
    IsSmooth ((extTensor a b).comp (gpProj k m j)) :=
  isSmooth_comp (isSmooth_extTensor ha hb) _ (GlobalTheory.CompanionTheory.BZMir.continuous_gpProj k m j)

theorem continuous_pgProj (i t : ℕ) : Continuous (pgProj k i t) := by
  have hincl : Continuous (hpgIncl k i t) :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have hlevi : Continuous fun h : HPG k i t => leviProj k (ePG i t) (hpgIncl k i t h) :=
    (GlobalTheory.SmGL.LeviInt.levi_integral_facts k Bool (Fin (i + t + 1)) (Two (Fin (i + 1)) (Fin t))
      (ePG i t)).2.2.2.2.2.1.comp hincl
  exact Continuous.prodMk (Continuous.subtype_mk ((continuous_apply false).comp hlevi) _)
    ((continuous_apply true).comp hlevi)

theorem smooth_pg {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (i t : ℕ)
    (a : Representation ℂ (Mir k i) V) (b : Representation ℂ (GL (Fin t) k) W) (ha : IsSmooth a) (hb : IsSmooth b) :
    IsSmooth ((extTensor a b).comp (pgProj k i t)) :=
  isSmooth_comp (isSmooth_extTensor ha hb) _ (continuous_pgProj i t)

theorem ePG_zero_true (t : ℕ) (b : Fin (t + 1)) : (ePG 0 (t + 1) ⟨true, b⟩ : Fin (0 + (t + 1) + 1)).val = b.val := by
  simp [ePG, two]

theorem blockIndex_zero_true_val (t : ℕ) (b : Fin (t + 1)) : (eGP 0 t ⟨true, b⟩ : Fin (0 + t + 1)).val = b.val := by
  simp [eGP, two, stdSum]

theorem pg_gp (t : ℕ) (m : Mir k (0 + t)) (h₁ : levi k (0 + t + 1) (m : GL (Fin (0 + t + 1)) k) ∈ HPG k 0 (t + 1))
    (h₂ : m ∈ MirabolicParabolic k 0 t) :
    (pgProj k 0 (t + 1) ⟨_, h₁⟩).2 = ((gpProj k 0 t ⟨m, h₂⟩).2 : GL (Fin (t + 1)) k) := by
  apply Units.ext
  ext i j
  show ((levi k (0 + t + 1) (m : GL (Fin (0 + t + 1)) k) : Mir k (0 + t + 1)) : GL (Fin (0 + t + 1 + 1)) k).val
      (ePG 0 (t + 1) ⟨true, i⟩) (ePG 0 (t + 1) ⟨true, j⟩) =
    (m : GL (Fin (0 + t + 1)) k).val (eGP 0 t ⟨true, i⟩) (eGP 0 t ⟨true, j⟩)
  have e : ∀ b : Fin (t + 1), (ePG 0 (t + 1) ⟨true, b⟩ : Fin (0 + t + 1 + 1)) = Fin.castSucc (eGP 0 t ⟨true, b⟩) := fun b =>
    Fin.ext ((ePG_zero_true t b).trans (blockIndex_zero_true_val t b).symm)
  rw [e, e]
  show glEmbMat k _ (m : GL (Fin (0 + t + 1)) k).val _ _ = _
  simp [glEmbMat]

theorem det_pg (t : ℕ) (m : Mir k (0 + t)) (h₂ : m ∈ MirabolicParabolic k 0 t) :
    Matrix.GeneralLinearGroup.det ((gpProj k 0 t ⟨m, h₂⟩).2 : GL (Fin (t + 1)) k) =
      Matrix.GeneralLinearGroup.det (m : GL (Fin (0 + t + 1)) k) := by
  apply Units.ext
  show ((gpProj k 0 t ⟨m, h₂⟩).2 : GL (Fin (t + 1)) k).val.det = (m : GL (Fin (0 + t + 1)) k).val.det
  have e : ∀ b : Fin (t + 1), (eGP 0 t ⟨true, b⟩ : Fin (0 + t + 1)) = Fin.cast (by omega) b := fun b =>
    Fin.ext (blockIndex_zero_true_val t b)
  have h : ((gpProj k 0 t ⟨m, h₂⟩).2 : GL (Fin (t + 1)) k).val =
      (m : GL (Fin (0 + t + 1)) k).val.submatrix (finCongr (by omega : t + 1 = 0 + t + 1)) (finCongr (by omega : t + 1 = 0 + t + 1)) := by
    ext i j
    show (m : GL (Fin (0 + t + 1)) k).val (eGP 0 t ⟨true, i⟩) (eGP 0 t ⟨true, j⟩) = _
    rw [e, e]
    rfl
  rw [h, Matrix.det_submatrix_equiv_self]

theorem cInd_top {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (hH : H = ⊤) (σ : Representation ℂ H W) (hσ : IsSmooth σ) (σ' : Representation ℂ G W)
    (h : ∀ (x : H) (w : W), σ' (x : G) w = σ x w) : Nonempty ((cInd H σ).Equiv σ') := by
  have hm : ∀ g : G, g ∈ H := fun g => hH ▸ Subgroup.mem_top g
  have hval : ∀ (f : cIndSpace H σ) (g : G), f.1.1.1 g = σ' g (f.1.1.1 1) := by
    intro f g
    have := f.1.1.2 ⟨g, hm g⟩ 1
    rw [mul_one] at this
    rw [this, h ⟨g, hm g⟩]
  let ev : cIndSpace H σ →ₗ[ℂ] W :=
    { toFun := fun f => f.1.1.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro f f' e
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rw [hval f, hval f']
    exact congrArg (σ' g) e
  have hsurj : Function.Surjective ev := by
    intro w
    have hO : IsOpen {g : G | σ' g w = w} := by
      have ho := (hσ w).preimage (Continuous.subtype_mk continuous_id hm)
      convert ho using 1
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_preimage, id]
      rw [← h ⟨g, hm g⟩]
    refine ⟨⟨⟨⟨fun g => σ' g w, fun x g => ?_⟩, ?_⟩, ⟨{1}, isCompact_singleton, fun g _ => ⟨g, hm g, 1, rfl, (mul_one g).symm⟩⟩⟩, ?_⟩
    · show σ' ((x : G) * g) w = σ x (σ' g w)
      rw [map_mul, Module.End.mul_apply, h]
    · show IsOpen {x : G | ind H σ x _ = _}
      convert hO using 1
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hx
        have := congrFun (congrArg Subtype.val hx) 1
        simpa using (show σ' (1 * x) w = σ' 1 w from this)
      · intro hx
        apply Subtype.ext
        funext g
        show σ' (g * x) w = σ' g w
        rw [map_mul, Module.End.mul_apply, hx]
    · show σ' 1 w = w
      simp
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩) fun g => LinearMap.ext fun f => ?_⟩
  show f.1.1.1 (1 * g) = σ' g (f.1.1.1 1)
  rw [one_mul, hval f]

theorem exists_finset_adjoin_laurent_preimage {X E : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E] (T : X →ₗ[ℂ] E) (c : ℂ) (hc : c ≠ 0)
    (b : X) (e : E) (h : T b = c • e) : T (c⁻¹ • b) = e := by
  rw [map_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem core0 (ψ : AddChar k Circle) (hψ : Continuous ψ) (N : ℕ) (ρ : Representation ℂ (LH k (N + 1)) E) (hρ : IsSmooth ρ)
    (ρ' : Representation ℂ (Mir k N) E)
    (hρ' : ∀ (m : Mir k N) (x : E), ρ' m x = ((nabs k (Matrix.GeneralLinearGroup.det (m : GL (Fin (N + 1)) k)) : ℝ) : ℂ) • ρ (lv k (N + 1) m) x) :
    Nonempty ((phiMinus k ψ (cInd (LH k (N + 1)) ρ)).Equiv ρ') := by
  have hT := exists_strictHenselian_absolutely_closed_local_ring ψ hψ N ρ
  have hT1 := hT.choose_spec.1
  have hT2 := hT.choose_spec.2.1
  have hT3 := hT.choose_spec.2.2
  have hs := (exists_small ψ hψ N).choose_spec
  have hc := hT3 _ hs
  have hker := ker_eq ψ hψ N ρ hρ hT.choose hT1 hT3
  refine tw_equiv _ _ _ _ (levi_stab ψ N) hT.choose (fun e => ?_) hker ρ' (fun m f => ?_)
  · exact ⟨_, exists_finset_adjoin_laurent_preimage hT.choose hc.choose hc.choose_spec.1 _ e
      (hc.choose_spec.2 _ e (exists_bump ρ hρ (exists_small ψ hψ N).choose e).choose_spec)⟩
  · exact (hT2 (m : GL (Fin (N + 1)) k) m.2 f).trans (hρ' m _).symm

theorem core (ψ : AddChar k Circle) (hψ : Continuous ψ) (N : ℕ) (H : Subgroup (Mir k (N + 1))) (hH : H = LH k (N + 1))
    (ρ : Representation ℂ H E) (hρ : IsSmooth ρ)
    (hlv : ∀ m : Mir k N, levi k (N + 1) (m : GL (Fin (N + 1)) k) ∈ H)
    (ρ' : Representation ℂ (Mir k N) E)
    (hρ' : ∀ (m : Mir k N) (x : E), ρ' m x = ((nabs k (Matrix.GeneralLinearGroup.det (m : GL (Fin (N + 1)) k)) : ℝ) : ℂ) • ρ ⟨_, hlv m⟩ x) :
    Nonempty ((phiMinus k ψ (cInd H ρ)).Equiv ρ') := by
  subst hH
  exact core0 ψ hψ N ρ hρ ρ' hρ'

theorem twist_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ G V) (B : Representation ℂ G W) (χ : G →* ℂˣ) (h : Nonempty (A.Equiv B)) :
    Nonempty ((twist A χ).Equiv (twist B χ)) := by
  obtain ⟨e⟩ := h
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun x => ?_⟩
  show e.toLinearEquiv ((χ g : ℂ) • A g x) = (χ g : ℂ) • B g (e.toLinearEquiv x)
  rw [map_smul]
  congr 1
  exact LinearMap.congr_fun (e.isIntertwining' g) x

theorem equiv_of_lin {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ G V) (B : Representation ℂ G W) (L : V ≃ₗ[ℂ] W) (h : ∀ g x, L (A g x) = B g (L x)) :
    Nonempty (A.Equiv B) :=
  ⟨Representation.Equiv.mk L fun g => LinearMap.ext fun x => h g x⟩

instance subsingleton_Mir0 : Subsingleton (Mir k 0) := by
  refine ⟨fun a b => Subtype.ext (Units.ext ?_)⟩
  ext i j
  have ha := congrFun ((mem_Mir_iff k _).1 a.2) (Fin.last 0)
  have hb := congrFun ((mem_Mir_iff k _).1 b.2) (Fin.last 0)
  have hi : i = Fin.last 0 := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
  have hj : j = Fin.last 0 := Fin.ext (by have := j.2; simp only [Fin.val_last]; omega)
  subst hi hj
  exact (ha.trans hb.symm)

instance subsingleton_GL0 : Subsingleton (GL (Fin 0) k) :=
  ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩

theorem twKer_zero (τ : MRep k 0) : twKer τ.ρ (MirUin k 0) 1 = ⊥ := by
  refine le_bot_iff.1 (Submodule.span_le.2 ?_)
  rintro _ ⟨u, v, rfl⟩
  have : (u : Mir k 0) = 1 := Subsingleton.elim _ _
  simp [this]

def eMk (τ : MRep k 0) : τ.V ≃ₗ[ℂ] (psiN τ).V :=
  (Submodule.quotEquivOfEqBot _ (twKer_zero τ)).symm

theorem eMk_apply (τ : MRep k 0) (x : τ.V) : eMk τ x = Submodule.Quotient.mk x := rfl

theorem smooth_mirabolic_zero {V : Type} [AddCommGroup V] [Module ℂ V] (a : Representation ℂ (Mir k 0) V) : IsSmooth a := by
  intro v
  have : {g : Mir k 0 | a g v = v} = Set.univ := by
    ext g
    simp [Subsingleton.elim g 1]
  rw [this]
  exact isOpen_univ

theorem smooth_GL_zero {V : Type} [AddCommGroup V] [Module ℂ V] (a : Representation ℂ (GL (Fin 0) k) V) : IsSmooth a := by
  intro v
  have : {g : GL (Fin 0) k | a g v = v} = Set.univ := by
    ext g
    simp [Subsingleton.elim g 1]
  rw [this]
  exact isOpen_univ

theorem smc_dpow (n : ℕ) (s : ℝ) : IsSmoothChar (dpow (k := k) n s) := (GlobalTheory.LocGL.isSmoothChar_absPow _).detChar

theorem sm_tw {n : ℕ} {σ : GRep k n} (hσ : IsSmooth σ.ρ) (s : ℝ) : IsSmooth (σ.tw s).ρ :=
  isSmooth_twist hσ (smc_dpow n s)

theorem sm_gres {n : ℕ} {σ : GRep k (n + 1)} (hσ : IsSmooth σ.ρ) : IsSmooth (gres σ).ρ :=
  isSmooth_comp hσ _ continuous_subtype_val

theorem sm_mtw {n : ℕ} {τ : MRep k n} (hτ : IsSmooth τ.ρ) (s : ℝ) : IsSmooth (mtw τ s).ρ :=
  isSmooth_twist hτ ((smc_dpow (n + 1) s).preimage continuous_subtype_val)

section Final
variable {t : ℕ} (τ : MRep k 0) (σ : GRep k (t + 1))

abbrev rho0 : Representation ℂ (HPG k 0 (t + 1)) (τ.V ⊗[ℂ] σ.V) :=
  (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k 0 (t + 1))

abbrev rhoR : Representation ℂ (MirabolicParabolic k 0 t) ((psiN τ).V ⊗[ℂ] σ.V) :=
  (extTensor ((psiN τ).tw (((t + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres σ) (-((0 : ℕ) : ℝ) / 2)).ρ).comp (gpProj k 0 t)

theorem hlv (t : ℕ) (m : Mir k (0 + t)) : levi k (0 + t + 1) (m : GL (Fin (0 + t + 1)) k) ∈ HPG k 0 (t + 1) := by
  have h : HPG k 0 (t + 1) = LH k (0 + t + 1) := HPG_zero (t + 1)
  rw [h]
  exact ⟨_, rfl⟩

def iotaH (t : ℕ) : Mir k (0 + t) →* HPG k 0 (t + 1) :=
  ((levi k (0 + t + 1)).comp (Mir k (0 + t)).subtype).codRestrict _ (hlv t)

def iotaG (t : ℕ) : Mir k (0 + t) →* MirabolicParabolic k 0 t :=
  (MonoidHom.id _).codRestrict _ (fun m => by rw [mirabolicParabolic_zero_left_eq_top]; trivial)

theorem ext_tm {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ G V) (B : Representation ℂ H W) (g : G × H) (a a' : V) (b b' : W) (c : ℂ)
    (ha : A g.1 a = a') (hb : B g.2 b = c • b') : extTensor A B g (a ⊗ₜ[ℂ] b) = c • (a' ⊗ₜ[ℂ] b') := by
  rw [extTensor_tmul, ha, hb, TensorProduct.tmul_smul]

theorem rep_one_apply {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V] (A : Representation ℂ G V) (g : G) (a : V) :
    A g a = a := by
  rw [Subsingleton.elim g 1, map_one, Module.End.one_apply]

theorem rho0_tmul (m : Mir k (0 + t)) (a : τ.V) (b : σ.V) :
    rho0 τ σ (iotaH t m) (a ⊗ₜ[ℂ] b) =
      ((dpow (k := k) (t + 1) (-((0 + 1 : ℕ) : ℝ) / 2) (pgProj k 0 (t + 1) (iotaH t m)).2 : ℂˣ) : ℂ) •
        (a ⊗ₜ[ℂ] σ.ρ (pgProj k 0 (t + 1) (iotaH t m)).2 b) :=
  ext_tm (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).ρ _ a a b _ _ (rep_one_apply _ _ _) rfl

theorem dpowM_zero (n : ℕ) (p : Mir k n) : ((dpowM n (-((0 : ℕ) : ℝ) / 2) p : ℂˣ) : ℂ) = 1 := by
  show ((absPow k (((-((0 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) _ : ℂˣ) : ℂ) = 1
  rw [val_absPow_ofReal]
  simp

theorem rhoR_tmul (m : Mir k (0 + t)) (x : (psiN τ).V) (b : σ.V) :
    rhoR τ σ (iotaG t m) (x ⊗ₜ[ℂ] b) = x ⊗ₜ[ℂ] σ.ρ ((gpProj k 0 t (iotaG t m)).2 : GL (Fin (t + 1)) k) b :=
  (ext_tm ((psiN τ).tw (((t + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres σ) (-((0 : ℕ) : ℝ) / 2)).ρ (gpProj k 0 t (iotaG t m)) x x b
    (σ.ρ ((gpProj k 0 t (iotaG t m)).2 : GL (Fin (t + 1)) k) b) 1 (rep_one_apply _ _ _)
    (congrArg (· • σ.ρ ((gpProj k 0 t (iotaG t m)).2 : GL (Fin (t + 1)) k) b) (dpowM_zero t (gpProj k 0 t (iotaG t m)).2))).trans (one_smul _ _)

theorem scal_one (d : kˣ) :
    ((absPow k (((-1 / 2 : ℝ)) : ℂ) d : ℂˣ) : ℂ) * (((absPow k (((1 : ℝ)) : ℂ) d : ℂˣ) : ℂ) *
      ((absPow k (((-((0 + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) d : ℂˣ) : ℂ)) = 1 := by
  rw [val_absPow_ofReal, val_absPow_ofReal, val_absPow_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have hp := nabs_pos' k d
  rw [← Real.rpow_add hp, ← Real.rpow_add hp]
  norm_num

theorem sm3 {W : Type} [AddCommGroup W] [Module ℂ W] (c₁ c₂ c₃ : ℂ) (h : c₁ * (c₂ * c₃) = 1) (w : W) :
    c₁ • c₂ • c₃ • w = w := by
  rw [smul_smul, smul_smul, ← mul_assoc] at *
  rw [h, one_smul]

theorem match_tmul (m : Mir k (0 + t)) (a : τ.V) (b : σ.V) :
    TensorProduct.congr (eMk τ) (LinearEquiv.refl ℂ σ.V)
      (twist (twist ((rho0 τ σ).comp (iotaH t)) (dpowM (0 + t) 1)) (dpowM (0 + t) (-1 / 2)) m (a ⊗ₜ[ℂ] b)) =
    ((rhoR τ σ).comp (iotaG t)) m (TensorProduct.congr (eMk τ) (LinearEquiv.refl ℂ σ.V) (a ⊗ₜ[ℂ] b)) := by
  have hq : (pgProj k 0 (t + 1) (iotaH t m)).2 = ((gpProj k 0 t (iotaG t m)).2 : GL (Fin (t + 1)) k) :=
    pg_gp t m (hlv t m) (iotaG t m).2
  have hd : Matrix.GeneralLinearGroup.det (pgProj k 0 (t + 1) (iotaH t m)).2 =
      Matrix.GeneralLinearGroup.det (m : GL (Fin (0 + t + 1)) k) := by
    rw [hq]
    exact det_pg t m (iotaG t m).2
  have hs := scal_one (Matrix.GeneralLinearGroup.det (m : GL (Fin (0 + t + 1)) k))
  rw [twist_apply, twist_apply]
  show TensorProduct.congr (eMk τ) (LinearEquiv.refl ℂ σ.V) (_ • _ • rho0 τ σ (iotaH t m) (a ⊗ₜ[ℂ] b)) =
    rhoR τ σ (iotaG t m) (eMk τ a ⊗ₜ[ℂ] b)
  have h3 : ((dpow (k := k) (t + 1) (-((0 + 1 : ℕ) : ℝ) / 2) (pgProj k 0 (t + 1) (iotaH t m)).2 : ℂˣ) : ℂ) =
      ((absPow k (((-((0 + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (Matrix.GeneralLinearGroup.det (m : GL (Fin (0 + t + 1)) k)) : ℂˣ) : ℂ) :=
    congrArg (fun d : kˣ => ((absPow k (((-((0 + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) d : ℂˣ) : ℂ)) hd
  rw [rho0_tmul, rhoR_tmul, h3, hq, map_smul, map_smul, map_smul, TensorProduct.congr_tmul]
  exact sm3 _ _ _ hs _

theorem final_match (m : Mir k (0 + t)) (x : τ.V ⊗[ℂ] σ.V) :
    TensorProduct.congr (eMk τ) (LinearEquiv.refl ℂ σ.V)
      (twist (twist ((rho0 τ σ).comp (iotaH t)) (dpowM (0 + t) 1)) (dpowM (0 + t) (-1 / 2)) m x) =
    ((rhoR τ σ).comp (iotaG t)) m (TensorProduct.congr (eMk τ) (LinearEquiv.refl ℂ σ.V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    exact match_tmul τ σ m a b

theorem smooth_rho0 (hσ : IsSmooth σ.ρ) : IsSmooth (rho0 τ σ) := smooth_pg 0 (t + 1) _ _ (smooth_mirabolic_zero _) (sm_tw hσ _)

theorem sm_rhoR (hσ : IsSmooth σ.ρ) : IsSmooth (rhoR τ σ) := smooth_gp 0 t _ _ (smooth_GL_zero _) (sm_mtw (sm_gres hσ) _)

theorem dpowM_one (n : ℕ) (m : Mir k n) :
    ((dpowM n 1 m : ℂˣ) : ℂ) = ((nabs k (Matrix.GeneralLinearGroup.det (m : GL (Fin (n + 1)) k)) : ℝ) : ℂ) := by
  show ((absPow k ((1 : ℝ) : ℂ) (Matrix.GeneralLinearGroup.det (m : GL (Fin (n + 1)) k)) : ℂˣ) : ℂ) = _
  rw [val_absPow_ofReal, Real.rpow_one]

theorem phi_of_induced_rank_zero_equiv (ψ : AddChar k Circle) (hψ : Continuous ψ) (hσ : IsSmooth σ.ρ) :
    Nonempty ((phiMinus k ψ (cInd (HPG k 0 (t + 1)) (rho0 τ σ) : Representation ℂ (Mir k (0 + t + 1)) _)).Equiv
      (twist ((rho0 τ σ).comp (iotaH t)) (dpowM (0 + t) 1))) :=
  core ψ hψ (0 + t) (HPG k 0 (t + 1)) (HPG_zero (t + 1)) (rho0 τ σ) (smooth_rho0 τ σ hσ) (hlv t) _
    (fun m x => congrArg (fun c : ℂ => c • (rho0 τ σ ⟨_, hlv t m⟩ x)) (dpowM_one (0 + t) m))

theorem comb_lem (ψ : AddChar k Circle) (hψ : Continuous ψ) (hσ : IsSmooth σ.ρ) :
    Nonempty ((twist (phiMinus k ψ (cInd (HPG k 0 (t + 1)) (rho0 τ σ) : Representation ℂ (Mir k (0 + t + 1)) _)) (dpowM (0 + t) (-1 / 2))).Equiv
      (cInd (MirabolicParabolic k 0 t) (rhoR τ σ))) :=
  ⟨((twist_equiv _ _ (dpowM (0 + t) (-1 / 2)) (phi_of_induced_rank_zero_equiv τ σ ψ hψ hσ)).some.trans
      (equiv_of_lin _ _ _ (final_match τ σ)).some).trans
    (cInd_top (MirabolicParabolic k 0 t) (mirabolicParabolic_zero_left_eq_top t) (rhoR τ σ) (sm_rhoR τ σ hσ) ((rhoR τ σ).comp (iotaG t)) (fun x w => rfl)).some.symm⟩

theorem miso_of (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (Mir k (n + 1)) V) (B : MRep k n)
    (h : Nonempty ((twist (phiMinus k ψ π) (dpowM n (-1 / 2))).Equiv B.ρ)) : MIso (phiN ψ (⟨V, π⟩ : MRep k (n + 1))) B := h

theorem aux0 (ψ : AddChar k Circle) (hψ : Continuous ψ) (hσ : IsSmooth σ.ρ) :
    MIso (phiN (n := 0 + t) ψ (⟨_, cInd (HPG k 0 (t + 1)) (rho0 τ σ)⟩ : MRep k (0 + t + 1))) (prodGPn (psiN τ) (gres σ)) :=
  miso_of ψ _ _ (comb_lem τ σ ψ hψ hσ)

theorem mcast_self {a : ℕ} (h : a = a) (X : MRep k a) : mcast h X = X := rfl

theorem phiPG_zero (ψ : AddChar k Circle) (hψ : Continuous ψ) (hσ : IsSmooth σ.ρ) {n : ℕ} (hc : 0 + (t + 1) = n + 1) (hd : 0 + t = n) :
    MIso (phiN ψ (mcast hc (prodPGn τ σ))) (mcast hd (prodGPn (psiN τ) (gres σ))) := by
  subst hd
  exact aux0 τ σ ψ hψ hσ

end Final

open GlobalTheory.RgGu.Leib in

theorem phiPG0_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG0 k := by
  intro k _ _ _ _ ψ hψ _ t τ σ hσ
  exact phiPG_zero τ σ ψ hψ hσ _ rfl

end GlobalTheory.CompanionTheory.MirLevi
