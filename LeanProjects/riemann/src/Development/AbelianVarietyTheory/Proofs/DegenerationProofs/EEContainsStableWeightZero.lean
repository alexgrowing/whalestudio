import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AddHomExtSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSpanRowsIffCoordsMem
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisTestLattice

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.LatticeStable

open FreeNear TestBasis

theorem quadratic_nonneg {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) : 0 ≤ q a := by
  obtain ⟨b, hb⟩ := hq.exists_forall_le
  have h0 : q b ≤ 0 := by simpa using hb 0
  have h2 := hb ((2 : ℤ) • b)
  rw [QuadraticMap.map_smul] at h2
  simp only [zsmul_eq_mul] at h2
  push_cast at h2
  have := hb a
  linarith

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem operator_comm_proj (H : AddSubgroup S.Gam) {h : S.Gam} (hh : h ∈ H) (c : S.perp H →+ ZMod S.N) :
    S.ρ h * S.proj (S.perp H) c = S.proj (S.perp H) c * S.ρ h := by
  have := Fintype.ofFinite (S.perp H)
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : eStd S.g _ (t : S.Gam) h = 0 := t.2 h hh
  rw [mul_smul_comm, smul_mul_assoc, S.ρ_add _ _ (by rw [Weights.eStd_swap, h1, neg_zero, smul_zero]),
    S.ρ_add _ _ (by rw [h1, smul_zero]), add_comm]

variable {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)

theorem single_mem_testLattice [hA : ArithBase o Ω] (i : S.J) : Pi.single i (1 : PadicAlgCl p) ∈ τ.E := by
  have : IsDomain o := hA.inj.isDomain
  have := finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨-, hsum⟩ := proj_orthogonal S _ τ.isoFree
  have h1 : Pi.single i (1 : PadicAlgCl p) = ∑ c : S.perp τ.yy.ker →+ ZMod S.N,
      fun j => 1 * y₀ (algebraMap o S.R (S.proj _ c j i)) := by
    funext j
    rw [Finset.sum_apply]
    simp only [_root_.one_mul]
    rw [← map_sum, ← map_sum, ← Matrix.sum_apply, hsum, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [h1]
  refine Submodule.sum_mem _ fun c _ => Submodule.subset_span ?_
  obtain ⟨α, hα, rfl⟩ := (test_weights o Ω S p y₀ τ).1 c
  refine ⟨α, 1, i, hα, ?_, rfl⟩
  rw [norm_one]
  exact Real.one_le_exp (div_nonneg (quadratic_nonneg τ.q τ.pos α) (Nat.cast_nonneg _))

theorem operator_mem_testLattice (hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) {h : S.Gam} (hh : h ∈ τ.yy.ker)
    {w : S.J → PadicAlgCl p} (hw : w ∈ τ.E) :
    (fun j => ∑ k, y₀ (algebraMap o S.R (S.ρ h j k)) * w k) ∈ τ.E := by
  induction hw using Submodule.span_induction with
  | mem _ h' =>
    obtain ⟨α, l, i, hα, hl, rfl⟩ := h'
    have h1 : (fun j => ∑ k, y₀ (algebraMap o S.R (S.ρ h j k)) *
        (l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) k i)))) =
        ∑ k, (⟨_, (mem_OO_iff _).2 (hint (S.ρ h k i))⟩ : OO p) •
          fun j => l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j k)) := by
      funext j
      have h2 := congrArg (fun a => l * y₀ (algebraMap o S.R a))
        (congrFun (congrFun (operator_comm_proj _ hh (τ.wt α)) j) i)
      simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum] at h2
      rw [Finset.sum_apply]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (h2.trans (Finset.sum_congr rfl fun k _ => ?_))
      · ring
      · change _ = y₀ (algebraMap o S.R (S.ρ h k i)) * (l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j k)))
        ring
    rw [h1]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, l, k, hα, hl, rfl⟩)
  | zero =>
    convert Submodule.zero_mem τ.E using 1
    funext j
    simp
  | add a a' _ _ ha ha' =>
    convert Submodule.add_mem _ ha ha' using 1
    funext j
    simp [mul_add, Finset.sum_add_distrib]
  | smul s a _ ha =>
    convert Submodule.smul_mem _ s ha using 1
    funext j
    change ∑ k, _ * ((s : PadicAlgCl p) * a k) = (s : PadicAlgCl p) * ∑ k, _ * a k
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem weightZero_mem [hA : ArithBase o Ω] (hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1)
    {w : S.J → PadicAlgCl p} (hw : w ∈ τ.E) (j : S.J) :
    ∑ k, w k * y₀ (algebraMap o S.R (S.proj (S.perp τ.yy.ker) 0 j k)) ∈ OO p := by
  have : IsDomain o := hA.inj.isDomain
  have := finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, -⟩ := proj_orthogonal S _ τ.isoFree
  refine sum_mul_mem_of_mem_span (OO p) _ ?_ hw
  rintro _ ⟨α, l, i, hα, hl, rfl⟩
  have h2 := congrArg (fun a => l * y₀ (algebraMap o S.R a)) (congrFun (congrFun (hmul 0 (τ.wt α)) j) i)
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum] at h2
  rw [(Finset.sum_congr rfl fun k _ => by ring).trans h2]
  split_ifs with h0
  · have h3 := q_le_of_wt_eq τ (β := 0) hα (by rw [map_zero, h0])
    rw [map_zero] at h3
    refine mul_mem ((mem_OO_iff _).2 (hl.trans ?_)) ((mem_OO_iff _).2 (hint _))
    exact Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg h3 (Nat.cast_nonneg _))
  · simp

variable {M : RatModel o Ω} {U₀ : M.Z.Opens}

theorem exists_opens_regular (hne : (U₀ : Set M.Z).Nonempty) {J : Type} [Finite J] (v : J → Ω) :
    ∃ U₁ : M.Z.Opens, U₁ ≤ U₀ ∧ (U₁ : Set M.Z).Nonempty ∧ ∀ j, v j ∈ M.ringOn U₁ := by
  let W : M.Z.Opens := ⟨⋂ j, {z | v j ∈ M.O z}, isOpen_iInter_of_finite fun j => M.isOpen_setOf_mem_O _⟩
  refine ⟨U₀ ⊓ W, inf_le_left, M.nonempty_inf hne ⟨genericPoint M.Z, Set.mem_iInter.2 fun j => ?_⟩,
    fun j => RatModel.mem_ringOn.2 fun z hz => Set.mem_iInter.1 hz.2 j⟩
  rw [Set.mem_setOf_eq, M.O_genericPoint]
  exact Algebra.mem_top

theorem over_mono (hO : S.Over₀ M U₀) {U₁ : M.Z.Opens} (hle : U₁ ≤ U₀) (hne : (U₁ : Set M.Z).Nonempty) :
    S.Over₀ M U₁ :=
  ⟨hO.normal, hO.proj, hO.div, hne, hO.le.trans (RatModel.ringOn_anti hle),
    fun x hx => RatModel.ringOn_anti hle (hO.th_unit x hx),
    fun T c k hT hk => RatModel.ringOn_anti hle (hO.FF_unit T c k hT hk)⟩

theorem val_mulVec {U₁ : Set M.Z} {z : M.Z} {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₁ z y) (hat : S.At M y y₀)
    (A : Matrix S.J S.J o) {v : S.J → Ω} (hv : ∀ j, v j ∈ M.ringOn U₁) (j : S.J) :
    M.val (gPt p ≫ y) ((A.map (algebraMap o Ω)).mulVec v j) =
      ∑ k, M.val (gPt p ≫ y) (v k) * y₀ (algebraMap o S.R (A j k)) := by
  obtain ⟨ξ, hξU, hsp⟩ : ∃ ξ ∈ U₁, ∀ w, (gPt p ≫ y) w ⤳ ξ :=
    ⟨(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)), hc.2 ⟨_, rfl⟩,
      RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)⟩
  rw [← Matrix.vecMul_transpose, RatModel.val_vecMul_eq_sum (c := (A.map (algebraMap o Ω)).transpose) hsp
    (fun j => RatModel.mem_ringOn.1 (hv j) _ hξU) (fun _ _ => Subalgebra.algebraMap_mem _ _)]
  exact Finset.sum_congr rfl fun k _ => by rw [hat]; rfl

theorem norm_base_le_one {U₁ : Set M.Z} {z : M.Z} {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₁ z y) (hat : S.At M y y₀)
    (a : o) : ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := by
  rw [hat]
  exact hc.norm_val_le_one (Subalgebra.algebraMap_mem _ a)

end GlobalTheory.ZH.LatticeStable

namespace GlobalTheory.ZH

open LatticeStable in

theorem EE_contains_stable_weightZero :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → S.IsEE M U₀ EE → ∀ ξ : M.Z, (∀ i, Pi.single i (1 : Ω) ∈ EE.E ξ) ∧ (∀ h ∈ S.HH M ξ, ∀ v ∈ EE.E ξ, ((S.ρ h).map (algebraMap o Ω)).mulVec v ∈ EE.E ξ) ∧ (IsClosed ({ξ} : Set M.Z) → ∀ v ∈ EE.E ξ, ((S.proj (S.TT M ξ) 0).map (algebraMap o Ω)).mulVec v = v → ∀ j, v j ∈ M.O ξ) := by
  intro o Ω _ _ _ _ S M U₀ EE hO hloc htest hsup hT hEE
  have hmem : ∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → _ := fun U₁ hle hne =>
    mem_EE_iff_forall_test o Ω S M U₁ EE (over_mono hO hle hne)
      ⟨fun U hU => hloc.1 U (hU.trans hle), hloc.2⟩
      (fun z p _ y hc => htest z p y ⟨hc.1, hc.2.trans hle⟩)
      ⟨fun z hz => hEE.1 z (hle hz), fun z p _ y y₀ τ hc => hEE.2 z p y y₀ τ ⟨hc.1, hc.2.trans hle⟩⟩
  have h1 : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ i, Pi.single i (1 : Ω) ∈ EE.E z := by
    intro z hz i
    refine (hmem U₀ le_rfl hO.ne z hz _ fun j => ?_).2 fun p _ y y₀ τ hc hat => ?_
    · rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · convert single_mem_testLattice τ i using 1
      funext j
      simp only [Pi.single_apply]
      split_ifs
      exacts [RatModel.val_one _, RatModel.val_zero _]
  have h2 : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ h ∈ S.HH M z, ∀ v ∈ EE.E z,
      ((S.ρ h).map (algebraMap o Ω)).mulVec v ∈ EE.E z := by
    intro z hz h hh v hv
    obtain ⟨U₁, hle, hne, hreg⟩ := exists_opens_regular hO.ne v
    refine (hmem U₁ hle hne z hz _ fun j => ?_).2 fun p _ y y₀ τ hc hat => ?_
    · exact sum_mem fun k _ => mul_mem (Subalgebra.algebraMap_mem _ _) (hreg k)
    · have h3 := (hmem U₁ hle hne z hz v hreg).1 hv p y y₀ τ hc hat
      rw [(hsup z p y y₀ τ ⟨hc.1, hc.2.trans hle⟩ hat).2] at hh
      convert operator_mem_testLattice τ (norm_base_le_one hc hat) hh h3 using 1
      funext j
      rw [val_mulVec hc hat _ hreg]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  intro ξ
  obtain ⟨W, b, hξ, -, hE⟩ := EE.loc ξ
  obtain ⟨x, hxW, hx, hsp, hI⟩ := hT.2.2.2 ξ W hξ
  have hle : ∀ v ∈ EE.E x, v ∈ EE.E ξ := fun v hv => by
    rw [hE x hxW] at hv
    rw [hE ξ hξ]
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (v := fun i => b i) _).1 hv
    exact (Submodule.mem_span_range_iff_exists_fun (v := fun i => b i) _).2
      ⟨fun i => ⟨c i, RatModel.O_le_of_specializes hsp (c i).2⟩, rfl⟩
  refine ⟨fun i => hle _ (h1 x hx i), fun h hh v hv => ?_, fun hz v hv hP j => ?_⟩
  · have hh' : h ∈ S.HH M x := by rwa [ThetaSys.HH, hI]
    rw [hE ξ hξ] at hv
    induction hv using Submodule.span_induction with
    | mem w hw => exact hle _ (h2 x hx h hh' w (by rw [hE x hxW]; exact Submodule.subset_span hw))
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add a a' _ _ ha ha' => rw [Matrix.mulVec_add]; exact add_mem ha ha'
    | smul s a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ s ha
  · obtain ⟨U₁, hle₁, hne, hreg⟩ := exists_opens_regular hO.ne v
    refine (hloc.1 U₁ hle₁ hne ξ hz).2 _ (hreg j) fun p _ y hc => ?_
    have hc₀ : M.Cen U₀ ξ y := ⟨hc.1, hc.2.trans hle₁⟩
    obtain ⟨y₀, hat, hint, ⟨τ⟩⟩ := htest ξ p y hc₀
    have h3 := (hmem U₁ hle₁ hne ξ hz v hreg).1 hv p y y₀ τ hc hat
    rw [ThetaSys.TT, (hsup ξ p y y₀ τ hc₀ hat).2] at hP
    rw [← hP, val_mulVec hc hat _ hreg, ← mem_OO_iff]
    exact weightZero_mem τ hint h3 j

end GlobalTheory.ZH
