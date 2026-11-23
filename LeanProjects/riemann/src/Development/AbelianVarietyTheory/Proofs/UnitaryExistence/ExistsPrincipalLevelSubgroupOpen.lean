import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous

noncomputable section

namespace GlobalTheory.Member.PrincLevel

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem smul_mem_hat (L : Set (Fin n → E)) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {z : Fin n → GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat F L) : a • z ∈ GlobalTheory.AdLat.hat F L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, x, hx, ?_⟩
    · exact mul_mem (ha v) (hb v)
    · funext i
      simp only [Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

def congSub {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (H : AddSubgroup (Fin n → R)) (N : ℕ) :
    AddSubgroup (Fin n → R) where
  carrier := {z | ∃ y ∈ H, M *ᵥ z - z = N • y}
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    refine ⟨x + y, add_mem hx hy, ?_⟩
    rw [Matrix.mulVec_add, smul_add, ← ha, ← hb]; abel
  neg_mem' := by
    rintro a ⟨x, hx, ha⟩
    refine ⟨-x, neg_mem hx, ?_⟩
    rw [Matrix.mulVec_neg, smul_neg, ← ha]; abel

theorem cong_of_gen (L : Set (Fin n → E)) (S : Set (Fin n → E)) (hS : L ⊆ AddSubgroup.closure S)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (N : ℕ)
    (h : ∀ x ∈ S, ∃ y ∈ GlobalTheory.AdLat.hat F L, M *ᵥ GlobalTheory.AdLat.fv F x - GlobalTheory.AdLat.fv F x = N • y) :
    ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L, M *ᵥ z - z = N • y := by
  have h1 : ∀ x ∈ AddSubgroup.closure S, GlobalTheory.AdLat.fv F x ∈ congSub M (GlobalTheory.AdLat.hat F L) N := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem z hz => exact h z hz
    | zero =>
      have : GlobalTheory.AdLat.fv F (0 : Fin n → E) = 0 := by funext i; simp [GlobalTheory.AdLat.fv]
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : GlobalTheory.AdLat.fv F (x + y) = GlobalTheory.AdLat.fv F x + GlobalTheory.AdLat.fv F y := by
        funext i; simp [GlobalTheory.AdLat.fv, TensorProduct.tmul_add]
      rw [this]; exact add_mem hx hy
    | neg x _ hx =>
      have : GlobalTheory.AdLat.fv F (-x) = -GlobalTheory.AdLat.fv F x := by
        funext i; simp [GlobalTheory.AdLat.fv, TensorProduct.tmul_neg]
      rw [this]; exact neg_mem hx
  have h2 : GlobalTheory.AdLat.hat F L ≤ congSub M (GlobalTheory.AdLat.hat F L) N := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨y, hy, e⟩ := h1 x (hS hx)
    have hz : (fun i => a ⊗ₜ[F] x i : Fin n → GlobalTheory.AdLat.RA F E) = a • GlobalTheory.AdLat.fv F x := by
      funext i
      simp only [GlobalTheory.AdLat.fv, Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    refine ⟨a • y, smul_mem_hat L a ha hy, ?_⟩
    rw [hz, Matrix.mulVec_smul, ← smul_sub, e, smul_comm]
  exact fun z hz => h2 hz

theorem continuous_mulVec_sub {X R : Type} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {f : X → Matrix (Fin n) (Fin n) R} (hf : Continuous f) (v : Fin n → R) :
    Continuous fun k => f k *ᵥ v - v :=
  (hf.matrix_mulVec continuous_const).sub continuous_const

end General

variable {D : D7}

theorem finCong_map {V : HSp D} {N : ℕ} {k : GA D V} (hk : FinCong V N k) :
    ∀ z ∈ latHat V, (finHom V k).1 *ᵥ z ∈ latHat V := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  rw [sub_eq_iff_eq_add] at e
  rw [e]
  exact add_mem (nsmul_mem hy N) hz

theorem finCong_one (V : HSp D) (N : ℕ) : FinCong V N 1 := by
  intro z _
  exact ⟨0, zero_mem _, by simp⟩

theorem finCong_mul {V : HSp D} {N : ℕ} {a b : GA D V} (ha : FinCong V N a) (hb : FinCong V N b) :
    FinCong V N (a * b) := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hb z hz
  obtain ⟨x, hx, e'⟩ := ha _ (finCong_map hb z hz)
  refine ⟨x + y, add_mem hx hy, ?_⟩
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, nsmul_add, ← e, ← e']
  abel

theorem finCong_inv {V : HSp D} {N : ℕ} {a : GA D V} (ha : FinCong V N a) : FinCong V N a⁻¹ := by
  obtain ⟨h1, -, h3, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hinv : ∀ z ∈ latHat V, (finHom V a⁻¹).1 *ᵥ z ∈ latHat V := by
    have hm := finCong_map ha
    rw [h1] at hm ⊢
    rw [map_inv]
    exact GlobalTheory.AdLat.inv_mulVec_mem_hat D.host.F D.host.E V.rank (latC V) (finHom V a) (cF D) h3 h4 hm
      (GlobalTheory.Member.finHom_herm_det D V a).2.1
  intro z hz
  obtain ⟨y, hy, e⟩ := ha _ (hinv z hz)
  refine ⟨-y, neg_mem hy, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at e
  rw [neg_nsmul, ← e, neg_sub]

def levelGroup (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | k ∈ GfC V ∧ FinCong V N k}
  one_mem' := ⟨one_mem _, finCong_one V N⟩
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, finCong_mul ha.2 hb.2⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, finCong_inv ha.2⟩

theorem finCong_mem_nhds (V : HSp D) {N : ℕ} (hN : 0 < N) :
    {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V) := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨hop, hc, -⟩ := GlobalTheory.Member.latHat_open_and_continuous D V
  have : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨S, hS⟩ := h3.restrictScalars (R := ℤ)
  have hLS : (latC V : Set (Fin V.rank → D.host.E)) ⊆
      (AddSubgroup.closure (S : Set (Fin V.rank → D.host.E)) : AddSubgroup (Fin V.rank → D.host.E)) := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (S : Set (Fin V.rank → D.host.E)) := by rw [hS]; exact hx
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    exact hx'
  have hU : (⋂ x ∈ S, {k : GA D V | ∃ y ∈ latHat V,
      (finHom V k).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x - GlobalTheory.AdLat.fv D.host.F x = N • y}) ∈ 𝓝 (1 : GA D V) := by
    refine (Filter.biInter_finset_mem S).2 fun x _ => ?_
    have hcx : Continuous fun k : GA D V =>
        (finHom V k).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x - GlobalTheory.AdLat.fv D.host.F x :=
      continuous_mulVec_sub hc _
    refine ((hop N hN).preimage hcx).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hU fun k hk => ?_
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hk
  unfold FinCong
  rw [Set.mem_ofPred_eq]
  rw [h1] at hk ⊢
  exact cong_of_gen _ _ hLS _ N fun x hx => hk x hx

theorem exists_levelK_and_nhds : ∀ (D : D7) (V : HSp D), ∀ N : ℕ,
    (∃ Kf : Subgroup (GA D V), IsLevelK V N Kf) ∧
      (0 < N → {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V)) :=
  fun _ V N => ⟨⟨levelGroup V N, fun _ => Iff.rfl⟩, fun hN => finCong_mem_nhds V hN⟩

end GlobalTheory.Member.PrincLevel
