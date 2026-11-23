import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabOfDefinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSupersetStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

namespace GlobalTheory.DefSkewStab

open GlobalTheory.DefiniteStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isOpen_stab_of_theta_one {B : Base F E} {n : ℕ} {X : Spc F E n} (hlat : X.L.IsLattice E)
    (hθ : ∀ w, X.θ w = 1) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) : IsOpen (K : Set (UA σ X.J)) := by
  obtain ⟨c, hc0, hc⟩ := exists_transfer hlat
  obtain ⟨t, ht0, ht⟩ := exists_int_scale (F := F) (E := E)
  let V : Set (AE F E) := {u | ∀ k, (basA F E).repr (inclR (F := F) (AF F) (t * c)⁻¹ * u) k ∈ intFin F}
  have hVo : IsOpen V := by
    have hcont : Continuous fun u : AE F E => (basA F E).equivFun (inclR (F := F) (AF F) (t * c)⁻¹ * u) :=
      (IsModuleTopology.continuous_of_linearMap (basA F E).equivFun.toLinearMap).comp
        (continuous_const.mul continuous_id)
    have e : V = ⋂ k, (fun u => (basA F E).equivFun (inclR (F := F) (AF F) (t * c)⁻¹ * u) k) ⁻¹' intFin F := by
      ext u; simp [V, Module.Basis.equivFun_apply]
    rw [e]
    exact isOpen_iInter_of_finite fun k => isOpen_intFin.preimage ((continuous_apply k).comp hcont)
  have hV0 : (0 : AE F E) ∈ V := fun k => by
    rw [mul_zero, map_zero, Finsupp.zero_apply]; exact zero_mem_intFin
  have hmat : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  let W : Set (UA σ X.J) := {g | ∀ i j, (mat g - 1) i j ∈ V ∧ (mat g⁻¹ - 1) i j ∈ V}
  have hWo : IsOpen W := by
    have h1 : ∀ i j, Continuous fun g : UA σ X.J => (mat g - 1) i j :=
      fun i j => (hmat.sub continuous_const).matrix_elem i j
    have h2 : ∀ i j, Continuous fun g : UA σ X.J => (mat g⁻¹ - 1) i j :=
      fun i j => ((hmat.comp continuous_inv).sub continuous_const).matrix_elem i j
    simp only [W, Set.setOf_forall, Set.setOf_and]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (hVo.preimage (h1 i j)).inter (hVo.preimage (h2 i j))
  have hW1 : (1 : UA σ X.J) ∈ W := by
    have e : mat (1 : UA σ X.J) = 1 := rfl
    intro i j
    rw [inv_one, e, sub_self]
    exact ⟨hV0, hV0⟩
  have key : ∀ N : Matrix (Fin n) (Fin n) (AE F E), (∀ i j, (N - 1) i j ∈ V) → ∀ z ∈ latHat X, N *ᵥ z ∈ latHat X := by
    intro N hN z hz
    have e : N *ᵥ z = z + (N - 1) *ᵥ z := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e]
    exact add_mem hz (mulVec_mem hc0 ht0 hc ht (fun i j => hN i j) hz)
  refine Subgroup.isOpen_of_mem_nhds K (g := 1) (Filter.mem_of_superset (hWo.mem_nhds hW1) fun g hg => ?_)
  rw [SetLike.mem_coe, hK]
  refine ⟨fun w => ?_, fun z hz => ⟨key _ (fun i j => (hg i j).1) z hz, key _ (fun i j => (hg i j).2) z hz⟩⟩
  rw [hθ w]
  exact Commute.one_right _

theorem mem_latHat_sum {n : ℕ} {W : Spc F E n} {W₂ : Spc F E (n + n)} (hL : W₂.L = sumLat finSumFinEquiv W.L W.L)
    {u v : Fin n → AE F E} : pairVec finSumFinEquiv u v ∈ latHat W₂ ↔ u ∈ latHat W ∧ v ∈ latHat W := by
  constructor
  · intro h
    have key : ∀ z ∈ latHat W₂, (fun i => z (finSumFinEquiv (.inl i))) ∈ latHat W ∧
        (fun i => z (finSumFinEquiv (.inr i))) ∈ latHat W := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨b, hb0, hb, x, hx, rfl⟩ := hz
        rw [hL, mem_sumLat] at hx
        exact ⟨gen_mem W hb0 hb hx.1, gen_mem W hb0 hb hx.2⟩
      | zero => exact ⟨zero_mem _, zero_mem _⟩
      | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
      | neg x _ hx => exact ⟨neg_mem hx.1, neg_mem hx.2⟩
    simpa only [pairVec_inl, pairVec_inr] using key _ h
  · rintro ⟨hu, hv⟩
    have hadd : ∀ a b c d : Fin n → AE F E, pairVec finSumFinEquiv (a + b) (c + d) =
        pairVec finSumFinEquiv a c + pairVec finSumFinEquiv b d := by
      intro a b c d
      funext j; obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp only [pairVec_inl, pairVec_inr, Pi.add_apply]
    have hneg : ∀ a c : Fin n → AE F E, pairVec finSumFinEquiv (-a) (-c) = -pairVec finSumFinEquiv a c := by
      intro a c
      funext j; obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp only [pairVec_inl, pairVec_inr, Pi.neg_apply]
    have hzero : pairVec finSumFinEquiv (0 : Fin n → AE F E) (0 : Fin n → AE F E) = 0 := by
      funext j; obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp only [pairVec_inl, pairVec_inr, Pi.zero_apply]
    have hgen : ∀ (b : AF F) (x y : Fin n → E), pairVec finSumFinEquiv (b • incV F x) (b • incV F y) =
        b • incV F (pairVec finSumFinEquiv x y) := by
      intro b x y
      funext j; obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp only [pairVec_inl, pairVec_inr, Pi.smul_apply, incV]
    have h1 : pairVec finSumFinEquiv u 0 ∈ latHat W₂ := by
      induction hu using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨b, hb0, hb, x, hx, rfl⟩ := hz
        have := hgen b x 0
        rw [GlobalTheory.LatHatClosed.incV_zero, smul_zero] at this
        rw [this]
        exact gen_mem W₂ hb0 hb (by rw [hL, pairVec_mem_sumLat]; exact ⟨hx, zero_mem _⟩)
      | zero => rw [hzero]; exact zero_mem _
      | add x y _ _ hx hy => rw [← add_zero (0 : Fin n → AE F E), hadd]; exact add_mem hx hy
      | neg x _ hx => rw [← neg_zero, hneg]; exact neg_mem hx
    have h2 : pairVec finSumFinEquiv 0 v ∈ latHat W₂ := by
      induction hv using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨b, hb0, hb, x, hx, rfl⟩ := hz
        have := hgen b 0 x
        rw [GlobalTheory.LatHatClosed.incV_zero, smul_zero] at this
        rw [this]
        exact gen_mem W₂ hb0 hb (by rw [hL, pairVec_mem_sumLat]; exact ⟨zero_mem _, hx⟩)
      | zero => rw [hzero]; exact zero_mem _
      | add x y _ _ hx hy => rw [← add_zero (0 : Fin n → AE F E), hadd]; exact add_mem hx hy
      | neg x _ hx => rw [← neg_zero, hneg]; exact neg_mem hx
    have := add_mem h1 h2
    rwa [← hadd, add_zero, zero_add] at this

theorem blkMat_mulVec_mem {n : ℕ} {W : Spc F E n} {W₂ : Spc F E (n + n)} (hL : W₂.L = sumLat finSumFinEquiv W.L W.L)
    {A : Matrix (Fin n) (Fin n) (AE F E)} (hA : ∀ z ∈ latHat W, A *ᵥ z ∈ latHat W) {z : Fin (n + n) → AE F E}
    (hz : z ∈ latHat W₂) : blkMat finSumFinEquiv A 1 *ᵥ z ∈ latHat W₂ := by
  rw [← pairVec_eta finSumFinEquiv z] at hz ⊢
  rw [mem_latHat_sum hL] at hz
  rw [blkMat_mulVec, mem_latHat_sum hL, Matrix.one_mulVec]
  exact ⟨hA _ hz.1, hz.2⟩

theorem exists_open_compact : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (W : Spc F E n), B.IsGood σ → W.IsSkew σ B n 0 →
    ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ K₂ : Subgroup (UA σ W₂.J), IsStab B K₂ →
    ∃ K : Subgroup (UA σ W.J), IsOpen (K : Set (UA σ W.J)) ∧ IsCompact (K : Set (UA σ W.J)) ∧ ∀ k ∈ K, i (k, 1) ∈ K₂ := by
  intro _ F E _ _ _ _ _ σ B n W hB hW W₂ _ hL hθ₂ i hi K₂ hK₂
  have hθ : ∀ w, W.θ w = 1 := fun w => GlobalTheory.DefiniteCartan.eq_one_of_hasSig (hW.sig w) (hW.cartan w)
  have hK := GlobalTheory.StabHaar.isStab_stabK (σ := σ) B W
  refine ⟨GlobalTheory.StabHaar.stabK B W, isOpen_stab_of_theta_one hW.lat hθ hK, ?_, fun k hk => ?_⟩
  · obtain ⟨C, hC, hsub⟩ := GlobalTheory.StabBoundedSkew.exists_compact_superset_stab F E σ B n W n 0 hB hW _ hK
    exact hC.of_isClosed_subset
      (GlobalTheory.StabHaar.isClosed_stabK B W (GlobalTheory.LatHatClosed.isClosed_latHat F E n W hW.lat)) hsub
  · have hk' := (hK k).1 hk
    have e1 : mat (i (k, 1)) = blkMat finSumFinEquiv (mat k) 1 := hi k 1
    have e2 : mat (i (k, 1))⁻¹ = blkMat finSumFinEquiv (mat k⁻¹) 1 := by
      rw [← map_inv, Prod.inv_mk, inv_one]; exact hi k⁻¹ 1
    refine (hK₂ _).2 ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [e1, hθ₂, hθ, blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
      show _ * _ = _ * _
      rw [blkMat_mul, blkMat_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    · rw [e1, e2]
      exact ⟨blkMat_mulVec_mem hL (fun y hy => (hk'.2 y hy).1) hz, blkMat_mulVec_mem hL (fun y hy => (hk'.2 y hy).2) hz⟩

end GlobalTheory.DefSkewStab
