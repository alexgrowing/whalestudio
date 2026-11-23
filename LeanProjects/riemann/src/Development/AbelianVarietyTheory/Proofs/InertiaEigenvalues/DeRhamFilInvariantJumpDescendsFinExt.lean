import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.InvDescent

theorem exists_invariant_of_subgroup {G F Ω V : Type} [Group G] [Field F] [Field Ω]
    [AddCommGroup V] [Module Ω V] (H : Subgroup G) [Finite (G ⧸ H)]
    (ι : F →* Ω) (σ : G → Ω →* Ω) (hσ : ∀ g h c, σ (g * h) c = σ g (σ h c))
    (hσ1 : ∀ c, σ 1 c = c)
    (hH : ∀ g, g ∈ H ↔ ∀ c, σ g (ι c) = ι c)
    (A : G → V →+ V) (hA : ∀ g h v, A (g * h) v = A g (A h v))
    (hAs : ∀ g (c : Ω) v, A g (c • v) = σ g c • A g v)
    (N₀ N₁ : Submodule Ω V) (hN : ∀ g, ∀ v ∈ N₀, A g v ∈ N₀)
    (y : V) (hy : ∀ h ∈ H, A h y = y) (h0 : y ∈ N₀) (h1 : y ∉ N₁) :
    ∃ z, (∀ g, A g z = z) ∧ z ∈ N₀ ∧ z ∉ N₁ := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _

  have key : ∀ (v : V), (∀ h ∈ H, A h v = v) → ∀ g g' : G,
      (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g' → A g v = A g' v := by
    intro v hv g g' hgg'
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, g' = g * h :=
      ⟨g⁻¹ * g', QuotientGroup.eq.mp hgg', by group⟩
    rw [hA, hv h hh]
  have hfix : ∀ c : F, ∀ h ∈ H, A h (ι c • y) = ι c • y := by
    intro c h hh
    rw [hAs, hy h hh, ((hH h).mp hh) c]

  let T : F → V := fun c => ∑ q : G ⧸ H, A q.out (ι c • y)
  have hTinv : ∀ c g, A g (T c) = T c := by
    intro c g
    simp only [T, map_sum, ← hA]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun q => ?_)
    apply key _ (hfix c)
    rw [MulAction.toPerm_apply, QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  have hT0 : ∀ c, T c ∈ N₀ := by
    intro c
    refine Submodule.sum_mem _ (fun q _ => ?_)
    rw [hAs]
    exact N₀.smul_mem _ (hN _ _ h0)
  by_contra hcon
  push Not at hcon
  have hT1 : ∀ c, T c ∈ N₁ := fun c => hcon (T c) (hTinv c) (hT0 c)

  let χ : G ⧸ H → (F →* Ω) := fun q => (σ q.out).comp ι
  have hσinv : ∀ g x, σ g⁻¹ (σ g x) = x := by
    intro g x
    rw [← hσ, inv_mul_cancel, hσ1]
  have hχ : Function.Injective χ := by
    intro q q' hqq'
    have hcq : ∀ c : F, σ q.out (ι c) = σ q'.out (ι c) := fun c => DFunLike.congr_fun hqq' c
    have hmem : q.out⁻¹ * q'.out ∈ H := by
      rw [hH]
      intro c
      rw [hσ, ← hcq, hσinv]
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact QuotientGroup.eq.mpr hmem
  have hli : LinearIndependent Ω (fun q => (χ q : F → Ω)) :=
    (linearIndependent_monoidHom F Ω).comp χ hχ

  let w : G ⧸ H → V ⧸ N₁ := fun q => N₁.mkQ (A q.out y)
  have hrel : ∀ c : F, ∑ q, χ q c • w q = 0 := by
    intro c
    have hz := (Submodule.Quotient.mk_eq_zero N₁).mpr (hT1 c)
    simp only [T, hAs] at hz
    rw [← Submodule.mkQ_apply, map_sum] at hz
    simpa [χ, w] using hz
  have hw : ∀ q, w q = 0 := by
    intro q
    rw [← Module.forall_dual_apply_eq_zero_iff Ω]
    intro φ
    have hsum : ∑ q', φ (w q') • (χ q' : F → Ω) = 0 := by
      funext c
      have hcq := congrArg φ (hrel c)
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hcq
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hcq]
      exact Finset.sum_congr rfl (fun q' _ => mul_comm _ _)
    exact Fintype.linearIndependent_iff.mp hli _ hsum q
  have hy1 : A (QuotientGroup.mk (1 : G) : G ⧸ H).out y = y := by
    rw [key y hy _ 1 (QuotientGroup.out_eq' _)]
    exact hy 1 H.one_mem
  have hw1 := hw (QuotientGroup.mk 1)
  simp only [w, Submodule.mkQ_apply, hy1, Submodule.Quotient.mk_eq_zero] at hw1
  exact h1 hw1

variable {l : ℕ} [Fact l.Prime]

theorem smul_mem_Fil (P : LocPrime l) (K : FinExt l) (a : ℤ) (c : Om l) {x : P.R.BdR}
    (hx : x ∈ (P.PD K).Fil a) : c • x ∈ (P.PD K).Fil a := by

  have hint : IsIntegral ℚ_[l] c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  obtain ⟨K', hcK⟩ : ∃ K' : FinExt l, c ∈ K'.1 :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {c}, IntermediateField.adjoin.finiteDimensional hint⟩,
      IntermediateField.mem_adjoin_simple_self ℚ_[l] c⟩
  have hx' : x ∈ (P.PD K').Fil a := by
    rw [← SetLike.mem_coe, ← P.PD_Fil K K' a]
    exact hx
  rw [← SetLike.mem_coe, P.PD_Fil K K' a, SetLike.mem_coe]
  exact ((P.PD K').Fil a).smul_mem (⟨c, hcK⟩ : K'.1) hx'

def filOm (P : LocPrime l) (K : FinExt l) (a : ℤ) : Submodule (Om l) P.R.BdR where
  carrier := ((P.PD K).Fil a : Set P.R.BdR)
  zero_mem' := ((P.PD K).Fil a).zero_mem
  add_mem' := fun h h' => ((P.PD K).Fil a).add_mem h h'
  smul_mem' := fun c _ hx => smul_mem_Fil P K a c hx

theorem finite_quot (K E : FinExt l) : Finite (↥(GK K) ⧸ (GK E).subgroupOf (GK K)) := by
  classical
  have : FiniteDimensional ℚ_[l] E.1 := E.2

  let f : (↥(GK K) ⧸ (GK E).subgroupOf (GK K)) → (E.1 →ₐ[ℚ_[l]] Om l) :=
    fun q => ((q.out : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp E.1.val
  refine Finite.of_injective f (fun q q' hqq' => ?_)
  have hres : ∀ x : E.1, (q.out : GQ l) x = (q'.out : GQ l) x := fun x => DFunLike.congr_fun hqq' x
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
  refine QuotientGroup.eq.mpr ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  change _ ∈ IntermediateField.fixingSubgroup E.1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' := hres ⟨x, hx⟩
  simp only at hx'
  rw [AlgEquiv.mul_apply, ← hx']
  exact AlgEquiv.symm_apply_apply _ _

theorem jump_descends (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K E : FinExt l) (_hKE : K.1 ≤ E.1)
    (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l])
    (hM : ∀ g ∈ GK K, ∀ h ∈ GK K, M (g * h) = M g * M h) (a : ℤ) (y : Fin d → P.R.BdR)
    (hy : ∀ g ∈ GK E, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
      (fun i => P.actQdR g (y i)) = y)
    (h0 : ∀ i, y i ∈ (P.PD K).Fil a) (h1 : ¬ (∀ i, y i ∈ (P.PD K).Fil (a + 1))) :
    ∃ z : Fin d → P.R.BdR, (∀ g ∈ GK K, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
      (fun i => P.actQdR g (z i)) = z) ∧ (∀ i, z i ∈ (P.PD K).Fil a) ∧
      ¬ (∀ i, z i ∈ (P.PD K).Fil (a + 1)) := by
  have := finite_quot K E
  let am := algebraMap ℚ_[l] P.R.BdR

  let A : ↥(GK K) → (Fin d → P.R.BdR) →+ (Fin d → P.R.BdR) := fun g =>
    AddMonoidHom.mk' (fun v => ((M g).map am).mulVec (fun i => P.actQdR g (v i)))
      (fun v w => by simp only [Pi.add_apply, map_add]; exact Matrix.mulVec_add _ _ _)
  have hAapp : ∀ g v, A g v = ((M g).map am).mulVec (fun i => P.actQdR g (v i)) := fun _ _ => rfl
  let σ : ↥(GK K) → Om l →* Om l := fun g => MonoidHomClass.toMonoidHom (g : GQ l)
  let ι : ↥E.1 →* Om l := MonoidHomClass.toMonoidHom E.1.val
  have hσ : ∀ g h c, σ (g * h) c = σ g (σ h c) := fun g h c => by
    simp only [σ, MonoidHom.coe_coe, Subgroup.coe_mul, AlgEquiv.mul_apply]
  have hσ1 : ∀ c, σ 1 c = c := fun c => by
    simp only [σ, MonoidHom.coe_coe, OneMemClass.coe_one, AlgEquiv.one_apply]
  have hH : ∀ g, g ∈ (GK E).subgroupOf (GK K) ↔ ∀ c, σ g (ι c) = ι c := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    unfold GK
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h c => h c c.2, fun h x hx => h ⟨x, hx⟩⟩
  have hcomm : ∀ (f : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) (N : Matrix (Fin d) (Fin d) ℚ_[l])
      (w : Fin d → P.R.BdR), (fun i => f ((N.map am).mulVec w i)) = (N.map am).mulVec (fun i => f (w i)) := by
    intro f N w
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, am, AlgEquiv.commutes]
  have hA : ∀ g h v, A (g * h) v = A g (A h v) := by
    intro g h v
    rw [hAapp, hAapp, hAapp, hcomm, Matrix.mulVec_mulVec, ← Matrix.map_mul,
      ← hM g g.2 h h.2, Subgroup.coe_mul]
    congr 1
    funext i
    rw [map_mul, AlgEquiv.mul_apply]
  have hAs : ∀ g (c : Om l) v, A g (c • v) = σ g c • A g v := by
    intro g c v
    rw [hAapp, hAapp]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, Algebra.smul_def,
      map_mul, P.actQdR_Om, Finset.mul_sum, σ, MonoidHom.coe_coe]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  let N₀ : Submodule (Om l) (Fin d → P.R.BdR) := Submodule.pi Set.univ (fun _ => filOm P K a)
  let N₁ : Submodule (Om l) (Fin d → P.R.BdR) := Submodule.pi Set.univ (fun _ => filOm P K (a + 1))
  have hmem : ∀ (b : ℤ) (v : Fin d → P.R.BdR),
      v ∈ Submodule.pi Set.univ (fun _ => filOm P K b) ↔ ∀ i, v i ∈ (P.PD K).Fil b := by
    intro b v
    simp only [Submodule.mem_pi, Set.mem_univ, true_imp_iff]
    rfl
  have hN : ∀ g, ∀ v ∈ N₀, A g v ∈ N₀ := by
    intro g v hv
    rw [hmem] at hv ⊢
    intro i
    rw [hAapp]
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have hj : P.actQdR g (v j) ∈ (P.PD K).Fil a := by
      rw [← P.PD_actdR K g]
      exact (P.PD K).Fil_G g a _ (hv j)
    rw [Matrix.map_apply, ← Algebra.smul_def]
    exact Submodule.smul_of_tower_mem _ _ hj
  obtain ⟨z, hzA, hz0, hz1⟩ := exists_invariant_of_subgroup ((GK E).subgroupOf (GK K)) ι σ hσ hσ1 hH
    A hA hAs N₀ N₁ hN y (fun h hh => hy h ((Subgroup.mem_subgroupOf).mp hh)) ((hmem a y).mpr h0)
    (fun h => h1 ((hmem (a + 1) y).mp h))
  exact ⟨z, fun g hg => hzA ⟨g, hg⟩, (hmem a z).mp hz0, fun h => hz1 ((hmem (a + 1) z).mpr h)⟩

end GlobalTheory.InvDescent
