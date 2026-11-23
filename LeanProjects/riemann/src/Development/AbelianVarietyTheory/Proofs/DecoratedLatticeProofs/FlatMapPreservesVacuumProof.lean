import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.FlatVacuum

variable {D : D7}

theorem mulVec_mem_ideal {m n : ℕ} (I : Ideal (AE D)) (M : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) (i : Fin m) : (M *ᵥ y) i ∈ I := by
  show ∑ j, M i j * y j ∈ I
  exact I.sum_mem fun j _ => I.mul_mem_left _ (hy j)

theorem mulVec_latV_of_local {S S' : HSp D} {L : Lat S} {L' : Lat S'} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {P : Pl D → Prop} (M : Matrix (Fin S'.rank) (Fin S.rank) (AE D))
    (h : ∀ v, P v → ∀ y ∈ latV S L (· = v), M *ᵥ y ∈ latV S' L' (· = v)) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : M *ᵥ y ∈ latV S' L' P := by
  obtain ⟨h1, h2⟩ := (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S).2.2.2 L y hL).1 hy
  refine (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S').2.2.2 L' _ hL').2 ⟨mulVec_mem_ideal _ M h1, fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact h v hv _ (h2 v hv e he)

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem mulVec_latA {S S' : HSp D} {L : Lat S} {L' : Lat S'} {P : Pl D → Prop}
    (M : Matrix (Fin S'.rank) (Fin S.rank) (AE D)) (h : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV S' L' P)
    {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) : M *ᵥ y ∈ latA S' L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    have e : (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) : AE D)) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) : AE D) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e, Matrix.mulVec_smul]
    exact smul_mem_latA ha (h _ (AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

section Mono

variable {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L : Lat S} {L₀ : Lat S₀}

theorem p0_mem {v : Pl D} (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    d.p0 *ᵥ y ∈ latV S₀ L₀ (· = v) := ((h y).1 hy).2.2

theorem wittCoreInclusion_mulVec_mem_latticeCompletionAtPlace {v : Pl D} (h : MonoAt d L L₀ v) {y : Fin S₀.rank → AE D} (hy : y ∈ latV S₀ L₀ (· = v)) :
    d.j0 *ᵥ y ∈ latV S L (· = v) := by
  have hX : d.pX *ᵥ (d.j0 *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec]; exact (congrArg (· *ᵥ y) d.pX_j0).trans (Matrix.zero_mulVec _)
  have hY : d.pY *ᵥ (d.j0 *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec]; exact (congrArg (· *ᵥ y) d.pY_j0).trans (Matrix.zero_mulVec _)
  have h0 : d.p0 *ᵥ (d.j0 *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec]; exact (congrArg (· *ᵥ y) d.p0_j0).trans (Matrix.one_mulVec _)
  have hc : ∀ (x : Mx D S.rank ρ) i, colMul x i 0 = 0 := fun x i => funext fun k => zero_mul _
  refine (h _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [hX, Pi.zero_apply, hc]; exact zero_mem _
  · rw [hY, Pi.zero_apply, hc]; exact zero_mem _
  · rw [h0]; exact hy

theorem wittExtendByZero_mem_completedHomLattice {T : HSp D} {LT : Lat T} {P : Pl D → Prop} (hL : IsSelfDualC S L) (hL₀ : IsSelfDualC S₀ L₀)
    (hT : IsSelfDualC T LT) (h : ∀ v, P v → MonoAt d L L₀ v) {w : WO S₀ T}
    (hw : w ∈ latO S₀ T (L₀ : Set _) (LT : Set _) P) : d.ext0 T w ∈ latO S T (L : Set _) (LT : Set _) P := by
  obtain ⟨h1, h2⟩ := (LatMem.mem_latO_iff D S₀ T L₀ LT hL₀ hT P w).1 hw
  refine (LatMem.mem_latO_iff D S T L LT hL hT P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · show ∑ k, w i k * d.p0 k j ∈ idAt D P
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (h1 i k)
  · have := h2 _ (mulVec_latV_of_local hL.1 hL₀.1 d.p0 (fun v hv z hz => p0_mem (h v hv) hz) hy)
    rw [Matrix.mulVec_mulVec] at this
    exact this

theorem wittCoreInclusion_mem_completedHomLattice {T : HSp D} {LT : Lat T} {P : Pl D → Prop} (hL : IsSelfDualC S L) (hL₀ : IsSelfDualC S₀ L₀)
    (hT : IsSelfDualC T LT) (h : ∀ v, P v → MonoAt d L L₀ v) {w : WO T S₀}
    (hw : w ∈ latO T S₀ (LT : Set _) (L₀ : Set _) P) : d.inc0 T w ∈ latO T S (LT : Set _) (L : Set _) P := by
  obtain ⟨h1, h2⟩ := (LatMem.mem_latO_iff D T S₀ LT L₀ hT hL₀ P w).1 hw
  refine (LatMem.mem_latO_iff D T S LT L hT hL P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · show ∑ k, d.j0 i k * w k j ∈ idAt D P
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h1 k j)
  · have := mulVec_latA d.j0
      (fun z hz => mulVec_latV_of_local hL₀.1 hL.1 d.j0 (fun v hv z hz => wittCoreInclusion_mulVec_mem_latticeCompletionAtPlace (h v hv) hz) hz) (h2 y hy)
    rw [Matrix.mulVec_mulVec] at this
    exact this

theorem isHalf_wittExtendByZero {T : HSp D} {e : AE D} {w : WO S₀ T} (hw : IsHalf e w) : IsHalf e (d.ext0 T w) :=
  fun i j => GlobalTheory.WeilSrc.entries_fix_right e hw d.p0 i j

theorem isHalf_wittCoreInclusion {T : HSp D} {e : AE D} {w : WO T S₀} (hw : IsHalf e w) : IsHalf e (d.inc0 T w) := by
  intro i j
  show e * (∑ k, d.j0 i k * w k j) = ∑ k, d.j0 i k * w k j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hw k j]

end Mono

theorem isLatVac_of_intertwine {m n m' n' : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)}
    {hs' : Mx D m' n' → (Mx D m' n' → ℂ) → (Mx D m' n' → ℂ)} {Λ : AddSubgroup (Mx D m n)} {Λ' : AddSubgroup (Mx D m' n')}
    (ι : Mx D m' n' →+ Mx D m n) (hΛ : ∀ u ∈ Λ', ι u ∈ Λ) (hh : ∀ e u, IsHalf e u → IsHalf e (ι u))
    (𝔉 : (Mx D m n → ℂ) → (Mx D m' n' → ℂ)) {f : Mx D m n → ℂ} (hF : ∀ u ∈ Λ', 𝔉 (hs (ι u) f) = hs' u (𝔉 f))
    (hf : IsLatVac hs Λ f) : IsLatVac hs' Λ' (𝔉 f) := by
  refine ⟨fun u hu => ?_, fun e he u hu hue => ?_⟩
  · rw [← hF _ (Λ'.nsmul_mem hu 2), map_nsmul, hf.1 _ (hΛ u hu)]
  · rw [← hF _ hu, hf.2 e he _ (hΛ u hu) (hh e u hue)]

theorem latO_empty {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} (hP : ∀ v, ¬ P v) {u : WO S T} (hu : u ∈ latO S T LS LT P) : u = 0 := by
  ext i j
  have h1 := LatMem.mul_indP (LatMem.latO_mxAt hu i j)
  have h2 : LatMem.indP D.host.F P = 0 := by
    classical
    refine Subtype.ext (funext fun v => ?_)
    exact if_neg (hP v)
  have h3 : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
  rw [h2, h3, TensorProduct.zero_tmul, mul_zero] at h1
  exact h1.symm

theorem vac_of_heisLaws {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} {dV : HypDec V V₀ ρ}
    {dW : HypDec W W₀ σ} {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ} {P : Pl D → Prop}
    {𝔉 : (WO V W → ℂ) → (WO V₀ W₀ → ℂ)} (H : HeisLaws ψ dV dW x y P 𝔉) {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W}
    {LW₀ : Lat W₀}
    (h : ∀ v, P v → IsSelfDualC V LV ∧ IsSelfDualC V₀ LV₀ ∧ IsSelfDualC W LW ∧ IsSelfDualC W₀ LW₀ ∧
      MonoAt dV LV LV₀ v ∧ MonoAt dW LW LW₀ v) {Φ : WO V W → ℂ} (hΦ : Vac ψ V W LV LW P Φ) :
    Vac ψ V₀ W₀ LV₀ LW₀ P (𝔉 Φ) := by
  refine ⟨H.theta Φ hΦ.1, isLatVac_of_intertwine ((dV.ext0 W).comp (dW.inc0 V₀)) (fun u hu => ?_)
    (fun e u hu => isHalf_wittExtendByZero (isHalf_wittCoreInclusion hu)) 𝔉 (fun u hu => H.core Φ hΦ.1 u (LatMem.latO_mxAt hu)) hΦ.2⟩
  by_cases hP : ∃ v, P v
  · obtain ⟨v, hv⟩ := hP
    obtain ⟨a, b, c, e, -⟩ := h v hv
    exact wittExtendByZero_mem_completedHomLattice a b c (fun v hv => (h v hv).2.2.2.2.1) (wittCoreInclusion_mem_completedHomLattice c e b (fun v hv => (h v hv).2.2.2.2.2) hu)
  · rw [latO_empty (not_exists.1 hP) hu, map_zero]
    exact zero_mem _

theorem flatVac : ∀ D : D7, GlobalTheory.FinPl.FlatVac D := by
  intro D ψ P
  refine ⟨fun ρ B J s LV LV₀ LW LW₀ h Φ hΦ => ?_, fun σ J B s LV LV₀ LW LW₀ h Φ hΦ => ?_,
    fun V V₀ T d L L₀ LT hL hL₀ hT h Φ hΦ => ?_⟩
  · exact vac_of_heisLaws ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).1 ρ B J s).Heisenberg₂
      (fun v hv => ⟨(h v hv).sdV, (h v hv).sdV₀, (h v hv).sdW, (h v hv).sdW₀, (h v hv).monoV, (h v hv).monoW⟩) hΦ
  · exact vac_of_heisLaws ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).2 σ J B s).Heisenberg₂
      (fun v hv => ⟨(h v hv).sdV, (h v hv).sdV₀, (h v hv).sdW, (h v hv).sdW₀, (h v hv).monoV, (h v hv).monoW⟩) hΦ
  · exact ⟨(GlobalTheory.WeilSrc.Zero.theta_iff d Φ).2 hΦ.1, isLatVac_of_intertwine (d.ext0 T)
      (fun u hu => wittExtendByZero_mem_completedHomLattice hL hL₀ hT h hu) (fun e u hu => isHalf_wittExtendByZero hu) (fun f w => f (d.ext0 T w))
      (fun u _ => GlobalTheory.WeilSrc.Zero.heisO_eqv d u Φ) hΦ.2⟩

end GlobalTheory.FinPl.FlatVacuum
