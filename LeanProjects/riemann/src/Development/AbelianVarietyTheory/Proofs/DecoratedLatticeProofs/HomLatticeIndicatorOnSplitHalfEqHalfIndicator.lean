import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LatIndHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_one (p : SplitPt D k) : p.sec 1 = p.e := by
  rw [← map_one p.pr, p.sec_pr, mul_one]

theorem e_mul_sec (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem sec_mul (p : SplitPt D k) (a b : k) : p.sec (a * b) = p.sec a * p.sec b :=
  calc p.sec (a * b) = p.sec (p.pr (p.sec a * p.sec b)) := by rw [map_mul p.pr, p.pr_sec, p.pr_sec]
    _ = p.e * (p.sec a * p.sec b) := p.sec_pr _
    _ = p.sec a * p.sec b := by rw [← mul_assoc, e_mul_sec]

theorem e_mem_idAt (p : SplitPt D k) : p.e ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem p
  obtain ⟨α, rfl, -, h0⟩ := hε
  have hmem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ idAt D (· = p.v) := by
    rw [show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) from rfl]
    unfold idAt
    rw [Submodule.mem_inf, RingHom.mem_ker, Submodule.mem_iInf]
    refine ⟨?_, fun w => RingHom.mem_ker.2 ?_⟩
    · change fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · change evalV D.host.F w.1 α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  rw [← heε]
  exact Ideal.mul_mem_right _ _ hmem

theorem mul_mem_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} {w : AE D} (hw : finPart D w ∈ intAE D)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : (fun i => w * y i) ∈ latV S L P := by
  let Ψ : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) :=
    AddMonoidHom.mk' (fun y i => w * y i) fun a b => funext fun i => mul_add w (a i) (b i)
  have main : latV S L P ≤ (latV S L P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) :=
      AddMonoidHom.mk' (fun c i => GlobalTheory.LatticeStable.liftFin D (c * (β ⊗ₜ[D.host.F] (1 * x i))))
        fun c c' => funext fun i => by rw [add_mul, LinearMap.map_add]; rfl
    have hle : intAE D ≤ (latV S L P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨γ, hγ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨γ * β, fun v => by rw [map_mul]; exact mul_mem (hγ v) (hβi v),
        fun v hv => by rw [map_mul, hβ v hv, mul_zero], 1, rfl, o • x, L.smul_mem o hx, ?_⟩
      funext i
      change GlobalTheory.LatticeStable.liftFin D ((γ ⊗ₜ[D.host.F] (o : D.host.E)) * (β ⊗ₜ[D.host.F] (1 * x i))) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
        show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl]
      congr 1
      ring
    have e : Ψ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) = Φ (finPart D w) :=
      funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D w β _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact main hy

variable {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem mulVec_sec (α : Frame p S n') (β : Frame p T n) {t : WO S T} (ht : IsHalf p.e t) (x : n' → k) :
    t *ᵥ (fun j => p.sec ((α.b *ᵥ x) j)) = fun i => p.sec ((β.b *ᵥ (rd α β t *ᵥ x)) i) := by
  have hM : (β.b * rd α β t * α.b') *ᵥ (α.b *ᵥ x) = β.b *ᵥ (rd α β t *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (β.b * rd α β t), α.b'b, Matrix.mul_one, Matrix.mulVec_mulVec]
  rw [← hM]
  funext i
  conv_lhs => rw [← GlobalTheory.FinPl.HalfInd.wr_rd α β ht]
  simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.HalfInd.wr_apply]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => (sec_mul p _ _).symm

theorem mem_latO_iff_rd (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) (hU : p.UnitAA) {ΛS : Submodule 𝒪[k] (n' → k)} {ΛT : Submodule 𝒪[k] (n → k)}
    (hα : α.IsLat LS ΛS) (hβ : β.IsLat LT ΛT) {t : WO S T} (ht : IsHalf p.e t) :
    t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ↔ ∀ x ∈ ΛS, rd α β t *ᵥ x ∈ ΛT := by
  have hmem := GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = p.v) t
  rw [hU.2 T LT] at hmem
  constructor
  · intro h x hx
    have h1 : t *ᵥ (fun j => p.sec ((α.b *ᵥ x) j)) ∈ latV T LT (· = p.v) := (hmem.1 h).2 _ ((hα x).1 hx)
    rw [mulVec_sec α β ht] at h1
    exact (hβ _).2 h1
  · intro h
    refine hmem.2 ⟨fun i j => ?_, fun y hy => ?_⟩
    · rw [← ht i j]
      exact Ideal.mul_mem_right _ _ (e_mem_idAt p)
    · have hy' : t *ᵥ y = t *ᵥ (fun j => p.e * y j) := by
        funext i
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, mul_comm (t i j) p.e, ht i j]
      have hey : (fun j => p.e * y j) = fun j => p.sec ((α.b *ᵥ (α.b' *ᵥ fun j => p.pr (y j))) j) := by
        funext j
        rw [Matrix.mulVec_mulVec, α.bb', Matrix.one_mulVec, p.sec_pr]
      have hint : finPart D p.e ∈ intAE D := by
        rw [← sec_one p]
        exact (p.int_iff 1).1 (one_mem _)
      have hx : α.b' *ᵥ (fun j => p.pr (y j)) ∈ ΛS := (hα _).2 (hey ▸ mul_mem_latV hint hy)
      show t *ᵥ y ∈ latV T LT (· = p.v)
      rw [hy', hey, mulVec_sec α β ht]
      exact (hβ _).1 (h _ hx)

end GlobalTheory.FinPl.LatIndHalf

theorem GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → p.UnitAA → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → extFun α β (latInd ΛS ΛT) = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT hU ΛS ΛT hα hβ
  funext t
  unfold extFun halfInd
  by_cases ht : IsHalf p.e t
  · rw [if_pos ht]
    unfold latInd
    have key := GlobalTheory.FinPl.LatIndHalf.mem_latO_iff_rd α β hS hT hU hα hβ ht
    by_cases h : t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v)
    · rw [if_pos (key.1 h), if_pos ⟨h, ht⟩]
    · rw [if_neg fun h' => h (key.2 h'), if_neg fun h' => h h'.1]
  · rw [if_neg ht, if_neg fun h => ht h.2]

end
