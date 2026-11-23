import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverseStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDualFamilySelfDualHermitianSpace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.UpMem
variable {D : D7}
open GlobalTheory.FinPl

theorem smul_mem_latMul (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) (P : Pl D → Prop) (w : AE D)
    (hw : finPart D w ∈ intAE D) : ∀ y ∈ latMul S 𝔞 L P, w • y ∈ latMul S 𝔞 L P := by
  let Ψ : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) := AddMonoidHom.mk' (fun u => w • u) fun x y => smul_add w x y
  have main : latMul S 𝔞 L P ≤ (latMul S 𝔞 L P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, x, hx, rfl⟩
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) := AddMonoidHom.mk'
      (fun y => fun i => GlobalTheory.LatticeStable.liftMul D (α ⊗ₜ[D.host.F] (a * x i)) y)
      fun y y' => funext fun i => (GlobalTheory.LatticeStable.liftMul D _).map_add y y'
    have hle : intAE D ≤ (latMul S 𝔞 L P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨β, hβ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun v hv => ?_, a, ha, o • x, L.smul_mem o hx, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · rw [map_mul, hP v hv, mul_zero]
      · funext i
        change GlobalTheory.LatticeStable.liftFin D ((β ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] _)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
          show algebraMap _ _ o = (o : D.host.E) from rfl]
        congr 1
        ring
    have e : Ψ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) = Φ (finPart D w) :=
      funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D w α _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact fun u hu => main hu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finPart_e_int (q : SplitPt D k) : finPart D q.e ∈ intAE D := by
  have h := (q.int_iff 1).1 (one_mem _)
  have h1 : q.sec 1 = q.e := by
    have := q.sec_pr 1
    rwa [map_one, mul_one] at this
  rwa [h1] at h

theorem e_mul_mem_latV (q : SplitPt D k) (S : HSp D) (L : Lat S) {s : Fin S.rank → D.host.E} (hs : s ∈ L) :
    (fun j => q.e * incA D (s j)) ∈ latV S L (· = q.v) := by
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, hsum⟩ := q.above
  have hα : α ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have hg : (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s j)) ∈ latV S L (· = q.v) :=
    AddSubgroup.subset_closure ⟨α, hα, fun u hu => h0 u hu, 1, rfl, s, hs, rfl⟩
  have he : q.e • (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s j)) ∈ latV S L (· = q.v) :=
    smul_mem_latMul S {1} L (· = q.v) q.e (finPart_e_int q) _ hg
  convert he using 1
  funext j
  have hee : q.e * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = q.e := by
    rw [← hsum, mul_add, q.split.1, q.split.2.1, add_zero]
  rw [Pi.smul_apply, smul_eq_mul, one_mul]
  have : pairA D.host.F 0 α ⊗ₜ[D.host.F] s j = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * incA D (s j) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    change _ = (_ ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] s j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this, ← mul_assoc, hee]

end GlobalTheory.UpMem

namespace GlobalTheory.UpMem
variable {D : D7}
open GlobalTheory.FinPl

theorem rankOne_mem_latO (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop) {s : Fin S.rank → D.host.E}
    (hs : s ∈ LS) {y : Fin T.rank → AE D} (hy : y ∈ latA T LT P) :
    (Matrix.of fun i j => y i * incA D (∑ l, star (s l) * S.gram l j) : WO S T) ∈
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P := by
  let Φ : (Fin T.rank → AE D) →+ WO S T := AddMonoidHom.mk'
    (fun y => Matrix.of fun i j => y i * incA D (∑ l, star (s l) * S.gram l j))
    fun y y' => Matrix.ext fun i j => add_mul (y i) (y' i) _
  have main : latA T LT P ≤ (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩
    ext i j
    change (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  exact main hy

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mul (q : SplitPt D k) (a : k) (b : AE D) : q.sec a * b = q.sec (a * q.pr b) := by
  have h1 : q.e * q.sec a = q.sec a := by rw [← q.sec_pr, q.pr_sec]
  calc q.sec a * b = q.e * (q.sec a * b) := by rw [← mul_assoc, h1]
    _ = q.sec (q.pr (q.sec a * b)) := (q.sec_pr _).symm
    _ = q.sec (a * q.pr b) := by rw [map_mul, q.pr_sec]

end GlobalTheory.UpMem

namespace GlobalTheory.UpMem
open GlobalTheory.FinPl

theorem up_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → (ofSplit q).up FS FT x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hS hT hFS hFT x hx
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S LS hS
  set u := (ofSplit q).up FS FT x with hu_def
  let z : Fin n → Y' → k := fun c => FS.γ *ᵥ (fun m => q.pr (incA D (s c m)))
  let y : Fin n → Fin T.rank → AE D := fun c i => ∑ m, u i m * incA D (s c m)
  have hz : ∀ c r, z c r ∈ 𝒪[k] := by
    intro c
    refine (hFS (z c)).2 ?_
    have : (fun i => q.sec ((FS.β *ᵥ z c) i)) = fun j => q.e * incA D (s c j) := by
      funext j
      simp only [z, Matrix.mulVec_mulVec, FS.βγ, Matrix.one_mulVec]
      exact q.sec_pr _
    rw [this]
    exact e_mul_mem_latV q S LS (hs c).1
  have hy : ∀ c, y c ∈ latA T LT (· = q.v) := by
    intro c
    rw [hU.2 T LT]
    have hint : ∀ r, (x *ᵥ z c) r ∈ 𝒪[k] := fun r =>
      Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hx r m) (hz c m)
    convert (hFT (x *ᵥ z c)).1 hint using 1
    funext i
    change ∑ m, q.sec ((FT.β * x * FS.γ) i m) * incA D (s c m) = _
    simp_rw [sec_mul]
    rw [← map_sum]
    congr 1
    simp only [z, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc]
    rfl
  have hdec : u = ∑ c, (Matrix.of fun i j => y c i * incA D (∑ l, star (s' c l) * S.gram l j) : WO S T) := by
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.of_apply, y, Finset.sum_mul]
    rw [Finset.sum_comm]
    have key : ∀ m, ∑ c, u i m * incA D (s c m) * incA D (∑ l, star (s' c l) * S.gram l j) =
        u i m * incA D (if m = j then 1 else 0) := by
      intro m
      rw [← hss m j, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul, mul_assoc]
    rw [Finset.sum_congr rfl fun m _ => key m]
    simp [apply_ite]
  rw [hdec]
  exact sum_mem fun c _ => rankOne_mem_latO S T LS LT _ (hs c).2 (hy c)

end GlobalTheory.UpMem
