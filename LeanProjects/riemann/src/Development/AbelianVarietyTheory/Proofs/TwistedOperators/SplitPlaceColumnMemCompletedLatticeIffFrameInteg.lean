import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SplitFrameColumn

theorem intAE_mul {D : D7} {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, c, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, d, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, c * d, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; push_cast; rfl
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem comm_mem_intAf_iff {D : D7} (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      z ∈ intAE D := by
  constructor
  · intro hs
    have hs' : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z ∈
        Subring.closure (Set.range (fun x : Formalism.UG.intOE D.host.E => (x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∪
        Set.range (fun y : Formalism.UG.intAd D.host.F => (1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F))) := hs
    suffices h : ∀ s ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE D.host.E => (x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∪
        Set.range (fun y : Formalism.UG.intAd D.host.F => (1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F))),
        (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm s ∈ intAE D by
      simpa using h _ hs'
    have hone : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by rw [map_one]; exact one_mem _
    intro s hs
    induction hs using Subring.closure_induction with
    | mem s hs =>
      rcases hs with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
      · exact AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩
      · refine AddSubgroup.subset_closure ⟨a, fun w => ha w, 1, ?_⟩
        simp
    | zero => rw [map_zero]; exact zero_mem _
    | one => rw [map_one]; exact AddSubgroup.subset_closure ⟨1, hone, 1, by simp [Algebra.TensorProduct.one_def]⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact intAE_mul hx hy
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      rw [Algebra.TensorProduct.comm_tmul]
      have hx : (x : D.host.E) ⊗ₜ[D.host.F] a =
          ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hx]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨(x : D.host.E), ⟨x, rfl⟩⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem toEAf_finEmb {D : D7} (t : EAf D) : toEAf D (GlobalTheory.AdelicLatMove.finEmb D t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul x α => rfl

theorem latHat_iff_hatL {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) ↔
      (fun i => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact GlobalTheory.AdelicLatMove.pure_mem_hatL Λ a (fun w => ha w) x hx
    | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => simp only [Pi.add_apply, map_add]; exact add_mem hx hy
    | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx
  · intro hz
    have key : ∀ w ∈ AddSubgroup.closure (GlobalTheory.AdelicLatMove.pureSet (D := D) Λ),
        (fun i => (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm (w i)) ∈
          Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) := by
      intro w hw
      induction hw using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨α, hα, x, hx, rfl⟩ := hw
        exact AddSubgroup.subset_closure ⟨α, fun u => hα u, x, hx, rfl⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => simp only [Pi.add_apply, map_add]; exact add_mem hx hy
      | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx
    have := key _ (GlobalTheory.AdelicLatMove.mem_closure_of_mem_hatL Λ _ hz)
    simpa only [AlgEquiv.symm_apply_apply] using this

theorem frame_column : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (EAf D)), IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ ∀ i, Valued.v ((((frCo φ β)⁻¹ : GL (Fin V.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdA φ (y k)) i) ≤ 1 := by
  intro D V Λ β _ hβ v φ e he y
  obtain ⟨hπ, hE, -, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  set u : Fin V.rank → EAf D := (β⁻¹).1 *ᵥ fun k => toEAf D (y k) with hu
  have hsw : (fun k => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (e * y k))) =
      toEAf D e • fun k => toEAf D (y k) := funext fun k => (toEAf D).map_mul e (y k)
  have hfe : ∀ t : EAf D, toEAf D (GlobalTheory.AdelicLatMove.finEmb D t) = t := toEAf_finEmb
  rw [latHat_iff_hatL, hβ, hsw, Matrix.mulVec_smul]
  refine forall_congr' fun i => ?_
  have h1 : (toEAf D e • u) i = toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (u i)) := by
    rw [map_mul, hfe]; rfl
  have h2 : rdA φ (GlobalTheory.AdelicLatMove.finEmb D (u i)) =
      ((((frCo φ β)⁻¹ : GL (Fin V.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdA φ (y k)) i) := by
    rw [← hE, hfe, hu, RingHom.map_mulVec]
    unfold frCo
    rw [← map_inv]
    congr 1
    funext k
    exact hE (y k)
  rw [h1, show toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (u i)) =
      Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (e * GlobalTheory.AdelicLatMove.finEmb D (u i))) from rfl,
    comm_mem_intAf_iff, hπ.2.2.2, GlobalTheory.SplitHecke.isInt_Ov, HeightOneSpectrum.mem_adicCompletionIntegers, h2]

end GlobalTheory.SplitFrameColumn
