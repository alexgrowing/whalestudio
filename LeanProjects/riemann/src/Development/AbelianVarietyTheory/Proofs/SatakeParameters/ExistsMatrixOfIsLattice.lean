import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLatBasis

theorem exists_matrix_of_isLattice {R K : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {n : ℕ} (M : Submodule R (Fin n → K)) [Submodule.IsLattice K M] :
    ∃ B : GL (Fin n) K, ∀ x : Fin n → K, x ∈ M ↔
      ∀ i, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x i ∈ (algebraMap R K).range := by
  have hr : Module.finrank R M = n := by
    rw [Submodule.IsLattice.finrank_of_pi K M, Fintype.card_fin]
  let b : Module.Basis (Fin n) R M := Module.finBasisOfFinrankEq R M hr
  let c : Module.Basis (Fin n) K (Fin n → K) := b.extendOfIsLattice K
  let p := Pi.basisFun K (Fin n)
  let B : GL (Fin n) K := ⟨p.toMatrix c, c.toMatrix p, by simp, by simp⟩
  have hB : ∀ x i, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x i = c.repr x i := by
    intro x i
    have := congrFun (Module.Basis.toMatrix_mulVec_repr p c x) i
    exact this
  refine ⟨B, fun x => ?_⟩
  simp only [hB]
  constructor
  · intro hx i
    refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 : x = ∑ j, algebraMap R K (b.repr ⟨x, hx⟩ j) • c j := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at this
      simp only [c, Module.Basis.extendOfIsLattice_apply, algebraMap_smul]
      exact this.symm
    have h2 := congrFun (c.repr_sum_self fun j => algebraMap R K (b.repr ⟨x, hx⟩ j)) i
    rw [← h1] at h2
    exact h2.symm
  · intro h
    choose r hr using h
    rw [← c.sum_repr x]
    refine sum_mem fun j _ => ?_
    rw [← hr, algebraMap_smul]
    refine M.smul_mem _ ?_
    simp [c]

theorem mul_mem_intAE (D : D7) {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem section_mem {A K ι κ : Type} [CommRing A] [Field K] (O : ValuationSubring K) (π : A →+* K) (σ : K → A) (ε : A)
    (I : Set A) (L : AddSubgroup (ι → A)) (h1 : ∀ a, π (σ a) = a) (h2 : ∀ x, σ (π x) = ε * x)
    (h3 : ∀ x, π x ∈ O → ε * x ∈ I) (h4 : ∀ a ∈ I, ∀ y ∈ L, (fun i => a * y i) ∈ L)
    (g : κ → ι → A) (hg : ∀ j, g j ∈ L) (w : ι → K)
    (hw : w ∈ Submodule.span O (Set.range fun j i => π (g j i))) : (fun i => σ (w i)) ∈ L := by
  have hε : ε ∈ I := by simpa using h3 1 (by simpa using one_mem O)
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    simp only [h2]
    exact h4 _ hε _ (hg j)
  | zero =>
    have : σ 0 = 0 := by simpa using h2 0
    simp only [Pi.zero_apply, this]
    exact zero_mem L
  | add x y _ _ hx hy =>
    have : ∀ a b, σ (a + b) = ε * (σ a + σ b) := fun a b => by rw [← h2, map_add, h1, h1]
    simp only [Pi.add_apply, this]
    exact h4 _ hε _ (add_mem hx hy)
  | smul c x _ hx =>
    have : ∀ i, σ ((c • x) i) = (ε * σ c) * σ (x i) := fun i => by
      rw [mul_assoc, ← h2, map_mul, h1, h1]; rfl
    simp only [this]
    exact h4 _ (h3 _ (by rw [h1]; exact c.2)) _ hx

set_option maxHeartbeats 1000000 in

theorem exists_basis : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v) (s : Fv D.host.F v → Formalism.L2.Theta.AE D), e * e = e → (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) → (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) → (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) → ∃ B : GL (Fin V.rank) (Fv D.host.F v), ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (fun i => finPart D e * y i) ∈ LamHat V ↔ ∀ i, ((B⁻¹ : GL (Fin V.rank) (Fv D.host.F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v)).mulVec (fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  intro D V e v π s _ h1 h2 h3 h4
  obtain ⟨k, x, hxL, hx⟩ := GlobalTheory.LatticeLocalGlobal.exists_generators V
  let φ : D.host.E →+* Fv D.host.F v := π.comp (Algebra.TensorProduct.includeRight
    (R := D.host.F) (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (B := D.host.E)).toRingHom
  have hφ : ∀ a, φ a = π (1 ⊗ₜ[D.host.F] a) := fun _ => rfl
  let M : Submodule (v.adicCompletionIntegers D.host.F) (Fin V.rank → Fv D.host.F v) :=
    Submodule.span _ (Set.range fun j i => φ (V.frame.repr (x j) i))
  have hL : ∀ w ∈ V.L0, (fun i => φ (V.frame.repr w i)) ∈ M := by
    intro w hw
    obtain ⟨n, rfl⟩ := hx w hw
    have : (fun i => φ (V.frame.repr (∑ j, n j • x j) i)) = ∑ j, n j • fun i => φ (V.frame.repr (x j) i) := by
      funext i
      simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply]
    rw [this]
    exact sum_mem fun j _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self j)) _
  have hsp : ∀ w : V.V, (fun i => φ (V.frame.repr w i)) ∈
      Submodule.span (Fv D.host.F v) (M : Set (Fin V.rank → Fv D.host.F v)) := by
    intro w
    have hw : w ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [V.standardTuple_isLattice.span_eq_top]; trivial
    induction hw using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span (hL w hw)
    | zero =>
      simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
      exact zero_mem _
    | add a b _ _ ha hb =>
      simp only [map_add, Finsupp.coe_add, Pi.add_apply]
      exact add_mem ha hb
    | smul c a _ ha =>
      simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      exact Submodule.smul_mem _ (φ c) ha
  have : Submodule.IsLattice (Fv D.host.F v) M := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← (Pi.basisFun (Fv D.host.F v) (Fin V.rank)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : Pi.basisFun (Fv D.host.F v) (Fin V.rank) i = fun j => φ (V.frame.repr (V.frame i) j) := by
      funext j
      simp only [Pi.basisFun_apply, Module.Basis.repr_self, Pi.single_apply, Finsupp.single_apply, eq_comm (a := i)]
      split_ifs <;> simp
    rw [this]
    exact hsp _
  obtain ⟨B, hB⟩ := exists_matrix_of_isLattice M
  have hε : finPart D e ∈ intAE D := by simpa using (h3 1).2 (by rw [RingHom.map_one]; exact one_mem _)
  have hπε : π (finPart D e) = 1 := by
    have := h1 (π 1)
    rwa [h2, mul_one, RingHom.map_one] at this
  have hto : ∀ z ∈ LamHat V, (fun i => π (z i)) ∈ M := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hy
      have ha' : π (a ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ Formalism.UG.Ov D.host.F v :=
        (h3 _).1 (mul_mem_intAE D hε (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩))
      have hu' := M.smul_mem ⟨_, ha'⟩ (hL _ hu)
      convert hu' using 1
      funext i
      rw [V.frame.repr_sum_self]
      show _ = π _ * π _
      rw [← RingHom.map_mul]
      congr 1
      show _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] u i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | zero =>
      simp only [Pi.zero_apply, RingHom.map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      simp only [Pi.add_apply, RingHom.map_add]
      exact add_mem hy hz
    | neg y _ hy =>
      simp only [Pi.neg_apply, RingHom.map_neg]
      exact neg_mem hy
  refine ⟨B, fun y => ?_⟩
  have hR : ∀ t : Fv D.host.F v, t ∈ (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)).range ↔
      t ∈ Formalism.UG.Ov D.host.F v := fun t => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨t, h⟩, rfl⟩⟩
  have hB' := hB fun j => π (y j)
  simp only [hR] at hB'
  rw [← hB']
  constructor
  · intro h
    have := hto _ h
    simpa only [RingHom.map_mul, hπε, one_mul] using this
  · intro h
    have hg : ∀ j, (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] V.frame.repr (x j) i) ∈ LamHat V :=
      fun j => AddSubgroup.subset_closure
        ⟨1, fun w => by rw [map_one]; exact one_mem _, fun i => V.frame.repr (x j) i, by
          show ∑ i, V.frame.repr (x j) i • V.frame i ∈ V.L0
          rw [V.frame.sum_repr]
          exact hxL j, rfl⟩
    have := section_mem (v.adicCompletionIntegers D.host.F) π (fun a => finPart D (s a)) (finPart D e)
      (intAE D) (LamHat V) h1 h2 (fun x hx => (h3 x).2 hx) h4 _ hg (fun j => π (y j)) h
    simpa only [h2] using this

end GlobalTheory.SplitLatBasis
