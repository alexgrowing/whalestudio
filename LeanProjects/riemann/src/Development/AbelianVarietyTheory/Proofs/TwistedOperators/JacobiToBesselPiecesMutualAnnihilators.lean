import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProof
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.DualParts
open GlobalTheory.MixModel.HypDec

variable {D : D7}

theorem smul_mem_latV {S : HSp D} {L L' : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} {c : D.host.E}
    (hc : ∀ x ∈ L, c • x ∈ L') {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] c : AE D) • y ∈ latV S L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, c • x, hc x hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem mem_idLat_of {n : ℕ} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {s : D.host.E} (hs : s ∈ I) {x : Fin n → D.host.E} (hx : x ∈ Λ) : s • x ∈ idLat I Λ :=
  Submodule.subset_span ⟨s, hs, x, hx, rfl⟩

theorem gen_mem {S : HSp D} {L : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (M : Mx D S.rank S.rank)
    (h : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV S L P) {β : Af D.host.F} (hβi : β ∈ intAf D.host.F)
    (hβ : ∀ v, ¬ P v → evalV D.host.F v β = 0) {x : Fin S.rank → D.host.E} (hx : x ∈ idLat I L) :
    M *ᵥ (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) : AE D)) ∈ latV S (idLat I L) P := by
  have gsmul : ∀ (c : D.host.E) (x : Fin S.rank → D.host.E),
      (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * (c • x) i) : AE D)) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] c : AE D) • fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) : AE D) := by
    intro c x
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  let N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
    { carrier := {x | M *ᵥ (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) : AE D)) ∈ latV S (idLat I L) P}
      add_mem' := by
        intro x x' hx hx'
        have e : (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * (x + x') i) : AE D)) =
            (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) : AE D)) +
              fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i) : AE D) := by
          funext i; simp [TensorProduct.tmul_add]
        change M *ᵥ _ ∈ latV S (idLat I L) P
        rw [e, Matrix.mulVec_add]; exact add_mem hx hx'
      zero_mem' := by
        have e : (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * (0 : Fin S.rank → D.host.E) i) : AE D)) = 0 := by
          funext i; simp
        change M *ᵥ _ ∈ latV S (idLat I L) P
        rw [e, Matrix.mulVec_zero]; exact zero_mem _
      smul_mem' := by
        intro c x hx
        have e : c • x = (algebraMap (𝓞 D.host.E) D.host.E c) • x := (algebraMap_smul D.host.E c x).symm
        change M *ᵥ _ ∈ latV S (idLat I L) P
        rw [e, gsmul, Matrix.mulVec_smul]
        exact smul_mem_latV (fun z hz => by rw [algebraMap_smul]; exact (idLat I L).smul_mem c hz) hx }
  have key : idLat I L ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, x₀, hx₀, rfl⟩
    change M *ᵥ _ ∈ latV S (idLat I L) P
    rw [gsmul, Matrix.mulVec_smul]
    exact smul_mem_latV (fun x hx => mem_idLat_of hs hx)
      (h _ (AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x₀, hx₀, rfl⟩))
  exact key hx
theorem mulVec_latV_idLat {S : HSp D} {L : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (M : Mx D S.rank S.rank)
    (h : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV S L P) {y : Fin S.rank → AE D} (hy : y ∈ latV S (idLat I L) P) :
    M *ᵥ y ∈ latV S (idLat I L) P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact gen_mem I M h hβi hβ hx
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem mulVec_eq_sum_colMul {m n : ℕ} (j : Mx D m n) (z : Fin n → AE D) : j *ᵥ z = ∑ i, GlobalTheory.FinPl.colMul j i (z i) := by
  funext k
  simp [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul, Finset.sum_apply, mul_comm]

section Mono

variable {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L : Lat S} {L₀ : Lat S₀} {v : GlobalTheory.FinPl.Pl D}

theorem projX_mem (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    (d.jX * d.pX) *ᵥ y ∈ latV S L (· = v) := by
  rw [← Matrix.mulVec_mulVec, mulVec_eq_sum_colMul]
  exact sum_mem fun i _ => ((h y).1 hy).1 i

theorem projY_mem (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    (d.jY * d.pY) *ᵥ y ∈ latV S L (· = v) := by
  rw [← Matrix.mulVec_mulVec, mulVec_eq_sum_colMul]
  exact sum_mem fun i _ => ((h y).1 hy).2.1 i

theorem witt_projCore_mem_split_lattice_completion (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    (d.j0 * d.p0) *ᵥ y ∈ latV S L (· = v) := by
  rw [← Matrix.mulVec_mulVec]
  exact GlobalTheory.FinPl.FlatVacuum.wittCoreInclusion_mulVec_mem_latticeCompletionAtPlace h (GlobalTheory.FinPl.FlatVacuum.p0_mem h hy)

end Mono

theorem mxAt_mul {P : GlobalTheory.FinPl.Pl D → Prop} {k l m n : ℕ} (A : Mx D k l) (B : Mx D m n) {x : Mx D l m}
    (hx : MxAt P x) : MxAt P (A * x * B) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l k))

theorem mul_mem_latO {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    {P : GlobalTheory.FinPl.Pl D → Prop} (A : Mx D T.rank T.rank) (B : Mx D S.rank S.rank)
    (hA : ∀ y ∈ latV T LT P, A *ᵥ y ∈ latV T LT P) (hB : ∀ y ∈ latV S LS P, B *ᵥ y ∈ latV S LS P)
    {u : WO S T} (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) :
    HMul.hMul (HMul.hMul A u) B ∈ latO S T (LS : Set _) (LT : Set _) P := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT P u).1 hu
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT P _).2 ⟨mxAt_mul A B h1, fun y hy => ?_⟩
  show (A * u * B) *ᵥ y ∈ latA T LT P
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact GlobalTheory.FinPl.FlatVacuum.mulVec_latA A hA (h2 _ (hB y hy))

section Pair

variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)

theorem pairS_zero_left (T : HSp D) {k : ℕ} (y : Mx D T.rank k) : pairS T 0 y = 0 := by
  simp [pairS]

theorem hO_incX_eq (ξ : Mx D σ V₀.rank) (w : WO V₀ W) : hO V₀ W (dW.incX V₀ ξ) w = pairT V₀ ξ (dW.pY * w) := by
  rw [hO_eq_trace, pairT, pY_eq, adj_mul, adj_mul, adj_adj, adj_gA, incX_apply]
  simp only [Matrix.mul_assoc]

theorem hO_incY_eq (η : Mx D σ V₀.rank) (w : WO V₀ W) : hO V₀ W (dW.incY V₀ η) w = pairT V₀ η (dW.pX * w) := by
  rw [hO_eq_trace, pairT, pX_eq, adj_mul, adj_mul, adj_adj, adj_gA, incY_apply]
  simp only [Matrix.mul_assoc]

theorem hermitian_form_extension_first_inclusion (ξ : Mx D σ V₀.rank) (u : WO V W) :
    hO V W (dV.ext0 W (dW.incX V₀ ξ)) u = hO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ (dW.pY * (u * dV.j0))) := by
  have e1 : dV.ext0 W (dW.incX V₀ ξ) * dV.jX = 0 := by
    rw [matrixExtendByZero_apply, Matrix.mul_assoc, p0_jX, Matrix.mul_zero]
  have e2 : dV.ext0 W (dW.incX V₀ ξ) * dV.jY = 0 := by
    rw [matrixExtendByZero_apply, Matrix.mul_assoc, p0_jY, Matrix.mul_zero]
  have e3 : dV.ext0 W (dW.incX V₀ ξ) * dV.j0 = dW.incX V₀ ξ := by
    rw [matrixExtendByZero_apply, Matrix.mul_assoc, p0_j0, Matrix.mul_one]
  have f3 : dW.pY * dW.incY V₀ (dW.pY * (u * dV.j0)) = dW.pY * (u * dV.j0) := by
    rw [incY_apply, ← Matrix.mul_assoc, pY_jY, Matrix.one_mul]
  rw [dV.hO_coordS, e1, e2, e3, pairS_zero_left, pairS_zero_left, zero_add, add_zero, hO_incX_eq, hO_incX_eq, f3]

theorem hermitian_form_extension_second_inclusion (η : Mx D σ V₀.rank) (u : WO V W) :
    hO V W (dV.ext0 W (dW.incY V₀ η)) u = hO V₀ W (dW.incY V₀ η) (dW.incX V₀ (dW.pX * (u * dV.j0))) := by
  have e1 : dV.ext0 W (dW.incY V₀ η) * dV.jX = 0 := by
    rw [matrixExtendByZero_apply, Matrix.mul_assoc, p0_jX, Matrix.mul_zero]
  have e2 : dV.ext0 W (dW.incY V₀ η) * dV.jY = 0 := by
    rw [matrixExtendByZero_apply, Matrix.mul_assoc, p0_jY, Matrix.mul_zero]
  have e3 : dV.ext0 W (dW.incY V₀ η) * dV.j0 = dW.incY V₀ η := by
    rw [matrixExtendByZero_apply, Matrix.mul_assoc, p0_j0, Matrix.mul_one]
  have f3 : dW.pX * dW.incX V₀ (dW.pX * (u * dV.j0)) = dW.pX * (u * dV.j0) := by
    rw [incX_apply, ← Matrix.mul_assoc, pX_jX, Matrix.one_mul]
  rw [dV.hO_coordS, e1, e2, e3, pairS_zero_left, pairS_zero_left, zero_add, add_zero, hO_incY_eq, hO_incY_eq, f3]

theorem symplectic_form_extension_first_inclusion (ξ : Mx D σ V₀.rank) (u : WO V W) :
    symplO V W (dV.ext0 W (dW.incX V₀ ξ)) u = symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ (dW.pY * (u * dV.j0))) := by
  unfold symplO; rw [hermitian_form_extension_first_inclusion]

theorem symplectic_form_extension_second_inclusion (η : Mx D σ V₀.rank) (u : WO V W) :
    symplO V W (dV.ext0 W (dW.incY V₀ η)) u = symplO V₀ W (dW.incY V₀ η) (dW.incX V₀ (dW.pX * (u * dV.j0))) := by
  unfold symplO; rw [hermitian_form_extension_second_inclusion]

theorem extension_of_first_inclusion_eq (ξ : Mx D σ V₀.rank) : dV.ext0 W (dW.incX V₀ ξ) = dW.jX * ξ * dV.p0 := by
  rw [matrixExtendByZero_apply, incX_apply]

theorem extension_of_second_inclusion_eq (η : Mx D σ V₀.rank) : dV.ext0 W (dW.incY V₀ η) = dW.jY * η * dV.p0 := by
  rw [matrixExtendByZero_apply, incY_apply]

theorem second_projection_extension_inclusion (η : Mx D σ V₀.rank) : dW.pY * (dV.ext0 W (dW.incY V₀ η) * dV.j0) = η := by
  rw [extension_of_second_inclusion_eq, Matrix.mul_assoc, p0_j0, Matrix.mul_one, ← Matrix.mul_assoc, pY_jY, Matrix.one_mul]

theorem first_projection_extension_inclusion (ξ : Mx D σ V₀.rank) : dW.pX * (dV.ext0 W (dW.incX V₀ ξ) * dV.j0) = ξ := by
  rw [extension_of_first_inclusion_eq, Matrix.mul_assoc, p0_j0, Matrix.mul_one, ← Matrix.mul_assoc, pX_jX, Matrix.one_mul]

theorem psi_neg_eq_one (ψ : AddChar (AF D.host.F) ℂ) {x : AF D.host.F} (h : ψ x = 1) : ψ (-x) = 1 := by
  have e := ψ.map_add_eq_mul (-x) x
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at e
  exact e.symm

theorem dual_parts (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {LV : Lat V} {LW : Lat W}
    (hV : IsSelfDualC V LV) (hW : IsSelfDualC W LW)
    (hX : ∀ y ∈ latV W LW (fun _ => True), (dW.jX * dW.pX) *ᵥ y ∈ latV W LW (fun _ => True))
    (hY : ∀ y ∈ latV W LW (fun _ => True), (dW.jY * dW.pY) *ᵥ y ∈ latV W LW (fun _ => True))
    (h0 : ∀ y ∈ latV V LV (fun _ => True), (dV.j0 * dV.p0) *ᵥ y ∈ latV V LV (fun _ => True)) :
    (∀ ξ : Mx D σ V₀.rank, MxAt (fun _ => True) ξ →
      (dV.ext0 W (dW.incX V₀ ξ) ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True) ↔
        ∀ η : Mx D σ V₀.rank, dV.ext0 W (dW.incY V₀ η) ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True) →
          ψ (symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ η)) = 1)) ∧
    (∀ η : Mx D σ V₀.rank, MxAt (fun _ => True) η →
      (dV.ext0 W (dW.incY V₀ η) ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True) ↔
        ∀ ξ : Mx D σ V₀.rank, dV.ext0 W (dW.incX V₀ ξ) ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True) →
          ψ (symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ η)) = 1)) := by
  have ann := fun u (hu : MxAt (fun _ => True) u) =>
    GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ V W LV LW hV hW (fun _ => True) u hu
  have compY : ∀ u ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True),
      dV.ext0 W (dW.incY V₀ (dW.pY * (u * dV.j0))) ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True) := by
    intro u hu
    have e : dV.ext0 W (dW.incY V₀ (dW.pY * (u * dV.j0))) = dW.jY * dW.pY * u * (dV.j0 * dV.p0) := by
      rw [extension_of_second_inclusion_eq]; simp only [Matrix.mul_assoc]
    rw [e]
    exact mul_mem_latO hV hW _ _ hY h0 hu
  have compX : ∀ u ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True),
      dV.ext0 W (dW.incX V₀ (dW.pX * (u * dV.j0))) ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True) := by
    intro u hu
    have e : dV.ext0 W (dW.incX V₀ (dW.pX * (u * dV.j0))) = dW.jX * dW.pX * u * (dV.j0 * dV.p0) := by
      rw [extension_of_first_inclusion_eq]; simp only [Matrix.mul_assoc]
    rw [e]
    exact mul_mem_latO hV hW _ _ hX h0 hu
  refine ⟨fun ξ hξ => ?_, fun η hη => ?_⟩
  · have hM : MxAt (fun _ => True) (dV.ext0 W (dW.incX V₀ ξ)) := by
      rw [extension_of_first_inclusion_eq]; exact mxAt_mul _ _ hξ
    rw [ann _ hM]
    constructor
    · intro H η hη'
      have := H _ hη'
      rwa [symplectic_form_extension_first_inclusion, second_projection_extension_inclusion] at this
    · intro H u hu
      rw [symplectic_form_extension_first_inclusion]
      exact H _ (compY u hu)
  · have hM : MxAt (fun _ => True) (dV.ext0 W (dW.incY V₀ η)) := by
      rw [extension_of_second_inclusion_eq]; exact mxAt_mul _ _ hη
    rw [ann _ hM]
    constructor
    · intro H ξ hξ'
      have := H _ hξ'
      rw [symplectic_form_extension_second_inclusion, first_projection_extension_inclusion, Formalism.IndefR.Fin.symplO_swap] at this
      simpa using psi_neg_eq_one ψ this
    · intro H u hu
      rw [symplectic_form_extension_second_inclusion, Formalism.IndefR.Fin.symplO_swap]
      exact psi_neg_eq_one ψ (H _ (compX u hu))

end Pair

theorem pcFB_dual : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    (∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ (pcFB W F σ h h').B₁ ↔ ∀ η ∈ (pcFB W F σ h h').B₂,
      W.ψ (symplO _ _ ((F.dB σ h').incX _ ξ) ((F.dB σ h').incY _ η)) = 1)) ∧
    (∀ η, MxAt (fun _ => True) η → (η ∈ (pcFB W F σ h h').B₂ ↔ ∀ ξ ∈ (pcFB W F σ h h').B₁,
      W.ψ (symplO _ _ ((F.dB σ h').incX _ ξ) ((F.dB σ h').incY _ η)) = 1)) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h'
  have HI := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF
  have hWsd : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (idLat (shiftId G) (G.Λ (.grid (2 * σ + 2) 0))) :=
    (HI.1 (2 * σ + 2) (by omega)).2.2.2
  have hVsd : IsSelfDualC (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) :=
    (G.isV (X := .grid (2 * σ + 2 + 1) 0) ⟨by omega, by omega⟩
      (fun j hj => by have := (Node.grid.inj hj).1; omega)).sd
  have hΛ : Submodule.IsLattice D.host.E (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) ⟨by omega, by omega⟩
      (fun j hj => by have := (Node.grid.inj hj).1; omega)).sd.1
  have monoV := fun v => ((HI.2.1 (σ + 1) h).2.1 v).2
  have monoW := fun v => ((HI.2.1 σ h').2.1 v).1
  have h0 : ∀ y ∈ latV _ (G.Λ (.grid (2 * σ + 2 + 1) 0)) (fun _ => True),
      ((F.dJ (σ + 1) h).j0 * (F.dJ (σ + 1) h).p0) *ᵥ y ∈ latV _ (G.Λ (.grid (2 * σ + 2 + 1) 0)) (fun _ => True) :=
    fun y hy => GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hVsd.1 hVsd.1 _ (fun v _ z hz => witt_projCore_mem_split_lattice_completion (monoV v) hz) hy
  have hX : ∀ y ∈ latV _ (idLat (shiftId G) (G.Λ (.grid (2 * σ + 2) 0))) (fun _ => True),
      ((F.dB σ h').jX * (F.dB σ h').pX) *ᵥ y ∈ latV _ (idLat (shiftId G) (G.Λ (.grid (2 * σ + 2) 0))) (fun _ => True) :=
    fun y hy => mulVec_latV_idLat (shiftId G) _
      (fun z hz => GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hΛ hΛ _ (fun v _ z hz => projX_mem (monoW v) hz) hz) hy
  have hY : ∀ y ∈ latV _ (idLat (shiftId G) (G.Λ (.grid (2 * σ + 2) 0))) (fun _ => True),
      ((F.dB σ h').jY * (F.dB σ h').pY) *ᵥ y ∈ latV _ (idLat (shiftId G) (G.Λ (.grid (2 * σ + 2) 0))) (fun _ => True) :=
    fun y hy => mulVec_latV_idLat (shiftId G) _
      (fun z hz => GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hΛ hΛ _ (fun v _ z hz => projY_mem (monoW v) hz) hz) hy
  obtain ⟨H1, H2⟩ := dual_parts (F.dJ (σ + 1) h) (F.dB σ h') W.ψ W.ψ_std hVsd hWsd hX hY h0
  exact ⟨fun ξ hξ => H1 ξ hξ, fun η hη => H2 η hη⟩

end GlobalTheory.AscFin.DualParts
