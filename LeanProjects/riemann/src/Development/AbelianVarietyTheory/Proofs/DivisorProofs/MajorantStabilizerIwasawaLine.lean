import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers

noncomputable section

namespace GlobalTheory.KBridge

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def infT : AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)

variable (F E) in

def finT : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)

variable (F E) in

def ofInfT : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := (LinearMap.inl F (Ainf F) (Af F)).rTensor E

variable (F E) in

def ofFinT : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := (LinearMap.inr F (Ainf F) (Af F)).rTensor E

theorem decomp (z : AF F ⊗[F] E) : z = ofInfT F E (infT F E z) + ofFinT F E (finT F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add]
    conv_lhs => rw [hx, hy]
    abel
  | tmul a e =>
    change a ⊗ₜ[F] e = ((a.1, 0) : AF F) ⊗ₜ[F] e + ((0, a.2) : AF F) ⊗ₜ[F] e
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero _).symm (zero_add _).symm

theorem tmul_eq_smul_incV {n : ℕ} (a : AF F) (x : Fin n → E) : (fun i => a ⊗ₜ[F] x i) = a • incV F x := by
  funext i
  change a ⊗ₜ[F] x i = a • ((1 : AF F) ⊗ₜ[F] x i)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem infT_tmul (a : AF F) (e : E) : infT F E (a ⊗ₜ[F] e) = a.1 ⊗ₜ[F] e := rfl

theorem mem_latHat_iff {n : ℕ} (X : Spc F E n) (z : Fin n → AE F E) :
    z ∈ latHat X ↔ (∀ i, infT F E (z i) = 0) ∧
      (fun i => finT F E (z i)) ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)) := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hv, x, hx, rfl⟩ := hz
      have h0 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 ha
      rw [← tmul_eq_smul_incV]
      refine ⟨fun i => ?_, ?_⟩
      · rw [infT_tmul, h0, TensorProduct.zero_tmul]
      · exact AddSubgroup.subset_closure ⟨a.2, fun v => hv v, x, hx, rfl⟩
    | zero =>
      refine ⟨fun i => map_zero _, ?_⟩
      have e : (fun i => finT F E ((0 : Fin n → AE F E) i)) = 0 := funext fun i => map_zero _
      rw [e]; exact zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨fun i => ?_, ?_⟩
      · rw [Pi.add_apply, map_add, hy.1 i, hz.1 i, add_zero]
      · have e : (fun i => finT F E ((y + z) i)) = (fun i => finT F E (y i)) + fun i => finT F E (z i) :=
          funext fun i => map_add _ _ _
        rw [e]; exact add_mem hy.2 hz.2
    | neg y _ hy =>
      refine ⟨fun i => ?_, ?_⟩
      · rw [Pi.neg_apply, map_neg, hy.1 i, neg_zero]
      · have e : (fun i => finT F E ((-y) i)) = -fun i => finT F E (y i) := funext fun i => map_neg _ _
        rw [e]; exact neg_mem hy.2
  · rintro ⟨hi, hf⟩
    have e : z = fun i => ofFinT F E (finT F E (z i)) := funext fun i => by
      conv_lhs => rw [decomp (z i)]
      rw [hi i, map_zero, zero_add]
    rw [e]
    suffices H : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)), (fun i => ofFinT F E (y i)) ∈ latHat X from H _ hf
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨show AF F from (0, a), map_zero _, fun v => ha v, x, hx, tmul_eq_smul_incV (show AF F from (0, a)) x⟩
    | zero =>
      have e : (fun i => ofFinT F E ((0 : Fin n → Af F ⊗[F] E) i)) = 0 := funext fun i => map_zero _
      rw [e]; exact zero_mem _
    | add y y' _ _ hy hy' =>
      have e : (fun i => ofFinT F E ((y + y') i)) = (fun i => ofFinT F E (y i)) + fun i => ofFinT F E (y' i) :=
        funext fun i => map_add _ _ _
      rw [e]; exact add_mem hy hy'
    | neg y _ hy =>
      have e : (fun i => ofFinT F E ((-y) i)) = -fun i => ofFinT F E (y i) := funext fun i => map_neg _ _
      rw [e]; exact neg_mem hy

theorem mulVec_mem_latHat {n : ℕ} (σ : E →ₐ[F] E) (X : Spc F E n) (hfg : X.L.FG) {k : GAd σ X.Jᵀ}
    (hk : k ∈ levelOpen σ X.Jᵀ X.L) {z : Fin n → AE F E} (hz : z ∈ latHat X) :
    (matHom (AF F) σ X.Jᵀ k).1 *ᵥ z ∈ latHat X := by
  rw [mem_latHat_iff] at hz ⊢
  obtain ⟨hi, hf⟩ := hz
  refine ⟨fun i => ?_, ?_⟩
  · have e : ((infT F E).toRingHom ∘ z) = 0 := funext fun j => hi j
    refine (RingHom.map_mulVec (infT F E).toRingHom (matHom (AF F) σ X.Jᵀ k).1 z i).trans ?_
    rw [e, Matrix.mulVec_zero]
    rfl
  · have e : (fun i => finT F E (((matHom (AF F) σ X.Jᵀ k).1 *ᵥ z) i)) =
        Formalism.MainNotions.StandardLattice.finMat σ X.Jᵀ k *ᵥ fun i => finT F E (z i) :=
      funext fun i => RingHom.map_mulVec (finT F E).toRingHom _ _ i
    rw [e]
    exact ((mem_levelOpen_iff_latHat σ X.Jᵀ hfg k).1 hk _).1 hf

theorem ofGAd_mem_stabK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), X.L.IsLattice E → ∀ g : GAd σ X.Jᵀ,
    (∀ w, Commute ((matHom w.Completion σ X.Jᵀ (projArch σ X.Jᵀ w g)).1.map (infEmb (B.emb w))) (X.θ w)) →
    (∀ v, proj σ X.Jᵀ v g ∈ stabLoc σ X.Jᵀ X.L v) → GlobalTheory.IwLine.ofGAd σ X.J g ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X := by
  intro F E _ _ _ _ _ σ B n X hL g h1 h2
  have hfg : X.L.FG := hL.fg
  have hg : g ∈ levelOpen σ X.Jᵀ X.L := mem_levelOpen.2 h2
  refine ⟨fun w => h1 w, fun z hz => ⟨?_, ?_⟩⟩
  · rw [GlobalTheory.IwLine.mat_ofGAd]
    exact mulVec_mem_latHat σ X hfg hg hz
  · rw [← map_inv, GlobalTheory.IwLine.mat_ofGAd]
    exact mulVec_mem_latHat σ X hfg (inv_mem hg) hz

end GlobalTheory.KBridge
