import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine

noncomputable section

namespace GlobalTheory.KBridgeConv

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.KBridge GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finT_ofFinT (a : Af F ⊗[F] E) : finT F E (ofFinT F E a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a e => rfl

theorem infT_ofFinT (a : Af F ⊗[F] E) : infT F E (ofFinT F E a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul a e => exact TensorProduct.zero_tmul _ _

theorem ofFinT_mem_latHat {n : ℕ} (X : Spc F E n) {y : Fin n → Af F ⊗[F] E}
    (hy : y ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E))) : (fun i => ofFinT F E (y i)) ∈ latHat X := by
  rw [KBridge.mem_latHat_iff]
  refine ⟨fun i => infT_ofFinT _, ?_⟩
  have e : (fun i => finT F E (ofFinT F E (y i))) = y := funext fun i => finT_ofFinT _
  rw [e]; exact hy

theorem local_of_ofGAd_mem_stabK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsLattice E →
    ∀ g : GAd σ X.Jᵀ, GlobalTheory.IwLine.ofGAd σ X.J g ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X →
      (∀ w, Commute ((matHom w.Completion σ X.Jᵀ (projArch σ X.Jᵀ w g)).1.map (infEmb (B.emb w))) (X.θ w)) ∧
      ∀ v, proj σ X.Jᵀ v g ∈ stabLoc σ X.Jᵀ X.L v := by
  intro F E _ _ _ _ _ σ B n X hL g hK
  obtain ⟨h1, h2⟩ := hK
  refine ⟨fun w => h1 w, ?_⟩
  have hfg : X.L.FG := hL.fg
  have hMM : (matHom (AF F) σ X.Jᵀ g⁻¹).1 * (matHom (AF F) σ X.Jᵀ g).1 = 1 := by
    rw [map_inv]; exact Units.inv_mul _
  have hfin : ∀ z : Fin n → AE F E, (fun i => finT F E (((matHom (AF F) σ X.Jᵀ g).1 *ᵥ z) i)) = Formalism.MainNotions.StandardLattice.finMat σ X.Jᵀ g *ᵥ fun i => finT F E (z i) :=
    fun z => funext fun i => RingHom.map_mulVec (finT F E).toRingHom _ _ i
  have hinf : ∀ z : Fin n → AE F E, (∀ i, infT F E (z i) = 0) → ∀ i, infT F E (((matHom (AF F) σ X.Jᵀ g).1 *ᵥ z) i) = 0 := by
    intro z hz i
    have e : ((infT F E).toRingHom ∘ z) = 0 := funext fun j => hz j
    refine (RingHom.map_mulVec (infT F E).toRingHom (matHom (AF F) σ X.Jᵀ g).1 z i).trans ?_
    rw [e, Matrix.mulVec_zero]
    rfl
  have hg : g ∈ levelOpen σ X.Jᵀ X.L := by
    refine (mem_levelOpen_iff_latHat σ X.Jᵀ hfg g).2 fun y => ?_
    let z : Fin n → AE F E := fun i => ofFinT F E (y i)
    have hzy : (fun i => finT F E (z i)) = y := funext fun i => finT_ofFinT _
    constructor
    · intro hy
      have hzL : z ∈ latHat X := ofFinT_mem_latHat X hy
      have := (h2 z hzL).1
      rw [GlobalTheory.IwLine.mat_ofGAd] at this
      have h := ((KBridge.mem_latHat_iff X _).1 this).2
      rw [hfin, hzy] at h
      exact h
    · intro hy
      have hw : (matHom (AF F) σ X.Jᵀ g).1 *ᵥ z ∈ latHat X := by
        rw [KBridge.mem_latHat_iff]
        refine ⟨hinf z (fun i => infT_ofFinT _), ?_⟩
        rw [hfin, hzy]; exact hy
      have := (h2 _ hw).2
      rw [← map_inv, GlobalTheory.IwLine.mat_ofGAd, Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec] at this
      have h := ((KBridge.mem_latHat_iff X _).1 this).2
      rw [hzy] at h
      exact h
  exact mem_levelOpen.1 hg

end GlobalTheory.KBridgeConv
