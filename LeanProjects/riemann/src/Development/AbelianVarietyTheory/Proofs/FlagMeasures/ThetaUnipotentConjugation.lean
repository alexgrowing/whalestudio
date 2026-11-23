import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisCoord

open GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices (gramA gramInvA)
open Matrix

variable {D : D7}

theorem dot_cT {R : Type} [CommRing R] (σ : R →+* R) {n m : ℕ} (P : Matrix (Fin n) (Fin m) R) (y : Fin m → R)
    (v : Fin n → R) : (fun i => σ ((P *ᵥ y) i)) ⬝ᵥ v = (fun i => σ (y i)) ⬝ᵥ (Formalism.UG.cT σ P *ᵥ v) := by
  rw [← BesselChar.mulVec_map, Formalism.UG.cT, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem cancel_gen {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} {H H' J J' : Matrix (Fin n) (Fin n) R}
    (hH : H * H' = 1) (hJ : J' * J = 1) {v w : Fin n → R}
    (h : Formalism.UG.cT σ H *ᵥ (J *ᵥ v) = Formalism.UG.cT σ H *ᵥ (J *ᵥ w)) : v = w := by
  have h3 : J' * Formalism.UG.cT σ H' * Formalism.UG.cT σ H * J = 1 := by
    rw [Matrix.mul_assoc J', ← Formalism.UG.cT_mul, hH, Formalism.UG.cT_one, Matrix.mul_one, hJ]
  have h4 : ∀ u, (J' * Formalism.UG.cT σ H') *ᵥ (Formalism.UG.cT σ H *ᵥ (J *ᵥ u)) = u := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3, Matrix.one_mulVec]
  rw [← h4 v, h, h4]

theorem hA_dot (B : HSp D) (x y : Fin B.rank → AE D) : hA B x y = (fun i => cA D (y i)) ⬝ᵥ (gramA B *ᵥ x) := by
  simp only [hA, dotProduct, Matrix.mulVec, gramA, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem mt_unitary (B : HSp D) (g : GA D B) :
    Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt B g) * gramA B * Formalism.L2.Theta.mt B g = gramA B := g.2

theorem hA_mt (B : HSp D) (g : GA D B) (x y : Fin B.rank → AE D) :
    hA B (Formalism.L2.Theta.mt B g *ᵥ x) (Formalism.L2.Theta.mt B g *ᵥ y) = hA B x y := by
  rw [hA_dot, hA_dot, dot_cT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mt_unitary]

theorem exists_rat {B : HSp D} {γ : GA D B} (hγ : γ ∈ GQ B) (x : B.V) : ∃ x', actV B γ x = vecA B x' := by
  obtain ⟨γ', -, h⟩ := hγ
  have hm : Formalism.L2.Theta.mt B γ = (γ' : Matrix (Fin B.rank) (Fin B.rank) D.host.E).map (incA D) :=
    (congrArg Units.val h).symm
  obtain ⟨v, hv⟩ := BesselCompare.co_surj B
    ((γ' : Matrix (Fin B.rank) (Fin B.rank) D.host.E) *ᵥ BesselCompare.co B x)
  refine ⟨v, ?_⟩
  have := BesselChar.mulVec_map (incA D) (γ' : Matrix (Fin B.rank) (Fin B.rank) D.host.E) (BesselCompare.co B x)
  rw [← hv] at this
  unfold actV
  rw [hm]
  exact this

theorem exists_rat_hA {B : HSp D} {γ : GA D B} (hγ : γ ∈ GQ B) (x y : B.V) :
    ∃ s, hA B (actV B γ x) (vecA B y) = incA D s := by
  obtain ⟨x', h⟩ := exists_rat hγ x
  exact ⟨_, by rw [h, BesselCompare.hA_vec]⟩

theorem continuous_hA (B : HSp D) (x y : B.V) : Continuous fun n : GA D B => hA B (actV B n x) (vecA B y) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hm0 : Continuous (fun k : GA D B => Formalism.L2.Theta.mt B k) := Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun n : GA D B => actV B n x := hm0.matrix_mulVec continuous_const
  unfold hA
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).comp h1)

variable {L A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem chr_rat (d : FJDat L A B ι) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {γ : GA D B}
    (hγ : γ ∈ GQ B) : d.chr ψ γ = 1 := by
  choose s hs using exists_rat_hA hγ
  unfold FJDat.chr
  simp only [hs, ← map_mul, ← map_sum]
  rw [BesselChar.trace_incA]
  exact hψ.2.2.1 _

theorem jac_rat (d : FJDat L A B ι) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {γ : GA D B}
    (hγ : γ ∈ GQ B) {f : WA L A → ℂ} (hf : IsThetaFun ψ L A f) : d.jac ψ γ f 0 = f 0 := by
  choose s hs using exists_rat_hA hγ
  have h1 : ψ (cenCo L d.c (d.tCo γ)) = 1 := by
    unfold cenCo FJDat.tCo
    rw [hs, ← map_mul, BesselChar.trace_incA, ← map_mul]
    exact hψ.2.2.1 _
  have h2 : d.aCo γ = fun i => incA D ((A.gram⁻¹ *ᵥ fun k => s d.fTop (ι (A.frame k))) i) := by
    unfold FJDat.aCo gramInvA
    simp only [hs]
    exact BesselChar.mulVec_map _ _ _
  have h3 : tPt L A d.c (d.aCo γ) =
      ratW L A (Matrix.of fun _ i => -(d.c * (A.gram⁻¹ *ᵥ fun k => s d.fTop (ι (A.frame k))) i)) := by
    rw [h2]
    ext i k
    change -(incA D _ * incA D _) = incA D (-(_ * _))
    rw [map_neg, map_mul]
  have h4 : ∀ w : WA L A, symplH L A w 0 = 0 := fun w => by
    have := DualPairCheck.symplH_add_right L A w 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have h5 := hf.quasi (Matrix.of fun _ i => -(d.c * (A.gram⁻¹ *ᵥ fun k => s d.fTop (ι (A.frame k))) i)) 0
  rw [h4, neg_zero, AddChar.map_zero_eq_one, one_mul, add_zero, ← h3] at h5
  have h6 := d.theta_eq ψ (fun _ => f) γ 1
  rw [h1, one_mul, h5] at h6
  exact h6

theorem continuous_chr (d : FJDat L A B ι) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    Continuous (d.chr ψ) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact hψ.1.comp (ht.comp (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_hA B _ _)))

theorem continuous_aCo (d : FJDat L A B ι) : Continuous d.aCo := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact (continuous_const (y := gramInvA A)).matrix_mulVec (continuous_pi fun i => continuous_hA B _ _)

theorem fix_of_perp {g : GA D B} {h : GA D A} (hg : EmbRel B A ι g h) {v : B.V} (hv : ∀ x, B.hD v (ι x) = 0) :
    Formalism.L2.Theta.mt B g *ᵥ vecA B v = vecA B v := by
  refine hg.2 (BesselCompare.co B v) ?_
  funext i
  rw [BesselCompare.frameMat_eq, BesselCompare.cT_mulVec]
  exact hv _

theorem actV_conj {g : GA D B} (n : GA D B) {v : B.V} (hv : Formalism.L2.Theta.mt B g *ᵥ vecA B v = vecA B v) :
    actV B (g * n * g⁻¹) v = Formalism.L2.Theta.mt B g *ᵥ actV B n v := by
  unfold actV
  rw [BesselChar.mt_mul, BesselChar.mt_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    BesselChar.inv_fix_vec (BesselChar.mt_inv_mul B g) hv]

theorem hA_conj {g : GA D B} (n : GA D B) {v w : B.V} (hv : Formalism.L2.Theta.mt B g *ᵥ vecA B v = vecA B v)
    (hw : Formalism.L2.Theta.mt B g *ᵥ vecA B w = vecA B w) :
    hA B (actV B (g * n * g⁻¹) v) (vecA B w) = hA B (actV B n v) (vecA B w) := by
  rw [actV_conj n hv]
  conv_lhs => rw [← hw]
  exact hA_mt B g _ _

theorem gram_aCo (d : FJDat L A B ι) (n : GA D B) : gramA A *ᵥ d.aCo n =
    Formalism.UG.cT (cA D) ((frameMat B A ι).map (incA D)) *ᵥ (gramA B *ᵥ actV B n d.fTop) := by
  unfold FJDat.aCo
  rw [Matrix.mulVec_mulVec, WeilTieCompare.gram_mul_inv, Matrix.one_mulVec, BesselCompare.frameMat_eq]
  funext i
  rw [hA_dot]
  rfl

theorem aCo_conj (d : FJDat L A B ι) {g : GA D B} {h : GA D A} (hg : EmbRel B A ι g h) (n : GA D B) :
    d.aCo (g * n * g⁻¹) = Formalism.L2.Theta.mt A h *ᵥ d.aCo n := by
  have hf := fix_of_perp hg fun x => d.hD_fTop _ fun i => d.fA i x
  have h1 : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt B g * (frameMat B A ι).map (incA D)) =
      Formalism.UG.cT (cA D) ((frameMat B A ι).map (incA D) * Formalism.L2.Theta.mt A h) := congrArg _ hg.1
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul] at h1
  have h2 : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt A h) *ᵥ (gramA A *ᵥ d.aCo (g * n * g⁻¹)) =
      Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt A h) *ᵥ (gramA A *ᵥ (Formalism.L2.Theta.mt A h *ᵥ d.aCo n)) := by
    rw [gram_aCo, Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, actV_conj n hf,
      Matrix.mulVec_mulVec _ _ (gramA B), Matrix.mulVec_mulVec _ _ (Formalism.L2.Theta.mt B g), mt_unitary, ← gram_aCo,
      Matrix.mulVec_mulVec _ _ (gramA A), Matrix.mulVec_mulVec _ _ (Formalism.L2.Theta.mt A h), mt_unitary]
  exact cancel_gen (cA D) (BesselChar.mt_mul_inv A h) (WeilTieCompare.inv_mul_gram A) h2

theorem conj_mem (d : FJDat L A B ι) {g : GA D B} {h : GA D A} (hg : EmbRel B A ι g h) {n : GA D B} (hn : n ∈ d.N) :
    g * n * g⁻¹ ∈ d.N := by
  have he : HMul.hMul (Formalism.L2.Theta.mt B g) (d.eM.map (incA D)) = d.eM.map (incA D) := by
    ext k i
    exact congr_fun (fix_of_perp hg (d.eA i)) k
  have he' := BesselChar.inv_fix_cols (BesselChar.mt_inv_mul B g) he
  rw [FJDat.N, BesselChar.mem_NFlag_iff B d.eM d.isIsoSub.1] at hn ⊢
  rw [BesselChar.mt_mul, BesselChar.mt_mul]
  exact hn.conj he he' (BesselChar.mt_mul_inv B g) (BesselChar.perp_fixed d.eM g⁻¹ he')

theorem coords_laws : ∀ (D : D7) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), (∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → (∀ γ ∈ GQ B, d.chr ψ γ = 1 ∧ ∀ f, IsThetaFun ψ L A f → d.jac ψ γ f 0 = f 0) ∧ Continuous (d.chr ψ)) ∧ Continuous d.aCo ∧ Continuous d.tCo ∧ ∀ g h, EmbRel B A ι g h → ∀ n ∈ d.N, g * n * g⁻¹ ∈ d.N ∧ d.aCo (g * n * g⁻¹) = (Formalism.L2.Theta.mt A h).mulVec (d.aCo n) ∧ d.tCo (g * n * g⁻¹) = d.tCo n ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, d.chr ψ (g * n * g⁻¹) = d.chr ψ n := by
  intro D L A B ι d
  refine ⟨fun ψ hψ => ⟨fun γ hγ => ⟨chr_rat d hψ hγ, fun f hf => jac_rat d hψ hγ hf⟩, continuous_chr d hψ⟩,
    continuous_aCo d, continuous_hA B _ _, fun g h hg n hn => ⟨conj_mem d hg hn, aCo_conj d hg n, ?_, fun ψ => ?_⟩⟩
  · have hf := fix_of_perp hg fun x => d.hD_fTop _ fun i => d.fA i x
    exact hA_conj n hf hf
  · unfold FJDat.chr
    simp only [hA_conj n (fix_of_perp hg (d.eA _)) (fix_of_perp hg (d.fA _))]

end GlobalTheory.HeisCoord

end
