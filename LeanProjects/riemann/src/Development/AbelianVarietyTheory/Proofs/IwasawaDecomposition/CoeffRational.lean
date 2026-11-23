import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActEEqOfConjRelated

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffRational

theorem conj_closure {G : Type} [Group G] (S : Set G) (γ : G) (h : ∀ n ∈ S, γ * n * γ⁻¹ ∈ S) :
    ∀ n ∈ Subgroup.closure S, γ * n * γ⁻¹ ∈ Subgroup.closure S := by
  have : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj γ).toMonoidHom :=
    (Subgroup.closure_le _).2 fun n hn => Subgroup.subset_closure (h n hn)
  exact fun n hn => this hn

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjN (N : Subgroup G) (γ : G) (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ ∈ N) : N ≃ₜ* N where
  toFun n := ⟨γ⁻¹ * n * γ, h2 n n.2⟩
  invFun n := ⟨γ * n * γ⁻¹, h1 n n.2⟩
  left_inv n := Subtype.ext (by simp [mul_assoc])
  right_inv n := Subtype.ext (by simp [mul_assoc])
  map_mul' m n := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

theorem exists_pair [MeasurableSpace G] [BorelSpace G] (N Q : Subgroup G) (γ : G) (hγ : γ ∈ Q)
    (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ ∈ N) (ν : Measure N) (𝓝 : Set N)
    (hν : ν.IsHaarMeasure) (hF : IsFundamentalDomain (Q.subgroupOf N) 𝓝 ν) (hv : ν 𝓝 = 1) :
    ∃ (ν' : Measure N) (𝓝' : Set N), (ν'.IsHaarMeasure ∧ IsFundamentalDomain (Q.subgroupOf N) 𝓝' ν' ∧ ν' 𝓝' = 1) ∧
      ∀ f : G → ℂ, ∫ n in 𝓝', f n ∂ν' = ∫ n in 𝓝, f (γ⁻¹ * n * γ) ∂ν := by
  let c := conjN N γ h1 h2
  let cm : N ≃ᵐ N := c.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving cm ν (ν.map cm) := ⟨cm.measurable, rfl⟩
  have hpre : cm ⁻¹' (cm.symm ⁻¹' 𝓝) = 𝓝 := by
    ext x; simp
  refine ⟨ν.map cm, cm.symm ⁻¹' 𝓝, ⟨c.isHaarMeasure_map ν, ?_, ?_⟩, fun f => ?_⟩
  · let e : Q.subgroupOf N → Q.subgroupOf N := fun q =>
      ⟨c q.1, Subgroup.mem_subgroupOf.2 (Q.mul_mem (Q.mul_mem (Q.inv_mem hγ) (Subgroup.mem_subgroupOf.1 q.2)) hγ)⟩
    have he : Function.Bijective e := by
      refine ⟨fun a b h => Subtype.ext (c.injective (congrArg Subtype.val h)), fun q => ?_⟩
      exact ⟨⟨c.symm q.1, Subgroup.mem_subgroupOf.2
        (Q.mul_mem (Q.mul_mem hγ (Subgroup.mem_subgroupOf.1 q.2)) (Q.inv_mem hγ))⟩,
        Subtype.ext (c.apply_symm_apply _)⟩
    refine hF.preimage_of_equiv (hmp.symm cm).quasiMeasurePreserving he fun q x => ?_
    show c.symm (c q.1 * x) = q.1 * c.symm x
    rw [map_mul, c.symm_apply_apply]
  · rw [cm.map_apply, hpre, hv]
  · rw [setIntegral_map_equiv, hpre]
    rfl

end General

section Conj

open GlobalTheory.BesselCompare

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem emb_fix {γ : GA D B} {h : GA D A} (hγ : EmbRel B A ι γ h) {v : B.V} (hv : ∀ x, B.hD v (ι x) = 0) :
    (mt B γ).mulVec (vecA B v) = vecA B v :=
  hγ.2 (co B v) (by funext i; rw [frameMat_eq, cT_mulVec]; exact hv _)

theorem emb_iA {γ : GA D B} {h : GA D A} (hγ : EmbRel B A ι γ h) (t : Fin A.rank → AE D) :
    (mt B γ).mulVec (iA ι t) = iA ι ((mt A h).mulVec t) := by
  unfold iA
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun M => Matrix.mulVec M t) hγ.1

theorem vecA_add (v w : B.V) : vecA B (v + w) = vecA B v + vecA B w := by
  funext k; simp [vecA]

theorem vecA_emb (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  funext k
  have h1 := RingHom.map_mulVec (incA D) (frameMat B A ι) (A.frame.repr a) k
  rw [frameMat, LinearMap.toMatrix_mulVec_repr] at h1
  exact h1

theorem emb_move (hι : HSpace.IsIsomEmb A B ι) {γ : GA D B} {h : GA D A} (hγ : EmbRel B A ι γ h) (x : B.V) :
    ∃ t, (mt B γ).mulVec (vecA B x) = vecA B x + iA ι t := by
  obtain ⟨a, ha⟩ := exists_rep A ((B.hT x).comp ι)
  have h1 : ∀ y, B.hD (x - ι a) (ι y) = 0 := fun y => hD_swap_zero (by
    show B.hT (x - ι a) (ι y) = 0
    rw [map_sub, LinearMap.sub_apply, hι a y, ha, LinearMap.comp_apply, sub_self])
  have h2 : vecA B x = vecA B (x - ι a) + iA ι (vecA A a) := by
    rw [← vecA_emb, ← vecA_add, sub_add_cancel]
  refine ⟨(mt A h).mulVec (vecA A a) + -vecA A a, ?_⟩
  rw [h2, Matrix.mulVec_add, emb_fix hγ h1, emb_iA hγ, iA_add, iA_neg]
  abel

set_option maxHeartbeats 1000000 in
theorem conj_NSet (d : BesselDatum A B ι) {γ : GA D B} {h h' : GA D A} (hγ : EmbRel B A ι γ h)
    (hγ' : EmbRel B A ι γ⁻¹ h') {n : GA D B} (hn : n ∈ d.NSet) : γ * n * γ⁻¹ ∈ d.NSet := by
  have hsum : ∀ c : Fin d.ρ → AE D, (mt B γ).mulVec (∑ l, c l • vecA B (d.e l)) = ∑ l, c l • vecA B (d.e l) := by
    intro c
    rw [← Matrix.mulVecLin_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, Matrix.mulVecLin_apply, emb_fix hγ (d.eA l)]
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc, e⟩ := hn.1 i
    refine ⟨c, hc, ?_⟩
    unfold actV at e ⊢
    rw [mulVec_mul, mulVec_mul, emb_fix hγ' (d.eA i), e, Matrix.mulVec_add, emb_fix hγ (d.eA i), hsum]
  · obtain ⟨t, ht⟩ := emb_move d.isom hγ' x
    obtain ⟨c, e⟩ := hn.2 x hx
    choose a ha using fun k => hn.2 (ι (A.frame k)) fun i => hD_swap_zero (d.eA i _)
    unfold actV at e ha ⊢
    have e2 : (mt B n).mulVec (iA ι t) = iA ι t + ∑ l, (∑ k, t k * a k l) • vecA B (d.e l) := by
      rw [iA, frameMat_eq, eMat_mulVec, ← Matrix.mulVecLin_apply, map_sum]
      simp only [map_smul, Matrix.mulVecLin_apply, ha, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
        Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
    refine ⟨fun l => c l + ∑ k, t k * a k l, ?_⟩
    have e3 : (mt B n).mulVec ((mt B γ⁻¹).mulVec (vecA B x)) =
        (mt B γ⁻¹).mulVec (vecA B x) + ∑ l, (c l + ∑ k, t k * a k l) • vecA B (d.e l) := by
      rw [ht, Matrix.mulVec_add, e, e2]
      simp only [add_smul, Finset.sum_add_distrib]
      abel
    rw [mulVec_mul, mulVec_mul, e3, Matrix.mulVec_add]
    exact congrArg₂ (· + ·) (mulVec_cancel_inv γ (vecA B x)) (hsum fun l => c l + ∑ k, t k * a k l)

theorem conj_N (d : BesselDatum A B ι) {γ : GA D B} {h h' : GA D A} (hγ : EmbRel B A ι γ h)
    (hγ' : EmbRel B A ι γ⁻¹ h') : ∀ n ∈ d.N, γ * n * γ⁻¹ ∈ d.N := by
  have h1 : ∀ n ∈ d.NSet, γ * n * γ⁻¹ ∈ d.NSet := fun n hn => conj_NSet d hγ hγ' hn
  have h2 := conj_closure (G := GA D B) d.NSet γ h1
  unfold BesselDatum.N
  exact h2

theorem psiN_conj (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) {γ : GA D B} {h : GA D A}
    (hγ : EmbRel B A ι γ h) (n : GA D B) : d.psiN ψ (γ⁻¹ * n * γ) = d.psiN ψ n := by
  unfold BesselDatum.psiN BesselDatum.simpleSum actV
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_mul, mulVec_mul, emb_fix hγ (besselDatum_auxiliaryVector_orthogonal_image d _), hA_mt_left, inv_inv, emb_fix hγ (d.fA i)]

end Conj

theorem coeff_rational : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ F : GA D B → ℂ, (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → ∀ γ h, EmbRel B A ι γ h → γ ∈ GQ B → ∀ g, d.coeff ψ ν 𝓝 F (γ * g) = d.coeff ψ ν 𝓝 F g := by
  intro D A B ι d ψ hψ F hF ν 𝓝 hν γ h hγ hQ g
  haveI : BorelSpace (GA D B) := ⟨rfl⟩
  haveI : IsTopologicalGroup (GA D B) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B).2.2.2.2.1
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι d.isom
  have hγ' : EmbRel B A ι γ⁻¹ h⁻¹ := by
    rw [hs] at hγ ⊢
    rw [hγ, map_inv]
  have h1 := conj_N d hγ hγ'
  have h2 : ∀ n ∈ d.N, γ⁻¹ * n * γ ∈ d.N := fun n hn => by
    have := conj_N d hγ' (by rwa [inv_inv]) n hn
    rwa [inv_inv] at this
  obtain ⟨ν', 𝓝', hν', hint⟩ := exists_pair d.N (GQ B) γ hQ h1 h2 ν 𝓝 hν.1 hν.2.1 hν.2.2
  have e := congrFun ((GlobalTheory.Mem.BesselCoeffIndep.coeff_indep_and_equivariant D A B ι d ψ hψ F hF ν 𝓝 hν).1 ν' 𝓝' hν') g
  rw [← e]
  unfold BesselDatum.coeff
  rw [hint fun n => F (n * g) * star (d.psiN ψ n)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  show F (n * (γ * g)) * star (d.psiN ψ n) = F (γ⁻¹ * n * γ * g) * star (d.psiN ψ (γ⁻¹ * n * γ))
  rw [psiN_conj d ψ hγ, mul_assoc, mul_assoc, hF _ ((GQ B).inv_mem hQ)]

end GlobalTheory.CoeffRational

end
