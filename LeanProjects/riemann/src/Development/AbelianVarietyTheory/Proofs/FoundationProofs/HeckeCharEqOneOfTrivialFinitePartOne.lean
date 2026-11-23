import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmType
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeFinTrivial

theorem mem_closure_range {F E ι : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (τ : ι → E →+* ℂ) (θ : ι → (InfiniteAdeleRing F ⊗[F] E →+* ℂ))
    (h1 : ∀ i (x : E), θ i ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x) = τ i x)
    (h2 : ∀ i, Continuous fun a : InfiniteAdeleRing F => θ i (a ⊗ₜ[F] (1 : E)))
    (y : InfiniteAdeleRing F ⊗[F] E) :
    (fun i => θ i y) ∈ closure (Set.range fun (k : E) i => τ i k) := by
  let S : AddSubgroup (ι → ℂ) := (RingHom.pi τ).toAddMonoidHom.range.topologicalClosure
  show (fun i => θ i y) ∈ S
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact S.zero_mem
  | add a b ha hb => simp only [map_add]; exact S.add_mem ha hb
  | tmul a x =>
    have e : ∀ (a : InfiniteAdeleRing F) i, θ i (a ⊗ₜ[F] x) = θ i (a ⊗ₜ[F] (1 : E)) * τ i x := by
      intro a i
      rw [← h1, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hc : Continuous fun (a : InfiniteAdeleRing F) i => θ i (a ⊗ₜ[F] x) := by
      refine continuous_pi fun i => ?_
      simp only [e]
      exact (h2 i).mul continuous_const
    refine DenseRange.induction_on (InfiniteAdeleRing.denseRange_algebraMap F) a
      (isClosed_closure.preimage hc) fun f => ?_
    refine subset_closure ⟨f • x, funext fun i => ?_⟩
    show τ i (f • x) = θ i (algebraMap F _ f ⊗ₜ[F] x)
    rw [← h1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem denseRange_units {E ι : Type} [Field E] [Finite ι] [Nonempty ι] (τ : ι → E →+* ℂ)
    (h : DenseRange fun (k : E) i => τ i k) :
    DenseRange fun (k : Eˣ) i => Units.map (τ i).toMonoidHom k := by
  have hg : Topology.IsOpenEmbedding (Pi.map (fun _ : ι => (Units.val : ℂˣ → ℂ))) :=
    Topology.IsOpenEmbedding.piMap (fun w => Units.isOpenEmbedding_val)
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := h.exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty ι := inferInstance
    have h1 := congrFun hk w
    beta_reduce at h1
    rw [map_zero] at h1
    exact (v w).ne_zero h1
  refine ⟨v, hv, Units.mk0 k hk0, ?_⟩
  funext w
  exact Units.ext (congrFun hk w).symm

set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare in

theorem eq_one_of_trivial_on_finite : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c → (∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x = 1) → ∀ x, c x = 1 := by
  intro D c hc hf
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun τ => θ' (tauE D τ)
  have hθ : IsInfFam θ := fun τ => hθ' _
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau :=
    ⟨((GlobalTheory.CMTypePlaces.places_bijective D).2 (Classical.arbitrary _)).choose⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Tc : Continuous T.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hT : ∀ x : (AE D)ˣ, c x = c (T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) := by
    intro x
    have h1 : a x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x :=
      Units.ext (ext _ _ ((ha x).2.trans (tf _).symm) fun τ =>
        (congrArg (θ τ) (ha x).1).trans (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
    rw [← h1]
    conv_lhs => rw [hab x, map_mul, hf _ (hb x).1, mul_one]
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  intro x
  rw [hT]
  generalize (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) = z
  refine (denseRange_units (tauE D) hd).induction_on z
    (isClosed_eq (hc.1.comp Tc) continuous_const) fun k => ?_
  refine Eq.trans ?_ ((hT _).symm.trans (hc.2 k))
  congr 2
  funext τ
  exact Units.ext ((hθ τ).1 k).symm

end GlobalTheory.HeckeFinTrivial
