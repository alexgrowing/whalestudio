import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsDIffDOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanWeilOperatorTransportsHeisenbergLineD
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

noncomputable section

namespace GlobalTheory.KInfPolV

open GlobalTheory.ThK.EvAt0.PolD

theorem polLe_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ k ∈ KInf σ G.V B.emb, ∀ (m : ℕ), ∀ h ∈ GlobalTheory.FockKFin.polLe G.M B.emb m, locOpInf (om (k, 1)) h ∈ GlobalTheory.FockKFin.polLe G.M B.emb m := by
  intro F E _ _ _ _ _ σ _ B a a' G X om om' hP k hk m
  have hB := hP.base
  have hw := hP.weil
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), om x Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun x Φ hΦ => hS.pres x Φ hΦ
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evI F) := by
    intro u _
    simp [mat]
  have hk1 : k ∈ UAt σ G.V (evI F) := hk.1
  obtain ⟨A, hA⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hB.std hw (k, 1) hk1 h1W
  obtain ⟨T₂, hT₂⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hB.std hw (k⁻¹, (1 : UA σ G.W.J)⁻¹)
    (GlobalTheory.RealConjFac.inv_mem_UAt hk1) (GlobalTheory.RealConjFac.inv_mem_UAt h1W)
  have hid : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (1 : Module.End ℂ _) (⇑f) (⇑f) := fun f r _ => rfl
  have e21 : ∀ f, T₂ (A f) = f := by
    intro f
    have hc := GlobalTheory.RealConjFac.acts_comp (hpres _) (hA f) (hT₂ (A f))
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin a × Fin (a + a')) f (T₂ (A f)) f).2.2.2.1 _ hc (hid f))
  have e12 : ∀ f, A (T₂ f) = f := by
    intro f
    have hc := GlobalTheory.RealConjFac.acts_comp (hpres _) (hT₂ f) (hA (T₂ f))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin a × Fin (a + a')) f (A (T₂ f)) f).2.2.2.1 _ hc (hid f))
  let T : SInf F (Fin a × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    LinearEquiv.ofLinear A T₂ (LinearMap.ext e12) (LinearMap.ext e21)
  have hloc : ∀ f, locOpInf (om (k, 1)) f = A f := fun f => locOpInf_eq (hA f)
  have hatk : ∀ (g : Matrix (Fin a) (Fin a) (AE F E)) (u : Matrix (Fin a) (Fin (a + a')) (AE F E)),
      At (evI F) u → At (evI F) (g * u) := by
    intro g u hu c hc
    rw [← Matrix.mul_smul, hu c hc, Matrix.mul_zero]

  have htr : ∀ u, At (evI F) u → ∀ f : SInf F (Fin a × Fin (a + a')),
      A (dOp (arc (G.M.co.e u).1) (arc (G.M.co.e u).2) f) =
        dOp (arc (G.M.co.e (mat k * u)).1) (arc (G.M.co.e (mat k * u)).2) (A f) := by
    intro u hu f
    have hf : ActsD (evI F) (G.M.heisLine B.ψ u) f (dOp (arc (G.M.co.e u).1) (arc (G.M.co.e u).2) f) :=
      (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hB.std G.M u hu _ _).2 rfl
    have ht := GlobalTheory.HeisTransport.actsD_heisLine_transport F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hB
      hP.geo.hV hP.geo.hW hP.geo.hM hw k hk1 1 h1W T (fun f => hA f) (fun f => hT₂ f) u hu f _ hf
    have e : mat k * u * (mat (1 : UA σ G.W.J)).transpose = mat k * u := by
      rw [show mat (1 : UA σ G.W.J) = 1 from rfl, Matrix.transpose_one, Matrix.mul_one]
    rw [e] at ht
    exact (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hB.std G.M _ (hatk _ u hu) _ _).1 ht
  have hdab : ∀ a₁ b₁ : Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F, ∃ a₂ b₂ : Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F,
      ∀ f : SInf F (Fin a × Fin (a + a')), A (dOp a₁ b₁ f) = dOp a₂ b₂ (A f) := by
    intro a₁ b₁
    have hu := GlobalTheory.ThK.EvAt0.PolEv.at_symm G.M a₁ b₁
    refine ⟨arc (G.M.co.e (mat k * G.M.co.e.symm (fun i => liftA (a₁ i), fun i => liftA (b₁ i)))).1,
      arc (G.M.co.e (mat k * G.M.co.e.symm (fun i => liftA (a₁ i), fun i => liftA (b₁ i)))).2, fun f => ?_⟩
    have h := htr _ hu f
    rw [LinearEquiv.apply_symm_apply, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA] at h
    exact h
  have hkk : ∀ u : Matrix (Fin a) (Fin (a + a')) (AE F E), mat k * (mat k⁻¹ * u) = u := by
    intro u
    rw [← Matrix.mul_assoc]
    change mat (k * k⁻¹) * u = u
    rw [mul_inv_cancel]
    exact Matrix.one_mul u

  have hgauss : ∀ g : SInf F (Fin a × Fin (a + a')), GaussD G.M B.emb g → GaussD G.M B.emb (A g) := by
    intro g hg
    obtain ⟨ε, hε⟩ := hg
    refine ⟨ε, fun u u' hu hu' huu => ?_⟩
    have hv := hatk (mat k⁻¹) u hu
    have hv' := hatk (mat k⁻¹) u' hu'
    have hrel : ∀ w, (mat k⁻¹ * u').map (piInf (B.emb w)) =
        (((ε w : ℤ) : ℂ) * Complex.I) • (G.V.θ w * (mat k⁻¹ * u).map (piInf (B.emb w)) * (G.W.θ w)ᵀ) := by
      intro w
      have hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
        rw [← Matrix.map_mul]
        change (mat (k⁻¹ * k)).map _ = 1
        rw [inv_mul_cancel]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      have hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := mul_eq_one_comm.1 hm
      have hc : (mat k⁻¹).map (piInf (B.emb w)) * G.V.θ w = G.V.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
        calc _ = (mat k⁻¹).map (piInf (B.emb w)) * G.V.θ w *
              ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by rw [hm', Matrix.mul_one]
          _ = (mat k⁻¹).map (piInf (B.emb w)) * (G.V.θ w * (mat k).map (piInf (B.emb w))) *
              (mat k⁻¹).map (piInf (B.emb w)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
      rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.mul_smul]
      congr 1
      simp only [← Matrix.mul_assoc]
      rw [hc]
    have key := hε _ _ hv hv' hrel
    have t1 := htr _ hv' g
    have t2 := htr _ hv g
    rw [hkk] at t1 t2
    rw [← t1, ← t2, key, map_smul]

  have hst : ∀ m, ∀ f ∈ GlobalTheory.FockKFin.polLe G.M B.emb m, A f ∈ GlobalTheory.FockKFin.polLe G.M B.emb m := by
    intro m
    induction m with
    | zero =>
      intro f hf
      rw [GlobalTheory.FockKFin.polLe_zero] at hf ⊢
      refine Submodule.span_induction (fun g hg => Submodule.subset_span (hgauss g hg))
        (by rw [map_zero]; exact Submodule.zero_mem _) (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
        (fun c x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) hf
    | succ m ih =>
      intro f hf
      rw [GlobalTheory.FockKFin.polLe_succ] at hf ⊢
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      rw [map_add]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (ih y hy)) (Submodule.mem_sup_right ?_)
      refine Submodule.span_induction (fun g hg => ?_)
        (by rw [map_zero]; exact Submodule.zero_mem _) (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
        (fun c x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) hz
      obtain ⟨a₁, b₁, g₀, hg₀, rfl⟩ := hg
      obtain ⟨a₂, b₂, hab⟩ := hdab a₁ b₁
      rw [hab]
      exact GlobalTheory.FockKFin.dOp_mem_dStep _ a₂ b₂ (ih g₀ hg₀)
  intro h hh
  rw [hloc]
  exact hst m h hh

end GlobalTheory.KInfPolV

end
