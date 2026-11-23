import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
import GroundTheory.GlobalFields.Adele.Compact
import GroundTheory.GlobalFields.Adele.Approximation

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchHeis

variable {F : Type} [Field F] [NumberField F]

def intFin (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intFin_mem (κ : Type) [Fintype κ] : intFin (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set B := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hB
  have hO : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles
  have hK : IsCompact B := isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hC : IsClosed B := hK.isClosed
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ B
  · refine ⟨_, hO, hx, fun y hy => ?_⟩
    simp only [intFin, ← hB, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]
  · refine ⟨_, hC.isOpen_compl, hx, fun y hy => ?_⟩
    simp only [intFin, ← hB, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

def refFin (κ : Type) (x : κ → AF F) : ℂ := intFin κ (fun i => (x i).2)

theorem fst_eq_zero_of_ev {a : AF F} (h : evI F a = 0) : a.1 = 0 :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp h

theorem snd_eq_zero_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have := congrArg Prod.snd (congrFun (hz (0, 1) h0) i)
  change (((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 * (z i).2) = (0 : AF F).2 at this
  rw [one_mul] at this
  exact this

theorem refFin_of_zero (κ : Type) (x : κ → AF F) (hx : ∀ i, (x i).2 = 0) : refFin κ x = 1 := by
  have : (fun i => (x i).2) = 0 := funext hx
  simp only [refFin, this, intFin]
  rw [Set.indicator_of_mem (show (0 : κ → FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
    fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
      fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
  rfl

theorem refFin_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : refFin κ (liftV y) = 1 :=
  refFin_of_zero κ _ fun _ => rfl

theorem refFin_add_liftV {κ : Type} (x : κ → AF F) (y : κ → mixedEmbedding.mixedSpace F) :
    refFin κ (x + liftV y) = refFin κ x := by
  have : (fun i => ((x + liftV y) i).2) = fun i => (x i).2 := by
    funext i
    change (x i).2 + 0 = (x i).2
    rw [add_zero]
  simp only [refFin, this]

theorem rest_refFin (κ : Type) [Fintype κ] (f : SInf F κ) :
    Rest (evI F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (refFin κ) := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, intFin κ, intFin_mem κ, rfl⟩⟩
  have : (fun i => ((x + z) i).2) = fun i => (x i).2 := by
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [snd_eq_zero_of_at hz i, add_zero]
  simp only [refFin, this]

theorem liftV_locV_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) : liftV (locV z) = z := by
  funext i
  refine Prod.ext ?_ ?_
  · exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
  · exact (snd_eq_zero_of_at hz i).symm

theorem evI_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) (i : κ) : evI F (liftV y i) = y i :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem evH_invTwo : evH F (⅟(2 : AF F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
  have h1 : evH F (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evH F) 2, ← map_mul, invOf_mul_self, map_one]
  have h2 : (2 : mixedEmbedding.mixedSpace F) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2, ← map_mul]
    norm_num
  calc evH F (⅟(2 : AF F)) = evH F (⅟(2 : AF F)) * (2 * algebraMap ℝ _ (1 / 2)) := by rw [h2, mul_one]
    _ = algebraMap ℝ _ (1 / 2) := by rw [← mul_assoc, h1, one_mul]

theorem schr_tens {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ (liftV v.1, liftV v.2) (tens (evI F) g (refFin κ)) = tens (evI F) (schrF (trP F κ) v g) (refFin κ) := by
  funext x
  set z : AF F := x ⬝ᵥ liftV v.2 + ⅟(2 : AF F) * (liftV v.1 ⬝ᵥ liftV v.2) with hz
  let finH : AF F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
  have hfin : finH z = 0 := by
    simp only [hz, dotProduct, map_add, map_mul, map_sum]
    have e : ∀ i, finH (liftV v.2 i) = 0 := fun _ => rfl
    simp only [e, mul_zero, Finset.sum_const_zero, add_zero]
  have hAt : At (evI F) z := by
    intro c hc
    refine Prod.ext ?_ ?_
    · change c.1 * z.1 = 0
      rw [fst_eq_zero_of_ev hc, zero_mul]
    · change c.2 * finH z = 0
      rw [hfin, mul_zero]
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F z) =
      trP F κ (fun i => evI F (x i)) v.2 + trP F κ v.1 v.2 / 2 := by
    rw [evI_eq, hz]
    simp only [dotProduct, map_add, map_mul, map_sum, ← evI_eq, evI_liftV, trP]
    rw [show evI F (⅟(2 : AF F)) = algebraMap ℝ _ (1 / 2) from evH_invTwo, ← Algebra.smul_def, map_smul, map_sum,
      smul_eq_mul]
    ring
  have hloc : (fun i => evI F ((x + liftV v.1) i)) = (fun i => evI F (x i)) + v.1 := by
    funext i
    simp only [Pi.add_apply, evI_eq, map_add]
    exact congrArg (evH F (x i) + ·) (evI_liftV v.1 i)
  simp only [schr, tens, schrF]
  rw [hψ.2.2 z hAt, htr, hloc, refFin_add_liftV]
  ring

end GlobalTheory.ArchHeis

namespace GlobalTheory.ArchHeis

theorem archOp_schrF : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    ∀ h ∈ UAt σ W (evI F), ∀ (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      (f f₁ : SInf F (Fin n × Fin d)), ⇑f₁ = schrF (trP F (Fin n × Fin d)) v ⇑f →
      ⇑(archOp om h f₁) = schrF (trP F (Fin n × Fin d)) (archAct M h v) ⇑(archOp om h f) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hψ hW hex h hh v f f₁ hf₁
  have hS := IsUWeilPair.isUSplitting hW
  set u := M.co.e.symm (liftV v.1, liftV v.2) with hu
  set u' := actAB (cA σ) ((1 : UA σ X.J), h) u with hu'
  have hAt : ∀ c : AF F, evI F c = 0 → c • u' = 0 := by
    intro c hc
    have h0 : c • u = 0 := by
      have hl : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, c • liftV y = 0 := by
        intro y
        funext i
        refine Prod.ext ?_ ?_
        · change c.1 * _ = 0
          rw [fst_eq_zero_of_ev hc, zero_mul]
        · change c.2 * 0 = 0
          rw [mul_zero]
      rw [hu, ← LinearEquiv.map_smul, Prod.smul_mk, hl, hl, Prod.mk_zero_zero, LinearEquiv.map_zero]
    simp only [hu', actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero, Matrix.zero_mul]
  have hAt₁ : At (evI F) (M.co.e u').1 := by
    intro c hc
    have := congrArg Prod.fst (congrArg M.co.e (hAt c hc))
    rwa [LinearEquiv.map_smul, LinearEquiv.map_zero] at this
  have hAt₂ : At (evI F) (M.co.e u').2 := by
    intro c hc
    have := congrArg Prod.snd (congrArg M.co.e (hAt c hc))
    rwa [LinearEquiv.map_smul, LinearEquiv.map_zero] at this
  have he' : M.co.e u' = (liftV (archAct M h v).1, liftV (archAct M h v).2) := by
    change M.co.e u' = (liftV (locV (M.co.e u').1), liftV (locV (M.co.e u').2))
    rw [liftV_locV_of_at hAt₁, liftV_locV_of_at hAt₂]
  have hA₁ := acts_archOp om h f₁ (hex h hh f₁) (refFin _) (rest_refFin _ f₁)
  have hA := acts_archOp om h f (hex h hh f) (refFin _) (rest_refFin _ f)
  have himpl := hS.impl (1, h) u (tens (evI F) ⇑f (refFin _)) (rest_refFin _ f).2
  have h1 : M.co.rho ψ u (tens (evI F) ⇑f (refFin _)) = tens (evI F) ⇑f₁ (refFin _) := by
    simp only [Darboux.rho, hu, LinearEquiv.apply_symm_apply]
    rw [schr_tens ψ hψ v, hf₁]
  have h2 : M.co.rho ψ u' (tens (evI F) ⇑(archOp om h f) (refFin _)) =
      tens (evI F) (schrF (trP F (Fin n × Fin d)) (archAct M h v) ⇑(archOp om h f)) (refFin _) := by
    simp only [Darboux.rho]
    rw [he', schr_tens ψ hψ]
  rw [h1, hA₁, hA, ← hu', h2] at himpl
  funext y
  have := congrFun himpl (liftV y)
  simp only [tens, refFin_liftV, mul_one] at this
  have hy : (fun i => evI F (liftV y i)) = y := funext fun i => evI_liftV y i
  rwa [hy] at this

end GlobalTheory.ArchHeis
