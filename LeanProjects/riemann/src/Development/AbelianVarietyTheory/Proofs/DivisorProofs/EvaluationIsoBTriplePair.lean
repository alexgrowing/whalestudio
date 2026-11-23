import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct GlobalTheory.VacAny
open Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.VanishLocInv

section Cancel

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def atInf (y : mixedEmbedding.mixedSpace F) : AF F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y, (0 : Af F))

def build (y : mixedEmbedding.mixedSpace F) (T : Finset (Pl F)) (p : ∀ w : Pl F, Fv F w) : AF F :=
  atInf y + ∑ w ∈ T, GlobalTheory.LatVac.liftV w (p w)

theorem evFin_build (y : mixedEmbedding.mixedSpace F) (T : Finset (Pl F)) (p : ∀ w : Pl F, Fv F w) (u : Pl F) :
    evFin F u (build y T p) = if u ∈ T then p u else 0 := by
  rw [build, map_add, map_sum]
  have h0 : evFin F u (atInf y) = 0 := by
    show evalV F u (0 : Af F) = 0
    exact map_zero _
  rw [h0, zero_add]
  split_ifs with hu
  · rw [Finset.sum_eq_single u]
    · exact GlobalTheory.LatVac.evFin_liftV u (p u)
    · intro w _ hw
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hw) _
    · intro h; exact absurd hu h
  · apply Finset.sum_eq_zero
    intro w hw
    exact GlobalTheory.AdelicU.evalV_singleFin_ne (fun h : u = w => hu (h ▸ hw)) _

theorem evI_sum (T : Finset (Pl F)) (p : ∀ w : Pl F, Fv F w) :
    evI F (∑ w ∈ T, GlobalTheory.LatVac.liftV w (p w)) = 0 := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  | insert w T hw ih =>
    rw [Finset.sum_insert hw, GlobalTheory.ThK.LocalOps.evI_add, ih, add_zero]
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_build (y : mixedEmbedding.mixedSpace F) (T : Finset (Pl F)) (p : ∀ w : Pl F, Fv F w) :
    evI F (build y T p) = y := by
  have hs : evI F (∑ w ∈ T, GlobalTheory.LatVac.liftV w (p w)) = 0 := by
    apply GlobalTheory.VanishLocInv.evI_sum
  rw [build, GlobalTheory.ThK.LocalOps.evI_add, hs, add_zero]
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y) = y
  exact RingEquiv.apply_symm_apply _ _

theorem eq_of_pure_update_eq (vac : ∀ w : Pl F, (κ → Fv F w) → ℂ) (hne : ∀ w, vac w ≠ 0)
    (hstd : ∀ᶠ w in cofinite, vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    (g : SInf F κ) (hg : g ≠ 0) (v : Pl F) (A B : (κ → Fv F v) → ℂ)
    (h : pure g (Function.update vac v A) = pure g (Function.update vac v B)) : A = B := by
  obtain ⟨y, hy⟩ : ∃ y, g y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hg (SchwartzMap.ext fun y => by simp [hc y])
  have hS : {w : Pl F | ¬ vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1}.Finite :=
    Filter.eventually_cofinite.mp hstd
  have hz : ∀ w, ∃ z : κ → Fv F w, vac w z ≠ 0 := fun w => by
    by_contra hc
    push_neg at hc
    exact hne w (funext hc)
  choose zw hzw using hz
  funext t
  set T : Finset (Pl F) := insert v hS.toFinset with hT
  set p : ∀ w : Pl F, κ → Fv F w := Function.update zw v t with hp
  set x : κ → AF F := fun i => build (y i) T (fun w => p w i) with hx
  have hev : ∀ u, (fun i => evFin F u (x i)) = if u ∈ T then p u else 0 := by
    intro u
    funext i
    show evFin F u (build (y i) T (fun w => p w i)) = _
    rw [evFin_build (y i) T (fun w => p w i) u]
    split_ifs <;> rfl
  have hevI : (fun i => evI F (x i)) = y := by
    funext i
    exact evI_build (y i) T (fun w => p w i)
  have hsub : ∀ c : (κ → Fv F v) → ℂ,
      Function.mulSupport (fun w => (Function.update vac v c : ∀ w, (κ → Fv F w) → ℂ) w fun i => evFin F w (x i)) ⊆
        (T : Set (Pl F)) := by
    intro c w hw
    by_contra hwT
    apply hw
    have hwv : w ≠ v := fun e => hwT (e ▸ Finset.mem_insert_self _ _)
    have hwS : vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
      by_contra hc
      exact hwT (Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 hc))
    show Function.update vac v c w (fun i => evFin F w (x i)) = 1
    rw [Function.update_of_ne hwv, hev w, if_neg (show w ∉ T from hwT), hwS]
    exact Set.indicator_of_mem (show (0 : κ → Fv F w) ∈ {x | ∀ i, x i ∈ w.adicCompletionIntegers F} from
      fun i => zero_mem _) 1
  have hfin : (Function.mulSupport fun w => vac w fun i => evFin F w (x i)).Finite :=
    GlobalTheory.PureFactor.mulSupport_finite vac hstd x
  have hsplit : ∀ c : (κ → Fv F v) → ℂ, pure g (Function.update vac v c) x =
      c (fun i => evFin F v (x i)) * pure g (Function.update vac v fun _ => 1) x := by
    intro c
    have := GlobalTheory.ThK.LocalOps.pure_split v g vac (Function.update vac v c) x hfin
      (fun w hw => Function.update_of_ne hw _ _)
    rw [Function.update_self] at this
    exact this
  have hxv : (fun i => evFin F v (x i)) = t := by
    rw [hev v, if_pos (Finset.mem_insert_self _ _), hp, Function.update_self]
  have hP : pure g (Function.update vac v fun _ => 1) x ≠ 0 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    rw [hevI]
    refine mul_ne_zero hy ?_
    rw [finprod_eq_prod_of_mulSupport_subset _ (hsub fun _ => 1), Finset.prod_ne_zero_iff]
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      rw [Function.update_self]
      exact one_ne_zero
    · rw [Function.update_of_ne hwv, hev w, if_pos hw, hp, Function.update_of_ne hwv]
      exact hzw w
  have e := congrFun h x
  rw [hsplit A, hsplit B, hxv] at e
  exact mul_right_cancel₀ hP e

end Cancel

theorem inv_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)),
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (v : Pl F) (u : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)), u ∈ isoB H H' → At (evFin F v) u →
    ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
      ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v u) φ) = ev v φ := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' e' hEv X om om' om₁ om₁' hT hT₁ ei ev hei hev hfac v u hu hat φ hφ
  set φ₁ := schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v u) φ with hφ₁def
  have hφ₁ : φ₁ ∈ SB _ := GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 v _ φ hφ
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hei (ContinuousLinearMap.ext hc)
  have hSB : ∀ c ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), ∀ w, Function.update G.M'.vac v c w ∈ SB _ := by
    intro c hc w
    by_cases hwv : w = v
    · subst hwv
      rw [Function.update_self]; exact hc
    · rw [Function.update_of_ne hwv]; exact (hT.geo.hM'.vac w).1
  have hco : ∀ c : (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ,
      ∀ᶠ w in cofinite, Function.update G.M'.vac v c w = G.M'.vac w := by
    intro c
    filter_upwards [Filter.eventually_cofinite_ne v] with w hw
    exact Function.update_of_ne hw _ _
  have hstd := GlobalTheory.PureFactor.update_eventually G.M'.vac v φ hT.geo.hM'.std
  have hpure := GlobalTheory.TensUniq.pure_mem_schA f _ (hSB φ hφ) hstd
  have hfin := GlobalTheory.PureFactor.mulSupport_finite _ hstd
  have hact : Acts (evFin F v) (G.M'.co.rho B.ψ u) (Function.update G.M'.vac v φ v) φ₁ := by
    rw [Function.update_self]
    exact GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v u hat φ
  have hrho := GlobalTheory.ThK.LocalOps.acts_pure v (G.M'.co.rho B.ψ u) f _ φ₁ hpure hfin hact
  rw [Function.update_idem] at hrho
  have hinv := hEv.inv u hu _ hpure
  rw [hrho, hfac f _ (hSB φ₁ hφ₁) (hco φ₁), hfac f _ (hSB φ hφ) (hco φ)] at hinv
  have hup : ∀ c : (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ,
      (fun w => ev w (Function.update G.M'.vac v c w)) = Function.update G₁.M'.vac v (ev v c) := by
    intro c
    funext w
    by_cases hwv : w = v
    · subst hwv
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hwv, Function.update_of_ne hwv]; exact (hev w).1
  rw [hup, hup] at hinv
  exact eq_of_pure_update_eq G₁.M'.vac (fun w => (hT₁.geo.hM'.vac w).2.1) hT₁.geo.hM'.std (ei f) hf v _ _ hinv

end GlobalTheory.VanishLocInv
