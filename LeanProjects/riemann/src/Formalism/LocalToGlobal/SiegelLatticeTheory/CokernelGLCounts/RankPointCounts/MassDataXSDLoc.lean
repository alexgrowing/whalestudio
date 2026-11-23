import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SelfDualLoc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InclR

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX.SDL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

def swp : E ⊗[F] Fv F v ≃ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.comm F E (Fv F v)

theorem swp_tmul (a : E) (c : Fv F v) : swp v (a ⊗ₜ[F] c) = c ⊗ₜ[F] a := rfl

def swVv (w : Fin n → E ⊗[F] Fv F v) : Fin n → Fv F v ⊗[F] E := fun i => swp v (w i)

theorem swVv_injective : Function.Injective (swVv (E := E) v (n := n)) := fun _ _ h =>
  funext fun i => (swp v).injective (congrFun h i)

theorem swVv_surjective : Function.Surjective (swVv (E := E) v (n := n)) := fun w =>
  ⟨fun i => (swp v).symm (w i), funext fun i => (swp v).apply_symm_apply (w i)⟩

theorem swVv_incl (x : Fin n → E) :
    swVv v (fun i => PI.SelfDualLoc.inclE (F := F) (Fv F v) (x i)) = ratV (F := F) (Fv F v) x := by
  funext i
  simp [swVv, swp, PI.SelfDualLoc.inclE, ratV, inclR, Algebra.TensorProduct.comm_tmul]

theorem sig_swap (σ : E →ₐ[F] E) (t : E ⊗[F] Fv F v) :
    sigR (Fv F v) σ (swp v t) = swp v (PI.SelfDualLoc.sigR σ (Fv F v) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => simp [sigR, PI.SelfDualLoc.sigR, swp, Algebra.TensorProduct.comm_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem incl_swap (e : E) : swp v (PI.SelfDualLoc.inclE (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) e := by
  simp [swp, PI.SelfDualLoc.inclE, inclR, Algebra.TensorProduct.comm_tmul]

theorem hR_swap (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (z y : Fin n → E ⊗[F] Fv F v) :
    hR (Fv F v) σ J (swVv v z) (swVv v y) =
      swp v (PI.SelfDualLoc.hform (PI.SelfDualLoc.sigR σ (Fv F v)) (J.map (PI.SelfDualLoc.inclE (F := F) (Fv F v))) z y) := by
  simp only [hR, Formalism.UG.hform, PI.SelfDualLoc.hform, map_sum, map_mul, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [swVv, sig_swap, incl_swap]

section Rings

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

abbrev Sv : Subring (E ⊗[F] Fv F v) :=
  PI.SelfDualLoc.tensInt (F := F) (Fv F v) (PI.SelfDualLoc.intOE E) (v.adicCompletionIntegers F).toSubring

theorem oev_gen (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, trivial, rfl⟩

theorem oev_mul {s t : Fv F v ⊗[F] E} (hs : s ∈ OEv (E := E) v) (ht : t ∈ OEv (E := E) v) :
    s * t ∈ OEv (E := E) v := by
  first | exact UpperTheory.Reformulated.B.Qh24.oev_mul .. | (apply UpperTheory.Reformulated.B.Qh24.oev_mul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh24.oev_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh24.oev_mul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh24.oev_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh24.oev_mul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› v s t hs ht | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› v s t hs | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› v s t | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› v s | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› v | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F

theorem oev_alg (c : v.adicCompletionIntegers F) : ((c : Fv F v) ⊗ₜ[F] (1 : E)) ∈ OEv (E := E) v := by
  have h : ((c : Fv F v) ⊗ₜ[F] (1 : E)) = c • inclR (F := F) (Fv F v) ((1 : 𝓞 E) : E) := by
    simp [inclR, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  rw [h]
  exact Submodule.smul_mem _ c (oev_gen v 1)

theorem swp_mem_oev {s : E ⊗[F] Fv F v} (hs : s ∈ Sv (E := E) v) : swp v s ∈ OEv (E := E) v := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨a, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩
    · exact oev_gen v b
    · exact oev_alg v ⟨c, hc⟩
  | zero => rw [map_zero]; exact zero_mem (Submodule.span _ _)
  | one => rw [map_one]; simpa using oev_gen v (E := E) 1
  | add x y _ _ hx hy => rw [map_add]; exact add_mem (S := Submodule _ _) hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem (S := Submodule _ _) hx
  | mul x y _ _ hx hy => rw [map_mul]; exact oev_mul v hx hy

theorem oev_swp {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v) : ∃ s ∈ Sv (E := E) v, swp v s = t := by
  unfold OEv at ht
  rw [SetLike.mem_coe] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    refine ⟨(a : E) ⊗ₜ[F] (1 : Fv F v), Subring.subset_closure (Or.inl ⟨⟨(a : E), ⟨a, rfl⟩⟩, rfl⟩), ?_⟩
    rfl
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', rfl⟩ := hy
    exact ⟨s + s', add_mem hs hs', map_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    refine ⟨((1 : E) ⊗ₜ[F] (c : Fv F v)) * s,
      mul_mem (Subring.subset_closure (Or.inr ⟨c, rfl⟩)) hs, ?_⟩
    rw [map_mul, swp_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl

end Rings

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Lb : Submodule (𝓞 E) (Fin n → E))

theorem oev_smul_lat {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v) {w : Fin n → Fv F v ⊗[F] E}
    (hw : w ∈ latLoc v (Lb : Set (Fin n → E))) : (fun i => t * w i) ∈ latLoc v (Lb : Set (Fin n → E)) := by
  unfold OEv at ht
  rw [SetLike.mem_coe] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine Submodule.subset_span ⟨a • x, Lb.smul_mem a hx, ?_⟩
      funext i
      simp [ratV, map_mul, Pi.smul_apply, Algebra.smul_def]
    | zero =>
      convert zero_mem (latLoc v (Lb : Set (Fin n → E))) using 1
      funext i; simp
    | add y z _ _ hy hz =>
      have e : (fun i => inclR (F := F) (Fv F v) (a : E) * (y + z) i) =
          (fun i => inclR (F := F) (Fv F v) (a : E) * y i) + (fun i => inclR (F := F) (Fv F v) (a : E) * z i) := by
        funext i; simp [mul_add]
      rw [e]; exact add_mem hy hz
    | smul c y _ hy =>
      have e : (fun i => inclR (F := F) (Fv F v) (a : E) * (c • y) i) =
          c • (fun i => inclR (F := F) (Fv F v) (a : E) * y i) := by
        funext i; simp [mul_smul_comm]
      rw [e]; exact Submodule.smul_mem _ c hy
  | zero =>
    convert zero_mem (latLoc v (Lb : Set (Fin n → E))) using 1
    funext i; simp
  | add x y _ _ hx hy =>
    have e : (fun i => (x + y) * w i) = (fun i => x * w i) + (fun i => y * w i) := by funext i; simp [add_mul]
    rw [e]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : (fun i => (c • x) * w i) = c • (fun i => x * w i) := by funext i; simp [smul_mul_assoc]
    rw [e]; exact Submodule.smul_mem _ c hx

theorem swVv_mem_latLoc {z : Fin n → E ⊗[F] Fv F v}
    (hz : z ∈ PI.SelfDualLoc.latS (F := F) (Fv F v) (Sv (E := E) v) Lb) :
    swVv v z ∈ latLoc v (Lb : Set (Fin n → E)) := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [swVv_incl]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : swVv v (0 : Fin n → E ⊗[F] Fv F v) = 0 := by funext i; simp [swVv]
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : swVv v (x + y) = swVv v x + swVv v y := by funext i; simp [swVv]
    rw [this]; exact add_mem hx hy
  | smul s x _ hx =>
    have : swVv v (s • x) = fun i => swp v (s : E ⊗[F] Fv F v) * swVv v x i := by
      funext i; simp [swVv, Submodule.coe_smul_of_tower, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]
    exact oev_smul_lat v Lb (swp_mem_oev v s.2) hx

theorem latLoc_swVv {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc v (Lb : Set (Fin n → E))) :
    ∃ z ∈ PI.SelfDualLoc.latS (F := F) (Fv F v) (Sv (E := E) v) Lb, swVv v z = w := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩, swVv_incl v x⟩
  | zero => exact ⟨0, zero_mem _, by funext i; simp [swVv]⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact ⟨z + z', add_mem hz hz', by funext i; simp [swVv]⟩
  | smul c x _ hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    have hc : ((1 : E) ⊗ₜ[F] (c : Fv F v)) ∈ Sv (E := E) v := Subring.subset_closure (Or.inr ⟨c, rfl⟩)
    refine ⟨(⟨_, hc⟩ : Sv (E := E) v) • z, Submodule.smul_mem _ _ hz, ?_⟩
    funext i
    simp only [swVv, Pi.smul_apply]
    rw [Subring.smul_def, smul_eq_mul, map_mul, swp_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl

theorem isSDLoc_of (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hfg : Lb.FG)
    (hint : ∀ x ∈ Lb, ∀ y ∈ Lb, PI.SelfDualLoc.hform (σ : E →+* E) J x y ∈ PI.SelfDualLoc.intOE E)
    (hdual : ∀ y : Fin n → E, (∀ x ∈ Lb, PI.SelfDualLoc.hform (σ : E →+* E) J x y ∈ PI.SelfDualLoc.intOE E) → y ∈ Lb) :
    IsSDLoc σ J v (Lb : Set (Fin n → E)) := by
  have hT : ((1 : ℕ) : 𝓞 F) ∉ v.asIdeal := by
    rw [Nat.cast_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have key := self_dual_local F E n σ J v Lb 1 (Module.Finite.iff_fg.2 hfg) hint
    (fun y hy => by simpa using hdual y hy) hT
  intro y'
  obtain ⟨y, rfl⟩ := swVv_surjective (E := E) v y'
  have hlat : swVv v y ∈ latLoc v (Lb : Set (Fin n → E)) ↔
      y ∈ PI.SelfDualLoc.latS (F := F) (Fv F v) (Sv (E := E) v) Lb := by
    constructor
    · intro h
      obtain ⟨z, hz, e⟩ := latLoc_swVv v Lb h
      rwa [← swVv_injective v e]
    · exact swVv_mem_latLoc v Lb
  rw [hlat, key]
  constructor
  · intro h x' hx'
    obtain ⟨z, hz, rfl⟩ := latLoc_swVv v Lb hx'
    rw [hR_swap]
    exact swp_mem_oev v (h z hz)
  · intro h z hz
    have h1 := h (swVv v z) (swVv_mem_latLoc v Lb hz)
    rw [hR_swap] at h1
    obtain ⟨s, hs, e⟩ := oev_swp v h1
    rwa [← (swp v).injective e]

end Lat

theorem sdLocX_holds {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : PlX X) :
    IsSDLoc X.B.I.cm.sig X.B.I.J v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
  isSDLoc_of v X.B.I.L X.B.I.cm.sig X.B.I.J X.B.I.L_fg
    (fun x hx y hy => (X.B.I.L_dual y).1 hy x hx) (fun y h => (X.B.I.L_dual y).2 h)

end Formalism.L2.SG.Pf.MassDataX.SDL
