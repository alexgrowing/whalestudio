import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescentFreeModuleCocycleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismPushoutModAdicPowUniversalStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LevH

open CategoryTheory

theorem lev_ring {A B D T : Type} [CommRing A] [CommRing B] [CommRing D] [CommRing T] [Algebra A B]
    (p q : B →+* D) (q₁₂ q₂₃ q₁₃ : D →+* T) (q₃ : B →+* T)
    (hff : (algebraMap A B).FaithfullyFlat)
    (hpo1 : IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom p) (CommRingCat.ofHom q))
    (hpo2 : IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (p.comp (algebraMap A B)))
      (CommRingCat.ofHom q₃) (CommRingCat.ofHom q₁₂))
    (e1 : q₂₃.comp p = q₁₂.comp q) (e2 : q₂₃.comp q = q₃) (e3 : q₁₃.comp p = q₁₂.comp p) (e4 : q₁₃.comp q = q₃)
    (d : ℕ) (ε : Matrix (Fin d) (Fin d) D) (hε : IsUnit ε) (hc : ε.map q₁₂ * ε.map q₂₃ = ε.map q₁₃) :
    ∃ N : Submodule A (Fin d → B), (∀ z, z ∈ N ↔ (fun i => p (z i)) = ε.mulVec fun i => q (z i)) ∧
      Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  have hw : p.comp (algebraMap A B) = q.comp (algebraMap A B) := by
    have := congrArg CommRingCat.Hom.hom hpo1.w
    simpa using this
  have hr : ∀ c, p (algebraMap A B c) = q (algebraMap A B c) := fun c => RingHom.congr_fun hw c
  let N : Submodule A (Fin d → B) :=
    { carrier := {z | (fun i => p (z i)) = ε.mulVec fun i => q (z i)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have e : (fun i => q ((a + b) i)) = (fun i => q (a i)) + fun i => q (b i) := by
          funext i; simp [map_add]
        rw [e, Matrix.mulVec_add, ← ha, ← hb]
        funext i; simp [map_add]
      zero_mem' := by
        simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
        exact (Matrix.mulVec_zero ε).symm
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq] at hz ⊢
        have e1 : (fun i => p ((c • z) i)) = q (algebraMap A B c) • fun i => p (z i) := by
          funext i; simp [Algebra.smul_def, map_mul, hr]
        have e2 : (fun i => q ((c • z) i)) = q (algebraMap A B c) • fun i => q (z i) := by
          funext i; simp [Algebra.smul_def, map_mul]
        rw [e1, e2, Matrix.mulVec_smul, hz] }
  exact ⟨N, fun z => Iff.rfl, GlobalTheory.T.descent_free_module_cocycle A B D T p q q₁₂ q₂₃ q₁₃ q₃ hff hpo1 hpo2 e1 e2 e3 e4 d ε hε hc N
    fun z => Iff.rfl⟩

variable {l : ℕ} {R : Type} [CommRing R]

theorem hom_comp_assoc {B C D E : Obj l R} (h : Hom D E) (g : Hom C D) (f : Hom B C) :
    (h.comp g).comp f = h.comp (g.comp f) := Hom.ext' rfl

theorem lev_prism [Fact l.Prime] {B C D : Obj l R} (h : Hom B C) (p q : Hom C D) (hc : Cover h) (hpo : IsPO h h p q)
    (m : ℕ) (d : ℕ) (ε : Matrix (Fin d) (Fin d) D.A) (hε : IsUnit ε)
    (hcoc : ∀ (T : Obj l R) (q₁₂ q₂₃ q₁₃ : Hom D T) (q₃ : Hom C T), q₂₃.comp p = q₁₂.comp q → q₂₃.comp q = q₃ →
      q₁₃.comp p = q₁₂.comp p → q₁₃.comp q = q₃ → ε.map q₁₂.f * ε.map q₂₃.f = ε.map q₁₃.f) :
    letI := (qmap h m).toAlgebra
    ∃ N : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m),
      (∀ z, z ∈ N ↔ (fun i => qmap p m (z i)) = (ε.map (Ideal.Quotient.mk (adI D ^ m))).mulVec
        fun i => qmap q m (z i)) ∧
      Module.Finite (B.A ⧸ adI B ^ m) ↥N ∧ Module.Projective (B.A ⧸ adI B ^ m) ↥N ∧
        IsBaseChange (C.A ⧸ adI C ^ m) N.subtype := by
  letI := (qmap h m).toAlgebra
  have c1 : p.comp h = q.comp h := hpo.comm
  refine Exists.elim (hc.stable.po D (p.comp h)) fun T hT => Exists.elim hT fun q₃ hT => Exists.elim hT
    fun q₁₂ hT => ?_
  have c2 : q₃.comp h = q₁₂.comp (p.comp h) := hT.comm
  refine Exists.elim (GlobalTheory.T.prismPushoutModAdicPow_universal l R B C C D h h p q hpo T (q₁₂.comp q) q₃ (by
      rw [hom_comp_assoc, ← c1, c2])) fun q₂₃ h23 => ?_
  refine Exists.elim (GlobalTheory.T.prismPushoutModAdicPow_universal l R B C C D h h p q hpo T (q₁₂.comp p) q₃ (by
      rw [hom_comp_assoc, c2])) fun q₁₃ h13 => ?_
  have hpo2 := hT.po m
  have hq : qmap (p.comp h) m = (qmap p m).comp (qmap h m) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  rw [hq] at hpo2
  have hq2 : ∀ (k k' : Hom D T) (k'' : Hom C T), k.comp p = k'.comp q → (qmap k m).comp (qmap p m) = (qmap k' m).comp (qmap q m) :=
    fun k k' k'' e => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg (fun H : Hom C T => Ideal.Quotient.mk (adI T ^ m) (H.f x)) e)
  have hq3 : ∀ (k : Hom D T) (k' : Hom C T), k.comp q = k' → (qmap k m).comp (qmap q m) = qmap k' m :=
    fun k k' e => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg (fun H : Hom C T => Ideal.Quotient.mk (adI T ^ m) (H.f x)) e)
  have hq4 : ∀ (k : Hom D T) (k' : Hom D T), k.comp p = k'.comp p → (qmap k m).comp (qmap p m) = (qmap k' m).comp (qmap p m) :=
    fun k k' e => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg (fun H : Hom C T => Ideal.Quotient.mk (adI T ^ m) (H.f x)) e)
  refine lev_ring (qmap p m) (qmap q m) (qmap q₁₂ m) (qmap q₂₃ m) (qmap q₁₃ m) (qmap q₃ m) (hc.ff m) (hpo.po m) hpo2
    (hq2 q₂₃ q₁₂ q₃ h23.1.1) (hq3 q₂₃ q₃ h23.1.2) (hq4 q₁₃ q₁₂ h13.1.1) (hq3 q₁₃ q₃ h13.1.2) d _
    (hε.map (Ideal.Quotient.mk (adI D ^ m)).mapMatrix) ?_
  have := congrArg (fun M : Matrix (Fin d) (Fin d) T.A => M.map (Ideal.Quotient.mk (adI T ^ m)))
    (hcoc T q₁₂ q₂₃ q₁₃ q₃ h23.1.1 h23.1.2 h13.1.1 h13.1.2)
  simp only [Matrix.map_mul] at this
  exact this

end GlobalTheory.BSP.LevH

namespace GlobalTheory.BSP.LevH

theorem descent_at_level : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ m : ℕ, letI := (qmap h m).toAlgebra; ∃ N : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m), (∀ z, z ∈ N ↔ (fun i => qmap p m (z i)) = ((S.ε (p.comp f) (q.comp f)).map (Ideal.Quotient.mk (adI D ^ m))).mulVec fun i => qmap q m (z i)) ∧ Module.Finite (B.A ⧸ adI B ^ m) ↥N ∧ Module.Projective (B.A ⧸ adI B ^ m) ↥N ∧ IsBaseChange (C.A ⧸ adI C ^ m) N.subtype := by
  intro l _ K bk d S B C D h f p q hc hpo m
  refine lev_prism h p q hc hpo m d (S.ε (p.comp f) (q.comp f))
    ⟨⟨S.ε (p.comp f) (q.comp f), S.ε (q.comp f) (p.comp f), by rw [S.ε_trans, S.ε_refl],
      by rw [S.ε_trans, S.ε_refl]⟩, rfl⟩ ?_
  intro T q₁₂ q₂₃ q₁₃ q₃ e1 e2 e3 e4
  have a1 : q₂₃.comp (p.comp f) = q₁₂.comp (q.comp f) := by rw [← hom_comp_assoc, e1, hom_comp_assoc]
  have a2 : q₂₃.comp (q.comp f) = q₃.comp f := by rw [← hom_comp_assoc, e2]
  have a3 : q₁₃.comp (p.comp f) = q₁₂.comp (p.comp f) := by rw [← hom_comp_assoc, e3, hom_comp_assoc]
  have a4 : q₁₃.comp (q.comp f) = q₃.comp f := by rw [← hom_comp_assoc, e4]
  rw [S.ε_nat, S.ε_nat, S.ε_nat, a1, a2, a3, a4, S.ε_trans]

end GlobalTheory.BSP.LevH
