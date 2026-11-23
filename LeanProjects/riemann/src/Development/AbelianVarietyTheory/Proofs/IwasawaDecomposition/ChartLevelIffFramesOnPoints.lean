import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem frStab_iff_image {P : HeightOneSpectrum (𝓞 E)} {C : Set (Sp E n)} (g : ↥(GLint E n P)) :
    g ∈ frStab P C ↔ (fun v => g.1 v) '' C = C := by
  constructor
  · intro h
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).2 hw
    · intro hv
      have e : g.1 ((g⁻¹).1 v) = v := LinearEquiv.apply_symm_apply g.1 v
      refine ⟨(g⁻¹).1 v, ?_, e⟩
      have h' := h ((g⁻¹).1 v)
      rw [e] at h'
      exact h'.1 hv
  · intro h v
    constructor
    · intro hv
      rw [← h] at hv
      obtain ⟨w, hw, e⟩ := hv
      rwa [← g.1.injective e]
    · intro hv
      rw [← h]
      exact ⟨v, hv, rfl⟩

end SlopeTestRemainingChoices

theorem lev_iff_frames : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)), GlobalTheory.Mem.Col2.ChEx.InvActs cq → ∀ (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)), bar r = C → ∀ (D : ∀ P : Q, Set (Sp X.E n)), cq r = D → ∀ (q : QLoc hc n Q (GlobalTheory.Mem.Col2.ChEx.cutQ Θ D)) {g s : GL (Fin n) (AfE X.F X.E)}, g ∈ UAd hc n → g * s ∈ UAd hc n → ∀ (p : DecoF X.E n ST SG Q), FrExact q g r.1.1 → FrExact q (g * s) p → (s ∈ levUQ hc n ST SG Q (chG Λ C) q ↔ ∃ κ : FrmG Λ Θ, ufGL X.E n κ.1 = 1 ∧ (ya Λ Θ κ r).1.1 = p ∧ bar (ya Λ Θ κ r) = bar r ∧ cq (ya Λ Θ κ r) = cq r) := by
  intro X n ST SG Q y _ hc cq hact Λ Θ r C hC D hD q g s hg hgs p hr hp
  have hmul : ∀ P : Q, q.at P (g * s) = q.at P g * q.at P s := fun P => by simp only [QLoc.at, map_mul]
  have hat : ∀ P : Q, bc (q.phi P) (qGL n (r.1.1.fr P)) * q.at P s = bc (q.phi P) (qGL n (p.fr P)) := fun P => by
    rw [← hr.2 P, ← hp.2 P, hmul]
  have hcq : ∀ κ : FrmG Λ Θ, (∀ P : Q, κ.2.2.1 P ∈ frStab P.1 (D P)) ↔ cq (ya Λ Θ κ r) = cq r := by
    intro κ
    rw [funext_iff]
    refine forall_congr' fun P => ?_
    rw [hact Λ Θ κ r P, hD, frStab_iff_image]
  constructor
  · intro hs
    obtain ⟨hsU, hsQ⟩ := (mem_levUQ q _).1 hs
    have h1 := act_of_mem hc n _ 1 hg ⟨s, hsU⟩
    rw [DecoSet.dia_one, DecoSet.dia_one, hr.1, hp.1] at h1
    have h2 := mem_chG.1 ((Formalism.L2.Col.levRed hc n ST SG _ ⟨s, hsU⟩)⁻¹).2
    have hN : ∀ (P : Q) (x : Sp X.E n), x ∈ p.deco.1.at P.1 ↔ x ∈ r.1.1.deco.1.at P.1 := by
      intro P x
      rw [h1]
      exact (mem_localization_gmap P.1 ((1 : UF X.E n) : Sp X.E n ≃ₗ[X.E] Sp X.E n) r.1.1.deco.1.N x).trans Iff.rfl
    let t : GLQ X.E n Q := fun P => ⟨(r.1.1.fr P)⁻¹ * p.fr P, by
      show ∀ x, _ ↔ _
      intro x
      have A := r.1.1.2 P (((r.1.1.fr P)⁻¹ * p.fr P) x)
      have e : r.1.1.1.2 P (((r.1.1.fr P)⁻¹ * p.fr P) x) = p.fr P x := LinearEquiv.apply_symm_apply _ _
      rw [e] at A
      exact A.symm.trans ((hN P _).symm.trans (p.2 P x))⟩
    have hs_at : ∀ P : Q, q.at P s = bc (q.phi P) (qGL n (t P).1) := fun P => by
      rw [eq_inv_mul_of_mul_eq (hat P)]
      show _ = bc (q.phi P) (qGL n ((r.1.1.fr P)⁻¹ * p.fr P))
      simp only [qGL, map_mul, map_inv]
    have ht : ∀ P : Q, t P ∈ (cutQ Θ D P).H := fun P => by
      refine (q.U_rat P (t P)).1 ?_
      have h' := hsQ P
      rw [hs_at P] at h'
      exact h'
    have hθ : (fun P => (t P)⁻¹ : GLQ X.E n Q) ∈ Θ.grp := fun P _ => inv_mem (Subgroup.mem_inf.1 (ht P)).1
    let κ : FrmG Λ Θ := (1, ⟨_, h2.1⟩, ⟨_, hθ⟩)
    refine ⟨κ, map_one _, ?_, (bar_ya_eq_iff _ _ _ _).2 ?_, (hcq κ).1 fun P => inv_mem (Subgroup.mem_inf.1 (ht P)).2⟩
    · apply Subtype.ext
      apply Prod.ext
      · exact h1.symm
      · funext P
        show 1 * r.1.1.1.2 P * (((t P)⁻¹)⁻¹).1 = p.1.2 P
        rw [inv_inv, one_mul]
        exact mul_inv_cancel_left (r.1.1.fr P) (p.fr P)
    · rw [hC]
      exact h2.2
  · rintro ⟨⟨γ, h, θ⟩, h1, h2, h3, h4⟩
    have : γ = 1 := ufGL_inj hc n (h1.trans (map_one _).symm)
    subst this
    have hdeco : p.deco = ((1 : UF X.E n), h.1) • r.1.1.deco := by
      rw [← h2]
      rfl
    obtain ⟨hJ, hred⟩ := red_of_act hc n 1 hg hgs h.1 (by rw [DecoSet.dia_one, DecoSet.dia_one, hr.1, hp.1, hdeco])
    have hsU : s ∈ levU hc n ST SG (chG Λ C) := (mem_levU hc n ST SG _).2 ⟨hJ, by
      rw [hred]
      refine inv_mem (mem_chG.2 ⟨h.2, ?_⟩)
      rw [← hC]
      exact (bar_ya_eq_iff _ _ _ _).1 h3⟩
    refine (mem_levUQ q _).2 ⟨hsU, fun P => ?_⟩
    have hfr : p.fr P = r.1.1.fr P * ((θ.1 P)⁻¹).1 := by
      rw [← h2]
      show 1 * r.1.1.1.2 P * ((θ.1 P)⁻¹).1 = _
      rw [one_mul]
      rfl
    have hs_at : q.at P s = bc (q.phi P) (qGL n ((θ.1 P)⁻¹).1) := by
      rw [eq_inv_mul_of_mul_eq (hat P), hfr]
      simp only [qGL, map_mul, map_inv, inv_mul_cancel_left]
    rw [hs_at]
    refine (q.U_rat P ((θ.1 P)⁻¹)).2 ?_
    exact inv_mem (Subgroup.mem_inf.2 ⟨θ.2 P trivial, (hcq (1, h, θ)).2 h4 P⟩)

end GlobalTheory.Mem.Col2.ChEx
