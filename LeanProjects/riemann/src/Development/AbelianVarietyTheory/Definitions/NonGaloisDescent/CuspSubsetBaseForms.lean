import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverRead.Test

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

def idCov (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (nab : NabV (T.Q.Xo j) T.Q.c) : Cover T j σ where
  c' := T.Q.c
  hle := le_rfl
  d := GlobalTheory.RawSpan.idCover nab 0
  σ₂ := σ
  U₂ := T.U j σ
  dict₂ := T.dict j σ
  cc₂ := T.cE j σ

theorem idCov_rd (nab : NabV (T.Q.Xo j) T.Q.c) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    (idCov T j σ nab).rd a f = T.phiJ j σ a f := rfl

theorem idCov_ratForms (nab : NabV (T.Q.Xo j) T.Q.c) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    (idCov T j σ nab).ratForms a n = baseForms T j σ a n := rfl

theorem idCov_intForms (nab : NabV (T.Q.Xo j) T.Q.c) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) :
    (idCov T j σ nab).intForms a n S = baseInt T j σ a n S := by
  unfold Cover.intForms baseInt
  congr 1
  ext f
  exact and_assoc

theorem idCov_isUnif (h : LawsJ T) (hj : Formalism.L2.Pj.InR D j) (hσ : GoodEmb T.Q.c σ) (nab : NabV (T.Q.Xo j) T.Q.c) :
    (idCov T j σ nab).IsUnif := by
  obtain ⟨hr, g, e, F, ik, φ, th, -, -, h1, h2⟩ := h.adPin j hj σ hσ
  obtain ⟨hr', hm⟩ := h.modelW j hj σ hσ
  obtain ⟨_, _, -, hd⟩ := h.dictU j hj σ hσ
  exact ⟨GlobalTheory.RawSpan.idCover_isLev nab 0, h.pins.2.1.2, RingHom.ext fun _ => rfl, h.unf j hj σ hσ, hd.2.2.2.1,
    hr, g, e, F, ik, φ, th, hm, h1, h2⟩

theorem idCov_isPinned (h : LawsJ T) (hj : Formalism.L2.Pj.InR D j) (hσ : GoodEmb T.Q.c σ) (nab : NabV (T.Q.Xo j) T.Q.c)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : (idCov T j σ nab).IsPinned a n := by
  refine ⟨h.cUnit j hj σ hσ, fun f _ f₂ _ hp => ?_⟩
  have key : rdU (T.U j σ) f₂ = rdU (T.U j σ) f := by
    funext k x
    by_cases hx : x ∈ ((T.U j σ).X k).dom
    · have e := @hp ℂ _ σ.toAlgebra σ.toAlgebra σ.toAlgebra (fun _ => rfl) (fun _ => rfl) ((T.U j σ).un k ⟨x, hx⟩)
        ((T.U j σ).un k ⟨x, hx⟩) (GlobalTheory.RawSpan.frOver_self nab 0 ((T.U j σ).un k ⟨x, hx⟩))
      have r : ∀ u : T.R j, rdU (T.U j σ) u k x = toC (evR (T.Q.Xo j) T.Q.c u ((T.U j σ).un k ⟨x, hx⟩)) :=
        fun u => dif_pos hx
      exact (r f₂).trans (Eq.trans e (r f).symm)
    · exact (rdU_mem_offZero _ f₂ k x hx).trans (rdU_mem_offZero _ f k x hx).symm
  exact congrArg (fun P => (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ)) P) key

theorem rd_apply (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f₂ : Rul C.d.Xo₂ C.d.c₂) (g : GA D (T.V j σ)) :
    C.rd a f₂ g = C.cc₂ (C.dict₂ g).1 * ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) * T.mu j σ g *
      rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2) := by
  simp only [Cover.rd, Pi.smul_apply, smul_eq_mul, adel_muPin]
  ring

abbrev withC (C : Cover T j σ) (cc : C.U₂.Comp → ℂ) : Cover T j σ := { C with cc₂ := cc }

theorem isUnif_withC (C : Cover T j σ) (cc : C.U₂.Comp → ℂ) : (withC C cc).IsUnif ↔ C.IsUnif := Iff.rfl

theorem pinned_withC (C : Cover T j σ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (h : C.IsPinned a n)
    (cc : C.U₂.Comp → ℂ) (hc : CUnit cc)
    (hag : ∀ g, (∃ f ∈ sec (T.Q.Xo j) T.Q.c a n, T.phiJ j σ a f g ≠ 0) → cc (C.dict₂ g).1 = C.cc₂ (C.dict₂ g).1) :
    (withC C cc).IsPinned a n := by
  refine ⟨hc, fun f hf f₂ hf₂ hp => ?_⟩
  have e := h.2 f hf f₂ hf₂ hp
  funext g
  have e1 := congrFun e g
  rw [rd_apply] at e1
  rw [rd_apply]
  by_cases h0 : T.phiJ j σ a f g = 0
  · rw [h0] at e1 ⊢
    have hne : C.cc₂ (C.dict₂ g).1 ≠ 0 := fun hz => by simpa [hz] using h.1 (C.dict₂ g).1
    have := (mul_eq_zero.1 e1).resolve_left hne
    exact mul_eq_zero_of_right _ this
  · rw [← e1]
    exact congrArg (· * _) (hag g ⟨f, hf, h0⟩)

theorem pinned_unique (C : Cover T j σ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (h : C.IsPinned a n)
    (cc : C.U₂.Comp → ℂ) (h' : (withC C cc).IsPinned a n) {f : T.R j} (hf : f ∈ sec (T.Q.Xo j) T.Q.c a n)
    {f₂ : Rul C.d.Xo₂ C.d.c₂} (hf₂ : f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n) (hp : C.IsPull f f₂) {g : GA D (T.V j σ)}
    (hg : T.phiJ j σ a f g ≠ 0) : cc (C.dict₂ g).1 = C.cc₂ (C.dict₂ g).1 := by
  have e1 := congrFun (h.2 f hf f₂ hf₂ hp) g
  have e2 := congrFun (h'.2 f hf f₂ hf₂ hp) g
  rw [rd_apply] at e1 e2
  have hne : (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * T.mu j σ g * rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2 ≠ 0 :=
    fun hz => hg (by rw [← e1, hz, mul_zero])
  exact mul_right_cancel₀ hne (e2.trans e1.symm)

theorem cusp_subset_baseForms (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    T.phiJ j σ a '' (T.cuspA j a n : Set (T.R j)) ⊆ baseForms T j σ a n :=
  Set.image_mono fun f hf => ⟨((mem_cusp _ _ _ a n f).1 hf).1, ((mem_cusp _ _ _ a n f).1 hf).2 σ hσ, rdU_mem_offZero _ _⟩

theorem zero_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : 0 ∈ C.ratForms a n := by
  refine ⟨0, ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _⟩, ?_⟩
  funext g
  rw [rd_apply, map_zero]
  simp

theorem add_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {φ ψ : GA D (T.V j σ) → ℂ}
    (hφ : φ ∈ C.ratForms a n) (hψ : ψ ∈ C.ratForms a n) : φ + ψ ∈ C.ratForms a n := by
  obtain ⟨f, hf, rfl⟩ := hφ
  obtain ⟨f', hf', rfl⟩ := hψ
  refine ⟨f + f', ⟨Submodule.add_mem _ hf.1 hf'.1, by rw [map_add]; exact Submodule.add_mem _ hf.2 hf'.2⟩, ?_⟩
  funext g
  simp only [Pi.add_apply, rd_apply, map_add]
  ring

theorem smul_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : C.d.c₂.F)
    {φ : GA D (T.V j σ) → ℂ} (hφ : φ ∈ C.ratForms a n) : C.σ₂ x • φ ∈ C.ratForms a n := by
  obtain ⟨f, hf, rfl⟩ := hφ
  refine ⟨x • f, ⟨Submodule.smul_mem _ _ hf.1, by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hf.2⟩, ?_⟩
  funext g
  simp only [Pi.smul_apply, rd_apply, map_smulₛₗ, smul_eq_mul]
  ring

end GlobalTheory.CoverRead.Test
