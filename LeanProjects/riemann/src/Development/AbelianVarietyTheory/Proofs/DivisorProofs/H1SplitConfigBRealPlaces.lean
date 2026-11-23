import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompNonsplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMaximalCompactExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactFixesVacuumNonsplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaNonsplitInvariantStatement

noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

section Helpers

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt_loc {n : ℕ} (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) :
    (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

theorem mul_mem_UAt_loc {n : ℕ} {Y : Spc F E n} {R : Type} [Zero R] {ev : AF F → R} {g h : UA σ Y.J}
    (hg : g ∈ UAt σ Y ev) (hh : h ∈ UAt σ Y ev) : g * h ∈ UAt σ Y ev := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    simp only [mat, Subgroup.coe_mul, Units.val_mul]; noncomm_ring
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem acts_smul_loc {κ : Type} [Fintype κ] {v : Pl F} (T : Module.End ℂ ((κ → AF F) → ℂ))
    {φ φ₁ : (κ → Fv F v) → ℂ} (h : Acts (evFin F v) T φ φ₁) (c : ℂ) :
    Acts (evFin F v) T (c • φ) (c • φ₁) := by
  intro r hr
  have e : ∀ ψ : (κ → Fv F v) → ℂ, tens (evFin F v) (c • ψ) r = c • tens (evFin F v) ψ r := by
    intro ψ; funext x; simp [tens, mul_assoc]
  rw [e, e]
  by_cases hc : c = 0
  · subst hc; simp
  · have hr' : Rest (evFin F v) φ r := ⟨hr.1, by
      have := (schA F κ).smul_mem c⁻¹ hr.2
      rwa [e, smul_smul, inv_mul_cancel₀ hc, one_smul] at this⟩
    rw [map_smul, h r hr']

end Helpers

theorem indLineFin_beta_inert : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → IndLineFin v om om₁ (Rf.p v) (Rf₁.p v) H' X.β ((a : ℝ) / 2) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ v hv
  have hvT : v ∉ X.T := fun h => hv.1 (B.τ ⟨v, hM.triple.chars.sub h⟩)
  have hvac : G.M.vac v ∈ SB _ := (hM.triple.geo.hM.vac v).1
  have hvac₁ : G₁.M.vac v ∈ SB _ := (hM₁.triple.geo.hM.vac v).1
  have hpvac : Rf.p v (G.M.vac v) ≠ 0 := (hM.fin.sph v hvT).2
  have hK := GlobalTheory.T.compact_fixes_vacuum_nonsplit F E σ B _ _ G X om om' hM.triple v hv hvT
  have hIw := GlobalTheory.T.iwasawa_decomp_nonsplit_place F E σ B _ _ G.W G₁.W H' _ _ _ _ _ _ hM.triple.base hM.triple.geo.hW hM₁.triple.geo.hW hC.hH' v hv
  have hLv := GlobalTheory.T.levi_maximal_compact_exists F E σ B _ _ G.W G₁.W H' _ _ _ _ _ _ hM.triple.base hM.triple.geo.hW hM₁.triple.geo.hW hC.hH' v
  have hSph := GlobalTheory.T.local_theta_nonsplit_invariant hKP F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ hM₁ v hv
  have hEx : ∀ h₁ ∈ UAt σ G₁.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + b) → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + b) → Fv F v), Acts (evFin F v) (om₁ (1, h₁)) φ φ₁ := by
    intro h₁ hh₁ φ hφ
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := ((GlobalTheory.T.theta_action_exists hKP.base) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (GlobalTheory.ThK.Inhab.pairV hM₁.triple) v).1 1 (one_mem_UAt_loc _ _) h₁ hh₁ φ hφ
    exact ⟨φ₁, h1, h2⟩
  have step1 : ∀ A : Rf.Pi v →ₗ[ℂ] (UA σ G.W.J → Rf₁.Pi v),
      IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.β ((a : ℝ) / 2) A →
      ∃ c : ℂ, A (Rf.p v (G.M.vac v)) 1 = Rf₁.p v (c • G₁.M.vac v) := by
    intro A hA
    obtain ⟨φ, hφ, hφe⟩ : ∃ φ ∈ SB (Fin a × Fin (a + b) → Fv F v), Rf₁.p v φ = A (Rf.p v (G.M.vac v)) 1 := by
      have : A (Rf.p v (G.M.vac v)) 1 ∈ (SB _).map (Rf₁.p v) := by rw [hM₁.fin.onto v]; trivial
      simpa using this
    obtain ⟨c, hc⟩ := hSph φ hφ (by
      intro k₁ hk₁ φ₁ hφ₁ hact
      obtain ⟨m, hm, hlev⟩ := hLv k₁ hk₁
      have e1 := hA.levi 1 k₁ m hlev hm.1 hk₁.1 φ hφ φ₁ hφ₁ hact (Rf.p v (G.M.vac v)) 1
        (one_mem_UAt_loc _ _) hφe.symm
      have e2 := hA.right m hm.1 _ hvac _ hvac (hK m hm) 1 (one_mem_UAt_loc _ _)
      simp only [mul_one, one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one,
        one_smul] at e1 e2
      rw [← e1, ← e2, hφe])
    exact ⟨c, by rw [← hφe, hc, map_smul]⟩
  have step2 : ∀ h ∈ UAt σ G.W (evFin F v), ∃ w : Rf₁.Pi v, ∀ A : Rf.Pi v →ₗ[ℂ] (UA σ G.W.J → Rf₁.Pi v),
      IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.β ((a : ℝ) / 2) A → ∀ c : ℂ,
      A (Rf.p v (G.M.vac v)) 1 = Rf₁.p v (c • G₁.M.vac v) → A (Rf.p v (G.M.vac v)) h = c • w := by
    intro h hh
    obtain ⟨n, m, k, t, h₁, hn, hnv, hmv, hh₁, hlev, hk, rfl⟩ := hIw h hh
    obtain ⟨φ₁, hφ₁, hact⟩ := hEx h₁ hh₁ _ hvac₁
    refine ⟨((X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)) • Rf₁.p v φ₁, ?_⟩
    intro A hA c hc
    have hmk : m * k ∈ UAt σ G.W (evFin F v) := mul_mem_UAt_loc hmv hk.1
    have e0 : A (Rf.p v (G.M.vac v)) k = Rf₁.p v (c • G₁.M.vac v) := by
      have := hA.right k hk.1 _ hvac _ hvac (hK k hk) 1 (one_mem_UAt_loc _ _)
      rw [one_mul] at this
      rw [← this, hc]
    have e1 := hA.levi t h₁ m hlev hmv hh₁ (c • G₁.M.vac v) (Submodule.smul_mem _ c hvac₁) (c • φ₁)
      (Submodule.smul_mem _ c hφ₁) (acts_smul_loc _ hact c) _ k hk.1 e0
    have e2 := hA.unip n hn hnv (Rf.p v (G.M.vac v)) (m * k) hmk
    rw [mul_assoc, e2, e1, map_smul, smul_comm]
  have key : ∀ (A₁ A₂ : Rf.Pi v →ₗ[ℂ] (UA σ G.W.J → Rf₁.Pi v)),
      IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.β ((a : ℝ) / 2) A₁ →
      IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.β ((a : ℝ) / 2) A₂ → ∀ c₀ : ℂ,
      (∀ h ∈ UAt σ G.W (evFin F v), A₂ (Rf.p v (G.M.vac v)) h = c₀ • A₁ (Rf.p v (G.M.vac v)) h) →
      ∀ x, ∀ h ∈ UAt σ G.W (evFin F v), A₂ x h = c₀ • A₁ x h := by
    intro A₁ A₂ hA₁ hA₂ c₀ h0
    let P : Rf.Pi v → Prop := fun x => ∀ h ∈ UAt σ G.W (evFin F v), A₂ x h = c₀ • A₁ x h
    let N : Submodule ℂ (Rf.Pi v) :=
      { carrier := {x | P x}
        add_mem' := by
          intro x y hx hy h hh
          simp only [map_add, Pi.add_apply, hx h hh, hy h hh, smul_add]
        zero_mem' := by
          intro h hh; simp
        smul_mem' := by
          intro r x hx h hh
          simp only [map_smul, Pi.smul_apply, hx h hh, smul_comm r c₀] }
    have hmemN : ∀ x, x ∈ N ↔ P x := fun x => Iff.rfl
    have hN := hM.fin.irred v N (by
      intro g hg φ hφ φ₁ hφ₁ hact hmem
      rw [hmemN] at hmem ⊢
      intro h hh
      rw [hA₂.right g hg φ hφ φ₁ hφ₁ hact h hh, hA₁.right g hg φ hφ φ₁ hφ₁ hact h hh]
      exact hmem (h * g) (mul_mem_UAt_loc hh hg))
    rcases hN with hN | hN
    · exact absurd ((hmemN _).2 h0) (by rw [hN]; simpa using hpvac)
    · intro x; exact (hmemN x).1 (by rw [hN]; trivial)
  intro A A' hA hA'
  obtain ⟨c, hc⟩ := step1 A hA
  obtain ⟨c', hc'⟩ := step1 A' hA'
  by_cases h0 : c = 0
  · left
    intro x h hh
    have := key A A hA hA 0 (by
      intro h hh
      obtain ⟨w, hw⟩ := step2 h hh
      rw [hw A hA c hc, h0]; simp) x h hh
    simpa using this
  · right
    refine ⟨c' / c, key A A' hA hA' (c' / c) ?_⟩
    intro h hh
    obtain ⟨w, hw⟩ := step2 h hh
    rw [hw A hA c hc, hw A' hA' c' hc', smul_smul, div_mul_cancel₀ _ h0]

end GlobalTheory.IndLine
