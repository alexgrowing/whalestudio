import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCompactOpenLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitUnipotentFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumInvariantNonsplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedLocalThetaEigenStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.IndLine.AlphaInert
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_uAt {n : ℕ} (X : Spc F E n) (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
  intro u _
  show u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
  simp

theorem mul_mem_uAt {n : ℕ} {X : Spc F E n} {v : Pl F} {g h : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v))
    (hh : h ∈ UAt σ X (evFin F v)) : g * h ∈ UAt σ X (evFin F v) := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    show mat g * mat h - 1 = _
    noncomm_ring
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

end GlobalTheory.IndLine.AlphaInert

noncomputable section
namespace GlobalTheory.IndLine.AlphaInert
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open GlobalTheory.ThK.LocalOps in

theorem indLine : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → IndLineFin v om om₁ (Rf.p v) (Rf₁.p v) H' X.α ((a' : ℝ) / 2) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ v hv
  have hvT : v ∉ X.T := fun h => hv.false (B.τ ⟨v, hM.triple.chars.sub h⟩)
  have hvac : G.M.vac v ∈ SB _ := (hM.triple.geo.hM.vac v).1
  have hvac₁ : G₁.M.vac v ∈ SB _ := (hM₁.triple.geo.hM.vac v).1
  have hx₀ : Rf.p v (G.M.vac v) ≠ 0 := (hM.fin.sph v hvT).2
  have iw := GlobalTheory.T.nonsplit_unipotent_factor F E σ B _ _ G.W G₁.W H' 0 (b + 1) _ _ _ _ hM.triple.base hM.triple.geo.hW hM₁.triple.geo.hW hC.hH' v hv
  have vf := GlobalTheory.T.vacuum_invariant_nonsplit_place hKP F E σ B (b + 2) a' G X om om' hM.triple v hv hvT
  have lk := GlobalTheory.T.levi_compact_open_lift F E σ B _ _ G.W G₁.W H' 0 (b + 1) _ _ _ _ hM.triple.base hM.triple.geo.hW hM₁.triple.geo.hW hC.hH' v
  have sl := GlobalTheory.T.unramified_local_theta_eigen hKP F E σ B b a' G₁ X om₁ om₁' R₁ Rf₁ hM₁ v hv hvT
  have hP₁ : IsPair B G₁.M X.β (X.β / X.α) om₁ (b - G₁.p) G₁.p (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) :=
    ⟨hM₁.triple.base, hM₁.triple.geo.hV, hM₁.triple.geo.hW, hM₁.triple.geo.hM, hM₁.triple.chars.heckeβ,
      ⟨hM₁.triple.chars.heckeβ.1.div' hM₁.triple.chars.heckeα.1, fun x => by
        rw [MonoidHom.div_apply, hM₁.triple.chars.heckeβ.2 x, hM₁.triple.chars.heckeα.2 x, div_one]⟩,
      hM₁.triple.chars.resβ, ?resW, hM₁.triple.weil⟩
  case resW =>
    intro x
    have e₁ := hM₁.triple.chars.resβ x
    have e₂ := hM₁.triple.chars.resα x
    have hpar : ((-1 : ℂ)) ^ b = (-1) ^ a' := by
      rcases Nat.even_or_odd b with h | h
      · have h' : Even a' := (Nat.even_add.mp hM₁.triple.geo.even).mp h
        rw [h.neg_one_pow, h'.neg_one_pow]
      · have h' : Odd a' := by
          rcases Nat.even_or_odd a' with h'' | h''
          · exact absurd ((Nat.even_add.mp hM₁.triple.geo.even).mpr h'') (Nat.not_even_iff_odd.mpr h)
          · exact h''
        rw [h.neg_one_pow, h'.neg_one_pow]
    rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂, hM₁.triple.geo.even.neg_one_pow]
    split_ifs
    · simp
    · rw [hpar, div_self (pow_ne_zero _ (by norm_num))]

  have key1 : ∀ A, IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.α ((a' : ℝ) / 2) A →
      ∃ c : ℂ, A (Rf.p v (G.M.vac v)) 1 = c • Rf₁.p v (G₁.M.vac v) := by
    intro A hA
    apply sl
    intro k hk φ hφ φ₁ hφ₁ hact hp
    obtain ⟨m, hm, hL⟩ := lk k hk
    have h1 := hA.levi 1 k m hL hm.1 hk.1 φ hφ φ₁ hφ₁ hact _ 1 (one_mem_uAt _ v) hp.symm
    have h2 := hA.right m hm.1 _ hvac _ hvac (vf m hm) 1 (one_mem_uAt _ v)
    rw [one_mul] at h2
    rw [mul_one] at h1
    simpa [h1] using h2.symm

  have key2 : ∀ g ∈ UAt σ G.W (evFin F v), ∃ Ψ : Rf₁.Pi v, ∀ A,
      IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.α ((a' : ℝ) / 2) A →
      ∀ c : ℂ, A (Rf.p v (G.M.vac v)) 1 = c • Rf₁.p v (G₁.M.vac v) → A (Rf.p v (G.M.vac v)) g = c • Ψ := by
    intro g hg
    obtain ⟨u, hu, huU, t, h₁, m, hL, hmU, hh₁U, k, hk, rfl⟩ := iw g hg
    obtain ⟨ψ₁, hψ₁, hact⟩ := acts_exists hP₁ v (1, h₁) (one_mem_uAt _ v) hh₁U _ hvac₁
    refine ⟨((X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ)) • Rf₁.p v ψ₁, fun A hA c hc => ?_⟩
    have hact' : Acts (evFin F v) (om₁ (1, h₁)) (c • G₁.M.vac v) (c • ψ₁) := by
      have := acts_lin v (om₁ (1, h₁)) (fun φ hφ => acts_exists hP₁ v (1, h₁) (one_mem_uAt _ v) hh₁U φ hφ)
        hvac₁ hvac₁ hact hact c 0
      simpa using this
    rw [← hA.right k hk.1 _ hvac _ hvac (vf k hk) (u * m) (mul_mem_uAt huU hmU), hA.unip u hu huU _ m hmU]
    have h3 := hA.levi t h₁ m hL hmU hh₁U (c • G₁.M.vac v) ((SB _).smul_mem c hvac₁) (c • ψ₁)
      ((SB _).smul_mem c hψ₁) hact' _ 1 (one_mem_uAt _ v) (hc.trans (map_smul (Rf₁.p v) c _).symm)
    rw [mul_one] at h3
    rw [h3, map_smul, smul_comm]

  have span : ∀ A₁ A₂, IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.α ((a' : ℝ) / 2) A₁ →
      IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.α ((a' : ℝ) / 2) A₂ → ∀ r : ℂ,
      (∀ h ∈ UAt σ G.W (evFin F v), A₁ (Rf.p v (G.M.vac v)) h = r • A₂ (Rf.p v (G.M.vac v)) h) →
      ∀ x, ∀ h ∈ UAt σ G.W (evFin F v), A₁ x h = r • A₂ x h := by
    intro A₁ A₂ hA₁ hA₂ r h0
    let N : Submodule ℂ (Rf.Pi v) :=
      { carrier := {x | ∀ h ∈ UAt σ G.W (evFin F v), A₁ x h = r • A₂ x h}
        add_mem' := fun {x y} hx hy h hh => by
          simp only [map_add, Pi.add_apply, hx h hh, hy h hh, smul_add]
        zero_mem' := fun h _ => by simp
        smul_mem' := fun c x hx h hh => by
          simp only [map_smul, Pi.smul_apply, hx h hh, smul_comm c r] }
    have hstab : ∀ h' ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
        Acts (evFin F v) (om (1, h')) φ φ₁ → Rf.p v φ ∈ N → Rf.p v φ₁ ∈ N := by
      intro h' hh' φ hφ φ₁ hφ₁ hact hmem h hh
      rw [hA₁.right h' hh' φ hφ φ₁ hφ₁ hact h hh, hA₂.right h' hh' φ hφ φ₁ hφ₁ hact h hh]
      exact hmem _ (mul_mem_uAt hh hh')
    rcases hM.fin.irred v N hstab with hN | hN
    · exact absurd ((Submodule.eq_bot_iff N).1 hN _ h0) hx₀
    · intro x h hh
      have : x ∈ N := hN ▸ Submodule.mem_top
      exact this h hh
  intro A A' hA hA'
  obtain ⟨c, hc⟩ := key1 A hA
  obtain ⟨c', hc'⟩ := key1 A' hA'
  by_cases h0 : c = 0
  · left
    intro x h hh
    have := span A A hA hA 0 (fun g hg => by
      obtain ⟨Ψ, hΨ⟩ := key2 g hg
      rw [hΨ A hA c hc, h0, zero_smul, zero_smul]) x h hh
    simpa using this
  · right
    refine ⟨c' / c, fun x h hh => span A' A hA' hA (c' / c) (fun g hg => ?_) x h hh⟩
    obtain ⟨Ψ, hΨ⟩ := key2 g hg
    rw [hΨ A' hA' c' hc', hΨ A hA c hc, smul_smul, div_mul_cancel₀ _ h0]
end GlobalTheory.IndLine.AlphaInert
