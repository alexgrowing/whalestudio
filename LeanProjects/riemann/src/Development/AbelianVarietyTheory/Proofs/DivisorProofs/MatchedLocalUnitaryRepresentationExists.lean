import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.SphLine

section Local

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem acts_one_loc (v : Pl F) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (1 : Module.End ℂ ((κ → AF F) → ℂ)) φ φ := fun _ _ => rfl

theorem acts_mul_loc (v : Pl F) {T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)}
    (h₁ : ∀ Φ ∈ schA F κ, T₁ Φ ∈ schA F κ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (a : Acts (evFin F v) T₁ φ φ₁) (b : Acts (evFin F v) T₂ φ₁ φ₂) :
    Acts (evFin F v) (T₂ * T₁) φ φ₂ := by
  intro r hr
  have hr1 : Rest (evFin F v) φ₁ r := ⟨hr.1, by rw [← a r hr]; exact h₁ _ hr.2⟩
  show T₂ (T₁ _) = _
  rw [a r hr, b r hr1]

theorem acts_lin_loc (v : Pl F) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hex : ∀ φ ∈ SB (κ → Fv F v), ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) T φ φ₁)
    {φ ψ φ₁ ψ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) (hψ : ψ ∈ SB (κ → Fv F v))
    (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T ψ ψ₁) (a b : ℂ) :
    Acts (evFin F v) T (a • φ + b • ψ) (a • φ₁ + b • ψ₁) := by
  have hs : a • φ + b • ψ ∈ SB (κ → Fv F v) :=
    add_mem ((SB _).smul_mem a hφ) ((SB _).smul_mem b hψ)
  obtain ⟨χ, -, hχ⟩ := hex _ hs
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have e : tens (evFin F v) (a • φ + b • ψ) R = a • tens (evFin F v) φ R + b • tens (evFin F v) ψ R := by
    funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e' : tens (evFin F v) (a • φ₁ + b • ψ₁) R = a • tens (evFin F v) φ₁ R + b • tens (evFin F v) ψ₁ R := by
    funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have key : tens (evFin F v) χ R = tens (evFin F v) (a • φ₁ + b • ψ₁) R := by
    rw [← hχ R (hR _ hs), e, map_add, map_smul, map_smul, h₁ R (hR φ hφ), h₂ R (hR ψ hψ), e']
  have hχe : χ = a • φ₁ + b • ψ₁ := by
    funext t
    have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
      intro u' hu'; funext i; exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    have hRz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
      simpa using (hR φ hφ).1 0 _ hz
    have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (t i))
    simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
    exact mul_right_cancel₀ hR0 this
  rw [← hχe]
  exact hχ

end Local

theorem exists_locRep : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ v : Pl F,
    ∃ ρ : Representation ℂ (GlobalTheory.SphLine.locU σ G.W v) (Rf.Pi v),
      (∀ h : GlobalTheory.SphLine.locU σ G.W v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, (h : UA σ G.W.J))) φ φ₁) ∧
      ∀ h : GlobalTheory.SphLine.locU σ G.W v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, (h : UA σ G.W.J))) φ φ₁ → ρ h (Rf.p v φ) = Rf.p v φ₁ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM v
  have hAE := GlobalTheory.T.theta_action_exists hKP.base
  have hP := GlobalTheory.ThK.Inhab.pairV hM.triple
  have hP' := GlobalTheory.ThK.Inhab.pairV' hM.triple
  have h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := (locU σ G.V v).one_mem
  have h1V' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := (locU σ G.V' v).one_mem
  have ex : ∀ h : locU σ G.W v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, (h : UA σ G.W.J))) φ φ₁ := by
    intro h φ hφ
    obtain ⟨φ₁, ⟨k1, k2⟩, -⟩ := (hAE F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP v).1 1 h1V h h.2 φ hφ
    exact ⟨φ₁, k1, k2⟩
  have ex' : ∀ h : locU σ G.W v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, (h : UA σ G.W.J))) φ φ₁ := by
    intro h φ hφ
    obtain ⟨φ₁, ⟨k1, k2⟩, -⟩ := (hAE F E σ B a' (a + a') G.V' G.W G.M' _ _ om' _ _ _ _ hP' v).1 1 h1V' h h.2 φ hφ
    exact ⟨φ₁, k1, k2⟩
  have wd : ∀ h : locU σ G.W v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ ψ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ ψ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, (h : UA σ G.W.J))) φ φ₁ → Acts (evFin F v) (om (1, (h : UA σ G.W.J))) ψ ψ₁ →
      Rf.p v φ = Rf.p v ψ → Rf.p v φ₁ = Rf.p v ψ₁ := by
    intro h φ hφ ψ hψ φ₁ hφ₁ ψ₁ hψ₁ a1 a2 e
    have hm : Rf.p v φ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Rf.p' v) := by
      rw [hM.fin.onto' v]; trivial
    obtain ⟨φ', hφ', e'⟩ := Submodule.mem_map.1 hm
    obtain ⟨φ₁', hφ₁', a3⟩ := ex' h φ' hφ'
    have k1 := hM.fin.equiv v h h.2 φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' a1 a3 e'.symm
    have k2 := hM.fin.equiv v h h.2 ψ hψ φ' hφ' ψ₁ hψ₁ φ₁' hφ₁' a2 a3 (e.symm.trans e'.symm)
    exact k1.trans k2.symm
  have pre : ∀ x : Rf.Pi v, ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v φ = x := by
    intro x
    have hm : x ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by
      rw [hM.fin.onto v]; trivial
    exact Submodule.mem_map.1 hm
  obtain ⟨g, hg⟩ : ∃ g : locU σ G.W v → Rf.Pi v → Rf.Pi v, ∀ h : locU σ G.W v,
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, (h : UA σ G.W.J))) φ φ₁ → g h (Rf.p v φ) = Rf.p v φ₁ := by
    choose φof hφof hpφ using pre
    choose φ1 hφ1 hact using ex
    refine ⟨fun h x => Rf.p v (φ1 h (φof x) (hφof x)), fun h φ hφ φ₁ hφ₁ ac => ?_⟩
    exact wd h _ (hφof _) φ hφ _ (hφ1 _ _ _) φ₁ hφ₁ (hact _ _ _) ac (hpφ _)
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  have glin : ∀ h (c d : ℂ) x y, g h (c • x + d • y) = c • g h x + d • g h y := by
    intro h c d x y
    obtain ⟨φ, hφ, rfl⟩ := pre x
    obtain ⟨ψ, hψ, rfl⟩ := pre y
    obtain ⟨φ₁, hφ₁, a1⟩ := ex h φ hφ
    obtain ⟨ψ₁, hψ₁, a2⟩ := ex h ψ hψ
    have l := acts_lin_loc v _ (ex h) hφ hψ a1 a2 c d
    have hs : c • φ + d • ψ ∈ SB (Fin a × Fin (a + a') → Fv F v) :=
      add_mem ((SB _).smul_mem c hφ) ((SB _).smul_mem d hψ)
    have hs1 : c • φ₁ + d • ψ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v) :=
      add_mem ((SB _).smul_mem c hφ₁) ((SB _).smul_mem d hψ₁)
    have e := hg h _ hs _ hs1 l
    rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul] at e
    rw [e, hg h φ hφ φ₁ hφ₁ a1, hg h ψ hψ ψ₁ hψ₁ a2]
  have gone : ∀ x, g 1 x = x := by
    intro x
    obtain ⟨φ, hφ, rfl⟩ := pre x
    have ac : Acts (evFin F v) (om (1, ((1 : locU σ G.W v) : UA σ G.W.J))) φ φ := by
      rw [show ((1, ((1 : locU σ G.W v) : UA σ G.W.J)) : UA σ G.V.J × UA σ G.W.J) = 1 from rfl, map_one]
      exact acts_one_loc v φ
    exact hg 1 φ hφ φ hφ ac
  have gmul : ∀ h h' x, g (h * h') x = g h (g h' x) := by
    intro h h' x
    obtain ⟨φ, hφ, rfl⟩ := pre x
    obtain ⟨φ₁, hφ₁, a1⟩ := ex h' φ hφ
    obtain ⟨φ₂, hφ₂, a2⟩ := ex h φ₁ hφ₁
    have ac : Acts (evFin F v) (om (1, ((h * h' : locU σ G.W v) : UA σ G.W.J))) φ φ₂ := by
      rw [show ((1, ((h * h' : locU σ G.W v) : UA σ G.W.J)) : UA σ G.V.J × UA σ G.W.J) =
          (1, (h : UA σ G.W.J)) * (1, (h' : UA σ G.W.J)) from Prod.ext (mul_one 1).symm rfl, map_mul]
      exact acts_mul_loc v (fun Φ hΦ => hW.pres _ Φ hΦ) a1 a2
    rw [hg _ φ hφ φ₂ hφ₂ ac, hg h' φ hφ φ₁ hφ₁ a1, hg h φ₁ hφ₁ φ₂ hφ₂ a2]
  let ρ : Representation ℂ (locU σ G.W v) (Rf.Pi v) :=
    { toFun := fun h =>
        { toFun := g h
          map_add' := fun x y => by simpa using glin h 1 1 x y
          map_smul' := fun c x => by simpa using glin h c 0 x 0 }
      map_one' := LinearMap.ext gone
      map_mul' := fun h h' => LinearMap.ext (gmul h h') }
  exact ⟨ρ, ex, hg⟩

end GlobalTheory.SphLine

end
