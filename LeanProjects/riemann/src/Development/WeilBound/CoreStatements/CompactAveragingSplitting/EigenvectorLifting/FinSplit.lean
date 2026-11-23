import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

noncomputable section

namespace PositivityTheory.ThK

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

structure IsFinAt (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : FinMaps F a a') (v : Pl F) : Prop where
  onto : (SB _).map (R.p v) = ⊤
  onto' : (SB _).map (R.p' v) = ⊤
  inv : augAt om v ≤ LinearMap.ker (R.p v)
  inv' : augAt om' v ≤ LinearMap.ker (R.p' v)
  equiv : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
    Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
    R.p v φ = R.p' v φ' → R.p v φ₁ = R.p' v φ₁'
  nontriv : Nontrivial (R.Pi v)
  irred : ∀ N : Submodule ℂ (R.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
    Acts (evFin F v) (om (1, h)) φ φ₁ → R.p v φ ∈ N → R.p v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤
  sph : v ∉ X.T → R.p v (G.M.vac v) = R.p' v (G.M'.vac v) ∧ R.p v (G.M.vac v) ≠ 0
  zeta : ∀ hv : v ∈ B.P, v ∈ X.T → IsZetaAt B G X R ⟨v, hv⟩

def FinAt (Q : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Chars F E → Pl F → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∀ v, Q F E X v →
      ∃ R, IsFinAt B G X om om' R v

def FinRam : Prop := FinAt fun _ _ _ _ _ _ _ X v => v ∈ X.T

def FinSplit : Prop := FinAt fun F E _ _ _ _ _ X v => v ∉ X.T ∧ Nonempty (E →ₐ[F] Fv F v)

def FinInert : Prop := FinAt fun F E _ _ _ _ _ X v => v ∉ X.T ∧ IsEmpty (E →ₐ[F] Fv F v)

theorem kFin_of (h1 : FinRam) (h2 : FinSplit) (h3 : FinInert) : GlobalTheory.ThK.KFin := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT
  have h : ∀ v, ∃ R, IsFinAt B G X om om' R v := fun v => by
    by_cases hv : v ∈ X.T
    · exact h1 F E σ B a a' G X om om' hT v hv
    · rcases isEmpty_or_nonempty (E →ₐ[F] Fv F v) with he | he
      · exact h3 F E σ B a a' G X om om' hT v ⟨hv, he⟩
      · exact h2 F E σ B a a' G X om om' hT v ⟨hv, he⟩
  choose R hR using h
  exact ⟨{ Pi := fun v => (R v).Pi v, p := fun v => (R v).p v, p' := fun v => (R v).p' v },
    fun v => (hR v).onto, fun v => (hR v).onto', fun v => (hR v).inv, fun v => (hR v).inv', fun v => (hR v).equiv,
    fun v => (hR v).nontriv, fun v => (hR v).irred, fun v => (hR v).sph, fun v hv => (hR v.1).zeta v.2 hv⟩

end PositivityTheory.ThK
