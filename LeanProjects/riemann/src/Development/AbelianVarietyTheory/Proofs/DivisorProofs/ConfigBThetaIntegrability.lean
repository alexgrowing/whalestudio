import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.FrobInfLin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_quot {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_quot {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isPair_big {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_quot h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    resEtaPow_quot h.chars.resβ h.chars.resα rfl, h.weil⟩

theorem isFrobInf_sub_smul : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ φ φ' : R.Pi →ₗ[ℂ] R₁.Pi, IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2) φ →
        IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2) φ' → ∀ c : ℂ,
        IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2) (φ' - c • φ) := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' _ X om om' R Rf om₁ om₁' R₁ Rf₁ _ hM₁ φ φ' hφ hφ' c
  have act := GlobalTheory.T.polynomial_datum_action_of_pair hK.base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (isPair_big hM₁.triple)
  have onto : ∀ y : R₁.Pi, ∃ g ∈ G₁.M.Pol B.ψ B.emb, R₁.p g = y := fun y => by
    have : y ∈ (G₁.M.Pol B.ψ B.emb).map R₁.p := hM₁.real.quot.onto ▸ Submodule.mem_top
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 this
    exact ⟨g, hg, e⟩
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ hu f hf f₁ hf₁
    simp [hφ.unip γ hγ hu f hf f₁ hf₁, hφ'.unip γ hγ hu f hf f₁ hf₁]
  · intro γ hγ γ₁ hγ₁ t ht f hf f₁ hf₁ g hg g₁ hg₁ he c₀ hd
    obtain ⟨D, hDm, hDi⟩ := act.2.2.1 γ₁ hγ₁
    obtain ⟨g', hg', e'⟩ := onto (φ (R.p f))
    have hgs : g + c • g' ∈ G₁.M.Pol B.ψ B.emb := Submodule.add_mem _ hg (Submodule.smul_mem _ c hg')
    have he2 : φ' (R.p f) = R₁.p (g + c • g') := by
      rw [map_add, map_smul, e', ← he]; simp
    have h1 := hφ'.lie γ hγ γ₁ hγ₁ t ht f hf f₁ hf₁ (g + c • g') hgs (D (g + c • g'))
      ((hDi _ hgs _).2 rfl) he2 c₀ hd
    have h2 := hφ.lie γ hγ γ₁ hγ₁ t ht f hf f₁ hf₁ g' hg' (D g') ((hDi _ hg' _).2 rfl) e'.symm c₀ hd
    have h3 : g₁ = D g := (hDi g hg g₁).1 hg₁
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, h1, h2, h3, map_add, map_smul]
    module
  · intro k hk t k₁ ht hk₁ f hf f₁ hf₁ g hg g₁ hg₁ he
    obtain ⟨D, hDm, hDi⟩ := act.2.2.2 k₁ hk₁
    obtain ⟨g', hg', e'⟩ := onto (φ (R.p f))
    have hgs : g + c • g' ∈ G₁.M.Pol B.ψ B.emb := Submodule.add_mem _ hg (Submodule.smul_mem _ c hg')
    have he2 : φ' (R.p f) = R₁.p (g + c • g') := by
      rw [map_add, map_smul, e', ← he]; simp
    have h1 := hφ'.cpt k hk t k₁ ht hk₁ f hf f₁ hf₁ (g + c • g') hgs (D (g + c • g'))
      ((hDi _ hgs _).2 rfl) he2
    have h2 := hφ.cpt k hk t k₁ ht hk₁ f hf f₁ hf₁ g' hg' (D g') ((hDi _ hg' _).2 rfl) e'.symm
    have h3 : g₁ = D g := (hDi g hg g₁).1 hg₁
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, h1, h2, h3, map_add, map_smul]
    module

end GlobalTheory.FrobInfLin
