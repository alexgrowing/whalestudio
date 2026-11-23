import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne

noncomputable section

namespace GlobalTheory.TwistedRepresentationEmbedding

open Module

def twist {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V) (χ : G →* Kˣ) :
    Representation K G V where
  toFun g := ((χ g : Kˣ) : K) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul, smul_smul]
    ring_nf

theorem twist_apply {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (χ : G →* Kˣ) (g : G) (v : V) : twist ρ χ g v = ((χ g : Kˣ) : K) • ρ g v := rfl

def embV {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) : (Fin N → K) →ₛₗ[σ] (Fin N → ℂ) where
  toFun v k := σ (v k)
  map_add' v w := by funext k; simp
  map_smul' a v := by funext k; simp

def repE {K G : Type} [Field K] [Group G] {N : ℕ} (σ : K →+* ℂ) (ρ : Representation K G (Fin N → K)) :
    Representation ℂ G (Fin N → ℂ) where
  toFun g := Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map σ)
  map_one' := by
    rw [map_one, LinearMap.toMatrix'_one, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.toLin'_one]; rfl
  map_mul' g h := by
    rw [map_mul, LinearMap.toMatrix'_mul, Matrix.map_mul, Matrix.toLin'_mul]; rfl

theorem repE_embV {K G : Type} [Field K] [Group G] {N : ℕ} (σ : K →+* ℂ) (ρ : Representation K G (Fin N → K)) (g : G)
    (v : Fin N → K) : repE σ ρ g (embV σ N v) = embV σ N (ρ g v) := by
  funext k
  change (Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map σ)) (fun j => σ (v j)) k = σ (ρ g v k)
  have h := RingHom.map_mulVec σ (LinearMap.toMatrix' (ρ g)) v k
  rw [LinearMap.toMatrix'_mulVec] at h
  rw [Matrix.toLin'_apply, h]
  rfl

theorem embV_single {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) (k : Fin N) :
    embV σ N (Pi.single k 1) = Pi.single k 1 := by
  funext j
  change σ ((Pi.single k (1 : K) : Fin N → K) j) = (Pi.single k (1 : ℂ) : Fin N → ℂ) j
  by_cases h : j = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem embV_li {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) :
    LinearIndependent ℂ fun k => embV σ N (Pi.single k 1) := by
  convert (Pi.basisFun ℂ (Fin N)).linearIndependent using 1
  funext k
  simp [embV_single]

theorem embV_span {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) :
    Submodule.span ℂ (Set.range (embV σ N)) = ⊤ := by
  refine eq_top_iff.2 ((Pi.basisFun ℂ (Fin N)).span_eq.ge.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨Pi.single k 1, by simp [embV_single]⟩

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem isPullRep_twist {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U]
    [MulAction U C] {M : TwoLevels E r U C} {la : Wt M.Ψ r} {ρ : Representation ℂ U (M.cusp la)}
    (h : IsPullRep M la ρ) (χ : U →* ℂˣ) : IsPullRep M la (twist ρ χ) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun u c => χ u⁻¹ * a u c, fun u F hF c x => ?_⟩
  rw [twist_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, ha u F hF c x]
  simp [mul_assoc]

end GlobalTheory.TwistedRepresentationEmbedding

end
