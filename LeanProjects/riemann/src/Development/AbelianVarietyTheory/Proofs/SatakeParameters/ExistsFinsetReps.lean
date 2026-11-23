import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

namespace GlobalTheory.FinsetConjugateRepresentatives

theorem mem_map_conj {G : Type} [Group G] (K : Subgroup G) (g y : G) :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have : g⁻¹ * (MulAut.conj g).toMonoidHom z * g = z := by
      simp [mul_assoc]
    rw [this]
    exact hz
  · intro h
    refine ⟨g⁻¹ * y * g, h, ?_⟩
    simp [mul_assoc]

theorem exists_finset_reps : ∀ {G : Type} [inst : Group G] {K : Subgroup G},
    Formalism.UG.IsCommensurated K → ∀ (g : G), ∃ (R : Finset G),
      (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
      ∀ (x : G), (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ : G, γ ∈ R ∧ γ⁻¹ * x ∈ K := by
  intro G _ K hK g
  classical
  set H : Subgroup K := (K.map (MulAut.conj g).toMonoidHom).subgroupOf K with hH
  have hidx : H.index ≠ 0 := hK g
  haveI : Finite (K ⧸ H) := Nat.finite_of_card_ne_zero hidx
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have key : ∀ (q : K ⧸ H) (a : K) (b : G), b ∈ K →
      ((((q.out : K) : G) * g)⁻¹ * ((a : G) * g * b) ∈ K ↔ q = (a : K ⧸ H)) := by
    intro q a b hb
    have e : (((q.out : K) : G) * g)⁻¹ * ((a : G) * g * b)
        = (g⁻¹ * (((q.out)⁻¹ * a : K) : G) * g) * b := by
      simp [mul_assoc]
    rw [e, K.mul_mem_cancel_right hb, ← mem_map_conj, ← Subgroup.mem_subgroupOf, ← hH,
      ← QuotientGroup.eq, QuotientGroup.out_eq']
  refine ⟨Finset.univ.image (fun q : K ⧸ H => ((q.out : K) : G) * g), ?_, ?_⟩
  · intro γ hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hγ
    exact ⟨_, (q.out).2, 1, K.one_mem, by simp⟩
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    refine ⟨((((⟨k₁, hk₁⟩ : K) : K ⧸ H).out : K) : G) * g,
      ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, (key _ ⟨k₁, hk₁⟩ k₂ hk₂).mpr rfl⟩, ?_⟩
    rintro γ ⟨hγ, hx⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hγ
    rw [(key q ⟨k₁, hk₁⟩ k₂ hk₂).mp hx]

end GlobalTheory.FinsetConjugateRepresentatives
