import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory

theorem exists_unit_of_cocycle_rightAction_charZero :
    ∀ (K : Type) [Field K] [CharZero K] (Γ : Type) [Group Γ] [Finite Γ] (σ : Γ → K →+* K),
    (∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a)) → ∀ (c : Γ → Kˣ),
    (∀ γ δ, (c (γ * δ) : K) = σ δ (c γ) * c δ) → (∀ γ, (∀ a, σ γ a = a) → c γ = 1) →
    ∃ f : Kˣ, ∀ γ, σ γ f = c γ * f := by
  intro K _ _ Γ _ _ σ hσ c hc htriv
  classical
  haveI := Fintype.ofFinite Γ
  have h1 : ∀ a, σ 1 a = a := by
    intro a
    have e := hσ 1 1 a
    rw [mul_one] at e
    exact (σ 1).injective e.symm
  have key : ∀ γ δ, (σ δ (c γ : K))⁻¹ = (c δ : K) * ((c (γ * δ) : K))⁻¹ := by
    intro γ δ
    rw [hc γ δ, mul_inv, mul_left_comm, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
  let F : K → K := fun b => ∑ γ, ((c γ : K))⁻¹ * σ γ b
  have hF : ∀ b δ, σ δ (F b) = c δ * F b := by
    intro b δ
    simp only [F, map_sum, map_mul, map_inv₀, Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.mulRight δ)
    intro γ
    simp only [Equiv.coe_mulRight]
    rw [key γ δ, hσ]
    ring
  have hex : ∃ b, F b ≠ 0 := by
    by_contra hno
    push_neg at hno
    let φ : Γ → (K →* K) := fun γ => (σ γ : K →* K)
    let s : Finset (K →* K) := Finset.univ.image φ
    let g : (K →* K) → K := fun ψ => ∑ γ ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c γ : K))⁻¹
    have hli := linearIndependent_monoidHom K K
    have hsum : ∑ ψ ∈ s, g ψ • (ψ : K → K) = 0 := by
      funext b
      rw [Finset.sum_apply, Pi.zero_apply, ← hno b]
      simp only [Pi.smul_apply, smul_eq_mul, g, Finset.sum_mul]
      have hterm : ∀ ψ ∈ s, ∑ i ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c i : K))⁻¹ * ψ b
          = ∑ i ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c i : K))⁻¹ * σ i b := fun ψ _ =>
        Finset.sum_congr rfl fun γ hγ => by rw [← (Finset.mem_filter.mp hγ).2]; rfl
      rw [Finset.sum_congr rfl hterm, Finset.sum_fiberwise_of_maps_to
        (fun γ _ => Finset.mem_image_of_mem φ (Finset.mem_univ γ))]
    have hz := linearIndependent_iff'.mp hli s g hsum (φ 1)
      (Finset.mem_image_of_mem φ (Finset.mem_univ 1))
    have hterm : ∀ γ ∈ Finset.univ.filter (fun γ => φ γ = φ 1), ((c γ : K))⁻¹ = 1 := by
      intro γ hγ
      rw [Finset.mem_filter] at hγ
      have hid : ∀ a, σ γ a = a := fun a => (DFunLike.congr_fun hγ.2 a).trans (h1 a)
      rw [htriv γ hid]
      simp
    have hcard : g (φ 1) = ((Finset.univ.filter (fun γ => φ γ = φ 1)).card : K) := by
      simp only [g]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard, Nat.cast_eq_zero, Finset.card_eq_zero] at hz
    have hmem : (1 : Γ) ∈ Finset.univ.filter (fun γ => φ γ = φ 1) := by simp
    rw [hz] at hmem
    simp at hmem
  obtain ⟨b, hb⟩ := hex
  refine ⟨Units.mk0 (F b) hb, fun γ => ?_⟩
  simp only [Units.val_mk0]
  exact hF b γ

end GlobalTheory
