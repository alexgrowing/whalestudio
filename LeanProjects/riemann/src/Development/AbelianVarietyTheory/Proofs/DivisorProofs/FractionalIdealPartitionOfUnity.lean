import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open scoped nonZeroDivisors

namespace GlobalTheory.PartitionFracId

theorem exists_partition (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) :
    ∃ (n : ℕ) (d : Fin n → 𝔠.elt) (a : Fin n → 𝓞 F),
    (∀ j (e : 𝔠.elt), ∃ b : 𝓞 F, a j • e = b • d j) ∧ ∑ j, a j = 1 := by
  set I : FractionalIdeal (𝓞 F)⁰ F := (𝔠 : FractionalIdeal (𝓞 F)⁰ F) with hI
  set J : FractionalIdeal (𝓞 F)⁰ F := ((𝔠⁻¹ : FracId F) : FractionalIdeal (𝓞 F)⁰ F) with hJ
  have hIJ : I * J = 1 := Units.mul_inv 𝔠
  have hJI : J * I = 1 := by rw [mul_comm]; exact hIJ
  have hmem : ∀ {u v : F}, u ∈ I → v ∈ J → ∃ r : 𝓞 F, (r : F) = u * v := by
    intro u v hu hv
    have h := FractionalIdeal.mul_mem_mul hu hv
    rw [hIJ] at h
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h
    exact ⟨r, hr⟩
  have hmem' : ∀ {u v : F}, v ∈ J → u ∈ I → ∃ r : 𝓞 F, (r : F) = v * u := by
    intro u v hv hu
    have h := FractionalIdeal.mul_mem_mul hv hu
    rw [hJI] at h
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h
    exact ⟨r, hr⟩
  let P : F → Prop := fun x => ∃ (n : ℕ) (d : Fin n → 𝔠.elt) (a : Fin n → 𝓞 F),
    (∀ j (e : 𝔠.elt), ∃ b : 𝓞 F, a j • e = b • d j) ∧ ∑ j, (a j : F) = x
  have h1 : (1 : F) ∈ (I : Submodule (𝓞 F) F) * (J : Submodule (𝓞 F) F) := by
    rw [← FractionalIdeal.coe_mul, hIJ]
    exact FractionalIdeal.one_mem_one _
  have hP : P 1 := by
    refine Submodule.mul_induction_on (C := P) h1 ?_ ?_
    · intro u hu v hv
      obtain ⟨r, hr⟩ := hmem hu hv
      refine ⟨1, fun _ => ⟨u, hu⟩, fun _ => r, ?_, ?_⟩
      · intro j e
        obtain ⟨s, hs⟩ := hmem' (u := (e : F)) hv e.2
        refine ⟨s, Subtype.ext ?_⟩
        show ((r • e : 𝔠.elt) : F) = ((s • (⟨u, hu⟩ : 𝔠.elt) : 𝔠.elt) : F)
        rw [Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def]
        change (r : F) * (e : F) = (s : F) * u
        rw [hr, hs]; ring
      · simp [hr]
    · rintro x y ⟨n, d, a, ha, hx⟩ ⟨m, d', a', ha', hy⟩
      refine ⟨n + m, Fin.append d d', Fin.append a a', ?_, ?_⟩
      · intro j e
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · obtain ⟨b, hb⟩ := ha i e
          exact ⟨b, by simpa using hb⟩
        · obtain ⟨b, hb⟩ := ha' i e
          exact ⟨b, by simpa using hb⟩
      · rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right, hx, hy]
  obtain ⟨n, d, a, ha, hs⟩ := hP
  refine ⟨n, d, a, ha, ?_⟩
  apply RingOfIntegers.coe_injective
  simpa using hs

end GlobalTheory.PartitionFracId
