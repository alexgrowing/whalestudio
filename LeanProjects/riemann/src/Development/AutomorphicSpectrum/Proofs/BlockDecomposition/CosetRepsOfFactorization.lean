import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

namespace GlobalTheory.CompanionTheory.SatPow.RepsGen

private theorem mem_map_conj_iff_inv_mul_mul_mem {G : Type*} [Group G] (I : Subgroup G) (t y : G) :
    y ∈ I.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * y * t ∈ I := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro h
    exact ⟨t⁻¹ * y * t, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem reps_of_quotient_with_property (G : Type) [Group G] (I : Subgroup G) (t : G) (P : G → Prop)
    (hP1 : P 1)
    (hfin : Finite (I ⧸ (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I))
    (hfac : ∀ i ∈ I, ∃ u ∈ I, P u ∧ ∃ y ∈ I, t⁻¹ * y * t ∈ I ∧ i = u * y) :
    ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ r ∈ R, r ∈ I ∧ P r) ∧
      ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I := by
  classical
  set H := (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I with hH
  have : Fintype (I ⧸ H) := @Fintype.ofFinite _ hfin
  have hmem : ∀ a b : I, (QuotientGroup.mk a : I ⧸ H) = QuotientGroup.mk b ↔
      t⁻¹ * ((a : G)⁻¹ * b) * t ∈ I := by
    intro a b
    rw [QuotientGroup.eq, hH, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      and_iff_right (a⁻¹ * b).2, mem_map_conj_iff_inv_mul_mul_mem]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have key : ∀ c : I ⧸ H, ∃ r : I, P r ∧ (QuotientGroup.mk r : I ⧸ H) = c ∧
      (c = QuotientGroup.mk 1 → r = 1) := by
    intro c
    obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective c
    by_cases h : (QuotientGroup.mk i : I ⧸ H) = QuotientGroup.mk 1
    · exact ⟨1, by simpa using hP1, h.symm, fun _ => rfl⟩
    · obtain ⟨u, hu, hPu, y, hy, hty, hi⟩ := hfac i i.2
      refine ⟨⟨u, hu⟩, hPu, ?_, fun h' => absurd h' h⟩
      rw [hmem]
      have hy' : u⁻¹ * (i : G) = y := by rw [hi, inv_mul_cancel_left]
      show t⁻¹ * (u⁻¹ * (i : G)) * t ∈ I
      rw [hy']
      exact hty
  choose f hfP hfmk hf1 using key
  refine ⟨Finset.univ.image (fun c => (f c : G)), ?_, ?_, ?_⟩
  · exact Finset.mem_image.2 ⟨QuotientGroup.mk 1, Finset.mem_univ _, by rw [hf1 _ rfl]; simp⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    exact ⟨(f c).2, hfP c⟩
  · intro i hi
    refine ⟨f (QuotientGroup.mk ⟨i, hi⟩),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · exact (hmem (f (QuotientGroup.mk ⟨i, hi⟩)) ⟨i, hi⟩).1 (hfmk _)
    · rintro r ⟨hr, hri⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
      have hc : c = QuotientGroup.mk ⟨i, hi⟩ := (hfmk c).symm.trans ((hmem _ _).2 hri)
      subst hc
      rfl

end GlobalTheory.CompanionTheory.SatPow.RepsGen
