import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPartitionOneIntegralAtPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitScalarSmulCoreIntegralAdelicFormPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DescGlue

open GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries

theorem finite_of_overPrime {L : Type} [Field L] [NumberField L] (l : ℕ) (hl : l.Prime)
    (S : Set (HeightOneSpectrum (𝓞 L))) (h : OverPrime l S) : S.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 L)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine (Ideal.finite_factors h0).subset fun la hla => ?_
  show la.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact h la hla

theorem finite_below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L)
    {S : Set (HeightOneSpectrum (𝓞 L))} (hS : S.Finite) : (below φ S).Finite := by
  have e : below φ S = ⋃ la ∈ S, {p : HeightOneSpectrum (𝓞 K) |
      p.asIdeal = la.asIdeal.comap (RingOfIntegers.mapRingHom φ)} := by
    ext p; simp [below]
  rw [e]
  exact hS.biUnion fun la _ => Set.Subsingleton.finite fun p1 h1 p2 h2 =>
    HeightOneSpectrum.ext (h1.trans h2.symm)

set_option maxHeartbeats 800000 in

theorem glue : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.OverPrime l S → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc S → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n S, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → (∀ la ∈ S, ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a) → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ S (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc S)) ∧ φ = ∑ a, x' a • ψ' a := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hT h1 h2 h3 h4 h5 h6 i hVS hV hFP l hl C hC hPin S hS hUn φ hφmem hKf
    m x ψ hψ hφ hloc
  classical
  have hσ : ∀ t : T.Q.c.F, C.σ₂ (C.inc t) = T.σ₀ t := fun t => by
    rw [← RingHom.comp_apply, hC.1.2.2.1]
  have hfin : S.Finite := finite_of_overPrime l hl S hS
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · subst hS0
    refine ⟨m, fun a => C.σ₂ (x a), ψ, fun a => ⟨x a, rfl, fun la h => absurd h (Set.notMem_empty la)⟩,
      fun a => ?_, hφ⟩
    obtain ⟨f, ⟨hf1, hf2⟩, hf⟩ := hψ a
    exact ⟨f, ⟨hf1, hf2, fun p hp => by
      obtain ⟨la, hla, _⟩ := hp
      exact absurd hla (Set.notMem_empty la)⟩, hf⟩
  set S' := hfin.toFinset with hS'
  have hmem : ∀ la : S', la.1 ∈ S := fun la => hfin.mem_toFinset.1 la.2
  choose m' x' ψ' hx' hψ' hφ' using fun la : S' => hloc la.1 (hmem la)
  choose a' ha' hav using fun (la : S') (a : Fin (m' la)) => hx' la a
  have hset : ∀ la : S', below C.inc {la.1} =
      {p | p.asIdeal = la.1.asIdeal.comap (RingOfIntegers.mapRingHom C.inc)} := fun la => by
    ext p; simp [below]
  choose t ht htψ using fun (la : S') (a : Fin (m' la)) =>
    GlobalTheory.T.exists_unitScalar_smul_coreIntegralAdelicForm_places D T hT i (κ i) (GlobalTheory.AdTh.lastPos_of_kapIs h6.kap i)
      (la.1.asIdeal.comap (RingOfIntegers.mapRingHom C.inc))
      (Ideal.IsPrime.comap _ (hK := la.1.isPrime)) (below C.inc S) (finite_below C.inc hfin) (ψ' la a)
      (hset la ▸ hψ' la a)
  have hte : ∀ (la : S') (a : Fin (m' la)), la.1.valuation _ (C.inc (t la a : T.Q.c.F)) = 1 := fun la a => by
    have e : C.inc (t la a : T.Q.c.F) = ((RingOfIntegers.mapRingHom C.inc (t la a) : 𝓞 C.d.c₂.F) : C.d.c₂.F) := rfl
    rw [e]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem la.1).mpr fun h => ht la a (Ideal.mem_comap.2 h)
  have ht0 : ∀ (la : S') (a : Fin (m' la)), T.σ₀ (t la a : T.Q.c.F) ≠ 0 := fun la a => by
    refine (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.mpr ?_)
    rintro h0
    exact ht la a (h0 ▸ Ideal.zero_mem _)
  let Y : S' → Finset C.d.c₂.F := fun la => Finset.univ.image fun a => a' la a / C.inc (t la a : T.Q.c.F)
  have hY : ∀ la, ∀ y ∈ Y la, la.1.valuation _ y ≤ 1 := by
    intro la y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
    rw [map_div₀, hte, div_one]
    exact hav la a la.1 (Set.mem_singleton _)
  have hne : S'.Nonempty := by
    obtain ⟨la, h⟩ := hSne
    exact ⟨la, hfin.mem_toFinset.2 h⟩
  obtain ⟨e, he1, he⟩ := GlobalTheory.exists_partition_one_integral_at_places _ S' hne Y hY
  let ι := Σ la : S', Fin (m' la)
  let ε := Fintype.equivFin ι
  let X : ι → ℂ := fun s => C.σ₂ (e s.1 * (a' s.1 s.2 / C.inc (t s.1 s.2 : T.Q.c.F)))
  let Ψ : ι → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ) := fun s => T.σ₀ (t s.1 s.2 : T.Q.c.F) • ψ' s.1 s.2
  have key : ∀ s : ι, X s • Ψ s = C.σ₂ (e s.1) • (x' s.1 s.2 • ψ' s.1 s.2) := by
    intro s
    simp only [X, Ψ, smul_smul, map_mul, map_div₀, hσ, ha']
    congr 1
    field_simp [ht0 s.1 s.2]
  refine ⟨Fintype.card ι, fun k => X (ε.symm k), fun k => Ψ (ε.symm k), fun k => ⟨_, rfl, fun la'' h'' =>
    he _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)) la'' (hfin.mem_toFinset.2 h'')⟩,
    fun k => htψ _ _, ?_⟩
  symm
  calc ∑ k, X (ε.symm k) • Ψ (ε.symm k) = ∑ s : ι, X s • Ψ s := Equiv.sum_comp ε.symm (fun s => X s • Ψ s)
    _ = ∑ s : ι, C.σ₂ (e s.1) • (x' s.1 s.2 • ψ' s.1 s.2) := Finset.sum_congr rfl fun s _ => key s
    _ = ∑ la : S', ∑ a : Fin (m' la), C.σ₂ (e la) • (x' la a • ψ' la a) := Fintype.sum_sigma _
    _ = ∑ la : S', C.σ₂ (e la) • φ := Finset.sum_congr rfl fun la _ => by rw [← Finset.smul_sum, ← hφ' la]
    _ = φ := by rw [← Finset.sum_smul, ← map_sum, he1, map_one, one_smul]

end GlobalTheory.DescGlue
