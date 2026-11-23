import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceA
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteImageOfLocallyConstantOnHolomorphicFamilie
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes

noncomputable section

namespace SheetDecomposition.One

open AlgebraicGeometry CategoryTheory Filter Topology Metric TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem const_affine {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra K ℂ] [IsDomain (ℂ ⊗[K] A)] (d : ℕ)
    (hs : SmoothOfRelativeDimension d (spMap (algebraMap K A))) [Algebra.FiniteType K A] (F : (Sp ℂ ⟶ Sp A) → ℂ)
    (hF : ∀ (m : ℕ) (T : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Sp A)), IsOpen T → IsPreconnected T → IsHolTo T y →
      ∀ b ∈ T, ∀ b' ∈ T, F (y b) = F (y b'))
    (x x' : Sp ℂ ⟶ Sp A) (hx : x ≫ spMap (algebraMap K A) = spMap (algebraMap K ℂ))
    (hx' : x' ≫ spMap (algebraMap K A) = spMap (algebraMap K ℂ)) : F x = F x' := by
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct K ℂ A)
  let q : Sp (ℂ ⊗[K] A) ⟶ Sp A := spMap (Algebra.TensorProduct.includeRight (R := K) (A := ℂ) (B := A)).toRingHom
  have hpb' : IsPullback (spMap (algebraMap ℂ (ℂ ⊗[K] A))) q (spMap (algebraMap K ℂ)) (spMap (algebraMap K A)) := hpb
  have hp : SmoothOfRelativeDimension d (spMap (algebraMap ℂ (ℂ ⊗[K] A))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback hpb'.flip hs
  have hl := GlobalTheory.FiniteClasses.isLocallyConstant_of_hol _ d hp (fun z => F (z.1 ≫ q)) (by
    intro B y hB hy b₀ hb₀
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hB b₀ hb₀
    filter_upwards [ball_mem_nhds b₀ hε] with b hb
    exact hF d (ball b₀ ε) (fun b => (y b).1 ≫ q) isOpen_ball (convex_ball b₀ ε).isPreconnected
      (isHolTo_mono (GagaRat.isHolTo_comp q hy) isOpen_ball hsub) b hb b₀ (mem_ball_self hε))
  haveI := GlobalTheory.FiniteClasses.preconnectedSpace_pts (ℂ ⊗[K] A)
  have := hl.apply_eq_of_preconnectedSpace
    ⟨hpb'.lift (𝟙 _) x (by rw [Category.id_comp, hx]), hpb'.lift_fst _ _ _⟩
    ⟨hpb'.lift (𝟙 _) x' (by rw [Category.id_comp, hx']), hpb'.lift_fst _ _ _⟩
  simpa only [IsPullback.lift_snd] using this

theorem const_chart {K : Type} [Field K] (σ : K →+* ℂ) {X : Scheme.{0}} (s : X ⟶ Sp K) {Ω : Type} [Field Ω] [Algebra K Ω]
    (ξ : Sp Ω ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) (F : (Sp ℂ ⟶ X) → ℂ) (d : ℕ) (hs : SmoothOfRelativeDimension d s)
    (hξs : ξ ≫ s = spMap (algebraMap K Ω)) (hξ : IsCptGen ξ) (hcl : ConstClosed K Ω) (hVc : ∀ q ∈ V, genPt ξ ⤳ q)
    (hF : ∀ (m : ℕ) (T : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen T → IsPreconnected T → IsHolTo T y →
      (∀ b ∈ T, ⊤ ≤ y b ⁻¹ᵁ V) → ∀ b ∈ T, ∀ b' ∈ T, F (y b) = F (y b'))
    (x x' : Sp ℂ ⟶ X) (hx : x ≫ s = spMap σ) (hx' : x' ≫ s = spMap σ) (hxV : ⊤ ≤ x ⁻¹ᵁ V) (hxV' : ⊤ ≤ x' ⁻¹ᵁ V) :
    F x = F x' := by
  haveI : CharZero K := σ.charZero
  letI : Algebra K ℂ := σ.toAlgebra
  obtain ⟨A, _, _, a, -, ha, hr, has, -⟩ := GagaRat.exists_chart (C := ℂ) s V hV
  have hm : ∀ P, a P ∈ V := fun P => by
    have : a P ∈ Set.range a := ⟨P, rfl⟩
    rwa [hr] at this
  have hg : genPt ξ ∈ V := (hVc _ (GagaRat.centre_mem hxV)).mem_open V.isOpen (GagaRat.centre_mem hxV)
  obtain ⟨φ, hφ⟩ := GagaRat.exists_ringHom_of_mem a ξ (by rw [hr]; exact hg)
  obtain ⟨χ, hχ⟩ := GagaRat.exists_ringHom_of_mem a x (by rw [hr]; exact GagaRat.centre_mem hxV)
  obtain ⟨χ', hχ'⟩ := GagaRat.exists_ringHom_of_mem a x' (by rw [hr]; exact GagaRat.centre_mem hxV')
  have hφK : φ.comp (algebraMap K A) = algebraMap K Ω := by
    have e : spMap (φ.comp (algebraMap K A)) = spMap (algebraMap K Ω) := by
      rw [← GagaRat.spMap_comp, ← has, ← Category.assoc, hφ, hξs]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun b hb => ?_
    by_contra h0
    have hne : (Submodule.span A {b}).annihilator ≠ ⊤ := fun h => h0 (by
      have h1 : (1 : A) ∈ (Submodule.span A {b}).annihilator := h ▸ Submodule.mem_top
      simpa using Submodule.mem_annihilator_span_singleton b 1 |>.1 h1)
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let P : Sp A := (⟨M, hM.isPrime⟩ : PrimeSpectrum A)
    obtain ⟨u, hu, e⟩ := GagaRat.local_descend ξ a φ hφ P (hVc _ (hm P)) (hξ.inj ⟨_, hVc _ (hm P)⟩) b hb
    exact hu (hle ((Submodule.mem_annihilator_span_singleton b u).2 e))
  have hsA : SmoothOfRelativeDimension d (spMap (algebraMap K A)) := by
    rw [← has]
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + d) (a ≫ s))
  haveI : Algebra.FiniteType K A := by
    haveI : Smooth (spMap (algebraMap K A)) := SmoothOfRelativeDimension.smooth d _
    exact RingHom.finiteType_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1
      (inferInstance : LocallyOfFiniteType (spMap (algebraMap K A))))
  haveI : IsDomain (ℂ ⊗[K] A) := GlobalTheory.GeomConn.isDomain_tensor
    ({ φ with commutes' := fun k => RingHom.congr_fun hφK k } : A →ₐ[K] Ω) hinj (fun w hw => by
      obtain ⟨u, v, hv, h⟩ := hcl w hw
      exact ⟨u / v, by rw [map_div₀, ← h, mul_div_cancel_right₀ _ ((map_ne_zero _).2 hv)]⟩) ℂ
  have := const_affine d hsA (fun z => F (z ≫ a)) (fun m T y hT hc hy =>
    hF m T (fun b => y b ≫ a) hT hc (GagaRat.isHolTo_comp a hy) fun b _ p _ => hm (y b p)) (spMap χ) (spMap χ')
    (by rw [← has, ← Category.assoc, hχ, hx]) (by rw [← has, ← Category.assoc, hχ', hx'])
  simpa only [hχ, hχ'] using this

theorem const_of_hol {K : Type} [Field K] (σ : K →+* ℂ) {X : Scheme.{0}} (s : X ⟶ Sp K) {Ω : Type} [Field Ω] [Algebra K Ω]
    (ξ : Sp Ω ⟶ X) (W : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (d : ℕ) (hs : SmoothOfRelativeDimension d s)
    (hξs : ξ ≫ s = spMap (algebraMap K Ω)) (hξ : IsCptGen ξ) (hcl : ConstClosed K Ω)
    (hF : ∀ (m : ℕ) (T : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen T → IsPreconnected T → IsHolTo T y →
      (∀ b ∈ T, ⊤ ≤ y b ⁻¹ᵁ W) → ∀ b ∈ T, ∀ b' ∈ T, F (y b) = F (y b'))
    (x x' : Sp ℂ ⟶ X) (hx : x ≫ s = spMap σ) (hx' : x' ≫ s = spMap σ) (hxW : ⊤ ≤ x ⁻¹ᵁ W) (hxW' : ⊤ ≤ x' ⁻¹ᵁ W)
    (hc : genPt ξ ⤳ centre x) (hc' : genPt ξ ⤳ centre x') : F x = F x' := by
  haveI : Smooth s := SmoothOfRelativeDimension.smooth d s
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨Z, hZ, -, -⟩ := cpt_open_integral X Ω ξ hξ
  obtain ⟨V, hV, m, le⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := centre x) (U := W ⊓ Z)
    ⟨GagaRat.centre_mem hxW, (hZ _).2 hc⟩
  obtain ⟨V', hV', m', le'⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := centre x') (U := W ⊓ Z)
    ⟨GagaRat.centre_mem hxW', (hZ _).2 hc'⟩
  obtain ⟨z, hz, hzV⟩ := exists_point σ s (V ⊓ V') (q := genPt ξ) ⟨hc.mem_open V.isOpen m, hc'.mem_open V'.isOpen m'⟩
  have e := const_chart σ s ξ V hV F d hs hξs hξ hcl (fun q hq => (hZ q).1 (le hq).2)
    (fun n T y h1 h2 h3 h4 => hF n T y h1 h2 h3 fun b hb p hp => (le (h4 b hb hp)).1) x z hx hz
    (GagaRat.top_le_of_centre_mem m) fun p hp => (hzV hp).1
  have e' := const_chart σ s ξ V' hV' F d hs hξs hξ hcl (fun q hq => (hZ q).1 (le' hq).2)
    (fun n T y h1 h2 h3 h4 => hF n T y h1 h2 h3 fun b hb p hp => (le' (h4 b hb hp)).1) x' z hx' hz
    (GagaRat.top_le_of_centre_mem m') fun p hp => (hzV hp).2
  exact e.trans e'.symm

theorem genPt_mem_dense {X : Scheme.{0}} [IsLocallyNoetherian X] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (U : X.Opens)
    (hξ : IsCptGen ξ) (hU : Dense (U : Set X)) : genPt ξ ∈ U := by
  obtain ⟨Z, hZ, -, -⟩ := cpt_open_integral X Ω ξ hξ
  obtain ⟨q, hq, hqU⟩ := hU.inter_open_nonempty _ Z.isOpen ⟨genPt ξ, (hZ _).2 specializes_rfl⟩
  exact ((hZ q).1 hq).mem_open U.isOpen hqU

end SheetDecomposition.One
