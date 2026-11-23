import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem isLC_sum {X ι : Type*} [TopologicalSpace X] (s : Finset ι) (f : ι → X → ℤ)
    (h : ∀ j, IsLocallyConstant (f j)) : IsLocallyConstant (fun t => ∑ j ∈ s, f j t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

private theorem key {T Z S : Scheme.{0}} {p : Z ⟶ S} {π : T ⟶ S} {ι : Type} [Fintype ι] [IsFinite p]
    (hFib : FibFin) (σ : ι → (T ⟶ Z)) (m : ι → ℤ) (w : Wt Z) (hC : Counts p π σ m w) (A : Sq p)
    (φ : A.V → ℤ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] {U1 : Scheme.{0}} (f : U1 ⟶ T) (g : U1 ⟶ A.U)
    (hfg : f ≫ π = g ≫ A.u) (τ : ι → (U1 ⟶ A.V)) (hτv : ∀ j, τ j ≫ A.v = f ≫ σ j)
    (hτr : ∀ j, τ j ≫ A.r = g) (x1 : gp Ω ⟶ U1) :
    ∑ j, m j * φ (τ j (pt x1)) = ∑ᶠ z ∈ fib A.r (x1 ≫ g), w Ω (z ≫ A.v) * φ (pt z) := by
  classical
  haveI : IsFinite A.r := A.finite
  have hfin := hFib A.r Ω (x1 ≫ g)
  have hmem : ∀ j, x1 ≫ τ j ∈ fib A.r (x1 ≫ g) := fun j => by
    show (x1 ≫ τ j) ≫ A.r = x1 ≫ g
    rw [Category.assoc, hτr]
  have hiff : ∀ z ∈ fib A.r (x1 ≫ g), ∀ j, (x1 ≫ f) ≫ σ j = z ≫ A.v ↔ x1 ≫ τ j = z := by
    intro z hz j
    have hz' : z ≫ A.r = x1 ≫ g := hz
    constructor
    · intro h
      apply A.pb.hom_ext
      · rw [Category.assoc, hτv, ← Category.assoc, h]
      · rw [Category.assoc, hτr, hz']
    · intro h
      rw [← h, Category.assoc, Category.assoc, hτv]
  have hw : ∀ z ∈ fib A.r (x1 ≫ g),
      w Ω (z ≫ A.v) = ∑ j, if x1 ≫ τ j = z then m j else 0 := by
    intro z hz
    have hz' : z ≫ A.r = x1 ≫ g := hz
    have hsq : (z ≫ A.v) ≫ p = (x1 ≫ f) ≫ π := by
      rw [Category.assoc, A.pb.w, ← Category.assoc, hz', Category.assoc, ← hfg, Category.assoc]
    rw [hC Ω (x1 ≫ f) (z ≫ A.v) hsq, finsum_mem_def, finsum_eq_sum_of_fintype]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : x1 ≫ τ j = z
    · rw [Set.indicator_of_mem
        (show j ∈ {j | (x1 ≫ f) ≫ σ j = z ≫ A.v} from (hiff z hz j).mpr h) m, if_pos h]
    · rw [Set.indicator_of_notMem
        (show j ∉ {j | (x1 ≫ f) ≫ σ j = z ≫ A.v} from fun h' => h ((hiff z hz j).mp h')) m,
        if_neg h]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [Finset.sum_congr rfl
    (g := fun z => (∑ j, if x1 ≫ τ j = z then m j else 0) * φ (pt z))
    (fun z hz => by rw [hw z (hfin.mem_toFinset.mp hz)])]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (hfin.mem_toFinset.mpr (hmem j)), pt_comp]

theorem UpperTheory.Gal.TranscendenceTraces.countWt_of :
    PtEx → PtLift → FibFin → CountWt := by
  intro hPE hPL hFib T Z S p π _ _ _ ι _ σ m w hσ hC
  classical
  haveI := Fintype.ofFinite ι
  intro A φ hφ
  let f : pullback π A.u ⟶ T := pullback.fst π A.u
  let g : pullback π A.u ⟶ A.U := pullback.snd π A.u
  have hfg : f ≫ π = g ≫ A.u := pullback.condition
  have hpb1 : IsPullback f g π A.u := IsPullback.of_hasPullback π A.u
  haveI : Surjective g := MorphismProperty.of_isPullback (P := @Surjective) hpb1 inferInstance
  haveI : IsIntegralHom g :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom) hpb1 inferInstance
  let τ : ι → (pullback π A.u ⟶ A.V) := fun j =>
    A.pb.lift (f ≫ σ j) g (by rw [Category.assoc, hσ j, hfg])
  have hτv : ∀ j, τ j ≫ A.v = f ≫ σ j := fun j => A.pb.lift_fst _ _ _
  have hτr : ∀ j, τ j ≫ A.r = g := fun j => A.pb.lift_snd _ _ _
  let χ : ↥(pullback π A.u) → ℤ := fun t => ∑ j, m j * φ (τ j t)
  have hχ : IsLocallyConstant χ :=
    isLC_sum Finset.univ (fun j t => m j * φ (τ j t))
      (fun j => (hφ.comp_continuous (τ j).continuous).comp (fun a => m j * a))
  have hconst : ∀ t1 t2, g t1 = g t2 → χ t1 = χ t2 := by
    intro t1 t2 h
    obtain ⟨Ω, hF, hA, x1, hx1⟩ := hPE _ t1
    letI := hF
    haveI := hA
    obtain ⟨z, hz, hzt⟩ := hPL g Ω (x1 ≫ g) t2 (by rw [pt_comp, hx1, h])
    have k1 := key hFib σ m w hC A φ Ω f g hfg τ hτv hτr x1
    have k2 := key hFib σ m w hC A φ Ω f g hfg τ hτv hτr z
    rw [hz] at k2
    show ∑ j, m j * φ (τ j t1) = ∑ j, m j * φ (τ j t2)
    rw [← hx1, ← hzt, k1, k2]
  have hsurj : Function.Surjective g := g.surjective
  let ψ : A.U → ℤ := fun s => χ (Function.surjInv hsurj s)
  have hψg : ∀ t, ψ (g t) = χ t := fun t => hconst _ _ (Function.surjInv_eq hsurj _)
  refine ⟨ψ, ?_, ?_⟩
  · have hq : Topology.IsQuotientMap g := g.isClosedMap.isQuotientMap g.continuous hsurj
    intro s
    rw [← hq.isOpen_preimage]
    have hpre : g ⁻¹' (ψ ⁻¹' s) = χ ⁻¹' s := by
      ext t
      simp only [Set.mem_preimage, hψg]
    rw [hpre]
    exact hχ s
  · intro Ω _ _ x
    obtain ⟨t, ht⟩ := hsurj (pt x)
    obtain ⟨z, hz, _⟩ := hPL g Ω x t ht
    rw [← hz, pt_comp, hψg]
    exact key hFib σ m w hC A φ Ω f g hfg τ hτv hτr z
