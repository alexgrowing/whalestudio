import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrSs
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem quot_ss {B Bh E κ Γ : Type} [CommRing B] [CommRing Bh] [Algebra B Bh] [Ring E] [Algebra Bh E]
    [Field κ] [Algebra Bh κ] [Group Γ] (I : Set (MonoidAlgebra B Γ))
    (ι : MonoidAlgebra Bh Γ →ₐ[Bh] E) (surj : Function.Surjective ι)
    (ker : ∀ y, ι y = 0 → y ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom Γ (algebraMap B Bh) '' I))
    [IsSemisimpleRing (κ ⊗[Bh] E)] :
    IsSemisimpleRing (TwoSidedIdeal.span
      (MonoidAlgebra.mapRingHom Γ ((algebraMap Bh κ).comp (algebraMap B Bh)) '' I)).ringCon.Quotient := by
  set J := TwoSidedIdeal.span
      (MonoidAlgebra.mapRingHom Γ ((algebraMap Bh κ).comp (algebraMap B Bh)) '' I) with hJ
  let π : MonoidAlgebra κ Γ →+* J.ringCon.Quotient := J.ringCon.mk'
  have hπ : ∀ z, z ∈ J → π z = 0 := by
    intro z hz
    rw [← map_zero π]
    exact (RingCon.eq _).2 ((TwoSidedIdeal.mem_iff _ _).1 hz)
  let ψ0 : MonoidAlgebra Bh Γ →+* J.ringCon.Quotient :=
    π.comp (MonoidAlgebra.mapRingHom Γ (algebraMap Bh κ))
  have hk : RingHom.ker ι.toRingHom ≤ RingHom.ker ψ0 := by
    intro y hy
    have h1 := ker y hy
    have h2 : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom Γ (algebraMap B Bh) '' I) ≤ TwoSidedIdeal.ker ψ0 := by
      rw [TwoSidedIdeal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker]
      apply hπ
      apply TwoSidedIdeal.subset_span
      refine ⟨z, hz, ?_⟩
      ext a
      simp
    exact (TwoSidedIdeal.mem_ker _).1 (h2 h1)
  let ψ : E →+* J.ringCon.Quotient := ι.toRingHom.liftOfSurjective surj ⟨ψ0, hk⟩
  have hψ : ∀ y, ψ (ι y) = ψ0 y := fun y => RingHom.liftOfSurjective_comp_apply ι.toRingHom surj ⟨ψ0, hk⟩ y
  let ψa : E →ₐ[Bh] J.ringCon.Quotient :=
    { ψ with
      commutes' := fun b => by
        change ψ (algebraMap Bh E b) = π (algebraMap Bh (MonoidAlgebra κ Γ) b)
        rw [← ι.commutes, hψ]
        change π _ = _
        congr 1
        simp [MonoidAlgebra.coe_algebraMap] }
  let ka : κ →ₐ[Bh] J.ringCon.Quotient :=
    { π.comp (algebraMap κ (MonoidAlgebra κ Γ)) with
      commutes' := fun b => by
        change π _ = π (algebraMap Bh (MonoidAlgebra κ Γ) b)
        congr 1 }
  have hc : ∀ a y, Commute (ka a) (ψa y) := by
    intro a y
    obtain ⟨y, rfl⟩ := surj y
    change Commute (π (algebraMap κ _ a)) (ψ (ι y))
    rw [hψ]
    exact Commute.map (Algebra.commutes a _) π
  let Φ := Algebra.TensorProduct.lift ka ψa hc
  refine RingHom.isSemisimpleRing_of_surjective Φ.toRingHom ?_
  intro w
  obtain ⟨w, rfl⟩ : ∃ z, π z = w := J.ringCon.mk'_surjective w
  induction w using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add u v hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  | single m a =>
    refine ⟨a ⊗ₜ ι (MonoidAlgebra.single m 1), ?_⟩
    change Φ _ = _
    rw [Algebra.TensorProduct.lift_tmul]
    change π (algebraMap κ _ a) * ψ (ι _) = _
    rw [hψ]
    change π _ * π _ = _
    rw [← map_mul]
    congr 1
    simp [MonoidAlgebra.coe_algebraMap, MonoidAlgebra.single_mul_single]

theorem UpperTheory.V.Pa.gr_thick :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)] {e : G.G₀ →* Bˣ} (H : Hat h x D I Bh e) {ep : Fin n → H.E} (g : GrAlg H.T n x.a H.r ep), ∀ Q : Ideal Bh, Q.IsPrime → NonSS I (algebraMap B Bh) Q → Module.annihilator Bh g.N ≤ Q := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ _ e H ep g Q _ hQ s hs
  obtain ⟨κ, _, f, hf, hns⟩ := hQ
  by_contra hsQ
  letI : Algebra Bh κ := f.toAlgebra
  have hs0 : algebraMap Bh κ s ≠ 0 := fun h0 => hsQ (hf ▸ (RingHom.mem_ker.2 h0 : s ∈ RingHom.ker f))
  haveI := UpperTheory.V.Pa.gr_ss g κ s hs0 hs
  exact hns (quot_ss (κ := κ) I H.ι H.surj (fun y hy => (H.ker y).1 hy))
