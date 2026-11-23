import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulNormLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceKq
import GroundTheory.Brauer.BaseChangeCSA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisIntKQ
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

open scoped Pointwise

namespace GlobalTheory.FinAtP

variable {p : ℕ} [Fact p.Prime]

theorem kq_lc (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    LocallyCompactSpace (KQ p K 1) ∧ SecondCountableTopology (KQ p K 1) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : ContinuousSMul ℚ_[p] (KQ p K 1) := IsModuleTopology.toContinuousSMul ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  let b := Module.finBasis ℚ_[p] (KQ p K 1)
  let e : KQ p K 1 ≃L[ℚ_[p]] (Fin (Module.finrank ℚ_[p] (KQ p K 1)) → ℚ_[p]) :=
    b.equivFun.toContinuousLinearEquiv
  exact ⟨e.toHomeomorph.isClosedEmbedding.locallyCompactSpace,
    e.toHomeomorph.isEmbedding.secondCountableTopology⟩

theorem isCompact_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    IsCompact (intKQ p K 1 : Set (KQ p K 1)) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : ContinuousSMul ℚ_[p] (KQ p K 1) := IsModuleTopology.toContinuousSMul ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  obtain ⟨ι, _, b, hb⟩ := GlobalTheory.IntBasisKQ.exists_basis_intKQ p K inferInstance 1 one_pos
  let e : KQ p K 1 ≃L[ℚ_[p]] (ι → ℚ_[p]) := b.equivFun.toContinuousLinearEquiv
  have hset : (intKQ p K 1 : Set (KQ p K 1)) = e ⁻¹' Set.univ.pi fun _ => Metric.closedBall (0 : ℚ_[p]) 1 := by
    ext x
    simp only [SetLike.mem_coe, hb, Set.mem_preimage, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
    rfl
  rw [hset]
  exact e.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun _ => isCompact_closedBall _ _)

theorem isCompact_Kres (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (n : ℕ) :
    IsCompact (Kres p K n 1 : Set (GL (Fin n) (KQ p K 1))) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  set B : Set (Matrix (Fin n) (Fin n) (KQ p K 1)) := {M | ∀ i j, M i j ∈ intKQ p K 1} with hB
  have hBc : IsCompact B := by
    have : B = Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (intKQ p K 1 : Set (KQ p K 1)) := by
      ext M
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_intKQ K
  have hB' : IsCompact (MulOpposite.unop ⁻¹' B : Set (Matrix (Fin n) (Fin n) (KQ p K 1))ᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hBc
  have e : (Kres p K n 1 : Set (GL (Fin n) (KQ p K 1))) = Units.embedProduct _ ⁻¹' (B ×ˢ (MulOpposite.unop ⁻¹' B)) := by
    ext g
    simp only [SetLike.mem_coe, mem_Kres_iff, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply,
      MulOpposite.unop_op, hB, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩, fun h i j => ⟨h.1 i j, h.2 i j⟩⟩
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hBc.prod hB')

open Polynomial in

theorem rho_charpoly_sep (G : HTGroup p) (w : Fin G.m) (y : G.C) (hdeg : (minpoly G.F y).natDegree = G.n)
    (hsep : (minpoly G.F y).Separable) : (G.rho w y).charpoly.Separable := by
  letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  let ρF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    { G.rho w with
      commutes' := fun x => by
        change G.rho w (algebraMap G.F G.C x) = _
        rw [G.rho_F]
        ext i j
        simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
          RingHom.algebraMap_toAlgebra, HTGroup.embW] }
  have hρF : ∀ c, ρF c = G.rho w c := fun _ => rfl
  let Φ : G.Fw w ⊗[G.F] G.C →ₐ[G.Fw w] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    Algebra.TensorProduct.lift (Algebra.ofId (G.Fw w) _) ρF (fun _ _ => Algebra.commute_algebraMap_left _ _)
  have hΦinj : Function.Injective Φ :=
    (Φ : G.Fw w ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) (G.Fw w)).injective
  set z : G.Fw w ⊗[G.F] G.C := (1 : G.Fw w) ⊗ₜ y with hz
  have hΦz : Φ z = G.rho w y := by
    change Φ ((1 : G.Fw w) ⊗ₜ y) = _
    refine (Algebra.TensorProduct.lift_tmul (Algebra.ofId (G.Fw w) (Matrix (Fin G.n) (Fin G.n) (G.Fw w))) ρF _
      (1 : G.Fw w) y).trans ?_
    rw [map_one, one_mul]
    exact hρF y
  set M := G.rho w y with hM
  have hliF : LinearIndependent G.F (fun i : Fin G.n => y ^ (i : ℕ)) := by
    have h := linearIndependent_pow (K := G.F) y
    rw [hdeg] at h
    exact h
  have hliC : LinearIndependent (G.Fw w) (fun i : Fin G.n => z ^ (i : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := G.Fw w) hliF
    convert h using 1
    funext i
    simp [z, Algebra.TensorProduct.tmul_pow]
  have hMint : IsIntegral (G.Fw w) M := Algebra.IsIntegral.isIntegral M
  have hQ0 : minpoly (G.Fw w) M ≠ 0 := minpoly.ne_zero hMint
  have hzQ : aeval z (minpoly (G.Fw w) M) = 0 := by
    apply hΦinj
    rw [map_zero, ← Polynomial.aeval_algHom_apply, hΦz, minpoly.aeval]
  have hdegQ : G.n ≤ (minpoly (G.Fw w) M).natDegree := by
    by_contra hlt
    push_neg at hlt
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at hzQ
    have hc := Fintype.linearIndependent_iff.1 hliC (fun i => (minpoly (G.Fw w) M).coeff i) hzQ
    apply hQ0
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_zero]
    by_cases hk : k < G.n
    · exact hc ⟨k, hk⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  set Pv := (minpoly G.F y).map (algebraMap G.F (G.Fw w)) with hPv
  have hPvM : aeval M Pv = 0 := by
    rw [hPv, Polynomial.aeval_map_algebraMap, hM, ← hρF, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hyint : IsIntegral G.F y := Algebra.IsIntegral.isIntegral y
  have hPvmon : Pv.Monic := (minpoly.monic hyint).map _
  have hPvdeg : Pv.natDegree = G.n := by
    rw [hPv, Polynomial.natDegree_map, hdeg]
  have hdvd : minpoly (G.Fw w) M ∣ Pv := minpoly.dvd (G.Fw w) M hPvM
  have hmin : minpoly (G.Fw w) M = Pv :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hMint) hPvmon hdvd (by omega)).symm
  have hchar : M.charpoly = Pv := by
    have h1 : minpoly (G.Fw w) M ∣ M.charpoly := Matrix.minpoly_dvd_charpoly M
    have h2 : M.charpoly.natDegree = G.n := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    rw [hmin] at h1
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hPvmon (Matrix.charpoly_monic M) h1
      (by omega)
  rw [hchar, hPv]
  exact hsep.map

theorem loc (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {n : ℕ}
    (γ : GL (Fin n) (KQ p K 1)) (hγ : (γ : Matrix (Fin n) (Fin n) (KQ p K 1)).charpoly.Separable)
    (S₂ : Finset (GL (Fin n) (KQ p K 1))) :
    ∃ S : Finset (GL (Fin n) (KQ p K 1)), ∀ h : GL (Fin n) (KQ p K 1),
      (∃ s ∈ S₂, ∃ k₁ ∈ Kres p K n 1, ∃ k₂ ∈ Kres p K n 1, h⁻¹ * γ * h = k₁ * s * k₂) →
      ∃ a : GL (Fin n) (KQ p K 1), a * γ = γ * a ∧ ∃ s ∈ S, ∃ k ∈ Kres p K n 1, h = a * s * k := by
  obtain ⟨hlc, hsc⟩ := kq_lc K
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  haveI : IsArtinianRing (KQ p K 1) := IsArtinianRing.of_finite ℚ_[p] (KQ p K 1)
  have hK := isCompact_Kres K n
  have hO := isOpen_Kres p K inferInstance n 1 one_pos
  set Ω : Set (GL (Fin n) (KQ p K 1)) := ⋃ s ∈ S₂,
    (fun x : GL (Fin n) (KQ p K 1) × GL (Fin n) (KQ p K 1) => x.1 * s * x.2) ''
      ((Kres p K n 1 : Set _) ×ˢ (Kres p K n 1 : Set _)) with hΩdef
  have hΩ : IsCompact Ω := S₂.isCompact_biUnion fun s _ => (hK.prod hK).image (by fun_prop)
  obtain ⟨C, hC, hCx⟩ := GlobalTheory.Orb.isProperOrbit_GL (A := KQ p K 1) (g := γ) hγ Ω hΩ
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun c : C => (c : GL (Fin n) (KQ p K 1)) • (Kres p K n 1 : Set (GL (Fin n) (KQ p K 1))))
    (fun c => hO.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, Set.mem_smul_set.2 ⟨1, one_mem _, by simp⟩⟩)
  refine ⟨t.image fun c : C => (c : GL (Fin n) (KQ p K 1)), fun h ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩ => ?_⟩
  have hmem : h⁻¹ * γ * h ∈ Ω := Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, he.symm⟩
  obtain ⟨u, hu, huC⟩ := hCx h hmem
  have := ht huC
  simp only [Set.mem_iUnion] at this
  obtain ⟨c, hc, hx⟩ := this
  obtain ⟨k, hk, hck⟩ := Set.mem_smul_set.1 hx
  refine ⟨u⁻¹, ?_, c, Finset.mem_image_of_mem _ hc, k, hk, ?_⟩
  · have hu' : u * γ = γ * u := GlobalTheory.Orb.mem_cent.1 hu
    calc u⁻¹ * γ = u⁻¹ * (γ * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * γ) * u⁻¹ := by rw [hu']
      _ = γ * u⁻¹ := by group
  · have e : u * h = (c : GL (Fin n) (KQ p K 1)) * k := hck.symm
    calc h = u⁻¹ * (u * h) := by group
      _ = u⁻¹ * c * k := by rw [e]; group

end GlobalTheory.FinAtP

namespace GlobalTheory.FinAtP

variable {p : ℕ} [Fact p.Prime]

theorem gl_one_comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem prod_fin (G : HTGroup p) (γ : Gr G 1)
    (hγ : ∀ w, ((γ.2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).charpoly.Separable)
    (S₂ : Finset (Gr G 1)) :
    ∃ S : Finset (Gr G 1), ∀ h : Gr G 1,
      (∃ s ∈ S₂, ∃ k₁ ∈ KHT p G.m G.n 1 G.Fw, ∃ k₂ ∈ KHT p G.m G.n 1 G.Fw, h⁻¹ * γ * h = k₁ * s * k₂) →
      ∃ a : Gr G 1, a * γ = γ * a ∧ ∃ s ∈ S, ∃ k ∈ KHT p G.m G.n 1 G.Fw, h = a * s * k := by
  choose Sw hSw using fun w => loc (G.Fw w) (γ.2 w) (hγ w) (S₂.image fun s => s.2 w)
  refine ⟨(Fintype.piFinset Sw).image fun t => ((1 : GL (Fin 1) (Qr p 1)), t), ?_⟩
  rintro h ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩
  have hw : ∀ w, ∃ a : GL (Fin G.n) (KQ p (G.Fw w) 1), a * γ.2 w = γ.2 w * a ∧
      ∃ s ∈ Sw w, ∃ k ∈ Kres p (G.Fw w) G.n 1, h.2 w = a * s * k := fun w =>
    hSw w (h.2 w) ⟨s.2 w, Finset.mem_image_of_mem _ hs, k₁.2 w, (Subgroup.mem_prod.1 hk₁).2 w (Set.mem_univ _),
      k₂.2 w, (Subgroup.mem_prod.1 hk₂).2 w (Set.mem_univ _), congrArg (fun x : Gr G 1 => x.2 w) he⟩
  choose a ha s' hs' k hk hk' using hw
  refine ⟨(h.1, a), Prod.ext (gl_one_comm _ _) (funext ha), (1, s'),
    Finset.mem_image.2 ⟨s', Fintype.mem_piFinset.2 hs', rfl⟩, (1, k),
    Subgroup.mem_prod.2 ⟨one_mem _, fun w _ => hk w⟩, Prod.ext (by simp) (funext fun w => ?_)⟩
  simp [hk' w]

theorem exists_finset_cosets {H : Type} [Group H] (K₀ K : Subgroup H) (hK : K.relIndex K₀ ≠ 0) :
    ∃ T : Finset H, ∀ k ∈ K₀, ∃ t ∈ T, ∃ k' ∈ K, k = t * k' := by
  haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hK⟩
  haveI : Finite (K₀ ⧸ K.subgroupOf K₀) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K₀ ⧸ K.subgroupOf K₀) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : H), fun k hk => ?_⟩
  set q : K₀ ⧸ K.subgroupOf K₀ := QuotientGroup.mk ⟨k, hk⟩
  have hq : (Quotient.out q)⁻¹ * (⟨k, hk⟩ : K₀) ∈ K.subgroupOf K₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  rw [Subgroup.mem_subgroupOf] at hq
  refine ⟨((Quotient.out q : K₀) : H), Finset.mem_image_of_mem _ (Finset.mem_univ _), _, hq, ?_⟩
  simp

theorem charpoly_formGroupToPadicPoints_component (G : HTGroup p) (β : G.Cˣ) (y : grp G β) (w : Fin G.m) :
    (((toP1 G β y).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).charpoly =
      (G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).charpoly.map (inclK p (G.Fw w) 1).toRingHom := by
  rw [← Matrix.charpoly_map]
  rfl

end GlobalTheory.FinAtP
