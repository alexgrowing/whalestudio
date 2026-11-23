import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem tupN_lam {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  show (-1) ^ i * Polynomial.coeff (D.D (Polynomial A) (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
      (MonoidAlgebra.single 1 Polynomial.X -
        MonoidAlgebra.mapRingHom H Polynomial.C (MonoidAlgebra.single g 1)))) (n - i) = _
  rw [map_sub]
  simp [GDet.lam, GDet.chi, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

private theorem tupN_ofRep {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) : (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (ρ.comp φ) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => simp [GDet.repAlg]

private theorem tupN_X {R σ : Type} [CommRing R] [IsLocalRing R] (a : σ) :
    (MvPowerSeries.X a : MvPowerSeries σ R) ∈ maximalIdeal (MvPowerSeries σ R) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_X]
  exact not_isUnit_zero

theorem UpperTheory.V.Pa.Core.tupN :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T), Adapted T (r := r) → ∀ N, ∃ t : Tup Λ A (A.A N).R, t.D = (A.A N).p.D.comap (πN0 Λ N) ∧ t.ψ = (A.A N).p.ψ ∧ t.s = (A.A N).s (MvPowerSeries.C (MvPowerSeries.X (.inl ()))) ∧ t.U = (A.A N).U ∧ t.y = fun j i => (A.A N).s (MvPowerSeries.X (j, i)) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A hAd N
  haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete (l := l)
  haveI hO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun x hx => by simpa using hx⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hL : IsCO O (abelian₂ O Unit D) := co_mvps O O (Unit ⊕ Fin D)
  haveI hS : IsCO O (Sinf O Unit D T.q n) := co_mvps O (abelian₂ O Unit D) (Fin T.q × Fin n)
  have hC : ∀ x : abelian₂ O Unit D, x ∈ maximalIdeal (abelian₂ O Unit D) →
      (MvPowerSeries.C x : Sinf O Unit D T.q n) ∈ maximalIdeal (Sinf O Unit D T.q n) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      MvPowerSeries.constantCoeff_C]
    exact (IsLocalRing.mem_maximalIdeal x).mp hx
  have hmap : ∀ z : Sinf O Unit D T.q n, z ∈ maximalIdeal (Sinf O Unit D T.q n) →
      (A.A N).s z ∈ maximalIdeal (A.A N).R := by
    intro z hz
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hz
  have hcomp := (A.A N).compat
  have key : ∀ (g : Ph0 Λ) (i : Fin n),
      (r.chib i) ((T.h N).p₀ (πN0 Λ N g)) = (r.chib i) (Λ.h.p₀ (πo0 Λ g)) := by
    intro g i
    have hH := hAd.1 ((T.h N).p₀ (πN0 Λ N g) * (Λ.h.p₀ (πo0 Λ g))⁻¹) (Λ.modH N g) i
    rw [map_mul, map_inv, mul_inv_eq_one] at hH
    exact hH
  refine ⟨⟨(A.A N).p.D.comap (πN0 Λ N), ?_, ?_, (A.A N).p.ψ, ?_,
    (A.A N).s (MvPowerSeries.C (MvPowerSeries.X (.inl ()))), ?_, (A.A N).U, (A.A N).U_res,
    fun j i => (A.A N).s (MvPowerSeries.X (j, i)), ?_⟩, rfl, rfl, rfl, rfl, rfl⟩
  · intro i M
    have h2 := ((A.A N).p.cont i M).comp_continuous (Λ.π0_cont N)
    convert h2 using 1
    funext g
    simp only [Function.comp_apply, tupN_lam]
    try rfl
  · show ((A.A N).p.D.map (res O (A.A N).R : (A.A N).R →+* ResidueField O)).comap (πN0 Λ N) = _
    rw [(A.A N).p.red]
    simp only [Resid.Dbar, tupN_ofRep]
    congr 1
    ext g i j
    simp only [MonoidHom.comp_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      rw [hcomp.1 i, MonoidHom.comp_apply, key]
    · simp [Matrix.diagonal_apply_ne _ hij]
  · intro v i
    have hp := (A.A N).p.psi v i
    exact ⟨hp.cont, fun g => by rw [hp.red g, hcomp.2.1], fun g => by rw [hp.mu g, hcomp.2.2] <;> rfl⟩
  · exact hmap _ (hC _ (tupN_X _))
  · intro j i
    exact hmap _ (tupN_X _)
