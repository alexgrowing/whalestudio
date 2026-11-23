import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.CompleteDVRExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CurveDVRPrecompleteFinite

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open IsLocalRing in
private theorem fpd_prec_finite {O M : Type} [CommRing O] [IsNoetherianRing O] (I : Ideal O)
    [IsAdicComplete I O] [AddCommGroup M] [Module O M] [Module.Finite O M] : IsPrecomplete I M :=
  _root_.UpperTheory.Reformulated.B.PrecompleteOfFiniteOverAdicComplete.curveDVR_prec_finite I

private theorem fpd_prec_cofinal {R : Type} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

open IsLocalRing in
private theorem fpd_complete {R R' : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [IsLocalRing R'] : IsAdicComplete (maximalIdeal R') R' := by
  haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    fpd_prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 (fpd_prec_finite _))
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hP }

open IsLocalRing in
private theorem fpd_ext {A k k₁ : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)] [Field k] [Field k₁] [Finite k₁]
    (f : k →+* k₁) (j : k →+* A) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (φ : A →+* B) (j₁ : k₁ →+* B),
      IsAdicComplete (maximalIdeal B) B ∧ Finite (ResidueField B) ∧ Function.Injective φ ∧ IsLocalHom φ ∧
        ∀ a, j₁ (f a) = φ (j a) := by
  classical
  let K := FractionRing A
  let Kb := AlgebraicClosure K
  letI : Algebra k k₁ := f.toAlgebra
  letI : Algebra k Kb := ((algebraMap A Kb).comp j).toAlgebra
  haveI : Module.Finite k k₁ := Module.Finite.of_finite
  haveI : Module.IsTorsionFree k k₁ := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree k Kb := DivisionSemiring.to_moduleIsTorsionFree
  let g : k₁ →ₐ[k] Kb := IsAlgClosed.lift
  have hint : ∀ x : k₁, IsIntegral A (g x) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simpa using isIntegral_zero
    · have h1 : IsOfFinOrder (Units.mk0 x hx) := isOfFinOrder_of_finite _
      obtain ⟨m, hm, h2⟩ := isOfFinOrder_iff_pow_eq_one.1 h1
      have h3 : x ^ m = 1 := by simpa using congrArg Units.val h2
      refine IsIntegral.of_pow hm ?_
      rw [← map_pow, h3, map_one]
      exact isIntegral_one
  let L := IntermediateField.adjoin K (Set.range g)
  haveI : Finite (Set.range g) := (Set.finite_range g).to_subtype
  haveI : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨x, rfl⟩
      exact (hint x).tower_top)
  obtain ⟨hfin, hdvr⟩ := UpperTheory.V.Pr.T.completeDVRExt (A := A) (K := K) (L := L)
  let gL : k₁ →+* L := (g : k₁ →+* Kb).codRestrict L fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
  have hmem : ∀ x, gL x ∈ integralClosure A L := fun x =>
    (isIntegral_algHom_iff (L.val.restrictScalars A) Subtype.val_injective).1 (hint x)
  have hinj : Function.Injective (algebraMap A (integralClosure A L)) := by
    intro x y h
    have h' : algebraMap A L x = algebraMap A L y := congrArg Subtype.val h
    rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L y] at h'
    exact IsFractionRing.injective A K ((algebraMap K L).injective h')
  have hf : (algebraMap A (integralClosure A L)).Finite := RingHom.finite_algebraMap.2 hfin
  haveI hl : IsLocalHom (algebraMap A (integralClosure A L)) := hf.to_isIntegral.isLocalHom hinj
  refine ⟨integralClosure A L, inferInstance, inferInstance, hdvr, algebraMap _ _,
    gL.codRestrict (integralClosure A L) hmem, fpd_complete (R := A), Module.finite_of_finite (ResidueField A),
    hinj, hl, fun a => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact g.commutes a

open IsLocalRing UpperTheory.V.Alg in
private theorem fpd_cont {Γ A B : Type} [TopologicalSpace Γ] [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] {x : Γ → A} (h : AdicCont (maximalIdeal A) x) :
    AdicCont (maximalIdeal B) fun g => φ (x g) := by
  intro N
  have hle : maximalIdeal A ^ N ≤ (maximalIdeal B ^ N).comap φ := by
    refine le_trans ?_ (Ideal.le_comap_pow φ N)
    exact Ideal.pow_right_mono (fun a ha => map_nonunit φ a ha) N
  exact (h N).comp (Ideal.quotientMap _ φ hle)

open IsLocalRing UpperTheory.V.Fr in
theorem UpperTheory.V.Pr.finPtDown :
    UpperTheory.V.Pr.FinPtDown := by
  intro l _ c c₁ f _ _ Φ n H A _ _ hA _ _ ρ hρ hψ g
  haveI : IsDiscreteValuationRing A := hA.toIsDiscreteValuationRing
  haveI := UpperTheory.V.UnitaryThreeInertia.Coef.finite_residue c₁
  obtain ⟨B, _, _, hB, φ, j₁, hc, hfin, hinj, hloc, hj⟩ :=
    fpd_ext (A := A) f (algebraMap (ResidueField c.O) A)
  letI : Algebra (ResidueField c₁.O) B := j₁.toAlgebra
  letI : Algebra c₁.O B := (j₁.comp (residue c₁.O)).toAlgebra
  haveI : IsScalarTower c₁.O (ResidueField c₁.O) B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hl : IsLocalHom (algebraMap c₁.O B) := RingHom.isLocalHom_comp j₁ (residue c₁.O)
  haveI : IsCD c₁.O B := { toIsDiscreteValuationRing := hB, complete := hc, isLocalHom := hl, fin := hfin }
  let ρ₀ := ρ.map φ
  let ρ₁ : NRep (Φ.ext f) n B := ⟨ρ₀.r, ρ₀.ψ, ρ₀.pol, ρ₀.diag, ρ₀.ord⟩
  have key : ∀ a, ResidueField.map φ (ResidueField.map (algebraMap c.O A) a) =
      ResidueField.map (algebraMap c₁.O B) (f a) := by
    intro a
    obtain ⟨b, hb⟩ := residue_surjective (f a)
    obtain ⟨a, rfl⟩ := residue_surjective a
    rw [← hb, ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue,
      IsScalarTower.algebraMap_apply c.O (ResidueField c.O) A, ← hj]
    exact congrArg (fun t => residue B (j₁ t)) hb.symm
  have hz : ∀ (s : Φ.Γ) (m : ℤ), (((Φ.ext f).Ψ s ^ m : (ResidueField c₁.O)ˣ) : ResidueField c₁.O) =
      f ((Φ.Ψ s ^ m : (ResidueField c.O)ˣ) : ResidueField c.O) := by
    intro s m
    show ((Units.map f.toMonoidHom (Φ.Ψ s) ^ m : (ResidueField c₁.O)ˣ) : ResidueField c₁.O) = _
    rw [← map_zpow]
    rfl
  have h1 : IsLiftA c₁.O ρ₁ := by
    refine ⟨⟨fun i j => fpd_cont φ (hρ.cont.1 i j), fun v i => fpd_cont φ (hρ.cont.2 v i)⟩,
      ⟨fun s i => ?_, fun v i s => ?_⟩, fun s i j hij => ?_⟩
    · exact (congrArg (ResidueField.map φ) (hρ.bar.1 s i)).trans ((key _).trans (congrArg _ (hz _ _).symm))
    · exact (congrArg (ResidueField.map φ) (hρ.bar.2 v i s)).trans ((key _).trans (congrArg _ (hz _ _).symm))
    · exact (congrArg (ResidueField.map φ) (hρ.diag s i j hij)).trans (map_zero _)
  have h2 := H B ρ₁ h1 (fun v i s hs h => by
    have h' : Φ.Ψ (Φ.loc v s) = 1 := Units.ext (f.injective ((congrArg Units.val h).trans (map_one f).symm))
    show Units.map φ.toMonoidHom (ρ.ψ v i s) = 1
    rw [hψ v i s hs h', map_one]) g
  apply Polynomial.map_injective φ hinj
  rw [← Matrix.charpoly_map, Polynomial.map_prod]
  refine h2.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ← hj]
  exact congrArg (fun t => Polynomial.X - Polynomial.C (j₁ t)) (hz _ _)
