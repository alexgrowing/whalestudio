import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.MapRepComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.AutKQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.UnlPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.UnlRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.FreePU
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.AdDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.NiceFour
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.RgAdjConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.LinkEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PhiEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.PtFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResOneOfMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.PowMemOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.HalfPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.CharpolySmulScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.IrrOfStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.SupComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PairJAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CondC
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CondDRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Factor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolQ

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th

section Alg

open Matrix

private theorem factor_chi {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (h : H) : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp

private theorem factor_abs {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : H →* GL (Fin n) A) (hn : 1 ≤ n) (hF : Eb.Full ρ)
    (hD : D.comap φ = W.GDet.ofRep (W.mat ρ)) :
    ∃ ρ₀ : G →* GL (Fin n) A, ρ₀.comp φ = ρ ∧ Eb.Full ρ₀ ∧ D = W.GDet.ofRep (W.mat ρ₀) := by
  have hchi : ∀ h, D.chi (MonoidAlgebra.single (φ h) 1) = (W.GDet.ofRep (W.mat ρ)).chi (MonoidAlgebra.single h 1) :=
    fun h => by rw [← hD, factor_chi]
  have hker : φ.ker ≤ ρ.ker := fun g hg => by
    have h0 := (Eb.trPlus ρ hF).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun h => by
      have e : (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single (h * g) 1) =
          (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1) := by
        unfold W.GDet.tr W.GDet.lam
        rw [← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]
      rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn] at e
      rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, mul_sub, map_sub, Matrix.trace_sub,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]
    rw [map_sub, sub_eq_zero] at h0
    refine Units.ext ?_
    simpa [W.GDet.repAlg, W.mat] using h0
  let ρ₀ : G →* GL (Fin n) A := φ.liftOfSurjective hφ ⟨ρ, hker⟩
  have h0 : ∀ h, ρ₀ (φ h) = ρ h := fun h => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ h
  have hm : ∀ h, W.mat ρ₀ (φ h) = W.mat ρ h := fun h => congrArg Units.val (h0 h)
  refine ⟨ρ₀, MonoidHom.ext h0, ?_, CA.d_gext _ _ fun g i _ _ => ?_⟩
  · refine top_le_iff.1 (le_trans (le_of_eq (Eq.symm hF)) (Submodule.span_mono ?_))
    rintro _ ⟨h, rfl⟩
    exact ⟨φ h, hm h⟩
  · obtain ⟨h, rfl⟩ := hφ g
    unfold W.GDet.lam
    rw [hchi, (AlgebraTools.Det.repApi _).2.1, (AlgebraTools.Det.repApi _).2.1, hm]

private theorem charpoly_eq_prod_flag_characters {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) :
    (W.mat r s).charpoly = ∏ i, ((X : Polynomial k) - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (W.mat r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  refine h3.trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

private theorem irr_conj {H K : Type} [Group H] [Field K] {r r' : H →* M4 K} (h : IsConj4 r r') (hi : Irr r) : Irr r' := by
  obtain ⟨u, hu⟩ := h
  rw [Irr, eq_top_iff]
  intro X _
  have key : ∀ Y ∈ Submodule.span K (Set.range r), (u : M4 K) * Y * (u⁻¹ : (M4 K)ˣ) ∈ Submodule.span K (Set.range r') := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact Submodule.subset_span ⟨g, hu g⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
    | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ a hx
  have := key ((u⁻¹ : (M4 K)ˣ) * X * u) (hi ▸ Submodule.mem_top)
  simpa [mul_assoc] using this

private theorem free_pow {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (α ψ : Fin n → Kˣ) (κ : Kˣ) (m : ℕ)
    (hm : 0 < m) (hα : Pr.FreeRatios α) (h1 : M.charpoly = ∏ i, (X - C (α i : K)))
    (h2 : ((κ : K) • M ^ m).charpoly = ∏ i, (X - C (ψ i : K))) : Pr.FreeRatios ψ := by
  have key : ∀ i, ∃ j, ψ j = κ * α i ^ m := fun i => by
    have e1 : (Matrix.scalar (Fin n) (α i : K) - M).det = 0 := by
      rw [← Matrix.eval_charpoly, h1, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨v, hv, hM⟩ := Matrix.exists_mulVec_eq_zero_iff.2 e1
    have e2 : M *ᵥ v = (α i : K) • v := by
      rw [Matrix.sub_mulVec, sub_eq_zero] at hM
      rw [← hM]
      ext a
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have e3 : ∀ k : ℕ, M ^ k *ᵥ v = (α i : K) ^ k • v := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
    have e4 : (Matrix.scalar (Fin n) ((κ : K) * (α i : K) ^ m) - (κ : K) • M ^ m).det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, e3, smul_smul, sub_eq_zero]
      ext a
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rw [← Matrix.eval_charpoly, h2, eval_prod] at e4
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 e4
    refine ⟨j, Units.ext ?_⟩
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
    simpa using hj.symm
  choose σ hσ using key
  have hinj : Function.Injective σ := fun i j hij => by
    by_contra hne
    exact hα i j hne m hm (mul_left_cancel ((hσ i).symm.trans (hij ▸ hσ j)))
  have hsurj := Finite.surjective_of_injective hinj
  intro i j hij k hk e
  obtain ⟨i, rfl⟩ := hsurj i
  obtain ⟨j, rfl⟩ := hsurj j
  rw [hσ, hσ, mul_pow, mul_pow, ← pow_mul, ← pow_mul] at e
  exact hα i j (fun h => hij (h ▸ rfl)) _ (mul_pos hm hk) (mul_left_cancel e)

end Alg

section Gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem free_up (K L : IntermediateField ℚ Ω) [NumberField K] [NumberField L] {n : ℕ} (r : G ℚ Ω →* GL (Fin n) (Qbar l))
    (hf : FreeAt l (r.comp (resQ K))) (ka : G L Ω →* (Qbar l)ˣ) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1)
    (ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ)
    (hfl : W.HasFlag ((Af.tw (r.comp (resQ L)) ka).comp (Dec (F := L) A).subtype) ψ) :
    ∃ g : Dec (F := L) A, cycZ L Ω l g = 1 ∧ Pr.FreeRatios fun i => ψ i g := by
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨g, hg, hc, α, hα, hcp⟩ := hf A hA
  have hi : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index Ω L]
    exact Module.finrank_pos.ne'
  obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi (resQ K g)
  let g' : G L Ω := IntermediateField.fixingSubgroupEquiv L ⟨_, hmem⟩
  have e : resQ L g' = resQ K (g ^ m) := by rw [map_pow]; rfl
  have hd : g' ∈ Dec (F := L) A := by
    have h1 : resQ K (g ^ m) ∈ Dec (F := ℚ) A := (pow_mem hg m : g ^ m ∈ Dec (F := K) A)
    rw [← e] at h1
    exact h1
  refine ⟨⟨g', hd⟩, ?_, free_pow _ α _ (ka g') m hm hα hcp ?_⟩
  · have h1 : cycZ ℚ Ω l (resQ K (g ^ m)) = 1 := by
      show cycZ K Ω l (g ^ m) = 1
      rw [map_pow, hc, one_pow]
    rw [← e] at h1
    exact h1
  · rw [← charpoly_eq_prod_flag_characters _ _ hfl ⟨g', hd⟩]
    congr 1
    refine Eq.trans ?_ (Af.tw_val (r.comp (resQ L)) ka g').symm
    rw [← map_pow, MonoidHom.comp_apply, e]
    rfl

end Gal

section Core

private theorem par' {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r}
    (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v, StrictAnti (m v)) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : Par x := fun v =>
  ⟨m v, k, hm v, hk, fun i j g hg => by
    have e : x.psi v i g / x.psi v j g * cycBar L Ω l g ^ (m v j - m v i) =
        (x.psi v i g * cycBar L Ω l g ^ (-m v i)) / (x.psi v j g * cycBar L Ω l g ^ (-m v j)) := by
      rw [mul_div_mul_comm, div_eq_mul_inv (_ ^ (-m v i)), ← zpow_neg, ← zpow_add]
      congr 2
      ring
    rw [e, div_pow, hw v i g hg, hw v j g hg, div_one]⟩

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

end Core

section Rg

open scoped Matrix TensorProduct

private theorem rg_twist {Γ k V : Type} [Group Γ] [CommRing k] [AddCommGroup V] [Module k V] (A : Representation k Γ V)
    (p : V →ₗ[k] V) (hp : ∀ x, p (p x) = p x) (hA : ∀ g x, p (A g x) = A g (p x)) (η : Γ →* kˣ) :
    ∃ ρ : Representation k Γ V, ∀ g x, ρ g x = A g (p x) + (η g : k) • A g (x - p x) := by
  refine ⟨{ toFun := fun g => A g ∘ₗ p + (η g : k) • (A g ∘ₗ (LinearMap.id - p))
            map_one' := ?_
            map_mul' := fun g h => ?_ }, fun g x => rfl⟩
  · ext x
    simp
  · ext x
    simp only [map_mul, Units.val_mul, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.id_apply, Module.End.mul_apply, map_add, map_smul, map_sub, hA, hp, sub_self, smul_zero, add_zero,
      mul_smul, smul_sub, smul_add, map_zero]
    module

private theorem rg_sign {K Ω : Type} [Field K] [NumberField K] [IsCMField K] (h : Module.finrank ℚ K = 2) [Field Ω]
    [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] (k : Type) [Field k] :
    ∃ η : G ℚ Ω →* kˣ, (∀ s : G K Ω, η (s.restrictScalars ℚ) = 1) ∧
      ∀ c : G ℚ Ω, (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) → η c = -1 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : K, IsCMField.complexConj K x ≠ x := by
    by_contra hc
    push Not at hc
    exact IsCMField.complexConj_ne_one K (AlgEquiv.ext hc)
  set δ : K := x - IsCMField.complexConj K x with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 hx.symm
  have hδc : IsCMField.complexConj K δ = -δ := by simp [hδ]
  have hsq : δ * δ ∈ maximalRealSubfield K := (IsCMField.complexConj_eq_self_iff K _).1 (by rw [map_mul, hδc]; ring)
  obtain ⟨q, hq⟩ := Af.surjective_algebraMap_real K h ⟨_, hsq⟩
  have hq' : algebraMap ℚ K q = δ * δ := by
    have := congrArg (fun y : maximalRealSubfield K => (y : K)) hq
    simpa using this
  set d : Ω := algebraMap K Ω δ with hd
  have hd0 : d ≠ 0 := by simpa [hd] using hδ0
  have hdd : d * d = algebraMap ℚ Ω q := by rw [IsScalarTower.algebraMap_apply ℚ K Ω, hq', map_mul]
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hne : -d ≠ d := fun e => hd0 (by linear_combination (-1 / 2 : Ω) * e)
  have hpm : ∀ g : G ℚ Ω, g d = d ∨ g d = -d := fun g => by
    have : g d * g d = d * d := by rw [← map_mul, hdd, AlgEquiv.commutes]
    exact mul_self_eq_mul_self_iff.1 this
  refine ⟨{ toFun := fun g => if g d = d then 1 else -1
            map_one' := by simp
            map_mul' := fun g g' => ?_ }, fun s => ?_, fun c ⟨j, hj⟩ => ?_⟩
  · rcases hpm g with h1 | h1 <;> rcases hpm g' with h2 | h2 <;> simp [AlgEquiv.mul_apply, h1, h2, hne]
  · have : (s.restrictScalars ℚ) d = d := s.commutes δ
    simp [this]
  · have : c d = -d := by
      apply j.injective
      rw [hj, hd, ← map_neg (algebraMap K Ω), ← hδc]
      exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K Ω)) δ).symm
    simp [this, hne]

section BK

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]

private theorem rg_bk {ρ ρ' : Representation C (G F Ω) V} (f : V →ₗ[C] V) (hf : ∀ g x, f (ρ g x) = ρ' g (f x))
    {z : G F Ω → V} (hz : ∀ g, f (z g) = z g) (h1 : z ∈ Z1 ρ) (h2 : Af.IsBK l ρ z) : z ∈ Z1 ρ' ∧ Af.IsBK l ρ' z := by
  have hc : ∀ g h, z (g * h) = z g + ρ' g (z h) := fun g h => by
    rw [← hz (g * h), h1.2, map_add, hf, hz, hz]
  refine ⟨⟨h1.1, hc⟩, fun w hw => ?_, fun τ => ?_⟩
  · obtain ⟨A, hA, x, hx⟩ := h2.away w hw
    exact ⟨A, hA, f x, fun s hs => by rw [← hz, hx s hs, map_sub, hf]⟩
  · obtain ⟨j, hj, ⟨hc1, -⟩, x, hx⟩ := h2.above τ
    refine ⟨j, hj, ⟨hc1, fun g h => hc g.1.1 h.1.1⟩,
      LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) x, fun g => ?_⟩
    have key : ∀ y : V ⊗[ℚ_[l]] Loc.Bcr l, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l])
        (Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype) (ρ.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g y) =
        Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype) (ρ'.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g
          (LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Loc.actC, hf]
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
    simp [hz]

end BK

private def rgJ (k : Type) [CommRing k] : GL (Fin 4) k where
  val := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  inv := !![0, 0, 0, -1; 0, 0, -1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

private theorem rgJ_adj {k : Type} [CommRing k] (X : M4 k) : Xᵀ * (rgJ k : M4 k) = (rgJ k : M4 k) * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rgJ, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev]

private noncomputable def rgP (k : Type) [Field k] : M4 k →ₗ[k] M4 k where
  toFun X := (2 : k)⁻¹ • (X - adj X)
  map_add' X Y := by rw [(grp k).2.2.1, ← smul_add]; congr 1; abel
  map_smul' a X := by rw [(grp k).2.2.2.1, ← smul_sub, smul_comm]; rfl

private theorem rgP_apply {k : Type} [Field k] (X : M4 k) : rgP k X = (2 : k)⁻¹ • (X - adj X) := rfl

private theorem rgP_mem {k : Type} [Field k] (X : M4 k) : rgP k X ∈ sp4 k := by
  have h1 : adj (-adj X) = -X := by
    rw [← neg_one_smul k, (grp k).2.2.2.1, (grp k).2.1, neg_one_smul]
  show adj _ = -_
  rw [rgP_apply, (grp k).2.2.2.1, sub_eq_add_neg, (grp k).2.2.1, h1, ← smul_neg]
  congr 1
  abel

private theorem rgP_of_mem {k : Type} [Field k] [CharZero k] {X : M4 k} (h : X ∈ sp4 k) : rgP k X = X := by
  have h' : adj X = -X := h
  rw [rgP_apply, h', sub_neg_eq_add, ← two_smul k, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

private theorem rg_adjConj {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (θ : Γ →* kˣ) (hm : ∀ g, IsGSp (θ g : k) (r g))
    (g : Γ) (X : M4 k) : adj (r g * X * r g⁻¹) = r g * adj X * r g⁻¹ := by
  have h1 : adj (r g) = (θ g : k) • r g⁻¹ := (grp k).2.2.2.2.2.2.1 _ _ _ (hm g) (by rw [← map_mul]; simp)
  have h2 : adj (r g⁻¹) = (θ g⁻¹ : k) • r g := (grp k).2.2.2.2.2.2.1 _ _ _ (hm g⁻¹) (by rw [← map_mul]; simp)
  rw [(grp k).1, (grp k).1, h1, h2]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul]
  simp

private theorem rg_ad {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (g : Γ) (X : M4 k) :
    Loc.adGL r.toHomUnits g X = r g * X * r g⁻¹ := rfl

private theorem rg_pair {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (θ : Γ →* kˣ) (hm : ∀ g, IsGSp (θ g : k) (r g))
    (c s s' : Γ) (hs : s' = c * s * c⁻¹) :
    (r.toHomUnits s : M4 k)ᵀ * (rgJ k * (r.toHomUnits c)⁻¹ : GL (Fin 4) k) * (r.toHomUnits s' : M4 k) =
      (θ s : k) • ((rgJ k * (r.toHomUnits c)⁻¹ : GL (Fin 4) k) : M4 k) := by
  show (r s)ᵀ * ((rgJ k : M4 k) * r c⁻¹) * r s' = (θ s : k) • ((rgJ k : M4 k) * r c⁻¹)
  have h := hm s
  unfold IsGSp at h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by
    rw [← map_mul, ← map_mul, hs]
    congr 1
    group
  rw [mul_assoc, mul_assoc, e, ← mul_assoc, rgJ_adj, mul_assoc, ← mul_assoc (adj _), h, smul_mul_assoc, one_mul, mul_smul_comm]

private theorem rg_alg {Γ k : Type} [Group Γ] [Field k] [CharZero k] (r : Γ →* M4 k) (θ : Γ →* kˣ)
    (hm : ∀ g, IsGSp (θ g : k) (r g)) (η : Γ →* kˣ) :
    ∃ ρ : Representation k Γ (M4 k),
      (∀ g X, η g = 1 → ρ g X = (r.toHomUnits g : M4 k) * X * ((r.toHomUnits g)⁻¹ : GL (Fin 4) k)) ∧
      (∀ g X, η g = -1 → ρ g X = -((((rgJ k * (r.toHomUnits g)⁻¹)⁻¹ : GL (Fin 4) k) : M4 k) * Xᵀ *
        (rgJ k * (r.toHomUnits g)⁻¹ : GL (Fin 4) k))) ∧
      (∀ g X, rgP k (Loc.adGL r.toHomUnits g X) = ρ g (rgP k X)) ∧
      ∀ g X Z, Z * r g⁻¹ ∈ sp4 k → Z * r g⁻¹ = ρ g X - X → Z = -rgP k X * r g - r g * -rgP k X := by
  have hpp : ∀ X, rgP k (rgP k X) = rgP k X := fun X => rgP_of_mem (rgP_mem X)
  have hpA : ∀ g X, rgP k (Loc.adGL r.toHomUnits g X) = Loc.adGL r.toHomUnits g (rgP k X) := fun g X => by
    rw [rgP_apply, rgP_apply, map_smul, map_sub, rg_ad, rg_ad, rg_adjConj r θ hm]
  obtain ⟨ρ, hρ⟩ := rg_twist (Loc.adGL r.toHomUnits) (rgP k) hpp hpA η
  refine ⟨ρ, fun g X h => ?_, fun g X h => ?_, fun g X => ?_, fun g X Z h1 h2 => ?_⟩
  · rw [hρ, h, Units.val_one, one_smul, ← map_add, add_sub_cancel]
    rfl
  · rw [mul_inv_rev, inv_inv]
    show _ = -((r g * ((rgJ k)⁻¹ : GL _ _)) * Xᵀ * ((rgJ k : M4 k) * r g⁻¹))
    have e : rgP k X - (X - rgP k X) = -adj X := by
      rw [rgP_apply]
      match_scalars <;> field_simp <;> ring
    rw [hρ, h, Units.val_neg, Units.val_one, neg_one_smul, ← sub_eq_add_neg, ← map_sub, e, map_neg, rg_ad,
      mul_assoc _ Xᵀ, ← mul_assoc Xᵀ, rgJ_adj]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  · rw [hρ, hpp, sub_self, map_zero, smul_zero, add_zero, hpA]
  · have e1 : Z * r g⁻¹ = r g * rgP k X * r g⁻¹ - rgP k X := by
      rw [← rgP_of_mem h1, h2, map_sub, hρ, map_add, map_smul, hpA, hpA, map_sub, hpp, sub_self, map_zero, smul_zero,
        add_zero, rg_ad]
    have := congrArg (· * r g) e1
    simp only [sub_mul, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
    rw [this]
    noncomm_ring

end Rg
