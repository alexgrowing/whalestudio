import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep2
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Clifford
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MatGstar
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.SubSmulMulSubSmulEqZeroOfQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsIsFlagOnOfEigenvectorNormalSubgroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

namespace UpperTheory.V.Pr.LkAut2

open Matrix

private theorem kills_open {Ω C : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Group C] {M : ℕ} (hM : 1 ≤ M)
    {φ : G ℚ Ω →* C} (hφ : Af.KillsMu M φ) : IsOpen (φ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

private theorem exists_two {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2)
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ n : ℤ, cycBar ℚ Ω l s ^ n = 1 → n = 0 := by
  have hu : IsUnit ((2 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes hl.out Nat.prime_two).2 h2
  obtain ⟨u, hu⟩ := hu
  obtain ⟨s, hs, e⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
  refine ⟨s, hs, fun n hn => ?_⟩
  have e2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = ((2 : ℚ) : Qbar l) := by
    show ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) (cycZ ℚ Ω l s : ℤ_[l]) = _
    rw [e, hu, map_natCast]
    simp
  have e3 := congrArg Units.val hn
  rw [Units.val_zpow_eq_zpow_val, e2, Units.val_one, ← Rat.cast_zpow] at e3
  have e4 : (2 : ℚ) ^ n = 1 := by exact_mod_cast e3
  exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).1 e4

private theorem eigvec {k : Type} [Field k] (M : GL (Fin 3) k) (X : Matrix (Fin 3) (Fin 3) k) (a : k)
    (h0 : (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * X * (M : Matrix (Fin 3) (Fin 3) k)) 0 0 = a)
    (h : ∀ i j, wt i j < 0 →
      (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * X * (M : Matrix (Fin 3) (Fin 3) k)) i j = 0) :
    X *ᵥ ((M : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) = a • ((M : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) := by
  have e : (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * X * (M : Matrix (Fin 3) (Fin 3) k)) *ᵥ Pi.single 0 1 =
      a • Pi.single 0 1 := by
    rw [Matrix.mulVec_single_one]
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h 1 0 (by decide)
    · simpa using h 2 0 (by decide)
  rw [← Matrix.mulVec_smul, ← e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Units.mul_inv, Matrix.one_mul]

private theorem flag {Γ k : Type} [Group Γ] [Field k] (I : Subgroup Γ) (W : Γ →* GL (Fin 2) k) (Ψ : Γ →* kˣ)
    (X : Γ → Matrix (Fin 3) (Fin 3) k) (M : GL (Fin 3) k)
    (hW : ∀ s ∈ I, (W s).val = corner (X s)) (hb : ∀ s ∈ I, ∀ a b, Odd (wt a b) → X s a b = 0) (h1 : ∀ s ∈ I, X s 1 1 = 1)
    (hd : ∀ s ∈ I, (W s).val.det = 1)
    (h0 : ∀ s ∈ I, (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * X s * (M : Matrix (Fin 3) (Fin 3) k)) 0 0 = Ψ s)
    (h : ∀ s ∈ I, ∀ i j, wt i j < 0 →
      (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * X s * (M : Matrix (Fin 3) (Fin 3) k)) i j = 0)
    (hs : ∃ s ∈ I, (Ψ s : k) ^ 2 ≠ 1) :
    Af.IsFlagOn W I ![Ψ.comp I.subtype, Ψ⁻¹.comp I.subtype] := by
  obtain ⟨s₀, hs₀, hs₀'⟩ := hs
  set v : Fin 3 → k := (M : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1 with hv
  have hv0 : v ≠ 0 := fun h0 => by
    have := congrArg (fun x => (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ x) 0) (hv.symm.trans h0)
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    simp at this
  have hev : ∀ s ∈ I, X s *ᵥ v = (Ψ s : k) • v := fun s hs => eigvec M _ _ (h0 s hs) (h s hs)
  have hv1 : v 1 = 0 := by
    have := congrFun (hev s₀ hs₀) 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hb s₀ hs₀ 1 0 (by decide), hb s₀ hs₀ 1 2 (by decide),
      h1 s₀ hs₀, zero_mul, zero_add, add_zero, Pi.smul_apply, smul_eq_mul] at this
    by_contra hne
    exact hs₀' (by rw [← mul_right_cancel₀ hne this, one_pow])
  obtain ⟨κ, hflag, hκ⟩ := UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup I I W Ψ ![v 0, v 2]
    (fun d hd s hs => mul_mem (mul_mem (inv_mem hd) hs) hd)
    (fun h0 => hv0 (by
      funext i
      fin_cases i
      · exact congrFun h0 0
      · exact hv1
      · exact congrFun h0 1))
    (fun s hs => by
      have a0 := congrFun (hev s hs) 0
      have a2 := congrFun (hev s hs) 2
      rw [hW s hs]
      funext i
      fin_cases i
      · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, hv1, corner] using a0
      · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, hv1, corner] using a2)
    hd ⟨s₀, hs₀, hs₀'⟩
  have e : κ = ![Ψ.comp I.subtype, Ψ⁻¹.comp I.subtype] := by
    funext i
    fin_cases i
    · exact MonoidHom.ext fun s => (hκ s s.2).1
    · exact MonoidHom.ext fun s => (hκ s s.2).2
  exact e ▸ hflag

section Red

variable {O A Γ : Type} [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A] [Group Γ]
  {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {r : Γ →* GG 3 A}

private theorem red_ent (h : UnitaryThreeInertia.Red η Ψ r) (g : Γ) :
    residue A ((r g).mat 0 0) = residue A (algebraMap O A (Ψ g)) ∧
    residue A ((r g).mat 2 2) = residue A (algebraMap O A ((Ψ g)⁻¹ : Oˣ)) ∧ residue A ((r g).mat 0 2) = 0 := by
  have h0 := (residue_eq_zero_iff _).2 (h.red g 0 0)
  have h1 := (residue_eq_zero_iff _).2 (h.red g 2 2)
  have h2 := (residue_eq_zero_iff _).2 (h.red g 0 2)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0 h1 h2
  refine ⟨h0.trans ?_, h1.trans ?_, h2.trans ?_⟩ <;> simp [GG.mat, tor_val, wt1]

private theorem det_one [NoZeroDivisors A] (h : UnitaryThreeInertia.Red η Ψ r) (h2 : IsUnit (2 : O)) (g : Γ)
    (hd : (corner (r g).mat).det ^ 2 = 1) : (corner (r g).mat).det = 1 := by
  obtain ⟨a, b, c⟩ := red_ent h g
  have e : residue A (corner (r g).mat).det = 1 := by
    have : (corner (r g).mat).det = (r g).mat 0 0 * (r g).mat 2 2 - (r g).mat 0 2 * (r g).mat 2 0 := by
      rw [Matrix.det_fin_two]; rfl
    rw [this, map_sub, map_mul, map_mul, a, b, c, ← map_mul, ← map_mul, Units.mul_inv]
    simp
  rcases mul_self_eq_one_iff.1 ((sq _).symm.trans hd) with h1 | h1
  · exact h1
  · exfalso
    have := (h2.map ((residue A).comp (algebraMap O A))).ne_zero
    rw [h1, map_neg, map_one] at e
    rw [map_ofNat] at this
    exact this (by linear_combination -e)

private theorem sq_of_trace [IsLocalHom (algebraMap O A)] (h : UnitaryThreeInertia.Red η Ψ r) (g : Γ)
    (ht : (r g).mat 0 0 + (r g).mat 2 2 = 0) : ((barChar O Ψ g : (ResidueField O)ˣ) : ResidueField O) ^ 2 = -1 := by
  obtain ⟨a, b, -⟩ := red_ent h g
  have e := congrArg (residue A) ht
  rw [map_add, a, b, ← map_add, ← map_add, map_zero, residue_eq_zero_iff, mem_maximalIdeal, map_mem_nonunits_iff,
    ← mem_maximalIdeal, ← residue_eq_zero_iff, map_add] at e
  have e2 : residue O (Ψ g) * residue O ((Ψ g)⁻¹ : Oˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  show residue O (Ψ g) ^ 2 = -1
  linear_combination residue O (Ψ g) * e - e2

end Red

private theorem norm_lt {l : ℕ} [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O]
    [Module.Finite ℤ_[l] O] (b : O) (hb : ¬ IsUnit b) : ‖(b : PadicAlgCl l)‖ < 1 := by
  rcases eq_or_ne b 0 with rfl | h0
  · simp
  have h := UpperTheory.V.Base.normO l O b h0
  have hv : (IsDiscreteValuationRing.addVal O b).toNat ≠ 0 := by
    rw [Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff,
      IsDiscreteValuationRing.addVal_eq_top_iff]
    exact fun h => h.elim hb h0
  have hl : ((l : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have h1 := pow_lt_one₀ (by positivity) hl hv
  rw [← h] at h1
  by_contra hn
  exact absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))

private theorem norm_lt' {l : ℕ} [Fact l.Prime] (c : Coef l) (A : Subalgebra c.O (PadicAlgCl l))
    [hA : IsDiscreteValuationRing A] [Module.Finite c.O A] (b : A) (hb : ¬ IsUnit b) : ‖(b : PadicAlgCl l)‖ < 1 :=
  haveI : IsDiscreteValuationRing (A.restrictScalars ℤ_[l]) := hA
  haveI : Module.Finite ℤ_[l] (A.restrictScalars ℤ_[l]) := Module.Finite.trans (R := ℤ_[l]) c.O A
  norm_lt (A.restrictScalars ℤ_[l]) b hb

set_option linter.overlappingInstances false in
private theorem cont_val {A κ Γ : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [NormedField κ] (j : A →+* κ)
    (hj : ∀ b, ¬ IsUnit b → ‖j b‖ < 1) [TopologicalSpace Γ] (f : Γ → A)
    (hf : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal A ^ n) (f g)) :
    Continuous fun g => j (f g) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hm := hϖ.maximalIdeal_eq
  have hb : ∀ n : ℕ, ∀ x ∈ maximalIdeal A ^ (n + 1), ‖j x‖ ≤ ‖j ϖ‖ ^ n := by
    intro n x hx
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    have := hj (ϖ * a) fun h => hϖ.not_isUnit (isUnit_of_mul_isUnit_left h)
    rw [pow_succ, mul_assoc, map_mul, norm_mul, map_pow, norm_pow]
    exact mul_le_of_le_one_right (by positivity) this.le
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (hj ϖ hϖ.not_isUnit)
  filter_upwards [(hf (n + 1)).eventually_eq g] with x hx
  rw [dist_eq_norm, ← map_sub]
  exact (hb n _ (Ideal.Quotient.eq.1 hx)).trans_lt hn

private theorem cont_of_open {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [NormedField k] {n : ℕ}
    (W : Γ →* GL (Fin n) k) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)) (X : Γ → Matrix (Fin n) (Fin n) k)
    (hX : Continuous X) (h : ∀ g ∈ U, (W g).val = X g) : Continuous W := by
  have hc : Continuous fun g => (W g).val := by
    refine continuous_of_continuousAt_one ((Units.coeHom _).comp W) (hX.continuousAt.congr ?_)
    filter_upwards [hU.mem_nhds U.one_mem] with g hg
    exact (h g hg).symm
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  simp only [← map_inv]
  exact hc.comp continuous_inv

private theorem irr_sub {Γ κ k : Type} [Group Γ] [Field κ] [IsAlgClosed κ] [CharZero κ] [Field k] (W : Γ →* GL (Fin 2) κ)
    (U H : Subgroup Γ) [H.Normal] (hab : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H) (hU : MatIrr U fun g => (W g).val)
    (χ : Γ →* kˣ) (ht : ∀ g ∈ U, (W g).val.trace = 0 → (χ g : k) ^ 2 = -1) (h : Γ) (hh : h ∈ H) (hhU : h ∈ U)
    (hχ : χ h ^ 2 ≠ 1) : MatIrr H fun g => (W g).val := by
  intro V hV
  by_contra hne
  obtain ⟨φ, h1, h2, -, P, hP⟩ := exists_selfTwist (W.comp U.subtype) (H.subgroupOf U) (fun a b => hab a b)
    (fun V' hV' => hU V' fun g hg => hV' ⟨g, hg⟩ trivial) (fun hi => hne (hi V fun g hg => hV g hg))
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 1 := by
    by_contra hn
    push Not at hn
    exact h1 (MonoidHom.ext hn)
  have key : ∀ g : U, φ g ≠ 1 → (χ g : k) ^ 2 = -1 := fun g hg => by
    refine ht g g.2 ?_
    have e := congrArg (fun Y => ((P⁻¹ : GL (Fin 2) κ).val * Y).trace) (hP g trivial)
    simp only [] at e
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one, Matrix.trace_smul, smul_eq_mul] at e
    by_contra h0
    exact hg (Units.ext (mul_right_cancel₀ h0 (e.trans (one_mul _).symm)))
  have e1 := key g hg
  have e2 := key (g * ⟨h, hhU⟩) (by rwa [map_mul, show φ ⟨h, hhU⟩ = 1 from h2 hh, mul_one])
  rw [Subgroup.coe_mul, map_mul, Units.val_mul, mul_pow, e1] at e2
  refine hχ (Units.ext ?_)
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  linear_combination -e2

private theorem comm_mem (L Ω : Type) [Field L] [NumberField L] [Field Ω] [CharZero Ω] [Algebra L Ω] [IsAbelianGalois ℚ L]
    (a b : G ℚ Ω) : a * b * a⁻¹ * b⁻¹ ∈ Base.galOf ℚ L Ω := by
  intro x
  have h : AlgEquiv.restrictNormalHom L (a * b * a⁻¹ * b⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, IsMulCommutative.is_comm.comm (AlgEquiv.restrictNormalHom L a)]
    group
  rw [← AlgEquiv.restrictNormal_commutes]
  exact congrArg (fun s : L ≃ₐ[ℚ] L => algebraMap L Ω (s x)) h

private theorem isIrr_of {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (W : Γ →* GL (Fin 2) k) (f : Γ' →* Γ) (H : Subgroup Γ)
    (hH : H ≤ f.range) (h : MatIrr H fun g => (W g).val) : Af.IsIrr (W.comp f) :=
  ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun V _ hV => h V fun g hg v hv => by
    obtain ⟨s, rfl⟩ := hH hg
    exact hV s v hv⟩

private theorem tw_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) :
    Af.tw (Af.tw r χ) χ⁻¹ = r := by
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [Af.tw_val, Af.tw_val, smul_smul, MonoidHom.inv_apply, Units.inv_mul, one_smul]

private theorem det_star {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) :
    (corner (Jmat R 3 * Xᵀ * Jmat R 3)).det = (corner X).det := by
  have e : ∀ Y : Matrix (Fin 3) (Fin 3) R, (corner Y).det = Y 0 0 * Y 2 2 - Y 0 2 * Y 2 0 := fun Y => by
    rw [Matrix.det_fin_two]; rfl
  rw [e, e]
  simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev, mul_comm]

private theorem conj_mat {D C κ : Type} [Group D] [CommRing C] [CommRing κ] (f : C →+* κ) (r : D →* GG 3 C) (h : GL (Fin 3) C) (g : D)
    (hg : (r g).right = 1) (a b : Fin 3) :
    ((((GeneralLinearGroup.map f h)⁻¹ : GL (Fin 3) κ) : Matrix (Fin 3) (Fin 3) κ) * (r g).mat.map f *
      (GeneralLinearGroup.map f h : Matrix (Fin 3) (Fin 3) κ)) a b = f ((conjBy h⁻¹ r g).mat a b) := by
  have e : (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (r g).mat * h := by
    simp [conjBy, GG.mat, hg]
  rw [e, ← map_inv, ← Matrix.map_apply (f := f), Matrix.map_mul, Matrix.map_mul]
  rfl

end UpperTheory.V.Pr.LkAut2

open UpperTheory.V.Pr.LkAut2 in
theorem UpperTheory.V.Pr.autEnd2_of_autPt :
    RankTwoAutomorphyDescendsFromAbelianCMToRat → AutNewform → Sd.TwC → Sd.AlgCyc → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)} (k : GalLink D.η D.Ψ D.cc g₁ B M L Φ) [CharP (ResidueField c.O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → B.valuation (l : Ω) < 1 →
      ∀ (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ), Sd.IsAlgChar ι ka → AutPt k 2 ι ka → AutEnd2 c D.η D.Ψ D.cc g₁ B e ι := by
  intro hDown hNew hTw hAlg Ω _ _ _ K _ _ _ l hl c N _ e ψ D g₁ B M L _ _ _ _ Φ k _ C₀ hok hM hB ι ka hka hA
  intro A _ _ r hr hII h11 W hW _
  obtain ⟨hcc, hηc, -, hηl, -, -, h2, -⟩ := dat_facts D
  obtain ⟨hk1, hk2, hk3, -⟩ := eta_killsMu D
  haveI := k.ab
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  haveI : FaithfulSMul c.O A := (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h =>
    Subtype.ext (congrArg A.val h)
  haveI : IsLocalHom (algebraMap c.O A) := Algebra.IsIntegral.isLocalHom _ _
  haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  have hW' : ∀ g ∈ D.η.ker, (W g).val = (corner (r g).mat).map A.val := hW
  have hblk : Block D.η r := fun g hg a b h => Subtype.ext (hII.1 g hg a b h)
  have hirr : MatIrr D.η.ker fun g => (W g).val := fun V hV => hII.2 V fun g hg v hv => by
    have : (W g).val.mulVec v ∈ V := hV g hg v hv
    rwa [hW g hg] at this
  have hopen : IsOpen (D.η.ker : Set (G ℚ Ω)) := hηl.isOpen_fiber 1
  have hcont : Continuous W := by
    refine cont_of_open W D.η.ker hopen _ (continuous_matrix fun i j => ?_) hW
    exact cont_val (A.val : A →+* PadicAlgCl l) (norm_lt' c A) (fun g => (r g).mat (![0, 2] i) (![0, 2] j)) fun n =>
      (hr.cont n).comp fun X => X (![0, 2] i) (![0, 2] j)
  have hdW : ∀ g ∈ D.η.ker, (W g).val.det = A.val (corner (r g).mat).det := fun g hg => by
    rw [hW' g hg, AlgHom.map_det]
    rfl
  have hdet : ∀ g ∈ D.η.ker, (W g).val.det = 1 := fun g hg => by
    obtain ⟨s1, s2⟩ := mat_gstar r D.cc g hr.norm.atc ((hr.red.mult _).trans hηc) ((hr.red.mult _).trans hg)
    have e1 := hdW _ (show gstar D.cc g ∈ D.η.ker from (hr.red.mult _).symm.trans s2)
    rw [s1, det_star, ← hdW g hg] at e1
    have e2 : Matrix.GeneralLinearGroup.det (W (gstar D.cc g)) * Matrix.GeneralLinearGroup.det (W g) = 1 := by
      have := congrArg (Matrix.GeneralLinearGroup.det.comp W) hcc
      rw [map_mul, map_one] at this
      show (Matrix.GeneralLinearGroup.det.comp W) (D.cc * g⁻¹ * D.cc) * (Matrix.GeneralLinearGroup.det.comp W) g = 1
      rw [map_mul, map_mul, map_inv, mul_right_comm _ _⁻¹, this, one_mul, inv_mul_cancel]
    have e3 : (W (gstar D.cc g)).val.det * (W g).val.det = 1 := congrArg Units.val e2
    rw [e1, hdW g hg, ← map_mul] at e3
    rw [hdW g hg, det_one hr.red h2 g ((sq _).trans (Subtype.ext e3)), map_one]
  have hcyc : Af.IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) :=
    ⟨_, Matrix.GeneralLinearGroup.det.comp W, hk2, fun s hs => Units.ext (hdet s (hk1 s hs)), by simp⟩
  obtain ⟨hg, eg⟩ := k.g0
  have hηg : D.η g₁ = 1 := by
    have h := k.del ⟨g₁, hg⟩
    rw [eg] at h
    exact h.symm.trans Φ.g0.2
  have hirrL : Af.IsIrr (W.comp (Base.galEmb ℚ L Ω)) := by
    refine isIrr_of W _ _ (Base.range_galEmb ℚ L Ω).ge (irr_sub W D.η.ker (Base.galOf ℚ L Ω) (comm_mem L Ω) hirr
      (barChar c.O D.Ψ) (fun g hg ht => sq_of_trace hr.red g (Subtype.ext ?_)) g₁ (k.gal ▸ ⟨hg, hηg⟩) hηg ?_)
    · rw [hW g hg, Matrix.trace_fin_two] at ht
      exact ht
    · have h := k.psi ⟨g₁, hg⟩
      rw [eg] at h
      exact h ▸ hok.baseSubgroup_spec
  obtain ⟨ρ, r1, r2, r3⟩ := exists_nrep2 k hok hM hcc r hr hblk
  obtain ⟨π, p1, -, p3⟩ := hA A ρ r1 r3 (W.comp (Base.galEmb ℚ L Ω)) (fun s => by
    rw [r2]
    exact hW' _ (k.gal.le (Base.galEmb_mem ℚ L Ω s)).2) hirrL
  have hC := hTw L Ω l ι 2 _ ka⁻¹ ((hAlg L Ω l ι).2.2 ka hka) ⟨π, p1, p3⟩
  rw [tw_tw] at hC
  have hR := hDown L Ω l ι W hcont hcyc hirrL
    ⟨D.η, D.cc, D.conj, hηc, fun s => (k.gal.le (Base.galEmb_mem ℚ L Ω s)).2⟩ hC
  have hΨ : ∀ g, Chr.dirG ℚ Ω ψ g = 1 → D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) := fun g hg => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Base.chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [hg, mul_one, map_zpow]
    rfl
  refine hNew Ω l ι e D.gd.e_pos W hcont (isIrr_of W (MonoidHom.id _) _ (fun g _ => ⟨g, rfl⟩) hirr) hR B hB
    (D.η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker) (hopen.inter (kills_open (NeZero.pos N) hk3)) ?_
  obtain ⟨h, -, hT⟩ := hr.ord
  obtain ⟨s₀, hs₀, hn⟩ := exists_two D.gd.l_odd B hB
  have hID : ∀ s ∈ Ine (F := ℚ) B, s ∈ Dec (F := ℚ) B := fun s hs => Ine_le_Dec B hs
  have hf := flag (D.η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker ⊓ Ine (F := ℚ) B) W (cycBar ℚ Ω l ^ (e : ℤ))
    (fun g => (UnitaryThreeInertia.push A.val r g).mat) (Matrix.GeneralLinearGroup.map (A.val : A →+* PadicAlgCl l) h)
    (fun s hs => hW s hs.1.1) (fun s hs => hII.1 s hs.1.1) (fun s hs => congrArg Subtype.val (h11 s hs.1.1))
    (fun s hs => hdet s hs.1.1) (fun s hs => ?_) (fun s hs i j hij => ?_) ?_
  · convert hf using 1
    funext i
    fin_cases i
    · rfl
    · simp
  · refine (conj_mat _ r h s ((hr.red.mult _).trans hs.1.1) 0 0).trans ?_
    have := hT.ine ⟨s, hID s hs.2⟩ hs.2 hs.1.1 0
    refine (congrArg A.val this).trans ?_
    rw [MonoidHom.zpow_apply, ← hΨ s hs.1.2]
    simp [UnitaryThreeInertia.psi, wt1]
    rfl
  · refine (conj_mat _ r h s ((hr.red.mult _).trans hs.1.1) i j).trans ?_
    exact (congrArg A.val (hT.tri ⟨s, hID s hs.2⟩ hs.1.1 i j hij)).trans (map_zero _)
  · refine ⟨s₀ ^ (2 * Nat.card (ZMod N)ˣ), ⟨⟨?_, ?_⟩, pow_mem hs₀ _⟩, fun h0 => ?_⟩
    · show D.η _ = 1
      rw [map_pow, pow_mul, Int.units_sq, one_pow]
    · show ψ.toUnitHom (Chr.cls ℚ Ω N _) = 1
      rw [map_pow, pow_mul', pow_card_eq_one', one_pow, map_one]
    · have := hn (((2 * Nat.card (ZMod N)ˣ : ℕ) : ℤ) * e * 2) (Units.ext (by
        rw [_root_.zpow_mul, _root_.zpow_mul, zpow_two, ← sq, Units.val_pow_eq_pow_val, _root_.zpow_natCast _ (2 * _), ← map_pow]
        exact h0))
      have h3 : 0 < 2 * Nat.card (ZMod N)ˣ * e * 2 := by
        have := D.gd.e_pos
        have := Nat.card_pos (α := (ZMod N)ˣ)
        positivity
      exact h3.ne' (by exact_mod_cast this)
