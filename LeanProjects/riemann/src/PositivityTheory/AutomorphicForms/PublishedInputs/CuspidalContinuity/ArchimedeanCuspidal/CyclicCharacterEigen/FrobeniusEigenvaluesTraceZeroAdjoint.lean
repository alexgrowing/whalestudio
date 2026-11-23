import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SelfTwGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Ad0IrrMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.QuadraticCharpolyCoeffDifference
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SchurTwistHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Sd.EG

namespace Ad3P.SEGAux

theorem adjoint_zero_twist {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (χ : Γ →* kˣ) : ad0 (tw ρ χ) = ad0 ρ := by
  have hv : ∀ (ρ' : Γ →* GL (Fin 2) k) (s : Γ), (ad0 ρ' s : Matrix (Fin 3) (Fin 3) k) =
      ((ρ' s : Matrix (Fin 2) (Fin 2) k).det)⁻¹ • symSquareMatrixHom k (ρ' s : Matrix (Fin 2) (Fin 2) k) := fun ρ' s => by
    rw [ad0, tw_val]
    simp
  ext s : 1
  apply Units.ext
  rw [hv, hv, tw_val, Matrix.det_smul, Fintype.card_fin]
  have hc : (χ s : k) ≠ 0 := (χ s).ne_zero
  have hd : (ρ s : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := (ρ s).det_ne_zero
  have e : symSquareMatrixHom k ((χ s : k) • (ρ s : Matrix (Fin 2) (Fin 2) k)) = (χ s : k) ^ 2 • symSquareMatrixHom k (ρ s : Matrix (Fin 2) (Fin 2) k) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom] <;> ring
  rw [e, smul_smul]
  congr 1
  field_simp

theorem irrOpen_of_tw {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l))
    (D : Γ →* (Qbar l)ˣ) (h : IrrOpen (tw r D)) : IrrOpen r := fun H hH => by
  have e1 : (tw r D).comp H.subtype = tw (r.comp H.subtype) (D.comp H.subtype) := MonoidHom.ext fun _ => rfl
  have e2 : r.comp H.subtype = tw (tw (r.comp H.subtype) (D.comp H.subtype)) (D.comp H.subtype)⁻¹ := by
    ext s : 1
    apply Units.ext
    rw [tw_val, tw_val, smul_smul]
    simp
  have h1 := h H hH
  rw [e1] at h1
  rw [e2]
  exact (shapeFacts l H 2 _ _).2.2.2.2.2 h1

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem charEig_cyc_inv {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    CharEig ι (cycBar F Ω l)⁻¹ w (normV w : ℂ) := by
  intro A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : cycZ F Ω l s = 1 := Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
      rw [cycZ_toZModPow_eq hw hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
      simp)
    rw [MonoidHom.inv_apply, cycBar, MonoidHom.comp_apply, h1, map_one, inv_one]
  · have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
    rw [MonoidHom.inv_apply, map_inv, inv_inv, h2, map_natCast]

private theorem frobenius_eigenvalues_trace_zero_adjoint {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ρ : G F Ω →* GL (Fin 2) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (a b : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : FrobEig ι ρ w {a, b}) : FrobEig ι (ad0 ρ) w {a / b, 1, b / a} := by
  intro A hA
  obtain ⟨h1, h2⟩ := h A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · apply Units.ext
    rw [ad0, tw_val, MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h1 s hs]
    simp
  · have ha' : ι.symm a ≠ 0 := by simpa using ha
    have hb' : ι.symm b ≠ 0 := by simpa using hb
    have h3 : (ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
        (X - C ((Units.mk0 _ ha' : (Qbar l)ˣ) : Qbar l)) * (X - C ((Units.mk0 _ hb' : (Qbar l)ˣ) : Qbar l)) := by
      apply Polynomial.map_injective ι.toRingHom ι.injective
      rw [h2 σ hσ]
      simp
    rw [(UpperTheory.V.Sd.ad0Facts l (G F Ω) ρ).2.2.2.2.1 _ _ _ h3]
    simp [mul_assoc]

private theorem sub_mem_int {x y : ℂ} {m n : ℤ} (hx : x = (m : ℂ) + (((2 : ℕ) : ℂ) - 1) / 2)
    (hy : y = (n : ℂ) + (((2 : ℕ) : ℂ) - 1) / 2) : ∃ k : ℤ, x - y = (k : ℂ) + (((3 : ℕ) : ℂ) - 1) / 2 :=
  ⟨m - n - 1, by rw [hx, hy]; push_cast; ring⟩

private theorem primRam_lift (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) (u : (ZMod N)ˣ)
    (hu : u ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker) :
    ∃ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω N σ = u := by
  have : Fact r.Prime := ⟨hr⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero (ordCompl[r] N) := ⟨(Nat.ordCompl_pos r (NeZero.ne N)).ne'⟩
  have hcop : (ordCompl[r] N).Coprime r := (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
  have hone : ∀ ζ : Ω, ζ ^ ordCompl[r] N = 1 →
      ζ ^ ((1 : (ZMod (ordCompl[r] N))ˣ) : ZMod (ordCompl[r] N)).val = ζ := fun ζ hζ => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  obtain ⟨w, hw⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r) (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
  obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA w
  refine ⟨σ, hσ, (Chr.clsFacts ℚ Ω N).2.2.1 σ u ?_⟩
  refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨fun ζ hζ => ?_, ?_⟩
  · rw [MonoidHom.mem_ker.1 hu, hone ζ hζ]
    exact (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA _ hcop ζ hζ).2 σ hσ
  · have hc : cyclotomicCharacter Ω r σ.toRingEquiv = w := hσw
    rw [hc, hw]

section Norm

variable {l : ℕ} [hl : Fact l.Prime]

private theorem root_small {x : Qbar l} (h : x ^ l = 1) : ‖x - 1‖ < 1 := by
  have hx := norm_root hl.out.ne_zero h
  have hy : ‖x - 1‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (by simp [hx])
  have e := add_pow_prime_eq hl.out (x - 1) 1
  rw [sub_add_cancel, h, one_pow] at e
  set S := ∑ k ∈ Finset.Ioo 0 l, (x - 1) ^ (k - 1) * 1 ^ (l - k - 1) * ((l.choose k / l : ℕ) : Qbar l) with hS
  have hs : ‖S‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [one_pow, mul_one, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hy) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  have e2 : (x - 1) ^ l = -((l : Qbar l) * ((x - 1) * S)) := by linear_combination -e
  have h3 : ‖x - 1‖ ^ l < 1 := by
    rw [← norm_pow, e2, norm_neg, norm_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_l (mul_le_one₀ hy (norm_nonneg _) hs)
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h3

variable (l) in

private def Uprin : Subgroup (Qbar l)ˣ where
  carrier := {u | ‖(u : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have e : ((u * v : (Qbar l)ˣ) : Qbar l) - 1 = u * (v - 1) + (u - 1) := by push_cast; ring
    show ‖_‖ < 1
    rw [e]
    refine small_add ?_ hu
    rw [norm_mul, norm_eq_one_of hu, one_mul]
    exact hv
  inv_mem' {u} hu := by
    have e : (u : Qbar l) * (((u⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(u - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have := congrArg norm e
    rw [norm_mul, norm_eq_one_of hu, one_mul, norm_neg] at this
    show ‖_‖ < 1
    rw [this]
    exact hu

private theorem cong_mul {a u : (Qbar l)ˣ} (ha : ‖(a : Qbar l)‖ = 1) (hu : u ∈ Uprin l) : Cong (a * u) a := by
  have e : ((a * u : (Qbar l)ˣ) : Qbar l) - a = a * (u - 1) := by push_cast; ring
  unfold Cong
  rw [e, norm_mul, ha, one_mul]
  exact hu

private theorem resSum_of {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)) (Φ : Γ →* (Qbar l)ˣ)
    (ht : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + Φ s)‖ < 1)
    (hd : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det - Φ s‖ < 1) : ResSum ρ ![1, Φ] := by
  intro s i
  have e : (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly - ∏ j, (X - C ((![1, Φ] j s : (Qbar l)ˣ) : Qbar l)) =
      C (-((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + Φ s))) * X +
        C ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det - Φ s) := by
    rw [Matrix.charpoly_fin_two, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_one, map_neg, map_sub, map_add]
    ring
  rw [← coeff_sub, e, coeff_add, coeff_C_mul_X, coeff_C]
  refine small_add ?_ ?_
  · split_ifs
    · rw [norm_neg]; exact ht s
    · simp
  · split_ifs
    · exact hd s
    · simp

private theorem trace_inv {K : Type} [Field K] (g : GL (Fin 2) K) (d : Kˣ) (h : Matrix.GeneralLinearGroup.det g = d⁻¹) :
    ((d : K) • (g : Matrix (Fin 2) (Fin 2) K)).trace = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace := by
  have h1 := congrArg Units.val h
  rw [Matrix.GeneralLinearGroup.val_det_apply] at h1
  rw [Matrix.coe_units_inv, Matrix.inv_def, h1, Ring.inverse_unit, inv_inv, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [add_comm]

end Norm

section Gal

variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem dec_le {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) {γ : G ℚ Ω}
    (hγ : IsFrob A (normV v) γ) (K : Subgroup (G ℚ Ω)) (hI : Ine (F := ℚ) A ≤ K) (hK : γ ∈ K) :
    Dec (F := ℚ) A ≤ K.topologicalClosure := by
  haveI : IsGalois ℚ Ω := {}
  have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω) ⟨K.topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
  refine le_trans (le_sInf ?_) key.ge
  rintro N ⟨hNo, hN⟩
  have h := (Subgroup.le_topologicalClosure _).trans hN
  exact Kum.decGen ℚ Ω A _ γ N hv hγ hNo (hI.trans h) (h hK)

private theorem above_of {ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)} (hρ : Continuous ρ) {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ}
    (hκ : IsFlagOn ρ (Dec (F := ℚ) A) κ) (hI : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = 1)
    (hF : ∀ σ : ↥(Dec (F := ℚ) A), IsFrob A (normV v) (σ : G ℚ Ω) → κ 0 σ ∈ Uprin l) (s : ↥(Dec (F := ℚ) A)) :
    κ 0 s * κ 1 s = Matrix.GeneralLinearGroup.det (ρ s) ∧ κ 0 s ∈ Uprin l := by
  obtain ⟨g, hg⟩ := hκ
  constructor
  · have e : Matrix.GeneralLinearGroup.det (g * ρ s * g⁻¹) = Matrix.GeneralLinearGroup.det (ρ s) := by
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [← e]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]
    simp
  · obtain ⟨γ, hγ⟩ := exists_isFrob hv
    have h1 := dec_le hv hγ (((Uprin l).comap (κ 0)).map (Dec (F := ℚ) A).subtype)
      (fun t ht => ⟨⟨t, ht.1⟩, by
        show κ 0 _ ∈ Uprin l
        rw [hI _ ht]; exact one_mem _, rfl⟩)
      ⟨⟨γ, hγ.1⟩, hF _ hγ, rfl⟩ s.2
    have hc : Continuous fun t : G ℚ Ω => (g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 - 1 :=
      ((continuous_apply 0).comp ((continuous_apply 0).comp
        ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Qbar l))).comp ((continuous_const.mul hρ).mul continuous_const)))).sub continuous_const
    have h2 := closure_minimal (t := {t : G ℚ Ω | ‖(g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 - 1‖ < 1}) (by
      rintro _ ⟨t, ht, rfl⟩
      show ‖(g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 - 1‖ < 1
      rw [(hg t).2]
      exact ht) (isClosed_small hc) h1
    show ‖_‖ < 1
    rw [← (hg s).2]
    exact h2

private theorem ram {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (f : ℂ →+* Qbar l) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) :
    ¬ Ine (F := ℚ) A ≤ (Chr.dirG ℚ Ω (χ.ringHomComp f)).ker := fun hall => by
  have hft : χ.FactorsThrough (ordCompl[p] N) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N p)).2 fun u hu => ?_
    obtain ⟨σ, hσ, rfl⟩ := primRam_lift Ω N p hp A hA u hu
    have h1 := congrArg Units.val (MonoidHom.mem_ker.1 (hall hσ))
    refine MonoidHom.mem_ker.2 (Units.ext (f.injective ?_))
    rw [Units.val_one, map_one]
    exact h1
  have hd : χ.conductor ≤ ordCompl[p] N := Nat.sInf_le hft
  rw [hχ] at hd
  have := Nat.div_lt_self (NeZero.pos N) (Nat.one_lt_pow (hp.factorization_pos_of_dvd (NeZero.ne N) hpN).ne' hp.one_lt)
  omega

private theorem ordExL (P : HypothesesH) (ι : Qbar l ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 3 ≤ k) (hN : ¬ l ∣ N) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (g : Eigenform k N χ)
    (hg : ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)))‖ < 1)
    {ψ : G ℚ Ω →* (Qbar l)ˣ} (hm : Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) = ψ) :
    ∃ c π r, OrdForm ι ψ⁻¹ (1 - (k : ℤ)) c (fun _ => ![0, 1 - (k : ℤ)]) (fun _ => 1) π r ∧
      (∀ s, ‖(r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + (cycBar ℚ Ω l ^ (k - 1) * ψ) s)‖ < 1) ∧ Ad3P.Lifts k N χ g π := by
  classical
  obtain ⟨ω, φ, hω, hval, hφ, hcu⟩ := adelise k N (by omega) χ g
  obtain ⟨π, hreg, ⟨χ', hpol⟩, hinf, hU, hsat⟩ := holRep P ℚ k (by omega) _ ω hω φ _ hφ hcu
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := exR P ℚ Ω l ι 2 one_le_two π χ' hreg hpol
  have hlN : l * N ≠ 0 := mul_ne_zero hl.out.ne_zero (NeZero.ne N)
  set c : Pl ℚ → ℕ := fun w => N.factorization (normV w) with hc
  have hc0 : ∀ w, c w = 0 ↔ ¬ normV w ∣ N := fun w => by
    simp [hc, Nat.factorization_eq_zero_iff, normV_prime w, NeZero.ne N]
  have hLift : Ad3P.Lifts k N χ g π := by
    refine ⟨hinf, Filter.eventually_cofinite.2 ((fin_dvd (NeZero.ne N)).subset fun w hw => ?_)⟩
    by_contra hq
    obtain ⟨B, hB, e⟩ := hsat w ((hc0 w).2 hq)
    exact hw ⟨B, hB, by rw [e, (hval w hq).2]⟩
  set D : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * ψ with hD
  have hDv : ∀ s, (D s : Qbar l) = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) s := fun s => by
    rw [hD, ← hm]; simp
  have hDc : Continuous fun s => (D s : Qbar l) := by
    simp only [hDv]
    exact (cyc_cont.pow _).mul (dirG_cont _)
  have c1 : Continuous fun s : G ℚ Ω => (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp (hG.cont.comp continuous_inv)
  have hdense := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    ((Filter.eventually_cofinite.1 hatt.2).union (fin_dvd hlN))
  have hall : ∀ s, ‖(r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + D s)‖ < 1 ∧
      (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D s := fun s => by
    refine ((isClosed_small (c1.matrix_trace.sub (continuous_const.add hDc))).inter
      (isClosed_eq c1.matrix_det hDc)).closure_subset_iff.2 ?_ (hdense s)
    rintro σ ⟨w, hw, -, A, hA, hσ⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
    obtain ⟨⟨B₁, hB₁, hF⟩, hq⟩ := hw
    have hqN : ¬ normV w ∣ N := fun h => hq (h.mul_left _)
    obtain ⟨B₂, hB₂, e⟩ := hsat w ((hc0 w).2 hqN)
    obtain rfl := hB₁.unique hB₂
    obtain ⟨h2, h3⟩ := tr_det ι _ (((hF A hA).2 σ hσ).trans e)
    have hAq := (over_iff hA _).2 dvd_rfl
    have h1 : (D σ : Qbar l) = ι.symm (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1)) := by
      rw [hDv, cyc_frob (normV_prime w) hAq (fun h => hq (h.mul_right _)) hσ, dirG_frob _ (normV_prime w) hAq hqN hσ]
      simp [mul_comm]
    have h4 := hg _ (normV_prime w)
    rw [map_sub, map_add, map_one, ← h1, ← h2] at h4
    exact ⟨h4, by rw [Set.mem_ofPred_eq, h3, h1, (hval w hqN).2]⟩
  have hlev : ∀ w : Pl ℚ, ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → levL l c w = c w := fun w hw => if_neg hw
  have hlev1 : ∀ w : Pl ℚ, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → levL l c w = 1 := fun w hw => if_pos hw
  have hker : ψ⁻¹.ker = ψ.ker := by ext s; simp
  refine ⟨levL l c, π, r, ⟨hreg, ⟨χ', hpol⟩, hG.cont, hatt, MonoidHom.ext fun s => ?_, ?_, ?_, fun w A hA => ?_, fun w hw => ?_,
    fun w hw hwl => ?_, fun w hw => ?_⟩, fun s => (hall s).1, hLift⟩
  · have h1 := (hall s⁻¹).2
    rw [inv_inv] at h1
    refine (Units.ext h1 : Matrix.GeneralLinearGroup.det (r s) = D s⁻¹).trans ?_
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← mul_inv, map_inv]
    rfl
  · rw [hker, ← hm]
    exact dirG_open _
  · refine (fin_dvd hlN).subset fun w hw => ?_
    by_cases h : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    · exact ((mem_iff w l).1 h).mul_right _
    · rw [Set.mem_ofPred_eq, hlev w h, Ne, hc0, not_not] at hw
      exact hw.mul_left _
  · rw [hker, ← hm]
    by_cases h : normV w ∣ N
    · have h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h' => hN ((mem_iff_eq w hl.out).1 h' ▸ h)
      rw [hlev w h1, hc0]
      exact iff_of_false (ram hχ _ (normV_prime w) h ((over_iff hA _).2 dvd_rfl)) (by simp [h, h1])
    · refine iff_of_true (fun s hs => dirG_unr _ (fun h' => h ((over_iff hA _).1 h')) hs) ?_
      by_cases h1 : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
      · exact Or.inr h1
      · exact Or.inl ((hlev w h1).trans ((hc0 w).2 h))
  · have h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h' => by rw [hlev1 w h'] at hw; exact one_ne_zero hw
    obtain ⟨v, h2, h3, -⟩ := hU w
    rw [show N.factorization (normV w) = 0 from (hlev w h1).symm.trans hw] at h3
    exact ⟨v, h2, h3⟩
  · rw [hlev w hwl] at hw ⊢
    refine ⟨_, hU w, norm_eq_one_of ?_⟩
    have h4 := hg _ (normV_prime w)
    rw [Ne, hc0, not_not] at hw
    rwa [χ.map_nonunit (fun h' => (Nat.Prime.coprime_iff_not_dvd (normV_prime w)).1 ((ZMod.isUnit_iff_coprime _ _).1 h') hw),
      zero_mul, add_zero, map_sub, map_one] at h4
  · have hq := (mem_iff_eq w hl.out).1 hw
    have hqN : ¬ normV w ∣ N := hq ▸ hN
    obtain ⟨B, hB, e⟩ := hsat w ((hc0 w).2 hqN)
    rw [(hval w hqN).2] at e
    have h2 : ‖ι.symm (χ (normV w : ZMod N))‖ = 1 := by
      refine norm_root (n := Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_
      rw [← ZMod.coe_unitOfCoprime _ ((Nat.Prime.coprime_iff_not_dvd (normV_prime w)).2 hqN), ← map_pow, ← map_pow,
        ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one, map_one]
    have h3 : ‖(normV w : Qbar l)‖ < 1 := by rw [hq]; exact norm_l
    have hs : ‖ι.symm (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))‖ < ‖(normV w : Qbar l)‖ := by
      rw [map_mul, norm_mul, h2, one_mul, map_pow, map_natCast, norm_pow]
      exact pow_lt_self_of_lt_one₀ (norm_pos_iff.2 (Nat.cast_ne_zero.2 (normV_prime w).ne_zero)) h3 (by omega)
    have ha : ‖ι.symm (g.a (normV w)) - 1‖ < 1 := by
      have := small_add (hg _ (normV_prime w)) (hs.trans h3)
      rw [← map_add] at this
      rw [← map_one ι.symm, ← map_sub]
      convert this using 3
      ring
    obtain ⟨lam, h5, h6⟩ := stab w ι π hB e ha hs
    refine ⟨hlev1 w hw, ?_, ?_, norm_one, ⟨lam, h5, ?_⟩, fun τ _ => hinf _⟩
    · simp; omega
    · simp
    · simpa using h6

private theorem adjL (P : HypothesesH) (hAd : Ad3P.AdjEig) (ι : Qbar l ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 3 ≤ k)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (g : Eigenform k N χ) (π : TR.CuspSub ℚ 2) (hL : Ad3P.Lifts k N χ g π)
    (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hc : Continuous ρ) (hreg : π.IsRegAlg) (hatt : AttR ι ρ π) (hirr : IrrOpen ρ) :
    IsAutR ι (tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹) := by
  rcases hAd k N hk χ hχ g π hL with ⟨η, hη1, hη2, hη⟩ | ⟨Q, hinf, hfin⟩
  · obtain ⟨δ, hδ1, hδo, hiso, -⟩ := UpperTheory.V.Sd.selfTwGal P.toClassicalTheorems ℚ Ω l ι 2 ρ π.HasSat (fun _ _ _ h h' => h.unique h')
      hc hatt η 2 two_pos hη2 hη1 hη
    refine absurd (UpperTheory.schur_twist_holds _ _ _ 2 ρ δ.ker.subtype δ (hirr _ hδo) ?_ hiso) hδ1
    exact MonoidHom.ext fun s => s.2
  refine ⟨Q, fun v => ?_, ?_, ?_⟩
  · obtain ⟨m, hm, hnd, hz⟩ := hreg v
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hm.1
    have hxy : x ≠ y := by simpa using hnd
    obtain ⟨i, hi⟩ := hz x (by simp)
    obtain ⟨j, hj⟩ := hz y (by simp)
    refine ⟨_, hinf v x y hm, ?_, ?_⟩
    · have h1 : x - y ≠ 0 := sub_ne_zero.2 hxy
      have h2 : (0 : ℂ) ≠ y - x := (sub_ne_zero.2 hxy.symm).symm
      have h3 : x - y ≠ y - x := fun h => h1 (by linear_combination h / 2)
      simp [h1, h2, h3]
    · intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact sub_mem_int hi hj
      · exact ⟨-1, by push_cast; ring⟩
      · exact sub_mem_int hj hi
  · have h1 := UpperTheory.V.Sd.ad0Irr l (G ℚ Ω) ρ hc hirr ⊤ isOpen_univ
    have h2 := UpperTheory.galoisRep_irreducibility_criterion.1 (G ℚ Ω) (⊤ : Subgroup (G ℚ Ω)) (Qbar l) 3 (ad0 ρ)
    exact h2.2.2 _ (h2.2.1 (h2.1 _ h1))
  · have h0 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal :=
      (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
    filter_upwards [hatt.2, hfin, hl] with w ⟨B₁, hB₁, hF⟩ ⟨B, ⟨α, β, hαβ, hB⟩, hPB⟩ hw
    obtain rfl := hαβ.unique hB₁
    subst hB
    refine ⟨_, hPB, ?_⟩
    have hq0 : normV w ≠ 0 := by
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
      obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
      intro h0
      have := (charEig_cyc_inv (Ω := Ω) ι w hw A hA).2 σ hσ
      rw [h0, Nat.cast_zero, map_eq_zero] at this
      exact Units.ne_zero _ this
    have hqR : (0 : ℝ) < normV w := by exact_mod_cast Nat.pos_of_ne_zero hq0
    rw [algSat_eq] at hF ⊢
    set c : ℂ := ((((normV w : ℕ) : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) with hcd
    have hc0 : c ≠ 0 := by
      rw [hcd]; exact_mod_cast (Real.rpow_pos_of_pos hqR _).ne'
    have h1 := frobenius_eigenvalues_trace_zero_adjoint ι ρ w (c * α) (c * β) (mul_ne_zero hc0 α.ne_zero) (mul_ne_zero hc0 β.ne_zero) (by simpa using hF)
    have h2 := UpperTheory.frobenius_eigenvalues_twist ℚ Ω l ι 3 _ _ w _ _ h1 (charEig_cyc_inv ι w hw)
    have h3 : ((((3 : ℕ) : ℝ) - 1) / 2) = 1 := by norm_num
    rw [h3, Real.rpow_one]
    rw [mul_div_mul_left _ _ hc0, mul_div_mul_left _ _ hc0] at h2
    convert h2 using 1
    simp [mul_comm]

private theorem coreA (P : HypothesesH) (hAd : Ad3P.AdjEig) (hl2 : l ≠ 2) (ι : Qbar l ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 3 ≤ k) (hN : ¬ l ∣ N)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (g : Eigenform k N χ)
    (hg : ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)))‖ < 1)
    {φ θ : G ℚ Ω →* (Qbar l)ˣ} (hm : Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) = φ * θ) (hθ : θ ^ l = 1) :
    ∃ ρ, EisRep ι φ θ k ρ ∧ (IrrOpen ρ → IsAutR ι (tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹)) := by
  obtain ⟨c, π, r, H, htr, hL⟩ := ordExL P ι hk hN hχ g hg hm
  have hθU : ∀ s, θ s ∈ Uprin l := fun s => root_small (by
    have := DFunLike.congr_fun hθ s
    rw [MonoidHom.pow_apply] at this
    rw [← Units.val_pow_eq_pow_val, this]; rfl)
  set D : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * (φ * θ) with hD
  set Φ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * φ with hΦ
  have hDv : ∀ s, (D s : Qbar l) = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) s := fun s => by
    rw [hD, ← hm]; simp
  have hDΦ : ∀ s, D s = Φ s * θ s := fun s => by simp [hD, hΦ, mul_assoc]
  have hΦn : ∀ s, ‖(Φ s : Qbar l)‖ = 1 := fun s => by
    have := congrArg norm (hDv s)
    rwa [norm_mul, norm_pow, cyc_norm, dirG_norm, one_pow, mul_one, hDΦ, Units.val_mul, norm_mul, norm_eq_one_of (hθU s), mul_one] at this
  have hDc : Continuous fun s => (D s : Qbar l) := by
    simp only [hDv]
    exact (cyc_cont.pow _).mul (dirG_cont _)
  have hcong : ∀ s, ‖(D s : Qbar l) - Φ s‖ < 1 := fun s => by
    rw [hDΦ]; exact cong_mul (hΦn s) (hθU s)
  have hdr : ∀ s, Matrix.GeneralLinearGroup.det (r s) = (D s)⁻¹ := fun s => by
    refine (DFunLike.congr_fun H.det s).trans ?_
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← mul_inv]
    rfl
  have hdet : ∀ s, (tw r D s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D s := fun s => by
    rw [tw_val, Matrix.det_smul, ← Matrix.GeneralLinearGroup.val_det_apply, hdr, Fintype.card_fin, sq, mul_assoc, Units.mul_inv, mul_one]
  have SF := shapeFacts l (G ℚ Ω) 2 r D
  have hc0 : Continuous fun s => (tw r D s : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
    simp only [tw_val]
    exact hDc.smul (Units.continuous_val.comp H.cont)
  have halg := (algCyc P.toClassicalTheorems ℚ Ω l ι).1 ((k - 1 : ℕ) : ℤ) (φ * θ) (hm ▸ dirG_open _)
  rw [zpow_natCast] at halg
  have hadj : IrrOpen (tw r D) → IsAutR ι (tw (ad0 (tw r D)) (cycBar ℚ Ω l)⁻¹) := fun h => by
    rw [adjoint_zero_twist]
    exact adjL P hAd ι hk hχ g π hL r H.cont H.reg H.att (irrOpen_of_tw r D h)
  refine ⟨tw r D, ⟨Units.continuous_iff.2 ⟨hc0, ?_⟩, SF.2.2.2.2.2 (ordIrr P ℚ Ω l hl2 (splitL hl.out) ι _ _ _ _ _ _ _ H),
    twR P.toClassicalTheorems ℚ Ω l ι 2 r D halg ⟨π, H.reg, H.att⟩, MonoidHom.ext fun s => Units.ext (hdet s),
    resSum_of _ Φ (fun s => ?_) fun s => ?_, fun A hA => ?_, fun A hA => ?_⟩, hadj⟩
  · simp only [← map_inv]
    exact hc0.comp continuous_inv
  · have := small_add (htr s) (hcong s)
    rw [tw_val, trace_inv _ _ (hdr s), ← map_inv]
    convert this using 2
    ring
  · rw [hdet]; exact hcong s
  · refine (shapeFacts l (G ℚ Ω) 2 _ 1).2.1 _ _ _ (Equiv.swap 0 1) (SF.1 _ _ (ordAway P ℚ Ω l ι _ _ _ _ _ _ _ H A hA))
      fun i s hs => ?_
    have h1 : cycZ ℚ Ω l s = 1 := (places ℚ Ω l A).2.2.2 hA hs
    have h2 : D s = (φ * θ) s := by
      rw [hD, MonoidHom.mul_apply, MonoidHom.pow_apply, cycBar, MonoidHom.comp_apply, h1, map_one, one_pow, one_mul]
    fin_cases i
    · show 1 = ((φ * θ) s)⁻¹ * D s
      rw [h2, inv_mul_cancel]
    · show (φ * θ) s = 1 * D s
      rw [h2, one_mul]
  · obtain ⟨w, hw, hwl, hmem⟩ := (ML.placeBasic Ω).2.2.2.2.2.2.2.2.1 A l hl.out hA
    obtain ⟨κ, hκ, hI, hFr⟩ := ordAbove P ℚ Ω l hl2 (splitL hl.out) ι _ _ _ _ _ _ _ H w hmem A hw
    have hI0 : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = 1 := fun s hs => (hI 0 s hs).trans (zpow_zero _)
    have key := above_of H.cont hw hκ hI0 fun σ hσ => by
      have h1 : κ 0 σ⁻¹ * cycBar ℚ Ω l (σ : G ℚ Ω) ^ (0 : ℤ) ∈ Uprin l := hFr σ hσ
      rwa [zpow_zero, mul_one, map_inv, inv_mem_iff] at h1
    have h1 : ∀ s : ↥(Dec (F := ℚ) A), κ 1 s * D s = (κ 0 s)⁻¹ := fun s => by
      rw [eq_inv_iff_mul_eq_one, mul_comm, ← mul_assoc, (key s).1, hdr, inv_mul_cancel]
    refine ⟨_, SF.2.2.1 _ κ hκ, fun i s hs => ?_, fun i s => ?_⟩
    · fin_cases i
      · have h2 : (φ * θ) s = 1 := hm ▸ dirG_unr _ (not_over hl.out hA hN) hs
        show κ 0 s * D s = cycBar ℚ Ω l s ^ ((k : ℤ) - 1)
        rw [hI0 s hs, one_mul, hD, MonoidHom.mul_apply, h2, mul_one, MonoidHom.pow_apply,
          show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]
      · show κ 1 s * D s = cycBar ℚ Ω l s ^ (0 : ℤ)
        rw [h1, hI0 s hs, inv_one, zpow_zero]
    · fin_cases i
      · show Cong (κ 0 s * D s) (Φ s)
        rw [hDΦ, mul_comm, mul_assoc]
        exact cong_mul (hΦn s) (mul_mem (hθU s) (key s).2)
      · show Cong (κ 1 s * D s) 1
        rw [h1]
        exact inv_mem (key s).2

end Gal

end Ad3P.SEGAux
