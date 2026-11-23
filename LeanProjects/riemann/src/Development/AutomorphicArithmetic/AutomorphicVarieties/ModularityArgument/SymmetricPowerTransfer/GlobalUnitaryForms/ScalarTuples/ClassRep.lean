import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.FourValues
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IsUnitP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup

open NumberField IsDedekindDomain Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open scoped nonZeroDivisors

private theorem reps {G Γ A C : Type} [Group G] [Group Γ] [CommGroup A] [Finite C] (ι : Γ →* G) (N : G →* A)
    (U K : Subgroup G) (Off : G → Prop) (hUK : U.relIndex K ≠ 0) (c : G → C)
    (hc : ∀ g g', c g = c g' → ∃ γ, ∃ k ∈ K, N g = N g' * N (ι γ) * N k)
    (hw : ∀ g, ∃ γ, ∃ u ∈ U, Off (ι γ * g * u)) :
    ∃ Y : Finset G, (∀ y ∈ Y, Off y) ∧ ∀ g, ∃ γ, ∃ s, N s = 1 ∧ ∃ y ∈ Y, ∃ u ∈ U, g = ι γ * s * y * u := by
  classical
  let H : Subgroup G := ((N.comp ι).range ⊔ U.map N).comap N
  haveI : H.Normal := Subgroup.Normal.comap inferInstance N
  have hUH : U ≤ H := fun u hu => Subgroup.mem_sup_right ⟨u, hu, rfl⟩
  have h1 : H.relIndex (H ⊔ K) ≠ 0 := by
    rw [Subgroup.relIndex_sup_left]
    exact fun h => hUK (Subgroup.relIndex_eq_zero_of_le_left hUH h)
  have h2 : Finite (G ⧸ (H ⊔ K)) := by
    refine Finite.of_injective (fun q : G ⧸ (H ⊔ K) => c q.out) fun p q h => ?_
    obtain ⟨γ, k, hk, e⟩ := hc _ _ h
    rw [← p.out_eq', ← q.out_eq', eq_comm, QuotientGroup.eq]
    have : q.out⁻¹ * p.out * k⁻¹ ∈ H := by
      refine Subgroup.mem_sup_left ⟨γ, ?_⟩
      simp only [MonoidHom.comp_apply, map_mul, map_inv, e]
      simp [mul_assoc]
    simpa using mul_mem (Subgroup.mem_sup_left this : _ ∈ H ⊔ K) (Subgroup.mem_sup_right hk)
  have h3 : H.index ≠ 0 := by
    rw [← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ K)]
    exact mul_ne_zero h1 Subgroup.index_ne_zero_of_finite
  haveI := Subgroup.fintypeOfIndexNeZero h3
  choose γ u hu ho using hw
  refine ⟨Finset.univ.image fun q : G ⧸ H => ι (γ q.out) * q.out * u q.out, ?_, fun g => ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact ho _
  · set g' := (g : G ⧸ H).out with hg'
    have : g'⁻¹ * g ∈ H := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    obtain ⟨_, ⟨γ₁, rfl⟩, _, ⟨u₁, hu₁, rfl⟩, e⟩ := Subgroup.mem_sup.1 (Subgroup.mem_comap.1 this)
    have e' : N g = N g' * (N (ι γ₁) * N u₁) := by
      rw [MonoidHom.comp_apply] at e
      rw [e, map_mul, map_inv, mul_inv_cancel_left]
    refine ⟨γ₁ * (γ g')⁻¹, (ι (γ₁ * (γ g')⁻¹))⁻¹ * g * ((u g')⁻¹ * u₁)⁻¹ * (ι (γ g') * g' * u g')⁻¹, ?_,
      ι (γ g') * g' * u g', Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (u g')⁻¹ * u₁, mul_mem (inv_mem (hu _)) hu₁, by group⟩
    simp only [map_mul, map_inv, e']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel

private theorem box_idx {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (J : ∀ v, Subgroup (Gv v)) (S : Finset I) (h1 : ∀ v ∈ S, (J v).relIndex (K v) ≠ 0) (h2 : ∀ v ∉ S, K v ≤ J v) :
    (P.box J).relIndex (P.box K) ≠ 0 := by
  have h : (⨅ v : S, (J v).comap (P.p v)).relIndex (P.box K) ≠ 0 := by
    refine Subgroup.relIndex_iInf_ne_zero fun v h => h1 v v.2 ?_
    rw [Subgroup.relIndex_comap] at h
    exact Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_le_iff_le_comap.2 (iInf_le (fun w => (K w).comap (P.p w)) v.1)) h
  rw [← Subgroup.inf_relIndex_right] at h
  refine fun h' => h (Subgroup.relIndex_eq_zero_of_le_left (fun g hg => Subgroup.mem_iInf.2 fun v => ?_) h')
  by_cases hv : v ∈ S
  · exact Subgroup.mem_iInf.1 hg.1 ⟨v, hv⟩
  · exact h2 v hv (Subgroup.mem_iInf.1 hg.2 v)

private theorem narrow (F : Type) [Field F] [NumberField F] : ∃ (C : Type) (_ : Finite C) (c : (Pl F → ℤ) → C), ∀ n m,
    (∀ᶠ v in Filter.cofinite, n v = 0) → (∀ᶠ v in Filter.cofinite, m v = 0) → c n = c m →
    ∃ z : F, z ≠ 0 ∧ TPos z ∧ ∀ v : Pl F, n v = m v + WithZero.log (v.valuation F z) := by
  have h : ∀ I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ClassGroup.mk F I = ClassGroup.mk F J → ∃ z : F, z ≠ 0 ∧ ∀ v : Pl F,
      FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) - WithZero.log (v.valuation F z) := by
    intro I J e
    have h1 : ClassGroup.mk F (I * J⁻¹) = 1 := by rw [map_mul, map_inv, e, mul_inv_cancel]
    obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact Units.ne_zero _ (hx.trans FractionalIdeal.spanSingleton_zero)
    refine ⟨x, hx0, fun v => ?_⟩
    have := FractionalIdeal.count_mul F v (I * J⁻¹).ne_zero J.ne_zero
    rw [← Units.val_mul, inv_mul_cancel_right, hx, GroundTheory.Global.count_spanSingleton v hx0] at this
    omega
  let ρ : ClassGroup (𝓞 F) → (FractionalIdeal (𝓞 F)⁰ F)ˣ := Function.invFun (ClassGroup.mk F)
  have hρ : ∀ I, ClassGroup.mk F I = ClassGroup.mk F (ρ (ClassGroup.mk F I)) := fun I => (Function.invFun_eq ⟨I, rfl⟩).symm
  choose z hz hv using fun I => h I _ (hρ I)
  let J : (Pl F → ℤ) → (FractionalIdeal (𝓞 F)⁰ F)ˣ := fun n => ∏ᶠ w, GroundTheory.Global.primeIdealUnit w ^ n w
  refine ⟨ClassGroup (𝓞 F) × ((F →+* ℝ) → Prop), inferInstance, fun n => (ClassGroup.mk F (J n), fun σ => 0 < σ (z (J n))), ?_⟩
  intro n m hn hm e
  obtain ⟨e1, e2⟩ := Prod.ext_iff.1 e
  refine ⟨z (J m) / z (J n), div_ne_zero (hz _) (hz _), fun σ => ?_, fun v => ?_⟩
  · have e3 : 0 < σ (z (J n)) ↔ 0 < σ (z (J m)) := iff_of_eq (congrFun e2 σ)
    have a := (map_ne_zero σ).2 (hz (J n))
    have b := (map_ne_zero σ).2 (hz (J m))
    rw [map_div₀]
    rcases a.lt_or_gt with a | a
    · exact div_pos_of_neg_of_neg (b.lt_or_gt.resolve_right fun b => a.not_gt (e3.2 b)) a
    · exact div_pos (e3.1 a) a
  · have a := hv (J n) v
    have b := hv (J m) v
    rw [GroundTheory.Global.count_finprod_primeIdealUnit_zpow _ hn] at a
    rw [GroundTheory.Global.count_finprod_primeIdealUnit_zpow _ hm] at b
    dsimp only at e1
    rw [e1] at a
    rw [map_div₀, WithZero.log_div ((map_ne_zero _).2 (hz _)) ((map_ne_zero _).2 (hz _))]
    omega

section Loc

variable {K : Type} [Field K] {Δ : K}

private theorem det_eq [CharZero K] (g : DX Δ) : (mt g).det = algebraMap K _ (mt g).det.re := by
  have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g.1 = (wJ Δ)⁻¹ * g.1 * (wJ Δ)⁻¹⁻¹ := g.2
  have h1 := congrArg (fun x => (GeneralLinearGroup.det x : Lsq K Δ)) h
  simp only [map_mul, map_inv, mul_right_comm _ (GeneralLinearGroup.det g.1), mul_inv_cancel, one_mul] at h1
  have h2 : star (mt g).det = (mt g).det := by
    rw [← starRingEnd_apply, RingHom.map_det]
    exact h1
  have h3 := congrArg QuadraticAlgebra.im h2
  rw [QuadraticAlgebra.im_star] at h3
  ext
  · simp
  · simpa using (self_eq_neg.1 h3.symm)

private theorem nrd_ex [CharZero K] (Δ : K) : ∃ N : DX Δ →* Kˣ, ∀ g : DX Δ, (Glob.mt g).det = algebraMap K _ (N g : K) := by
  let f : DX Δ →* K :=
    { toFun := fun g => (Glob.mt g).det.re
      map_one' := (congrArg QuadraticAlgebra.re (det_one (n := Fin 2) (R := Lsq K Δ))).trans QuadraticAlgebra.re_one
      map_mul' := fun a b => by
        have : (mt (a * b)).det = (mt a).det * (mt b).det := by rw [← det_mul]; rfl
        rw [this, det_eq a, det_eq b, ← map_mul]
        simp }
  exact ⟨f.toHomUnits, det_eq⟩

variable (O : Type) [CommRing O] [Algebra O K]

private theorem det_int {g : DX Δ} (h : g ∈ KD Δ O) : IsIntegral O (mt g).det := by
  obtain ⟨k, hk⟩ := h
  have : mt g = ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).mapMatrix k.1 :=
    (congrArg Units.val hk).symm
  rw [this, ← RingHom.map_det]
  exact (k.1.det).2

private theorem star_int {x : Lsq K Δ} (h : IsIntegral O x) : IsIntegral O (star x) := by
  let f : Lsq K Δ →ₐ[O] Lsq K Δ := { starRingEnd (Lsq K Δ) with
    commutes' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one]
      ext <;> simp [starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] }
  exact h.map f

private theorem unit_ex (u : Oˣ) (ν : Lsq K Δ) (h : IsIntegral O ν) (e : QuadraticAlgebra.norm ν = algebraMap O K u) :
    ∃ k ∈ KD Δ O, (mt k).det = algebraMap K _ (algebraMap O K u) := by
  let R := integralClosure O (Lsq K Δ)
  let a : R := ⟨ν, h⟩
  let b : R := ⟨star ν, star_int O h⟩
  have e1 : ν * star ν = algebraMap K _ (algebraMap O K u) := by rw [← e, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  have e2 : a * b = algebraMap O R u := Subtype.ext (e1.trans (IsScalarTower.algebraMap_apply O K (Lsq K Δ) u).symm)
  have hu : IsUnit (!![a, 0; 0, b]).det := by
    rw [det_fin_two_of, mul_zero, sub_zero, e2]
    exact u.isUnit.map _
  let k : GL (Fin 2) R := GeneralLinearGroup.mk'' _ hu
  let g := GeneralLinearGroup.map (R.val : R →+* Lsq K Δ) k
  have hg : (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![ν, 0; 0, star ν] := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> rfl
  have hD : g ∈ DX Δ := by
    change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * (wJ Δ)⁻¹⁻¹
    apply Units.ext
    change (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) = !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0]
    rw [hg]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply]
  refine ⟨⟨g, hD⟩, ⟨k, rfl⟩, ?_⟩
  change (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = _
  rw [hg, det_fin_two_of, mul_zero, sub_zero, e1]

private theorem split_ex [CharZero K] (h0 : Δ ≠ 0) (h : IsSquare Δ) (u : Oˣ) :
    ∃ ν : Lsq K Δ, IsIntegral O ν ∧ QuadraticAlgebra.norm ν = algebraMap O K u := by
  obtain ⟨s, rfl⟩ := h
  have hs : s ≠ 0 := left_ne_zero_of_mul h0
  set x := algebraMap O K u with hx
  let ν : Lsq K (s * s) := ⟨(x + 1) / 2, (x - 1) / (2 * s)⟩
  refine ⟨ν, ⟨(Polynomial.X - Polynomial.C (u : O)) * (Polynomial.X - Polynomial.C 1),
    (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _), ?_⟩, ?_⟩
  · rw [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Polynomial.eval₂_C, IsScalarTower.algebraMap_apply O K (Lsq K (s * s)) u, map_one, ← hx]
    ext <;> simp [ν, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  · simp only [QuadraticAlgebra.norm_def, ν]
    field_simp
    ring

end Loc

section Place

variable {F : Type} [Field F] [NumberField F] {v : Pl F} {Δ : Kv v} {N : DX Δ →* (Kv v)ˣ}

private theorem val_one (hN : ∀ g : DX Δ, (Glob.mt g).det = algebraMap _ _ (N g : Kv v)) {g : DX Δ} (hg : g ∈ KD Δ (Ov v)) :
    Valued.v (N g : Kv v) = 1 := by
  have h : ∀ g ∈ KD Δ (Ov v), Valued.v (N g : Kv v) ≤ 1 := fun g hg => by
    have h1 := det_int (Ov v) hg
    rw [hN, isIntegral_algebraMap_iff QuadraticAlgebra.algebraMap_injective] at h1
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
    rw [← hy]
    exact y.2
  have h2 := h _ (inv_mem hg)
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (N g).ne_zero))] at h2
  exact le_antisymm (h g hg) h2

private theorem of_val_one (hN : ∀ g : DX Δ, (Glob.mt g).det = algebraMap _ _ (N g : Kv v))
    (h : ∀ u : (Ov v)ˣ, ∃ ν : Lsq (Kv v) Δ, IsIntegral (Ov v) ν ∧ QuadraticAlgebra.norm ν = algebraMap (Ov v) (Kv v) u)
    (x : (Kv v)ˣ) (hx : Valued.v (x : Kv v) = 1) : ∃ k ∈ KD Δ (Ov v), N k = x := by
  obtain ⟨u, hu⟩ := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (a := (⟨x, hx.le⟩ : Ov v))).2 hx
  obtain ⟨ν, h1, h2⟩ := h u
  obtain ⟨k, hk, e⟩ := unit_ex (Ov v) u ν h1 h2
  refine ⟨k, hk, Units.ext ?_⟩
  rw [hN] at e
  rw [QuadraticAlgebra.algebraMap_injective e, hu]
  rfl

end Place

theorem UpperTheory.V.Z.Sym.Glob.classRep :
    UpperTheory.V.Z.Sym.Glob.ClassRep := by
  intro F _ _ Δ D hD ι hι
  have hΔ : Δ ≠ 0 := by
    haveI := hD.real
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    rintro rfl
    simpa using hD.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  haveI : ∀ v : Pl F, CharZero (Kv v) := fun v => charZero_of_injective_algebraMap (cv v).injective
  choose Nv hNv using fun v : Pl F => nrd_ex (cv v Δ)
  let P := rpg (fun v : Pl F => DX (cv v Δ)) fun v => KD (cv v Δ) (Ov v)
  let N : DA Δ →* ∀ v : Pl F, (Kv v)ˣ := Pi.monoidHom fun v => (Nv v).comp (P.p v)
  have hN : ∀ g v, N g v = Nv v (P.p v g) := fun _ _ => rfl
  obtain ⟨C, _, c, hc⟩ := narrow F
  have hae : ∀ g : DA Δ, ∀ᶠ v in Filter.cofinite, WithZero.log (Valued.v (N g v : Kv v)) = 0 := fun g =>
    (P.ae g).mono fun v hv => by rw [hN, val_one (hNv v) hv, WithZero.log_one]
  have hloc : ∀ (v : Pl F) (u : (Ov v)ˣ), ∃ ν : Lsq (Kv v) (cv v Δ), IsIntegral (Ov v) ν ∧
      QuadraticAlgebra.norm ν = algebraMap (Ov v) (Kv v) u := fun v u => by
    by_cases hv : v ∈ D.Sg
    · exact split_ex (Ov v) ((map_ne_zero _).2 hΔ) (hD.split v hv) u
    · exact normEx _ _ _ (hD.off v hv) u
  have hidx : D.U2.relIndex (P.box fun v => KD (cv v Δ) (Ov v)) ≠ 0 :=
    box_idx P D.J2v D.Sg (fun v hv => by rw [Dat.J2v, if_pos hv]; exact (hD.sig v hv).levelTwoFiniteIndex)
      fun v hv => by rw [Dat.J2v, if_neg hv]
  obtain ⟨Y, hY, h⟩ := reps ι N D.U2 _ D.Off hidx (fun g => c fun v => WithZero.log (Valued.v (N g v : Kv v)))
    (fun g g' e => by
      obtain ⟨z, hz, hp, e⟩ := hc _ _ (hae g) (hae g') e
      obtain ⟨γ, hγ⟩ := normD F Δ D hD z hp
      have h1 : ∀ v, (N (ι γ) v : Kv v) = cv v z := fun v => by
        apply QuadraticAlgebra.algebraMap_injective (a := cv v Δ) (b := 0)
        rw [hN, ← hNv]
        change (Glob.mt ((ι γ).1 v)).det = _
        rw [hι, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hγ]
        ext <;> simp [lmap]
      have h2 : ∀ v, Valued.v ((((N g' v * N (ι γ) v)⁻¹ * N g v : (Kv v)ˣ)) : Kv v) = 1 := fun v => by
        have a : ∀ x : (Kv v)ˣ, Valued.v (x : Kv v) ≠ 0 := fun x => (map_ne_zero _).2 x.ne_zero
        have b : Valued.v (cv v z) = v.valuation F z := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
        have d : Valued.v (N g v : Kv v) = Valued.v ((N g' v * N (ι γ) v : (Kv v)ˣ) : Kv v) := by
          rw [← WithZero.exp_log (a (N g v)), ← WithZero.exp_log (a (_ * _)), e v, Units.val_mul, map_mul,
            WithZero.log_mul (a _) (a _), h1, b]
        rw [Units.val_mul, map_mul, d, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
      choose k hk ek using fun v => of_val_one (hNv v) (hloc v) _ (h2 v)
      obtain ⟨k', hk'⟩ := P.surj k (Filter.Eventually.of_forall hk)
      refine ⟨γ, k', Subgroup.mem_iInf.2 fun v => ?_, funext fun v => ?_⟩
      · rw [Subgroup.mem_comap, hk']
        exact hk v
      · rw [Pi.mul_apply, Pi.mul_apply, hN k', hk', ek, mul_inv_cancel_left])
    (weakD F Δ D hD ι hι)
  refine ⟨Y, hY, fun g => ?_⟩
  obtain ⟨γ, s, hs, r⟩ := h g
  refine ⟨γ, s, Subgroup.mem_iInf.2 fun v => ?_, r⟩
  have h1 := hNv v (P.p v s)
  rw [← hN, hs, Pi.one_apply, Units.val_one, map_one] at h1
  exact Units.ext h1
