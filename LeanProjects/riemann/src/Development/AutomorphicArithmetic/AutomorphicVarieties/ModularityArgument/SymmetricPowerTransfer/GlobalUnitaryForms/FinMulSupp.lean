import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.SmulMkIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.MemCenterSupExistsScalarMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IotaEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.MassFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.EmbAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.StabLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.OrbOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FinD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OneD

open NumberField UpperTheory.V.Z.Sym.Loc

namespace UpperTheory.V.Z.Sym.Glob

variable {F : Type} [Field F] [NumberField F] {Δ : F}

theorem cm_ne [IsTotallyReal F] {τ : F} (h : IsCM τ) : τ ^ 2 - 4 ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro e
  have := h (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  rw [e, map_zero] at this
  exact lt_irrefl _ this

theorem Dat.Ok.ne0 {D : Dat Δ} (h : D.Ok) : Δ ≠ 0 := by
  haveI := h.real
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro e
  have := h.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  rw [e, map_zero] at this
  exact lt_irrefl _ this

theorem cv_reg {τ : F} (h : τ ^ 2 - 4 ≠ 0) (v : Pl F) : cv v τ ^ 2 - 4 ≠ 0 := by
  intro h0
  apply h
  rw [← map_ofNat (cv v) 4, ← map_pow, ← map_sub] at h0
  exact (map_eq_zero (cv v)).1 h0

theorem ae_mem (x : F) : ∀ᶠ v : Pl F in Filter.cofinite, cv v x ∈ v.adicCompletionIntegers F := by
  exact (IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 F) F x).2

theorem ae_unit {x : F} (h : x ≠ 0) : ∀ᶠ v : Pl F in Filter.cofinite, ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v x := by
  filter_upwards [ae_mem x, ae_mem x⁻¹] with v h1 h2
  refine ⟨⟨⟨cv v x, h1⟩, ⟨cv v x⁻¹, h2⟩, ?_, ?_⟩, rfl⟩
  · ext
    simp [← map_mul, h]
  · ext
    simp [← map_mul, h]

theorem ae_reg {τ : F} (h : τ ^ 2 - 4 ≠ 0) :
    ∀ᶠ v : Pl F in Filter.cofinite, ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v τ ^ 2 - 4 := by
  filter_upwards [ae_unit h] with v hv
  obtain ⟨u, hu⟩ := hv
  exact ⟨u, by rw [hu, map_sub, map_pow, map_ofNat]⟩

theorem prod_split (Sg S : Finset (Pl F)) (h : Sg ⊆ S) (a b g : Pl F → ℂ) (h1 : ∀ v ∈ Sg, g v = a v) (h2 : ∀ v ∉ Sg, g v = b v)
    (h3 : ∀ v ∉ S, b v = 1) : ∏ v ∈ S, g v = (∏ v ∈ Sg, a v) * ∏ᶠ (v) (_ : v ∉ Sg), b v := by
  classical
  rw [← Finset.prod_sdiff h, mul_comm, Finset.prod_congr rfl h1]
  congr 1
  rw [finprod_cond_eq_prod_of_cond_iff b (t := S \ Sg)]
  · exact Finset.prod_congr rfl fun v hv => h2 v (Finset.mem_sdiff.1 hv).2
  · intro x hx
    have hxS : x ∈ S := by
      by_contra hS
      exact hx (h3 x hS)
    simp [Finset.mem_sdiff, hxS]

theorem zEx {K : Type} [Field K] {τ : K} (h : τ ^ 2 - 4 ≠ 0) : ∃ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + QuadraticAlgebra.omega := by
  have hu : IsUnit (1 + QuadraticAlgebra.omega : Etau K τ) := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, isUnit_iff_ne_zero]
    simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    intro h0
    apply h
    linear_combination (τ - 2) * h0
  exact ⟨hu.unit, rfl⟩

theorem gqOn_zero {H G : Type} [Group H] [Group G] (j : H →* G) (H₀ : Subgroup H) (U : Subgroup G) (k : G ⧸ U → ℂ) (h : ∀ y, k y = 0) :
    gqOn j H₀ U k = 0 := by
  simp [gqOn, gq, h]

theorem fin_mulSupp {I : Type} {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (f : ∀ v, Gv v → ℂ) (S : Finset I)
    (h : ∀ v ∉ S, ∀ k ∈ K v, f v k = 1) (g : RP Gv K) {v : I} (hv : f v (g.1 v) = 0) : ∏ᶠ v, f v (g.1 v) = 0 := by
  apply finprod_eq_zero (fun w => f w (g.1 w)) v hv
  have hg : {w | ¬ g.1 w ∈ K w}.Finite := Filter.eventually_cofinite.1 g.2
  show (Function.mulSupport _).Finite
  refine (S.finite_toSet.union hg).subset ?_
  intro w hw
  by_contra hc
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hc
  exact hw (h w hc.1 _ hc.2)

theorem hasTr_conj {K : Type} [Field K] {Δ τ : K} {γ : DX Δ} (h : HasTr γ τ) (y : DX Δ) : HasTr (y⁻¹ * γ * y) τ := by
  obtain ⟨hd, ht⟩ := h
  have hd' : ((γ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = 1 := hd
  refine ⟨?_, ?_⟩
  · show (((y⁻¹ * γ * y : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rw [Matrix.det_mul, Matrix.det_mul, hd', mul_one, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  · show (((y⁻¹ * γ * y : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).trace = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    have key := Matrix.trace_units_conj ((y : GL (Fin 2) (Lsq K Δ))⁻¹) (mt γ)
    rw [inv_inv] at key
    exact key.trans ht

theorem gqD (D : Dat Δ) (hD : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) (t : Dat.Par F) (ht : D.Cone t) (τ : F) (hτ : IsCM τ)
    (hA : D.admitted t τ) (γ : DX Δ) (j : (Etau F τ)ˣ →* DX Δ) (hγ : HasTr γ τ) (hj : IsEmb τ γ j) (δ : DX Δ)
    (fv : ∀ v : Pl F, DX (cv v Δ) → ℂ) (hinv : ∀ v, ∀ u ∈ D.J2v v, ∀ x, fv v (u⁻¹ * x * u) = fv v x) (a b : Pl F → ℂ)
    (hloc : ∀ v jv, IsEmb (cv v τ) ((ι γ).1 v) jv → (∀ s, jv s * (ι δ).1 v = (ι δ).1 v * jv s) ∧
      FinOrb jv (MonoidHom.id _) (ZD _ ⊔ D.J2v v) (fv v) ((ι δ).1 v) ∧
      (v ∈ D.Sg → orb jv (Cint (Ov v) _) (MonoidHom.id _) (ZD _ ⊔ D.J2v v) (fv v) ((ι δ).1 v) = a v) ∧
      (v ∉ D.Sg → orb jv (Cint (Ov v) _) (MonoidHom.id _) (ZD _ ⊔ D.J2v v) (fv v) ((ι δ).1 v) = b v ∧
        ((ι γ).1 v ∈ KD _ (Ov v) → (∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v τ ^ 2 - 4) → fv v ((ι δ).1 v) = 1 ∧
          ∀ y, fv v (y⁻¹ * (ι δ).1 v * y) ≠ 0 → ∃ s, ∃ u ∈ ZD _ ⊔ KD _ (Ov v), y = jv s * u))) :
    gqOn (ι.comp j) (scalE τ) D.UZ (fun y => ∏ᶠ v, fv v ((y.out⁻¹ * ι δ * y.out).1 v)) =
      (∏ v ∈ D.Sg, a v) * (ms τ * ∏ᶠ (v) (_ : v ∉ D.Sg), b v) := by
  classical
  haveI := hD.real
  have hτ4 : τ ^ 2 - 4 ≠ 0 := cm_ne hτ
  have hΔ : Δ ≠ 0 := hD.ne0
  have hex : ∃ φ : (Etau F τ)ˣ →* TA τ, IsDiagT τ φ := (iotaEx F Δ).2.2 τ
  have hφ : IsDiagT τ hex.choose := hex.choose_spec
  have hchar : ∀ v : Pl F, CharZero (Kv v) := fun v =>
    charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective
  have hΔv : ∀ v : Pl F, cv v Δ ≠ 0 := fun v => (map_ne_zero (cv v)).2 hΔ
  have hτv : ∀ v : Pl F, cv v τ ^ 2 - 4 ≠ 0 := fun v => cv_reg hτ4 v
  have hγv : ∀ v : Pl F, HasTr ((ι γ).1 v) (cv v τ) := fun v => hasTr_map (cv v) (hι γ v) hγ
  have hjex : ∀ v : Pl F, ∃ jv : (Etau (Kv v) (cv v τ))ˣ →* DX (cv v Δ), IsEmb (cv v τ) ((ι γ).1 v) jv := by
    intro v
    haveI := hchar v
    exact (embAlg (Kv v) (cv v Δ) (cv v τ) (hΔv v) (hτv v) _ (hγv v)).1
  choose jv hjv using hjex
  have hιγ : ∀ᶠ v : Pl F in Filter.cofinite, (ι γ).1 v ∈ KD (cv v Δ) (Ov v) := (ι γ).2
  have hgood : ∀ᶠ v : Pl F in Filter.cofinite,
      (ι γ).1 v ∈ KD (cv v Δ) (Ov v) ∧ (∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v τ ^ 2 - 4) ∧
        cv v τ ∈ v.adicCompletionIntegers F :=
    (hιγ.and (ae_reg hτ4)).and (ae_mem τ) |>.mono fun v h => ⟨h.1.1, h.1.2, h.2⟩
  have hSbfin := Filter.eventually_cofinite.1 hgood
  have hSg : D.Sg ⊆ D.Sg ∪ hSbfin.toFinset := Finset.subset_union_left
  have hnotS : ∀ v ∉ D.Sg ∪ hSbfin.toFinset, v ∉ D.Sg ∧ ((ι γ).1 v ∈ KD (cv v Δ) (Ov v) ∧
      (∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v τ ^ 2 - 4) ∧ cv v τ ∈ v.adicCompletionIntegers F) := by
    intro v hv
    simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
    exact hv
  have hJ : ∀ v ∉ D.Sg, D.J2v v = KD (cv v Δ) (Ov v) := fun v hv => by simp [Dat.J2v, hv]
  have hcomm : ∀ v (s : (Etau (Kv v) (cv v τ))ˣ), (jv v s)⁻¹ * (ι δ).1 v * jv v s = (ι δ).1 v := by
    intro v s
    have hc := (hloc v (jv v) (hjv v)).1 s
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hoff : ∀ v ∉ D.Sg ∪ hSbfin.toFinset, Subgroup.comap (jv v) (ZD (cv v Δ) ⊔ KD (cv v Δ) (Ov v)) =
      Cint (Ov v) (cv v τ) ∧ Subgroup.map (jv v) (Cu (Ov v) (cv v τ)) ≤ KD (cv v Δ) (Ov v) := by
    intro v hv
    obtain ⟨hvSg, hKD, hunit, hint⟩ := hnotS v hv
    have hL := hD.off v hvSg
    exact ⟨(oneD (Ov v) (Kv v) (cv v Δ) (cv v τ) hL (hτv v) _ (jv v) (hγv v) (hjv v) hKD hunit).1,
      cu_map (Ov v) (isIntegral_Ov.2 hint) hunit hL.two (hjv v) hKD⟩
  refine (gqAbs (fun v => ZD (cv v Δ) ⊔ D.J2v v) (fun v => Cint (Ov v) (cv v τ))
    (rpg (fun v : Pl F => DX (cv v Δ)) fun v => KD (cv v Δ) (Ov v))
    (rpg (fun v : Pl F => (Etau (Kv v) (cv v τ))ˣ) fun v => Cu (Ov v) (cv v τ))
    jv (MonoidHom.id _) (fun v => MonoidHom.id _) (fun g => ∏ᶠ v, fv v (g.1 v)) fv (ι δ) hex.choose (ι.comp j)
    (scalE τ) ?_ (fun v g => rfl) (fun g => rfl) ?_ ?_ (D.Sg ∪ hSbfin.toFinset) ?_ ?_ ?_ ?_ ?_
    (massFin F τ hτ hex.choose hφ).1 (massFin F τ hτ hex.choose hφ).2).trans ?_
  · intro h v
    apply dx_ext
    show mt ((ι (j h)).1 v) = mt (jv v ((hex.choose h).1 v))
    rw [hι (j h) v]
    exact (emb_map (cv v) (hι γ v) hj (hjv v) h ((hex.choose h).1 v) (hφ h v)).symm
  · intro v u hu x
    exact conj_sup (hinv v) u hu x
  · intro v s
    exact hcomm v s
  · intro v _
    exact (hloc v (jv v) (hjv v)).2.1
  · intro v hv
    obtain ⟨hvSg, hKD, hunit, hint⟩ := hnotS v hv
    have hl := ((hloc v (jv v) (hjv v)).2.2.2 hvSg).2 hKD hunit
    obtain ⟨h1, h2⟩ := hoff v hv
    rw [hJ v hvSg]
    refine ⟨le_sup_right, ?_, ?_, hl.1, hl.2⟩
    · rw [← h1]
      exact Subgroup.map_le_iff_le_comap.1 (h2.trans le_sup_right)
    · rw [← h1]
      exact Subgroup.map_comap_le _ _
  · intro v hv
    exact (hoff v hv).2
  · intro v
    by_cases hvSg : v ∈ D.Sg
    · have hJS : D.J2v v = (D.S v).J2 := by simp [Dat.J2v, hvSg]
      obtain ⟨z, hz⟩ := zEx (hτv v)
      have hdo := SigOk.D_orb (hD.sig v hvSg) (t v) (ht v hvSg) (cv v τ) _ (jv v) (hτv v) (hγv v) (hjv v) z hz
      haveI := hchar v
      have hsl := (stabLe (Ov v) (Kv v) (cv v Δ) (cv v τ) (hΔv v) (hτv v)).1 _ (jv v) (hγv v) (hjv v)
      show ∀ y : DX (cv v Δ) ⧸ (ZD (cv v Δ) ⊔ D.J2v v), _
      rw [hJS]
      intro y
      refine ⟨?_, hdo.2.2.2.2 (hA v hvSg) y⟩
      intro s hs
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hs
      have hs' : jv v s • ((y.out : DX (cv v Δ)) : DX (cv v Δ) ⧸ (ZD (cv v Δ) ⊔ (D.S v).J2)) = y.out := by
        rw [QuotientGroup.out_eq']
        exact hs
      rw [smul_mk_iff] at hs'
      exact hsl y.out s (sup_le_sup_left (SigOk.levelTwoLeIntegral (hD.sig v hvSg)) _ hs')
    · show ∀ y : DX (cv v Δ) ⧸ (ZD (cv v Δ) ⊔ D.J2v v), _
      rw [hJ v hvSg]
      intro y
      exact (finD (Ov v) (Kv v) (cv v Δ) (cv v τ) (hD.off v hvSg) (hτv v) _ (jv v) (hγv v) (hjv v)).2.2 y
  · intro z hz v y
    obtain ⟨c, hc⟩ := hz
    have hsc : IsScal (Units.map (cv v : F →* Kv v) c) ((ι (j z)).1 v) := by
      unfold IsScal
      rw [hι, hj, ← hc]
      simp only [Units.coe_map, MonoidHom.coe_coe, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
        zero_smul, add_zero]
      ext i k : 1
      by_cases hik : i = k
      · subst hik
        ext <;> simp [lmap, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      · ext <;> simp [lmap, hik]
    have hZ : (ι (j z)).1 v ∈ ZD (cv v Δ) := by
      rw [ZD, Subgroup.mem_subgroupOf]
      refine ⟨Units.map (cv v : F →* Kv v) c, ?_⟩
      ext : 1
      simp
      exact hsc.symm
    show y⁻¹ * (ι (j z)).1 v * y ∈ ZD (cv v Δ) ⊔ D.J2v v
    rw [mul_assoc, scal_comm hsc y, ← mul_assoc, inv_mul_cancel, one_mul]
    exact Subgroup.mem_sup_left hZ
  · have hms : ms τ = mass hex.choose (scalE τ)
        ((rpg (fun v : Pl F => (Etau (Kv v) (cv v τ))ˣ) fun v => Cu (Ov v) (cv v τ)).box
          fun v => Cint (Ov v) (cv v τ)) := by
      rw [ms, dif_pos hex]
    have hb1 : ∀ v ∉ D.Sg ∪ hSbfin.toFinset, b v = 1 := by
      intro v hv
      obtain ⟨hvSg, hKD, hunit, hint⟩ := hnotS v hv
      have hl := (hloc v (jv v) (hjv v)).2.2.2 hvSg
      have hl2 := hl.2 hKD hunit
      have hmap : Subgroup.map (jv v) (Cint (Ov v) (cv v τ)) ≤ ZD (cv v Δ) ⊔ D.J2v v := by
        rw [hJ v hvSg, ← (hoff v hv).1]
        exact Subgroup.map_comap_le _ _
      have horb : ∀ y : DX (cv v Δ), fv v (y⁻¹ * (ι δ).1 v * (MonoidHom.id _) y) ≠ 0 →
          ∃ s, ∃ u ∈ ZD (cv v Δ) ⊔ D.J2v v, y = jv v s * u := by
        rw [hJ v hvSg]
        exact hl2.2
      rw [← hl.1]
      exact (UpperTheory.V.Z.Sym.Tf.orbOne _ _ (jv v) (Cint (Ov v) (cv v τ)) (MonoidHom.id _) (ZD (cv v Δ) ⊔ D.J2v v) (fv v) ((ι δ).1 v)
        (conj_sup (hinv v)) (hcomm v) hmap horb).trans hl2.1
    have e := prod_split D.Sg (D.Sg ∪ hSbfin.toFinset) hSg a b
      (fun v => orb (jv v) (Cint (Ov v) (cv v τ)) (MonoidHom.id _) (ZD (cv v Δ) ⊔ D.J2v v) (fv v) ((ι δ).1 v))
      (fun v hv => (hloc v (jv v) (hjv v)).2.2.1 hv) (fun v hv => ((hloc v (jv v) (hjv v)).2.2.2 hv).1) hb1
    rw [hms]
    change _ * ∏ v ∈ D.Sg ∪ hSbfin.toFinset, orb (jv v) (Cint (Ov v) (cv v τ)) (MonoidHom.id _)
      (ZD (cv v Δ) ⊔ D.J2v v) (fv v) ((ι δ).1 v) = _
    rw [e]
    ring

end UpperTheory.V.Z.Sym.Glob
