import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FinMulSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ModelMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ModelFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FinUq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.ThetaMem

open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem ku_theta {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ : K} {k : U3 Δ} (hk : k ∈ KU O Δ) :
    theta Δ k ∈ KU O Δ := by
  intro i j
  simp only [theta]
  exact ⟨(hk i j).2, by simpa using (hk i j).1⟩

private theorem theta_theta {K : Type} [Field K] {Δ : K} (y : U3 Δ) : theta Δ (theta Δ y) = y := by
  apply Subtype.ext
  funext i j
  show star (star (y.1 i j)) = y.1 i j
  exact star_star _

private theorem hasTau_conj {K : Type} [Field K] {Δ τ : K} {δ : U3 Δ} (h : HasTau δ τ) (y : U3 Δ) :
    HasTau (y⁻¹ * δ * theta Δ y) τ := by
  unfold HasTau at h ⊢
  have e : y⁻¹ * δ * theta Δ y * theta Δ (y⁻¹ * δ * theta Δ y) = y⁻¹ * (δ * theta Δ δ * y) := by
    simp only [map_mul, map_inv, theta_theta]
    group
  set w := δ * theta Δ δ with hw
  have e2 : w * y * y⁻¹ = w := by group
  have key := Matrix.charpoly_mul_comm (y⁻¹ : U3 Δ).1 (w * y).1
  have e3 : (w * y).1 * (y⁻¹ : U3 Δ).1 = w.1 := congrArg Subtype.val e2
  rw [e3] at key
  rw [e, ← h]
  exact key

private theorem isIntegral_star_of_isIntegral {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (τ : K)
    {x : Etau K τ} (hx : IsIntegral O x) : IsIntegral O (star x) := by
  let f : Etau K τ →ₐ[O] Etau K τ :=
    { starRingEnd (Etau K τ) with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply O K (Etau K τ)]
        ext <;> simp [starRingEnd_apply] }
  exact hx.map f

private theorem cu_le_cint {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (τ : K) : Cu O τ ≤ Cint O τ := by
  rintro _ ⟨u, rfl⟩
  have hI : ∀ w : (integralClosure O (Etau K τ))ˣ, IsIntegral O (((w : integralClosure O (Etau K τ)) : Etau K τ)) :=
    fun w => (w : integralClosure O (Etau K τ)).2
  refine ⟨?_, ?_⟩
  · simp only [quo, ← map_inv]
    exact (hI u).mul (isIntegral_star_of_isIntegral O τ (hI u⁻¹))
  · simp only [quo, ← map_inv, inv_inv]
    exact (hI u⁻¹).mul (isIntegral_star_of_isIntegral O τ (hI u))

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Z.Sym.Glob.gqG :
    UpperTheory.V.Z.Sym.Glob.GqG := by
  classical
  intro F _ _ Δ D hOk ι hιG θ hθ t hCone τ c d m δ i P hCM hdat hmod
  haveI := hOk.real
  have hΔ : Δ ≠ 0 := hOk.ne0
  have hcz : ∀ v : Pl F, CharZero (Kv v) := fun v => (RingHom.charZero_iff (cv v).injective).mp inferInstance
  have hreg : τ ^ 2 - 4 ≠ 0 := cm_ne hCM
  have hglob := modelFacts F Δ τ c d m δ i P hΔ hdat hmod
  have hloc : ∀ v : Pl F, ∃ (ι' : (Etau (Kv v) (cv v τ))ˣ →* U3 (cv v Δ))
      (P' : Sp (cv v Δ) (cv v τ) ≃ₗ[Lsq (Kv v) (cv v Δ)] Fin 3 → Lsq (Kv v) (cv v Δ)), Models (cv v c) (elmap (cv v) d) (elmap (cv v) m) ((ι δ).1 v) ι' P' ∧
      ∀ (z : (Etau F τ)ˣ) (z' : (Etau (Kv v) (cv v τ))ˣ), (z' : Etau (Kv v) (cv v τ)) = (emap (cv v) τ) ↑z →
        (↑(ι' z') : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v Δ))) = (↑(i z) : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).map ⇑(lmap (cv v) Δ) :=
    fun v => (modelMap F (Kv v) (cv v) Δ τ c d m hdat).2 δ i P hmod _ (hιG δ v)
  choose ιv Pv hMv hιv using hloc
  have hdatv : ∀ v : Pl F, IsDat (cv v c) (elmap (cv v) d) (elmap (cv v) m) :=
    fun v => (modelMap F (Kv v) (cv v) Δ τ c d m hdat).1
  have hΔv : ∀ v : Pl F, cv v Δ ≠ 0 := fun v => (map_ne_zero (cv v)).mpr hΔ
  have hlocF := fun v : Pl F => by
    haveI := hcz v
    exact modelFacts (Kv v) (cv v Δ) (cv v τ) (cv v c) _ _ _ (ιv v) (Pv v) (hΔv v) (hdatv v) (hMv v)
  have hfS : ∀ v ∈ D.Sg, D.fGv t v = (D.S v).fG (t v) := fun v hv => funext fun g => if_pos hv
  have hfN : ∀ v ∉ D.Sg, D.fGv t v = fun g => one (g ∈ KU (Ov v) (cv v Δ)) :=
    fun v hv => funext fun g => if_neg hv
  have hJS : ∀ v ∈ D.Sg, D.Jv v = (D.S v).J := fun v hv => if_pos hv
  have hJN : ∀ v ∉ D.Sg, D.Jv v = KU (Ov v) (cv v Δ) := fun v hv => if_neg hv
  obtain ⟨hphi⟩ : Nonempty (∃ φ, IsDiagT τ φ) := ⟨(iotaEx F Δ).2.2 τ⟩
  set φ := hphi.choose with hφdef
  have hφ : IsDiagT τ φ := hphi.choose_spec
  have hB : {v : Pl F | ¬ (((ι δ).1 v) ∈ KU (Ov v) (cv v Δ) ∧
      ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) ↑u = cv v τ ^ 2 - 4)}.Finite :=
    Filter.eventually_cofinite.mp
      (((rpg (fun v => U3 (cv v Δ)) fun v => KU (Ov v) (cv v Δ)).ae (ι δ)).and (ae_reg hreg))
  set S : Finset (Pl F) := D.Sg ∪ hB.toFinset with hSdef
  have hgood : ∀ v ∉ S, v ∉ D.Sg ∧ ((ι δ).1 v) ∈ KU (Ov v) (cv v Δ) ∧
      ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) ↑u = cv v τ ^ 2 - 4 := by
    intro v hv
    simp only [hSdef, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hv
    exact ⟨hv.1, hv.2⟩
  have hone := fun v (hv : v ∉ S) =>
    oneU (Ov v) (Kv v) (cv v Δ) (cv v τ) (hOk.off v (hgood v hv).1) (cv v c) _ _ (hdatv v) _ (ιv v) (Pv v)
      (hMv v) (hgood v hv).2.1 (hgood v hv).2.2
  have hfin := fun v (hv : v ∉ D.Sg) =>
    finUq (Ov v) (Kv v) (cv v Δ) (cv v τ) (hOk.off v hv) (cv v c) _ _ (hdatv v) _ (ιv v) (Pv v) (hMv v)
  have hGorb := fun v (hv : v ∈ D.Sg) =>
    (hOk.sig v hv).G_orb (t v) (hCone v hv) (cv v τ) (cv v c) _ _ _ (ιv v) (Pv v) (hdatv v) (hMv v)
  have hinv : ∀ v, ∀ u ∈ D.Jv v, ∀ x, D.fGv t v (u⁻¹ * x * theta (cv v Δ) u) = D.fGv t v x := by
    intro v u hu x
    by_cases hv : v ∈ D.Sg
    · rw [hJS v hv] at hu
      rw [hfS v hv]
      have hg := (hOk.sig v hv).G_inv (t v) (hCone v hv)
      rw [(hg u hu _).2, (hg u⁻¹ (inv_mem hu) x).1]
    · rw [hJN v hv] at hu
      rw [hfN v hv]
      have hθu := ku_theta hu
      have e : u⁻¹ * x * theta (cv v Δ) u ∈ KU (Ov v) (cv v Δ) ↔ x ∈ KU (Ov v) (cv v Δ) := by
        constructor
        · intro h
          have := mul_mem (mul_mem hu h) (inv_mem hθu)
          rwa [show u * (u⁻¹ * x * theta (cv v Δ) u) * (theta (cv v Δ) u)⁻¹ = x by group] at this
        · intro h
          exact mul_mem (mul_mem (inv_mem hu) h) hθu
      simp only [e]
  have hcomm : ∀ v (s : (Etau (Kv v) (cv v τ))ˣ),
      (ιv v s)⁻¹ * ((ι δ).1 v) * theta (cv v Δ) (ιv v s) = ((ι δ).1 v) :=
    fun v s => ((hlocF v).2.2.2 _).mpr (Or.inl ⟨s, rfl⟩)
  have hmapKU : ∀ v ∉ S, Subgroup.map (ιv v) (Cint (Ov v) (cv v τ)) ≤ KU (Ov v) (cv v Δ) :=
    fun v hv => Subgroup.map_le_iff_le_comap.mpr (le_of_eq (hone v hv).2.symm)
  have hy : ∀ v ∉ S, ∀ y : U3 (cv v Δ), one (y⁻¹ * ((ι δ).1 v) * theta (cv v Δ) y ∈ KU (Ov v) (cv v Δ)) ≠ 0 →
      ∃ s, ∃ u ∈ KU (Ov v) (cv v Δ), y = ιv v s * u := by
    intro v hv y hne
    have hm : y⁻¹ * ((ι δ).1 v) * theta (cv v Δ) y ∈ KU (Ov v) (cv v Δ) := by
      by_contra hc
      exact hne (by simp [one, hc])
    exact ((hone v hv).1 y).mp hm
  by_cases hAdm : D.admitted t τ
  · have key := gqAbs (fun v => D.Jv v) (fun v => Cint (Ov v) (cv v τ))
      (rpg (fun v => U3 (cv v Δ)) fun v => KU (Ov v) (cv v Δ))
      (rpg (fun v => (Etau (Kv v) (cv v τ))ˣ) fun v => Cu (Ov v) (cv v τ))
      ιv θ (fun v => theta (cv v Δ)) (D.FG t) (D.fGv t) (ι δ) φ (ι.comp i) (scalE τ)
      (fun h v => Subtype.ext ((hιG (i h) v).trans (hιv v h _ (hφ h v)).symm))
      (fun v g => hθ g v) (fun g => rfl) hinv hcomm S
      (by
        intro v hv
        by_cases hs : v ∈ D.Sg
        · rw [hfS v hs, hJS v hs]
          exact (hGorb v hs).1
        · rw [hfN v hs, hJN v hs]
          exact (hfin v hs).2.1)
      (by
        intro v hv
        have hs := (hgood v hv).1
        refine ⟨by rw [hJN v hs], cu_le_cint _ _, by rw [hJN v hs]; exact hmapKU v hv, ?_, ?_⟩
        · rw [hfN v hs]
          show one (((ι δ).1 v) ∈ KU (Ov v) (cv v Δ)) = 1
          simp [one, (hgood v hv).2.1]
        · rw [hfN v hs, hJN v hs]
          exact hy v hv)
      (fun v hv => (Subgroup.map_mono (cu_le_cint _ _)).trans (hmapKU v hv))
      (by
        intro v
        by_cases hs : v ∈ D.Sg
        · rw [hJS v hs]
          intro y
          refine ⟨?_, (hGorb v hs).2.2 (hAdm v hs) y⟩
          intro s hs'
          have hs2 : ιv v s • ((Quotient.out y : U3 (cv v Δ)) : U3 (cv v Δ) ⧸ (D.S v).J) =
              ((Quotient.out y : U3 (cv v Δ)) : U3 (cv v Δ) ⧸ (D.S v).J) := by
            rw [QuotientGroup.out_eq']
            exact hs'
          have hm := (smul_mk_iff _ _ _).mp hs2
          exact (stabLe (Ov v) (Kv v) (cv v Δ) (cv v τ) (hΔv v) (hdatv v).reg).2 (cv v c) _ _ _ (ιv v) (Pv v)
            (hdatv v) (hMv v) _ s ((hOk.sig v hs).J_le hm)
        · rw [hJN v hs]
          exact (hfin v hs).2.2)
      (by
        intro z hz v y
        rw [← hglob.2.1] at hz
        have : (ι.comp i) z = 1 := by rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hz, map_one]
        rw [this, map_one, mul_one, inv_mul_cancel]
        exact one_mem _)
      (massFin F τ hCM φ hφ).1 (massFin F τ hCM φ hφ).2
    refine key.trans ?_
    have hsplit := prod_split D.Sg S Finset.subset_union_left
      (fun v => ((D.S v).cG : ℂ) * one (Ind (D.S v).H (cv v τ) (t v)))
      (fun v => lcount (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m))
      (fun v => orb (ιv v) (Cint (Ov v) (cv v τ)) (theta (cv v Δ)) (D.Jv v) (D.fGv t v) (((ι δ).1 v)))
      (by
        intro v hv
        beta_reduce
        rw [hfS v hv, hJS v hv]
        exact (hGorb v hv).2.1)
      (by
        intro v hv
        beta_reduce
        rw [hfN v hv, hJN v hv]
        exact (hfin v hv).1)
      (by
        intro v hv
        have hs := (hgood v hv).1
        beta_reduce
        rw [← (hfin v hs).1]
        rw [Tf.orbOne _ _ (ιv v) _ (theta (cv v Δ)) _ _ _ ?_ (hcomm v) (hmapKU v hv) (hy v hv)]
        · simp [one, (hgood v hv).2.1]
        · intro u hu x
          have := hinv v u (by rw [hJN v hs]; exact hu) x
          rwa [hfN v hs] at this)
    have hms : ms τ = mass φ (scalE τ)
        ((rpg (fun v => (Etau (Kv v) (cv v τ))ˣ) fun v => Cu (Ov v) (cv v τ)).box fun v => Cint (Ov v) (cv v τ)) := by
      rw [ms, dif_pos hphi]
    have hprod : ∏ v ∈ D.Sg, ((D.S v).cG : ℂ) * one (Ind (D.S v).H (cv v τ) (t v)) = ∏ v ∈ D.Sg, ((D.S v).cG : ℂ) :=
      Finset.prod_congr rfl fun v hv => by simp [one, hAdm v hv]
    show mass φ (scalE τ) _ * ∏ v ∈ S, orb (ιv v) (Cint (Ov v) (cv v τ)) (theta (cv v Δ)) (D.Jv v) (D.fGv t v) ((ι δ).1 v) = _
    rw [hsplit, hprod, hms]
    simp only [one, if_pos hAdm, Dat.nL]
    ring
  · have hz : ∀ y : GA Δ ⧸ D.UG,
        D.FG t ((Quotient.out y)⁻¹ * ι δ * θ (Quotient.out y)) = 0 := by
      intro y
      simp only [Dat.admitted, not_forall] at hAdm
      obtain ⟨v0, hv0, hI⟩ := hAdm
      refine fin_mulSupp (D.fGv t) D.Sg ?_ _ (v := v0) ?_
      · intro v hv k hk
        rw [hfN v hv]
        simp [one, hk]
      · rw [hfS v0 hv0]
        by_contra hne
        apply hI
        refine (hOk.sig v0 hv0).G_supp (t v0) (hCone v0 hv0) _ (cv v0 τ) ?_ hne
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply, hθ]
        exact hasTau_conj (hlocF v0).1 _
    rw [gqOn_zero _ _ _ _ hz]
    simp [one, hAdm]
