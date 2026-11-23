import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrInertA
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.ExistsSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

noncomputable section

namespace GlobalTheory.ThK.Dbl.Split

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locpair PositivityTheory.ThKH.Locrep
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt)
open GlobalTheory.Doubling (absE)
open GlobalTheory.SplitFlip (invT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {Y : Spc F E n} (hσ : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v)

omit [NumberField E] in
theorem mem_latW (y : Fin n → AE F E) : y ∈ latW Y v ↔ At (evFin F v) y ∧ compFin F E v ∘ y ∈ latLoc F Y.L v := by
  have e0 : ∀ (a : AF F) (x : E), a • inclR (F := F) (AF F) x = a ⊗ₜ[F] x := fun a x => by
    change (a * 1) ⊗ₜ[F] x = _
    rw [mul_one]
  have key : ∀ y ∈ latW Y v, At (evFin F v) y ∧ compFin F E v ∘ y ∈ latLoc F Y.L v := fun y hy => by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, ha', x, hx, rfl⟩ := hy
      refine ⟨fun u hu => funext fun i => ?_, ?_⟩
      · change u • a • inclR (F := F) (AF F) (x i) = 0
        rw [smul_smul, show u * a = 0 from ha u hu, zero_smul]
      · convert tmul_mem_latLoc ha' hx using 1
        exact funext fun i => congrArg (compFin F E v) (e0 a (x i))
    | zero => exact ⟨at_zero, by convert zero_mem (latLoc F Y.L v) using 1; exact funext fun i => map_zero _⟩
    | add y z _ _ hy hz => exact ⟨at_add hy.1 hz.1, by convert add_mem hy.2 hz.2 using 1; exact funext fun i => map_add _ _ _⟩
    | neg y _ hy =>
      exact ⟨by simpa using at_sub at_zero hy.1, by convert neg_mem hy.2 using 1; exact funext fun i => map_neg _ _⟩
  refine ⟨key y, fun hy => ?_⟩
  have : ∀ z ∈ latLoc F Y.L v, (fun i => sgE E v (z i)) ∈ latW Y v := fun z hz => by
    refine latLoc_induction (p := fun z => (fun i => sgE E v (z i)) ∈ latW Y v) (fun a ha x hx => ?_) ?_
      (fun y z hy hz => ?_) (fun y hy => ?_) hz
    · exact AddSubgroup.subset_closure ⟨sg v a, at_sg a, by rwa [ev_sg], x, hx, funext fun i => (e0 _ _).symm⟩
    · convert zero_mem (latW Y v) using 1; exact funext fun i => map_zero _
    · convert add_mem hy hz using 1; exact funext fun i => map_add _ _ _
    · convert neg_mem hy using 1; exact funext fun i => map_neg _ _
  convert this _ hy.2 using 1
  exact (idem_smul hy.1).symm.trans (funext fun i => (sgE_comp (y i)).symm)

theorem int_iff {m : Matrix (Fin n) (Fin n) (Fv F v)} {L : Submodule (𝓞 E) (Fin n → E)} {b : GL (Fin n) (Fv F v)}
    (hb : IsSplitBasis τ L b) : (∀ u ∈ splitLat τ L, m *ᵥ u ∈ splitLat τ L) ↔
      ∀ i j, ((b⁻¹).1 * m * b.1) i j ∈ v.adicCompletionIntegers F := by
  simp only [hb.mem_iff]
  refine ⟨fun H i j => ?_, fun H u hu i => ?_⟩
  · have := H (b.1 *ᵥ Pi.single j 1) (fun l => by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _]) i
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
  · have : (b⁻¹).1 *ᵥ m *ᵥ u = ((b⁻¹).1 * m * b.1) *ᵥ (b⁻¹).1 *ᵥ u := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [this]
    exact sum_mem fun j _ => mul_mem (H i j) (hu j)

include hσ in
theorem stab_iff {b b' : GL (Fin n) (Fv F v)} (hb : IsSplitBasis τ Y.L b) (hb' : IsSplitBasis (τ.comp σ) Y.L b')
    (g : Matrix (Fin n) (Fin n) (AE F E)) : (∀ y ∈ latW Y v, g *ᵥ y ∈ latW Y v) ↔
      (∀ i j, ((b⁻¹).1 * g.map (piW τ) * b.1) i j ∈ v.adicCompletionIntegers F) ∧
        ∀ i j, ((b'⁻¹).1 * g.map (piW (τ.comp σ)) * b'.1) i j ∈ v.adicCompletionIntegers F := by
  have e : ∀ (t : E →ₐ[F] Fv F v) y, splitVec t (compFin F E v ∘ (g *ᵥ y)) = g.map (piW t) *ᵥ splitVec t (compFin F E v ∘ y) :=
    fun t y => funext fun i => RingHom.map_mulVec (piW t) g y i
  rw [← int_iff τ hb, ← int_iff _ hb']
  refine ⟨fun H => ?_, fun H y hy => ?_⟩
  · have k : ∀ t : E →ₐ[F] Fv F v, ∀ u ∈ splitLat t Y.L, g.map (piW t) *ᵥ u ∈ splitLat t Y.L := by
      rintro t _ ⟨z, hz, rfl⟩
      have c : compFin F E v ∘ (fun i => sgE E v (z i)) = z := funext fun i => comp_sgE _
      have := ((mem_latW _).1 (H _ ((mem_latW _).2 ⟨fun a ha => funext fun i => at_sgE (z i) a ha, c.symm ▸ hz⟩))).2
      exact ⟨_, this, by rw [e, c]⟩
    exact ⟨k _, k _⟩
  · obtain ⟨h1, h2⟩ := (mem_latW _).1 hy
    refine (mem_latW _).2 ⟨at_mulVec_right _ h1, (mem_latLoc_iff_split τ hσ).2 ?_⟩
    rw [e, e]
    exact ⟨H.1 _ ⟨_, h2, rfl⟩, H.2 _ ⟨_, h2, rfl⟩⟩

omit [NumberField E] in
theorem piW_cA (z : AE F E) : piW τ (cA σ z) = piW (τ.comp σ) z :=
  (congrArg (splitProj τ) (comp_cA v z)).trans (splitProj_comp τ σ _).symm

include hσ in
theorem extS {ι κ : Type} {a b : Matrix ι κ (AE F E)} (h1 : a.map (piW τ) = b.map (piW τ))
    (h2 : a.map (piW (τ.comp σ)) = b.map (piW (τ.comp σ))) (h3 : a.map (aw E v) = b.map (aw E v)) : a = b :=
  extM v (Matrix.ext fun i j => split_ext hσ τ (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)) h3

variable {β : Type} [Fintype β] [DecidableEq β]

def up (m m' : Matrix β β (Fv F v)) : Matrix β β (AE F E) :=
  liftM E v β (Matrix.of fun i j => (splitAlgEquiv hσ τ).symm (m i j, m' i j))

theorem up_fst (m m' : Matrix β β (Fv F v)) : (up hσ τ m m').map (piW τ) = m := Matrix.ext fun i j =>
  (congrArg (splitProj τ) (congrFun (congrFun (comp_liftM v _) i) j)).trans (splitProj_symm hσ τ _)

theorem up_snd (m m' : Matrix β β (Fv F v)) : (up hσ τ m m').map (piW (τ.comp σ)) = m' := Matrix.ext fun i j =>
  (congrArg (splitProj (τ.comp σ)) (congrFun (congrFun (comp_liftM v _) i) j)).trans (splitProj_comp_symm hσ τ _)

theorem up_aw (m m' : Matrix β β (Fv F v)) : (up hσ τ m m').map (aw E v) = 1 := aw_liftM v _

theorem up_at (m m' : Matrix β β (Fv F v)) : At (evFin F v) (up hσ τ m m' - 1) := at_liftM v _

def upH : Matrix β β (Fv F v) × Matrix β β (Fv F v) →* Matrix β β (AE F E) where
  toFun m := up hσ τ m.1 m.2
  map_one' := extS hσ τ (by rw [up_fst, Matrix.map_one _ (map_zero _) (map_one _)]; rfl)
    (by rw [up_snd, Matrix.map_one _ (map_zero _) (map_one _)]; rfl) (by rw [up_aw, Matrix.map_one _ (map_zero _) (map_one _)])
  map_mul' a b := extS hσ τ (by simp only [Matrix.map_mul, up_fst]; rfl) (by simp only [Matrix.map_mul, up_snd]; rfl)
    (by simp only [Matrix.map_mul, up_aw, mul_one])

theorem continuous_upH : Continuous (upH (β := β) hσ τ) := by
  haveI : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : IsTopologicalAddGroup (Ev E v) := IsModuleTopology.topologicalAddGroup (Fv F v) _
  have c1 : Continuous (liftM E v β) :=
    continuous_const.add ((continuous_id.sub continuous_const).matrix_map Inert.continuous_tensAt)
  exact c1.comp (continuous_matrix fun i j => (continuous_splitAlgEquiv_symm hσ τ).comp (by fun_prop))

theorem continuous_piW : Continuous (piW τ) := (continuous_splitProj τ).comp
  (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
    ((RestrictedProduct.continuous_eval v).comp continuous_snd))

def upG : GL β (Fv F v) × GL β (Fv F v) →* GL β (AE F E) :=
  (Units.map (upH hσ τ)).comp (MulEquiv.prodUnits (M := Matrix β β (Fv F v)) (N := Matrix β β (Fv F v))).symm.toMonoidHom

theorem upG_val (x y : GL β (Fv F v)) : (upG hσ τ (x, y)).1 = up hσ τ x.1 y.1 := rfl

def dual (J : GL β (Fv F v)) : GL β (Fv F v) →* GL β (Fv F v) := (MulAut.conj J⁻¹).toMonoidHom.comp invT

theorem dual_val (J x : GL β (Fv F v)) : (dual J x).1 = (J⁻¹).1 * (x⁻¹).1ᵀ * J.1 := rfl

variable {J : Matrix β β (AE F E)} {Jp : GL β (Fv F v)} (h1 : J.map (piW τ) = Jp.1) (h2 : J.map (piW (τ.comp σ)) = Jp.1ᵀ)

omit [NumberField E] [DecidableEq β] in
theorem pi_gram (M : Matrix β β (AE F E)) :
    (Mᵀ * J * M.map (cA σ)).map (piW τ) = (M.map (piW τ))ᵀ * J.map (piW τ) * M.map (piW (τ.comp σ)) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  exact congrArg _ (Matrix.ext fun i j => piW_cA τ _)

def liftS : GL β (Fv F v) →* UG (cA σ) J :=
  ((upG hσ τ).comp ((MonoidHom.id _).prod (dual Jp))).codRestrict _ fun g => by
    change (up hσ τ g.1 (dual Jp g).1)ᵀ * J * (up hσ τ g.1 (dual Jp g).1).map (cA σ) = J
    have k : g.1ᵀ * Jp.1 * (dual Jp g).1 = Jp.1 := by
      rw [dual_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv_cancel_right, ← Matrix.transpose_mul, Units.inv_mul,
        Matrix.transpose_one, Matrix.one_mul]
    refine extS hσ τ ?_ ?_ ?_
    · rw [pi_gram, up_fst, up_snd, h1, k]
    · rw [pi_gram, comp_conj_conj hσ, up_fst, up_snd, h2]
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using congrArg Matrix.transpose k
    · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, awM_cA, up_aw, Matrix.transpose_one,
        Matrix.map_one _ (map_zero _) (map_one _), one_mul, mul_one]

theorem liftS_val (g : GL β (Fv F v)) : (liftS hσ τ h1 h2 g).1.1 = up hσ τ g.1 (dual Jp g).1 := rfl

include h1 in
theorem snd_eq (g : UG (cA σ) J) : g.1.1.map (piW (τ.comp σ)) = (dual Jp (Matrix.GeneralLinearGroup.map (piW τ) g.1)).1 := by
  have := (pi_gram τ g.1.1).symm.trans (congrArg (·.map (piW τ)) g.2)
  rw [h1] at this
  set x := Matrix.GeneralLinearGroup.map (piW τ) g.1
  rw [dual_val, ← this, show g.1.1.map (piW τ) = x.1 from rfl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (Jp⁻¹).1,
    ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one, Units.inv_mul, Matrix.one_mul]

theorem lift_down {g : UG (cA σ) J} (hg : At (evFin F v) (g.1.1 - 1)) :
    liftS hσ τ h1 h2 (Matrix.GeneralLinearGroup.map (piW τ) g.1) = g := by
  refine Subtype.ext (Units.ext (extS hσ τ (up_fst _ _ _ _) ((up_snd _ _ _ _).trans (snd_eq τ h1 g).symm) ?_))
  have := awM_of_at v hg
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), sub_eq_zero] at this
  exact (up_aw _ _ _ _).trans this.symm

theorem continuous_liftS : Continuous (liftS hσ τ h1 h2) := by
  have c0 : Continuous fun g : GL β (Fv F v) => (g.1, (dual Jp g).1) := by
    simp only [dual_val]
    exact Units.continuous_val.prodMk
      ((continuous_const.matrix_mul Units.continuous_coe_inv.matrix_transpose).matrix_mul continuous_const)
  have c : Continuous fun g : GL β (Fv F v) => (liftS hσ τ h1 h2 g).1.1 := by
    have := (continuous_upH hσ τ).comp c0
    exact this
  have c' : Continuous fun g : GL β (Fv F v) => ((liftS hσ τ h1 h2 g).1⁻¹).1 :=
    (c.comp continuous_inv).congr fun g => congrArg (·.1.1) (map_inv (liftS hσ τ h1 h2) g)
  exact continuous_induced_rng.2 (Units.continuous_iff.2 ⟨c, c'⟩)

include hσ in
theorem above_iff (u : HeightOneSpectrum (𝓞 E)) : u.under (𝓞 F) = v ↔ u = splitPrime τ ∨ u = splitPrime (τ.comp σ) := by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> exact splitPrime_under _⟩
  obtain ⟨t, rfl⟩ := SplitChart.exists_splitPrime_eq hσ (SplitChart.isSplit_of_algHom hσ τ) h
  exact (eq_or_eq_comp_conj hσ τ t).imp (congrArg _) (congrArg _)

include hσ in
theorem chi_at (χ : Chr F E) {x : (AE F E)ˣ} (hx : At (evFin F v) (x.1 - 1)) {a b : (Fv F v)ˣ} (ha : piW τ x.1 = a)
    (hb : piW (τ.comp σ) x.1 = b) : (χ x : ℂ) = chrW χ τ a * chrW χ (τ.comp σ) b := by
  have m : ∀ t : E →ₐ[F] Fv F v, splitPrime t ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset := fun t =>
    (Set.Finite.mem_toFinset _).2 (splitPrime_under t)
  rw [GlobalTheory.InertChars.eq_ideleAt_of_at x hx, ideleAt_eq_prod_locIdele, Finset.prod_eq_mul_of_mem ⟨_, m τ⟩ ⟨_, m (τ.comp σ)⟩
    (Finset.mem_attach _ _) (Finset.mem_attach _ _) (fun h => splitPrime_comp_ne hσ τ (congrArg Subtype.val h).symm)
    fun c _ hc => absurd ((above_iff hσ τ c.1).1 ((Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 c.2))
      (not_or.2 ⟨fun h => hc.1 (Subtype.ext h), fun h => hc.2 (Subtype.ext h)⟩), map_mul, Circle.coe_mul]
  congr 1
  · exact congrArg (fun y => (χ (locIdele F _ y) : ℂ)) (Units.ext ((ConjPlace.toCompl_eq hσ _ rfl _).trans (congrArg _ ha)))
  · exact congrArg (fun y => (χ (locIdele F _ y) : ℂ)) (Units.ext ((ConjPlace.toCompl_eq hσ _ rfl _).trans (congrArg _ hb)))

include hσ in
theorem abs_at {x : (AE F E)ˣ} (hx : At (evFin F v) (x.1 - 1)) : (absE F E x : ℝ) = ‖piW τ x.1‖ * ‖piW (τ.comp σ) x.1‖ := by
  have := congrArg (splitProj τ) (GlobalTheory.Doubling.algebraMap_norm_eq hσ (compFin F E v x.1))
  rw [AlgHom.commutes, map_mul, ← splitProj_comp] at this
  conv_lhs => rw [GlobalTheory.InertChars.eq_ideleAt_of_at x hx, GlobalTheory.Doubling.absE_ideleAt, GlobalTheory.Doubling.absEv_apply, coe_nnnorm]
  exact (congrArg norm this).trans (norm_mul _ _)

include hσ in
theorem chrW_mul {χ : Chr F E} (hr : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0) (a : (Fv F v)ˣ) :
    (chrW χ τ a : ℂ) * chrW χ (τ.comp σ) a = 1 := by
  let j : Fv F v →* AF F :=
    { toFun := fun t => 1 + atPlace v (t - 1)
      map_one' := by simp
      map_mul' := fun s t => extF v (by simp [evFin_atPlace, -map_sub]) (by simp [awF_at, -map_sub]) }
  have e : ∀ t : E →ₐ[F] Fv F v, piW t (algebraMap (AF F) (AE F E) (j a)) = a := fun t => by
    change splitProj t (evFin F v (1 + atPlace v (a.1 - 1)) ⊗ₜ[F] 1) = _
    simp [evFin_atPlace, -map_sub]
  rw [← chi_at hσ τ χ (x := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (Units.map j a)) ?_ (e _) (e _),
    hr.triv_of_even (by simp), Circle.coe_one]
  change At _ (algebraMap (AF F) (AE F E) (1 + atPlace v (a.1 - 1)) - 1)
  rw [map_add, map_one, add_sub_cancel_left]
  exact at_tensAt v ((a.1 - 1) ⊗ₜ[F] 1)

theorem selfDual {B : Base F E} {r s : ℕ} (hY : Y.IsHerm σ B r s) (hd : ((1 : E) • Y.Jᵀ).det ≠ 0) :
    IsSelfDualAt σ ((1 : E) • Y.Jᵀ) Y.L v :=
  PositivityTheory.ThKG.Loc.Iwa.selfDual_of hd hY.lat (fun y hy x hx => SelfDual.inclR_mem_intLoc v (by
    rw [PositivityTheory.ThKG.Loc.Iwa.hE_smul, one_mul]; exact ⟨⟨_, (hY.dual y).1 hy x hx⟩, rfl⟩)) (s := 1)
    ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top) fun y hy => by
      simp only [OneMemClass.coe_one, map_one, one_smul]
      refine (hY.dual y).2 fun x hx => ?_
      obtain ⟨o, ho⟩ := hy x hx
      rw [PositivityTheory.ThKG.Loc.Iwa.hE_smul, one_mul] at ho
      rw [← ho]; exact o.isIntegral_coe

omit [NumberField E] in
theorem piW_incM (J : Matrix (Fin n) (Fin n) E) : (incM F J).map (piW τ) = J.map τ := Matrix.ext fun i j => by
  change splitProj τ (evFin F v 1 ⊗ₜ[F] J i j) = τ (J i j)
  rw [splitProj_tmul, map_one, one_mul]

theorem frames {B : Base F E} {r s : ℕ} (hσ : IsCMExt F E σ) (hY : Y.IsHerm σ B r s) : ∃ J b b' : GL (Fin n) (Fv F v),
    (incM F Y.J).map (piW τ) = J.1 ∧ (incM F Y.J).map (piW (τ.comp σ)) = J.1ᵀ ∧ IsSplitBasis τ Y.L b ∧
      IsSplitBasis (τ.comp σ) Y.L b' ∧ b.1ᵀ * J.1 * b'.1 = 1 := by
  have hd : ((1 : E) • Y.Jᵀ).det ≠ 0 := by rw [one_smul, Matrix.det_transpose]; exact (Vac.herm_det hY).ne_zero
  have hJ : IsHermND σ ((1 : E) • Y.Jᵀ) := ⟨fun i j => by simp [hY.herm], hd⟩
  have := hY.lat
  obtain ⟨b, hb⟩ := exists_isSplitBasis τ Y.L hσ
  have h1 := IsSplitBasis.dual hσ hJ (selfDual hY hd) hb
  have h2 := splitGram_val hJ τ
  generalize splitGram hJ τ = G at h1 h2
  rw [one_smul] at h2
  have e : ((invT G)⁻¹).1 = G.1ᵀ := GlobalTheory.SplitFlip.invT_inv_val G
  refine ⟨(invT G)⁻¹, b, _, ?_, ?_, hb, h1, ?_⟩
  · rw [e, h2, piW_incM]; rfl
  · rw [e, h2, piW_incM]
    exact Matrix.ext fun i j => congrArg τ (hY.herm j i)
  · rw [e, dualConj_one_val, ← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Units.val_mul, Units.inv_mul, Matrix.transpose_one]

end GlobalTheory.ThK.Dbl.Split

end
