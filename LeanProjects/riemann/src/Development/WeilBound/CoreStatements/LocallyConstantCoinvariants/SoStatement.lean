import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.CompFinLiftE

noncomputable section

namespace PositivityTheory.KCo

open Filter Topology NumberField IsDedekindDomain Matrix GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.CompanionTheory.Ar.RT.Move GlobalTheory.LatVac

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField Classical.propDecidable

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ}

def coB (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (t : E →ₐ[F] Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    Matrix (Fin n) (Fin d) (Fv F v) :=
  -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)

theorem coB_eq (t : E →ₐ[F] Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    coB σ X W t u = (-X.J.map t) * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ := by simp [coB]

theorem unit_map (t : E →ₐ[F] Fv F v) {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (h : J.det ≠ 0) : IsUnit (J.map t).det := by
  have : (J.map t).det = t J.det := (RingHom.map_det (t : E →+* Fv F v) J).symm
  rw [this]
  exact ((map_ne_zero t).2 h).isUnit

theorem rank_coB (t : E →ₐ[F] Fv F v) (hX : X.J.det ≠ 0) (hW : W.J.det ≠ 0) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    (coB σ X W t u).rank = (u.map (piW (t.comp σ))).rank := by
  rw [coB_eq, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by rw [Matrix.det_transpose]; exact unit_map t hW),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by rw [Matrix.det_neg]; exact (isUnit_one.neg.pow _).mul (unit_map t hX))]

theorem exists_coB (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (hX : X.J.det ≠ 0) (hW : W.J.det ≠ 0)
    (Y : Matrix (Fin n) (Fin d) (Fv F v)) : ∃ x, At (evFin F v) x ∧ x.map (piW t) = 0 ∧ coB σ X W t x = Y := by
  let y := (-X.J.map t)⁻¹ * Y * ((W.J.map t)ᵀ)⁻¹
  choose z h1 h2 h3 using fun i j => exists_pair h t 0 (y i j)
  refine ⟨Matrix.of z, at_matrix.2 h1, Matrix.ext h2, ?_⟩
  have e : (Matrix.of z).map (piW (t.comp σ)) = y := Matrix.ext h3
  have u1 : IsUnit (-X.J.map t).det := by rw [Matrix.det_neg]; exact (isUnit_one.neg.pow _).mul (unit_map t hX)
  have u2 : IsUnit ((W.J.map t)ᵀ).det := by rw [Matrix.det_transpose]; exact unit_map t hW
  rw [coB_eq, e, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ u2, Matrix.mul_nonsing_inv_cancel_left _ _ u1]

theorem mult' (hψ : IsStd ψ) {t : E →ₐ[F] Fv F v} {ι} (hι : M.IsLinBar ψ t 1 1 ι) {u x : Matrix (Fin n) (Fin d) (AE F E)}
    (hu : At (evFin F v) u) (h1 : u.map (piW (t.comp σ)) = 0) (hx : At (evFin F v) x) (h0 : x.map (piW t) = 0) {φ}
    (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    ι (locRho M ψ v u φ) (coB σ X W t x) = ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) * ι φ (coB σ X W t x) :=
  hι.mult u hu h1 φ hφ _ (locRho_mem M hψ u hφ) (fun r hr => rho_tens M ψ hu φ hr.1) x hx h0

theorem eigen_kill (h : IsCMExt F E σ) (hψ : IsStd ψ) (hX : X.J.det ≠ 0) (hW : W.J.det ≠ 0) {t : E →ₐ[F] Fv F v} {ι}
    (hι : M.IsLinBar ψ t 1 1 ι) (l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ) {x₁ : Matrix (Fin n) (Fin d) (AE F E)}
    (hx : At (evFin F v) x₁) (h0 : x₁.map (piW t) = 0)
    (hl : ∀ u, At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → ∀ φ ∈ SB _,
      l (locRho M ψ v u φ) = ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x₁ u) * l φ)
    {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) (hz : ι φ (coB σ X W t x₁) = 0) : l φ = 0 := by
  choose xo a1 a2 a3 using exists_coB h t hX hW
  have hb := hι.bij
  have key := kill ((SB _ ⊓ LinearMap.ker l).map ι) (coB σ X W t x₁) (fun Y hY => ?_) _ (hb.1 hφ) hz
  · obtain ⟨φ', h', e⟩ := key
    rw [← hb.2.1 h'.1 hφ e]
    exact h'.2
  obtain ⟨u, hu, h1, hne⟩ := exists_sep M h hψ t (z := xo Y - x₁)
    (fun a ha => by rw [smul_sub, a1 Y a ha, hx a ha, sub_zero])
    (by rw [Matrix.map_sub _ (map_sub _), a2, h0, sub_zero]) fun e => hY (by rw [← sub_eq_zero.1 e, a3])
  let m : Matrix (Fin n) (Fin d) (Fv F v) → ℂ := fun y => ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) (xo y) u)
  have hm : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ι (locRho M ψ v u φ) = fun y => m y * ι φ y := fun φ hφ => funext fun y => by
    have := mult' M hψ hι hu h1 (a1 y) (a2 y) hφ
    rwa [a3] at this
  have hm1 : m (coB σ X W t x₁) = ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x₁ u) := by
    have e : xo (coB σ X W t x₁) = x₁ := by
      have e1 := a3 (coB σ X W t x₁)
      have u1 : IsUnit (-X.J.map t).det := by rw [Matrix.det_neg]; exact (isUnit_one.neg.pow _).mul (unit_map t hX)
      have u2 : IsUnit ((W.J.map t)ᵀ).det := by rw [Matrix.det_transpose]; exact unit_map t hW
      rw [coB_eq t (xo _), coB_eq t x₁] at e1
      have e2 := congrArg (fun A => (-X.J.map t)⁻¹ * (A * ((W.J.map t)ᵀ)⁻¹)) e1
      simp only [Matrix.mul_nonsing_inv_cancel_right _ _ u2, Matrix.nonsing_inv_mul_cancel_left _ _ u1] at e2
      refine Matrix.ext fun i j => sub_eq_zero.1 (eq_zero_of_at h t (fun a ha => ?_) ?_ ?_)
      · rw [smul_sub, at_matrix.1 (a1 _) i j a ha, at_matrix.1 hx i j a ha, sub_zero]
      · rw [map_sub, show piW t (x₁ i j) = 0 from congrFun (congrFun h0 i) j, sub_zero]
        exact congrFun (congrFun (a2 _) i) j
      · rw [map_sub, sub_eq_zero]
        rw [← coB_eq] at e2
        exact congrFun (congrFun e2 i) j
    simp only [m, e]
  haveI : T2Space (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (T2Space (Fin n → Fin d → Fv F v))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → Fv F v))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) (Fv F v)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → Fv F v))
  refine ⟨m, lc_of_mul m fun Φ hΦ => ?_, fun e => hne ?_, fun Φ hΦ => ?_⟩
  · obtain ⟨φ', h', rfl⟩ := hb.2.2 hΦ
    rw [← hm φ' h']
    exact hb.1 (locRho_mem M hψ u h')
  · rw [hm1] at e
    have h3 := GlobalTheory.LatVacArith.symp_add_left σ (-1) (incM F X.J) (incM F W.J) (xo Y - x₁) x₁ u
    rw [sub_add_cancel] at h3
    have h4 : m Y = _ := congrArg ψ h3
    rw [AddChar.map_add_eq_mul, e] at h4
    have h5 : ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x₁ u) ≠ 0 := fun e0 => by
      have := GlobalTheory.StdCharFromIsStd.norm_psi hψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x₁ u)
      rw [e0, norm_zero] at this
      exact zero_ne_one this
    exact (mul_eq_right₀ h5).1 h4.symm
  · obtain ⟨φ', h', rfl⟩ := hb.2.2 hΦ
    refine ⟨locRho M ψ v u φ' - m (coB σ X W t x₁) • φ', ⟨sub_mem (locRho_mem M hψ u h') (Submodule.smul_mem _ _ h'), ?_⟩, ?_⟩
    · change l _ = 0
      rw [map_sub, map_smul, hl u hu h1 φ' h', hm1, smul_eq_mul, sub_self]
    · rw [map_sub, map_smul, hm φ' h']
      funext y
      simp [sub_mul]

theorem mem_so (hM : M.IsGood ψ) (t : E →ₐ[F] Fv F v) {Ψ} (hΨ : Ψ ∈ schA F (Fin n × Fin d))
    (hs : ∀ z, (fun y => Ψ (repl v z y)) ∈ M.SoLoc ψ t) : Ψ ∈ M.So ψ t := by
  obtain ⟨Q, hQ⟩ := (Submodule.span ℂ (M.SoLoc ψ t)).exists_isCompl
  let A := (Submodule.span ℂ (M.SoLoc ψ t)).subtype ∘ₗ Submodule.linearProjOfIsCompl _ Q hQ
  have hA : ∀ φ, A φ ∈ Submodule.span ℂ (M.SoLoc ψ t) := fun φ => Subtype.prop _
  have e : opL v A Ψ = Ψ := funext fun x => by
    change A (fun y => Ψ (repl v x y)) (piK v (finPart x)) = _
    have : A (fun y => Ψ (repl v x y)) = fun y => Ψ (repl v x y) :=
      congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hQ ⟨_, Submodule.subset_span (hs x)⟩)
    rw [this]
    refine congrArg Ψ (funext fun i => Prod.ext rfl ?_)
    change (finPart x - epsK v (piK v (finPart x)) + epsK v (piK v (finPart x))) i = finPart x i
    rw [sub_add_cancel]
  rw [← e]
  refine schA_le ((M.So ψ t).comap (opL v A)) (fun f φ h1 h2 => ?_) hΨ
  have h2' : ∀ᶠ w in cofinite, φ w = M.vac w := (h2.and hM.std).mono fun _ h => h.1.trans h.2.symm
  have hU : ∀ ψ' ∈ SB (Fin n × Fin d → Fv F v), ∀ w, Function.update φ v ψ' w ∈ SB _ := fun ψ' h' w => by
    by_cases h : w = v
    · subst h
      simpa using h'
    · rw [Function.update_of_ne h]
      exact h1 w
  have hC : ∀ ψ', ∀ᶠ w in cofinite, Function.update φ v ψ' w = M.vac w := fun ψ' => by
    filter_upwards [h2', Filter.eventually_cofinite_ne v] with w h h'
    rw [Function.update_of_ne h', h]
  rw [Submodule.mem_comap, opL_pure hM.std h2']
  refine pure_update_mem hM.std h2' v f _ (S := M.SoLoc ψ t) (fun ψ' h' => Submodule.subset_span ?_) (hA _)
  exact ⟨f, _, hU _ h'.1, hC _, by simpa using h', rfl⟩

theorem so_stable (h : IsCMExt F E σ) (hψ : IsStd ψ) (hX : X.J.det ≠ 0) (hW : W.J.det ≠ 0) (hM : M.IsGood ψ) {om : Rep σ X W}
    (hS : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om) (t : E →ₐ[F] Fv F v) (γ) :
    ∀ Φ ∈ M.So ψ t, om γ Φ ∈ M.So ψ t := by
  refine fun Φ hΦ => (Submodule.span_le (p := (M.So ψ t).comap (om γ))).2 ?_ hΦ
  rintro _ ⟨f, φ, h1, h2, ⟨hv, ι, hι, h3⟩, rfl⟩
  obtain ⟨r, hr, er⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_at M ψ hM φ h2 f v
  have hsch : ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), tens (evFin F v) φ' r ∈ schA F (Fin n × Fin d) := fun φ' h' => by
    have e := er (Function.update φ v φ') fun w hw => Function.update_of_ne hw _ _
    rw [Function.update_self] at e
    obtain ⟨g, hg, e'⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M ψ hM (Function.update φ v φ') (fun w => by
      by_cases hw : w = v
      · subst hw
        simpa using h'
      · rw [Function.update_of_ne hw]
        exact h1 w) (by
      filter_upwards [h2, Filter.eventually_cofinite_ne v] with w h h'
      rw [Function.update_of_ne h', h])
    rw [← e, e' f]
    exact Submodule.subset_span ⟨f, g, hg, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, er φ fun _ _ => rfl]
  have hp : ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), om γ (tens (evFin F v) φ' r) ∈ schA F (Fin n × Fin d) :=
    fun φ' h' => hS.pres γ _ (hsch φ' h')
  refine mem_so M hM t (hp _ hv) fun z => ⟨slice_mem' (hp _ hv) z, ι, hι, fun Y hY => ?_⟩
  obtain ⟨x, hx, h0, rfl⟩ := exists_coB (X := X) (W := W) h t hX hW Y
  let l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun φ' => ι (fun y => om γ (tens (evFin F v) φ' r) (repl v z y)) (coB σ X W t x)
      map_add' := fun a b => by
        have e : tens (evFin F v) (a + b) r = tens (evFin F v) a r + tens (evFin F v) b r := funext fun _ => add_mul _ _ _
        rw [e, map_add]
        exact congrFun (map_add ι _ _) _
      map_smul' := fun c a => by
        have e : tens (evFin F v) (c • a) r = c • tens (evFin F v) a r := funext fun _ => mul_assoc _ _ _
        rw [e, map_smul]
        exact congrFun (map_smul ι c _) _ }
  have hz : ∀ (π : AE F E →+* Fv F v) (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)),
      (actAB (cA σ) p u).map π = (mat p.1).map π * u.map π * ((mat p.2).map π)ᵀ := fun π p u => by
    rw [actAB, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    rfl
  have hback : actAB (cA σ) γ (actAB (cA σ) γ⁻¹ x) = x := by
    simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]
  have hun : ∀ {m : ℕ} (g : GL (Fin m) (AE F E)), IsUnit ((g : Matrix (Fin m) (Fin m) (AE F E)).map (piW (t.comp σ))).det := fun g =>
    (Matrix.isUnit_iff_isUnit_det _).1 (g.isUnit.map (piW (t.comp σ)).mapMatrix)
  refine eigen_kill M h hψ hX hW hι l (x₁ := actAB (cA σ) γ⁻¹ x) (at_mul_mul hx _ _) (by rw [hz, h0]; simp)
    (fun u hu hu1 φ' h' => ?_) hv (h3 _ ?_)
  · have hu' : At (evFin F v) (actAB (cA σ) γ u) := at_mul_mul hu _ _
    change ι (fun y => om γ (tens (evFin F v) (locRho M ψ v u φ') r) (repl v z y)) _ = _ * ι _ _
    rw [← rho_tens M ψ hu φ' hr, hS.impl γ u _ (hsch φ' h'), slice_rho M ψ hu',
      mult' M hψ hι hu' (by rw [hz, hu1]; simp) hx h0 (slice_mem' (hp φ' h') z), ← symp_act (cA σ) _ _ _ γ _ u, hback]
  · rw [rank_coB t hX hW] at hY ⊢
    rwa [hz, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by rw [Matrix.det_transpose]; exact hun _),
      Matrix.rank_mul_eq_right_of_isUnit_det ((mat γ⁻¹.1).map (piW (t.comp σ))) _ (hun γ⁻¹.1.1)]

theorem so_statement : SoSt := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT γ
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hd : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E), (J.map (B.emb w).1).det ≠ 0 → J.det ≠ 0 := fun J hJ h0 =>
    hJ (((RingHom.map_det _ J).symm.trans (congrArg _ h0)).trans (map_zero _))
  refine so_stable G.M' hT.base.cm hT.base.std
    (hd _ (GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hV'.sig w))) (hd _ fun h0 => ?_) hT.geo.hM'
    (IsUWeilPair.isUSplitting hT.weil').toIsSplitting B.τ₁ γ
  exact GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hW.sig w) (by rw [Matrix.det_smul, h0, mul_zero])

end PositivityTheory.KCo
