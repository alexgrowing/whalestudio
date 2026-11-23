import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LinkedUnlOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PhiMaps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsIrrTwistAndRepIsoOfTwistRepIso

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr

private theorem xa_norm {l : ℕ} [Fact l.Prime] (c : Coef l) (y : c.O) : ‖(y.1 : PadicAlgCl l)‖ ≤ 1 := by
  have hz : IsIntegral ℤ_[l] y.1 := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y).map c.O.val
  have hq : IsIntegral ℚ_[l] y.1 := Algebra.IsIntegral.isIntegral _
  have h0 : ‖(y.1 : PadicAlgCl l)‖ = spectralValue (minpoly ℚ_[l] y.1) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hq), ]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hz, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem xa_pow {l : ℕ} [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] :
    ∃ e : ℕ, maximalIdeal c.O ^ e ≤ Ideal.span {(l : c.O)} := by
  have hl0 : (l : c.O) ≠ 0 := fun h => by
    have h1 : ((l : c.O) : PadicAlgCl l) = 0 := congrArg Subtype.val h
    have h2 : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h1
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  refine ⟨e, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, hu, Ideal.span_singleton_le_span_singleton]
  exact (Units.isUnit u).mul_left_dvd.2 dvd_rfl

private theorem xa_lnorm {l : ℕ} [Fact l.Prime] : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends (p := l) ((l : ℕ) : ℚ_[l])
  have h2 : (((l : ℕ) : ℚ_[l]) : PadicAlgCl l) = ((l : ℕ) : PadicAlgCl l) := by simp
  rw [h2] at h
  rw [h]
  exact Padic.norm_p_lt_one

private theorem xa_key {l : ℕ} [Fact l.Prime] (c : Coef l) {e : ℕ} (he : maximalIdeal c.O ^ e ≤ Ideal.span {(l : c.O)})
    (N : ℕ) (x : c.O) (hx : x ∈ maximalIdeal c.O ^ (e * N)) :
    ‖(x.1 : PadicAlgCl l)‖ ≤ ‖((l : ℕ) : PadicAlgCl l)‖ ^ N := by
  have h1 : x ∈ Ideal.span {(l : c.O) ^ N} := by
    rw [← Ideal.span_singleton_pow]
    rw [pow_mul] at hx
    exact Ideal.pow_right_mono he N hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 h1
  have h2 : (((l : c.O) ^ N * y : c.O).1 : PadicAlgCl l) = ((l : ℕ) : PadicAlgCl l) ^ N * y.1 := by
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, show (((l : c.O)).1 : PadicAlgCl l) = ((l : ℕ) : PadicAlgCl l) from map_natCast c.O.val l]
  rw [h2, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (xa_norm c y)

private theorem xa_top {l : ℕ} [Fact l.Prime] {Γ : Type} [TopologicalSpace Γ] (u : Γ → PadicAlgCl l)
    (H : ∀ (g₀ : Γ) (ε : ℝ), 0 < ε → ∀ᶠ g in nhds g₀, ‖u g - u g₀‖ < ε) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  simpa only [dist_eq_norm] using H g₀ ε hε

private theorem xa_cont {l : ℕ} [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] {Γ : Type} [TopologicalSpace Γ]
    (f : Γ → c.O) (h : Alg.AdicCont (maximalIdeal c.O) f) : Continuous fun g => ((f g).1 : PadicAlgCl l) := by
  obtain ⟨e, he⟩ := xa_pow c
  refine xa_top _ fun g₀ ε hε => ?_
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (xa_lnorm (l := l))
  have h0 := (h (e * N)).eventually_eq g₀
  refine h0.mono fun g hg => ?_
  have h1 : f g - f g₀ ∈ maximalIdeal c.O ^ (e * N) := Ideal.Quotient.eq.1 hg
  have h2 : ((f g).1 : PadicAlgCl l) - (f g₀).1 = ((f g - f g₀ : c.O).1 : PadicAlgCl l) :=
    (map_sub c.O.val (f g) (f g₀)).symm
  rw [h2]
  exact lt_of_le_of_lt (xa_key c he N _ h1) hN

private theorem xa_gl {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (hχ : Continuous χ)
    (hr : ∀ i j, Continuous fun s => (r s : Matrix (Fin n) (Fin n) k) i j) : Continuous (tw r χ) := by
  have h0 : Continuous fun s => (tw r χ s : Matrix (Fin n) (Fin n) k) := by
    refine continuous_matrix fun i j => ?_
    simp only [tw_val, Matrix.smul_apply, smul_eq_mul]
    exact (Units.continuous_val.comp hχ).mul (hr i j)
  refine Units.continuous_iff.2 ⟨h0, ?_⟩
  have h1 : (fun s => (((tw r χ s)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      fun s => (tw r χ s⁻¹ : Matrix (Fin n) (Fin n) k) := by
    funext s
    rw [map_inv]
  rw [h1]
  exact h0.comp continuous_inv

private theorem xa_adic {O R Γ : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing R] [Algebra O R] [Alg.IsCO O R] [TopologicalSpace Γ] (ξ : R →ₐ[O] O) {u : Γ → R}
    (h : Alg.AdicCont (maximalIdeal R) u) : Alg.AdicCont (maximalIdeal O) fun g => ξ (u g) := fun N => by
  have hm : ∀ x ∈ maximalIdeal R, ξ x ∈ maximalIdeal O := fun x hx => by
    have h1 := Alg.res_map ξ x
    rw [(Alg.res_eq_zero_iff O R x).2 hx] at h1
    exact (Alg.res_eq_zero_iff O O _).1 h1
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal O ^ N).comap (ξ : R →+* O) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hm) N
  exact (h N).comp (Ideal.quotientMap _ (ξ : R →+* O) hle)

private theorem ap_det {n : ℕ} {A B G H : Type} [CommRing A] [CommRing B] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (f : A →+* B) (p : H →* G) (τ : H →* Matrix (Fin n) (Fin n) B)
    (h : ∀ g, τ g = (ρ (p g)).map f) : ((W.GDet.ofRep ρ).map f).comap p = W.GDet.ofRep τ := by
  refine W.GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (W.GDet.repAlg ρ C (MonoidAlgebra.mapDomainRingHom C p x)).det = (W.GDet.repAlg τ C x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r =>
    ext i j
    simp [W.GDet.repAlg, h]
    rfl

private theorem ap_locAlg (hG : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ)
    (hka : Sd.IsAlgChar ι ka) {A : ValuationSubring Ω} {w : W.Plc L} (h : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    ∃ wt : W.Emb l w → ℤ, ∀ (m : ℤ) (χ : G L Ω →* (Qbar l)ˣ), IsOpen (χ.ker : Set (G L Ω)) →
      ∀ κ : Dec (F := L) A →* (Qbar l)ˣ,
        (∀ g : Dec (F := L) A, (g : G L Ω) ∈ Ine (F := L) A → κ g = cycBar L Ω l g ^ m * χ g * ka g) →
        W.IsLocAlg h κ fun τ => wt τ - m := by
  obtain ⟨-, art, Y, a, hart, -, hY⟩ := hka
  refine ⟨fun τ => -a ((ι.toRingHom.comp τ.1).comp (algebraMap L (w.adicCompletion L))), fun m χ hχ κ hκ => ?_⟩
  by_cases hl : ∃ b, GlobalTheory.LocLanglands.IsLocalArtin h b
  swap
  · exact ⟨1, by simp, fun b hb => absurd ⟨b, hb⟩ hl⟩
  obtain ⟨ph, h1⟩ := Loc.laHecke h art hart ι Y a ka hY hl
  have h2 := (Loc.laMul h).2.1 _ _ _ m (Loc.laCyc hG h hw)
  have h3 := (Loc.laMul h).2.2 (χ.comp (Dec (F := L) A).subtype) (χ.comp (Ine (F := L) A).subtype)⁻¹
    (Subgroup.isOpen_mono (H₁ := χ.ker.comap (Ine (F := L) A).subtype) (fun x hx => inv_eq_one.2 hx)
      (hχ.preimage continuous_subtype_val)) fun s => mul_inv_cancel _
  have h4 := ((Loc.laMul h).1 _ _ _ _ _ _ ((Loc.laMul h).1 _ _ _ _ _ _ h2 h3).1 h1).1
  refine ⟨_, h4.1, fun b hb s => ?_⟩
  have h5 := h4.2 b hb s
  rw [hκ _ s.2]
  refine Eq.trans ?_ (h5.trans ?_)
  · rfl
  · refine finprod_congr fun τ => ?_
    congr 1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring

private theorem ap_psi {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)
    {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (L : Type) [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure L Ω] (m : ℤ) :
    ∃ χ : G L Ω →* (Qbar l)ˣ, IsOpen (χ.ker : Set (G L Ω)) ∧ ∀ g : G L Ω,
      (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ L Ω g) ^ m).val.1 = (cycBar L Ω l g ^ ((e : ℤ) * m) * χ g).val := by
  let u : c.Oˣ →* (Qbar l)ˣ := Units.map c.O.val.toRingHom.toMonoidHom
  refine ⟨((u.comp (Chr.dirG ℚ Ω ψ)).comp (galEmb ℚ L Ω)) ^ m, ?_, fun g => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker.comap (galEmb ℚ L Ω)) (fun g hg => ?_)
      ((Chr.clsFacts ℚ Ω N).1.preimage (galEmbTop ℚ L Ω).1.continuous)
    have h1 : Chr.cls ℚ Ω N (galEmb ℚ L Ω g) = 1 := hg
    rw [MonoidHom.mem_ker, MonoidHom.zpow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, Chr.dirG, MonoidHom.comp_apply,
      h1, map_one, map_one, one_zpow]
  · have h1 : u (chiO ℚ Ω l c.O (galEmb ℚ L Ω g)) = cycBar L Ω l g := Units.ext rfl
    change (u _).val = _
    rw [map_zpow, Chr.Psi, MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply, map_zpow, h1, mul_zpow, ← zpow_mul]
    rfl

theorem UpperTheory.V.J.xiArith :
    GlobalTheory.Published.GlobalArtinReciprocity → UpperTheory.V.J.XiArith := by
  intro hG Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f R hka φ hφ ξ r hr hirr hψ
  obtain ⟨hD1, hP1⟩ := hφ
  have hD0 : R.B₀.u.D.map ((R.S.B.val.comp φ : R.B₀.B →ₐ[c₁.O] R.S.R) : R.B₀.B →+* R.S.R) =
      W.GDet.ofRep (R.K.tw R.S.ρ) := hD1
  have hP0 : ∀ v i, W.pushCh ((R.S.B.val.comp φ : R.B₀.B →ₐ[c₁.O] R.S.R) : R.B₀.B →+* R.S.R) (R.B₀.u.ψ v i) =
      R.K.twψ R.S.ρ v i := hP1
  let F : R.B₀.B →ₐ[c₁.O] c₁.O := ξ.comp (R.S.B.val.comp φ)
  let j : c₁.O →ₐ[c₁.O] Qbar l := Algebra.ofId c₁.O (Qbar l)
  let ρ₂ : Fr.NRep (Φ.ext f) 3 c₁.O := R.S.ρ.map (ξ : R.S.R →+* c₁.O)
  have hD : R.B₀.u.D.map (F : R.B₀.B →+* c₁.O) = W.GDet.ofRep (R.K.tw ρ₂) := by
    rw [← R.K.ofRep_tw_map, ← hD0, (CA.d_gmap _).2.1]
    rfl
  have hP : ∀ v i, W.pushCh (F : R.B₀.B →+* c₁.O) (R.B₀.u.ψ v i) = R.K.twψ ρ₂ v i := fun v i => by
    rw [← R.K.twψ_map, ← hP0 v i]
    rfl
  have hw : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (R.s.w v).asIdeal := fun v => by
    have h1 := (R.s.hA v (l : ℕ)).2 v.2
    refine (R.s.hw v (l : ℕ)).1 ?_
    simpa using h1
  choose wt hwt using fun v : W.Vl l L => ap_locAlg hG ι _ hka.alg (R.s.hw v) (hw v)
  refine ⟨⟨fun v i τ => wt v τ - (e : ℤ) * Fr.w 3 i, ⟨fun v τ a b hab => ?_, fun v i => ?_⟩⟩,
    tw r (cycBar L Ω l)⁻¹, ?_, ?_, (UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).1 r hirr⟩
  · have h1 : Fr.w 3 b < Fr.w 3 a := by
      have h2 : (a : ℕ) < b := hab
      unfold Fr.w
      split_ifs <;> omega
    have h3 : (0 : ℤ) < e := by exact_mod_cast H.e_pos
    exact sub_lt_sub_left (mul_lt_mul_of_pos_left h1 h3) _
  · obtain ⟨χ, hχ, h1⟩ := ap_psi c e ψ L (Ω := Ω) (Fr.w 3 i)
    refine hwt v _ χ hχ _ fun g hg => Units.ext ?_
    have h2 : F (R.B₀.u.ψ v i g).val = (R.K.twψ ρ₂ v i g).val := congrArg (fun t => (t g).val) (hP v i)
    have h3 := hψ (R.K.e v) i (R.K.lam v g) ((R.K.lam_I v g).2 hg)
    rw [R.lam_j] at h3
    rw [Units.val_mul, ← h1, ← R.κ_pr]
    change j (F (R.B₀.u.ψ v i g).val) = _
    rw [h2]
    exact congrArg (fun t : Qbar l => t * (R.K.κ (R.V.pr g)).val.1) h3
  · refine xa_gl r _ hka.alg.1 fun a b => ?_
    have hp0 : Continuous k.p0 :=
      ((k.p_cont.comp ((galEmbTop ℚ L Ω).1.continuous.subtype_mk _)).subtype_mk _)
    have e1 : (fun s => (r s : Matrix (Fin 3) (Fin 3) (Qbar l)) a b) = fun s => (ξ (R.S.ρ.r (k.p0 s) a b)).1 :=
      funext fun s => by rw [hr s]; rfl
    rw [e1]
    exact xa_cont c₁ (fun s => ξ (R.S.ρ.r (k.p0 s) a b)) fun N =>
      (xa_adic ξ (R.S.lift.1.1 a b) N).comp_continuous hp0
  · have h1 : W.UniversalOrdinaryDeterminantRing.Pt.D (j.comp F) = (W.GDet.ofRep (R.K.tw ρ₂)).map (j : c₁.O →+* Qbar l) :=
      congrArg (fun D => D.map (j : c₁.O →+* Qbar l)) hD
    refine (congrArg (fun D => D.comap R.V.pr) h1).trans (ap_det _ _ _ _ fun g => ?_)
    change (tw r (cycBar L Ω l)⁻¹ g).val = _
    rw [tw_val, hr, ← R.κ_pr, ← R.π_pr]
    rfl
