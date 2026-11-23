import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckeFixedLevelSpaces.FreeMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckeFixedLevelSpaces.AddOnePowEqRingHomImageAddPrimeMulZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ProdZpowConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem spec_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem spec_int {l : ℕ} [Fact l.Prime] (c : Coef l) (ι : Qbar l ≃+* ℂ) [Algebra c.O ℂ]
    (h : ∀ a : c.O, algebraMap c.O ℂ a = ι a) (μ : ℂ) : IsIntegral c.O μ ↔ ‖ι.symm μ‖ ≤ 1 := by
  let e : Qbar l →ₐ[c.O] ℂ := { ι.toRingHom with commutes' := fun a => (h a).symm }
  have h1 : IsIntegral c.O (e (ι.symm μ)) ↔ IsIntegral c.O (ι.symm μ) := isIntegral_algHom_iff e ι.injective
  have h2 : e (ι.symm μ) = μ := ι.apply_symm_apply μ
  rw [h2] at h1
  rw [h1, ← spec_intIff]
  exact ⟨fun h => isIntegral_trans _ h, fun h => h.tower_top⟩

private theorem spec_unit {l : ℕ} [Fact l.Prime] (c : Coef l) (ι : Qbar l ≃+* ℂ) [Algebra c.O ℂ]
    (h : ∀ a : c.O, algebraMap c.O ℂ a = ι a) (μ : ℂ) : IsIntUnit c.O μ ↔ ‖ι.symm μ‖ = 1 := by
  rw [IsIntUnit, spec_int c ι h, spec_int c ι h, map_inv₀, norm_inv]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have h3 : 0 < ‖ι.symm μ‖ := norm_pos_iff.2 ((map_ne_zero ι.symm).2 h0)
    exact le_antisymm h1 ((inv_le_one₀ h3).1 h2)
  · intro h1
    refine ⟨fun h0 => ?_, h1.le, by rw [h1, inv_one]⟩
    rw [h0, map_zero, norm_zero] at h1
    exact zero_ne_one h1

private theorem spec_chi {G : Type} [Group G] {I : Iwa G} {O Ω : Type} [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω]
    (hinj : Function.Injective (algebraMap O Ω)) (R : WtRep I O Ω) :
    ∃ ψ : I.T →* Oˣ, ∀ t : I.T, algebraMap O Ω (ψ t) = R.χ ⟨t, I.T_le t.2⟩ := by
  have h : ∀ t : I.T, ∃ a : O, algebraMap O Ω a = R.χ ⟨t, I.T_le t.2⟩ := fun t => by
    have h1 := R.integral_torusCharacter t t.2 0 0
    have h2 := R.torusAction ⟨t, I.T_le t.2⟩ 0
    rw [if_pos rfl] at h2
    rw [← h2]
    exact h1
  choose a ha using h
  let f : I.T →* O :=
    { toFun := a
      map_one' := hinj (by rw [ha, map_one]; exact congrArg Units.val (map_one R.χ))
      map_mul' := fun s t => hinj (by
        rw [map_mul, ha, ha, ha, ← Units.val_mul, ← map_mul]
        rfl) }
  exact ⟨f.toHomUnits, ha⟩

private theorem spec_cl {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
    (x : A →+* Qbar l) (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (e : ℕ) (φ : H.X.I.T →* ℂˣ)
    (hφ : ∀ v i y, (φ (eV n H.Sl v i y) : ℂ) = ι (H.finPart θ x lam v i y)) :
    H.ClAt θ ι x lam ξ K e = H.X.Cl (H.τC ι) ξ (H.lev K) e φ := by
  ext F
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, -⟩, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨⟨h1, h2⟩, h3, h4, ?_⟩
    let M : Submonoid H.X.I.T :=
      { carrier := {t | H.X.rpF ℂ d H.m t F = (((φ t)⁻¹ : ℂˣ) : ℂ) • F}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          have ha' : H.X.rpF ℂ d H.m a F = (((φ a)⁻¹ : ℂˣ) : ℂ) • F := ha
          have hb' : H.X.rpF ℂ d H.m b F = (((φ b)⁻¹ : ℂˣ) : ℂ) • F := hb
          change H.X.rpF ℂ d H.m ((a : GV n H.Sl) * b) F = (((φ (a * b))⁻¹ : ℂˣ) : ℂ) • F
          rw [map_mul, Module.End.mul_apply, hb', map_smul, ha', smul_smul, map_mul, mul_inv_rev, Units.val_mul] }
    refine Sp.torus_mem_submonoid_of_elementaryTorus H.Sl M fun v i y => ?_
    have h6 : F ∈ ⨅ (v) (i) (y), Module.End.eigenspace (H.X.rpF ℂ d H.m (eV n H.Sl v i y : H.X.I.T))
      (ι (H.finPart θ x lam v i y))⁻¹ := h5
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at h6
    change H.X.rpF ℂ d H.m _ F = _
    rw [Units.val_inv_eq_inv_val, hφ]
    exact h6 v i y
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    refine ⟨⟨⟨⟨⟨h1, fun u hu => h2 u (Subgroup.mem_sup_left hu)⟩, h2⟩, h3⟩, h4⟩, ?_⟩
    change F ∈ ⨅ (v) (i) (y), Module.End.eigenspace (H.X.rpF ℂ d H.m (eV n H.Sl v i y : H.X.I.T))
      (ι (H.finPart θ x lam v i y))⁻¹
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro v i y
    rw [← hφ, ← Units.val_inv_eq_inv_val]
    exact h5 _

attribute [local instance 2000] UpperTheory.V.W.coefLocal

theorem UpperTheory.V.Hi.spec :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n), H.Arith θ x.toRingHom lam → ∃ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam ⟨e0, he0⟩
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨⟨c1, -, hx1⟩, a, ha1, -, ha⟩ := (GradeZeroInterpolatingElement.coPt c A).1 x
  obtain ⟨c', hc', hR⟩ := wtRep L l n H.V H.Sl ι lam c1
  letI : Algebra c'.O ℂ := (ι.toRingHom.comp (algebraMap c'.O (Qbar l))).toAlgebra
  have hal : ∀ a : c'.O, algebraMap c'.O ℂ a = ι a := fun _ => rfl
  obtain ⟨R, hR, hχ⟩ : ∃ R : WtRep H.X.I c'.O ℂ, IsAlgWt (S := H.Sl) ι lam R.ξ ∧ _ := hR
  haveI : IsCNL c'.O := { complete := (abelian₂.dvr_finite l c'.O).1, finite := (abelian₂.dvr_finite l c'.O).2.1 }
  let y : A →+* c'.O := x.toRingHom.codRestrict c'.O fun b => hc' (hx1 b)
  letI : Algebra A c'.O := y.toAlgebra
  letI : Algebra A ℂ := (ι.toRingHom.comp x.toRingHom).toAlgebra
  haveI : IsScalarTower A c'.O ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap c'.O ℂ) := ι.injective.comp Subtype.val_injective
  haveI : IsLocalHom (algebraMap A c'.O) := ⟨fun b hu => by
    by_contra hb
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h1 : x b * (w : PadicAlgCl l) = 1 := congrArg Subtype.val hw
    have h2 : ‖x b‖ ≤ a := by simpa using ha 1 b (by rwa [pow_one])
    have h3 := congrArg norm h1
    rw [norm_mul, norm_one] at h3
    have h4 := mul_le_of_le_one_right (norm_nonneg (x b))
      ((spec_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) w).map c'.O.val) : ‖(w : PadicAlgCl l)‖ ≤ 1)
    linarith⟩
  obtain ⟨ψ, hψ⟩ := spec_chi hinj R
  let φ : H.X.I.T →* c'.Oˣ := (Units.map y.toMonoidHom).comp θ / ψ
  have hφχ : ∀ t : H.X.I.T, algebraMap A ℂ (θ t) = algebraMap c'.O ℂ (φ t) * R.χ ⟨t, H.X.I.T_le t.2⟩ := fun t => by
    rw [← hψ, ← map_mul, ← Units.val_mul]
    simp only [φ, MonoidHom.div_apply, div_mul_cancel]
    rfl
  have hφe : ∀ v i z, algebraMap c'.O ℂ (φ (eV n H.Sl v i z)) = ι (H.finPart θ x.toRingHom lam v i z) := fun v i z => by
    rw [HSet.finPart, map_div₀, ← Sp.chi_eV H.Sl ι lam R.χ hχ]
    exact (eq_div_iff (Units.ne_zero _)).2 (hφχ _).symm
  have htriv : ∀ v i (z : Uo ((H.Sl v).adicCompletion L)), (z : ((H.Sl v).adicCompletion L)ˣ) ∈ Uc _ (max e0 R.c0 + 1) →
      H.finPart θ x.toRingHom lam v i z = 1 := fun v i z hz =>
    he0 v i z (Sp.Uc_anti _ ((le_max_left _ _).trans (Nat.le_succ _)) hz)
  have hφ1 : ∀ t : H.X.I.T, (t : GV n H.Sl) ∈ H.X.I.Tc (max e0 R.c0) → φ t = 1 :=
    Sp.gen_Tc H.Sl (MonoidHom.mker φ) _ fun v i z hz => Units.ext (hinj ((hφe v i z).trans (by
      rw [htriv v i z hz]; simp)))
  have hτ : H.τC ι = (Matrix.GeneralLinearGroup.map (algebraMap A ℂ)).comp (H.τA A) := by
    ext u i j
    exact congrArg ι (x.commutes _).symm
  obtain ⟨h1, sp, h2, h3, h4, h5, h6, h7⟩ := Sp.absSpec H.X hinj R (H.τA A) θ hθ.cont φ (max e0 R.c0) (le_max_right _ _) hφ1 hφχ
    H.lev (Sp.lev_dir H) hH.fin hθ.free (H.τC ι) hτ _ rfl
  have hcl := fun K e => spec_cl H θ ι x.toRingHom lam R.ξ K e ((Units.map (algebraMap c'.O ℂ).toMonoidHom).comp φ) hφe
  have hlow : ∀ v j, (R.χ ⟨alV n H.Sl v j, H.X.I.P_le _ (Sp.alV_mem H.Sl v j)⟩ : ℂ) = H.lowVal ι lam v j :=
    Sp.chi_alV H.Sl ι lam R.χ hχ
  have hU : ∀ v (j : Fin n), H.opC ι lam (R.d + 1) (.inr (v, j)) = H.X.UF H.m R ⟨_, Sp.alV_mem H.Sl v (j + 1)⟩ := fun v j => by
    rw [Frame.UF, Units.val_inv_eq_inv_val, hlow]
    rfl
  have hz : H.uzC ι lam (R.d + 1) = H.X.UF H.m R ⟨_, H.X.I.z_mem⟩ := by
    have := congrArg Units.val (Sp.weightChar_central_eq_prod_uniformizerDiag H.Sl R.χ)
    rw [Units.coe_prod] at this
    simp only [Units.coe_prod] at this
    rw [Frame.UF, Units.val_inv_eq_inv_val, HSet.uzC]
    congr 2
    exact (this.trans (Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => hlow v j)).symm
  refine ⟨R.d + 1, R.ξ, max e0 R.c0, sp, hR, htriv, fun K e he => ?_, fun K e he i F hF => ?_,
    fun K e he i F hF h0 μ hμ => ?_, h2, h3, fun K e he => ?_, h5, fun K i f hf => ?_, fun K K' q g f hf _ => ?_⟩
  · rw [hcl]
    exact (h1 K e he).1
  · rw [hcl] at hF ⊢
    rcases i with ⟨w, j⟩ | ⟨v, j⟩
    · obtain ⟨κ, _, u, hu⟩ := Sp.lev_sph H w.1 (j + 1)
      obtain ⟨e1, e2⟩ := hu ℂ _ (H.X.raF (R.d + 1) (H.τC ι))
      have e3 : H.opC ι lam (R.d + 1) (.inl (w, j)) = _ := e1
      rw [e3]
      exact Sp.sum_cl H.X R _ _ e _ _ u F hF (e2 hH w.2 K F hF.1.2)
    · rw [hU]
      exact ((h1 K e he).2.1 _).1 F hF
  · rw [hcl] at hF
    rw [← spec_int c' ι hal]
    rcases i with ⟨w, j⟩ | ⟨v, j⟩
    · obtain ⟨κ, _, u, hu⟩ := Sp.lev_sph H w.1 (j + 1)
      have e3 : H.opC ι lam (R.d + 1) (.inl (w, j)) = _ := (hu ℂ _ (H.X.raF (R.d + 1) (H.τC ι))).1
      rw [e3] at hμ
      exact (h1 K e he).2.2 κ u F hF h0 μ hμ
    · rw [hU] at hμ
      exact ((h1 K e he).2.1 _).2 F hF h0 μ hμ
  · rw [h4 K e he, HSet.OrdAt, hcl, hz]
    refine le_antisymm (iSup_le fun μ => ?_) (iSup_le fun μ => ?_)
    · exact le_iSup_of_le ⟨μ.1, (spec_unit c' ι hal _).1 μ.2⟩ le_rfl
    · exact le_iSup_of_le ⟨μ.1, (spec_unit c' ι hal _).2 μ.2⟩ le_rfl
  · rcases i with ⟨w, j⟩ | ⟨v, j⟩
    · obtain ⟨κ, _, u, hu⟩ := Sp.lev_sph H w.1 (j + 1)
      obtain ⟨e1, e2⟩ := hu ℂ _ (H.X.raF (R.d + 1) (H.τC ι))
      have e3 : H.opC ι lam (R.d + 1) (.inl (w, j)) = _ := e1
      have e4 : H.op A (.inl (w, j)) = _ := (hu A _ (H.X.ra (H.τA A))).1
      rw [e3, e4]
      exact h7 K K κ u (e2 hH w.2 K) f hf
    · rw [hU]
      exact h6 K ⟨_, Sp.alV_mem H.Sl v (j + 1)⟩ f hf
  · obtain ⟨K'', hK⟩ := Sp.lev_act H hH K q g
    have := h7 K K'' Unit (fun _ => H.sec (H.wq q) g) (fun F hF => by
      rw [Fintype.sum_unique]
      exact hK ℂ _ _ F hF) f hf
    rw [Fintype.sum_unique, Fintype.sum_unique] at this
    exact this
