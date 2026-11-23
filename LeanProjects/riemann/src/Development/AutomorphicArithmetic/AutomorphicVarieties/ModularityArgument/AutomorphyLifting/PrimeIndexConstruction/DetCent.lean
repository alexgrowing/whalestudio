import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTrans
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FiniteInfinitePlaceProduct
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SameSatTwist
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open GlobalTheory.HeckeGal GlobalTheory.LFun GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary Formalism.UG UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd Polynomial Matrix

namespace UpperTheory.V.Z.Win.Birth

private theorem scalar_eq_prod {E V : Type} [Field E] [NumberField E] {a : ℕ} [AddCommGroup V] [Module ℂ V]
    {w : HeightOneSpectrum (𝓞 E)} {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {B : Multiset ℂˣ}
    (hB : HasSatGL w ρ B) {c : ℂˣ}
    (hc : ∀ x, ρ (GeneralLinearGroup.scalar (Fin a) (atFin w (unif w))) x = (c : ℂ) • x) : c = B.prod := by
  classical
  obtain ⟨x, hx⟩ := hB.exists_vec
  set u : (w.adicCompletion E)ˣ := atFin w (unif w) with hu_def
  have hu : IsUnifV E w (u : w.adicCompletion E) := unif_spec w
  have h0 : (u : w.adicCompletion E) ≠ 0 := u.ne_zero
  have hTn : Tj ℂ a (Ov E w) (u : w.adicCompletion E) a =
      dosetInd ℂ (KGL w a) (GlobalTheory.WeylGL.tor h0 fun _ => 1) := by
    rw [GlobalTheory.WeylGL.Tj_eq h0]; simp
  have h1 := hx.2.2.2 _ hu a le_rfl
  rw [hTn, heckeVec_dosetInd (R := {GlobalTheory.WeylGL.tor h0 fun _ => 1}) hx.2.1, Finset.sum_singleton] at h1
  rotate_left
  · intro γ hγ
    exact GlobalTheory.WeylGL.mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
  · intro g hg
    obtain ⟨c, hc, d, hd, rfl⟩ := GlobalTheory.WeylGL.mem_doset.1 hg
    refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← GlobalTheory.WeylGL.tor_const_comm, mul_assoc, inv_mul_cancel_left]
    exact mul_mem hc hd
  have ht : GlobalTheory.WeylGL.tor h0 (fun _ : Fin a => (1 : ℤ)) = GeneralLinearGroup.scalar (Fin a) u := by
    ext i j
    simp [GlobalTheory.WeylGL.tor_val, Matrix.diagonal_apply]
  rw [ht, hc] at h1
  have h3 : satEig (qV E w) a B a = ((B.prod : ℂˣ) : ℂ) := by
    have hcd : (B.map fun b : ℂˣ => (b : ℂ)).card = a := by rw [Multiset.card_map]; exact hx.2.2.1
    rw [satEig, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul]
    conv_lhs => rw [← hcd]
    rw [Multiset.esymm, Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]
    exact (map_multiset_prod (Units.coeHom ℂ) B).symm
  rw [h3] at h1
  exact Units.ext (smul_left_injective ℂ hx.1 h1)

private theorem fin_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : HeightOneSpectrum (𝓞 F))
    (u : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) u)) =
      GeneralLinearGroup.scalar (Fin 2) (localIdele F w u) := by
  have hz : locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin 2) (Units.map (corner (sLoc F w)) u) := cornerGL_scalar _ u
  have hf : ∀ y, finGL F 2 (GeneralLinearGroup.scalar (Fin 2) y) = GeneralLinearGroup.scalar (Fin 2) (finId F y) :=
    fun y => cornerGL_scalar _ y
  have e1 := finId_det_locGL (E := F) (a := 1) w (GeneralLinearGroup.scalar (Fin 1) u)
  have e2 : GeneralLinearGroup.det (locGL F 1 w (GeneralLinearGroup.scalar (Fin 1) u)) =
      Units.map (corner (sLoc F w)) u := by
    rw [locGL, cornerGL_scalar]; ext; simp
  have e3 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) u) = u := by ext; simp
  rw [e2, e3] at e1
  rw [hz, hf, e1]

private theorem locRep_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (ω : HChar F)
    (hω : ∀ (z : Ideles F), ∀ φ ∈ π.V, ∀ g, φ.1 (GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g)
    (w : HeightOneSpectrum (𝓞 F)) (u : (w.adicCompletion F)ˣ) (x : π.V) :
    π.locRep w (GeneralLinearGroup.scalar (Fin 2) u) x = ((ω.loc w u : ℂˣ) : ℂ) • x := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  have e : (π.locRep w (GeneralLinearGroup.scalar (Fin 2) u) x).1.1 g =
      x.1.1 (g * finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) u))) := rfl
  rw [e, fin_scalar, show g * GeneralLinearGroup.scalar (Fin 2) (localIdele F w u) =
    GeneralLinearGroup.scalar (Fin 2) (localIdele F w u) * g from ?_, hω _ _ x.2]
  · rfl
  · ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]

private theorem absVal {F : Type} [Field F] [NumberField F] (t : ℤ) (v : HeightOneSpectrum (𝓞 F)) :
    (((GlobalTheory.HeckeGal.Model.absPow F (t : ℝ)).val v : ℂˣ) : ℂ) = (normV v : ℂ) ^ (-t) := by
  rw [(GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (t : ℝ)).2.1 v]
  have e : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (normV v : ℂ) := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [e, ← Complex.cpow_intCast]
  push_cast
  rfl

private theorem fin_order {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (ξ : G F Ω →* (Qbar l)ˣ) (h : IsOpen (ξ.ker : Set (G F Ω))) :
    Continuous ξ ∧ ∃ m : ℕ, 0 < m ∧ ξ ^ m = 1 := by
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  refine ⟨continuous_of_isOpen_ker' ξ h, ξ.ker.index, ?_, ?_⟩
  · haveI : Finite (G F Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ h
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  · ext σ
    have := Subgroup.pow_index_mem ξ.ker σ
    simpa [MonoidHom.mem_ker] using congrArg Units.val (MonoidHom.mem_ker.1 this)

private theorem det_sat {M : Matrix (Fin 2) (Fin 2) ℂ} {q : ℕ} {B : Multiset ℂˣ} (hc : B.card = 2)
    (h : M.charpoly = ((algSat 2 q B).map fun b => X - C b).prod) : M.det = (q : ℂ) * ((B.prod : ℂˣ) : ℂ) := by
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hc
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  have e : algSat 2 q {x, y} = {(((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * x,
      (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * y} := by
    simp [algSat]
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C, e, Multiset.prod_pair, Multiset.prod_pair,
    mul_mul_mul_comm, hq', Units.val_mul]

theorem detCent : DetCent := by
  intro F Ω _ _ _ _ _ _ l _ ι ξ s π r hatt hdet hker ω hω w
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds F Ω
  obtain ⟨hξc, m, hm, hξm⟩ := fin_order ξ hker
  obtain ⟨χ, ⟨hχm, hχ⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι ξ hξc hm hξm
  set P : HChar F := GlobalTheory.HeckeGal.Model.absPow F ((s + 1 : ℤ) : ℝ) with hP
  have hfl : {v : HeightOneSpectrum (𝓞 F) | ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h0 : ((l : ℕ) : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 F)})
      (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have hl' : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
    Filter.eventually_cofinite.2 (by simpa using hfl)
  have hqne : ∀ v : HeightOneSpectrum (𝓞 F), (normV v : ℂ) ≠ 0 := fun v => by
    have h1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
    have h2 : 0 < normV v := zero_lt_one.trans h1
    exact_mod_cast h2.ne'
  have hν : ω * χ⁻¹ * P⁻¹ = 1 := by
    refine PositivityTheory.jumpWindows.FiniteInfinitePlaceProduct.eq_one _ ?_
    filter_upwards [hatt.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.unr_ae_and_level F χ).1,
      hl'] with v ⟨B, hB, hF⟩ hu hl
    have hB' : HasSatGL v (π.locRep v) B := hB
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    have e1 : ω.val v = B.prod := scalar_eq_prod hB' (fun x => locRep_scalar π ω hω v _ x)
    have hcard : B.card = 2 := by
      obtain ⟨x, hx⟩ := hB'.exists_vec
      exact hx.2.2.1
    have e2 := (hF A hA).2 σ hσ
    rw [← Matrix.charpoly_map] at e2
    have e3 := det_sat hcard e2
    have e4 : ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det =
        ((r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom).det := ι.toRingHom.map_det _
    have e5 := congrArg (fun u : (Qbar l)ˣ => ι (u : Qbar l)) (DFunLike.congr_fun hdet σ⁻¹)
    have e6 := hχ.frob_unr ha (Or.inr rfl) hu hA hσ
    have e7 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) := by
      rw [cycBar, MonoidHom.comp_apply, Units.coe_map, cycZ_of_isFrob hl hA hσ]
      simp
    have h8 : ι ((ξ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (χ.val v : ℂˣ) := by
      rw [map_inv, Units.val_inv_eq_inv_val, e6, inv_inv, ι.apply_symm_apply]
    have h9 : ι (((cycBar F Ω l ^ s) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV v : ℂ) ^ (-s) := by
      rw [MonoidHom.zpow_apply, map_inv, _root_.inv_zpow', Units.val_zpow_eq_zpow_val, e7, map_zpow₀, map_natCast]
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, map_mul, Matrix.GeneralLinearGroup.val_det_apply,
      h8, h9] at e5
    rw [e4, e3] at e5
    refine Units.ext ?_
    have h10 := absVal (F := F) (s + 1) v
    rw [HChar.val_mul, HChar.val_mul, HChar.val_inv, HChar.val_inv, Units.val_mul, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hP, h10, e1, Units.val_one]
    have hq := hqne v
    have hc : ((χ.val v : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    rw [neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
    have hs : (normV v : ℂ) ^ (-s) ≠ 0 := zpow_ne_zero _ hq
    field_simp
    linear_combination e5
  have hωe : ω = χ * P := by
    rw [mul_assoc, ← mul_inv, mul_inv_eq_one] at hν
    exact hν
  refine ⟨⟨m, hm, ?_⟩, fun A hA hU => ?_⟩
  · have h1 : ω.loc w (atFin w (unif w)) = ω.val w := rfl
    have h2 : ((χ.val w : ℂˣ) : ℂ) ^ m = 1 := by
      have h3 : (χ ^ m).val w = χ.val w ^ m := MonoidHom.pow_apply χ.1 m _
      rw [show χ ^ m = 1 from hχm] at h3
      rw [← Units.val_pow_eq_pow_val, ← h3]
      rfl
    rw [h1, hωe, HChar.val_mul, Units.val_mul, hP, absVal, mul_assoc, ← zpow_add₀ (hqne w), neg_add_cancel, zpow_zero,
      mul_one, h2]
  · have hu : χ.UnrAt w := fun x hx => by
      have h1 := hU x hx
      rw [hωe, HChar.loc_mul, (GlobalTheory.HeckeGal.Model.absPow_isAbsPow F _).1 w x hx, mul_one] at h1
      exact h1
    exact fun σ hσ => (hχ.unr_iff ha (Or.inr rfl) hA).2 hu σ hσ

end UpperTheory.V.Z.Win.Birth
