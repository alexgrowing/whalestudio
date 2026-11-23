import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsObjOfUniformisedTripleComplex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.BdDim.CxField

theorem trLe_of_rat {K : Type} [Field K] [CharZero K] {n : ℕ} (h : Algebra.trdeg ℚ K ≤ n) : TrLe K n := by
  haveI : IsScalarTower ℚ (⊥ : Subfield K) K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  refine le_trans ?_ h
  rw [← trdeg_add_eq ℚ (⊥ : Subfield K) (A := K)]
  exact le_add_self

theorem exists_field_of_etale {F A : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [CommRing A] {n : ℕ}
    (g : MvPolynomial (Fin n) F →+* A) (hg : g.Etale) (φ : A →+* ℂ) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (ι : K →+* ℂ) (ψ : A →+* K), TrLe K n ∧ ι.comp ψ = φ := by
  classical
  let B := MvPolynomial (Fin n) F
  letI : Algebra B A := g.toAlgebra
  haveI : Algebra.Etale B A := hg
  letI : Algebra F ℂ := ((φ.comp g).comp MvPolynomial.C).toAlgebra
  let t : Fin n → ℂ := fun i => φ (g (MvPolynomial.X i))
  let L := IntermediateField.adjoin F (Set.range t)
  let K := algebraicClosure L ℂ
  let β : B →ₐ[F] L := MvPolynomial.aeval fun i => ⟨t i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩
  have hβ : (algebraMap L ℂ).comp β.toRingHom = φ.comp g := MvPolynomial.ringHom_ext
    (fun a => by
      show ((β (algebraMap F B a) : L) : ℂ) = _
      rw [β.commutes]; rfl)
    (fun i => by
      show ((β (MvPolynomial.X i) : L) : ℂ) = _
      exact congrArg Subtype.val (MvPolynomial.aeval_X _ i))
  letI : Algebra B L := β.toRingHom.toAlgebra
  letI : Algebra B ℂ := (φ.comp g).toAlgebra
  haveI : IsScalarTower B L ℂ := IsScalarTower.of_algebraMap_eq' hβ.symm
  haveI : Module.Finite L (L ⊗[B] A) := Algebra.FormallyUnramified.finite_of_free L (L ⊗[B] A)
  let Φ : L ⊗[B] A →ₐ[L] ℂ := Algebra.TensorProduct.lift (Algebra.ofId L ℂ) { φ with commutes' := fun _ => rfl }
    fun _ _ => Commute.all _ _
  have hφ : ∀ a, φ a ∈ K := fun a => by
    have h := (Algebra.IsIntegral.isIntegral (R := L) ((1 : L) ⊗ₜ[B] a)).map Φ
    rw [show Φ ((1 : L) ⊗ₜ[B] a) = φ a by simp [Φ]] at h
    exact h
  refine ⟨K, inferInstance, (algebraicClosure.isAlgClosure L ℂ).isAlgClosed, algebraMap K ℂ,
    φ.codRestrict K hφ, trLe_of_rat ?_, rfl⟩
  haveI : IsScalarTower ℚ F L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : IsScalarTower ℚ L K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FaithfulSMul L K := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap L K).injective
  haveI : FaithfulSMul F L := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F L).injective
  rw [← trdeg_add_eq ℚ L (A := K), trdeg_eq_zero (R := L) (A := K), add_zero, ← trdeg_add_eq ℚ F (A := L),
    trdeg_eq_zero (R := ℚ) (A := F), zero_add]
  open IntermediateField.algebraAdjoinAdjoin in
  rw [← trdeg_add_eq F (Algebra.adjoin F (Set.range t)) (A := L),
    trdeg_eq_zero (R := Algebra.adjoin F (Set.range t)) (A := L), add_zero]
  rw [Algebra.adjoin_range_eq_range_aeval]
  refine (trdeg_le_of_surjective _ (MvPolynomial.aeval t).rangeRestrict_surjective).trans ?_
  rw [MvPolynomial.trdeg_of_isDomain]
  simp

theorem exists_field_of_smooth {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] {X : Scheme.{0}}
    (s : X ⟶ Sp F) {n : ℕ} (hs : SmoothOfRelativeDimension n s) (x : Sp ℂ ⟶ X) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (ι : K →+* ℂ) (y : Sp K ⟶ X), TrLe K n ∧ spMap ι ≫ y = x := by
  obtain ⟨R, j, hj, hx, hsm⟩ : ∃ (R : CommRingCat.{0}) (j : Spec R ⟶ X) (_ : IsOpenImmersion j),
      x (default : PrimeSpectrum ℂ) ∈ Set.range j ∧
      (Spec.preimage (j ≫ s)).hom.IsStandardSmoothOfRelativeDimension n := by
    obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ :=
      hs.exists_isStandardSmoothOfRelativeDimension (x (default : PrimeSpectrum ℂ))
    have hU₀ : U₀ = ⊤ := by
      refine eq_top_iff.2 fun y _ => ?_
      have h1 : s (x (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
      have h2 : y = s (x (default : PrimeSpectrum ℂ)) := Subsingleton.elim (α := PrimeSpectrum F) _ _
      rw [h2]; exact h1
    subst hU₀
    refine ⟨_, hU.fromSpec, inferInstance, by rw [hU.range_fromSpec]; exact hp, ?_⟩
    have e : Spec.preimage (hU.fromSpec ≫ s) = (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ s.appLE ⊤ U hle := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hU hle,
        IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    rw [e]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (s.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv hsm
  obtain ⟨g, -, hg⟩ := hsm.exists_etale_mvPolynomial
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) z default]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift j x hr)
  obtain ⟨K, _, _, ι, ψ, h, e⟩ := exists_field_of_etale g hg φ.hom
  refine ⟨K, inferInstance, inferInstance, ι, Spec.map (CommRingCat.ofHom ψ) ≫ j, h, ?_⟩
  rw [← IsOpenImmersion.lift_fac j x hr, ← hφ, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext e

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open MonObj in

theorem exists_obj (l : Level H) (hA : l.A = 1) (T : PAT H (Sp ℂ)) {p q : ℕ}
    (hdet : ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ p) ∧
      (τ H.rt ≠ H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ q)) :
    ∃ (D : Datum H) (o : Obj D l (baseKA l) (spMap (KA l).val.toRingHom)), D.p = p ∧ D.q = q ∧
      Nonempty (SABMap T.t o.t (𝟙 _)) := by
  have hT := thetaUnifAV_all
  have hL := abelianSchemeLaws_all.1
  obtain ⟨g, ty, hty⟩ := AllClasses.exists_isTypeFn H p q
  obtain ⟨u, Hm, χ, -, hAH, -⟩ := PureType.exists_isThetaUnif hT T.pol
  obtain ⟨D, Pe, F, hp, hq, hP, hF, hE, hact⟩ := PureTriple.exists_datum_period hT hL T hty hdet u hAH
  obtain ⟨Ef, hEf, -, -, -, -, hW⟩ := AHWeil.tangent_and_weil_of_isAH hT T.pol _ u Hm χ hAH
  obtain ⟨I, -⟩ := UnifObj.exists_tateIso D D ty Pe (fun a x => x ≫ T.t.act.act a)
    (fun n x y c => Out.WeilIs T.t.G T.t.PP.L n x y (unitOn c)) (fun z => u.ex (F z)) (fun _ => LinearMap.id)
    hP.1 hP.2.1 (fun z z' => by rw [map_add, u.ex_add]) (u.ex_onto.comp F.surjective)
    (fun z => (u.ker _).trans (hF z)) hact
    (fun k a b c hk hc => by
      have := hW k ⟨F (Pe a), (hF _).2 ⟨a, rfl⟩⟩ ⟨F (Pe b), (hF _).2 ⟨b, rfl⟩⟩ c hk (by
        rw [hc]
        congr 4
        exact_mod_cast ((hEf ⟨F (Pe a), (hF _).2 ⟨a, rfl⟩⟩ ⟨F (Pe b), (hF _).2 ⟨b, rfl⟩⟩).trans (hE a b)).symm)
      beta_reduce
      rw [map_smul, map_smul]
      exact this)
    (fun n m _ _ a => ⟨0, by simp⟩) (fun n _ => ⟨fun _ => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩) (fun n _ a a' => by simp)
  obtain ⟨o, m, -⟩ := UnifObj.exists_obj hL hA (baseKA l) (KA l).val.toRingHom T.t T.ab.proper T.dim T.ample T.ktriv
    (D := D) (fun τ => by rw [hp, hq]; exact hdet τ) I
  exact ⟨D, o, hp, hq, ⟨m⟩⟩

theorem exists_field_of_det (l₀ : Level H) (T : PAT H (Sp ℂ)) {p q : ℕ}
    (hdet : ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ p) ∧
      (τ H.rt ≠ H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ q)) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (ι : K →+* ℂ) (P₀ : Out.PolAV (Sp K))
      (φ₀ : T.pol.A.left ⟶ P₀.A.left), TrLe K (Module.finrank ℚ E / 2 * p * q) ∧ IsPolFibre ι P₀ T.pol φ₀ := by
  let l : Level H := { l₀ with A := 1, A_pos := Nat.one_pos }
  obtain ⟨D, o, rfl, rfl, ⟨m⟩⟩ := exists_obj l rfl T hdet
  obtain ⟨Xo⟩ : Nonempty (Moduli D l) := by
    by_cases h : D.p + D.q = 0
    · exact ⟨RankZero.zeroModuli card_torsion_abelianVariety h l⟩
    · exact Moduli.moduli_scheme_exists E H D l (by omega)
  obtain ⟨x, ⟨-, ⟨m'⟩⟩, -⟩ := Xo.rep _ _ inferInstance o
  haveI : Algebra.IsAlgebraic ℚ (KA l) := IntermediateField.isAlgebraic_adjoin (by
    rintro z (rfl | rfl)
    · exact IsIntegral.of_pow two_pos (by rw [H.sqrt_neg_disc_sq]; exact (isIntegral_natCast _).neg)
    · exact (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').isIntegral l.A_pos |>.tower_top)
  obtain ⟨K, _, _, ι, y, hK, hy⟩ := exists_field_of_smooth Xo.s Xo.smooth x
  let U : PAT H Xo.X := ⟨Xo.univ.t, ObjDim.isAbelianScheme _, _, ObjDim.smoothOfRelativeDimension _, ObjDim.sym,
    Xo.univ.ample, Xo.univ.ktriv⟩
  obtain ⟨T₀, ⟨m₀⟩⟩ : ∃ T₀ : PAT H (Sp K), Nonempty (SABMap T₀.t U.t y) := by
    obtain ⟨_, _, _, _, _, m₀, -⟩ := sabPull Out.CubePf.cubePull y U.t
    obtain ⟨⟨T₀, ht, -⟩, -⟩ := PAT.exists_of_sabMap E H _ _ _ U _ m₀
    exact ⟨T₀, ⟨ht ▸ m₀⟩⟩
  obtain ⟨-, e₀⟩ := PAT.exists_of_sabMap E H _ _ _ U _ m₀
  obtain ⟨-, e₁⟩ := PAT.exists_of_sabMap E H _ _ _ U _ m'.toSABMap
  have e₂ : LBIso T.t.PP.L (o.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have n' : IsGrpPullback T.t.G U.t.G (spMap ι ≫ y) (m.φ ≫ m'.φ) :=
    (m.cart.comp m'.cart).congr ((Category.id_comp _).trans hy.symm) rfl
  have w : (m.φ ≫ m'.φ) ≫ U.t.G.hom = (T.t.G.hom ≫ spMap ι) ≫ y := n'.1.w.trans (Category.assoc _ _ _).symm
  have e : m₀.cart.1.lift _ _ w ≫ m₀.φ = m.φ ≫ m'.φ := m₀.cart.1.lift_fst _ _ w
  have hc : IsGrpPullback T.t.G T₀.t.G (spMap ι) (m₀.cart.1.lift _ _ w) :=
    m₀.cart.cancel (n'.congr rfl e.symm) (m₀.cart.1.lift_snd _ _ w)
  refine ⟨K, inferInstance, inferInstance, ι, T₀.pol, m₀.cart.1.lift _ _ w, hK, ?_, hc, ?_⟩
  · have hd : SmoothOfRelativeDimension T₀.g T.t.G.hom :=
      have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} T₀.g
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension T₀.g) hc.1 T₀.dim
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ T.dim hd (eSec T.t.G (default : PrimeSpectrum ℂ))
  · refine LBIso.trans (pull_isLB T₀.t.PP.isLB _) (pull_isLB U.t.PP.isLB _) T.t.PP.isLB (PolFibre.lbIso_pull_comp e₀ _).symm ?_
    rw [e]
    have e₃ : LBIso (U.t.PP.L.pull (m.φ ≫ m'.cm.F)) (o.t.PP.L.pull m.φ) := PolFibre.lbIso_pull_comp (L := U.t.PP.L) e₁ m.φ
    exact LBIso.trans (pull_isLB U.t.PP.isLB _) (pull_isLB o.t.PP.isLB _) T.t.PP.isLB e₃ e₂.symm

theorem exists_field_of_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (_ : Level H) (R : Type) [CommRing R] (σ : R →+* ℂ) (Q : PAT H (Sp R)) (ρ : ℂ) (p q : ℕ), ρ ^ 2 = -(H.d : ℂ) → (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = ρ → LieMult Q.t.act (spMap σ) τ p) ∧ (τ H.rt ≠ ρ → LieMult Q.t.act (spMap σ) τ q)) → ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (ι : K →+* ℂ) (P₀ : Out.PolAV (Sp K)) (P₁ : Out.PolAV (Sp ℂ)) (φ : P₁.A.left ⟶ Q.pol.A.left) (φ₀ : P₁.A.left ⟶ P₀.A.left), TrLe K (Module.finrank ℚ E / 2 * p * q) ∧ IsPolFibre σ Q.pol P₁ φ ∧ IsPolFibre ι P₀ P₁ φ₀ := by
  intro E _ _ _ H l R _ σ Q ρ p q hρ hdet
  obtain ⟨⟨T, m, -⟩, hu⟩ := LamT.pat_pullback E H R ℂ σ Q
  have hf := (hu T m inferInstance).2.1
  have hm : ∀ (τ : 𝓞 E →+* ℂ) (n : ℕ), LieMult Q.t.act (spMap σ) τ n → LieMult T.t.act (𝟙 _) τ n := fun τ n h =>
    (lieMult_iff_of_isGrpPullback m.cart T.t.act Q.t.act m.act (𝟙 _) τ n).2 (by rwa [Category.id_comp])
  by_cases h0 : ρ = H.rt0
  · subst h0
    obtain ⟨K, _, _, ι, P₀, φ₀, h₁, h₂⟩ := exists_field_of_det l T (p := p) (q := q) fun τ =>
      ⟨fun h => hm _ _ ((hdet τ).1 h), fun h => hm _ _ ((hdet τ).2 h)⟩
    exact ⟨K, inferInstance, inferInstance, ι, P₀, T.pol, m.φ, φ₀, h₁, hf, h₂⟩
  · have hsq : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
      rw [← map_pow, H.rt_sq, map_neg, map_natCast]
    have h1 := (sq_eq_sq_iff_eq_or_eq_neg.1 (hρ.trans H.sqrt_neg_disc_sq.symm)).resolve_left h0
    have h2 : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ≠ H.rt0 → τ H.rt = ρ := fun τ h =>
      ((sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq τ).trans H.sqrt_neg_disc_sq.symm)).resolve_left h).trans h1.symm
    obtain ⟨K, _, _, ι, P₀, φ₀, h₁, h₂⟩ := exists_field_of_det l T (p := q) (q := p) fun τ =>
      ⟨fun h => hm _ _ ((hdet τ).2 fun h' => h0 (h'.symm.trans h)), fun h => hm _ _ ((hdet τ).1 (h2 τ h))⟩
    rw [Nat.mul_right_comm] at h₁
    exact ⟨K, inferInstance, inferInstance, ι, P₀, T.pol, m.φ, φ₀, h₁, hf, h₂⟩

end GlobalTheory.BdDim.CxField

end
