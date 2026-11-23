import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyIdentitiesDescendFieldToDedekind
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmFamilyDescendsToNumberField
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionPrincipalTriplesTensorLattiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTensorRetractOfCmDatumRankOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRelationLinearHomsCmSignatureTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfBaseChangeEqPowPrincipalAbelianCMTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmObjHomOfTypeLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfMemSpanRingOfIntegersMapNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenLatticeImageLeSpanAfterBaseChangeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.FlatCM.HomLat.LieSpan

section Over

variable {S S' : Scheme.{0}} {s : S' ⟶ S} {G B : Over S} {G' B' : Over S'} [GrpObj B] [GrpObj B'] [IsCommMonObj B]
  [IsCommMonObj B'] {φ : G'.left ⟶ G.left} {m : B'.left ⟶ B.left}

theorem one_over (w : φ ≫ G.hom = G'.hom ≫ s) (hm : IsGrpPullback B' B s m) :
    (1 : G' ⟶ B').left ≫ m = φ ≫ (1 : G ⟶ B).left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hm G'.hom (G'.hom ≫ s) rfl
  let φ₀ : Over.mk (G'.hom ≫ s) ⟶ G := Over.homMk φ w
  have h1 := he 1
  rw [map_one, ← comp_one φ₀] at h1
  exact h1.symm

theorem prod_over (w : φ ≫ G.hom = G'.hom ≫ s) (hm : IsGrpPullback B' B s m) {I : Type} (t : Finset I)
    {x' : I → (G' ⟶ B')} {x : I → (G ⟶ B)} (h : ∀ i, (x' i).left ≫ m = φ ≫ (x i).left) :
    (∏ i ∈ t, x' i).left ≫ m = φ ≫ (∏ i ∈ t, x i).left := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using one_over w hm
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact FamDesc.exists_mul w hm (h a) ih

end Over

section Rel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R R' : Type} [CommRing R] [CommRing R']
  {j : R →+* R'} {A B : PAT H (Sp R)} {A' B' : PAT H (Sp R')} (mA : SABMap A'.t A.t (spMap j))
  (mB : SABMap B'.t B.t (spMap j))

theorem exists_linear_over {f : A.t.G ⟶ B.t.G} (hf : Serre.IsLinearHom A.t.act B.t.act f) :
    ∃ f' : A'.t.G ⟶ B'.t.G, Serre.IsLinearHom A'.t.act B'.t.act f' ∧ f'.left ≫ mB.φ = mA.φ ≫ f.left := by
  haveI := hf.isMonHom
  obtain ⟨f', hm, e⟩ := PairingFibre.exists_hom mA.cart mB.cart f
  refine ⟨f', ⟨hm, fun c => ?_⟩, e⟩
  apply Over.OverMorphism.ext
  apply mB.cart.1.hom_ext
  · have hc := congrArg CommaMorphism.left (hf.comm c)
    simp only [Over.comp_left] at hc ⊢
    rw [Category.assoc, e, ← Category.assoc, mA.act c, Category.assoc, hc, Category.assoc, mB.act c,
      ← Category.assoc, ← Category.assoc, e]
  · simp only [Over.comp_left, Category.assoc, Over.w]

theorem comb_over {n : ℕ} {f : Fin n → (A.t.G ⟶ B.t.G)} {f' : Fin n → (A'.t.G ⟶ B'.t.G)}
    (h : ∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) (x : Fin n → 𝓞 E) :
    (∏ i, (A'.t.act.act (x i) ≫ f' i)).left ≫ mB.φ = mA.φ ≫ (∏ i, (A.t.act.act (x i) ≫ f i)).left := by
  refine prod_over mA.cart.1.w mB.cart _ fun i => ?_
  rw [Over.comp_left, Over.comp_left, Category.assoc, h, ← Category.assoc, mA.act, Category.assoc]

theorem rel_descend (hj : Function.Injective j) {n : ℕ} {f : Fin n → (A.t.G ⟶ B.t.G)}
    {f' : Fin n → (A'.t.G ⟶ B'.t.G)} (h : ∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) (x : Fin n → 𝓞 E)
    (hx : ∏ i, (A'.t.act.act (x i) ≫ f' i) = 1) : ∏ i, (A.t.act.act (x i) ≫ f i) = 1 := by
  have : IsSchemeTheoreticallyDominant (spMap j) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom j) hj
  have : QuasiCompact (spMap j) := inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom j)))
  have := A.ab.smooth
  have : Flat A.t.G.hom := inferInstance
  have : IsSeparated B.t.G.hom := B.t.semi.separated
  refine ExtUnique.over_hom_ext_of_isPullback mA.cart.1 ?_
  rw [← comb_over mA mB h x, hx]
  exact one_over mA.cart.1.w mB.cart

theorem exists_pow_eq {n : ℕ} {f : A.t.G ⟶ B.t.G} {φ : Fin n → (A.t.G ⟶ B.t.G)}
    (hf : Serre.IsLinearHom A.t.act B.t.act f) (hφ : ∀ a, Serre.IsLinearHom A.t.act B.t.act (φ a)) {x₀ : 𝓞 E}
    (h₀ : x₀ ≠ 0) {x : Fin n → 𝓞 E} (h : (A.t.act.act x₀ ≫ f) * ∏ a, (A.t.act.act (x a) ≫ φ a) = 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ y : Fin n → 𝓞 E, f ^ N = ∏ a, (A.t.act.act (y a) ≫ φ a) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x₀}))
  have hN : Ideal.absNorm (Ideal.span {x₀}) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  refine ⟨_, Nat.pos_of_ne_zero hN, fun a => -(z * x a), ?_⟩
  let F : Serre.Pts B.t.act A.t.G := Serre.Pts.mk _ f
  let Φ : Fin n → Serre.Pts B.t.act A.t.G := fun a => Serre.Pts.mk _ (φ a)
  have h1 : x₀ • F + ∑ a, x a • Φ a = 0 := by
    apply Serre.Pts.ext
    rw [Serre.Pts.hom_add, Serre.Pts.hom_sum, Serre.Pts.hom_zero, ← h, hf.comm]
    simp only [Serre.Pts.hom_smul, (hφ _).comm, F, Φ, Serre.Pts.hom_mk]
  have h2 : Ideal.absNorm (Ideal.span {x₀}) • F = ∑ a, (-(z * x a)) • Φ a := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hz, mul_smul, eq_neg_of_add_eq_zero_left h1, smul_neg, Finset.smul_sum,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [neg_smul, mul_smul]
  have h3 := congrArg Serre.Pts.hom h2
  rw [Serre.Pts.hom_sum] at h3
  simp only [Serre.Pts.hom_smul, ← (hφ _).comm, Φ, Serre.Pts.hom_mk] at h3
  exact h3

end Rel

section Diff

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {A B : PAT H (Sp (𝓞 K))} {FA : GenFib A.pol} {FB : GenFib B.pol}

open IntCoord in

theorem smul_diff_eq {p : ℕ} {φ : Fin p → (A.t.G ⟶ B.t.G)}
    {MP : Fin p → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))} (hMP : ∀ a, FA.IsDiffOf FB (φ a) (MP a))
    {f : A.t.G ⟶ B.t.G} {M : (Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)} (hM : FA.IsDiffOf FB f M) {n : ℕ}
    {x : Fin p → 𝓞 E} (hfn : f ^ n = ∏ a, (A.t.act.act (x a) ≫ φ a)) {τ : 𝓞 E →+* 𝓞 K} {e : Fin FA.P₀.g → K}
    (he : e ∈ FA.eigLat A.t.act τ) : n • M e = ∑ a, ((τ (x a) : 𝓞 K) : K) • MP a e := by
  obtain ⟨u, hu, heig⟩ := ((integral_tangent_coordinates K _ FA).2.2.2.2.2 _ _ τ e).1 he
  have hd := hM u e hu
  have hs : ∀ a, FB.IsCoord (u ≫ (A.t.act.act (x a) ≫ φ a)) (MP a (τ (x a) • e)) := by
    intro a
    rw [← Category.assoc]
    exact hMP a _ _ (isCoord_smul FA hu (heig (x a)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ a ∈ s, (A.t.act.act (x a) ≫ φ a))
      (∑ a ∈ s, MP a (τ (x a) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]
      exact isCoord_mul FB (hs a) ih
  have hpow : ∀ m : ℕ, FB.IsCoord ((u ≫ f) ^ m) (m • M e) := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, zero_smul]
      exact isCoord_one FB
    | succ m ih =>
      rw [pow_succ, succ_nsmul]
      exact isCoord_mul FB ih hd
  have h1 := hpow n
  rw [← comp_pow, hfn] at h1
  rw [((integral_tangent_coordinates K _ FB).1 _ h1.1).unique h1 (hprod Finset.univ)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← algebraMap_smul K (τ (x a)) e, map_smul]

end Diff

theorem exists_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
    {ρ : 𝓞 K} {A B : PAT H (Sp (𝓞 K))} {p q : ℕ} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) (hA : HasType H A.t.act ρ 1 0)
    (hB : HasType H B.t.act ρ p q) {n : ℕ} (hn : p + q < n) {ψ : Fin n → (A.t.G ⟶ B.t.G)}
    (hψ : ∀ i, Serre.IsLinearHom A.t.act B.t.act (ψ i)) :
    ∃ x : Fin n → 𝓞 E, x ≠ 0 ∧ ∏ i, (A.t.act.act (x i) ≫ ψ i) = 1 := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  let β : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K)
  have hβ : Function.Injective β := σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨A', mA, -⟩ := PAT.exists_pullback E H _ _ (spMap β) A
  obtain ⟨B', mB, -⟩ := PAT.exists_pullback E H _ _ (spMap β) B
  choose ψ' hψ' e using fun i => exists_linear_over mA mB (hψ i)
  obtain ⟨x, hx, h⟩ := GlobalTheory.T.exists_integer_relation_linear_homs_cm_signature_type E H (β ρ) A' B' p q (by rw [← map_pow, hρ, map_neg, map_natCast])
    ((hasType_baseChange E H _ _ β _ _ mA ρ 1 0).1 hβ hA) ((hasType_baseChange E H _ _ β _ _ mB ρ p q).1 hβ hB)
    n hn ψ' hψ'
  exact ⟨x, hx, rel_descend mA mB hβ e x h⟩

theorem eigLat_le_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ ≤ Submodule.span (𝓞 K)
            {w | ∃ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X FP FB MP hMP τ _ τE hτE w hw
  obtain ⟨K', _, _, j, ω, C, A', B', mA, mB, DA, DB, hA, hB, rA, -, ⟨tA⟩, ⟨tB⟩⟩ :=
    GlobalTheory.T.exists_finiteExtension_principalTriples_tensorLattice E H K ρ (X.A true) X.B 1 p X.ρ_sq X.typeP X.typeB
  obtain ⟨n, f', g', hf', hg', hfg⟩ := GlobalTheory.T.cmTensor_retract_of_cmDatum_rank_one E H _ ω C A' B' DA DB hA hB rA tA tB
  have hj : Function.Injective (RingOfIntegers.mapRingHom j) := fun a b h => by
    apply RingOfIntegers.ext
    apply j.injective
    exact congrArg (fun x : 𝓞 K' => (x : K')) h
  have hφ : ∀ a, Serre.IsLinearHom (X.A true).t.act X.B.t.act (phiP X a) := fun a => X.lin (Sum.inl a)
  choose φ' hφ' eφ using fun a => exists_linear_over mA mB (hφ a)
  have key : ∀ i, ∃ f : (X.A true).t.G ⟶ X.B.t.G, Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
      (f' i).left ≫ mB.φ = mA.φ ≫ f.left ∧ ∃ N : ℕ, 0 < N ∧ ∃ y : Fin p → 𝓞 E,
        f ^ N = ∏ a, ((X.A true).t.act.act (y a) ≫ phiP X a) := fun i => by
    obtain ⟨x, hx, h⟩ := exists_rel (ρ := RingOfIntegers.mapRingHom j ρ) (A := A') (B := B') (p := p) (q := 0)
      (by rw [← map_pow, X.ρ_sq, map_neg, map_natCast])
      ((hasType_baseChange E H _ _ _ _ _ mA ρ 1 0).1 hj X.typeP)
      ((hasType_baseChange E H _ _ _ _ _ mB ρ p 0).1 hj X.typeB) (Nat.lt_succ_self p)
      (ψ := Fin.cons (f' i) φ') (Fin.cases (hf' i) hφ')
    rw [Fin.prod_univ_succ] at h
    simp only [Fin.cons_zero, Fin.cons_succ] at h
    have h₀ : x 0 ≠ 0 := fun h₀ => by
      haveI := (hf' i).isMonHom
      rw [h₀, Serre.act_zero, MonObj.one_comp, _root_.one_mul] at h
      have hs := GlobalTheory.T.cmObjHomOfType_linearIndependent E H K ρ σ₁ p 0 X _ (rel_descend mA mB hj eφ _ h)
      exact hx (funext (Fin.cases h₀ fun a => congrFun hs a))
    obtain ⟨N, hN, y, hy⟩ := exists_pow_eq (hf' i) hφ' h₀ h
    obtain ⟨f, hf, e₁, e₂⟩ := GlobalTheory.T.eq_pow_of_baseChange_eq_pow_principalAbelianCMTriple E H K K' j (X.A true) X.B A' B' mA mB _ (f' i) N hN (isLinearHom_prod X y) (hf' i)
      (by rw [hy]; exact comb_over mA mB eφ y)
    exact ⟨f, hf, e₂, N, hN, y, e₁⟩
  choose f hf ef N hN y hy using key
  choose M hM using fun i =>
    (DiffCoord.existsUnique_isDiffOf K _ FP _ FB (f i) (hf i).isMonHom).1.exists
  refine GlobalTheory.T.mem_of_mem_span_ringOfIntegers_map_numberField K K' j _ _ w (Submodule.span_mono (Set.image_mono ?_)
    (GlobalTheory.T.eigenLattice_image_le_span_after_baseChange E H K K' j (X.A true) X.B A' B' mA mB n f f' g' hf hf' hg' ef hfg FP FB M hM τ w hw))
  rintro _ ⟨i, e, he, rfl⟩
  have hE : (N i : E) ≠ 0 := Nat.cast_ne_zero.2 (hN i).ne'
  have hK : (N i : K) ≠ 0 := Nat.cast_ne_zero.2 (hN i).ne'
  refine Submodule.subset_span ⟨fun a => (y i a : E) / N i,
    Submodule.subset_span ⟨N i, hN i, y i, fun a => by field_simp, f i, hf i, hy i⟩, e, he, ?_⟩
  refine smul_right_injective _ hK ?_
  show (N i : K) • M i e = (N i : K) • _
  rw [Nat.cast_smul_eq_nsmul, smul_diff_eq hMP (hM i) (hy i) he, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, map_div₀, hτE, map_natCast, mul_div_cancel₀ _ hK]

end GlobalTheory.FlatCM.HomLat.LieSpan
