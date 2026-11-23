import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixExistsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroupStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRham

open GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.Published GlobalTheory.Published.AbelianDeRham DividedPowers

variable {R : Type} [CommRing R]

theorem exists_mem_Fil_corr (P : AbelianDeRham) {T : Type} [CommRing T] [Algebra T R]
    (su : Function.Surjective (algebraMap T R)) {C : Over (Sp T)} [GrpObj C] {g : ℕ} (hC : IsAbelianScheme C)
    (gC : SmoothOfRelativeDimension g C.hom) {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ C.left}
    (h : IsGrpPullback A C (spMap (algebraMap T R)) φ) {f : HdR A} (hf : f ∈ Fil A) :
    ∃ d ∈ Fil C, (bcMor h).Corr d f := by
  obtain ⟨-, hF⟩ := P.2.2.1 T C g hC gC R A φ h
  obtain ⟨-, ⟨N, hN⟩, -⟩ := P.2.1 T C g hC gC
  haveI : Module.Projective T (primDR C) := (P.1.prim hC gC).2.1
  let l : primDR C →ₗ[T] R :=
    { toFun c := f ((bcMor h).pull c)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun a b => by rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  obtain ⟨d₀, hd₀⟩ := Module.projective_lifting_property (Algebra.linearMap T R) l su
  have e₀ : ∀ c, algebraMap T R (d₀ c) = f ((bcMor h).pull c) := fun c => LinearMap.congr_fun hd₀ c
  have z : ∀ c ∈ PrimitiveSubmodule C, f ((bcMor h).pull c) = 0 := fun c hc =>
    (Submodule.mem_dualAnnihilator _).1 hf _ (hF ▸ Submodule.subset_span ⟨c, hc, rfl⟩)
  let p : primDR C →ₗ[T] primDR C := N.subtype ∘ₗ N.linearProjOfIsCompl _ hN.symm
  have p0 : ∀ c ∈ PrimitiveSubmodule C, p c = 0 := fun c hc =>
    (congrArg N.subtype (Submodule.linearProjOfIsCompl_apply_right hN.symm ⟨c, hc⟩)).trans (map_zero _)
  have p1 : ∀ c, c - p c ∈ PrimitiveSubmodule C := fun c => by
    obtain ⟨a, b, rfl, -⟩ := Submodule.existsUnique_add_of_isCompl hN c
    have e : p b = b := congrArg N.subtype (Submodule.linearProjOfIsCompl_apply_left hN.symm b)
    rw [map_add, p0 a a.2, e, zero_add, add_sub_cancel_right]
    exact a.2
  refine ⟨d₀ ∘ₗ p, (Submodule.mem_dualAnnihilator _).2 fun c hc => ?_, fun c => ?_⟩
  · rw [LinearMap.comp_apply, p0 c hc, map_zero]
  · rw [LinearMap.comp_apply, e₀, ← sub_eq_zero, ← map_sub, ← map_sub]
    exact z _ (p1 c)

set_option maxHeartbeats 1000000 in

theorem exists_isFilLift_dir (P : AbelianDeRham) {ι : Type} [Fintype ι] {C : Over (Sp (TrivSqZeroExt R (ι → R)))}
    [GrpObj C] {g : ℕ} (hC : IsAbelianScheme C) (gC : SmoothOfRelativeDimension g C.hom) {A : Over (Sp R)} [GrpObj A]
    {φ₀ : A.left ⟶ C.left} (h₀ : IsGrpPullback A C (spMap (TrivSqZeroExt.fstHom R R (ι → R)).toRingHom) φ₀)
    {f : HdR A} (hf : f ∈ Fil A) :
    ∃ gs : ι → HdR A, ∀ (m : ι → R) (B : Over (Sp (DualNumber R))) [GrpObj B] (φ : B.left ⟶ C.left)
      (j : A.left ⟶ B.left) (hj : IsGrpPullback A B (epsRed R) j),
      IsGrpPullback B C (spMap (TrivSqZeroExt.map (Fintype.linearCombination R m)).toRingHom) φ → j ≫ φ = φ₀ →
      IsFilLift hj f (∑ k, m k • gs k) := by
  let κ : DividedPowers (RingHom.ker (TrivSqZeroExt.fstHom R R (ι → R)).toRingHom) :=
    divided₂ (SqExt.ofModule R R (ι → R)).sq
  have su : Function.Surjective (TrivSqZeroExt.fstHom R R (ι → R)).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have su' : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rC := P.2.2.2.1 _ C g hC gC _ κ (isDPNilpotent_squareZero _) R _ su rfl A φ₀ h₀
  have cst : GrpMor (dp0 R) (𝟙 _) A κ (spMap (TrivSqZeroExt.fstHom R R (ι → R)).toRingHom) A
      (algebraMap R (TrivSqZeroExt R (ι → R))) (𝟙 _) (Over.Hom.left (𝟙 A)) :=
    GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _)
      (by rw [← Cris.spMap_comp]; exact (Cris.spMap_id R).symm) (𝟙 A)
  have red : GrpMor κ (spMap (TrivSqZeroExt.fstHom R R (ι → R)).toRingHom) A (dp0 R) (𝟙 _) A
      (TrivSqZeroExt.fstHom R R (ι → R)).toRingHom (𝟙 _) (Over.Hom.left (𝟙 A)) := by
    refine GrpMor.of_hom ?_ (by rw [Category.id_comp]) (𝟙 A)
    refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha => ha, fun n hn a ha => ?_⟩
    have ha' : (TrivSqZeroExt.fstHom R R (ι → R)).toRingHom a = 0 := ha
    rw [ha', dpow_eval_zero _ hn]
    rcases n with _ | _ | n
    · exact absurd rfl hn
    · rw [zero_add, κ.dpow_one ha, ha']
    · have e : κ.dpow (n + 1 + 1) a = 0 := squareZeroDividedPowers_dpow _ (by omega) a
      rw [e, map_zero]
  obtain ⟨d, hd, D, eD, ef⟩ : ∃ d ∈ Fil C, ∃ D, crysToDR κ h₀ D = d ∧ ∀ c, (D (cst.pull c)).fst = f c := by
    letI : Algebra (TrivSqZeroExt R (ι → R)) R := (TrivSqZeroExt.fstHom R R (ι → R)).toRingHom.toAlgebra
    obtain ⟨d, hd, ed⟩ := exists_mem_Fil_corr P su hC gC h₀ hf
    obtain ⟨D, rfl⟩ := (P.2.2.2.1.crysToDR_bijective hC gC (κ := κ) (isDPNilpotent_squareZero _) su rfl h₀).2 d
    refine ⟨_, hd, D, rfl, fun c => ?_⟩
    obtain ⟨e, he⟩ := rC.2 (cst.pull c)
    have k1 : red.pull (cst.pull c) = c :=
      (GrpMor.pull_pull cst red (homMor (dp0 R) (𝟙 _) (𝟙 A))
        (fun r => by simp [TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c).trans (Subtype.ext (IsMor.pullCohomologyOne_id _ c.1))
    have k2 : red.pull ((liftMor κ h₀).pull e) = (bcMor h₀).pull e :=
      GrpMor.pull_pull (liftMor κ h₀) red (bcMor h₀) (fun _ => rfl) (by simp) e
    rw [he, k1] at k2
    rw [← he]
    exact ((congrArg f k2).trans (ed e)).symm
  let gs : ι → HdR A := fun k =>
    { toFun c := (D (cst.pull c)).snd k
      map_add' := fun a b => by rw [LinearMap.map_add, LinearMap.map_add]; rfl
      map_smul' := fun a b => by
        rw [LinearMap.map_smulₛₗ, map_smul]
        simp [TrivSqZeroExt.algebraMap_eq_inl] }
  refine ⟨gs, fun m B _ φ j hj hφ sq => ?_⟩
  letI : Algebra (TrivSqZeroExt R (ι → R)) (DualNumber R) :=
    (TrivSqZeroExt.map (Fintype.linearCombination R m)).toRingHom.toAlgebra
  have hB := PolPull.isAbelianScheme_of_isGrpPullback hC hφ
  have gB := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 gC
  obtain ⟨bc, hF⟩ := P.2.2.1 _ C g hC gC _ B φ hφ
  have rB := P.2.2.2.1.crysToDR_bijective hB gB (κ := epsDP R) (isDPNilpotent_squareZero _) su' rfl hj
  obtain ⟨x', ex⟩ := bc.exists d
  obtain ⟨d', rfl⟩ := rB.2 x'
  subst eD
  have μ : GrpMor κ (spMap (TrivSqZeroExt.fstHom R R (ι → R)).toRingHom) A (epsDP R) (epsRed R) A
      (TrivSqZeroExt.map (Fintype.linearCombination R m)).toRingHom (𝟙 _) (Over.Hom.left (𝟙 A)) :=
    GrpMor.of_hom (isDPMorphism_sqDP _ _ _ fun a ha => (TrivSqZeroExt.fst_map _ a).trans ha) (by
      rw [← Cris.spMap_comp]
      exact congrArg spMap (RingHom.ext fun a => (TrivSqZeroExt.fst_map _ a).symm)) (𝟙 A)
  have em : μ.Corr D d' := fun c => by
    obtain ⟨c, rfl⟩ := rC.2 c
    have n := (liftMor κ h₀).comp μ
    rw [GrpMor.pull_pull (liftMor κ h₀) μ n (fun _ => rfl) rfl c,
      ← GrpMor.pull_pull (bcMor hφ) (liftMor (epsDP R) hj) n (fun _ => rfl) (by simpa using sq) c]
    exact ex c
  refine ⟨d', mem_Fil_of_corr (hφ := hφ) hF ex hd, fun c => ?_⟩
  rw [← GrpMor.pull_pull cst μ (constMor A) (fun r => (TrivSqZeroExt.map _).commutes r) (by simp) c, em]
  refine TrivSqZeroExt.ext ?_ ?_
  · exact (TrivSqZeroExt.fst_map _ _).trans ((ef c).trans (by simp))
  · refine (TrivSqZeroExt.snd_map _ _).trans ?_
    simp [Fintype.linearCombination_apply, gs, mul_comm]

end GlobalTheory.DeRham

namespace GlobalTheory.FlagTan

open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]

theorem IsKS.row (P : AbelianDeRham) {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} {x' : Sp (DualNumber K) ⟶ Xo.X}
    {M : HIx Dw Φ → K} (hM : IsKS Φ y x' M) {B : Over (Sp K)} [GrpObj B] {B' : Over (Sp (DualNumber K))} [GrpObj B']
    {ρ : B.left ⟶ Xo.univ.t.G.left} {ρ' : B'.left ⟶ Xo.univ.t.G.left} {j : B.left ⟶ B'.left}
    (hj : IsGrpPullback B B' (DeRham.epsRed K) j) {b₂ : LinearMap.BilinForm K (HdR B)}
    {vb : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ B)} {kb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR B}
    (hρ : IsGrpPullback B Xo.univ.t.G y.x ρ) (hρ' : IsGrpPullback B' Xo.univ.t.G x' ρ') (e₂ : j ≫ ρ' = ρ)
    (hpol₂ : IsPolForm (dp0 K) (𝟙 _) B (Xo.univ.t.PP.L.pull ρ) b₂) (hv : ∀ σ k, (vb σ k).left ≫ ρ = y.u σ k)
    (hl₂ : ∀ σ k, DeRham.IsLieImage (kb ⟨σ, k⟩) (vb σ k)) (τ : Φ) (r : Fin (Dw.mult (conjEmb τ.1))) {f₂ : HdR B}
    (hf₂ : f₂ ∈ Fil B) (hd₂ : ∀ k, b₂ f₂ (kb k) = @ite K (k = ⟨conjEmb τ.1, r⟩) (Classical.propDecidable _) 1 0) :
    ∃ w, IsLieComb (fun b => M ⟨τ, r, b⟩) (vb τ.1) w ∧ IsKSValue hj f₂ w := by
  obtain ⟨A, _, A', _, π, π', i, hi, b, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hM
  obtain ⟨φ, hφ, eφ⟩ := exists_isGrpPullback_self hπ hρ (spMap_algebraMap_id (K := K))
  obtain ⟨φ', hφ', eφ'⟩ := exists_isGrpPullback_self hπ' hρ' (spMap_dualMap_id (K := K))
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hB := PolPull.isAbelianScheme_of_isGrpPullback hU hρ
  have gB := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hρ.1 hg
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  haveI : IsCommMonObj B := PolPull.isCommMonObj_of_isGrpPullback hρ
  have sq : j ≫ φ' = φ ≫ i := by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, eφ', e₂, e, eφ]
    · have w1 : φ' ≫ A'.hom = B'.hom ≫ spMap (dualMap (algebraMap K K)) := hφ'.1.w
      have w2 : i ≫ A'.hom = A.hom ≫ DeRham.epsRed K := hi.1.w
      have w3 : j ≫ B'.hom = B.hom ≫ DeRham.epsRed K := hj.1.w
      have w4 : φ ≫ A.hom = B.hom ≫ spMap (algebraMap K K) := hφ.1.w
      rw [spMap_dualMap_id, Category.comp_id] at w1
      rw [spMap_algebraMap_id, Category.comp_id] at w4
      rw [Category.assoc, Category.assoc, w1, w2, ← Category.assoc, w3, w4]
  obtain ⟨bc, hF⟩ := P.2.2.1 K A _ hA gA K B φ hφ
  have hL := (P.2.1 K B _ hB gB).1
  have isL := Xo.univ.t.PP.isLB
  have isLρ := pull_isLB isL ρ
  obtain ⟨b', hpol', eb⟩ := hpol.pull_comp (AbelianDeRham.bcMor hφ) isL
  rw [eφ] at hpol'
  obtain rfl : b' = b₂ := IsPolForm.unique P.1 hB gB isLρ hpol' hpol₂
  obtain ⟨iso, perf⟩ := P.2.2.2.2 K B _ hB gB _ isLρ _ hpol'
  obtain ⟨w, hw⟩ := ChernExists.lbIso_refl isLρ
  have pp := perf (kTriv_pull hρ isL isLρ ((isGen_iff w).1 hw) Xo.univ.ktriv)
  choose tv' htv using ArcQ.NormalForm.exists_baseChange hφ
  choose th hth using bc.exists
  have et : ∀ (σ k), tv' (ub σ k) = vb σ k := fun σ k => by
    apply push_inj hρ
    apply Over.OverMorphism.ext
    change (tv' (ub σ k)).left ≫ ρ = (vb σ k).left ≫ ρ
    rw [hv, ← eφ, ← Category.assoc, htv, spMap_dualMap_id, Category.id_comp, hu]
  have hvs : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), pushHom hρ (epsR K) (vb k.1 k.2) = tv (fullB y k) :=
    fun k => Over.OverMorphism.ext (hv k.1 k.2)
  have zero : ∀ f ∈ Fil B, (∀ k, b' f (kb k) = 0) → f = 0 := fun f hf h0 => by
    apply pp.bijective_left.1
    rw [map_zero]
    refine LinearMap.ext fun h => ?_
    obtain ⟨a, ha⟩ := exists_sub_mem_Fil hρ hL hvs (kb := kb) (fun k => hl₂ k.1 k.2) h
    have := iso f hf _ ha
    rw [map_sub, map_sum] at this
    simpa [h0] using this
  have ed : ∀ k, th (hb k) - kb k ∈ Fil B := fun k => by
    have := (hl k.1 k.2).baseChange (hφ := hφ) hF hL (hth _) (htv _)
    rw [et] at this
    exact this.sub_mem (hl₂ k.1 k.2)
  obtain ⟨w₁, hc₁, f₁, hf₁, hd₁, hv₁⟩ := hM τ r
  have mf : th f₁ ∈ Fil B := mem_Fil_of_corr (hφ := hφ) hF (hth f₁) hf₁
  have ev₁ : IsKSValue hj (th f₁) (tv' w₁) := hv₁.baseChange (hφ := hφ) P hA' gA' hj hφ' sq (hth f₁) (htv w₁)
  have e0 : th f₁ - f₂ = 0 := zero _ (sub_mem mf hf₂) fun k => by
    have h1 := eb _ _ _ _ (hth f₁) (hth (hb k))
    have h2 := iso _ mf _ (ed k)
    rw [map_sub, h1, hd₁, sub_eq_zero] at h2
    rw [map_sub, LinearMap.sub_apply, hd₂, ← h2]
    simp
  rw [sub_eq_zero.1 e0] at ev₁
  have c₁ := ArcQ.NormalForm.isLieComb_baseChange hφ (u := fun i => tv' (ub τ.1 i)) (fun _ => htv _) (htv w₁) hc₁
  simp only [et, Algebra.algebraMap_self, RingHom.id_apply] at c₁
  exact ⟨_, c₁, ev₁⟩

theorem isKS_dir_sum : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K]
    (y : FrPt Xo c K) (ι : Type) [Fintype ι] [DecidableEq ι] (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X),
    1 ≤ Dw.p + Dw.q → X ≫ Xo.s = sOf c _ → spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x →
    ∀ N : ι → HIx Dw (psiSet H) → K,
      (∀ k, IsKS (psiSet H) y (spMap (dir c (Pi.single k (1 : K))).toRingHom ≫ X) (N k)) →
      ∀ M : ι → K, IsKS (psiSet H) y (spMap (dir c M).toRingHom ≫ X) (∑ k, M k • N k) := by
  intro Pr E _ _ _ H Dw l Xo c K _ _ y ι _ _ X hpq hXs hXy N hN M
  have P := Pr.p5
  have e₀ : ∀ m : ι → K, DeRham.epsRed K ≫ spMap (dir c m).toRingHom =
      spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom := fun m => by
    rw [← Cris.spMap_comp]
    exact congrArg spMap (RingHom.ext fun z => fst_dir (c := c) m z)
  have tan : IsTanX y (spMap (dir c M).toRingHom ≫ X) := by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, hXs]
      unfold sOf
      rw [← Cris.spMap_comp]
      exact congrArg spMap (RingHom.ext fun r => (dir c M).commutes _)
    · rw [← Category.assoc, ← hXy]
      exact congrArg (· ≫ X) (e₀ M)
  obtain ⟨M₀, A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hpol, hu, hl, what₂⟩ :=
    GlobalTheory.T.kodaira_spencer_matrix_exists Pr E H Dw l Xo c K y _ hpq tan
  obtain ⟨C, _, πC, hC⟩ := exists_isGrpPullback Xo.univ.t.G X
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have aC := PolPull.isAbelianScheme_of_isGrpPullback hU hC
  have gC := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hC.1 hg
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hL := (P.2.1 K A _ hA gA).1
  obtain ⟨φ, hφ, eφ⟩ : ∃ φ : A'.left ⟶ C.left, IsGrpPullback A' C (spMap (dir c M).toRingHom) φ ∧ φ ≫ πC = π' := by
    have w : π' ≫ Xo.univ.t.G.hom = (A'.hom ≫ spMap (dir c M).toRingHom) ≫ X :=
      hπ'.1.w.trans (Category.assoc _ _ _).symm
    exact ⟨hC.1.lift _ _ w, hC.cancel (hπ'.congr rfl (hC.1.lift_fst _ _ w).symm) (hC.1.lift_snd _ _ w),
      hC.1.lift_fst _ _ w⟩
  have h₀ := (hi.comp hφ).congr (e₀ M) rfl
  refine ⟨A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hpol, hu, hl, fun τ a => ?_⟩
  obtain ⟨-, -, f, hf, hd, -⟩ := what₂ τ a
  obtain ⟨gs, hgs⟩ := exists_isFilLift_dir P aC gC h₀ hf
  have row : ∀ k, ∃ w, IsLieComb (fun b => N k ⟨τ, a, b⟩) (ub τ.1) w ∧ DeRham.IsLieImage (gs k) w := fun k => by
    obtain ⟨B, _, χ, hχ⟩ := exists_isGrpPullback C (spMap (dir c (Pi.single k (1 : K))).toRingHom)
    have w : (i ≫ φ) ≫ C.hom = (A.hom ≫ DeRham.epsRed K) ≫ spMap (dir c (Pi.single k (1 : K))).toRingHom := by
      rw [Category.assoc _ (DeRham.epsRed K), e₀]
      exact h₀.1.w
    have sq : hχ.1.lift _ _ w ≫ χ = i ≫ φ := hχ.1.lift_fst _ _ _
    have hj : IsGrpPullback A B (DeRham.epsRed K) (hχ.1.lift _ _ w) :=
      hχ.cancel (h₀.congr (e₀ _).symm sq.symm) (hχ.1.lift_snd _ _ _)
    obtain ⟨v, hc, hv⟩ := (hN k).row P hj hπ (hχ.comp hC)
      (by rw [← Category.assoc, sq, Category.assoc, eφ, hiπ]) hpol hu hl τ a hf hd
    obtain ⟨v', hv', -⟩ := hL.1 (gs k)
    have fl := hgs (Pi.single k 1) B χ _ hj hχ sq
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at fl
    obtain rfl := IsKSValue.unique P (PolPull.isAbelianScheme_of_isGrpPullback aC hχ)
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hχ.1 gC) hv ⟨_, fl, hv'⟩
    exact ⟨_, hc, hv'⟩
  choose w hwc hwl using row
  let e := (Fintype.equivFin ι).symm
  refine ⟨lieComb (fun q => M (e q)) (fun q => w (e q)), ?_, f, hf, hd, _, ?_,
    isLieImage_lieComb _ (f := fun q => gs (e q)) fun q => hwl _⟩
  · obtain ⟨V, _, _, v, -, -, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo K y.x
    choose n hn using fun σ k => (htan _).1 (y.tan σ k)
    have key : ∀ {m : ℕ} (cf : Fin m → K) (u : Fin m → (epsR K ⟶ A)) (b : Fin m → V) (w : epsR K ⟶ A),
        (∀ j, (u j).left ≫ π = v (b j)) → (IsLieComb cf u w ↔ w.left ≫ π = v (∑ j, cf j • b j)) :=
      fun cf u b w hu => by rw [isLieComb_iff_isCombAt hπ, funext hu, hcomb]
    have hun : ∀ j, (ub τ.1 j).left ≫ π = v (n τ.1 j) := fun j => (hu _ j).trans (hn _ j).symm
    rw [key _ _ _ _ hun, (key _ _ _ _ fun q => (key _ _ _ _ hun).1 (hwc (e q))).1 (isLieComb_lieComb _ _),
      e.sum_comp fun k => M k • ∑ j, N k ⟨τ, a, j⟩ • n τ.1 j]
    congr 1
    simp only [Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
    exact Finset.sum_comm
  · rw [e.sum_comp fun k => M k • gs k]
    exact hgs M A' φ i hi hφ rfl

end GlobalTheory.FlagTan
