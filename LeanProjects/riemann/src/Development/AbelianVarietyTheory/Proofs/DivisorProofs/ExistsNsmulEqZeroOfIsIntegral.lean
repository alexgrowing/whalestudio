import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelRelAmpleAndPrincipalAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoOfDisjointCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HodgeMin

open GlobalTheory.CechPic

theorem exists_norm {K Ω : Type} [Field K] [Field Ω] (κ : K →+* Ω) {σ : Ω} (h0 : σ ≠ 0) (hσ : κ.IsIntegralElem σ) :
    ∃ (d : ℕ) (ν : K), 1 ≤ d ∧ ν ≠ 0 ∧ ∀ (R : Type) [CommRing R] (φ : R →+* K) (tr : K),
      ((κ.comp φ).IsIntegralElem (κ tr * σ) → φ.IsIntegralElem (tr ^ d * ν)) ∧
      ((κ.comp φ).IsIntegralElem (κ tr * σ)⁻¹ → φ.IsIntegralElem (tr ^ d * ν)⁻¹) := by
  letI := κ.toAlgebra
  let E := IntermediateField.adjoin K {σ}
  have : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hσ
  let s : E := IntermediateField.AdjoinSimple.gen K σ
  have key : ∀ (R : Type) [CommRing R] (φ : R →+* K) (x : E), (κ.comp φ).IsIntegralElem (x : Ω) →
      φ.IsIntegralElem (Algebra.norm K x) := by
    intro R _ φ x ⟨P, hP, e⟩
    letI := φ.toAlgebra
    letI := ((algebraMap K E).comp φ).toAlgebra
    have : IsScalarTower R K E := .of_algebraMap_eq fun _ => rfl
    refine Algebra.isIntegral_norm (R := R) K ⟨P, hP, (algebraMap E Ω).injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero]
    exact e
  have hn : ∀ tr : K, Algebra.norm K (algebraMap K E tr * s) = tr ^ Module.finrank K E * Algebra.norm K s := fun tr => by
    rw [map_mul, Algebra.norm_algebraMap]
  refine ⟨Module.finrank K E, Algebra.norm K s, Module.finrank_pos, Algebra.norm_ne_zero_iff.2 fun h => h0 (congrArg Subtype.val h),
    fun R _ φ tr => ⟨fun h => hn tr ▸ key R φ _ h, fun h => ?_⟩⟩
  rw [← hn, ← Algebra.norm_inv]
  exact key R φ _ h

theorem exists_section {S : Scheme.{0}} [IsIntegral S] [GlobalTheory.IsNormalScheme S] (U : S.Opens) (hU : genericPoint S ∈ U)
    (x : S.functionField) (h : ∀ (V : S.Opens) (hV : genericPoint S ∈ V), IsAffineOpen V → V ≤ U →
      (S.presheaf.germ V _ hV).hom.IsIntegralElem x) : ∃ a : Γ(S, U), (S.presheaf.germ U _ hU).hom a = x := by
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  refine GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally U x fun y hy => ?_
  obtain ⟨_, ⟨(V : S.Opens), hV, rfl⟩, hyV, hVU⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  obtain ⟨s, hs⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (R := Γ(S, V)) (A := S.functionField) (x := x)
    (h V _ hV hVU)
  exact ⟨V, this, s, hyV, hVU, hs⟩

theorem exists_nsmul_eq_zero_of_isIntegral {S W : Scheme.{0}} (p : W ⟶ S) [IsIntegral S] [GlobalTheory.IsNormalScheme S]
    [UniversallyClosed p] [Surjective p] (c : Pic S) (h : pull p c = 0) : ∃ d : ℕ, 1 ≤ d ∧ d • c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hL p)).1 h
  let ξ := genericPoint S
  have hξ : ∀ (V : S.Opens) (y : S), y ∈ V → ξ ∈ V := fun V y hy =>
    ((genericPoint_spec S).specializes (Set.mem_univ y)).mem_open V.isOpen hy
  obtain ⟨w, hw⟩ := p.surjective ξ
  have hsp : p w ⤳ ξ := hw ▸ specializes_rfl
  have hw' : ∀ {V : S.Opens}, ξ ∈ V → p w ∈ V := fun h => hw ▸ h
  let ρ : W.presheaf.stalk w →+* W.residueField w := (W.residue w).hom
  let κ : S.functionField →+* W.residueField w := ρ.comp (S.presheaf.stalkSpecializes hsp ≫ p.stalkMap w).hom
  have hκ : ∀ (V : S.Opens) (hV : ξ ∈ V), κ.comp (S.presheaf.germ V ξ hV).hom =
      (ρ.comp (W.presheaf.germ (p ⁻¹ᵁ V) w (hw' hV)).hom).comp (p.app V).hom := fun V hV => by
    have e : S.presheaf.germ V ξ hV ≫ S.presheaf.stalkSpecializes hsp ≫ p.stalkMap w =
        p.app V ≫ W.presheaf.germ (p ⁻¹ᵁ V) w (hw' hV) := by
      rw [S.presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
    exact congrArg (fun q => ρ.comp q.hom) e
  let σ : L.ι → W.residueField w := fun i => ρ (gm (𝟙 W) w _ (t.s fun _ => i)).val
  let tr : L.ι → L.ι → S.functionField := fun i j => (gm (𝟙 S) ξ _ (L.g i j)).val
  have hσ0 : ∀ i, σ i ≠ 0 := fun i => ((gm (𝟙 W) w _ (t.s fun _ => i)).isUnit.map ρ).ne_zero
  have hσ : ∀ i j, ξ ∈ L.U i → ξ ∈ L.U j → σ i = κ (tr i j) * σ j := fun i j hi hj => by
    have e := (isGen_iff_germ t).1 ht w (fun _ => i) (fun _ => j) (mem_pull.2 (hw' hi)) (mem_pull.2 (hw' hj))
    rw [gm_pull_g L p (𝟙 W) w _ _ (mem_pull.2 (hw' hi)) (mem_pull.2 (hw' hj)), Category.id_comp] at e
    refine (congrArg (fun u => ρ u.val) e).trans ((map_mul ρ _ _).trans (congrArg (· * σ j) ?_))
    have hij : ξ ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
    rw [gm_val p w _ (hw' hij)]
    refine (RingHom.congr_fun (hκ _ hij) _).symm.trans (congrArg κ ?_)
    exact (gm_val (𝟙 S) ξ _ hij _).symm
  have hint : ∀ i (V : S.Opens) (hV : ξ ∈ V), IsAffineOpen V → V ≤ L.U i → ∀ u : Γ(W, (L.pull p).U fun _ => i)ˣ,
      (κ.comp (S.presheaf.germ V ξ hV).hom).IsIntegralElem (ρ (gm (𝟙 W) w _ u).val) := fun i V hV ha hle u => by
    have l : p ⁻¹ᵁ V ≤ (L.pull p).U fun _ => i := fun x hx => mem_pull.2 (hle hx)
    rw [hκ, ← gm_res (𝟙 W) w l (hw' hV), gm_val (𝟙 W) w _ (hw' hV)]
    exact RingHom.IsIntegralElem.map (GenPush.isIntegral_app_of_universallyClosed p V ha (res l u).val)
      (ρ.comp (W.presheaf.germ (p ⁻¹ᵁ V) w (hw' hV)).hom)
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ξ
  obtain ⟨d, ν, hd, hν, H⟩ := exists_norm κ (hσ0 i₀) (by
    obtain ⟨_, ⟨(V : S.Opens), hV, rfl⟩, hyV, hVU⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hi₀ (L.U i₀).isOpen
    exact RingHom.IsIntegralElem.of_comp (hint i₀ V hyV hV hVU _))
  have ex : ∀ i, ∃ a : Γ(S, L.U i)ˣ, ξ ∈ L.U i → (gm (𝟙 S) ξ _ a).val = tr i i₀ ^ d * ν := fun i => by
    by_cases hi : ξ ∈ L.U i
    swap
    · exact ⟨1, fun h => (hi h).elim⟩
    obtain ⟨a, ha⟩ := exists_section (L.U i) hi (tr i i₀ ^ d * ν) fun V hV hV' hle =>
      (H _ _ _).1 (hσ i i₀ hi hi₀ ▸ hint i V hV hV' hle _)
    obtain ⟨b, hb⟩ := exists_section (L.U i) hi (tr i i₀ ^ d * ν)⁻¹ fun V hV hV' hle => (H _ _ _).2 (by
      have := hint i V hV hV' hle (t.s fun _ => i)⁻¹
      rwa [map_inv, map_units_inv ρ, show ρ _ = σ i from rfl, hσ i i₀ hi hi₀] at this)
    have hab : a * b = 1 := germ_injective_of_isIntegral S ξ hi (by
      refine (map_mul (S.presheaf.germ _ ξ hi).hom a b).trans ?_
      rw [ha, hb, map_one]
      exact mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero _ (gm (𝟙 S) ξ _ (L.g i i₀)).ne_zero) hν))
    exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, fun _ => (gm_val (𝟙 S) ξ _ hi _).trans ha⟩
  choose a ha using ex
  have hg : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (a i) =
      L.g i j ^ d * res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (a j) := fun i j => by
    by_cases hij : ξ ∈ L.U i ⊓ L.U j
    swap
    · exact unit_ext fun y hy => (hij (hξ _ y hy)).elim
    have e : gm (𝟙 S) ξ _ (res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (a i)) =
        gm (𝟙 S) ξ _ (L.g i j ^ d * res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (a j)) := by
      rw [map_mul, map_pow, gm_res _ ξ _ hij, gm_res _ ξ _ hij]
      apply Units.ext
      rw [Units.val_mul, Units.val_pow_eq_pow_val, ha i hij.1, ha j hij.2, ← _root_.mul_assoc, ← mul_pow]
      exact congrArg (fun u => u.val ^ d * ν) (gm_cocycle hL (𝟙 S) ξ hij.1 hij.2 hi₀).symm
    have e' := congrArg Units.val e
    rw [gm_val _ ξ _ hij, gm_val _ ξ _ hij] at e'
    exact Units.ext (germ_injective_of_isIntegral S ξ hij e')
  refine ⟨d, hd, ?_⟩
  rw [← cls_lbPow hL d (isLB_lbPow hL d), cls_eq_zero_iff]
  refine ⟨⟨fun J => res (LB.wchart_le L (fun _ : PUnit => 𝟙 S) J PUnit.unit) (a (J PUnit.unit))⟩,
    (isGen_iff_germ _).2 fun y J J' hJ hJ' => ?_⟩
  have m : y ∈ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) := ⟨Set.mem_iInter.1 hJ PUnit.unit, Set.mem_iInter.1 hJ' PUnit.unit⟩
  have e := congrArg (gm (𝟙 S) y _) (hg (J PUnit.unit) (J' PUnit.unit))
  rw [map_mul, map_pow, gm_res _ y _ m, gm_res _ y _ m] at e
  refine (gm_res (𝟙 S) y _ hJ _).trans (e.trans (congrArg₂ (· * ·) ?_ (gm_res (𝟙 S) y _ hJ' _).symm))
  refine Eq.trans ?_ (gm_linComb L (fun _ : PUnit => 𝟙 S) (fun _ => (d : ℤ)) (𝟙 S) y J J' hJ hJ').symm
  rw [Fintype.prod_unique, zpow_natCast, Category.id_comp]

theorem exists_nsmul_eq_zero {S W : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (hS : Geo.Tor.IsNormalScheme S) (p : W ⟶ S)
    [UniversallyClosed p] [Surjective p] (c : Pic S) (h : pull p c = 0) : ∃ d : ℕ, 1 ≤ d ∧ d • c = 0 := by
  have := GlobalTheory.IsNormalScheme.of_pred hS
  have := Fintype.ofFinite (irreducibleComponents S)
  choose d hd H using fun C : irreducibleComponents S =>
    exists_nsmul_eq_zero_of_isIntegral (pullback.snd p (IsNormalScheme.component C).ι) (pull (IsNormalScheme.component C).ι c)
      (by rw [← pull_comp, ← pullback.condition, pull_comp, h, map_zero])
  refine ⟨∏ C, d C, Finset.prod_pos (s := Finset.univ) (f := d) fun C _ => hd C, ?_⟩
  obtain ⟨L, hL, e⟩ := cls_surj ((∏ C, d C) • c)
  rw [← e]
  refine (cls_eq_iff hL (LB.isLB_triv S)).2 (DisjointCoverLB.lbIso_of_disjoint_cover S _ IsNormalScheme.component
    (fun a b y ha hb => Subtype.ext (IsNormalScheme.eq_of_mem_irreducibleComponents a.2 b.2 ha hb))
    (fun y => ⟨⟨_, irreducibleComponent_mem_irreducibleComponents y⟩, mem_irreducibleComponent⟩) L _ hL (LB.isLB_triv S)
    fun C => (cls_eq_iff (pull_isLB hL _) (pull_isLB (LB.isLB_triv S) _)).1 ?_)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ C)
  rw [cls_pull hL, cls_pull (LB.isLB_triv S), e, map_nsmul, hk, mul_comm, mul_smul, H, smul_zero]
  exact (map_zero _).symm

theorem exists_common_cover {R : Type} [CommRing R] [IsDedekindDomain R] [CharZero R] {Z S S' U : Scheme.{0}} (z : Z ⟶ Sp R)
    (π : S ⟶ Z) (π' : S' ⟶ Z) [LocallyOfFiniteType (π ≫ z)] [QuasiSeparated π] [IsProper π'] [IsLocallyNoetherian S']
    (hS' : Geo.Tor.IsNormalScheme S') (a : U ⟶ S) (k : U ⟶ S') [IsOpenImmersion k] (w : a ≫ π = k ≫ π')
    (hd : Dense (a '' {x | ((a ≫ π ≫ z) x).asIdeal = ⊥}))
    {A : Over U} [GrpObj A] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ G'.left} (hφ : IsGrpPullback A G a φ) (hψ : IsGrpPullback A G' k ψ) :
    ∃ (W : Scheme.{0}) (p : W ⟶ S) (p' : W ⟶ S') (H : Over W) (_ : GrpObj H) (α : H.left ⟶ G.left) (β : H.left ⟶ G'.left),
      IsProper p ∧ Surjective p ∧ p ≫ π = p' ≫ π' ∧ IsGrpPullback H G p α ∧ IsGrpPullback H G' p' β := by
  let K := FractionRing R
  let b : Sp K ⟶ Sp R := spMap (algebraMap R K)
  have : IsPreimmersion b := IsPreimmersion.of_isLocalization (R := CommRingCat.of R) (S := K) (nonZeroDivisors R)
  have : Flat b := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R)))
  let T := pullback (a ≫ π ≫ z) b
  let t : T ⟶ U := pullback.fst _ _
  have := GlobalTheory.IsNormalScheme.of_pred hS'
  have : QuasiCompact k := inferInstance
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (t ≫ k)
  have : GlobalTheory.IsNormalScheme T := GlobalTheory.IsNormalScheme.of_isIso_stalkMap (t ≫ k)
  have : IsLocallyNoetherian T := AmpUniq.isLocallyNoetherian_of_isPreimmersion (t ≫ k)
  let f : T ⟶ pullback π π' := pullback.lift (t ≫ a) (t ≫ k) (by simp [w])
  have hf₁ : f ≫ pullback.fst π π' = t ≫ a := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd π π' = t ≫ k := pullback.lift_snd _ _ _
  have : IsPreimmersion (f ≫ pullback.snd π π') := hf₂ ▸ inferInstance
  have : IsPreimmersion f := AmpUniq.isPreimmersion_of_comp f (pullback.snd π π')
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  have : IsLocallyNoetherian (pullback π π') := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst π π')
  have : QuasiCompact (f ≫ pullback.snd π π') := hf₂ ▸ inferInstance
  have : QuasiCompact f := .of_comp f (pullback.snd π π')
  have : Flat (f ≫ pullback.fst π π' ≫ π ≫ z) := by
    rw [reassoc_of% hf₁, pullback.condition]; infer_instance
  have : IsFinite f.fromNormalization := AmpUniq.isFinite_fromNormalization_graph f (pullback.fst π π' ≫ π ≫ z)
  let u := f.toNormalization
  let p := f.fromNormalization ≫ pullback.fst π π'
  let p' := f.fromNormalization ≫ pullback.snd π π'
  have hu₁ : u ≫ p = t ≫ a := by simp [u, p, hf₁]
  have hu₂ : u ≫ p' = t ≫ k := by simp [u, p', hf₂]
  have : IsPreimmersion (u ≫ p') := hu₂ ▸ inferInstance
  have : IsPreimmersion u := AmpUniq.isPreimmersion_of_comp u p'
  have : Flat u := AmpUniq.flat_of_isPreimmersion u
  have hN := GlobalTheory.IsNormalScheme.pred f.normalization
  have : IsLocallyNoetherian f.normalization := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsDominant (u ≫ p) := by
    rw [hu₁]
    refine ⟨hd.mono ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have : x ∈ Set.range t := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨closedPoint K, PrimeSpectrum.ext ?_⟩
      refine Eq.trans ?_ hx.symm
      change Ideal.comap (algebraMap R K) (maximalIdeal K) = ⊥
      rw [maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]
    obtain ⟨y, rfl⟩ := this
    exact ⟨y, by simp⟩
  have : IsDominant p := .of_comp u p
  have lift : ∀ {Y : Scheme.{0}} {B : Over Y} [GrpObj B] (q : f.normalization ⟶ Y) {c : U ⟶ Y} {χ : A.left ⟶ B.left},
      IsGrpPullback A B c χ → u ≫ q = t ≫ c →
      ∃ χ', IsGrpPullback ((Over.pullback t).obj A) ((Over.pullback q).obj B) u χ' := by
    intro Y B _ q c χ h e
    have h' := ((isGrpPullback_pullback A t).comp h).congr e.symm rfl
    exact ⟨pullback.lift _ _ (h'.1.w.trans (Category.assoc _ _ _).symm), (isGrpPullback_pullback B q).cancel
      (h'.congr rfl (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)⟩
  obtain ⟨_, a₁⟩ := lift p hφ hu₁
  obtain ⟨_, a₂⟩ := lift p' hψ hu₂
  obtain ⟨e, _⟩ := HodgeGenDesc.exists_iso_of_extensions u hN (IsSemiAbelian.pullback p G hG)
    (IsSemiAbelian.pullback p' G' hG') a₁ a₂
  exact ⟨f.normalization, p, p', (Over.pullback p).obj G, inferInstance, _, _, inferInstance,
    surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range, by simp [p, p', pullback.condition],
    isGrpPullback_pullback G p,
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G' p')).congr (Category.id_comp _) rfl⟩

end GlobalTheory.HodgeMin

end
