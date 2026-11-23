import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open ReciprocityTheory.AnForm.R (ds_stalkId_eq_map)
open ReciprocityTheory.AnForm.R.FinalTheorems (stalkId)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open GlobalTheory.Adelic (cutIdeal)
open H0

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' T : Scheme.{0}} {φ : Y' ⟶ Y}

section Ideal

variable {L : LB Y} {L' : LB Y'} {ι : Type}

theorem secGer_chartSec (l : ChartPull L' L φ) (s : ι → L.Sec) (j : L'.ι) (z : Y') (hj : z ∈ L'.U j)
    (i : ι) : secGer (fun i => chartSec l (s i)) j z hj i =
      (φ.stalkMap z).hom (secGer s (l.idx j) (φ z) (l.le j hj) i) :=
  ger_appLE φ (l.le j) z hj _

theorem stalkId_cutIdeal_chartSec (hL : L.IsLB) (hL' : L'.IsLB) (l : ChartPull L' L φ)
    (s : ι → L.Sec) (z : Y') : stalkId (cutIdeal hL' fun i => chartSec l (s i)) z =
      (stalkId (cutIdeal hL s) (φ z)).map (φ.stalkMap z).hom := by
  obtain ⟨j, hj⟩ := exists_chart hL' z
  rw [stalkId_cutIdeal hL' _ j z hj, stalkId_cutIdeal hL s _ _ (l.le j hj), Ideal.map_span,
    ← Set.range_comp]
  exact congrArg (fun f => Ideal.span (Set.range f)) (funext (secGer_chartSec l s j z hj))

theorem stalkId_cutIdeal_secPull (hL : L.IsLB) (s : ι → L.Sec) (z : Y') :
    stalkId (cutIdeal (LB.isLB_pull hL φ) fun i => secPull (s i) φ) z =
      (stalkId (cutIdeal hL s) (φ z)).map (φ.stalkMap z).hom :=
  stalkId_cutIdeal_chartSec hL _ (GlobalTheory.chartPullPull L φ) s z

variable {I : Y.IdealSheafData} {I' : Y'.IdealSheafData}

theorem le_ker_iff_stalk (t : T ⟶ Y) :
    I ≤ t.ker ↔ ∀ z, stalkId I (t z) ≤ RingHom.ker (t.stalkMap z).hom := by
  refine ⟨fun h z => ?_, fun h => Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U a ha => ?_⟩
  · obtain ⟨W, hW, -⟩ := exists_affine (U := ⊤) (y := t z) trivial
    rw [ds_stalkId_eq_map I W _ hW, Ideal.map_le_iff_le_comap]
    intro a ha
    have h₀ : (t.app W.1).hom a = 0 := t.ideal_ker_le W (h W ha)
    exact (Scheme.Hom.germ_stalkMap_apply t _ z hW a).trans ((congrArg _ h₀).trans (map_zero _))
  · refine fun_ext_ger (U := t ⁻¹ᵁ U.1) fun z hz => ?_
    have := h z ((mem_ideal_iff_ger I U a).1 ha _ hz)
    exact (Scheme.Hom.germ_stalkMap_apply t _ z hz a).symm.trans (this.trans (map_zero _).symm)

variable (hI : ∀ z, stalkId I' z = (stalkId I (φ z)).map (φ.stalkMap z).hom)
include hI

theorem le_ker_iff_comp (t : T ⟶ Y') : I' ≤ t.ker ↔ I ≤ (t ≫ φ).ker := by
  rw [le_ker_iff_stalk, le_ker_iff_stalk]
  refine forall_congr' fun z => ?_
  rw [hI, Ideal.map_le_iff_le_comap, RingHom.comap_ker, Scheme.Hom.stalkMap_comp]
  rfl

theorem le_map_of_stalk : I ≤ I'.map φ := (le_ker_iff_comp hI _).1 I'.ker_subschemeι.ge

theorem eq_comap_of_stalk : I' = I.comap φ :=
  le_antisymm ((le_ker_iff_comp hI _).2 (by
      rw [Limits.pullback.condition]
      exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)))
    (Scheme.IdealSheafData.le_map_iff_comap_le.1 (le_map_of_stalk hI))

theorem isPullback_subscheme {ψ : I'.subscheme ⟶ I.subscheme}
    (hψ : ψ ≫ I.subschemeι = I'.subschemeι ≫ φ) : IsPullback I'.subschemeι ψ φ I.subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ hψ.symm (by
    rw [I.ker_subschemeι, I'.ker_subschemeι, eq_comap_of_stalk hI])

theorem mem_support_iff_of_stalk (z : Y') : z ∈ I'.support ↔ φ z ∈ I.support := by
  rw [eq_comap_of_stalk hI, Scheme.IdealSheafData.support_comap]
  rfl

theorem SuppIn.preimage {O : Y.Opens} (hO : SuppIn O I) : SuppIn (φ ⁻¹ᵁ O) I' :=
  fun z hz => hO _ ((mem_support_iff_of_stalk hI z).1 hz)

end Ideal

section Order

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} {B : LB Y} {B' : LB Y'} {O : Y.Opens}
  {I : Y.IdealSheafData} {I' : Y'.IdealSheafData} {n : ℕ}
  (hI : ∀ z, stalkId I' z = (stalkId I (φ z)).map (φ.stalkMap z).hom)

theorem comap_map_stalkMap [Flat φ] (z : Y') (J : Ideal (Y.presheaf.stalk (φ z))) :
    (J.map (φ.stalkMap z).hom).comap (φ.stalkMap z).hom = J := by
  let _ := (φ.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (φ z)) (Y'.presheaf.stalk z) := Flat.stalkMap φ z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (φ z)) (Y'.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap z).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (φ z)) (Y'.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Ideal.comap_map_eq_self_of_faithfullyFlat J

include hI in

theorem vanishesTo_pullChart_iff_of_flat [Flat φ] [Surjective φ] (hB' : B'.IsLB)
    (a : ChartPull B' B φ) (w : φ ≫ p = p' ≫ spMap σ) (f : H0 p B O) :
    VanishesTo I' n (pullChart a w le_rfl f) ↔ VanishesTo I n f := by
  refine ⟨fun h => vanishesTo_of_exists fun y _ hy => ?_,
    fun h => h.pullChart a w le_rfl fun z => (hI z).ge⟩
  obtain ⟨z, rfl⟩ := φ.surjective y
  obtain ⟨i, hi⟩ := exists_chart hB' z
  have := vanishesTo_iff_forall.1 h z (show z ∈ φ ⁻¹ᵁ O from hy) i hi
  rw [germ_pullChart, hI, ← Ideal.map_pow, ← Ideal.mem_comap, comap_map_stalkMap] at this
  exact ⟨_, _, this⟩

theorem flat_of_isPullback {E E' : Type} [Field E] [Field E'] {σ : E →+* E'} {p : Y ⟶ Sp E}
    {p' : Y' ⟶ Sp E'} (H : IsPullback φ p' p (spMap σ)) : Flat φ :=
  MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance

theorem surjective_of_isPullback {E E' : Type} [Field E] [Field E'] {σ : E →+* E'} {p : Y ⟶ Sp E}
    {p' : Y' ⟶ Sp E'} (H : IsPullback φ p' p (spMap σ)) : Surjective φ :=
  MorphismProperty.of_isPullback (P := @Surjective) H.flip
    ⟨fun x => ⟨IsLocalRing.closedPoint E', Subsingleton.elim (α := PrimeSpectrum E) _ _⟩⟩

theorem mem_of_forall_ger {W : Y.Opens} (hW : IsAffineOpen W) (J : Ideal Γ(Y, W)) (x : Γ(Y, W))
    (h : ∀ y hy, ger y hy x ∈ J.map (ger y hy)) : x ∈ J := by
  have e : Ideal.span {r | r * x ∈ J} = ⊤ := by
    rw [← hW.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun r => Y.basicOpen_le _) fun y hy => ?_
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : W)
    have := hW.isLocalization_stalk ⟨y, hy⟩
    obtain ⟨r, hr, hx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y) J x).1 (h y hy)
    exact Opens.mem_iSup.2 ⟨⟨r, hx⟩, (Y.mem_basicOpen r y hy).2
      (IsLocalization.map_units (Y.presheaf.stalk y) (⟨r, hr⟩ : (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl))⟩
  have e' : Ideal.span {r | r * x ∈ J} ≤ J.colon {x} :=
    Ideal.span_le.2 fun r hr => Submodule.mem_colon_singleton.2 hr
  simpa using Submodule.mem_colon_singleton.1 (e' (e.ge (Submodule.mem_top (x := 1))))

theorem sum_mem_of_isPushout [Algebra k k'] {A A' : Type} [CommRing A] [CommRing A'] (α : k →+* A)
    (β : k' →+* A') (ρ : A →+* A')
    (H : IsPushout (CommRingCat.ofHom α) (CommRingCat.ofHom (algebraMap k k')) (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom β)) (J : Ideal A) (μ : k' →ₗ[k] k) {τ : Type*} (S : Finset τ) (c : τ → k')
    (x : τ → A) (h : ∑ t ∈ S, β (c t) * ρ (x t) ∈ J.map ρ) : ∑ t ∈ S, α (μ (c t)) * x t ∈ J := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A A' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' A' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w)
  have P : Algebra.IsPushout k A k' A' := CommRingCat.isPushout_iff_isPushout.1 H
  let lam : A' →ₗ[A] A := P.out.lift (Algebra.linearMap k A ∘ₗ μ)
  have hl (b : k') (a : A) : lam (β b * ρ a) = α (μ b) * a := by
    rw [mul_comm, mul_comm _ a]
    exact (lam.map_smul a _).trans (congrArg (a * ·) (P.out.lift_eq _ b))
  have hJ (y : A') (hy : y ∈ J.map ρ) : lam y ∈ J := by
    have hy' : y ∈ J • (⊤ : Submodule A A') := by
      rw [Ideal.smul_top_eq_map]
      exact hy
    exact Submodule.smul_induction_on hy' (fun r hr y _ => by
      rw [map_smul]; exact J.mul_mem_right _ hr) fun y y' h h' => by
        rw [map_add]; exact add_mem h h'
  simpa only [map_sum, hl] using hJ _ h

include hI in

theorem vanishesTo_sum_of_baseChange [Algebra k k'] (H : IsPullback φ p' p (spMap (algebraMap k k')))
    (hB' : B'.IsLB) (a : ChartPull B' B φ) (μ : k' →ₗ[k] k) {τ : Type*} (S : Finset τ) (c : τ → k')
    (f : τ → H0 p B O) (h : VanishesTo I' n (∑ t ∈ S, c t • pullChart a H.w le_rfl (f t))) :
    VanishesTo I n (∑ t ∈ S, μ (c t) • f t) := by
  refine vanishesTo_iff_affine.2 fun W i hW => ?_
  have hW' : IsAffineOpen (φ ⁻¹ᵁ W.1 ⊓ p' ⁻¹ᵁ ⊤) := by
    rw [show φ ⁻¹ᵁ W.1 ⊓ p' ⁻¹ᵁ ⊤ = φ ⁻¹ᵁ W.1 from inf_top_eq _]
    exact TopForm.isAffineOpen_preimage_of_isPullback H W.2
  have key := sum_mem_of_isPushout _ _ (φ.appLE W.1 _ inf_le_left).hom
    (isPushout_sections p p' φ H W.1 W.2) (I.ideal W ^ n) μ S c
    (fun t => resG Y hW ((f t).loc i)) (mem_of_forall_ger hW' _ _ fun z hz => by
      obtain ⟨j, hj⟩ := exists_chart hB' z
      have h₁ := vanishesTo_iff_forall.1 h z (show z ∈ φ ⁻¹ᵁ O from (hW hz.1).1) j hj
      have e : (ger z hz).comp (φ.appLE W.1 _ inf_le_left).hom =
          (φ.stalkMap z).hom.comp (ger (φ z) hz.1) := RingHom.ext (ger_appLE φ _ z hz)
      rw [Ideal.map_map, e, ← Ideal.map_map, Ideal.map_pow, ← ds_stalkId_eq_map I W _ hz.1,
        Ideal.map_pow, ← hI]
      convert Ideal.mul_mem_left _ ((φ.stalkMap z).hom (tr B (φ z) i (a.idx j)).val) h₁ using 1
      simp only [map_sum, map_mul, germ_smul, germ_pullChart, ger_algX, ger_appLE, ger_resG,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [mul_left_comm, ← map_mul]
      exact congrArg (fun x => _ * (φ.stalkMap z).hom x) ((ger_resG hW _ hz.1 _).trans
        (germ_change i _ _ (hW hz.1).1 (hW hz.1).2 (a.le j hj) (f t))))
  convert key using 1
  refine fun_ext_ger fun y hy => ?_
  simp only [map_sum, map_mul, ger_algX, ger_resG]
  change germ i y (hW hy).1 (hW hy).2 _ = _
  simp only [map_sum, germ_smul]
  rfl

include hI in

theorem Fil_span_pullChart_of_free [Algebra k k'] [Module.Free k k']
    (H : IsPullback φ p' p (spMap (algebraMap k k'))) (hB' : B'.IsLB) (a : ChartPull B' B φ)
    (V : Submodule k (H0 p B O)) :
    Fil I' n (Submodule.span k' (pullChart (O := O) a H.w le_rfl '' V)) =
      Submodule.span k' (pullChart (O := O) a H.w le_rfl '' Fil I n V) := by
  classical
  refine le_antisymm (fun g hg => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨S, hS, c, rfl⟩ := (Submodule.mem_span_image_iff_exists_fun k').1 hg.1
    let b := Module.Free.chooseBasis k k'
    let N := (Finset.univ : Finset S).biUnion fun t => (b.repr (c t)).support
    have hc (t : S) : c t = ∑ j ∈ N, b j * algebraMap k k' (b.coord j (c t)) := by
      conv_lhs => rw [← b.linearCombination_repr (c t), Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem
          (fun t => (b.repr (c t)).support) (Finset.mem_univ t)) _ (by simp)]
      exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]; rfl
    have e : ∑ t : S, c t • pullChart a H.w le_rfl t.1 =
        ∑ j ∈ N, b j • pullChart a H.w le_rfl (∑ t : S, b.coord j (c t) • t.1) := by
      simp only [map_sum, map_smulₛₗ, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => by rw [← Finset.sum_smul, ← hc]
    rw [e]
    refine sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨?_, ?_⟩, rfl⟩)
    · exact sum_mem fun t _ => V.smul_mem _ (hS t.2)
    · exact vanishesTo_sum_of_baseChange hI H hB' a (b.coord j) _ c (fun t => t.1) hg.2
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨Submodule.subset_span ⟨f, hf.1, rfl⟩,
      VanishesTo.pullChart hf.2 a H.w le_rfl fun z => (hI z).ge⟩

end Order

section On

variable {S S' : Scheme.{0}} {u : S ⟶ Y} {u' : S' ⟶ Y'} {ψ : S' ⟶ S}

theorem stalkMap_square (hψ : ψ ≫ u = u' ≫ φ) (z : S') {U : Y.Opens} (h : u (ψ z) ∈ U)
    (h' : φ (u' z) ∈ U) (x : Γ(Y, U)) :
    (ψ.stalkMap z).hom ((u.stalkMap (ψ z)).hom (ger _ h x)) =
      (u'.stalkMap z).hom ((φ.stalkMap (u' z)).hom (ger _ h' x)) := by
  have key {r r' : S' ⟶ Y} (e : r = r') (h : r z ∈ U) (h' : r' z ∈ U) :
      (r.stalkMap z).hom (ger _ h x) = (r'.stalkMap z).hom (ger _ h' x) := by
    subst e
    rfl
  have := key hψ h h'
  rwa [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at this

theorem pt_square (hψ : ψ ≫ u = u' ≫ φ) (z : S') : u (ψ z) = φ (u' z) :=
  congrArg (fun r : S' ⟶ Y => r z) hψ

theorem exists_stalkHom (hψ : ψ ≫ u = u' ≫ φ) (z : S') :
    ∃ θ : Y.presheaf.stalk (u (ψ z)) →+* Y'.presheaf.stalk (u' z),
      (∀ (U : Y.Opens) h h' (x : Γ(Y, U)),
        θ (ger _ h x) = (φ.stalkMap (u' z)).hom (ger _ h' x)) ∧
      ∀ x, (u'.stalkMap z).hom (θ x) = (ψ.stalkMap z).hom ((u.stalkMap (ψ z)).hom x) := by
  have key (y : Y) (e : y = φ (u' z)) : ∃ θ : Y.presheaf.stalk y →+* Y'.presheaf.stalk (u' z),
      ∀ (U : Y.Opens) h h' (x : Γ(Y, U)),
        θ (ger _ h x) = (φ.stalkMap (u' z)).hom (ger _ h' x) := by
    subst e
    exact ⟨_, fun _ _ _ _ => rfl⟩
  obtain ⟨θ, hθ⟩ := key _ (pt_square hψ z)
  refine ⟨θ, hθ, fun x => ?_⟩
  obtain ⟨U, hU, x, rfl⟩ := Y.presheaf.germ_exist x
  exact (congrArg _ (hθ U hU (pt_square hψ z ▸ hU) x)).trans (stalkMap_square hψ z hU _ x).symm

variable {B : LB Y} {B' : LB Y'}

def chartPullOn (a : ChartPull B' B φ) (hψ : ψ ≫ u = u' ≫ φ) :
    ChartPull (B'.pull u') (B.pull u) ψ where
  idx J _ := a.idx (J PUnit.unit)
  le J z hz := mem_pull.2 ((pt_square hψ z).symm ▸ a.le _ (mem_pull.1 hz))
  g z J J' hJ hJ' := by
    have h := memInf (a.le _ (mem_pull.1 hJ)) (a.le _ (mem_pull.1 hJ'))
    have h' : u (ψ z) ∈ B.U (a.idx (J PUnit.unit)) ⊓ B.U (a.idx (J' PUnit.unit)) :=
      (pt_square hψ z).symm ▸ h
    refine ((tr_pull B' u' z hJ hJ').trans ?_).trans (gm_pull_g B u ψ z (fun _ => _) (fun _ => _)
      (mem_pull.2 h'.1) (mem_pull.2 h'.2)).symm
    rw [tr_chartPull a _ (mem_pull.1 hJ) (mem_pull.1 hJ'), hψ]
    refine Units.ext (Eq.trans ?_ (gm_val (u' ≫ φ) z _ h _).symm)
    refine (congrArg (fun x => (u'.stalkMap z).hom ((φ.stalkMap (u' z)).hom x))
      (val_tr B _ h)).trans ?_
    refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply (u' ≫ φ) _ z h _)
    rw [Scheme.Hom.stalkMap_comp]
    rfl

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} {O : Y.Opens} {W : Y'.Opens}
  {I : Y.IdealSheafData} {I' : Y'.IdealSheafData} {ψ : I'.subscheme ⟶ I.subscheme}

def pullOn (a : ChartPull B' B φ) (w : φ ≫ p = p' ≫ spMap σ)
    (hψ : ψ ≫ I.subschemeι = I'.subschemeι ≫ φ) : sectionsOnClosedSubscheme p B I →ₛₗ[σ] sectionsOnClosedSubscheme p' B' I' :=
  pullChart (chartPullOn a hψ) (by rw [← Category.assoc, hψ, Category.assoc, w, Category.assoc])
    le_top

theorem germ_pullOn (a : ChartPull B' B φ) (w : φ ≫ p = p' ≫ spMap σ)
    (hψ : ψ ≫ I.subschemeι = I'.subschemeι ≫ φ) (g : sectionsOnClosedSubscheme p B I) (j : (B'.pull I'.subschemeι).ι)
    (z : I'.subscheme) (hj : z ∈ (B'.pull I'.subschemeι).U j) :
    germ j z (Opens.mem_top z) hj (pullOn a w hψ g) = (ψ.stalkMap z).hom
      (germ (fun _ => a.idx (j PUnit.unit)) (ψ z) (Opens.mem_top _)
        ((chartPullOn a hψ).le j hj) g) :=
  germ_pullChart _ _ _ g j z _ hj

theorem resTo_pullChart (a : ChartPull B' B φ) (w : φ ≫ p = p' ≫ spMap σ)
    (hψ : ψ ≫ I.subschemeι = I'.subschemeι ≫ φ) (h : W ≤ φ ⁻¹ᵁ O) (hO : SuppIn O I)
    (hW : SuppIn W I') (f : H0 p B O) :
    resTo hW (pullChart a w h f) = pullOn a w hψ (resTo hO f) :=
  LB.sec_ext fun j => fun_ext_ger fun z hz => by
    change germ j z (Opens.mem_top z) hz.2 _ = germ j z (Opens.mem_top z) hz.2 _
    rw [germ_resTo, germ_pullChart, germ_pullOn]
    refine Eq.trans ?_ (congrArg (ψ.stalkMap z).hom (germ_resTo hO (fun _ => a.idx (j PUnit.unit))
      (ψ z) ((chartPullOn a hψ).le j hz.2) f)).symm
    exact (stalkMap_square hψ z _ _ (f.loc (a.idx (j PUnit.unit)))).symm

end On

theorem LeadAt.map {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    {ι : Type} [Finite ι] {π : R →+* S} {π' : R' →+* S'} {x : ι → R} {a : ℕ} {f : R}
    {γ : MonoDeg ι a → S} (h : LeadAt π x f γ) (θ : R →+* R') (η : S →+* S')
    (e : ∀ r, π' (θ r) = η (π r)) : LeadAt π' (fun i => θ (x i)) (θ f) fun α => η (γ α) := by
  obtain ⟨m, hm, hf⟩ := h
  refine ⟨fun α => θ (m α), fun α => by rw [e, hm], ?_⟩
  have := Ideal.mem_map_of_mem θ hf
  rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at this
  simp only [map_sub, map_sum, map_mul, map_monoVal] at this
  exact this

section Lead

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} {L M : LB Y} {L' M' : LB Y'}
  {hL : L.IsLB} {hL' : L'.IsLB} {ι : Type} [Finite ι] {s : ι → L.Sec} {O : Y.Opens} {W : Y'.Opens}

theorem HasLead.pullChart (m : ChartPull M' M φ) (l : ChartPull L' L φ) (w : φ ≫ p = p' ≫ spMap σ)
    {ψ : (cutIdeal hL' fun i => chartSec l (s i)).subscheme ⟶ (cutIdeal hL s).subscheme}
    (hψ : ψ ≫ (cutIdeal hL s).subschemeι = (cutIdeal hL' fun i => chartSec l (s i)).subschemeι ≫ φ)
    (hW : W ≤ φ ⁻¹ᵁ O) {hO : SuppIn O (cutIdeal hL s)}
    (hO' : SuppIn W (cutIdeal hL' fun i => chartSec l (s i))) {n d : ℤ} {a : ℕ} {h : n + a = d}
    {f : H0 p (tw M L d) O} {c : MonoDeg ι a → sectionsOnClosedSubscheme p (tw M L n) (cutIdeal hL s)}
    (e : HasLead hL s hO h f c) :
    HasLead hL' _ hO' h (pullChart (chartPullTwist m l d) w hW f)
      fun α => pullOn (chartPullTwist m l n) w hψ (c α) := fun z i j hi hj => by
  obtain ⟨θ, hθ, hθ'⟩ := exists_stalkHom hψ z
  have := (e (ψ z) (m.idx i) (l.idx j) ((pt_square hψ z).symm ▸ m.le i hi)
    ((pt_square hψ z).symm ▸ l.le j hj)).map θ (ψ.stalkMap z).hom hθ'
  convert this using 1
  · exact funext fun t => (secGer_chartSec l s j _ hj t).trans (hθ _ _ _ _).symm
  · exact (germ_pullChart _ _ _ _ _ _ _ _).trans (hθ _ _ _ _).symm
  · exact funext fun α => germ_pullOn _ _ _ _ _ _ _

end Lead

section Symbol

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} (H : IsPullback φ p' p (spMap σ))

include H in

theorem isPullback_subscheme_base {I : Y.IdealSheafData} {I' : Y'.IdealSheafData}
    (hI : ∀ z, stalkId I' z = (stalkId I (φ z)).map (φ.stalkMap z).hom)
    {ψ : I'.subscheme ⟶ I.subscheme} (hψ : ψ ≫ I.subschemeι = I'.subschemeι ≫ φ) :
    IsPullback ψ (I'.subschemeι ≫ p') (I.subschemeι ≫ p) (spMap σ) :=
  (isPullback_subscheme hI hψ).flip.paste_vert H

include H in

theorem etale_baseChange {I : Y.IdealSheafData} {I' : Y'.IdealSheafData}
    (hI : ∀ z, stalkId I' z = (stalkId I (φ z)).map (φ.stalkMap z).hom)
    (hS : Etale (I.subschemeι ≫ p)) : Etale (I'.subschemeι ≫ p') :=
  MorphismProperty.of_isPullback (P := @Etale)
    (isPullback_subscheme_base H hI (I'.subschemeMap_subschemeι I φ (le_map_of_stalk hI))) hS

include H in

theorem smooth_baseChange (D : ℕ) [h : SmoothOfRelativeDimension D p] :
    SmoothOfRelativeDimension D p' :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} D
  MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D) H h

variable {D : ℕ} [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] (K : CanonLB p D)
  {L A B : LB Y} {L' A' B' : LB Y'} (l : ChartPull L' L φ) (a : ChartPull A' A φ)
  (b : ChartPull B' B φ) (s : Fin D → L.Sec)

abbrev chartPullCanon : ChartPull (K.baseChange H).bundle K.bundle φ :=
  GlobalTheory.chartPullPull K.bundle φ

theorem jacFun_baseChange (i : (K.baseChange H).bundle.ι) (j : L'.ι) :
    (K.baseChange H).jacFun (fun t => chartSec l (s t)) i j =
      (φ.appLE (K.bundle.U (i PUnit.unit) ⊓ L.U (l.idx j)) _
        (inf_le_inf (pull_U_le φ i) (l.le j))).hom (K.jacFun s (i PUnit.unit) (l.idx j)) := by
  refine Eq.trans (congrArg ((K.baseChange H).jacobian i inf_le_left) (funext fun t => ?_))
    (K.jacobian_baseChange H i inf_le_left inf_le_left _ _)
  exact (resG_appLE φ _ _ _).trans (LB.appLE_resG φ _ _ _).symm

abbrev pullQuotSec (e : (LB.div A (tw B L D)).Sec) : (LB.div A' (tw B' L' D)).Sec :=
  chartSec (chartPullQuot a (chartPullTwist b l D)) e

variable (hL : L.IsLB) (hA : A.IsLB) (hB : B.IsLB) (hL' : L'.IsLB) (hA' : A'.IsLB) (hB' : B'.IsLB)
  (e : (LB.div A (tw B L D)).Sec)

include hA' hB' in

theorem suppIn_pullQuotSec (he : SuppIn (nonzeroLocus e) (cutIdeal hL s)) :
    SuppIn (nonzeroLocus (pullQuotSec l a b e)) (cutIdeal hL' fun t => chartSec l (s t)) := by
  rw [nonzeroLocus_chartSec _ e fun y _ _ =>
    exists_chart (LB.isLB_div hA' (isLB_tw hB' hL' D)) y]
  exact he.preimage (stalkId_cutIdeal_chartSec hL hL' l s)

variable (hS : Etale ((cutIdeal hL s).subschemeι ≫ p))
  (hS' : Etale ((cutIdeal hL' fun t => chartSec l (s t)).subschemeι ≫ p'))
  (he : SuppIn (nonzeroLocus e) (cutIdeal hL s))
  (he' : SuppIn (nonzeroLocus (pullQuotSec l a b e)) (cutIdeal hL' fun t => chartSec l (s t)))
  {ψ : (cutIdeal hL' fun t => chartSec l (s t)).subscheme ⟶ (cutIdeal hL s).subscheme}
  (hψ : ψ ≫ (cutIdeal hL s).subschemeι = (cutIdeal hL' fun t => chartSec l (s t)).subschemeι ≫ φ)

theorem mulEDs_pullOn (n : ℤ) (g : sectionsOnClosedSubscheme p (tw B L n) (cutIdeal hL s)) :
    mulEDs (K.baseChange H) hL' hA' hB' _ hS' n _ he' (pullOn (chartPullTwist b l n) H.w hψ g) =
      pullOn (chartPullTwist (chartPullTens (chartPullCanon H K) a) l n) H.w hψ
        (mulEDs K hL hA hB s hS n e he g) :=
  ext_germ fun z _ => by
    obtain ⟨⟨i, c, d, j⟩, ⟨hc, -⟩, h', -⟩ := (quotChart (K.baseChange H).isLB hA' hB' hL' (n := n)
      (d := 0) rfl).cover ((cutIdeal hL' fun t => chartSec l (s t)).subschemeι z)
    obtain ⟨⟨hi, hd⟩, hj⟩ := mem_tw_U.1 h'
    have q := pt_square hψ z
    refine ⟨_, _, (germ_mulEDs _ hL' hA' hB' _ hS' _ he' _ z i c d j hi hc hd hj).trans ?_⟩
    refine Eq.trans ?_ (germ_pullOn _ _ _ _ _ _ _).symm
    refine Eq.trans ?_ (congrArg (ψ.stalkMap z).hom (germ_mulEDs K hL hA hB s hS e he g (ψ z)
      (i PUnit.unit) (a.idx c) (b.idx d) (l.idx j) (q.symm ▸ pull_U_le φ i hi) (q.symm ▸ a.le c hc)
      (q.symm ▸ b.le d hd) (q.symm ▸ l.le j hj))).symm
    simp only [map_mul]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) (germ_pullOn _ _ _ _ _ _ _)
    · exact (congrArg _ (ger_appLE φ _ _ _ _)).trans (stalkMap_square hψ z _ _ _).symm
    · rw [jacFun_baseChange]
      exact (congrArg _ (ger_appLE φ _ _ _ _)).trans (stalkMap_square hψ z _ _ _).symm

variable {O : Y.Opens} {W : Y'.Opens} (hW : W ≤ φ ⁻¹ᵁ O) (hO : SuppIn O (cutIdeal hL s))
  (hO' : SuppIn W (cutIdeal hL' fun t => chartSec l (s t)))

theorem Res_pullChart (n : ℤ) (m : H0 p (tw (tens K.bundle A) L n) O) :
    Res (K.baseChange H) hL' hA' hB' _ hS' n _ he' hO'
        (pullChart (chartPullTwist (chartPullTens (chartPullCanon H K) a) l n) H.w hW m) =
      pullOn (chartPullTwist b l n) H.w hψ (Res K hL hA hB s hS n e he hO m) := by
  rw [Res_eq_iff, mulEDs_pullOn H K l a b s hL hA hB hL' hA' hB' e hS hS' he he' hψ, mulEDs_Res,
    resTo_pullChart _ _ hψ hW hO]

theorem sym_pullChart {n d : ℤ} {r : ℕ} (h : n + r = d)
    {V : Submodule k (H0 p (tw (tens K.bundle A) L d) O)}
    {V' : Submodule k' (H0 p' (tw (tens (K.baseChange H).bundle A') L' d) W)}
    (f : Fil (cutIdeal hL s) r V) (f' : Fil (cutIdeal hL' fun t => chartSec l (s t)) r V')
    (hf : f'.1 = pullChart (chartPullTwist (chartPullTens (chartPullCanon H K) a) l d) H.w hW f.1) :
    sym (K.baseChange H) hL' hA' hB' _ hS' _ he' hO' h V' f' =
      fun α => pullOn (chartPullTwist b l n) H.w hψ (sym K hL hA hB s hS e he hO h V f α) := by
  rw [sym_eq_iff, HasSymbol, hf]
  simp only [mulEDs_pullOn H K l a b s hL hA hB hL' hA' hB' e hS hS' he he' hψ]
  exact HasLead.pullChart _ l H.w hψ hW hO' ((sym_eq_iff K hL hA hB s hS e he hO h f _).1 rfl)

end Symbol

section Field

variable {E E' : Type} [Field E] [Field E'] {σ : E →+* E'} {p : Y ⟶ Sp E} {p' : Y' ⟶ Sp E'}
  (H : IsPullback φ p' p (spMap σ)) {L : LB Y} (hL : L.IsLB)

variable (φ) in

abbrev cutIdealPull {ι : Type} (s : ι → L.Sec) : Y'.IdealSheafData :=
  cutIdeal (LB.isLB_pull hL φ) fun i => secPull (s i) φ

variable (φ) in

def cutMap {ι : Type} (s : ι → L.Sec) :
    (cutIdealPull φ hL s).subscheme ⟶ (cutIdeal hL s).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ φ (le_map_of_stalk (stalkId_cutIdeal_secPull hL s))

variable (φ) in

theorem cutMap_ι {ι : Type} (s : ι → L.Sec) :
    cutMap φ hL s ≫ (cutIdeal hL s).subschemeι = (cutIdealPull φ hL s).subschemeι ≫ φ :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

section Order

variable {ι : Type} (s : ι → L.Sec) {B : LB Y} {B' : LB Y'} {O : Y.Opens} {n : ℕ}

theorem vanishesTo_baseChange_iff (hB' : B'.IsLB) (a : ChartPull B' B φ) (f : H0 p B O) :
    VanishesTo (cutIdealPull φ hL s) n (pullChart a H.w le_rfl f) ↔
      VanishesTo (cutIdeal hL s) n f :=
  have := flat_of_isPullback H
  have := surjective_of_isPullback H
  vanishesTo_pullChart_iff_of_flat (stalkId_cutIdeal_secPull hL s) hB' a H.w f

theorem Fil_baseChange (hB' : B'.IsLB) (a : ChartPull B' B φ) (V : Submodule E (H0 p B O)) :
    Fil (cutIdealPull φ hL s) n (Submodule.span E' (pullChart (O := O) a H.w le_rfl '' V)) =
      Submodule.span E' (pullChart (O := O) a H.w le_rfl '' Fil (cutIdeal hL s) n V) :=
  letI := σ.toAlgebra
  Fil_span_pullChart_of_free (stalkId_cutIdeal_secPull hL s) H hB' a V

theorem pullChart_mem_Fil (a : ChartPull B' B φ) {V : Submodule E (H0 p B O)}
    (f : Fil (cutIdeal hL s) n V) : pullChart a H.w le_rfl f.1 ∈
      Fil (cutIdealPull φ hL s) n (Submodule.span E' (pullChart (O := O) a H.w le_rfl '' V)) :=
  ⟨Submodule.subset_span ⟨f.1, f.2.1, rfl⟩,
    VanishesTo.pullChart f.2.2 a H.w le_rfl fun z => (stalkId_cutIdeal_secPull hL s z).ge⟩

end Order

variable {D : ℕ} [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] (K : CanonLB p D)
  {A B : LB Y} {A' B' : LB Y'} (hA : A.IsLB) (hB : B.IsLB) (hA' : A'.IsLB) (hB' : B'.IsLB)
  (a : ChartPull A' A φ) (b : ChartPull B' B φ) (s : Fin D → L.Sec)
  (hS : Etale ((cutIdeal hL s).subschemeι ≫ p)) (e : (LB.div A (tw B L D)).Sec)
  (he : SuppIn (nonzeroLocus e) (cutIdeal hL s)) {O : Y.Opens} (hO : SuppIn O (cutIdeal hL s))

abbrev pullAdj (n : ℤ) : H0 p (tw (tens K.bundle A) L n) O →ₛₗ[σ]
    H0 p' (tw (tens (K.baseChange H).bundle A') (L.pull φ) n) (φ ⁻¹ᵁ O) :=
  pullChart (chartPullTwist (chartPullTens (chartPullCanon H K) a) (GlobalTheory.chartPullPull L φ) n) H.w
    le_rfl

abbrev pullCut {ι : Type} (s : ι → L.Sec) (n : ℤ) : sectionsOnClosedSubscheme p (tw B L n) (cutIdeal hL s) →ₛₗ[σ]
    sectionsOnClosedSubscheme p' (tw B' (L.pull φ) n) (cutIdealPull φ hL s) :=
  pullOn (chartPullTwist b (GlobalTheory.chartPullPull L φ) n) H.w (cutMap_ι φ hL s)

theorem Res_baseChange (n : ℤ) (m : H0 p (tw (tens K.bundle A) L n) O) :
    Res (K.baseChange H) (LB.isLB_pull hL φ) hA' hB' (fun i => secPull (s i) φ)
        (etale_baseChange H (stalkId_cutIdeal_secPull hL s) hS) n
        (pullQuotSec (GlobalTheory.chartPullPull L φ) a b e)
        (suppIn_pullQuotSec _ a b s hL _ hA' hB' e he)
        (hO.preimage (stalkId_cutIdeal_secPull hL s)) (pullAdj H K a n m) =
      pullCut H hL b s n (Res K hL hA hB s hS n e he hO m) :=
  Res_pullChart H K _ a b s hL hA hB _ hA' hB' e hS _ he _ (cutMap_ι φ hL s) le_rfl hO _ n m

theorem sym_baseChange {n d : ℤ} {r : ℕ} (h : n + r = d)
    (V : Submodule E (H0 p (tw (tens K.bundle A) L d) O)) (f : Fil (cutIdeal hL s) r V) :
    sym (K.baseChange H) (LB.isLB_pull hL φ) hA' hB' (fun i => secPull (s i) φ)
        (etale_baseChange H (stalkId_cutIdeal_secPull hL s) hS)
        (pullQuotSec (GlobalTheory.chartPullPull L φ) a b e)
        (suppIn_pullQuotSec _ a b s hL _ hA' hB' e he)
        (hO.preimage (stalkId_cutIdeal_secPull hL s)) h
        (Submodule.span E' (pullAdj H K a d '' V)) ⟨pullAdj H K a d f.1, pullChart_mem_Fil H hL s _ f⟩ =
      fun α => pullCut H hL b s n (sym K hL hA hB s hS e he hO h V f α) :=
  sym_pullChart H K _ a b s hL hA hB _ hA' hB' e hS _ he _ (cutMap_ι φ hL s) le_rfl hO _ h f _ rfl

end Field

theorem vanishing_baseChange {E E' : Type} [Field E] [Field E'] {σ : E →+* E'} {p : Y ⟶ Sp E}
    {p' : Y' ⟶ Sp E'} (H : IsPullback φ p' p (spMap σ)) {L : LB Y} (hL : L.IsLB) :
    (∀ {ι : Type} (s : ι → L.Sec),
      (∀ z, stalkId (cutIdealPull φ hL s) z =
        (stalkId (cutIdeal hL s) (φ z)).map (φ.stalkMap z).hom) ∧
      ∀ {B : LB Y} {B' : LB Y'}, B'.IsLB → ∀ (a : ChartPull B' B φ) (O : Y.Opens) (n : ℕ),
        (∀ f : H0 p B O, VanishesTo (cutIdealPull φ hL s) n (pullChart a H.w le_rfl f) ↔
          VanishesTo (cutIdeal hL s) n f) ∧
        ∀ V : Submodule E (H0 p B O),
          Fil (cutIdealPull φ hL s) n (Submodule.span E' (pullChart (O := O) a H.w le_rfl '' V)) =
            Submodule.span E' (pullChart (O := O) a H.w le_rfl '' Fil (cutIdeal hL s) n V)) ∧
    ∀ {D : ℕ} [SmoothOfRelativeDimension D p] (K : CanonLB p D) {A B : LB Y} {A' B' : LB Y'}
      (hA : A.IsLB) (hB : B.IsLB) (hA' : A'.IsLB) (hB' : B'.IsLB) (a : ChartPull A' A φ)
      (b : ChartPull B' B φ) (s : Fin D → L.Sec) (hS : Etale ((cutIdeal hL s).subschemeι ≫ p))
      (e : (LB.div A (tw B L D)).Sec) (he : SuppIn (nonzeroLocus e) (cutIdeal hL s)) {O : Y.Opens}
      (hO : SuppIn O (cutIdeal hL s)),
      haveI := smooth_baseChange H D
      (∀ (n : ℤ) (m : H0 p (tw (tens K.bundle A) L n) O),
        Res (K.baseChange H) (LB.isLB_pull hL φ) hA' hB' (fun i => secPull (s i) φ)
            (etale_baseChange H (stalkId_cutIdeal_secPull hL s) hS) n
            (pullQuotSec (GlobalTheory.chartPullPull L φ) a b e)
            (suppIn_pullQuotSec _ a b s hL _ hA' hB' e he)
            (hO.preimage (stalkId_cutIdeal_secPull hL s)) (pullAdj H K a n m) =
          pullCut H hL b s n (Res K hL hA hB s hS n e he hO m)) ∧
      ∀ {n d : ℤ} {r : ℕ} (h : n + r = d) (V : Submodule E (H0 p (tw (tens K.bundle A) L d) O))
        (f : Fil (cutIdeal hL s) r V),
        sym (K.baseChange H) (LB.isLB_pull hL φ) hA' hB' (fun i => secPull (s i) φ)
            (etale_baseChange H (stalkId_cutIdeal_secPull hL s) hS)
            (pullQuotSec (GlobalTheory.chartPullPull L φ) a b e)
            (suppIn_pullQuotSec _ a b s hL _ hA' hB' e he)
            (hO.preimage (stalkId_cutIdeal_secPull hL s)) h
            (Submodule.span E' (pullAdj H K a d '' V))
            ⟨pullAdj H K a d f.1, pullChart_mem_Fil H hL s _ f⟩ =
          fun α => pullCut H hL b s n (sym K hL hA hB s hS e he hO h V f α) :=
  ⟨fun s => ⟨stalkId_cutIdeal_secPull hL s, fun hB' a _ _ =>
      ⟨vanishesTo_baseChange_iff H hL s hB' a, Fil_baseChange H hL s hB' a⟩⟩,
    fun {D} _ K _ _ _ _ hA hB hA' hB' a b s hS e he _ hO =>
      haveI := smooth_baseChange H D
      ⟨Res_baseChange H hL K hA hB hA' hB' a b s hS e he hO,
        sym_baseChange H hL K hA hB hA' hB' a b s hS e he hO⟩⟩

end GlobalTheory.Vanishing
