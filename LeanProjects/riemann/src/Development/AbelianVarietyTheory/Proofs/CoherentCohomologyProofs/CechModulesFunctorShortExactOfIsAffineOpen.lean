import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe w t v u

noncomputable section

namespace GlobalTheory

section Cech

variable {X : Scheme.{u}} {ι : Type} {V : X.Opens} {U : ι → X.Opens}

theorem cechAcyclicMod_of_isAffineOpen
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (cechOpen V U s))
    (F : X.Modules) [F.IsQuasicoherent] : CechAcyclicMod V U F :=
  fun s hs q => cohOn.subsingleton_of_isAffineOpen F (hU s hs) q.succ_pos

theorem isAffineOpen_cechOpen_of_le (h : ∀ i, U i ≤ V)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (s : Finset ι)
    (hs : s.Nonempty) : IsAffineOpen (cechOpen V U s) := by
  rw [cechOpen_of_nonempty h hs]
  exact hU s hs

theorem isAffineOpen_finset_biInf [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hU : ∀ i, IsAffineOpen (U i)) (s : Finset ι) (hs : s.Nonempty) :
    IsAffineOpen (⨅ i ∈ s, U i) :=
  IsAffineOpen.biInf (s : Set ι) s.finite_toSet hs fun i _ => hU i

theorem isAffineHom_diagonal_of_isSeparated {S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [IsSeparated f] : IsAffineHom (pullback.diagonal (terminal.from X)) := by
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  infer_instance

theorem exists_fin_affine_cover (hV : IsCompact (V : Set X)) :
    ∃ (m : ℕ) (U : Fin m → X.Opens), (∀ i, IsAffineOpen (U i)) ∧ ⨆ i, U i = V := by
  obtain ⟨κ, _, 𝒰, h₁, h₂⟩ := QCoh.exists_finite_affine_cover_of_isCompact hV
  exact ⟨_, fun i => 𝒰 ((Fintype.equivFin κ).symm i), fun i => h₁ _,
    ((Fintype.equivFin κ).symm.iSup_comp (g := 𝒰)).trans h₂.symm⟩

section Comparison

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] [LinearOrder ι] [Finite ι]
  (hc : ⨆ i, U i = ⊤) (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i))

omit [LinearOrder ι] [Finite ι] in
include hU in

theorem cechAcyclicMod_top_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent] :
    CechAcyclicMod ⊤ U F :=
  cechAcyclicMod_of_isAffineOpen (isAffineOpen_cechOpen_of_le (fun _ => le_top) hU) F

def cechHEquivCoh (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    cechH R F ⊤ U n ≃ₗ[R] coh F n :=
  cechHEquivCohOn R hc.ge (cechAcyclicMod_top_of_isAffineOpen hU F) n

theorem cechHEquivCoh_def (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    cechHEquivCoh R hc hU F n =
      cechHEquivCohOn R hc.ge (cechAcyclicMod_top_of_isAffineOpen hU F) n := rfl

theorem cechHEquivCoh_map {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G)
    (n : ℕ) (x : cechH R F ⊤ U n) :
    cechHEquivCoh R hc hU G n ((cechHMap R ⊤ U φ n).hom x) =
      cohOn.map R φ ⊤ n (cechHEquivCoh R hc hU F n x) :=
  cechHEquivCohOn_map R hc.ge _ _ φ n x

theorem cechHEquivCoh_toCechH (F : X.Modules) [F.IsQuasicoherent] (x : sectionsOn F ⊤) :
    cechHEquivCoh R hc hU F 0 (toCechH R F ⊤ U x) = (cohOn.zeroEquiv R F ⊤).symm x := by
  rw [cechHEquivCoh_def, cechHEquivCohOn_zero, cechHZeroEquivCohOn, LinearEquiv.trans_apply,
    cechHZeroEquiv_toCechH]

omit [Finite ι] in
include hU in

theorem cechModulesFunctor_shortExact_of_isAffineOpen {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] :
    (S.map (cechModulesFunctor R ⊤ U)).ShortExact :=
  cechModulesFunctor_shortExact_of_acyclic R hS (cechAcyclicMod_top_of_isAffineOpen hU _)

theorem cechHEquivCoh_δ {S : ShortComplex X.Modules} (hS : S.ShortExact) [S.X₁.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] (h : (S.map (cechModulesFunctor R ⊤ U)).ShortExact) (n : ℕ)
    (x : cechH R S.X₃ ⊤ U n) :
    cechHEquivCoh R hc hU S.X₁ (n + 1) ((h.δ n (n + 1) rfl).hom x) =
      cohOn.δ R hS ⊤ n (cechHEquivCoh R hc hU S.X₃ n x) :=
  cechHEquivCohOn_δ R hc.ge hS _ _ n x

end Comparison

theorem cohOn.subsingleton_of_card_le [Fintype ι] (hc : V ≤ ⨆ i, U i)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (cechOpen V U s))
    (F : X.Modules) [F.IsQuasicoherent] {n : ℕ} (hn : Fintype.card ι ≤ n) :
    Subsingleton (cohOn F V n) :=
  subsingleton_cohOn_of_cechAcyclic hc (cechAcyclicMod_of_isAffineOpen hU F) hn

theorem coh.subsingleton_of_card_le [Fintype ι] (hc : ⨆ i, U i = ⊤)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i))
    (F : X.Modules) [F.IsQuasicoherent] {n : ℕ} (hn : Fintype.card ι ≤ n) :
    Subsingleton (coh F n) :=
  subsingleton_cohOn_of_cechAcyclic hc.ge (cechAcyclicMod_top_of_isAffineOpen hU F) hn

end Cech

section Affine

variable {X : Scheme.{u}} (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

theorem sectionsOn.exact_of_isAffineOpen {S : ShortComplex X.Modules} (hS : S.Exact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) : Function.Exact (sectionsOn.map R S.f U) (sectionsOn.map R S.g U) :=
  QCoh.exact_app_of_exact hS hU

theorem sectionsOn.shortExact_of_isAffineOpen {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (sectionsOn.map R S.f U) ∧
      Function.Exact (sectionsOn.map R S.f U) (sectionsOn.map R S.g U) ∧
      Function.Surjective (sectionsOn.map R S.g U) :=
  sections_shortExact_of_subsingleton (T := X.toPresheafedSpace.carrier)
    (shortExact_toAbSheaf hS) U (cohOn.subsingleton_of_isAffineOpen S.X₁ hU one_pos)

end Affine

section DirectSum

open DirectSum

variable {X : Scheme.{u}} {κ : Type w} [DecidableEq κ] {F : κ → X.Modules} {c : Cofan F}
  (hc : IsColimit c)

def cofanProj (k : κ) : c.pt ⟶ F k :=
  Cofan.IsColimit.desc hc fun j => if h : j = k then eqToHom (congrArg F h) else 0

theorem inj_cofanProj (k : κ) : c.inj k ≫ cofanProj hc k = 𝟙 _ := by
  rw [cofanProj, Cofan.IsColimit.fac, dif_pos rfl, eqToHom_refl]

theorem inj_cofanProj_of_ne {j k : κ} (h : j ≠ k) : c.inj j ≫ cofanProj hc k = 0 := by
  rw [cofanProj, Cofan.IsColimit.fac, dif_neg h]

theorem inj_comp_sum_cofanProj {T : Finset κ} {j : κ} (hj : j ∈ T) :
    c.inj j ≫ ∑ k ∈ T, cofanProj hc k ≫ c.inj k = c.inj j := by
  rw [Preadditive.comp_sum, Finset.sum_eq_single_of_mem j hj]
  · rw [← Category.assoc, inj_cofanProj, Category.id_comp]
  · intro k _ hk
    rw [← Category.assoc, inj_cofanProj_of_ne hc hk.symm, zero_comp]

theorem exists_finset_sum_cofanProj_app [Small.{u} κ] [∀ k, (F k).IsQuasicoherent] {W : X.Opens}
    (hW : IsAffineOpen W) (s : Γ(c.pt, W)) : ∃ T : Finset κ, ∀ T', T ⊆ T' →
      (∑ k ∈ T', cofanProj hc k ≫ c.inj k).app W s = s := by
  let N : Submodule Γ(X, W) Γ(c.pt, W) :=
    { carrier := {s | ∃ T : Finset κ, ∀ T', T ⊆ T' →
        QCoh.appLinear (∑ k ∈ T', cofanProj hc k ≫ c.inj k) W s = s}
      add_mem' := by
        rintro a b ⟨A, hA⟩ ⟨B, hB⟩
        exact ⟨A ∪ B, fun T h => by
          rw [map_add, hA T (Finset.subset_union_left.trans h),
            hB T (Finset.subset_union_right.trans h)]⟩
      zero_mem' := ⟨∅, fun _ _ => map_zero _⟩
      smul_mem' := by
        rintro r a ⟨A, hA⟩
        exact ⟨A, fun T h => by rw [map_smul, hA T h]⟩ }
  have := QCoh.preservesColimit_sections hW (Discrete.functor F)
  have h0 : (ModuleCat.ofHom N.mkQ : ((QCoh.sections W).mapCocone c).pt ⟶ _) = 0 := by
    refine (isColimitOfPreserves (QCoh.sections W) hc).hom_ext fun j => ?_
    refine Eq.trans (ModuleCat.hom_ext (LinearMap.ext fun x => ?_)) comp_zero.symm
    refine (Submodule.Quotient.mk_eq_zero N).2 ⟨{j.as}, fun T hT => ?_⟩
    exact congr(($(inj_comp_sum_cofanProj hc (hT (Finset.mem_singleton_self j.as)))).app W x)
  exact (Submodule.Quotient.mk_eq_zero N).1 congr(($h0).hom s)

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] (V : X.Opens) (n : ℕ)

variable (c) in

def cohOn.directSumMap : (⨁ k, cohOn (F k) V n) →ₗ[R] cohOn c.pt V n :=
  DirectSum.toModule R κ _ fun k => cohOn.map R (c.inj k) V n

variable (c) in

@[simp]
theorem cohOn.directSumMap_lof (k : κ) (x : cohOn (F k) V n) :
    cohOn.directSumMap c R V n (DirectSum.lof R κ (fun k => cohOn (F k) V n) k x) =
      cohOn.map R (c.inj k) V n x :=
  DirectSum.toModule_lof (M := fun k => cohOn (F k) V n) R k x

include hc in

theorem cohOn.directSumMap_injective : Function.Injective (cohOn.directSumMap c R V n) := by
  have key (j : κ) : cohOn.map R (cofanProj hc j) V n ∘ₗ cohOn.directSumMap c R V n =
      DirectSum.component R κ (fun k => cohOn (F k) V n) j := by
    refine DirectSum.linearMap_ext _ fun k => LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, cohOn.directSumMap_lof, cohOn.map_map]
    by_cases h : k = j
    · subst h
      rw [inj_cofanProj, cohOn.map_id, DirectSum.component.lof_self, LinearMap.id_apply]
    · rw [inj_cofanProj_of_ne hc h, cohOn.map_zero_hom, DirectSum.component.of, dif_neg h,
        LinearMap.zero_apply]
  intro x y hxy
  refine DirectSum.ext_component R fun j => ?_
  rw [← key j, LinearMap.comp_apply, LinearMap.comp_apply, hxy]

variable {V} [Small.{u} κ] [∀ k, (F k).IsQuasicoherent]

include hc in

theorem cohOn.directSumMap_bijective {ι : Type} [Finite ι] {U : ι → X.Opens} (hV : V ≤ ⨆ i, U i)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (cechOpen V U s)) :
    Function.Bijective (cohOn.directSumMap c R V n) := by
  refine ⟨cohOn.directSumMap_injective hc R V n, fun x => ?_⟩
  cases nonempty_fintype ι
  letI : LinearOrder ι := LinearOrder.lift' _ (Fintype.equivFin ι).injective
  haveI : c.pt.IsQuasicoherent := QCoh.isQuasicoherent_of_isColimit hc
  have ha := cechAcyclicMod_of_isAffineOpen hU c.pt
  obtain ⟨y, rfl⟩ := (cechHEquivCohOn R hV ha n).surjective x
  obtain ⟨z, rfl⟩ := cechClass_surjective (cechCube R c.pt V U) n y
  choose T hT using fun s : {s : Finset ι // s.card = n + 1} =>
    exists_finset_sum_cofanProj_app hc (hU s.1 (Finset.card_pos.1 (by have := s.2; omega)))
      (sectionsOn.toΓ c.pt _ (z.1 s))
  have h := cechHEquivCohOn_map R hV ha ha
    (∑ k ∈ Finset.univ.biUnion T, cofanProj hc k ≫ c.inj k) n (cechClass (cechCube R c.pt V U) n z)
  have hz : (cechHMap R V U (∑ k ∈ Finset.univ.biUnion T, cofanProj hc k ≫ c.inj k) n).hom
      (cechClass (cechCube R c.pt V U) n z) = cechClass (cechCube R c.pt V U) n z :=
    homologyMap_cechClass (cechCubeMap R V U _) n z z (funext fun s =>
      hT s _ (Finset.subset_biUnion_of_mem T (Finset.mem_univ s)))
  rw [hz, cohOn.map_sum_hom, LinearMap.sum_apply] at h
  refine ⟨∑ k ∈ Finset.univ.biUnion T, DirectSum.lof R κ (fun k => cohOn (F k) V n) k
    (cohOn.map R (cofanProj hc k) V n
      (cechHEquivCohOn R hV ha n (cechClass (cechCube R c.pt V U) n z))), Eq.trans ?_ h.symm⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [cohOn.directSumMap_lof, cohOn.map_map]

variable (F) [HasCoproduct F]

def coh.sigmaEquiv {ι : Type} [Finite ι] {U : ι → X.Opens} (hcov : ⨆ i, U i = ⊤)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) :
    (⨁ k, coh (F k) n) ≃ₗ[R] coh (∐ F) n :=
  LinearEquiv.ofBijective (cohOn.directSumMap (Cofan.mk (∐ F) (Sigma.ι F)) R ⊤ n)
    (cohOn.directSumMap_bijective (coproductIsCoproduct F) R n hcov.ge
      (isAffineOpen_cechOpen_of_le (fun _ => le_top) hU))

@[simp]
theorem coh.sigmaEquiv_lof {ι : Type} [Finite ι] {U : ι → X.Opens} (hcov : ⨆ i, U i = ⊤)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (k : κ) (x : coh (F k) n) :
    coh.sigmaEquiv F R n hcov hU (DirectSum.lof R κ (fun k => coh (F k) n) k x) =
      cohOn.map R (Sigma.ι F k) ⊤ n x :=
  cohOn.directSumMap_lof (Cofan.mk (∐ F) (Sigma.ι F)) R ⊤ n k x

end DirectSum

section Disjoint

open SheafLES in

theorem SheafLES.pi_res_bijective_of_disjoint {T : TopCat.{u}} {κ : Type w} {V : Opens T}
    {U : κ → Opens T} (h : ∀ i, U i ≤ V) (hc : V ≤ ⨆ i, U i)
    (hd : Pairwise fun i j => Disjoint (U i) (U j))
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (n : ℕ) :
    Function.Bijective fun (x : Sheaf.H'.{u} F n V) (i : κ) => res F n (homOfLE (h i)) x := by
  induction n generalizing F with
  | zero =>
    constructor
    · intro x y hxy
      apply (equivZero F V).injective
      refine TopCat.Sheaf.eq_of_locally_eq' (X := T) F U V (fun i => homOfLE (h i)) hc _ _
        fun i => ?_
      exact (equivZero_res _ x).symm.trans
        ((congrArg _ (congrFun hxy i)).trans (equivZero_res _ y))
    · intro y
      obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (X := T) F U V
        (fun i => homOfLE (h i)) hc (fun i => equivZero F (U i) (y i)) fun i j => by
          by_cases hij : i = j
          · subst hij
            rfl
          · haveI : Subsingleton (F.obj.obj (op (U i ⊓ U j))) :=
              AddCommGrpCat.subsingleton_of_isZero
                (TopCat.Sheaf.isTerminalOfEqEmpty F (hd hij).eq_bot).isZero
            exact Subsingleton.elim (α := F.obj.obj (op (U i ⊓ U j))) _ _
      refine ⟨(equivZero F V).symm s, funext fun i => (equivZero F (U i)).injective ?_⟩
      rw [equivZero_res, AddEquiv.apply_symm_apply]
      exact hs i
  | succ n ih =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    have inj : Injective (Flasque.injectiveShortComplex F).X₂ :=
      inferInstanceAs (Injective (Injective.under F))
    have hδ (W : Opens T) := δ_surjective_of_subsingleton.{u} hS n W
      (Flasque.subsingleton_H'_of_injective _ n W)
    constructor
    · have key (z) (hz : ∀ i, δ.{u} hS n (U i) (res _ n (homOfLE (h i)) z) = 0) :
          δ.{u} hS n V z = 0 := by
        choose w hw using fun i => (exact₃ hS n (U i) _).1 (hz i)
        obtain ⟨w₀, rfl⟩ := (ih _).2 w
        have : map (Flasque.injectiveShortComplex F).g n V w₀ = z :=
          (ih _).1 (funext fun i => (res_map _ n _ w₀).trans (hw i))
        rw [← this, δ_map]
      intro x y hxy
      obtain ⟨x, rfl⟩ := hδ V x
      obtain ⟨y, rfl⟩ := hδ V y
      rw [← sub_eq_zero, ← map_sub]
      refine key _ fun i => ?_
      rw [map_sub, map_sub, ← δ_res, ← δ_res, sub_eq_zero]
      exact congrFun hxy i
    · intro y
      choose z hz using fun i => hδ (U i) (y i)
      obtain ⟨z₀, rfl⟩ := (ih _).2 z
      exact ⟨δ hS n V z₀, funext fun i => (δ_res hS n _ z₀).trans (hz i)⟩

variable {X : Scheme.{u}} (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] {κ : Type w}
  {V : X.Opens} {U : κ → X.Opens}

theorem cohOn.pi_res_bijective_of_disjoint (h : ∀ i, U i ≤ V) (hc : V ≤ ⨆ i, U i)
    (hd : Pairwise fun i j => Disjoint (U i) (U j)) (F : X.Modules) (n : ℕ) :
    Function.Bijective (LinearMap.pi fun i => cohOn.res R F (h i) n) :=
  SheafLES.pi_res_bijective_of_disjoint (T := X.toPresheafedSpace.carrier) h hc hd
    ((toAbSheaf X).obj F) n

def coh.disjointEquiv (hc : ⨆ i, U i = ⊤) (hd : Pairwise fun i j => Disjoint (U i) (U j))
    (F : X.Modules) (n : ℕ) : coh F n ≃ₗ[R] ∀ i, cohOn F (U i) n :=
  LinearEquiv.ofBijective _ (cohOn.pi_res_bijective_of_disjoint R (fun _ => le_top) hc.ge hd F n)

@[simp]
theorem coh.disjointEquiv_apply (hc : ⨆ i, U i = ⊤)
    (hd : Pairwise fun i j => Disjoint (U i) (U j)) (F : X.Modules) (n : ℕ) (x : coh F n) (i : κ) :
    coh.disjointEquiv R hc hd F n x i = cohOn.res R F le_top n x := rfl

variable {Y : κ → Scheme.{u}} (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
  [∀ i, Algebra R Γ(Y i, ⊤)]
  (hj : ∀ i r, (j i).appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y i, ⊤) r)
  (hc : ⨆ i, (j i).opensRange = ⊤)
  (hd : Pairwise fun a b => Disjoint (j a).opensRange (j b).opensRange)

def coh.disjointRestrictEquiv (F : X.Modules) (n : ℕ) :
    coh F n ≃ₗ[R] ∀ i, coh (F.restrict (j i)) n :=
  (coh.disjointEquiv R hc hd F n).trans (LinearEquiv.piCongrRight fun i =>
    cohOn.restrictEquiv R (hj i) F (j i).image_top_eq_opensRange n)

theorem coh.disjointRestrictEquiv_apply (F : X.Modules) (n : ℕ) (x : coh F n) (i : κ) :
    coh.disjointRestrictEquiv R j hj hc hd F n x i =
      cohOn.pull (σ := RingHom.id R) (hj i) (G := F.restrict (j i))
        ((Scheme.Modules.restrictAdjunction (j i)).unit.app F) (V := ⊤) (W := ⊤) le_top n x :=
  cohOn.pull_res (σ := RingHom.id R) (hj i) (G := F.restrict (j i)) _ le_top _ x

end Disjoint

attribute [local instance] Abelian.hasFiniteBiproducts in
open DirectSum in

theorem cech_computes_coh_of_affine_cover (X : Scheme.{u}) (R : Type v) [CommRing R]
    [Algebra R Γ(X, ⊤)] :
    ((X.IsSeparated ∨ IsAffineHom (pullback.diagonal (terminal.from X))) →
      ∀ (ι : Type) (U : ι → X.Opens), (∀ i, IsAffineOpen (U i)) →
        ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) ∧
    (∀ (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → X.Opens), ⨆ i, U i = ⊤ →
      (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) →
      (∃ e : ∀ (F : X.Modules) [F.IsQuasicoherent] (n : ℕ), cechH R F ⊤ U n ≃ₗ[R] coh F n,
        (∀ (F : X.Modules) [F.IsQuasicoherent] (x : sectionsOn F ⊤),
          e F 0 (toCechH R F ⊤ U x) = (cohOn.zeroEquiv R F ⊤).symm x) ∧
        (∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) (n : ℕ)
          (x : cechH R F ⊤ U n),
          e G n ((cechHMap R ⊤ U φ n).hom x) = cohOn.map R φ ⊤ n (e F n x)) ∧
        ∀ (S : ShortComplex X.Modules) (hS : S.ShortExact) [S.X₁.IsQuasicoherent]
          [S.X₃.IsQuasicoherent], ∃ h : (S.map (cechModulesFunctor R ⊤ U)).ShortExact,
            ∀ (n : ℕ) (x : cechH R S.X₃ ⊤ U n),
              e S.X₁ (n + 1) ((h.δ n (n + 1) rfl).hom x) = cohOn.δ R hS ⊤ n (e S.X₃ n x)) ∧
      (∀ (F : X.Modules) [F.IsQuasicoherent] (n : ℕ), Fintype.card ι ≤ n →
        Subsingleton (coh F n)) ∧
      ∀ (κ : Type u) [DecidableEq κ] (F : κ → X.Modules) [∀ k, (F k).IsQuasicoherent] (n : ℕ),
        ∃ e : (⨁ k, coh (F k) n) ≃ₗ[R] coh (∐ F) n, ∀ k x,
          e (DirectSum.lof R κ (fun k => coh (F k) n) k x) = cohOn.map R (Sigma.ι F k) ⊤ n x) ∧
    (IsAffine X → ∀ (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
      [S.X₃.IsQuasicoherent],
      (S.Exact → Function.Exact (sectionsOn.map R S.f ⊤) (sectionsOn.map R S.g ⊤)) ∧
      (S.ShortExact → Function.Injective (sectionsOn.map R S.f ⊤) ∧
        Function.Exact (sectionsOn.map R S.f ⊤) (sectionsOn.map R S.g ⊤) ∧
        Function.Surjective (sectionsOn.map R S.g ⊤))) ∧
    (∀ (Y : Scheme.{u}) (f : Y ⟶ X) [Algebra R Γ(Y, ⊤)],
      (∀ r, f.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r) →
      (IsAffineHom f ∨ IsFinite f ∨ IsClosedImmersion f) →
      ∃ e : ∀ (G : Y.Modules) [G.IsQuasicoherent] (n : ℕ),
          coh ((Scheme.Modules.pushforward f).obj G) n ≃ₗ[R] coh G n,
        (∀ (G : Y.Modules) [G.IsQuasicoherent] (x : coh ((Scheme.Modules.pushforward f).obj G) 0),
          coh.zeroEquiv G (e G 0 x) = coh.zeroEquiv ((Scheme.Modules.pushforward f).obj G) x) ∧
        ∀ (G G' : Y.Modules) [G.IsQuasicoherent] [G'.IsQuasicoherent] (s : G ⟶ G') (n : ℕ)
          (x : coh ((Scheme.Modules.pushforward f).obj G) n),
          e G' n (cohOn.map R ((Scheme.Modules.pushforward f).map s) ⊤ n x) =
            cohOn.map R s ⊤ n (e G n x)) ∧
    (∀ (κ : Type u) [Finite κ] (F : κ → X.Modules) (n : ℕ),
      ∃ e : coh (biproduct F) n ≃ₗ[R] ∀ k, coh (F k) n,
        ∀ x k, e x k = cohOn.map R (biproduct.π F k) ⊤ n x) ∧
    (∀ (κ : Type w) (U : κ → X.Opens), ⨆ i, U i = ⊤ →
      (Pairwise fun i j => Disjoint (U i) (U j)) → ∀ (F : X.Modules) (n : ℕ),
      (∃ e : coh F n ≃ₗ[R] ∀ i, cohOn F (U i) n, ∀ x i, e x i = cohOn.res R F le_top n x) ∧
      ∀ [∀ i, Algebra R Γ(U i, ⊤)],
        ∀ hU : ∀ i r, (U i).ι.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(U i, ⊤) r,
        ∃ e : coh F n ≃ₗ[R] ∀ i, coh (F.restrict (U i).ι) n, ∀ x i, e x i =
          cohOn.pull (σ := RingHom.id R) (hU i) (G := F.restrict (U i).ι)
            ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app F) (V := ⊤) (W := ⊤)
            le_top n x) := by
  refine ⟨fun h ι U hU => ?_, fun ι _ _ U hc hU => ⟨⟨cechHEquivCoh R hc hU,
      cechHEquivCoh_toCechH R hc hU, fun _ _ _ _ => cechHEquivCoh_map R hc hU,
      fun S hS _ _ => ⟨cechModulesFunctor_shortExact_of_isAffineOpen R hU hS,
        cechHEquivCoh_δ R hc hU hS _⟩⟩,
      fun F _ _ hn => coh.subsingleton_of_card_le hc hU F hn,
      fun κ _ F _ n => ⟨coh.sigmaEquiv F R n hc hU, coh.sigmaEquiv_lof F R n hc hU⟩⟩,
    fun _ S _ _ _ => ⟨fun hS => sectionsOn.exact_of_isAffineOpen R hS (isAffineOpen_top X),
      fun hS => sectionsOn.shortExact_of_isAffineOpen R hS (isAffineOpen_top X)⟩,
    fun Y f _ hf h => ?_,
    fun κ _ F n => ⟨cohOn.biproductEquiv R ⊤ n F, cohOn.biproductEquiv_apply R ⊤ n F⟩,
    fun κ U hc hd F n => ⟨⟨coh.disjointEquiv R hc hd F n, coh.disjointEquiv_apply R hc hd F n⟩,
      fun hU => ⟨coh.disjointRestrictEquiv R (fun i => (U i).ι) hU (by simpa using hc)
        (by simpa using hd) F n, coh.disjointRestrictEquiv_apply R _ hU _ _ F n⟩⟩⟩
  · have : IsAffineHom (pullback.diagonal (terminal.from X)) := by
      rcases h with h | h
      · infer_instance
      · exact h
    exact isAffineOpen_finset_biInf hU
  · have : IsAffineHom f := by
      rcases h with h | h | h <;> infer_instance
    exact ⟨coh.pushforwardEquiv R hf, fun G _ x => cohOn.zeroEquiv_pushforwardEquiv R hf G ⊤ x,
      fun _ _ _ _ => coh.pushforwardEquiv_map R hf⟩

end GlobalTheory
