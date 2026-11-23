import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSpMapFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionsUniqueDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayBasis

open GlobalTheory.InvFieldRing

theorem decompR {K : Type} [CommRing K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} {π : Y' ⟶ Sp (DualNumber K)} {ρ : Y' ⟶ Y}
    (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)) :
    ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  refine GlobalTheory.RelConstThickening.existsUnique_comb (W := ⊤) (fun U hU _ F => ?_) O le_top F
  refine GlobalTheory.RelConstThickening.existsUnique_of_isPushout (GlobalTheory.RelConstThickening.constHom q U) (ρ.app U)
    (GlobalTheory.RelConstThickening.constHom π (ρ ⁻¹ᵁ U)) ?_ F
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine po.of_iso (Scheme.ΓSpecIso (.of K)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber K))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [GlobalTheory.RelConstThickening.constHom]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [GlobalTheory.RelConstThickening.constHom]

section Field

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

def transl (u : epsR R ⟶ G) : epsR R ⊗ G ⟶ G := snd _ G * (fst _ G ≫ u)

def red (R : Type) [CommRing R] : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (spMap_fst_comp R)

def fib (G : Over (Sp R)) : G ⟶ epsR R ⊗ G := lift (toUnit G ≫ red R) (𝟙 G)

theorem fib_snd : (fib G).left ≫ (snd (epsR R) G).left = 𝟙 _ := by
  rw [← Over.comp_left, fib, lift_snd]; rfl

theorem fib_fst : (fib G).left ≫ (fst (epsR R) G).left = G.hom ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
  rw [← Over.comp_left, fib, lift_fst, Over.comp_left, Over.toUnit_left]; rfl

theorem fib_transl {u : epsR R ⟶ G} (hu : IsTangent u) : (fib G).left ≫ (transl u).left = 𝟙 _ := by
  have hs : red R ≫ u = η[G] := Over.OverMorphism.ext hu
  have hT : fib G ≫ transl u = 𝟙 G := by
    rw [transl, fib, MonObj.comp_mul, lift_fst_assoc, lift_snd, Category.assoc, hs, ← Hom.one_def, _root_.mul_one]
  rw [← Over.comp_left, hT]; rfl

theorem isPullback_thickR : IsPullback (snd (epsR R) G).left (fst (epsR R) G).left G.hom
    (spMap (algebraMap R (DualNumber R))) :=
  (IsPullback.of_hasPullback (epsR R).hom G.hom).flip

theorem surjective_fib : Surjective (fib G).left := by
  have hp : IsPullback (fib G).left G.hom (fst (epsR R) G).left (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    refine IsPullback.of_right ?_ fib_fst isPullback_thickR
    rw [fib_snd, spMap_fst_comp]
    exact IsPullback.id_horiz G.hom
  exact MorphismProperty.of_isPullback (P := @Surjective) hp.flip (surjective_spMap_fst R)

theorem preimage_translR {u : epsR R ⟶ G} (hu : IsTangent u) (O : G.left.Opens) :
    (transl u).left ⁻¹ᵁ O = (snd (epsR R) G).left ⁻¹ᵁ O := by
  ext x
  obtain ⟨y, rfl⟩ := (surjective_fib (G := G)).surj x
  change ((fib G).left ≫ (transl u).left).base y ∈ O ↔ ((fib G).left ≫ (snd (epsR R) G).left).base y ∈ O
  rw [fib_transl hu, fib_snd]

theorem real_partR {u : epsR R ⟶ G} (hu : IsTangent u) (O : G.left.Opens) (f a b : Γ(G.left, O))
    (h : ((transl u).left.appLE O _ (preimage_translR hu O).ge).hom f =
      ((snd (epsR R) G).left.app O).hom a + constFn (fst (epsR R) G).left _ DualNumber.eps *
        ((snd (epsR R) G).left.app O).hom b) : a = f := by
  have hjO : O ≤ (fib G).left ⁻¹ᵁ ((snd (epsR R) G).left ⁻¹ᵁ O) := by
    rw [← Scheme.Hom.comp_preimage, fib_snd, Scheme.Hom.id_preimage]
  have k := congrArg ((fib G).left.appLE _ _ hjO).hom h
  simp only [map_add, map_mul, Scheme.Hom.app_eq_appLE, appLE_appLE, appLE_constFn] at k
  rw [appLE_eq_of_eq (fib_transl hu) O O _ le_rfl, appLE_eq_of_eq fib_snd O O _ le_rfl, fib_fst] at k
  have h0 : (TrivSqZeroExt.fstHom R R R).toRingHom DualNumber.eps = 0 := by simp
  rw [constFn_spMap, h0] at k
  simp only [constFn, map_zero, zero_mul, add_zero] at k
  have hid : ∀ s : Γ(G.left, O), ((𝟙 G.left : G.left ⟶ G.left).appLE O O le_rfl).hom s = s := fun s =>
    (congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_eq_app (𝟙 G.left) (U := O))).trans rfl
  rw [hid, hid] at k
  exact k.symm

variable [IsCommMonObj G]

def pt (v : TanM (𝟙 (Sp R)) G) : epsR R ⟶ G :=
  Over.homMk (tv v).left ((Over.w (tv v)).trans (Category.comp_id _))

theorem isTangent_pt (v : TanM (𝟙 (Sp R)) G) : IsTangent (pt v) := by
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.scK_zero_iff]
  apply Over.OverMorphism.ext
  have h := congrArg (fun V => V.left) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v)
  refine Eq.trans h ?_
  rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left]
  exact congrArg (· ≫ _) (Category.comp_id _)

theorem exists_isInv (v : TanM (𝟙 (Sp R)) G) : ∃ dd : Fld G.left, IsInv G v dd := by
  have hu := isTangent_pt v
  have hd := fun (O : G.left.Opens) (f : Γ(G.left, O)) =>
    decompR (isPullback_thickR (G := G)) O (((transl (pt v)).left.appLE O _ (preimage_translR hu O).ge).hom f)
  choose ab hab huq using hd
  have huniq : ∀ O f (a b : Γ(G.left, O)),
      ((transl (pt v)).left.appLE O _ (preimage_translR hu O).ge).hom f =
        ((snd (epsR R) G).left.app O).hom a + constFn (fst (epsR R) G).left _ DualNumber.eps *
          ((snd (epsR R) G).left.app O).hom b → (ab O f).2 = b :=
    fun O f a b h => congrArg Prod.snd (huq O f (a, b) h).symm
  have hre : ∀ O f, (ab O f).1 = f := fun O f => real_partR hu O f _ _ (hab O f)
  have hee := fun O : G.left.Opens => constFn_eps_sq (fst (epsR R) G).left ((snd (epsR R) G).left ⁻¹ᵁ O)
  refine ⟨fun O f => (ab O f).2, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro W _ f f'
    refine huniq W _ (f + f') _ ?_
    rw [map_add, hab W f, hab W f', hre, hre]
    simp only [map_add]
    ring
  · intro W _ f f'
    refine huniq W _ (f * f') _ ?_
    rw [map_mul, hab W f, hab W f', hre, hre]
    simp only [map_add, map_mul]
    linear_combination (((snd (epsR R) G).left.app W).hom (ab W f).2 *
      ((snd (epsR R) G).left.app W).hom (ab W f').2) * hee W
  · intro W W' h _ f
    refine huniq W' _ (resG _ h f) _ ?_
    have h' : (snd (epsR R) G).left ⁻¹ᵁ W' ≤ (snd (epsR R) G).left ⁻¹ᵁ W := (snd (epsR R) G).left.preimage_mono h
    rw [appLE_res _ h h' (preimage_translR hu W).ge, hab W f, hre, map_add, map_mul, res_app _ h h',
      res_app _ h h', res_constFn]
  · intro S _ φ g₀ w O f hg hgO htr
    obtain ⟨g', v', hg', hv', rfl⟩ := htr
    have e : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    let kA : tEpsG (g₀ ≫ G.hom) ⟶ epsR R := Over.homMk (spMap (dualMap φ)) (by
      change spMap (dualMap φ) ≫ spMap (algebraMap _ _) = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ G.hom
      rw [hg, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e])
    have hk : lift kA g' ≫ transl (pt v) = g' * v' := by
      unfold transl
      rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]
      congr 1
      exact Over.OverMorphism.ext hv'.symm
    have hk2 : (lift kA g').left ≫ (snd (epsR R) G).left = spMap (algebraMap S (DualNumber S)) ≫ g₀ := by
      rw [← Over.comp_left, lift_snd, hg']
    have hk1 : (lift kA g').left ≫ (fst (epsR R) G).left = spMap (dualMap φ) := by
      rw [← Over.comp_left, lift_fst]
      rfl
    have hT : (g' * v').left = (lift kA g').left ≫ (transl (pt v)).left := by rw [← hk, Over.comp_left]
    have hx : ⊤ ≤ (lift kA g').left ⁻¹ᵁ ((snd (epsR R) G).left ⁻¹ᵁ O) := by
      intro y _
      show ((lift kA g').left ≫ (snd (epsR R) G).left).base y ∈ O
      rw [hk2]
      exact hgO (Set.mem_univ _)
    rw [hT, ← valR_appLE _ _ O _ (preimage_translR hu O).ge hx, hab O f, hre, valR_add _ _ hx, valR_mul _ _ hx,
      valR_constFn _ _ _ hk1 _ hx, Scheme.Hom.app_eq_appLE, valR_appLE _ _ _ _ _ hx, valR_appLE _ _ _ _ _ hx, hk2,
      valR_spMap_comp _ _ _ hgO, valR_spMap_comp _ _ _ hgO]
    simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem tv_sum {κ : Type} (s : Finset κ) (f : κ → TanM (𝟙 (Sp R)) G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_add, ih]

open ReciprocityTheory.ChartRestriction.G.PullbackSections in

theorem exists_basis [IsLocalRing R] (hG : Smooth G.hom) :
    ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) := by
  have hS := isGrpPullback_pullback G (𝟙 (Sp R))
  have hsm : Smooth ((Over.pullback (𝟙 (Sp R))).obj G).hom := by
    show Smooth (pullback.snd _ _)
    infer_instance
  obtain ⟨n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis ((Over.pullback (𝟙 (Sp R))).obj G) hsm
  let b : Fin n → TanM (𝟙 (Sp R)) G := fun i =>
    mkT (pushHom hS (epsR R) (v i)) ((isTangent_iff hS _).1 (hv.1 i))
  have hb : ∀ m : TanM (𝟙 (Sp R)) G, ∃! a : Fin n → R, m = ∑ i, a i • b i := fun m => by
    obtain ⟨w', hw'⟩ := push_surj hS (tv m)
    have htan : IsTangent w' := (isTangent_iff hS w').2 (by rw [hw']; exact tv_mem m)
    have key : ∀ a : Fin n → R, IsLieComb a v w' ↔ m = ∑ i, a i • b i := by
      intro a
      rw [isLieComb_iff hS, hw']
      constructor
      · intro h
        apply tanM_ext
        rw [h, tv_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [tv_smul]
        rfl
      · intro h
        rw [h, tv_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [tv_smul]
        rfl
    obtain ⟨C, hC, hCu⟩ := hv.2 w' htan
    exact ⟨C, (key C).1 hC, fun a ha => hCu a ((key a).2 ha)⟩
  refine ⟨n, ⟨Module.Basis.mk (v := b) ?_ ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact congrFun ((hb 0).unique hg.symm (y₂ := 0) (by simp)) i
  · intro m _
    obtain ⟨a, ha, -⟩ := hb m
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Field

theorem exists_basis_isInv : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  intro R _ _ _ D O _ _ _ oa Y
  have h1 : Smooth Y.q.left := Y.smooth_q
  have h2 : Smooth D.P.A.hom := D.P.isAb.smooth
  have hG : Smooth Y.H.hom := by
    rw [← Over.w Y.q]
    infer_instance
  obtain ⟨n, ⟨v⟩⟩ := exists_basis hG
  choose dd hdd using fun a => exists_isInv (v a)
  exact ⟨n, v, dd, hdd⟩

end GlobalTheory.RayBasis
