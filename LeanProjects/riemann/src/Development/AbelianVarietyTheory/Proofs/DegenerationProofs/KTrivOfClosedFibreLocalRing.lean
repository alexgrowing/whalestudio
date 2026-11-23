import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivLocal

open GlobalTheory.AbLaw GlobalTheory.UU

theorem ring_retraction {A C : Type} [CommRing A] [IsLocalRing A] [CommRing C] (φ : A →+* C) (hφ : φ.Finite)
    (ε : C →+* A) (he : ∀ a, ε (φ a) = a)
    (h : ∀ c, c - φ (ε c) ∈ (IsLocalRing.maximalIdeal A).map φ) (c : C) : φ (ε c) = c := by
  algebraize [φ]
  have hle : (⊤ : Submodule A C) ≤ LinearMap.range (Algebra.linearMap A C) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) fun x _ => ?_
    refine Submodule.mem_sup.2 ⟨φ (ε x), ⟨ε x, rfl⟩, x - φ (ε x), ?_, by ring⟩
    rw [Ideal.smul_top_eq_map]
    exact h x
  obtain ⟨a, rfl⟩ := hle (Submodule.mem_top (x := c))
  exact congrArg φ (he a)

theorem comp_section_eq_id_spec {A : Type} [CommRing A] [IsLocalRing A] {C : CommRingCat.{0}}
    (f : Spec C ⟶ Spec (CommRingCat.of A)) [hf : IsFinite f] (e : Spec (CommRingCat.of A) ⟶ Spec C)
    (he : e ≫ f = 𝟙 _)
    (h : ∀ (T : Scheme.{0}) (t : T ⟶ Sp (IsLocalRing.ResidueField A)) (y : T ⟶ Spec C),
      y ≫ f = t ≫ spMap (IsLocalRing.residue A) → y ≫ f ≫ e = y) : f ≫ e = 𝟙 _ := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ε, rfl⟩ := Spec.map_surjective e
  have hφ : φ.hom.Finite := (IsFinite.SpecMap_iff φ).1 hf
  have he' : φ ≫ ε = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, he, Spec.map_id])
  let I : Ideal C := (IsLocalRing.maximalIdeal A).map φ.hom
  let τ : IsLocalRing.ResidueField A →+* C ⧸ I :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp φ.hom) fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  have k := h _ (spMap τ) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl)
  rw [← Spec.map_comp, ← Spec.map_comp] at k
  have k' := Spec.map_injective k
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext c
  refine ring_retraction φ.hom hφ ε.hom (fun a => congrArg (fun q => q.hom a) he') (fun x => ?_) c
  exact Ideal.Quotient.eq.1 (congrArg (fun q => q.hom x) k').symm

theorem comp_section_eq_id {A : Type} [CommRing A] [IsLocalRing A] {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of A)) [IsFinite f] (e : Spec (CommRingCat.of A) ⟶ H) (he : e ≫ f = 𝟙 _)
    (h : ∀ (T : Scheme.{0}) (t : T ⟶ Sp (IsLocalRing.ResidueField A)) (y : T ⟶ H),
      y ≫ f = t ≫ spMap (IsLocalRing.residue A) → y ≫ f ≫ e = y) : f ≫ e = 𝟙 _ := by
  have : IsAffine H := isAffine_of_isAffineHom f
  have k := comp_section_eq_id_spec (H.isoSpec.inv ≫ f) (e ≫ H.isoSpec.hom) (by simpa using he)
    fun T t y hy => by
      have := h T t (y ≫ H.isoSpec.inv) (by simpa using hy)
      simp only [Category.assoc] at this ⊢
      rw [reassoc_of% this]
      simp
  rw [← cancel_epi H.isoSpec.inv, ← cancel_mono H.isoSpec.hom]
  simpa using k

theorem kTriv_of_closed_fibre : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → RelAmple B N → KTriv ((Over.pullback (spMap (IsLocalRing.residue A))).obj B) (N.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))) → KTriv B N := by
  intro hLaws _ A _ _ _ B _ _ hB L hLB hL hk
  have hG := hLaws.globalFns
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy A B L hLB).1 hL
  have hP : IsProjBy B.hom := ⟨_, isLB_pw hLB _, n, s, hs⟩
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hLB
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG A B hB hP L (pw L 0) hLB hO
  have hfin : IsFinite H.hom :=
    GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG A B hB L (pw L 0) hLB hO hL H j hj hH
  have hrep : ∀ (T : Over (Spec (CommRingCat.of A))) (x : T ⟶ B), InK B L x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  obtain ⟨e, he⟩ := (hrep _ _).1 (inK_one hLB (𝟙_ _))
  have h := isGrpPullback_pullback B (spMap (IsLocalRing.residue A))
  have hL' : (L.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))).IsLB := DVR.linComb_isLB _ hLB _ _
  have key : H.hom ≫ e.left = 𝟙 _ := by
    refine comp_section_eq_id H.hom e.left (Over.w e) fun T t y hy => ?_
    have hdi : (y ≫ j.left) ≫ B.hom = t ≫ spMap (IsLocalRing.residue A) := by
      rw [Category.assoc, Over.w j, hy]
    let x : Over.mk t ⟶ (Over.pullback (spMap (IsLocalRing.residue A))).obj B :=
      Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
    let z : Over.mk (t ≫ spMap (IsLocalRing.residue A)) ⟶ H := Over.homMk y hy
    have hz : z ≫ j = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
    have hx : x = 1 := InK.eq_one hk (inK_of_push h hLB hL' (lbIso_self hL') x ((hrep _ _).2 ⟨z, hz⟩))
    have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
    have h1 : z ≫ toUnit H ≫ e = z := by
      rw [← cancel_mono j, hz, hx', Category.assoc, Category.assoc, he, MonObj.comp_one, MonObj.comp_one]
    have h2 : (toUnit H).left = H.hom := (Category.comp_id _).symm.trans (Over.w (toUnit H))
    exact (congrArg (fun q => y ≫ q ≫ e.left) h2).symm.trans (congrArg (fun q => q.left) h1)
  have hj1 : j = 1 := by
    have h2 : (toUnit H).left = H.hom := (Category.comp_id _).symm.trans (Over.w (toUnit H))
    have h1 : toUnit H ≫ e = 𝟙 H :=
      Over.OverMorphism.ext ((congrArg (fun q => q ≫ e.left) h2).trans key)
    rw [← Category.id_comp j, ← h1, Category.assoc, he, MonObj.comp_one]
  refine kTriv_iff_forall.2 fun T x hxK => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hxK
  rw [hj1, MonObj.comp_one]

end GlobalTheory.KTrivLocal
