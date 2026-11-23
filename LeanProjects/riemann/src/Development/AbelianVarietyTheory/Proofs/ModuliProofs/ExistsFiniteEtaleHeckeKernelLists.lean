import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkTuple

theorem exists_equiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (g : T.left ⟶ S) (hg : T.hom ≫ f = g) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk g ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  subst hg
  exact GlobalTheory.HkSetPull.exists_equiv h T

theorem exists_tuples {S : Scheme.{0}} (G : Over S) [GrpObj G] (N n : ℕ) (hG : IsAbelianScheme G)
    (hn : IsUnit (N : Γ(S, ⊤))) :
    ∃ (Z : Scheme.{0}) (a : Z ⟶ S) (x : Fin n → (Over.mk a ⟶ G)), IsFinite a ∧ Etale a ∧ (∀ j, x j ^ N = 1) ∧
      ∀ (T : Over S) (y : Fin n → (T ⟶ G)), (∀ j, y j ^ N = 1) → ∃! h : T ⟶ Over.mk a, ∀ j, h ≫ x j = y j := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hn
  have key : ∃ (Z : Over S) (x : Fin n → (Z ⟶ G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ j, x j ^ N = 1) ∧
      ∀ (T : Over S) (y : Fin n → (T ⟶ G)), (∀ j, y j ^ N = 1) → ∃! h : T ⟶ Z, ∀ j, h ≫ x j = y j := by
    refine ⟨Out.powObj (torsion G N) n, fun i => Out.powPr (torsion G N) i ≫ torsion.ι G N,
      LatticeTorsion.prop_powObj @IsFinite _ hfin n, LatticeTorsion.prop_powObj @Etale _ het n, fun i => ?_,
      fun T y' hy' => ?_⟩
    · rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]
    · choose y hy hyu using fun i : Fin n => LatticeTorsion.existsUnique_torsion G N (y' i) (hy' i)
      let h : T ⟶ Out.powObj (torsion G N) n := (Out.powIsLimit (torsion G N) n).lift (Fan.mk T y)
      have hh : ∀ i, h ≫ Out.powPr (torsion G N) i = y i := fun i =>
        (Out.powIsLimit (torsion G N) n).fac (Fan.mk T y) ⟨i⟩
      refine ⟨h, fun i => by rw [← hy i, ← hh i, Category.assoc], fun h' hh' => ?_⟩
      refine (Out.powIsLimit (torsion G N) n).hom_ext fun ⟨i⟩ => ?_
      exact (hyu i _ ((Category.assoc _ _ _).trans (hh' i))).trans (hh i).symm
  obtain ⟨Z, x, h⟩ := key
  exact ⟨Z.left, Z.hom, x, h⟩

theorem eq_of_mem_range {S : Scheme.{0}} {G : Over S} (τ : 𝟙_ (Over S) ⟶ G) {k : Type} [Field k] {x : Sp k ⟶ S}
    (z : Over.mk x ⟶ G) (u : Sp k) (hu : z.left u ∈ Set.range τ.left) : z = toUnit _ ≫ τ := by
  have w : τ.left ≫ G.hom = 𝟙 S := Over.w _
  have i₁ : IsImmersion τ.left := by
    have : IsImmersion (τ.left ≫ G.hom) := by rw [w]; exact inferInstanceAs (IsImmersion (𝟙 S))
    exact IsImmersion.of_comp _ G.hom
  have r : Set.range (pullback.fst z.left τ.left) = Set.univ := by
    rw [Scheme.Pullback.range_fst]
    refine Set.eq_univ_of_forall fun v => ?_
    rw [show v = u from Subsingleton.elim (α := PrimeSpectrum k) _ _]
    exact hu
  have i₂ : IsClosedImmersion (pullback.fst z.left τ.left) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [r]; exact isClosed_univ)
  have i₃ : Surjective (pullback.fst z.left τ.left) := ⟨Set.range_eq_univ.1 r⟩
  have i₄ : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have i₅ : IsIso (pullback.fst z.left τ.left) := isIso_of_isClosedImmersion_of_surjective _
  refine Over.OverMorphism.ext ?_
  have tu : (toUnit (Over.mk x)).left = x := by simp
  have wz : z.left ≫ G.hom = x := Over.w _
  rw [Over.comp_left, tu, ← cancel_epi (pullback.fst z.left τ.left)]
  have e : pullback.fst z.left τ.left ≫ z.left ≫ G.hom ≫ τ.left = pullback.fst z.left τ.left ≫ z.left := by
    rw [pullback.condition_assoc, reassoc_of% w, pullback.condition]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ.left) (Category.comp_id _))
  rw [← e, reassoc_of% wz]

theorem range_subset_iff {S : Scheme.{0}} {G : Over S} {n : ℕ} (τ : Fin n → (𝟙_ (Over S) ⟶ G)) {k : Type} [Field k]
    {x : Sp k ⟶ S} (z : Over.mk x ⟶ G) :
    Set.range z.left ⊆ (⋃ j, Set.range (τ j).left) ↔ z ∈ Set.range fun j => toUnit (Over.mk x) ≫ τ j := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨(default : PrimeSpectrum k), rfl⟩)
    exact ⟨j, (eq_of_mem_range (τ j) z _ hj).symm⟩
  · rintro ⟨j, rfl⟩ _ ⟨u, rfl⟩
    refine Set.mem_iUnion.2 ⟨j, (toUnit (Over.mk x)).left u, ?_⟩
    exact (Scheme.Hom.comp_apply _ _ _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem listed_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (D : Datum H) (P : Ideal (𝓞 E))
    (p i : ℕ) (m : SABMap t' t f) {n : ℕ} (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)) (τ : Fin n → (𝟙_ (Over S') ⟶ t'.G))
    (e : ∀ j, (τ j).left ≫ m.φ = f ≫ (σ j).left) {k : Type} [Field k] (x : Sp k ⟶ S') :
    ((Function.Injective fun j => x ≫ (τ j).left) ∧ ∃ C : Subgroup (Over.mk x ⟶ t'.G),
      (C : Set _) = Set.range (fun j => toUnit (Over.mk x) ≫ τ j) ∧ t'.HeckeKer (Over.mk x) D P p i C) ↔
    ((Function.Injective fun j => (x ≫ f) ≫ (σ j).left) ∧ ∃ C : Subgroup (Over.mk (x ≫ f) ⟶ t.G),
      (C : Set _) = Set.range (fun j => toUnit (Over.mk (x ≫ f)) ≫ σ j) ∧
        t.HeckeKer (Over.mk (x ≫ f)) D P p i C) := by
  obtain ⟨ρ, e₀⟩ := exists_equiv m.cart (Over.mk x) (x ≫ f) rfl
  have tu : (toUnit (Over.mk x)).left = x := by simp
  have tu' : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := by simp
  have l₁ : ∀ j, (toUnit (Over.mk x) ≫ τ j).left = x ≫ (τ j).left := fun j => by rw [Over.comp_left, tu]
  have l₂ : ∀ j, (toUnit (Over.mk (x ≫ f)) ≫ σ j).left = (x ≫ f) ≫ (σ j).left := fun j => by
    rw [Over.comp_left, tu']
  have e₁ : ∀ j, ρ (toUnit (Over.mk x) ≫ τ j) = toUnit (Over.mk (x ≫ f)) ≫ σ j := fun j =>
    Over.OverMorphism.ext (by
      rw [e₀, l₁, l₂]
      exact (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) (e j)).trans (Category.assoc _ _ _).symm))
  have mem : ∀ u, u ∈ Set.range (fun j => toUnit (Over.mk x) ≫ τ j) ↔
      ρ u ∈ Set.range (fun j => toUnit (Over.mk (x ≫ f)) ≫ σ j) := fun u =>
    exists_congr fun j => by beta_reduce; rw [← e₁]; exact ρ.injective.eq_iff.symm
  have eq : ∀ (u : Over.mk x ⟶ t'.G) (v : Over.mk (x ≫ f) ⟶ t.G), v.left = u.left ≫ m.φ → v = ρ u :=
    fun u v h => Over.OverMorphism.ext (h.trans (e₀ u).symm)
  refine and_congr (forall₂_congr fun a b => imp_congr_left ?_) ⟨?_, ?_⟩
  · beta_reduce
    rw [← l₁, ← l₁, ← l₂, ← l₂]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← e₁, ← e₁, Over.OverMorphism.ext h]
    · have := Over.OverMorphism.ext h
      rw [← e₁, ← e₁] at this
      rw [ρ.injective this]
  · rintro ⟨C', h₁, h₂⟩
    refine ⟨C'.comap ρ.symm.toMonoidHom, Set.ext fun v => ?_,
      (GlobalTheory.HkSetPull.heckeKer_iff D P p i m (Over.mk x) C' _ fun u v h => ?_).1 h₂⟩
    · obtain ⟨u, rfl⟩ := ρ.surjective v
      rw [← mem, ← h₁]
      show ρ.symm (ρ u) ∈ C' ↔ _
      rw [ρ.symm_apply_apply]
      rfl
    · rw [eq u v h]
      show _ ↔ ρ.symm (ρ u) ∈ C'
      rw [ρ.symm_apply_apply]
  · rintro ⟨C, h₁, h₂⟩
    refine ⟨C.comap ρ.toMonoidHom, Set.ext fun u => ?_,
      (GlobalTheory.HkSetPull.heckeKer_iff D P p i m (Over.mk x) _ C fun u v h => ?_).2 h₂⟩
    · rw [mem, ← h₁]
      rfl
    · rw [eq u v h]
      rfl

theorem range_subset_of_geom {T Z : Scheme.{0}} (h : T ⟶ Z) (V : Set Z)
    (hV : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), Set.range (x ≫ h) ⊆ V) : Set.range h ⊆ V := by
  rintro _ ⟨y, rfl⟩
  let k := AlgebraicClosure (T.residueField y)
  let z : Sp k ⟶ T := Spec.map (CommRingCat.ofHom (algebraMap (T.residueField y) k)) ≫ T.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  exact hV k z ⟨(default : PrimeSpectrum k), (Scheme.Hom.comp_apply _ _ _).trans (congrArg h (hz _))⟩

end GlobalTheory.HkTuple

open GlobalTheory.HkTuple in

theorem GlobalTheory.exists_finiteEtale_heckeLists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s), admitted l 𝔓 p → ∃ (Y : Scheme.{0}) (a : Y ⟶ S) (oY : Ob D l (a ≫ s)) (m : ObjMap oY o a) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite a ∧ Etale a ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t : SAB H T) (mu : SABMap t o.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃! h : T ⟶ Y, h ≫ a = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  intro E _ _ _ H D l P p i n S s o adm
  have hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    have := ((baseKA l).unit (p ^ 2) (pow_pos adm.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  have specMap_id₂ : spMap (RingHom.id (KA l)) = 𝟙 _ := Spec.map_id _
  obtain ⟨Z, b, x, hf, he, hx, huniv⟩ := exists_tuples o.t.G (p ^ 2) n (GlobalTheory.ObjDim.isAbelianScheme o) hu
  obtain ⟨oZ, ⟨mZ⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S Z s (b ≫ s) b rfl rfl
    (by rw [specMap_id₂, Category.comp_id]) o
  obtain ⟨ρ, e₀⟩ := exists_equiv mZ.cart (𝟙_ (Over Z)) b (Category.id_comp b)
  let σZ : Fin n → (𝟙_ (Over Z) ⟶ oZ.t.G) := fun j => ρ.symm (x j)
  have eZ : ∀ j, (σZ j).left ≫ mZ.toSABMap.φ = (x j).left := fun j => by
    rw [← e₀, ρ.apply_symm_apply]
  have pZ : ∀ j, σZ j ^ p ^ 2 = 1 := fun j => by rw [← map_pow, hx, map_one]
  obtain ⟨V, hc, hV⟩ := GlobalTheory.T.exists_clopen_locus_torsionSections_heckeKernel E H D l P p i n Z (b ≫ s) oZ σZ adm pZ
  obtain ⟨oY, ⟨mY⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) Z V (b ≫ s) ((V.ι ≫ b) ≫ s) V.ι
    rfl rfl (by rw [specMap_id₂, Category.comp_id, Category.assoc]) oZ
  obtain ⟨m, hm⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o oZ oY).2 b V.ι mZ).1 mY
  obtain ⟨ρ', e₀'⟩ := exists_equiv mY.cart (𝟙_ (Over V.toScheme)) V.ι (Category.id_comp _)
  let σ : Fin n → (𝟙_ (Over V.toScheme) ⟶ oY.t.G) := fun j => ρ'.symm (toUnit _ ≫ σZ j)
  have tu : (toUnit (Over.mk V.ι)).left = V.ι := by simp
  have eY : ∀ j, (σ j).left ≫ mY.toSABMap.φ = V.ι ≫ (σZ j).left := fun j => by
    rw [← e₀', ρ'.apply_symm_apply, Over.comp_left, tu]
  have eσ : ∀ j, (σ j).left ≫ m.toSABMap.φ = V.ι ≫ (x j).left := fun j => by
    rw [hm, ← eZ]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ mZ.toSABMap.φ) (eY j)).trans (Category.assoc _ _ _))
  have hY := fun (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ V.toScheme) =>
    (listed_iff D P p i mY.toSABMap σZ σ eY y).2 ((hV k (y ≫ V.ι)).1 (by
      rintro _ ⟨u, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact (y u).2))
  have ci : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by rwa [Scheme.Opens.range_ι])
  refine ⟨V, V.ι ≫ b, oY, m, σ, ⋃ j, Set.range (σ j).left, inferInstance, inferInstance,
    ⟨fun j => ?_, rfl, fun k _ _ y => (hY k y).1⟩, fun k _ _ y => ?_, ?_⟩
  · rw [← map_pow, ← MonObj.comp_pow, pZ, MonObj.comp_one, map_one]
  · obtain ⟨C, h₁, h₂⟩ := (hY k y).2
    exact ⟨C, fun z => by rw [range_subset_iff, ← h₁]; rfl, h₂⟩
  · rintro T f t mu τ K' ⟨hτ, rfl, hinj⟩ hK
    obtain ⟨ρ₂, e₂⟩ := exists_equiv mu.cart (𝟙_ (Over T)) f (Category.id_comp _)
    obtain ⟨h₀, hh₀, hh₀u⟩ := huniv (Over.mk f) (fun j => ρ₂ (τ j)) (fun j => by rw [← map_pow, hτ, map_one])
    have e₃ : ∀ j, h₀.left ≫ (x j).left = (τ j).left ≫ mu.φ := fun j => by
      rw [← e₂, ← hh₀, Over.comp_left]
    have uq : ∀ g : T ⟶ Z, g ≫ b = f → (∀ j, g ≫ (x j).left = (τ j).left ≫ mu.φ) → g = h₀.left := fun g w hg =>
      congrArg (·.left) (hh₀u (Over.homMk g w) fun j => Over.OverMorphism.ext ((hg j).trans (e₂ _).symm))
    obtain ⟨g, w, e₄, uq'⟩ : ∃ g : T ⟶ Z, g ≫ b = f ∧ (∀ j, g ≫ (x j).left = (τ j).left ≫ mu.φ) ∧
        ∀ g' : T ⟶ Z, g' ≫ b = f → (∀ j, g' ≫ (x j).left = (τ j).left ≫ mu.φ) → g' = g :=
      ⟨h₀.left, Over.w h₀, e₃, uq⟩
    clear uq e₃ hh₀u hh₀ h₀ e₂ ρ₂
    subst w
    obtain ⟨mu', hmu⟩ := GlobalTheory.ObjMaps.exists_sab_cancel mZ.toSABMap mu
    have e₅ : ∀ j, (τ j).left ≫ mu'.φ = g ≫ (σZ j).left := fun j => by
      have w₁ : (τ j).left ≫ t.G.hom = 𝟙 T := Over.w _
      have w₂ : (σZ j).left ≫ oZ.t.G.hom = 𝟙 Z := Over.w _
      refine mZ.cart.1.hom_ext ?_ ?_
      · exact (Category.assoc _ _ _).trans ((congrArg ((τ j).left ≫ ·) hmu.symm).trans ((e₄ j).symm.trans
          ((congrArg (g ≫ ·) (eZ j).symm).trans (Category.assoc _ _ _).symm)))
      · exact (Category.assoc _ _ _).trans ((congrArg ((τ j).left ≫ ·) mu'.cart.1.w).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) w₁).trans ((Category.id_comp g).trans
          ((Category.comp_id g).symm.trans ((congrArg (g ≫ ·) w₂.symm).trans (Category.assoc _ _ _).symm))))))
    have hr : Set.range g ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      refine range_subset_of_geom g _ fun k _ _ y => (hV k (y ≫ g)).2
        ((listed_iff D P p i mu' σZ τ e₅ y).1 ⟨hinj k y, ?_⟩)
      obtain ⟨C, h₁, h₂⟩ := hK k y
      exact ⟨C, Set.ext fun z => (h₁ z).trans (range_subset_iff τ z), h₂⟩
    refine ⟨IsOpenImmersion.lift V.ι g hr, ⟨by rw [IsOpenImmersion.lift_fac_assoc], fun j => ?_⟩, ?_⟩
    · exact (congrArg (IsOpenImmersion.lift V.ι g hr ≫ ·) (eσ j)).trans
        ((IsOpenImmersion.lift_fac_assoc _ _ _ _).trans (e₄ j))
    · rintro h ⟨w, hh⟩
      rw [← cancel_mono V.ι, IsOpenImmersion.lift_fac]
      exact uq' _ ((Category.assoc _ _ _).trans w) fun j =>
        (Category.assoc _ _ _).trans ((congrArg (h ≫ ·) (eσ j).symm).trans (hh j))
