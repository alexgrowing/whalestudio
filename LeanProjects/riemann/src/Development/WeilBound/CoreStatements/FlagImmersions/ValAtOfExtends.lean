import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasisStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open GlobalTheory.CompanionTheory.Ar.LieTangent

namespace RootFieldNumerics.RF.IntFr

section Gen

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

theorem exists_bc {R R' : Type} [CommRing R] [CommRing R'] {x : Spec (CommRingCat.of R) ⟶ X}
    {x' : Spec (CommRingCat.of R') ⟶ X} (φ : R →+* R') (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x')
    {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E)
    (M' : LieModel G x' E') : ∃ j : E →+ E', (∀ e, M'.pt (j e) = epsBase φ h ≫ M.pt e) ∧
      ∀ a e, j (a • e) = φ a • j e := by
  choose j hj using fun e => M'.onto _ (isTanAt_base φ h (M.tan e))
  refine ⟨AddMonoidHom.mk' j fun a b => M'.inj ?_, hj, fun a e => M'.inj ?_⟩
  · rw [M'.add, hj, hj, hj, M.add, MonObj.comp_mul]
  · show M'.pt (j (a • e)) = M'.pt (φ a • j e)
    rw [M'.pt_smul, hj, hj, M.pt_smul, ← Category.assoc, base_scale, Category.assoc]

theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom (dualMap (g.comp f))) := by
  rw [spec_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp

variable {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Em : Type} [AddCommGroup Em] [Module Ω Em]

theorem valAt_of_extends (M : LieModel G ξ Em) (hall : ∀ q : X, genPt ξ ⤳ q) {V L : Type} [CommRing V] [IsLocalRing V]
    [CommRing L] [IsLocalRing L] (φ : V →+* L) (z : Spec (CommRingCat.of V) ⟶ X) {e : Em}
    {v : epsAt (R := X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) ⟶ G}
    (hv : M.Extends ⟨centre z, hall _⟩ e v) {w : epsAt (Spec.map (CommRingCat.ofHom φ) ≫ z) ⟶ G}
    (hw : w.left = Spec.map (CommRingCat.ofHom (dualMap
      (RingHom.comp (α := X.presheaf.stalk (centre z)) φ (Scheme.stalkClosedPointTo z).hom))) ≫ v.left) :
    M.ValAt (Spec.map (CommRingCat.ofHom φ) ≫ z) e w := by
  have hs := centre_specializes φ z
  let s : X.presheaf.stalk (centre z) →+* X.presheaf.stalk (centre (Spec.map (CommRingCat.ofHom φ) ≫ z)) :=
    (X.presheaf.stalkSpecializes hs).hom
  have h1 : Spec.map (CommRingCat.ofHom s) ≫ X.fromSpecStalk (centre z) =
      X.fromSpecStalk (centre (Spec.map (CommRingCat.ofHom φ) ≫ z)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hs
  refine ⟨hall _, epsBase s h1 ≫ v, ⟨isTanAt_base s h1 hv.1, ?_⟩, ?_⟩
  · refine hv.2.trans ?_
    change _ = _ ≫ Spec.map (CommRingCat.ofHom (dualMap s)) ≫ v.left
    rw [← Category.assoc, dual_comp]
    congr 4
    exact RingHom.ext fun a => (genMap_specializes ⟨centre z, hall _⟩ (hall _) hs a).symm
  · refine hw.trans ?_
    change _ = _ ≫ Spec.map (CommRingCat.ofHom (dualMap s)) ≫ v.left
    rw [← Category.assoc, dual_comp]
    congr 4
    exact (congrArg (fun t => t.hom) (stalk_base φ z)).symm

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_coords {X : Scheme.{0}} (t : SAB H X) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {Em : Type} [AddCommGroup Em] [Module Ω Em] (M : LieModel t.G ξ Em) (hall : ∀ q : X, genPt ξ ⤳ q)
    (hξ : IsCptGen ξ) (V L : Type) [CommRing V] [IsLocalRing V] [Field L] [Algebra V L]
    (z : Spec (CommRingCat.of V) ⟶ X) :
    ∃ (g : ℕ) (MV : LieModel t.G z (Fin g → V)) (ρV : 𝓞 E →+* Module.End V (Fin g → V))
      (MC : LieModel t.G (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (Fin g → L))
      (ρC : 𝓞 E →+* Module.End L (Fin g → L)), MV.IsActOf t.act.act ρV ∧ MC.IsActOf t.act.act ρC ∧
      (∀ u, (MC.pt (algebraMap V L ∘ u)).left = spMap (dualMap (algebraMap V L)) ≫ (MV.pt u).left) ∧
      (∀ a u, ρC a (algebraMap V L ∘ u) = algebraMap V L ∘ ρV a u) ∧
      ∀ x, x ∈ M.fibAt M.lat z MC ↔ ∀ k, x k ∈ (algebraMap V L).range := by
  classical
  let R : Type := X.presheaf.stalk (centre z)
  let fV : R →+* V := (Scheme.stalkClosedPointTo z).hom
  obtain ⟨g, MR, ρR, -, hbc⟩ := GlobalTheory.T.lie_model_action_base_change E H X t R (X.fromSpecStalk (centre z))
  have hz : spMap fV ≫ X.fromSpecStalk (centre z) = z := spec_centre z
  obtain ⟨MV, ρV, aV, hV, -⟩ := hbc V fV z hz.symm
  obtain ⟨MC, ρC, aC, hC, -⟩ := hbc L ((algebraMap V L).comp fV) (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z)
    ((congrArg (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ ·) hz.symm).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ X.fromSpecStalk (centre z)) (spec_comp fV (algebraMap V L)))))
  obtain ⟨j, hj, hjs⟩ := exists_bc (algebraMap V L) rfl MV MC
  have sV : ∀ i : Fin g, (fV ∘ (Pi.single i 1 : Fin g → R)) = Pi.single i 1 := fun i => by
    ext k; by_cases h : k = i <;> simp [Pi.single_apply, h]
  have sC : ∀ i : Fin g, (((algebraMap V L).comp fV) ∘ (Pi.single i 1 : Fin g → R)) = Pi.single i 1 := fun i => by
    ext k; by_cases h : k = i <;> simp [Pi.single_apply, h]
  have hj1 : ∀ i : Fin g, j (Pi.single i 1) = Pi.single i 1 := fun i => MC.inj (Over.OverMorphism.ext (by
    rw [hj, ← sC, hC, ← sV]
    refine (congrArg (Spec.map (CommRingCat.ofHom (dualMap (algebraMap V L))) ≫ ·) (hV (Pi.single i 1))).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (MR.pt (Pi.single i 1)).left) (dual_comp _ _))))
  have hju : ∀ u, j u = algebraMap V L ∘ u := fun u => by
    have e : u = ∑ i, u i • (Pi.single i 1 : Fin g → V) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [e]
    rw [map_sum]
    simp only [hjs, hj1]
    ext k; simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  have hpt : ∀ u, MC.pt (algebraMap V L ∘ u) = epsBase (algebraMap V L) rfl ≫ MV.pt u := fun u => by
    rw [← hju, hj]
  refine ⟨g, MV, ρV, MC, ρC, aV, aC, fun u => congrArg (fun q => q.left) (hpt u), fun a u => MC.inj ?_, fun x => ?_⟩
  · rw [aC a, hpt, hpt, aV a, Category.assoc]
  · let Λ : Submodule V (Fin g → L) :=
      { carrier := {x | ∀ k, x k ∈ (algebraMap V L).range}
        add_mem' := fun ha hb k => add_mem (ha k) (hb k)
        zero_mem' := fun k => zero_mem _
        smul_mem' := fun a x hx k => by
          show a • x k ∈ _
          rw [Algebra.smul_def]
          exact mul_mem ⟨a, rfl⟩ (hx k) }
    constructor
    · intro hx
      refine (Submodule.span_le (p := Λ)).2 ?_ hx
      rintro w ⟨h, e, he, hv⟩
      obtain ⟨v, hv₀⟩ := (M.mem_lat_iff _ e).1 he
      obtain ⟨r, rfl⟩ := MR.onto v hv₀.1
      have h3 := valAt_of_extends M hall (algebraMap V L) z hv₀ (hC r)
      have e2 := MC.inj (LieModel.ValAt.unique hξ hv h3)
      intro k
      rw [e2]
      exact ⟨_, rfl⟩
    · intro hx
      choose v hv using hx
      have hsum : x = ∑ i, v i • (Pi.single i 1 : Fin g → L) := by
        ext k
        simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hv]
      rw [hsum]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      obtain ⟨e, he⟩ := M.onto _ (isTanAt_base (genMap ξ ⟨centre z, hall _⟩) (spec_genMap ξ ⟨centre z, hall _⟩)
        (MR.tan (Pi.single i 1)))
      have hex : M.Extends ⟨centre z, hall _⟩ e (MR.pt (Pi.single i 1)) :=
        (M.extends_iff _ _ _).2 ⟨MR.tan _, he⟩
      refine Submodule.subset_span ⟨hall _, e, (M.mem_lat_iff _ e).2 ⟨_, hex⟩, ?_⟩
      rw [← sC]
      exact valAt_of_extends M hall (algebraMap V L) z hex (hC _)

theorem exists_sab {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.proved_CubePullSt f t
  exact ⟨_, ⟨m₁⟩⟩

theorem transport {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (h : f = f')
    (m : SABMap t' t f) : ∃ m' : SABMap t' t f', m'.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

theorem act_iff {R : Type} [CommRing R] {X : Scheme.{0}} {t : SAB H X} {t₀ : SAB H (Sp R)} {x : Sp R ⟶ X}
    (m : SABMap t₀ t x) {W : Type} [AddCommGroup W] [Module R W] (M₀ : LieModel t₀.G (𝟙 _) W) (M : LieModel t.G x W)
    (h : ∀ e, (M₀.pt e).left ≫ m.φ = (M.pt e).left) (ρ : 𝓞 E →+* Module.End R W) :
    M₀.IsActOf t₀.act.act ρ ↔ M.IsActOf t.act.act ρ := by
  have key : ∀ a e, (M₀.pt e ≫ t₀.act.act a).left ≫ m.φ = (M.pt e ≫ t.act.act a).left := fun a e => by
    rw [Over.comp_left, Over.comp_left, ← h, Category.assoc, Category.assoc, m.act]
  refine ⟨fun h₀ a e => Over.OverMorphism.ext ?_, fun h₁ a e => Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ?_)⟩
  · rw [← h, h₀ a e, key]
  · rw [key, h, h₁ a e]
  · rw [Over.w, Over.w]

end RootFieldNumerics.RF.IntFr

namespace RootFieldNumerics.RF

open IntFr

theorem intFrames : IntFrames := by
  intro E _ _ _ H D l Xo c _ Y S Ω _ K _ J _ y 𝔐 V L _ _ _ _ _ _ _ z y₀ hz
  obtain ⟨g, MV, ρV, MC, ρC, aV, aC, hVC, hρ, hfib⟩ := exists_coords 𝔐.t 𝔐.M 𝔐.all 𝔐.tie.gen V L z
  obtain ⟨T, ⟨mT⟩⟩ := IntFr.exists_sab z 𝔐.t
  obtain ⟨tK, ⟨m'⟩⟩ := IntFr.exists_sab (spMap (algebraMap V L)) T
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mT m'
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ 𝔐.m n₁
  obtain ⟨n₃, hn₃⟩ := IntFr.transport hz n₂
  obtain ⟨m₃, hm₃⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n₃
  obtain ⟨m, hm⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m₃
  obtain ⟨MK, hK⟩ := (LieMove.main L _ _ _ _ _ (Fin g → L) n₁.cart).1 MC
  obtain ⟨MU, hU⟩ := (LieMove.main L _ _ _ _ _ (Fin g → L) m.cart).2 MK
  obtain ⟨MT, hT⟩ := (LieMove.main V _ _ _ _ _ (Fin g → V) mT.cart).1 MV
  have aK := (act_iff n₁ MK MC hK ρC).2 aC
  have aT := (act_iff mT MT MV hT ρV).2 aV
  refine ⟨T, tK, m, m', g, MC, MU, ρC, aC, (act_iff m MK MU hU ρC).1 aK, fun e => ?_, hfib, ?_⟩
  · have w := Over.w (MK.pt e)
    refine ⟨Over.homMk ((MK.pt e).left ≫ n₃.φ) ?_, ⟨(MK.pt e).left ≫ m₃.φ, ?_, ?_, ?_⟩, ?_⟩
    · rw [Category.assoc, n₃.cart.1.w, ← Category.assoc, w]
      simp
    · rw [Category.assoc, m₃.cart.1.w, ← Category.assoc, w]
      simp
    · rw [Category.assoc, ← hm]; exact hU e
    · rw [Category.assoc]
      exact congrArg ((MK.pt e).left ≫ ·) hm₃.symm
    · show _ = (MK.pt e).left ≫ n₃.φ
      rw [hn₃, hn₂, ← Category.assoc]
      exact congrArg (· ≫ 𝔐.m.φ) (hK e).symm
  · intro σ n x hx hspan
    have hinj : Function.Injective (algebraMap V L) := IsFractionRing.injective V L
    have hmem : ∀ k, x k ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V :=
      fun k => hspan ▸ Submodule.subset_span ⟨k, rfl⟩
    choose xV hxV using fun k => (hfib _).1 (hmem k).1
    have hxe : ∀ k, x k = algebraMap V L ∘ xV k := fun k => funext fun i => (hxV k i).symm
    have cinj : ∀ u u' : Fin g → V, algebraMap V L ∘ u = algebraMap V L ∘ u' → u = u' :=
      fun u u' h => funext fun i => hinj (congrFun h i)
    have heig : ∀ u : Fin g → V, u ∈ eigSp ρV σ ↔ algebraMap V L ∘ u ∈ eigSp ρC ((algebraMap V L).comp σ) := fun u => by
      simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero, hρ]
      refine forall_congr' fun a => ⟨fun h => ?_, fun h => cinj _ _ ?_⟩
      · rw [h]; ext i; simp
      · rw [h]; ext i; simp
    have hsum : ∀ cf : Fin n → V, algebraMap V L ∘ (∑ k, cf k • xV k) = ∑ k, cf k • x k := fun cf => by
      ext i; simp [Finset.sum_apply, hxe, Algebra.smul_def]
    refine ⟨σ, fun k => MT.pt (xV k), rfl, ?_, fun k => ⟨(MK.pt (x k)).left, hU _, ?_⟩⟩
    · refine (GlobalTheory.T.eigen_frame_iff_eigenspace_basis _ V T.G (𝟙 _) _ MT _ T.act ρV σ n xV aT).2 ⟨fun k => (heig _).2 (hxe k ▸ (hmem k).2), ?_⟩
      intro e he
      have h1 : algebraMap V L ∘ e ∈ Submodule.span V (Set.range x) := by
        rw [hspan]
        exact ⟨(hfib _).2 fun i => ⟨_, rfl⟩, (heig e).1 he⟩
      obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
      refine ⟨cf, cinj _ _ (by rw [hsum, hcf]), fun cf' h => ?_⟩
      have h2 : ∑ k, (algebraMap V L (cf' k) - algebraMap V L (cf k)) • x k = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, algebraMap_smul]
        rw [← hsum, ← h, hcf, sub_self]
      exact funext fun k => hinj (sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hx _ h2 k))
    · refine mT.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, ← hn₁, Category.assoc]
        refine (hK _).trans ?_
        rw [hxe, hVC]
        exact congrArg (_ ≫ ·) (hT _).symm
      · rw [Category.assoc, m'.cart.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
        simpa using (spec_dual_alg (algebraMap V L)).symm

end RootFieldNumerics.RF
