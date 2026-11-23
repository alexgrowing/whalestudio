import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Pull1RestrictPairRestriction
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.SmallLift

section Abstract

variable {R R₀ K : Type} [CommRing R] [CommRing R₀] [CommRing K] [Algebra R R₀] [Algebra R K]
  {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F₀ : C ⥤ CommAlgCat.{0} R₀} {Fk : C ⥤ CommAlgCat.{0} K}
  {G : C' ⥤ CommAlgCat.{0} R} {G₀ : C' ⥤ CommAlgCat.{0} R₀} {Gk : C' ⥤ CommAlgCat.{0} K}

structure ExA (a : BC F F₀) (t : R) : Prop where
  surj : ∀ T, Function.Surjective (a.α T)
  ker : ∀ T x, a.α T x = 0 → ∃ y, x = t • y
  smul : ∀ T x, a.α T (t • x) = 0

structure ExB (b : BC F Fk) (t : R) : Prop where
  surj : ∀ T, Function.Surjective (b.α T)
  ker : ∀ T x, b.α T x = 0 → t • x = 0
  ann : ∀ T x, t • x = 0 → b.α T x = 0

def red1 {A : C ⥤ CommAlgCat.{0} R} {B : C ⥤ CommAlgCat.{0} R₀} (a : BC A B) (f : C1 A) : C1 B :=
  fun T T' φ ↦ a.α T' (f T T' φ)

def red2 {A : C ⥤ CommAlgCat.{0} R} {B : C ⥤ CommAlgCat.{0} R₀} (a : BC A B) (y : C2 A) : C2 B :=
  fun T T' T'' φ ψ ↦ a.α T'' (y T T' T'' φ ψ)

theorem coboundary_zero_reduction {A : C ⥤ CommAlgCat.{0} R} {B : C ⥤ CommAlgCat.{0} R₀} (a : BC A B) (g : C0 A) :
    d0 B (fun T ↦ a.α T (g T)) = red1 a (d0 A g) := by
  funext T T' φ
  simp only [amitsur_d0_apply, red1, map_sub, a.naturality]

theorem coboundary_one_reduction {A : C ⥤ CommAlgCat.{0} R} {B : C ⥤ CommAlgCat.{0} R₀} (a : BC A B) (f : C1 A) :
    d1 B (red1 a f) = red2 a (d1 A f) := by
  funext T T' T'' φ ψ
  simp only [d1_apply, red1, red2, map_sub, map_add, a.naturality]

theorem cocycle_d1_eq_zero {A : C ⥤ CommAlgCat.{0} R} (f : Z1 A) : d1 A f.1 = 0 :=
  LinearMap.mem_ker.1 ((commAlgFunctorCocyclesOne_eq_ker A).le f.2)

theorem diffOne_diffZero (A : C ⥤ CommAlgCat.{0} R) (g : C0 A) : d1 A (d0 A g) = 0 := by
  have := commAlgFunctorCoboundaryZero_mem_cocyclesOne A g
  rw [commAlgFunctorCocyclesOne_eq_ker] at this
  exact this

def Bd (a : BC F F₀) (b : BC F Fk) (t : R) (c : H1 F₀) (z : H2 Fk) : Prop :=
  ∃ (f : C1 F) (y : C2 F) (hf : red1 a f ∈ Z1 F₀) (hy : red2 b y ∈ Z2 Fk),
    d1 F f = t • y ∧ H1.mk F₀ ⟨_, hf⟩ = c ∧ H2.mk Fk ⟨_, hy⟩ = z

variable {a : BC F F₀} {b : BC F Fk} {t : R}

theorem reduction_mem_cocycles_of_smul (hb : ExB b t) (f : C1 F) (y : C2 F) (e : d1 F f = t • y) : red2 b y ∈ Z2 Fk := by
  intro T T' T'' T''' φ ψ χ
  have h := differential_one_mem_scaled_lattice F f φ ψ χ
  rw [e] at h
  simp only [Pi.smul_apply, map_smul] at h
  have k : t • (mp F χ (y T T' T'' φ ψ) + y T T'' T''' (φ ≫ ψ) χ - y T T' T''' φ (ψ ≫ χ) -
      y T' T'' T''' ψ χ) = 0 := by
    simp only [smul_sub, smul_add, h]; abel
  have k' := hb.ann _ _ k
  simp only [map_sub, map_add, b.naturality] at k'
  simp only [red2]
  linear_combination k'

theorem bd_exists (ha : ExA a t) (hb : ExB b t) (c : H1 F₀) : ∃ z, Bd a b t c z := by
  obtain ⟨f₀, rfl⟩ := H1.mk_surjective F₀ c
  choose l hl using fun T T' (φ : T ⟶ T') ↦ ha.surj T' (f₀.1 T T' φ)
  have e₁ : red1 a l = f₀.1 := by funext T T' φ; exact hl T T' φ
  have e₂ : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), a.α T'' (d1 F l T T' T'' φ ψ) = 0 := by
    intro T T' T'' φ ψ
    have h : d1 F₀ (red1 a l) = 0 := by
      rw [e₁]
      exact cocycle_d1_eq_zero f₀
    rw [coboundary_one_reduction] at h
    exact congrFun (congrFun (congrFun (congrFun (congrFun h T) T') T'') φ) ψ
  choose y hy using fun T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T'') ↦ ha.ker T'' _ (e₂ T T' T'' φ ψ)
  have e₃ : d1 F l = t • (y : C2 F) := by funext T T' T'' φ ψ; exact hy T T' T'' φ ψ
  have hf : red1 a l ∈ Z1 F₀ := e₁ ▸ f₀.2
  exact ⟨_, l, y, hf, reduction_mem_cocycles_of_smul hb l y e₃, e₃, congrArg _ (Subtype.ext e₁), rfl⟩

theorem bd_unique (ha : ExA a t) (hb : ExB b t) {c : H1 F₀} {z z' : H2 Fk} (h : Bd a b t c z)
    (h' : Bd a b t c z') : z = z' := by
  obtain ⟨f, y, hf, hy, e, rfl, rfl⟩ := h
  obtain ⟨f', y', hf', hy', e', ec, rfl⟩ := h'
  obtain ⟨g₀, hg₀⟩ := H1.mk_eq_mk.1 ec.symm
  choose g hg using fun T ↦ ha.surj T (g₀ T)
  have e₁ : ∀ T T' (φ : T ⟶ T'), a.α T' ((f - f' - d0 F g) T T' φ) = 0 := by
    intro T T' φ
    have h1 : d0 F₀ (fun T ↦ a.α T (g T)) = red1 a (d0 F g) := coboundary_zero_reduction a g
    have h2 : (fun T ↦ a.α T (g T)) = g₀ := funext hg
    rw [h2, hg₀] at h1
    have h3 := congrFun (congrFun (congrFun h1 T) T') φ
    simp only [Pi.sub_apply, red1] at h3
    simp only [Pi.sub_apply, map_sub]
    linear_combination h3
  choose w hw using fun T T' (φ : T ⟶ T') ↦ ha.ker T' _ (e₁ T T' φ)
  have e₂ : f - f' - d0 F g = t • (w : C1 F) := by funext T T' φ; exact hw T T' φ
  have e₃ : t • (y - y' - d1 F w) = 0 := by
    have := congrArg (d1 F) e₂
    simp only [map_sub, map_smul, diffOne_diffZero, e, e', sub_zero] at this
    rw [smul_sub, smul_sub, this, sub_self]
  refine H2.mk_eq_mk.2 ⟨red1 b w, ?_⟩
  rw [coboundary_one_reduction]
  funext T T' T'' φ ψ
  have h4 := hb.ann T'' _ (congrFun (congrFun (congrFun (congrFun (congrFun e₃ T) T') T'') φ) ψ)
  simp only [Pi.sub_apply, map_sub] at h4
  simp only [Pi.sub_apply, red2]
  linear_combination -h4

theorem Bd.add {c c' : H1 F₀} {z z' : H2 Fk} (h : Bd a b t c z) (h' : Bd a b t c' z') :
    Bd a b t (c + c') (z + z') := by
  obtain ⟨f, y, hf, hy, e, rfl, rfl⟩ := h
  obtain ⟨f', y', hf', hy', e', rfl, rfl⟩ := h'
  have k₁ : red1 a (f + f') = red1 a f + red1 a f' := by
    funext T T' φ; simp [red1]
  have k₂ : red2 b (y + y') = red2 b y + red2 b y' := by
    funext T T' T'' φ ψ; simp [red2]
  refine ⟨f + f', y + y', k₁ ▸ add_mem hf hf', k₂ ▸ add_mem hy hy', ?_, ?_, ?_⟩
  · rw [map_add, e, e', smul_add]
  · rw [← map_add]; exact congrArg _ (Subtype.ext k₁)
  · rw [← map_add]; exact congrArg _ (Subtype.ext k₂)

theorem lift_of_bd (ha : ExA a t) (hb : ExB b t) {c : H1 F₀} (h : Bd a b t c 0) :
    ∃ d : H1 F, a.coef.pull1 d = c := by
  obtain ⟨f, y, hf, hy, e, rfl, e₀⟩ := h
  obtain ⟨g₀, hg₀⟩ := H2.mk_eq_zero.1 e₀
  choose g hg using fun T T' (φ : T ⟶ T') ↦ hb.surj T' (g₀ T T' φ)
  have k₁ : red1 b g = g₀ := by funext T T' φ; exact hg T T' φ
  have k₂ : t • (y - d1 F g) = 0 := by
    funext T T' T'' φ ψ
    refine hb.ker T'' _ ?_
    have h1 := coboundary_one_reduction b g
    rw [k₁, hg₀] at h1
    have h2 := congrFun (congrFun (congrFun (congrFun (congrFun h1 T) T') T'') φ) ψ
    simp only [red2] at h2
    simp only [Pi.sub_apply, map_sub]
    linear_combination h2
  have k₃ : d1 F (f - t • g) = 0 := by
    rw [map_sub, map_smul, e, ← smul_sub]; exact k₂
  refine ⟨H1.mk F ⟨f - t • g, by rw [commAlgFunctorCocyclesOne_eq_ker]; exact k₃⟩, ?_⟩
  refine congrArg _ (Subtype.ext ?_)
  funext T T' φ
  change a.α T' (f T T' φ - t • g T T' φ) = a.α T' (f T T' φ)
  rw [map_sub, ha.smul, sub_zero]

theorem lift_of_trivial (ha : ExA a t) (ht : t = 0 ∨ IsUnit t) (c : H1 F₀) :
    ∃ d : H1 F, a.coef.pull1 d = c := by
  obtain ⟨f₀, rfl⟩ := H1.mk_surjective F₀ c
  choose l hl using fun T T' (φ : T ⟶ T') ↦ ha.surj T' (f₀.1 T T' φ)
  rcases ht with rfl | ⟨u, rfl⟩
  · have inj : ∀ T x, a.α T x = 0 → x = 0 := fun T x hx ↦ by
      obtain ⟨y, rfl⟩ := ha.ker T x hx
      simp
    have hl' : l ∈ Z1 F := by
      rw [commAlgFunctorCocyclesOne_eq_ker]
      funext T T' T'' φ ψ
      refine inj _ _ ?_
      have e₁ : red1 a l = f₀.1 := by funext T T' φ; exact hl T T' φ
      have h2 : d1 F₀ (red1 a l) = 0 := by rw [e₁]; exact cocycle_d1_eq_zero f₀
      rw [coboundary_one_reduction] at h2
      exact congrFun (congrFun (congrFun (congrFun (congrFun h2 T) T') T'') φ) ψ
    exact ⟨H1.mk F ⟨l, hl'⟩, congrArg _ (Subtype.ext (by funext T T' φ; exact hl T T' φ))⟩
  · have zero : ∀ T (x : F₀.obj T), x = 0 := fun T x ↦ by
      obtain ⟨x, rfl⟩ := ha.surj T x
      have : x = (u : R) • ((u⁻¹ : Rˣ) • x) := by simp [Units.smul_def, smul_smul]
      rw [this]; exact ha.smul T _
    refine ⟨0, ?_⟩
    rw [map_zero]
    symm
    refine H1.mk_eq_zero.2 ⟨0, ?_⟩
    funext T T' φ
    exact (zero _ _).trans (zero _ _).symm

structure TriMap (a : BC F F₀) (b : BC F Fk) (a' : BC G G₀) (b' : BC G Gk) where

  fn : C' ⥤ C

  α : ∀ T, F.obj (fn.obj T) →+* G.obj T

  α₀ : ∀ T, F₀.obj (fn.obj T) →+* G₀.obj T

  αk : ∀ T, Fk.obj (fn.obj T) →+* Gk.obj T
  nat : ∀ {T T' : C'} (φ : T ⟶ T') x, α T' (mp F (fn.map φ) x) = mp G φ (α T x)
  nat₀ : ∀ {T T' : C'} (φ : T ⟶ T') x, α₀ T' (mp F₀ (fn.map φ) x) = mp G₀ φ (α₀ T x)
  natk : ∀ {T T' : C'} (φ : T ⟶ T') x, αk T' (mp Fk (fn.map φ) x) = mp Gk φ (αk T x)
  smul : ∀ T (r : R) x, α T (r • x) = r • α T x
  smul₀ : ∀ T (r : R₀) x, α₀ T (r • x) = r • α₀ T x
  smulk : ∀ T (r : K) x, αk T (r • x) = r • αk T x
  ca : ∀ T x, a'.α T (α T x) = α₀ T (a.α _ x)
  cb : ∀ T x, b'.α T (α T x) = αk T (b.α _ x)

variable {a' : BC G G₀} {b' : BC G Gk}

def TriMap.c₀ (M : TriMap a b a' b') : CoefMap (RingHom.id R₀) F₀ G₀ := ⟨M.fn, M.α₀, M.nat₀, M.smul₀⟩

def TriMap.ck (M : TriMap a b a' b') : CoefMap (RingHom.id K) Fk Gk := ⟨M.fn, M.αk, M.natk, M.smulk⟩

theorem Bd.pull (M : TriMap a b a' b') {c : H1 F₀} {z : H2 Fk} (h : Bd a b t c z) :
    Bd a' b' t (M.c₀.pull1 c) (M.ck.pull2 z) := by
  obtain ⟨f, y, hf, hy, e, rfl, rfl⟩ := h
  let f' : C1 G := fun T T' φ ↦ M.α T' (f _ _ (M.fn.map φ))
  let y' : C2 G := fun T T' T'' φ ψ ↦ M.α T'' (y _ _ _ (M.fn.map φ) (M.fn.map ψ))
  have e₁ : red1 a' f' = (M.c₀.pullbackOneCocycle ⟨_, hf⟩).1 := by
    funext T T' φ; exact M.ca _ _
  have e₂ : red2 b' y' = (M.ck.pullbackTwoCocycle ⟨_, hy⟩).1 := by
    funext T T' T'' φ ψ; exact M.cb _ _
  refine ⟨f', y', e₁ ▸ (M.c₀.pullbackOneCocycle ⟨_, hf⟩).2, e₂ ▸ (M.ck.pullbackTwoCocycle ⟨_, hy⟩).2, ?_,
    congrArg _ (Subtype.ext e₁), congrArg _ (Subtype.ext e₂)⟩
  funext T T' T'' φ ψ
  have k := congrFun (congrFun (congrFun (congrFun (congrFun e _) _) _) (M.fn.map φ)) (M.fn.map ψ)
  have k' := congrArg (M.α T'') k
  simp only [d1_apply, Pi.smul_apply, map_add, map_sub, M.smul, ← Functor.map_comp, M.nat] at k'
  exact k'

end Abstract

section Lattice

open GlobalTheory.CompanionTheory.SysBC

instance affLat {X : Scheme.{0}} [X.IsSeparated] : SemilatticeInf X.affineOpens :=
  { (inferInstance : PartialOrder X.affineOpens) with
    inf := fun U V ↦ ⟨U.1 ⊓ V.1, U.2.inf V.2⟩
    inf_le_left := fun U V ↦ (inf_le_left : U.1 ⊓ V.1 ≤ U.1)
    inf_le_right := fun U V ↦ (inf_le_right : U.1 ⊓ V.1 ≤ V.1)
    le_inf := fun U V W h₁ h₂ ↦ (le_inf h₁ h₂ : U.1 ≤ V.1 ⊓ W.1) }

instance pairLat {X X' : Scheme.{0}} [X.IsSeparated] [X'.IsSeparated] (φ : X' ⟶ X) :
    SemilatticeInf (Pair φ) :=
  Subtype.semilatticeInf fun p q hp hq ↦
    (le_inf (inf_le_left.trans hp) (inf_le_right.trans hq) :
      p.1.1 ⊓ q.1.1 ≤ φ ⁻¹ᵁ p.2.1 ⊓ φ ⁻¹ᵁ q.2.1)

def idSys (X : Scheme.{0}) [X.IsSeparated] : Sys X X.affineOpens where
  u := id
  map_inf _ _ := rfl
  cover := iSup_affineOpens_eq_top X

def pairSys {X X' : Scheme.{0}} [X.IsSeparated] [X'.IsSeparated] (φ : X' ⟶ X) : Sys X' (Pair φ) where
  u p := p.1.1
  map_inf _ _ := rfl
  cover := by
    refine top_le_iff.1 fun x _ ↦ ?_
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := φ x) (U := ⊤) trivial
    obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X') (x := x) (U := φ ⁻¹ᵁ U) hxU
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨W, hW⟩, ⟨U, hU⟩), hle⟩, hxW⟩

end Lattice

section Levels

open GlobalTheory.CompanionTheory.SysBC

variable {X Y : Scheme.{0}} [X.IsSeparated] [Y.IsSeparated]
  {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X' Y' : Scheme.{0}}
  {s : X ⟶ Sp R} {u : Y ⟶ Sp R} {s' : X' ⟶ Sp R'} {u' : Y' ⟶ Sp R'}
  {φ : X' ⟶ X} {ψ : Y' ⟶ Y} {f : Y ⟶ X} {f' : Y' ⟶ X'}

def thO (hX : IsPullback φ s' s (spMap (algebraMap R R'))) (hY : IsPullback ψ u' u (spMap (algebraMap R R')))
    (e : ψ ≫ f = f' ≫ φ) (p : Pair f) : Pair f' :=
  ⟨((pullSys hY (pairSys f)).u p, (pullSys hX (idSys X)).u p.1.2), fun x hx ↦ by
    have h1 : ψ x ∈ p.1.1.1 := hx
    have h2 : f (ψ x) ∈ p.1.2.1 := p.2 h1
    have h3 : (ψ ≫ f) x ∈ p.1.2.1 := by simpa using h2
    rw [e] at h3
    have h4 : φ (f' x) ∈ p.1.2.1 := by simpa using h3
    exact h4⟩

def thFn (hX : IsPullback φ s' s (spMap (algebraMap R R'))) (hY : IsPullback ψ u' u (spMap (algebraMap R R')))
    (e : ψ ≫ f = f' ≫ φ) : (Pair f)ᵒᵖ ⥤ (Pair f')ᵒᵖ :=
  (Monotone.functor (f := thO hX hY e) fun p q h ↦
    Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(pullSys hY (pairSys f)).mono h,
      (pullSys hX (idSys X)).mono (Pair.le_snd h)⟩)).op

def th (hX : IsPullback φ s' s (spMap (algebraMap R R'))) (hY : IsPullback ψ u' u (spMap (algebraMap R R')))
    (e : ψ ≫ f = f' ≫ φ) :
    CoefMap (RingHom.id R') (OPair f' u') (OSys u' (pullSys hY (pairSys f))) where
  G := thFn hX hY e
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def pcL (hX : IsPullback φ s' s (spMap (algebraMap R R'))) (hY : IsPullback ψ u' u (spMap (algebraMap R R')))
    (e : ψ ≫ f = f' ≫ φ) (w' : f' ≫ s' = u' ≫ spMap (RingHom.id R')) :
    CoefMap (RingHom.id R') (OSys s' (pullSys hX (idSys X))) (OSys u' (pullSys hY (pairSys f))) where
  G := pairSnd f
  α p := GlobalTheory.CechDR.secPull s' u' (thO hX hY e p.unop)
  naturality a b := (pairPull w').naturality ((thFn hX hY e).map a) b
  smul p := (pairPull w').smul (op (thO hX hY e p.unop))

def rsL (f : Y ⟶ X) (hY : IsPullback ψ u' u (spMap (algebraMap R R'))) :
    CoefMap (RingHom.id R') (OSys u' (pullSys hY (idSys Y))) (OSys u' (pullSys hY (pairSys f))) where
  G := pairFst f
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def pcR (w : f ≫ s = u ≫ spMap (RingHom.id R)) :
    CoefMap (RingHom.id R) (OSys s (idSys X)) (OSys u (pairSys f)) where
  G := pairSnd f
  α p := GlobalTheory.CechDR.secPull s u p.unop
  naturality a b := (pairPull w).naturality a b
  smul p := (pairPull w).smul p

def rsR (f : Y ⟶ X) (u : Y ⟶ Sp R) : CoefMap (RingHom.id R) (OSys u (idSys Y)) (OSys u (pairSys f)) where
  G := pairFst f
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem th_pull1_pairPull (hX : IsPullback φ s' s (spMap (algebraMap R R')))
    (hY : IsPullback ψ u' u (spMap (algebraMap R R'))) (e : ψ ≫ f = f' ≫ φ)
    (w' : f' ≫ s' = u' ≫ spMap (RingHom.id R')) (c : HO1 s') :
    (th hX hY e).pull1 ((pairPull w').pull1 c) =
      (pcL hX hY e w').pull1 ((resSys s' (pullSys hX (idSys X))).pull1 c) := by
  obtain ⟨g, rfl⟩ := H1.mk_surjective _ c
  rfl

theorem th_pull1_pairRes (hX : IsPullback φ s' s (spMap (algebraMap R R')))
    (hY : IsPullback ψ u' u (spMap (algebraMap R R'))) (e : ψ ≫ f = f' ≫ φ) (c : HO1 u') :
    (th hX hY e).pull1 ((pairRes f' u').pull1 c) =
      (rsL f hY).pull1 ((resSys u' (pullSys hY (idSys Y))).pull1 c) := by
  obtain ⟨g, rfl⟩ := H1.mk_surjective _ c
  rfl

theorem th_pull2_pairPull (hX : IsPullback φ s' s (spMap (algebraMap R R')))
    (hY : IsPullback ψ u' u (spMap (algebraMap R R'))) (e : ψ ≫ f = f' ≫ φ)
    (w' : f' ≫ s' = u' ≫ spMap (RingHom.id R')) (c : H2 (OAff s')) :
    (th hX hY e).pull2 ((pairPull w').pull2 c) =
      (pcL hX hY e w').pull2 ((resSys s' (pullSys hX (idSys X))).pull2 c) := by
  obtain ⟨g, rfl⟩ := H2.mk_surjective _ c
  rfl

theorem th_pull2_pairRes (hX : IsPullback φ s' s (spMap (algebraMap R R')))
    (hY : IsPullback ψ u' u (spMap (algebraMap R R'))) (e : ψ ≫ f = f' ≫ φ) (c : H2 (OAff u')) :
    (th hX hY e).pull2 ((pairRes f' u').pull2 c) =
      (rsL f hY).pull2 ((resSys u' (pullSys hY (idSys Y))).pull2 c) := by
  obtain ⟨g, rfl⟩ := H2.mk_surjective _ c
  rfl

theorem th_pull2_pairRes' (hX : IsPullback φ s' s (spMap (algebraMap R R')))
    (hY : IsPullback ψ u' u (spMap (algebraMap R R'))) (e : ψ ≫ f = f' ≫ φ) (c : H2 (OAff u')) :
    (th hX hY e).pull2 ((pairRes f' u').pull2 c) =
      (resSys u' (pullSys hY (pairSys f))).pull2 c := by
  obtain ⟨g, rfl⟩ := H2.mk_surjective _ c
  rfl

theorem res_bij (hD : DescentSt) (hL : LowSt) {Z : Scheme.{0}} (z : Z ⟶ Sp R) (hz : IsSeparated z)
    {P : Type} [SemilatticeInf P] (S : Sys Z P) :
    Function.Bijective (resSys z S).pull1 ∧ Function.Bijective (resSys z S).pull2 :=
  ⟨(hL _ _ _ _ _ _ (hD R Z z hz P S)).1, (hL _ _ _ _ _ _ (hD R Z z hz P S)).2.1⟩

theorem isPullback_second_cohomology_of_eq [X'.IsSeparated] [Y'.IsSeparated] (hD : DescentSt) (hL : LowSt) (hu : IsSeparated u')
    (hX : IsPullback φ s' s (spMap (algebraMap R R')))
    (hY : IsPullback ψ u' u (spMap (algebraMap R R'))) (e : ψ ≫ f = f' ≫ φ)
    (w' : f' ≫ s' = u' ≫ spMap (RingHom.id R')) {z : H2 (OAff s')} {y : H2 (OAff u')}
    (h : (pcL hX hY e w').pull2 ((resSys s' (pullSys hX (idSys X))).pull2 z) =
      (rsL f hY).pull2 ((resSys u' (pullSys hY (idSys Y))).pull2 y)) : IsPullbackH2Structure w' z y := by
  have b₁ : Function.Bijective (pairRes f' u').pull2 := (res_bij hD hL u' hu (pairSys f')).2
  have b₂ := (res_bij hD hL u' hu (pullSys hY (pairSys f))).2
  obtain ⟨x, hx⟩ := b₁.2 ((pairPull w').pull2 z)
  have k : x = y := b₂.1 (by
    rw [← th_pull2_pairRes' hX hY e x, hx, th_pull2_pairPull hX hY e w', h,
      ← th_pull2_pairRes hX hY e y, th_pull2_pairRes' hX hY e y])
  exact hx.symm.trans (congrArg _ k)

end Levels

section Tri

open GlobalTheory.CompanionTheory.SysBC

variable {X Y : Scheme.{0}} [X.IsSeparated] [Y.IsSeparated]
  {R R₀ K : Type} [CommRing R] [CommRing R₀] [CommRing K] [Algebra R R₀] [Algebra R K]
  {X₀ Y₀ Xk Yk : Scheme.{0}} {s : X ⟶ Sp R} {u : Y ⟶ Sp R} {s₀ : X₀ ⟶ Sp R₀} {u₀ : Y₀ ⟶ Sp R₀}
  {sk : Xk ⟶ Sp K} {uk : Yk ⟶ Sp K} {φ₀ : X₀ ⟶ X} {ψ₀ : Y₀ ⟶ Y} {φk : Xk ⟶ X} {ψk : Yk ⟶ Y}
  {f : Y ⟶ X} {f₀ : Y₀ ⟶ X₀} {fk : Yk ⟶ Xk}

theorem appLE_sq {A B C D : Scheme.{0}} {a : B ⟶ A} {b : C ⟶ B} {c : D ⟶ A} {d : C ⟶ D} (e : b ≫ a = d ≫ c)
    {U : A.Opens} {V : B.Opens} {W : C.Opens} {T : D.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : W ≤ b ⁻¹ᵁ V)
    (h₃ : T ≤ c ⁻¹ᵁ U) (h₄ : W ≤ d ⁻¹ᵁ T) :
    a.appLE U V h₁ ≫ b.appLE V W h₂ = c.appLE U T h₃ ≫ d.appLE T W h₄ := by
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  simp only [e]

def triP (w : f ≫ s = u ≫ spMap (RingHom.id R))
    (hX₀ : IsPullback φ₀ s₀ s (spMap (algebraMap R R₀))) (hY₀ : IsPullback ψ₀ u₀ u (spMap (algebraMap R R₀)))
    (e₀ : ψ₀ ≫ f = f₀ ≫ φ₀) (w₀ : f₀ ≫ s₀ = u₀ ≫ spMap (RingHom.id R₀))
    (hXk : IsPullback φk sk s (spMap (algebraMap R K))) (hYk : IsPullback ψk uk u (spMap (algebraMap R K)))
    (ek : ψk ≫ f = fk ≫ φk) (wk : fk ≫ sk = uk ≫ spMap (RingHom.id K)) :
    TriMap (pullBC hX₀ (idSys X)) (pullBC hXk (idSys X)) (pullBC hY₀ (pairSys f)) (pullBC hYk (pairSys f)) where
  fn := pairSnd f
  α := (pcR w).α
  α₀ := (pcL hX₀ hY₀ e₀ w₀).α
  αk := (pcL hXk hYk ek wk).α
  nat := (pcR w).naturality
  nat₀ := (pcL hX₀ hY₀ e₀ w₀).naturality
  natk := (pcL hXk hYk ek wk).naturality
  smul := (pcR w).smul
  smul₀ := (pcL hX₀ hY₀ e₀ w₀).smul
  smulk := (pcL hXk hYk ek wk).smul
  ca T x := congrArg (fun q ↦ q.hom x) (appLE_sq e₀ (a := f) (b := ψ₀) (U := T.unop.1.2.1) (V := T.unop.1.1.1)
    (W := ψ₀ ⁻¹ᵁ T.unop.1.1.1) (T := φ₀ ⁻¹ᵁ T.unop.1.2.1) T.unop.2 le_rfl le_rfl (thO hX₀ hY₀ e₀ T.unop).2)
  cb T x := congrArg (fun q ↦ q.hom x) (appLE_sq ek (a := f) (b := ψk) (U := T.unop.1.2.1) (V := T.unop.1.1.1)
    (W := ψk ⁻¹ᵁ T.unop.1.1.1) (T := φk ⁻¹ᵁ T.unop.1.2.1) T.unop.2 le_rfl le_rfl (thO hXk hYk ek T.unop).2)

def triR (f : Y ⟶ X) (hY₀ : IsPullback ψ₀ u₀ u (spMap (algebraMap R R₀)))
    (hYk : IsPullback ψk uk u (spMap (algebraMap R K))) :
    TriMap (pullBC hY₀ (idSys Y)) (pullBC hYk (idSys Y)) (pullBC hY₀ (pairSys f)) (pullBC hYk (pairSys f)) where
  fn := pairFst f
  α := (rsR f u).α
  α₀ := (rsL f hY₀).α
  αk := (rsL f hYk).α
  nat := (rsR f u).naturality
  nat₀ := (rsL f hY₀).naturality
  natk := (rsL f hYk).naturality
  smul := (rsR f u).smul
  smul₀ := (rsL f hY₀).smul
  smulk := (rsL f hYk).smul
  ca _ _ := rfl
  cb _ _ := rfl

theorem transfer {t : R} (w : f ≫ s = u ≫ spMap (RingHom.id R))
    (hX₀ : IsPullback φ₀ s₀ s (spMap (algebraMap R R₀))) (hY₀ : IsPullback ψ₀ u₀ u (spMap (algebraMap R R₀)))
    (e₀ : ψ₀ ≫ f = f₀ ≫ φ₀) (w₀ : f₀ ≫ s₀ = u₀ ≫ spMap (RingHom.id R₀))
    (hXk : IsPullback φk sk s (spMap (algebraMap R K))) (hYk : IsPullback ψk uk u (spMap (algebraMap R K)))
    (ek : ψk ≫ f = fk ≫ φk) (wk : fk ≫ sk = uk ≫ spMap (RingHom.id K))
    (ha : ExA (pullBC hY₀ (pairSys f)) t) (hb : ExB (pullBC hYk (pairSys f)) t)
    {c : HO1 s₀} {d : HO1 u₀} (hc : IsPullO w₀ c d)
    {z : H2 (OSys sk (pullSys hXk (idSys X)))} {y : H2 (OSys uk (pullSys hYk (idSys Y)))}
    (B₁ : Bd (pullBC hX₀ (idSys X)) (pullBC hXk (idSys X)) t ((resSys s₀ (pullSys hX₀ (idSys X))).pull1 c) z)
    (B₂ : Bd (pullBC hY₀ (idSys Y)) (pullBC hYk (idSys Y)) t ((resSys u₀ (pullSys hY₀ (idSys Y))).pull1 d) y) :
    (pcL hXk hYk ek wk).pull2 z = (rsL f hYk).pull2 y := by
  have k₁ := B₁.pull (triP w hX₀ hY₀ e₀ w₀ hXk hYk ek wk)
  have k₂ := B₂.pull (triR f hY₀ hYk)
  have e : (triP w hX₀ hY₀ e₀ w₀ hXk hYk ek wk).c₀.pull1 ((resSys s₀ (pullSys hX₀ (idSys X))).pull1 c) =
      (triR f hY₀ hYk).c₀.pull1 ((resSys u₀ (pullSys hY₀ (idSys Y))).pull1 d) := by
    change (pcL hX₀ hY₀ e₀ w₀).pull1 _ = (rsL f hY₀).pull1 _
    refine (th_pull1_pairPull hX₀ hY₀ e₀ w₀ c).symm.trans ?_
    rw [show (pairPull w₀).pull1 c = (pairRes f₀ u₀).pull1 d from hc]
    exact th_pull1_pairRes hX₀ hY₀ e₀ d
  rw [e] at k₁
  exact bd_unique ha hb k₁ k₂

end Tri

end GlobalTheory.CompanionTheory.SmallLift
