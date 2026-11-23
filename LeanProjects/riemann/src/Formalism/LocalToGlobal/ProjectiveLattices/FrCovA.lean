import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBCFrameR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread

noncomputable section

namespace Formalism.L2.Pj.FrCov

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

section Comb

variable {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
  {cf : Fin m → S} {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}

theorem comb_uniq (h : IsCombAt x v cf w) (h' : IsCombAt x v cf w') : w = w' := by
  unfold IsCombAt at h h'
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  have e : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [e]

def ρD (ψ : S →+* T) (x : Sp S ⟶ Xo.X) : tEps (spMap ψ ≫ x) ⟶ tEps x :=
  Over.homMk (spMap (dualMap ψ)) (by
    show spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg])

theorem eps_dual (ψ : S →+* T) (a : S) : spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

theorem comb_bc (ψ : S →+* T) (h : IsCombAt x v cf w) :
    IsCombAt (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ v j) (fun j => ψ (cf j)) (spMap (dualMap ψ) ≫ w) := by
  unfold IsCombAt at h ⊢
  obtain ⟨u, hu, rfl⟩ := h
  have key : ∀ l : List (tEps x ⟶ Xo.univ.t.G), (l.map (fun g => ρD ψ x ≫ g)).prod = ρD ψ x ≫ l.prod := by
    intro l
    induction l with
    | nil =>
      first | simp [comp_one] | simp [MonObj.comp_one] | simp [Hom.comp_one] | simp
    | cons a l ih =>
      first | simp [ih, comp_mul] | simp [ih, MonObj.comp_mul] | simp [ih, Hom.comp_mul] | simp [ih]
  refine ⟨fun i => ρD ψ x ≫ u i, fun i => ?_, ?_⟩
  · rw [Over.comp_left, hu i]
    show spMap (dualMap ψ) ≫ spMap (epsMul (cf i)) ≫ v i = _
    rw [← Category.assoc, eps_dual, Category.assoc]
  · have e2 : (List.ofFn fun i => ρD ψ x ≫ u i) = (List.ofFn u).map (fun g => ρD ψ x ≫ g) := by
      first | (rw [List.map_ofFn]; rfl) | simp [List.map_ofFn, Function.comp_def]
    rw [e2, key, Over.comp_left]
    rfl

def resM (ψ : S →+* T) (n : TanM x Xo.univ.t.G) : TanM (spMap ψ ≫ x) Xo.univ.t.G :=
  mkT (ρD ψ x ≫ tv n) (smT_zero_ovT (t := Xo.univ.t) (tan_bc ψ (isTanAtG_of (t := Xo.univ.t) (x0 := x) (tv n) (tv_mem n))))

def Full {κ : Type} [Fintype κ] (x : Sp S ⟶ Xo.X) (v : κ → TanM x Xo.univ.t.G) : Prop :=
  ∀ n : TanM x Xo.univ.t.G, ∃! a : κ → S, n = ∑ k, a k • v k

theorem full_iff {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ Xo.univ.t.G.left}
    (h : IsGrpPullback G' Xo.univ.t.G x Φ) {u : Fin m → (epsR S ⟶ G')} {v : Fin m → TanM x Xo.univ.t.G}
    (e : ∀ i, pushHom h (epsR S) (u i) = tv (v i)) : IsLieBasis u ↔ Full x v := by
  have key : ∀ a p n, pushHom h (epsR S) p = tv n → (IsLieComb a u p ↔ n = ∑ k, a k • v k) := fun a p n hp => by
    rw [isLieComb_iff h, hp]
    simp only [e]
    exact ⟨fun q => tanM_ext (q.trans (by rw [tv_sum]; rfl)), fun q => (congrArg tv q).trans (by rw [tv_sum]; rfl)⟩
  refine ⟨fun hu n => ?_, fun hv => ⟨fun i => (isTangent_iff h _).2 (by rw [e]; exact tv_mem _), fun p hp => ?_⟩⟩
  · obtain ⟨p, hp⟩ := push_surj h (tv n)
    simpa only [key _ p n hp] using hu.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem n))
  · simpa only [key _ p (mkT _ ((isTangent_iff h p).1 hp)) rfl] using hv (mkT _ ((isTangent_iff h p).1 hp))

theorem full_bc (ψ : S →+* T) {v : Fin m → TanM x Xo.univ.t.G} (hv : Full x v) : Full (spMap ψ ≫ x) fun i => resM ψ (v i) := by
  have h₀ := hS (Xo := Xo) x
  have h := hS (Xo := Xo) (spMap ψ ≫ x)
  choose u hu using fun i => push_surj h₀ (tv (v i))
  choose u' hu' using fun i => push_surj h (tv (resM ψ (v i)))
  have := Xo.univ.t.semi.smooth
  have : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  refine (full_iff h hu').1 (Chart.frameLieBCR _ ((full_iff h₀ hu).2 hv) ψ (Chart.isGrpPullback_factor x (spMap ψ) h)
    (fun a b v hv => push_inj h (by
      have := smT_add _ _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => ?_)
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc]
    exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (hu i)).symm)
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (u i)).symm)
    exact (spMap_comp_spMap _ _).trans ((congrArg spMap (dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)

end Comb

variable (hS' : Out.SecBaseChangeAnySt) (hT : Out.SecTwistSt) {R T T' : Type} [CommRing R] [Algebra c.F R] [CommRing T]
  [Algebra c.F T] [CommRing T'] [Algebra c.F T']

def bc (ψ : R →ₐ[c.F] T) (y : FrPt Xo c R) : FrPt Xo c T where
  x := spMap ψ.toRingHom ≫ y.x
  x_over := by
    rw [Category.assoc, y.x_over, sOf, sOf, spMap_comp_spMap, ← RingHom.comp_assoc]
    congr 2
    exact ψ.comp_algebraMap
  u τ i := spMap (dualMap ψ.toRingHom) ≫ y.u τ i
  tan τ i := tan_bc ψ.toRingHom (y.tan τ i)
  eig τ i := eig_bc ψ τ (y.eig τ i)
  basis := bcLieAll c ψ y
  s := secCP (cpS ψ.toRingHom y.x) y.s
  gen := genBC_frameR hS' hT y.x ψ.toRingHom y.s y.gen

abbrev Mx (Dw : Datum H) (T : Type) : Type := ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T

def Rl (y : FrPt Xo c R) (a : R →ₐ[c.F] T) (M : Mx Dw T) (t : T) (z : FrPt Xo c T) : Prop :=
  z.x = spMap a.toRingHom ≫ y.x ∧
    (∀ τ i, IsCombAt (spMap a.toRingHom ≫ y.x) (fun j => spMap (dualMap a.toRingHom) ≫ y.u τ j) (M τ i) (z.u τ i)) ∧
    ∃ pm : Gx z.x ⟶ Gx y.x, pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left ≫ spMap a.toRingHom ∧
      ∀ i, ∀ p ∈ (PPx z.x).U i, gs (𝟙 _) p _ (z.s.f i) = cst (fst (Over.mk z.x) Xo.univ.t.G).left p t * gs pm p _ (y.s.f i)

variable {y : FrPt Xo c R} {a : R →ₐ[c.F] T} {M M' N : Mx Dw T} {t t' r : T} {z z' : FrPt Xo c T} {w : FrPt Xo c T'}

theorem pm_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {Z : Scheme.{0}} {p q : Z ⟶ Gx x}
    (h₁ : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left)
    (h₂ : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left) : p = q := by
  apply pullback.hom_ext
  · first | exact h₁ | simpa using h₁
  · first | exact h₂ | simpa using h₂

theorem exists_pm {S S' : Type} [CommRing S] [CommRing S'] {x : Sp S ⟶ Xo.X} {x' : Sp S' ⟶ Xo.X} (g : Sp S' ⟶ Sp S)
    (h : x' = g ≫ x) : ∃ pm : Gx x' ⟶ Gx x, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ g := by
  subst h
  refine ⟨pullback.lift ((fst (Over.mk (g ≫ x)) Xo.univ.t.G).left ≫ g) (snd (Over.mk (g ≫ x)) Xo.univ.t.G).left ?_, ?_, ?_⟩
  · rw [Category.assoc]
    exact pullback.condition
  · exact pullback.lift_snd _ _ _
  · exact pullback.lift_fst _ _ _

theorem Rl.map (ψ : T →ₐ[c.F] T') (h : Rl y a M t z) :
    FrMap ψ z w ↔ Rl y (ψ.comp a) (fun τ => (M τ).map ψ) (ψ t) w := by
  obtain ⟨hx, hu, pm, s₁, f₁, v₁⟩ := h
  have cb := fun τ i => comb_bc ψ.toRingHom (hu τ i)
  simp only [← Category.assoc, ← spMap_algHom_comp, ← spMap_dual_comp] at cb
  have val : ∀ q : Gx w.x ⟶ Gx z.x, q ≫ (snd (Over.mk z.x) Xo.univ.t.G).left = (snd (Over.mk w.x) Xo.univ.t.G).left →
      q ≫ (fst (Over.mk z.x) Xo.univ.t.G).left = (fst (Over.mk w.x) Xo.univ.t.G).left ≫ spMap ψ.toRingHom → ∀ i,
      ∀ p ∈ (PPx w.x).U i, gs q p _ (z.s.f i) = cst (fst (Over.mk w.x) Xo.univ.t.G).left p (ψ t) * gs (q ≫ pm) p _ (y.s.f i) :=
    fun q s₂ f₂ i p hp => by
      have m := ppx_le_cov q s₂ i hp
      rw [gs_stalkMap q p _ m, v₁ i _ m, map_mul, cst_stalkMap, f₂, cst_comp, ← gs_comp q pm p _ (ppx_le_cov pm s₁ i m)]; rfl
  constructor
  · rintro ⟨hx₂, hu₂, q, s₂, f₂, v₂⟩
    refine ⟨by rw [hx₂, hx, spMap_algHom_comp, Category.assoc], fun τ i => (hu₂ τ i).symm ▸ cb τ i, q ≫ pm,
      by rw [Category.assoc, s₁, s₂], by rw [Category.assoc, f₁, ← Category.assoc, f₂, Category.assoc, spMap_algHom_comp],
      fun i p hp => ?_⟩
    rw [← val q s₂ f₂ i p hp, ← v₂ i (ppx_le_cov q s₂ i), gs_appLE q _ _ _ (𝟙 _) p hp, Category.id_comp]
  · rintro ⟨hx₂, hu₂, pm₂, s₂, f₂, v₂⟩
    have e : w.x = spMap ψ.toRingHom ≫ z.x := by rw [hx₂, hx, spMap_algHom_comp, Category.assoc]
    obtain ⟨q, s₃, f₃⟩ := exists_pm _ e
    refine ⟨e, fun τ i => comb_uniq (hu₂ τ i) (cb τ i), q, s₃, f₃, fun i h => fn_ext fun p hp => ?_⟩
    rw [gs_appLE q _ _ _ (𝟙 _) p hp, Category.id_comp, val q s₃ f₃ i p hp, v₂ i p hp, show q ≫ pm = pm₂ from pm_ext
      (by rw [Category.assoc, f₁, ← Category.assoc, f₃, f₂, Category.assoc, spMap_algHom_comp]) (by rw [Category.assoc, s₁, s₃, s₂])]

theorem comb_tv (h : Rl y a M t z) (τ i) (hz : IsTanAt (spMap a.toRingHom ≫ y.x) (z.u τ i)) :
    tvOf hz = ∑ j, M τ i j • tvOf (tan_bc a.toRingHom (y.tan τ j)) := (combAt_iff _ _ _ hz).1 (h.2.1 τ i)

theorem Rl.bor (h : Rl y a M t z) (hx : z'.x = z.x) :
    ((∀ τ i, IsCombAt z.x (z.u τ) (N τ i) (z'.u τ i)) ∧ ∃ pm : Gx z'.x ⟶ Gx z.x,
      pm ≫ (snd (Over.mk z.x) Xo.univ.t.G).left = (snd (Over.mk z'.x) Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk z.x) Xo.univ.t.G).left = (fst (Over.mk z'.x) Xo.univ.t.G).left ∧
      ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z'.x).U i ≤ pm ⁻¹ᵁ (PPx z.x).U i),
        (pm.appLE _ _ h).hom (scal z.x r i * z.s.f i) = z'.s.f i) ↔ Rl y a (fun τ => N τ * M τ) (r * t) z' := by
  have tz : ∀ τ i, IsTanAt (spMap a.toRingHom ≫ y.x) (z.u τ i) := fun τ i => h.1 ▸ z.tan τ i
  have tz' : ∀ τ i, IsTanAt (spMap a.toRingHom ≫ y.x) (z'.u τ i) := fun τ i => (hx.trans h.1) ▸ z'.tan τ i
  have cb : ∀ τ i, IsCombAt z.x (z.u τ) (N τ i) (z'.u τ i) ↔ IsCombAt (spMap a.toRingHom ≫ y.x)
      (fun j => spMap (dualMap a.toRingHom) ≫ y.u τ j) ((N τ * M τ) i) (z'.u τ i) := fun τ i => by
    rw [h.1, combAt_iff _ (tz τ) _ (tz' τ i), combAt_iff _ (fun j => tan_bc a.toRingHom (y.tan τ j)) _ (tz' τ i)]
    simp only [comb_tv h τ _ (tz τ _), Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  obtain ⟨hx₁, -, pm, s₁, f₁, v₁⟩ := h
  have val : ∀ q : Gx z'.x ⟶ Gx z.x, q ≫ (snd (Over.mk z.x) Xo.univ.t.G).left = (snd (Over.mk z'.x) Xo.univ.t.G).left →
      q ≫ (fst (Over.mk z.x) Xo.univ.t.G).left = (fst (Over.mk z'.x) Xo.univ.t.G).left → ∀ i, ∀ p ∈ (PPx z'.x).U i,
      gs q p _ (scal z.x r i * z.s.f i) = cst (fst (Over.mk z'.x) Xo.univ.t.G).left p (r * t) * gs (q ≫ pm) p _ (y.s.f i) :=
    fun q s₂ f₂ i p hp => by
      have m := ppx_le_cov q s₂ i hp
      rw [gs_mul q p _ m, gs_scal z.x r i q p m, gs_stalkMap q p _ m, v₁ i _ m, map_mul, cst_stalkMap, f₂,
        ← gs_comp q pm p _ (ppx_le_cov pm s₁ i m), cst_mul, _root_.mul_assoc]
  constructor
  · rintro ⟨hu, q, s₂, f₂, v₂⟩
    refine ⟨hx.trans hx₁, fun τ i => (cb τ i).1 (hu τ i), q ≫ pm, by rw [Category.assoc, s₁, s₂],
      by rw [Category.assoc, f₁, ← Category.assoc, f₂], fun i p hp => ?_⟩
    rw [← val q s₂ f₂ i p hp, ← v₂ i (ppx_le_cov q s₂ i), gs_appLE q _ _ _ (𝟙 _) p hp, Category.id_comp]
  · rintro ⟨-, hu, pm₂, s₂, f₂, v₂⟩
    obtain ⟨q, s₃, f₃⟩ := exists_pm (𝟙 _) (hx.trans (Category.id_comp _).symm)
    replace f₃ := f₃.trans (Category.comp_id _)
    refine ⟨fun τ i => (cb τ i).2 (hu τ i), q, s₃, f₃, fun i h => fn_ext fun p hp => ?_⟩
    rw [gs_appLE q _ _ _ (𝟙 _) p hp, Category.id_comp, val q s₃ f₃ i p hp, v₂ i p hp, show q ≫ pm = pm₂ from pm_ext
      (by rw [Category.assoc, f₁, ← Category.assoc, f₃, f₂]) (by rw [Category.assoc, s₁, s₃, s₂])]

include hS' hT

theorem bc_val (pm : Gx z.x ⟶ Gx y.x) (hx : z.x = spMap a.toRingHom ≫ y.x)
    (s₁ : pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left)
    (f₁ : pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left ≫ spMap a.toRingHom) :
    ∃ s : LB.Sec (PPx z.x), (∀ i, ∀ p ∈ (PPx z.x).U i, gs (𝟙 _) p _ (s.f i) = gs pm p _ (y.s.f i)) ∧
      ∀ s' : LB.Sec (PPx z.x), ∃! b : T, ∀ i, s'.f i = scal z.x b i * s.f i := by
  obtain ⟨x, _, _, _, _, _, _, _⟩ := z
  subst hx
  obtain rfl : pm = bcPm a.toRingHom y.x := pm_ext (f₁.trans (bcPm_fst _ _).symm) (s₁.trans (bcPm_snd _ _).symm)
  exact ⟨(bc hS' hT a y).s, fun i p hp => (gs_secCP _ _ (𝟙 _) p i hp).trans (by rw [Category.id_comp]; rfl), (bc hS' hT a y).gen⟩

theorem Rl.uniq (h : Rl y a M t z) (h' : Rl y a M' t' z) : M = M' ∧ t = t' := by
  refine ⟨funext fun τ => funext fun i => ((bc hS' hT a y).basis τ _
    (show IsTanAt (spMap a.toRingHom ≫ y.x) _ from h.1 ▸ z.tan τ i) (z.eig τ i)).unique (h.2.1 τ i) (h'.2.1 τ i), ?_⟩
  obtain ⟨hx, -, pm, s₁, f₁, v₁⟩ := h
  obtain ⟨-, -, pm', s₂, f₂, v₂⟩ := h'
  obtain rfl : pm = pm' := pm_ext (f₁.trans f₂.symm) (s₁.trans s₂.symm)
  obtain ⟨s, hs, g⟩ := bc_val hS' hT pm hx s₁ f₁
  exact (g z.s).unique ((scal_eq_iff _ _ _ _).2 fun i p hp => by rw [hs i p hp, v₁ i p hp])
    ((scal_eq_iff _ _ _ _).2 fun i p hp => by rw [hs i p hp, v₂ i p hp])

theorem exists_pt (y : FrPt Xo c R) (a : R →ₐ[c.F] T) (M : Mx Dw T) (hM : ∀ τ, IsUnit (M τ).det) (t : Tˣ) : ∃ z, Rl y a M t z := by
  let b := bc hS' hT a y
  let n := fun τ i => ∑ j, M τ i j • tvOf (b.tan τ j)
  have tn := fun τ i => isTanAtG_of (t := Xo.univ.t) (x0 := b.x) (tv (n τ i)) (tv_mem _)
  let s : LB.Sec (PPx b.x) := DVR.SecOps.secScale ((fst (Over.mk b.x) Xo.univ.t.G).left.appTop.hom (toΓ T (t : T))) b.s
  have hs : ∀ i, s.f i = scal b.x (t : T) i * b.s.f i := fun _ => rfl
  refine ⟨⟨b.x, b.x_over, fun τ i => (tv (n τ i)).left, tn, fun τ i => (eigAt_iff c (tn τ i) τ).2 ((tvOf_tv (n τ i)).symm ▸
    eig_comb τ _ (fun j => (eigAt_iff c (b.tan τ j) τ).1 (b.eig τ j)) (M τ i)), fun τ w hw he => ?_, s, fun s' => ?_⟩, rfl,
    fun τ i => (combAt_iff _ (b.tan τ) _ (tn τ i)).2 (tvOf_tv _), bcPm a.toRingHom y.x, bcPm_snd _ _, bcPm_fst _ _, fun i p hp => ?_⟩
  · simp only [combAt_iff _ (tn τ) _ hw, tvOf_tv]
    have hs : ∀ d, ∑ i, d i • n τ i = ∑ k, Matrix.vecMul d (M τ) k • tvOf (b.tan τ k) := fun d => by
      simp only [n, Matrix.vecMul, dotProduct, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    obtain ⟨r, hr, hu⟩ := eig_coords b τ _ ((eigAt_iff c hw τ).1 he)
    refine ⟨Matrix.vecMul r (M τ)⁻¹, ?_, fun d hd => ?_⟩
    · exact hr.trans (Eq.symm ((hs _).trans (by rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hM τ), Matrix.vecMul_one])))
    · rw [← hu _ (hd.trans (hs d)), Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (hM τ), Matrix.vecMul_one]
  · obtain ⟨r, hr, hu⟩ := b.gen s'
    have k : ∀ d : T, (∀ i, s'.f i = scal b.x d i * s.f i) ↔ ∀ i, s'.f i = scal b.x (d * t) i * b.s.f i := fun d => by
      rw [scal_eq_iff, scal_eq_iff]
      refine forall_congr' fun i => forall_congr' fun p => forall_congr' fun hp => ?_
      rw [(scal_eq_iff _ _ _ _).1 hs i p hp, cst_mul, _root_.mul_assoc]
    exact ⟨r * ↑t⁻¹, (k _).2 (by rwa [Units.inv_mul_cancel_right]), fun d hd => (Units.eq_mul_inv_iff_mul_eq t).2 (hu _ ((k d).1 hd))⟩
  · exact ((scal_eq_iff _ _ _ _).1 hs i p hp).trans (congrArg _ ((gs_secCP (cpS a.toRingHom y.x) y.s (𝟙 _) p i hp).trans
      (congrArg (fun q => gs q p _ (y.s.f i)) (Category.id_comp _))))

end Formalism.L2.Pj.FrCov
