import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilLocalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapSnd
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullbackPointsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingTransportRelationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianOfPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualNumberSectionDerivationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackSmoothStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtPull

theorem deriv_gen {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
    {E : Type} [AddCommGroup E] [Module Ω E] {M : LieModel G ξ E} {A : Type} [CommRing A] {g : A →+* Ω}
    (hg : Function.Injective g) {x : Spec (CommRingCat.of A) ⟶ X} (hx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ)
    {W : G.left.Opens} (s : Γ(G.left, W)) (hin : ∀ v : epsAt x ⟶ G, IsTanAt G x v → ⊤ ≤ v.left ⁻¹ᵁ W)
    {r : ℕ} {B : Fin r → E} {v : Fin r → (epsAt x ⟶ G)}
    (hl : ∀ e u, LiePull.Ext g x M e u → e ∈ Submodule.span g.range (Set.range B))
    (hv : ∀ k, LiePull.Ext g x M (B k) (v k)) (hk : ∀ k, ⊤ ≤ (v k).left ⁻¹ᵁ W) {e : E} {u : epsAt x ⟶ G}
    (h : ⊤ ≤ u.left ⁻¹ᵁ W) (hu : LiePull.Ext g x M e u) :
    ∃ a : Fin r → A, e = ∑ k, g (a k) • B k ∧
      (secVal (B := DualNumber A) u.left W h s).snd = ∑ k, a k * (secVal (B := DualNumber A) (v k).left W (hk k) s).snd := by
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : LieModel G x (LiePull.ExtE hx M), ∀ l, M₀.pt l = LiePull.vec l :=
    ⟨LiePull.extModel hg hx M, fun _ => rfl⟩
  have hin₀ : ∀ l, ⊤ ≤ (M₀.pt l).left ⁻¹ᵁ W := fun l => hin _ (M₀.tan l)
  obtain ⟨D, hD⟩ := GlobalTheory.T.dual_number_section_derivation X G A x (LiePull.ExtE hx M) M₀ W hin₀ s
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hl e u hu)
  choose a ha using fun k => (c k).2
  let b : Fin r → LiePull.ExtE hx M := fun k => ⟨B k, v k, hv k⟩
  let y : LiePull.ExtE hx M := ⟨e, u, hu⟩
  have hce : e = ∑ k, g (a k) • B k := by
    rw [← hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ha k]
    rfl
  have hy : y = ∑ k, a k • b k := by
    apply LiePull.val_inj
    rw [map_sum]
    refine hce.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [LiePull.val_smul]
    rfl
  have hyu : M₀.pt y = u := (hM₀ y).trans ((LiePull.vec_spec y).unique hg hu)
  have hbv : ∀ k, M₀.pt (b k) = v k := fun k => (hM₀ (b k)).trans ((LiePull.vec_spec (b k)).unique hg (hv k))
  refine ⟨a, hce, ?_⟩
  have key : ∀ (p p' : epsAt x ⟶ G), p = p' → ∀ (h₁ : ⊤ ≤ p.left ⁻¹ᵁ W) (h₂ : ⊤ ≤ p'.left ⁻¹ᵁ W),
      (secVal (B := DualNumber A) p.left W h₁ s).snd = (secVal (B := DualNumber A) p'.left W h₂ s).snd := by
    rintro p _ rfl h₁ h₂
    rfl
  have e₁ : (secVal (B := DualNumber A) u.left W h s).snd = D y :=
    (key _ _ hyu.symm h (hin₀ y)).trans (hD y).symm
  have e₂ : ∀ k, D (b k) = (secVal (B := DualNumber A) (v k).left W (hk k) s).snd := fun k =>
    (hD (b k)).trans (key _ _ (hbv k) (hin₀ (b k)) (hk k))
  refine e₁.trans ?_
  rw [hy, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, e₂ k]

theorem deriv : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (q : Cpt ξ) (r : ℕ) (B : Fin r → E) (v : Fin r → (epsAt (X.fromSpecStalk q.1) ⟶ G)), M.lat q = Submodule.span (regAt ξ q) (Set.range B) → (∀ k, M.Extends q (B k) (v k)) → ∀ (W : G.left.Opens), (η[G]).left q.1 ∈ W → ∀ (s : Γ(G.left, W)) (hk : ∀ k, ⊤ ≤ (v k).left ⁻¹ᵁ W) (e : E) (u : epsAt (X.fromSpecStalk q.1) ⟶ G) (h : ⊤ ≤ u.left ⁻¹ᵁ W), M.Extends q e u → ∃ a : Fin r → X.presheaf.stalk q.1, e = ∑ k, genMap ξ q (a k) • B k ∧ (secVal (B := DualNumber (X.presheaf.stalk q.1)) u.left W h s).snd = ∑ k, a k * (secVal (B := DualNumber (X.presheaf.stalk q.1)) (v k).left W (hk k) s).snd := by
  intro X Ω _ ξ hξ G _ _ E _ _ M q r B v hl hv W hW s hk e u h hu
  exact deriv_gen (g := genMap ξ q) (hξ.inj q) (LieCarrier.genMap_fromSpecStalk (ξ := ξ) q) s
    (fun t ht => tanin X G q.1 t ht W hW) (fun e' u' hu' => by
      have : e' ∈ M.lat q := Submodule.subset_span ⟨u', hu'⟩
      rw [hl] at this
      exact this) hv hk h hu

theorem om_pull {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} (hξ : IsCptGen ξ) (hξ' : IsCptGen ξ') {f : X' ⟶ X} {i : Ω →+* Ω'}
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) {G : Over X} [GrpObj G] [IsCommMonObj G] {G' : Over X'} [GrpObj G']
    [IsCommMonObj G'] {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (hs : Smooth G.hom)
    {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {E' : Type} [AddCommGroup E'] [Module Ω' E']
    (M' : LieModel G' ξ' E') (j : E →+ E') (jd : Module.Dual Ω E →+ Module.Dual Ω' E')
    (hj : ∀ v, (M'.pt (j v)).left ≫ φ = spMap (dualMap i) ≫ (M.pt v).left)
    (hjd : ∀ w v, jd w (j v) = i (w v)) : M'.omLat = M.omLat.pull ξ' f jd := by
  funext q'
  obtain ⟨r, B, B', v, v', hBB, hl, hl', hv, hv', hvv⟩ :=
    GlobalTheory.T.lie_model_pullback_smooth X X' Ω Ω' ξ ξ' hξ hξ' f i hd G G' φ hp hs E M E' M' j hj q'
  obtain ⟨h', hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q'
  rw [Lat.pull_apply _ hd]
  have hcoord : ∀ k, B.coord k ∈ M.omLat ⟨f q'.1, hd.specializes q'⟩ := by
    intro k e he
    rw [hl] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => simpa using zero_mem _
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      have : (B.coord k) (a • x) = (a : Ω) * (B.coord k) x := by
        rw [show a • x = (a : Ω) • x from rfl, map_smul, smul_eq_mul]
      rw [this]
      exact mul_mem a.2 hx
  have hdual : ∀ k, jd (B.coord k) = B'.coord k := by
    intro k
    apply B'.ext
    intro l
    rw [hBB l, hjd, ← hBB l]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  apply le_antisymm
  · intro w' hw'
    have hmem : ∀ k, w' (B' k) ∈ regAt ξ' q' := fun k =>
      hw' (B' k) (by rw [hl']; exact Submodule.subset_span ⟨k, rfl⟩)
    have hsum : w' = ∑ k, w' (B' k) • jd (B.coord k) := by
      apply B'.ext
      intro l
      simp only [hdual, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
      simp
    rw [hsum]
    refine Submodule.sum_mem _ fun k _ => ?_
    exact Submodule.smul_mem _ (⟨w' (B' k), hmem k⟩ : regAt ξ' q')
      (Submodule.subset_span ⟨B.coord k, hcoord k, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    intro e' he'
    rw [hl'] at he'
    induction he' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [hBB l, hjd]
      exact hreg _ (hw (B l) (by rw [hl]; exact Submodule.subset_span ⟨l, rfl⟩))
    | zero => simpa using zero_mem _
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      have : (jd w) (a • x) = (a : Ω') * (jd w) x := by
        rw [show a • x = (a : Ω') • x from rfl, map_smul, smul_eq_mul]
      rw [this]
      exact mul_mem a.2 hx

theorem ht_pull {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} (hξ : IsCptGen ξ) (hξ' : IsCptGen ξ') {f : X' ⟶ X} {i : Ω →+* Ω'}
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) {G : Over X} [GrpObj G] [IsCommMonObj G] {G' : Over X'} [GrpObj G']
    [IsCommMonObj G'] {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (hs : Smooth G.hom)
    {L : LB G.left} {n : ℕ} {e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ} (he : GenWeil G L ξ n e)
    (hF : FullTorsion G ξ n) (hF' : FullTorsion G' ξ' n)
    {L' : LB G'.left} {e' : (Over.mk ξ' ⟶ G') → (Over.mk ξ' ⟶ G') → Ω'ˣ} (he' : GenWeil G' L' ξ' n e')
    (t1 : ∀ (g : Over.mk ξ ⟶ G), g ^ n = 1 → ∃ g' : Over.mk ξ' ⟶ G', g' ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left)
    (t2 : ∀ (g' : Over.mk ξ' ⟶ G'), g' ^ n = 1 → ∃ g : Over.mk ξ ⟶ G, g ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left)
    {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {E' : Type} [AddCommGroup E'] [Module Ω' E']
    (M' : LieModel G' ξ' E') (j : E →+ E') (jd : Module.Dual Ω E →+ Module.Dual Ω' E')
    (hj : ∀ v, (M'.pt (j v)).left ≫ φ = spMap (dualMap i) ≫ (M.pt v).left)
    (hjd : ∀ w v, jd w (j v) = i (w v)) (q' : Cpt ξ') {y : Over.mk ξ ⟶ G} {y' : Over.mk ξ' ⟶ G'}
    (hy : y ^ n = 1) (hy' : y' ^ n = 1)
    (hc : ∀ (g : Over.mk ξ ⟶ G) (g' : Over.mk ξ' ⟶ G'), g ^ n = 1 → g' ^ n = 1 → g'.left ≫ φ = spMap i ≫ g.left →
      (e' y' g' : Ω') = i (e y g)) {w : Module.Dual Ω E}
    (hw : M.IsHTAt L n y ⟨f q'.1, hd.specializes q'⟩ w) : M'.IsHTAt L' n y' q' (jd w) := by
  obtain ⟨hwω, W, s, hη, hT, hD⟩ := hw
  obtain ⟨r, B, B', v, v', hBB, hl, hl', hv, hv', hvv⟩ :=
    GlobalTheory.T.lie_model_pullback_smooth X X' Ω Ω' ξ ξ' hξ hξ' f i hd G G' φ hp hs E M E' M' j hj q'
  obtain ⟨h', hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q'
  have hom := om_pull hξ hξ' hd hp hs M M' j jd hj hjd
  have hη' : (η[G']).left q'.1 ∈ φ ⁻¹ᵁ W := by
    have e₁ : (η[G']).left ≫ φ = f ≫ (η[G]).left := eta X X' G G' f φ hp
    have e₂ : φ ((η[G']).left q'.1) = (η[G]).left (f q'.1) := by
      have := congrArg (fun g : X' ⟶ G.left => g q'.1) e₁
      simpa using this
    show φ ((η[G']).left q'.1) ∈ W
    rw [e₂]
    exact hη
  refine ⟨?_, φ ⁻¹ᵁ W, φ.app W s, hη', ?_, ?_⟩
  · rw [hom, Lat.pull_apply _ hd]
    exact Submodule.subset_span ⟨w, hwω, rfl⟩
  · exact GlobalTheory.T.weil_pairing_pullback X X' Ω Ω' ξ ξ' f i hd G L n e he hF G' φ hp hF' L' e' he' y y' hy hy' hc t1 t2 W s hT
  · intro e₀ u hu h
    have hk : ∀ k, ⊤ ≤ (v' k).left ⁻¹ᵁ (φ ⁻¹ᵁ W) := fun k => tanin X' G' q'.1 (v' k) (hv' k).1 _ hη'
    have hk₀ : ∀ k, ⊤ ≤ (v k).left ⁻¹ᵁ W := fun k => tanin X G (f q'.1) (v k) (hv k).1 _ hη
    obtain ⟨a, rfl, hsum⟩ := deriv X' Ω' ξ' hξ' G' E' M' q' r B' v' hl' hv' (φ ⁻¹ᵁ W) hη' (φ.app W s) hk e₀ u h hu
    have hcomp : ∀ k, (secVal (B := DualNumber (X'.presheaf.stalk q'.1)) (v' k).left (φ ⁻¹ᵁ W) (hk k) (φ.app W s)).snd =
        (f.stalkMap q'.1).hom (secVal (B := DualNumber (X.presheaf.stalk (f q'.1))) (v k).left W (hk₀ k) s).snd := by
      intro k
      exact (congrArg TrivSqZeroExt.snd (comp_ring (dualMap (f.stalkMap q'.1).hom) (v' k).left (v k).left φ (hvv k) W (hk k) (hk₀ k) s)).trans (dualMap_snd _ _)
    choose ρ hρ hρe using fun k => hD (B k) (v k) (hv k) (hk₀ k)
    have hρ' := fun k => hreg _ (hρ k)
    have hρe' : ∀ k, w (B k) = genMap ξ ⟨f q'.1, hd.specializes q'⟩
        (secVal (B := DualNumber (X.presheaf.stalk (f q'.1))) (v k).left W (hk₀ k) s).snd + n * ρ k := hρe
    refine ⟨∑ k, genMap ξ' q' (a k) * i (ρ k), sum_mem fun k _ => mul_mem ⟨a k, rfl⟩ (hρ' k), ?_⟩
    have hg : ∀ t, genMap ξ' q' ((f.stalkMap q'.1).hom t) = i (genMap ξ ⟨f q'.1, hd.specializes q'⟩ t) :=
      fun t => RegAtDom.genMap_stalkMap hd q'.1 q'.2 (hd.specializes q') t
    refine Eq.trans ?_ (congrArg (fun t => genMap ξ' q' t + (n : Ω') * ∑ k, genMap ξ' q' (a k) * i (ρ k)) hsum).symm
    show jd w (∑ k, genMap ξ' q' (a k) • B' k) = genMap ξ' q' (∑ k, a k * _) + (n : Ω') * ∑ k, genMap ξ' q' (a k) * i (ρ k)
    rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, hBB k, hjd, hρe' k, map_add, map_mul, map_mul, hcomp k, hg, map_natCast]
    ring

theorem main : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (X' : Scheme.{0}) [IsLocallyNoetherian X'] (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X'), IsCptGen ξ' → Flat.NormalCpt ξ' → ∀ (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (L' : LB G'.left) (e' : (Over.mk ξ' ⟶ G') → (Over.mk ξ' ⟶ G') → Ω'ˣ), GenWeil G' L' ξ' n e' → ∀ (E' : Type) [AddCommGroup E'] [Module Ω' E'] (M' : LieModel G' ξ' E') (j : E →+ E') (jd : Module.Dual Ω E →+ Module.Dual Ω' E'), (∀ v, (M'.pt (j v)).left ≫ φ = spMap (dualMap i) ≫ (M.pt v).left) → (∀ w v, jd w (j v) = i (w v)) → M'.htOm L' n = (M.htOm L n).pull ξ' f jd ∧ M'.omLat = M.omLat.pull ξ' f jd := by
  intro X _ Ω _ _ ξ hξ hN G _ hG L n hn hF e he E _ _ M X' _ Ω' _ ξ' hξ' hN' f i hd G' _ _ φ hp L' e' he' E' _ _ M' j jd hj hjd
  haveI : IsCommMonObj G := hG.comm
  haveI : CharZero Ω' := charZero_of_injective_ringHom i.injective
  have hs : Smooth G.hom := hG.smooth
  have hG' : IsSemiAbelian G' := GlobalTheory.T.semi_abelian_of_pullback X X' G G' f φ hp hG
  obtain ⟨hF', t1, t2, tm, tu1, tu2⟩ := GlobalTheory.T.full_torsion_pullback_points X X' Ω Ω' ξ ξ' f i hd G G' φ hp n hF
  obtain ⟨c1, c2⟩ := GlobalTheory.T.weil_pairing_transport_relation Ω Ω' i (Over.mk ξ ⟶ G) (Over.mk ξ' ⟶ G') (fun a c => a.left ≫ φ = spMap i ≫ c.left)
    n hn t1 t2 tm tu1 tu2 e e' (fun x g g' _ hg hg' => he.mul_right x g g' ‹_› hg hg') he.perfect he.nondeg
    (fun x g g' _ hg hg' => he'.mul_right x g g' ‹_› hg hg') he'.perfect
  have om := om_pull hξ hξ' hd hp hs M M' j jd hj hjd
  have hpull := fun q' {y y'} hy hy' hc {w} hw =>
    ht_pull (e := e) (e' := e') hξ hξ' hd hp hs he hF hF' he' t1 t2 M M' j jd hj hjd q' (y := y) (y' := y') hy hy' hc (w := w) hw
  obtain ⟨hext, hspan, -⟩ := LiePull.main X X' Ω Ω' ξ ξ' f i G G' φ E E' M M' j hξ hξ' hd hp hs hj
  have hjs : ∀ (a : Ω) (w : Module.Dual Ω E), jd (a • w) = i a • jd w := by
    intro a w
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨v, rfl⟩
    simp [hjd]
  refine ⟨?_, om⟩
  funext q'
  have hsp := hd.specializes q'
  obtain ⟨h', hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q'
  rw [Lat.pull_apply _ hd]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w' ⟨y', hy', hw'⟩
    obtain ⟨y, hy, hc⟩ := c1 y' hy'
    obtain ⟨⟨U, hU, wf, hwf⟩, -⟩ := GlobalTheory.T.hodge_tate_weil_local X Ω ξ hξ hN G hG L n hn hF e he E M ⟨f q'.1, hsp⟩
    have h0 := hwf y hy ⟨f q'.1, hsp⟩ hU
    have h1 := hpull q' hy hy' hc h0
    obtain ⟨u, hu, rfl⟩ := (GlobalTheory.T.hodge_tate_weil_unique X' Ω' ξ' hξ' hN' G' hG' L' n hn hF' e' he' E' M' y' q' _ w' hy' h1).1 hw'
    refine add_mem (Submodule.subset_span ⟨wf y, Submodule.subset_span ⟨y, hy, h0⟩, rfl⟩) ?_
    clear hw'
    rw [om, Lat.pull_apply _ hd] at hu
    have hnz : ∀ z ∈ M.omLat ⟨f q'.1, hsp⟩, n • z ∈ M.htOm L n ⟨f q'.1, hsp⟩ := by
      intro z hz
      have h2 := (GlobalTheory.T.hodge_tate_weil_unique X Ω ξ hξ hN G hG L n hn hF e he E M y ⟨f q'.1, hsp⟩ _ (wf y + n • z) hy h0).2 ⟨z, hz, rfl⟩
      have h3 : wf y + n • z ∈ M.htOm L n ⟨f q'.1, hsp⟩ := Submodule.subset_span ⟨y, hy, h2⟩
      have h4 : wf y ∈ M.htOm L n ⟨f q'.1, hsp⟩ := Submodule.subset_span ⟨y, hy, h0⟩
      simpa using sub_mem h3 h4
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      rw [← map_nsmul]
      exact Submodule.subset_span ⟨_, hnz z hz, rfl⟩
    | zero => simp
    | add x z _ _ hx hz => rw [smul_add]; exact add_mem hx hz
    | smul a x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ a hx
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, hxw⟩ := hx
      obtain ⟨y', hy', hc⟩ := c2 y hy
      exact Submodule.subset_span ⟨y', hy', hpull q' hy hy' hc hxw⟩
    | zero => simp
    | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
    | smul a x _ hx =>
      obtain ⟨a, ha⟩ := a
      have : jd ((⟨a, ha⟩ : regAt ξ ⟨f q'.1, hsp⟩) • x) = i a • jd x := hjs a x
      rw [SetLike.mem_coe, this]
      exact Submodule.smul_mem _ (⟨i a, hreg a ha⟩ : regAt ξ' q') hx

end GlobalTheory.CompanionTheory.Ar.HtPull
