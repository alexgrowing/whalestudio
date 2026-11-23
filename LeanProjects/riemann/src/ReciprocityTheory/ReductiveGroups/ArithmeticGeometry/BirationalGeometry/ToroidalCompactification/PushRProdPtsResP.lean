import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem tanS_prodPts {d : ℕ} (c : Fin d → S) {u : Fin d → (sp (R₀ := S) (DualNumber S) ⟶ G)} (hu : ∀ i, TanS (u i)) :
    TanS (prodPts c u) := by
  unfold TanS prodPts
  change preH (spMap (TrivSqZeroExt.fstHom S S S)) (List.ofFn fun i => spMap (scaleD (c i)) ≫ u i).prod = 1
  rw [map_list_prod, List.map_ofFn]
  have h1 : ∀ i, preH (spMap (TrivSqZeroExt.fstHom S S S)) (spMap (scaleD (c i)) ≫ u i) = 1 :=
    fun i => tanS_scale (c i) (hu i)
  simp only [Function.comp_def, h1, List.ofFn_const, List.prod_replicate, one_pow]

section Local

variable (p : Ideal S) [p.IsPrime]

abbrev Gp : Over (Spec (CommRingCat.of (Localization.AtPrime p))) := (Over.pullback (fB S (Localization.AtPrime p))).obj G

def resP (v : sp (R₀ := S) (DualNumber S) ⟶ G) :
    sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p)) ⟶ Gp (G := G) p :=
  pullR G (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ v)

theorem pushR_resP (v : sp (R₀ := S) (DualNumber S) ⟶ G) :
    pushR G (resP p v) = spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ v := by
  unfold resP
  exact pushR_pullR (R := S) (R' := Localization.AtPrime p) (G := G) _

theorem pushR_prodPts_resP {d : ℕ} (c : Fin d → S) (u : Fin d → (sp (R₀ := S) (DualNumber S) ⟶ G)) :
    pushR G (prodPts (fun i => algebraMap S (Localization.AtPrime p) (c i)) (fun i => resP p (u i))) =
      spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ prodPts c u := by
  unfold prodPts
  rw [pushR_prod]
  change _ = preH (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))))
    (List.ofFn fun i => spMap (scaleD (c i)) ≫ u i).prod
  rw [map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  show pushR G (spMap (scaleD _) ≫ resP p (u i)) =
    spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ spMap (scaleD (c i)) ≫ u i
  rw [pushR_spMap, pushR_resP, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]
  congr 2
  exact (dualMapS_comp_scaleS (Algebra.ofId S (Localization.AtPrime p)) (c i)).symm

theorem isTan_iff_tanS (w : sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p)) ⟶ Gp (G := G) p) :
    IsTan w ↔ TanS (pushR G w) := by
  unfold IsTan TanS
  constructor
  · intro h
    have h' := congrArg (pushR G) h
    rw [pushR_spMap, pushR_one] at h'
    exact h'
  · intro h
    apply pushR_inj (G := G)
    rw [pushR_spMap, pushR_one]
    exact h

variable [∀ s : S, Smooth (Gs G s).hom]

theorem prodPts_resP_inj {d : ℕ} {u : Fin d → (Geo.Tor.epsR S ⟶ G)} (hu : Geo.Tor.IsLieBasis u)
    {a b : Fin d → Localization.AtPrime p}
    (h : prodPts a (fun i => resP p (u i)) = prodPts b (fun i => resP p (u i))) : a = b := by
  classical
  unfold Geo.Tor.IsLieBasis at hu
  obtain ⟨hT, hU⟩ := hu
  have hTS : ∀ i, TanS (u i) := fun i => (isTan_iff (u i)).2 (hT i)
  obtain ⟨⟨s, hs⟩, hint⟩ := IsLocalization.exist_integer_multiples (M := p.primeCompl)
    (Finset.univ : Finset (Fin d ⊕ Fin d)) (Sum.elim a b)
  have hint' : ∀ j, ∃ y : S, algebraMap S (Localization.AtPrime p) y = s • Sum.elim a b j :=
    fun j => hint j (Finset.mem_univ _)
  choose y hy using hint'
  let a' : Fin d → S := fun i => y (Sum.inl i)
  let b' : Fin d → S := fun i => y (Sum.inr i)
  have ea : algebraMap S (Localization.AtPrime p) s • a = fun i => algebraMap S _ (a' i) := by
    funext i
    simp only [a', hy, Pi.smul_apply, smul_eq_mul, Sum.elim_inl, Algebra.smul_def]
  have eb : algebraMap S (Localization.AtPrime p) s • b = fun i => algebraMap S _ (b' i) := by
    funext i
    simp only [b', hy, Pi.smul_apply, smul_eq_mul, Sum.elim_inr, Algebra.smul_def]
  have h2 : spMap (scaleD (algebraMap S (Localization.AtPrime p) s)) ≫ prodPts a (fun i => resP p (u i)) =
      spMap (scaleD (algebraMap S (Localization.AtPrime p) s)) ≫ prodPts b (fun i => resP p (u i)) := by
    rw [h]
  rw [scale_prodPts, scale_prodPts, ea, eb] at h2
  have h3 := congrArg (pushR G) h2
  rw [pushR_prodPts_resP, pushR_prodPts_resP] at h3
  have hA : TanS (prodPts a' u) := tanS_prodPts a' hTS
  have hB : TanS (prodPts b' u) := tanS_prodPts b' hTS
  have hx : TanS (prodPts a' u * (prodPts b' u)⁻¹) := by
    unfold TanS at hA hB ⊢
    change preH (spMap (TrivSqZeroExt.fstHom S S S)) (prodPts a' u * (prodPts b' u)⁻¹) = 1
    rw [map_mul, map_inv]
    change (spMap (TrivSqZeroExt.fstHom S S S) ≫ prodPts a' u) *
      (spMap (TrivSqZeroExt.fstHom S S S) ≫ prodPts b' u)⁻¹ = 1
    rw [hA, hB, _root_.inv_one, _root_.mul_one]
  have hx1 : spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫
      (prodPts a' u * (prodPts b' u)⁻¹) = 1 := by
    change preH (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))))
      (prodPts a' u * (prodPts b' u)⁻¹) = 1
    rw [map_mul, map_inv]
    change (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ prodPts a' u) *
      (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ prodPts b' u)⁻¹ = 1
    rw [h3, _root_.mul_inv_cancel]
  obtain ⟨q, hq, hq1⟩ := tan_prime_uniq (p := p) hx hx1
  change preH (spMap (scaleS (S := S) q)) (prodPts a' u * (prodPts b' u)⁻¹) = 1 at hq1
  rw [map_mul, map_inv, _root_.mul_inv_eq_one] at hq1
  have hq2 : prodPts (q • a') u = prodPts (q • b') u := by
    rw [← scale_prodPts, ← scale_prodPts]
    exact hq1
  have hw : Geo.Tor.IsTangent (prodPts (q • a') u) := (isTan_iff _).1 (tanS_prodPts _ hTS)
  obtain ⟨c, _, huniq⟩ := hU _ hw
  have e1 := huniq (q • a') ((isLieComb_iff _ _ _).2 rfl)
  have e2 := huniq (q • b') ((isLieComb_iff _ _ _).2 hq2)
  have hab : q • a' = q • b' := e1.trans e2.symm
  funext i
  have hi := congrArg (algebraMap S (Localization.AtPrime p)) (congrFun hab i)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, a', b', hy, Sum.elim_inl, Sum.elim_inr,
    Algebra.smul_def] at hi
  have hqu : IsUnit (algebraMap S (Localization.AtPrime p) q) :=
    IsLocalization.map_units (M := p.primeCompl) _ ⟨q, hq⟩
  have hsu : IsUnit (algebraMap S (Localization.AtPrime p) s) :=
    IsLocalization.map_units (M := p.primeCompl) _ ⟨s, hs⟩
  rw [hqu.mul_right_inj, hsu.mul_right_inj] at hi
  exact hi

private theorem scaleD_comp_scaleD {R : Type} [CommRing R] (a b : R) :
    (scaleD a).comp (scaleD b) = scaleD (a * b) := by
  apply AlgHom.ext
  intro x
  ext
  · simp
  · simp only [AlgHom.comp_apply, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring

private theorem spMap_scaleD_one {R : Type} [CommRing R] {H : Over (Spec (CommRingCat.of R))}
    (w : sp (R₀ := R) (DualNumber R) ⟶ H) : spMap (scaleD (1 : R)) ≫ w = w := by
  have h1 : scaleD (1 : R) = AlgHom.id R (DualNumber R) := by
    apply AlgHom.ext
    intro x
    ext <;> simp
  have h2 : spMap (R₀ := R) (AlgHom.id R (DualNumber R)) = 𝟙 _ := by
    ext1
    simp [spMap]
  rw [h1, h2, Category.id_comp]

theorem isLieBasis_local {d : ℕ} {u : Fin d → (Geo.Tor.epsR S ⟶ G)} (hu : Geo.Tor.IsLieBasis u) :
    Geo.Tor.IsLieBasis (G := Gp (G := G) p) (fun i => resP p (u i)) := by
  have hu0 := hu
  unfold Geo.Tor.IsLieBasis at hu0 ⊢
  obtain ⟨hT, hU⟩ := hu0
  have hTS : ∀ i, TanS (u i) := fun i => (isTan_iff (u i)).2 (hT i)
  refine ⟨fun i => (isTan_iff _).1 ((isTan_iff_tanS p _).2 ?_), fun w hw => ?_⟩
  · rw [pushR_resP]
    exact tanS_restrict _ (hTS i)
  · have hwS : TanS (pushR G w) := (isTan_iff_tanS p w).1 ((isTan_iff w).2 hw)
    obtain ⟨q, hq, w0, hw0, he⟩ := tan_prime_lift (p := p) hwS
    obtain ⟨c0, hc0, -⟩ := hU w0 ((isTan_iff w0).1 hw0)
    rw [isLieComb_iff] at hc0
    have hQ : IsUnit (algebraMap S (Localization.AtPrime p) q) :=
      IsLocalization.map_units (M := p.primeCompl) _ ⟨q, hq⟩
    have E : prodPts (fun i => algebraMap S (Localization.AtPrime p) (c0 i)) (fun i => resP p (u i)) =
        spMap (scaleD (algebraMap S (Localization.AtPrime p) q)) ≫ w := by
      apply pushR_inj (G := G)
      rw [pushR_prodPts_resP, ← hc0, he, pushR_spMap]
      rfl
    have hw1 : w = prodPts ((hQ.unit⁻¹ : (Localization.AtPrime p)ˣ) •
        (fun i => algebraMap S (Localization.AtPrime p) (c0 i))) (fun i => resP p (u i)) := by
      rw [Units.smul_def, ← scale_prodPts, E, ← Category.assoc, spMap_comp, scaleD_comp_scaleD,
        hQ.val_inv_mul, spMap_scaleD_one]
    refine ⟨_, (isLieComb_iff _ _ _).2 hw1, fun c' hc' => ?_⟩
    exact prodPts_resP_inj p hu (((isLieComb_iff _ _ _).1 hc').symm.trans hw1)

end Local

theorem frameLieBC {S : Type} [CommRing S] (G : Over (Spec (CommRingCat.of S))) [GrpObj G] [Smooth G.hom] {d : ℕ}
    {u : Fin d → (Geo.Tor.epsR S ⟶ G)} (hu : Geo.Tor.IsLieBasis u) {k : Type} [Field k] (φ : S →+* k)
    {G' : Over (Spec (CommRingCat.of k))} [GrpObj G'] {F : G'.left ⟶ G.left}
    (h : Geo.Tor.IsGrpPullback G' G (Geo.Tor.spMap φ) F) {u' : Fin d → (Geo.Tor.epsR k ⟶ G')}
    (hu' : ∀ i, (u' i).left ≫ F = Geo.Tor.spMap (dualMapR φ) ≫ (u i).left) : Geo.Tor.IsLieBasis u' := by
  classical
  haveI : ∀ s : S, Smooth (Gs G s).hom := fun s => by
    show Smooth (pullback.snd G.hom (fB S (Localization.Away s)))
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd (P := @Smooth) _ _ (inferInstance : Smooth G.hom)
  haveI hpr : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  let φp : Localization.AtPrime (RingHom.ker φ) →+* k :=
    IsLocalization.lift (M := (RingHom.ker φ).primeCompl) (S := Localization.AtPrime (RingHom.ker φ)) (g := φ)
      (fun s => isUnit_iff_ne_zero.2 fun h0 => s.2 (RingHom.mem_ker.2 h0))
  have hφ : φp.comp (algebraMap S (Localization.AtPrime (RingHom.ker φ))) = φ := IsLocalization.lift_comp _
  haveI : Smooth (Gp (G := G) (RingHom.ker φ)).hom := by
    show Smooth (pullback.snd G.hom (fB S (Localization.AtPrime (RingHom.ker φ))))
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd (P := @Smooth) _ _ (inferInstance : Smooth G.hom)
  have hsp : Geo.Tor.spMap φ = Geo.Tor.spMap φp ≫ fB S (Localization.AtPrime (RingHom.ker φ)) := by
    simp only [Geo.Tor.spMap, fB]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have h2 : Geo.Tor.IsGrpPullback G' G (Geo.Tor.spMap φp ≫ fB S (Localization.AtPrime (RingHom.ker φ))) F :=
    h.congr hsp rfl
  have h3 := isGrpPullback_factor (fB S (Localization.AtPrime (RingHom.ker φ))) (Geo.Tor.spMap φp) h2
  refine isLieBasis_baseChange (G := Gp (G := G) (RingHom.ker φ)) φp h3
    (isLieBasis_local (RingHom.ker φ) hu) (fun j => ?_)
  have hring : (dualMapR φp).comp (dualMapS (Algebra.ofId S (Localization.AtPrime (RingHom.ker φ)))).toRingHom =
      dualMapR φ := by
    conv_rhs => rw [← hφ]
    apply RingHom.ext
    intro x
    apply TrivSqZeroExt.ext <;> simp [dualMapR, dualMapS_fst, dualMapS_snd]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hu' j]
    simp only [resP, pullR, Over.homMk_left, Category.assoc, IsPullback.lift_fst, Over.comp_left, spMap]
    rw [← Category.assoc, Geo.Tor.spMap, Geo.Tor.spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
  · rw [Category.assoc, pullback.lift_snd]
    simp only [resP, pullR, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
    rw [← Category.assoc, Over.w (u' j)]
    simp only [Geo.Tor.epsR, sp, Over.mk_hom, Geo.Tor.spMap]
    erw [IsPullback.lift_snd]
    simp only [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end ReciprocityTheory.ChartRestriction.G.Chart
