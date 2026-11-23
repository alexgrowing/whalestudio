import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

set_option maxHeartbeats 1000000 in

theorem lieBasis_of_etale {S : Type} [CommRing S] [Algebra R S] {n : ℕ} [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S] [Algebra.FormallyEtale (MvPolynomial (Fin n) R) S] (ε' : S →ₐ[R] R)
    (y₀ : sp (R₀ := R) S ⟶ G) (h₀ : spMap ε' ≫ y₀ = 1)
    (locExt : ∀ φ₁ φ₂ : S →ₐ[R] DualNumber R, spMap φ₁ ≫ y₀ = spMap φ₂ ≫ y₀ → φ₁ = φ₂)
    (up : ∀ {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R), IsNilpotent (RingHom.ker aug) →
      ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 → ∃ ψ : S →ₐ[R] A, aug.comp ψ = ε' ∧ y = spMap ψ ≫ y₀) :
    ∃ v : Fin n → (Geo.Tor.epsR R ⟶ G), Geo.Tor.IsLieBasis v := by
  classical
  have nD : IsNilpotent (RingHom.ker (fstD R)) := ⟨2, by
    rw [Ideal.zero_eq_bot, ← le_bot_iff, pow_two, Ideal.mul_le]
    intro a ha b hb
    rw [Ideal.mem_bot, show a = TrivSqZeroExt.inr a.snd from TrivSqZeroExt.ext ha rfl,
      show b = TrivSqZeroExt.inr b.snd from TrivSqZeroExt.ext hb rfl, TrivSqZeroExt.inr_mul_inr]⟩
  let Co : (sp (R₀ := R) (DualNumber R) ⟶ G) → (Fin n → R) → Prop := fun w c =>
    ∃ ψ : S →ₐ[R] DualNumber R, (fstD R).comp ψ = ε' ∧ w = spMap ψ ≫ y₀ ∧ ∀ j, (ψ (sX R j)).snd = c j
  have tan : ∀ {w c}, Co w c → IsTan w := fun ⟨ψ, h, e, _⟩ => by
    rw [IsTan, e, ← Category.assoc, spMap_comp, h, h₀]
  have fn : ∀ {w c c'}, Co w c → Co w c' → c = c' := fun ⟨ψ, _, e, h⟩ ⟨ψ', _, e', h'⟩ => funext fun j => by
    rw [← h j, ← h' j, locExt ψ ψ' (e.symm.trans e')]
  have inj : ∀ {w w' c}, Co w c → Co w' c → w = w' := fun ⟨ψ, a, e, h⟩ ⟨ψ', a', e', h'⟩ => by
    rw [e, e', etale_ext (n := n) ε' (fstD R) nD ψ ψ' a a' fun j => TrivSqZeroExt.ext
      ((AlgHom.congr_fun a _).trans (AlgHom.congr_fun a' _).symm) ((h j).trans (h' j).symm)]
  have ex : ∀ {w}, IsTan w → ∃ c, Co w c := fun hw => let ⟨ψ, a, e⟩ := up (fstD R) nD _ hw; ⟨_, ψ, a, e, fun _ => rfl⟩
  have sj : ∀ c, ∃ w, Co w c := fun c => by
    obtain ⟨ψ, a, h⟩ := etale_exists (n := n) ε' (fstD R) nD (fun j => TrivSqZeroExt.inl (ε' (sX R j)) + TrivSqZeroExt.inr (c j))
      fun j => by simp [fstD]
    exact ⟨_, ψ, a, rfl, fun j => by rw [h j]; simp⟩
  have sc : ∀ {w c} (a : R), Co w c → Co (spMap (scaleD a) ≫ w) (a • c) := fun a ⟨ψ, h, e, k⟩ =>
    ⟨(scaleD a).comp ψ, AlgHom.ext fun b => (TrivSqZeroExt.fst_map _ _).trans (AlgHom.congr_fun h b),
      by rw [e, ← Category.assoc, spMap_comp], fun j => (TrivSqZeroExt.snd_map _ _).trans (congrArg (a * ·) (k j))⟩
  have ad : ∀ {w₁ w₂ c₁ c₂}, Co w₁ c₁ → Co w₂ c₂ → Co (w₁ * w₂) (c₁ + c₂) := fun {w₁ w₂ c₁ c₂} h₁ h₂ => by
    obtain ⟨ψ, a, e⟩ := up (jetAug R (Fin 2) 1) (ker_jetAug_nil (Fin 2) 1) ((spMap (qD 0) ≫ w₁) * (spMap (qD 1) ≫ w₂)) (by
      rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, jetAug_comp_qD, jetAug_comp_qD, tan h₁,
        tan h₂, _root_.mul_one])
    have r : ∀ l : R × R →ₗ[R] R, Co ((spMap (scaleD (l (1, 0))) ≫ w₁) * (spMap (scaleD (l (0, 1))) ≫ w₂))
        fun j => (rD l (ψ (sX R j))).snd := fun l =>
      ⟨(rD l).comp ψ, by rw [← AlgHom.comp_assoc, fstD_comp_rD, a], by
        rw [← spMap_comp, Category.assoc, ← e, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp,
          restrictDiag_comp_incl_fst, restrictDiag_comp_incl_snd], fun _ => rfl⟩
    have r₁ := r (LinearMap.fst R R R)
    have r₂ := r (LinearMap.snd R R R)
    have r₃ := r (LinearMap.fst R R R + LinearMap.snd R R R)
    simp only [LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, add_zero, zero_add, scaleD_one, spMap_id,
      Category.id_comp, spMap_scaleD_zero (tan h₁), spMap_scaleD_zero (tan h₂), _root_.mul_one, _root_.one_mul] at r₁ r₂ r₃
    rw [fn h₁ r₁, fn h₂ r₂]
    exact (show (fun j => (rD (LinearMap.fst R R R + LinearMap.snd R R R) (ψ (sX (n := n) R j))).snd) =
      (fun j => (rD (LinearMap.fst R R R) (ψ (sX (n := n) R j))).snd) + fun j => (rD (LinearMap.snd R R R) (ψ (sX (n := n) R j))).snd from
      funext fun j => snd_rD_add _) ▸ r₃
  choose v hv using fun i => sj (Pi.single i 1)
  have pr : ∀ {m} (a : Fin m → R) (u : Fin m → _) (c : Fin m → Fin n → R), (∀ i, Co (u i) (c i)) →
      Co (prodPts a u) (∑ i, a i • c i) := fun {m} => by
    induction m with
    | zero =>
      intro a u c _
      obtain ⟨w, hw⟩ := sj 0
      have := sc 0 hw
      rwa [spMap_scaleD_zero (tan hw), zero_smul] at this
    | succ m ih =>
      intro a u c h
      rw [prodPts, List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
      exact ad (sc _ (h 0)) (ih _ _ _ fun i => h i.succ)
  have pv : ∀ a, Co (prodPts a v) a := fun a => by
    have := pr a v _ hv
    rwa [show ∑ i, a i • (Pi.single i 1 : Fin n → R) = a from funext fun j => by simp [Finset.sum_apply, Pi.single_apply]] at this
  refine ⟨v, fun i => (isTan_iff _).1 (tan (hv i)), fun w hw => ?_⟩
  obtain ⟨c, hc⟩ := ex ((isTan_iff _).2 hw)
  exact ⟨c, (isLieComb_iff _ _ _).2 (inj hc (pv c)), fun a ha => fn ((isLieComb_iff _ _ _).1 ha ▸ pv a) hc⟩

theorem etale_parameter_exists {R' S : Type} [CommRing R'] [Algebra R R'] (g : R) [IsLocalization.Away g R'] [CommRing S] [Algebra R S] {n : ℕ}
    [Algebra (MvPolynomial (Fin n) R) S] [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Algebra.FormallyEtale (MvPolynomial (Fin n) R) S] (ug : IsUnit (algebraMap R S g)) :
    ∃ (_ : Algebra R' S) (_ : IsScalarTower R R' S) (_ : Algebra (MvPolynomial (Fin n) R') S)
      (_ : IsScalarTower R' (MvPolynomial (Fin n) R') S), Algebra.FormallyEtale (MvPolynomial (Fin n) R') S := by
  letI iA : Algebra R' S := (IsLocalization.Away.lift g ug).toAlgebra
  have h1 : IsScalarTower R R' S := IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq _ ug r).symm
  let ev : MvPolynomial (Fin n) R' →ₐ[R'] S := MvPolynomial.aeval fun j => algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X j)
  letI iB : Algebra (MvPolynomial (Fin n) R') S := ev.toRingHom.toAlgebra
  have h2 : IsScalarTower R' (MvPolynomial (Fin n) R') S := IsScalarTower.of_algebraMap_eq fun r => (ev.commutes r).symm
  letI : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R') := MvPolynomial.algebraMvPolynomial
  have : IsScalarTower (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R') S := IsScalarTower.of_algebraMap_eq' (by
    apply MvPolynomial.ringHom_ext
    · intro r
      show _ = ev (MvPolynomial.map _ (MvPolynomial.C r))
      rw [MvPolynomial.map_C, MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply]
      exact (IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R) S r).symm
    · intro j
      show _ = ev (MvPolynomial.map _ (MvPolynomial.X j))
      rw [MvPolynomial.map_X, MvPolynomial.aeval_X])
  exact ⟨iA, h1, iB, h2, Algebra.FormallyEtale.localization_base ((Submonoid.powers g).map (MvPolynomial.C (σ := Fin n)))⟩

theorem lift_aux {B S₁ S : Type} [CommRing B] [Algebra R B] (f : B) [CommRing S₁] [Algebra B S₁] [Algebra R S₁] [IsScalarTower R B S₁]
    [IsLocalization.Away f S₁] (g : R) [CommRing S] [Algebra S₁ S] [Algebra R S] [IsScalarTower R S₁ S]
    [IsLocalization.Away (algebraMap R S₁ g) S] {A : Type} [CommRing A] [Algebra R A] :
    (∀ φ₁ φ₂ : S →ₐ[R] A, φ₁.comp ((IsScalarTower.toAlgHom R S₁ S).comp (IsScalarTower.toAlgHom R B S₁)) =
      φ₂.comp ((IsScalarTower.toAlgHom R S₁ S).comp (IsScalarTower.toAlgHom R B S₁)) → φ₁ = φ₂) ∧
    ∀ φ : B →ₐ[R] A, IsUnit (φ f) → IsUnit (algebraMap R A g) →
      ∃ ψ : S →ₐ[R] A, ψ.comp ((IsScalarTower.toAlgHom R S₁ S).comp (IsScalarTower.toAlgHom R B S₁)) = φ := by
  refine ⟨fun φ₁ φ₂ h => ?_, fun φ hf hg => ?_⟩
  · have h2 : φ₁.toRingHom = φ₂.toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R S₁ g))
      apply IsLocalization.ringHom_ext (Submonoid.powers f)
      ext b
      exact DFunLike.congr_fun h b
    ext x
    exact DFunLike.congr_fun h2 x
  · have hu1 : ∀ y : Submonoid.powers f, IsUnit (φ.toRingHom (y : B)) := by
      rintro ⟨y, k, rfl⟩
      simpa using hf.pow k
    let ψ₁ : S₁ →+* A := IsLocalization.lift (M := Submonoid.powers f) hu1
    have hψ₁ : ∀ b : B, ψ₁ (algebraMap B S₁ b) = φ b := fun b => IsLocalization.lift_eq hu1 b
    have hg1 : ψ₁ (algebraMap R S₁ g) = algebraMap R A g := by
      rw [IsScalarTower.algebraMap_apply R B S₁, hψ₁, AlgHom.commutes]
    have hu2 : ∀ y : Submonoid.powers (algebraMap R S₁ g), IsUnit (ψ₁ (y : S₁)) := by
      rintro ⟨y, k, rfl⟩
      rw [map_pow, hg1]
      exact hg.pow k
    let ψ₂ : S →+* A := IsLocalization.lift (M := Submonoid.powers (algebraMap R S₁ g)) hu2
    have hψ₂ : ∀ s : S₁, ψ₂ (algebraMap S₁ S s) = ψ₁ s := fun s => IsLocalization.lift_eq hu2 s
    refine ⟨{ ψ₂ with commutes' := fun r => ?_ }, ?_⟩
    · show ψ₂ (algebraMap R S r) = algebraMap R A r
      rw [IsScalarTower.algebraMap_apply R S₁ S, hψ₂, IsScalarTower.algebraMap_apply R B S₁, hψ₁,
        AlgHom.commutes]
    · ext b
      show ψ₂ (algebraMap S₁ S (algebraMap B S₁ b)) = φ b
      rw [hψ₂, hψ₁]

theorem exists_param {B : Type} [CommRing B] [Algebra R B] [Algebra.Smooth R B] (e : B →ₐ[R] R) (p : Ideal R) [p.IsPrime] :
    ∃ f : B, e f ∉ p ∧ ∃ (n : ℕ) (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra (Localization.Away (e f)) S)
      (_ : IsScalarTower R (Localization.Away (e f)) S) (_ : Algebra (MvPolynomial (Fin n) (Localization.Away (e f))) S)
      (_ : IsScalarTower (Localization.Away (e f)) (MvPolynomial (Fin n) (Localization.Away (e f))) S)
      (_ : Algebra.FormallyEtale (MvPolynomial (Fin n) (Localization.Away (e f))) S) (toS : B →ₐ[R] S),
      (∀ {A : Type} [CommRing A] [Algebra R A] (φ₁ φ₂ : S →ₐ[R] A), φ₁.comp toS = φ₂.comp toS → φ₁ = φ₂) ∧
      ∀ {A : Type} [CommRing A] [Algebra R A] [Algebra (Localization.Away (e f)) A] [IsScalarTower R (Localization.Away (e f)) A]
        (φ : B →ₐ[R] A), IsUnit (φ f) → ∃ ψ : S →ₐ[Localization.Away (e f)] A, (ψ.restrictScalars R).comp toS = φ := by
  obtain ⟨f, hfq, n, _, hST, hSE⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p.comap e)
  have h₀ : Algebra.FormallyEtale (MvPolynomial (Fin n) R) (Localization.Away f) := inferInstance
  let S := Localization.Away (algebraMap R (Localization.Away f) (e f))
  have : Algebra.FormallyEtale (Localization.Away f) S := Algebra.FormallyEtale.of_isLocalization
    (Submonoid.powers (algebraMap R (Localization.Away f) (e f)))
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) R) S := Algebra.FormallyEtale.comp _ (Localization.Away f) S
  obtain ⟨iA, h1, iB, h2, h3⟩ := etale_parameter_exists (R' := Localization.Away (e f)) (S := S) (n := n) (e f) (by
    rw [IsScalarTower.algebraMap_apply R (Localization.Away f) S]; exact IsLocalization.Away.algebraMap_isUnit _)
  refine ⟨f, hfq, n, S, inferInstance, inferInstance, iA, h1, iB, h2, h3, _,
    fun {A} _ _ => (lift_aux (S₁ := Localization.Away f) f (e f)).1, fun {A} _ _ _ _ φ hu => ?_⟩
  obtain ⟨ψ, hψ⟩ := (lift_aux (S₁ := Localization.Away f) (S := S) f (e f)).2 φ hu (by
    rw [IsScalarTower.algebraMap_apply R (Localization.Away (e f)) A]; exact (IsLocalization.Away.algebraMap_isUnit _).map _)
  exact ⟨upS (s := e f) ψ, hψ⟩

theorem exists_lieBasis_away [Smooth G.hom] (C : Chart G) (p : Ideal R) [p.IsPrime] :
    ∃ g ∉ p, ∃ (n : ℕ) (v : Fin n → (Geo.Tor.epsR (Localization.Away g) ⟶ Gs G g)), Geo.Tor.IsLieBasis v := by
  haveI := chart_smooth C
  obtain ⟨f, hf, n, S, _, _, _, _, _, _, _, toS, ext, lift⟩ := exists_param (eps C) p
  refine ⟨eps C f, hf, n, ?_⟩
  let R' := Localization.Away (eps C f)
  obtain ⟨ε', hε'⟩ := lift ((Algebra.ofId R R').comp (eps C)) (IsLocalization.Away.algebraMap_isUnit (S := R') (eps C f))
  have py : ∀ {A : Type} [CommRing A] [Algebra R A] [Algebra R' A] [IsScalarTower R R' A] (ψ : S →ₐ[R'] A),
      pushR G (spMap ψ ≫ pullR (R' := R') G (pt C toS)) = pt C ((ψ.restrictScalars R).comp toS) := fun ψ => by
    rw [pushR_spMap, pushR_pullR, spMap_pt]
  refine lieBasis_of_etale ε' (pullR G (pt C toS)) (pushR_inj G (by rw [py, hε', pt_eps, pushR_one])) (fun φ₁ φ₂ h => ?_)
    fun {A} _ _ aug hJ y hy => ?_
  · exact AlgHom.restrictScalars_injective R (ext _ _ (pt_injective C ((py _).symm.trans ((congrArg (pushR G) h).trans (py _)))))
  · letI : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
    haveI : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hy' : spMap (aug.restrictScalars R) ≫ pushR G y = pt C ((Algebra.ofId R R').comp (eps C)) := by
      rw [← pushR_spMap, hy, pushR_one, pt_eps]
    obtain ⟨φ, hφ⟩ := exists_pt C (pushR G y) (le_preimage_of_nil C (aug.restrictScalars R) (aug_surj aug) (elt_nil _ hJ) _ _ hy')
    have ha : (aug.restrictScalars R).comp φ = _ := pt_injective C ((spMap_pt C _ φ).symm.trans ((congrArg (_ ≫ ·) hφ.symm).trans hy'))
    obtain ⟨ψ, hψ⟩ := lift φ (isUnit_of_aug aug hJ _ (by
      rw [show aug (φ f) = algebraMap R R' (eps C f) from AlgHom.congr_fun ha f]; exact IsLocalization.Away.algebraMap_isUnit _))
    refine ⟨ψ, AlgHom.restrictScalars_injective R (ext _ _ ?_), pushR_inj G (by rw [py, hψ, hφ])⟩
    exact ((congrArg (aug.restrictScalars R).comp hψ).trans ha).trans hε'.symm

end ReciprocityTheory.ChartRestriction.G.Chart

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1

theorem isReduced_of_smooth_alg (K B : Type) [Field K] [CommRing B] [Algebra K B] [Algebra.Smooth K B] : _root_.IsReduced B := by
  refine ⟨fun a ha => ?_⟩
  by_contra h0
  obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal (Ideal.span {a}).annihilator fun h =>
    h0 ((one_smul B a).symm.trans ((Submodule.mem_annihilator_span_singleton a 1).1 (h ▸ Submodule.mem_top)))
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let P := MvPolynomial (Fin n) K
  have : _root_.IsReduced (TensorProduct P (FractionRing P) (Localization.Away f)) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing P) _
  have : _root_.IsReduced (Localization.Away f) := isReduced_of_injective _
    (Algebra.TensorProduct.includeRight_injective (A := FractionRing P) (IsFractionRing.injective P _))
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) a).1
    (ha.map (algebraMap B (Localization.Away f))).eq_zero
  exact hf (hp.isPrime.mem_of_pow_mem N (hI ((Submodule.mem_annihilator_span_singleton a _).2 hN)))

theorem isReduced_sec_of_smooth {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Sp K) [Smooth q] {U : X.Opens}
    (hU : IsAffineOpen U) : _root_.IsReduced Γ(X, U) := by
  have h := HasRingHomProperty.appLE @Smooth q ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h' : RingHom.Smooth ((q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective) h
  letI := ((q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  have : Algebra.Smooth K Γ(X, U) := h'
  exact isReduced_of_smooth_alg K _

theorem isReduced_of_smooth {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Sp K) [Smooth q] : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
    have := isReduced_sec_of_smooth q hU
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact isReduced_localizationPreserves (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ ‹_›
  exact isReduced_of_isReduced_stalk X

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {B : Type} [CommRing B]
  {b : Base l B} {X : Scheme.{0}} {s : X ⟶ Sp B}

set_option maxHeartbeats 2000000 in
theorem gen_of_ne (hT : SecTwistSt) (o : Obj D l b s) {K : Type} [CommRing K] {x : Sp K ⟶ X} {t' : SAB H (Sp K)}
    (n : SABMap t' o.t x) (σ' : LB.Sec t'.PP.L) (hne₀ : ∀ (k : Type) [Field k] (χ : K →+* k) (t₂ : SAB H (Sp k))
      (m₂ : SABMap t₂ t' (spMap χ)), ¬ ∀ y j, m₂.φ y ∈ t'.PP.L.U j → gs m₂.φ y _ (σ'.f j) = 0) (s' : LB.Sec t'.PP.L) :
    ∃! a : K, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i := by
  classical
  have : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n.cart.1 o.proper
  have : CompactSpace t'.G.left := QuasiCompact.compactSpace_of_compactSpace t'.G.hom
  have loc : ∀ (p : Ideal K) [p.IsPrime], ∃ (t₁ : SAB H (Sp (Localization.AtPrime p)))
      (m₁ : SABMap t₁ t' (spMap (algebraMap K _))), ∀ τ : LB.Sec t'.PP.L, ∃! a : Localization.AtPrime p,
        ∀ y j, m₁.φ y ∈ t'.PP.L.U j → gs m₁.φ y _ (τ.f j) = cst t₁.G.hom y a * gs m₁.φ y _ (σ'.f j) := fun p _ => by
    obtain ⟨t₁, ⟨m₁⟩⟩ := exists_sab (spMap (algebraMap K (Localization.AtPrime p))) t'
    refine ⟨_, m₁, fun τ => ?_⟩
    obtain ⟨n₁, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ n m₁
    obtain ⟨β, hβ⟩ := globalSections_rank_one_obj hT o n₁
    obtain ⟨w₁, g₁, -⟩ := m₁.lin
    have dn := fun τ => sec_pull_down ((isGen_iff w₁).1 g₁) t'.PP.isLB t₁.PP.isLB τ
    choose d hd using dn
    have hd' : ∀ τ y j k, m₁.φ y ∈ t'.PP.L.U j → y ∈ t₁.PP.L.U k →
        gs m₁.φ y _ (τ.f j) = (gw w₁ (𝟙 _) y j k).val * gs (𝟙 _) y _ ((d τ).f k) := fun τ y j k h h' =>
      (congrArg (fun q => gs q y _ (τ.f j)) (Category.id_comp _)).symm.trans (hd τ _ (𝟙 _) y j k h h')
    obtain ⟨a₀, ha₀, -⟩ := hβ (d σ')
    have h₀ : IsUnit a₀ := by
      by_contra hne
      obtain ⟨t₂, ⟨m₂⟩⟩ := exists_sab (spMap (IsLocalRing.residue (Localization.AtPrime p))) t₁
      obtain ⟨n₂, e₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m₂
      have key : ∀ y k, n₂.φ y ∈ t'.PP.L.U k → gs n₂.φ y _ (σ'.f k) = 0 := fun y k hk₀ => by
        obtain ⟨k', hk'⟩ := exists_chart t₁.PP.isLB (m₂.φ y)
        have hk : m₁.φ (m₂.φ y) ∈ t'.PP.L.U k := (congrArg (fun q => q y ∈ t'.PP.L.U k) e₂).mp hk₀
        rw [show n₂.φ = m₂.φ ≫ m₁.φ from e₂, gs_comp m₂.φ _ y _ hk, hd' σ' _ k k' hk hk', (sec_eq_iff _ _ _ _).1 ha₀ k' _ hk',
          map_mul, map_mul, cst_stalkMap, m₂.cart.1.w, cst_comp, (IsLocalRing.residue_eq_zero_iff _).2 hne, cst, map_zero,
          gs_zero _ y ⊤ trivial, zero_mul, mul_zero]
      clear e₂
      revert n₂
      rw [← spMap_comp]
      exact fun n₂ key => hne₀ _ _ _ n₂ key
    obtain ⟨u, rfl⟩ := h₀
    have iff : ∀ a : Localization.AtPrime p, (∀ y j, m₁.φ y ∈ t'.PP.L.U j → gs m₁.φ y _ (τ.f j) = cst _ y a * gs m₁.φ y _ (σ'.f j)) ↔
        ∀ i, (d τ).f i = constFn _ _ (a * u) * β.f i := fun a => by
      rw [sec_eq_iff]
      refine ⟨fun h k y hk => ?_, fun h y j hj => ?_⟩
      · obtain ⟨j, hj⟩ := exists_chart t'.PP.isLB (m₁.φ y)
        have := h y j hj
        rw [hd' τ y j k hj hk, hd' σ' y j k hj hk, mul_left_comm, Units.mul_right_inj, (sec_eq_iff _ _ _ _).1 ha₀ k y hk] at this
        rw [this, cst_mul, _root_.mul_assoc]
      · obtain ⟨k, hk⟩ := exists_chart t₁.PP.isLB y
        rw [hd' τ y j k hj hk, hd' σ' y j k hj hk, h k y hk, (sec_eq_iff _ _ _ _).1 ha₀ k y hk, cst_mul]
        ring
    obtain ⟨a, ha, hu⟩ := hβ (d τ)
    exact ⟨a * ↑u⁻¹, (iff _).2 (by rwa [Units.inv_mul_cancel_right]), fun a' h =>
      (Units.eq_mul_inv_iff_mul_eq u).2 (hu _ ((iff _).1 h))⟩
  have cadd : ∀ {Z : Scheme.{0}} (q : Z ⟶ Sp K) z a c, cst q z (a + c) = cst q z a + cst q z c := fun q z a c => by
    rw [cst, map_add, gs_eq q z ⊤ trivial, map_add, map_add, ← gs_eq q z ⊤ trivial, ← gs_eq q z ⊤ trivial]; rfl
  let I : Ideal K :=
    { carrier := {r | ∃ a, ∀ j, ∀ y ∈ t'.PP.L.U j,
        cst t'.G.hom y r * gs (𝟙 _) y _ (s'.f j) = cst t'.G.hom y a * gs (𝟙 _) y _ (σ'.f j)}
      add_mem' := fun ⟨a, ha⟩ ⟨c, hc⟩ => ⟨a + c, fun j y hy => by rw [cadd, cadd, add_mul, add_mul, ha j y hy, hc j y hy]⟩
      zero_mem' := ⟨0, fun j y _ => by rw [cst, map_zero, gs_zero _ y ⊤ trivial, zero_mul, zero_mul]⟩
      smul_mem' := fun r c ⟨a, ha⟩ => ⟨r * a, fun j y hy => by
        rw [smul_eq_mul, cst_mul, cst_mul, _root_.mul_assoc, ha j y hy, _root_.mul_assoc]⟩ }
  have top : I = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨t₁, m₁, h₁⟩ := loc p
    obtain ⟨c, hc, -⟩ := h₁ s'
    obtain ⟨⟨a, q⟩, hq⟩ := IsLocalization.surj p.primeCompl c
    let g : ∀ j, Γ(t'.G.left, t'.PP.L.U j) := fun j => constFn t'.G.hom _ q.1 * s'.f j + constFn t'.G.hom _ (-a) * σ'.f j
    have gv : ∀ {Z : Scheme.{0}} (r : Z ⟶ t'.G.left) z j, r z ∈ t'.PP.L.U j → gs r z _ (g j) =
        cst (r ≫ t'.G.hom) z q.1 * gs r z _ (s'.f j) + cst (r ≫ t'.G.hom) z (-a) * gs r z _ (σ'.f j) := fun r z j h => by
      rw [← gs_constFn _ _ r z h, ← gs_constFn _ _ r z h, ← gs_mul r z _ h, ← gs_mul r z _ h, gs_eq r z _ h, gs_eq r z _ h,
        gs_eq r z _ h, map_add, map_add]
    choose j hj using fun y : t'.G.left => exists_chart t'.PP.isLB y
    choose V hV hyV hVU using fun y : t'.G.left => exists_isAffineOpen_mem_and_subset (hj y)
    have kill : ∀ y, ∃ r ∈ p.primeCompl, ∀ z ∈ V y, cst t'.G.hom z r * gs (𝟙 _) z _ (g (j y)) = 0 := fun y => by
      obtain ⟨r, hr, h⟩ := loc_ker p.primeCompl m₁.cart.1 (hV y) (resG _ (hVU y) (g (j y))) fun z hz => by
        rw [show gs m₁.φ z (V y) (resG _ (hVU y) (g (j y))) = _ from gs_res m₁.φ z (hVU y) hz _, gv _ z _ (hVU y hz),
          hc z _ (hVU y hz), m₁.cart.1.w, cst_comp, cst_comp, ← _root_.mul_assoc, ← cst_mul, ← add_mul, mul_comm _ c, hq, map_neg]
        have : cst t₁.G.hom z (algebraMap K (Localization.AtPrime p) a) + cst t₁.G.hom z (-algebraMap K _ a) = 0 := by
          rw [cst, cst, gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, map_neg, map_neg, map_neg, add_neg_cancel]
        rw [this, zero_mul]
      exact ⟨r, hr, fun z hz => (congrArg _ (gs_res (𝟙 _) z (hVU y) hz _).symm).trans (h z hz)⟩
    choose r hr hk using kill
    obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set t'.G.left)) (fun y => (V y).2)
      fun y _ => Set.mem_iUnion.2 ⟨y, hyV y⟩
    refine p.primeCompl.mul_mem (p.primeCompl.prod_mem fun y (_ : y ∈ F) => hr y) q.2
      (hI ⟨(∏ y ∈ F, r y) * a, fun i z hz => ?_⟩)
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ z))
    have k := hk y z hzy
    rw [gv _ z _ (hVU y hzy), Category.id_comp, gs_compat s' (𝟙 _) z (hVU y hzy) hz, gs_compat σ' (𝟙 _) z (hVU y hzy) hz] at k
    have n₀ : cst t'.G.hom z a + cst t'.G.hom z (-a) = 0 := by
      rw [← cadd, add_neg_cancel, cst, map_zero, gs_zero _ z ⊤ trivial]
    simp only [← Finset.mul_prod_erase F r hy, cst_mul]
    refine (Units.mul_right_inj (gm (𝟙 _) z (t'.PP.L.U (j y) ⊓ t'.PP.L.U i) (t'.PP.L.g (j y) i))).1 ?_
    rw [eq_neg_of_add_eq_zero_right n₀] at k
    linear_combination (cst t'.G.hom z (∏ x ∈ F.erase y, r x)) * k
  obtain ⟨a, ha⟩ : (1 : K) ∈ I := top ▸ Submodule.mem_top
  have ea := (sec_eq_iff _ _ _ _).2 fun j y hy => ((_root_.one_mul _).symm.trans (congrArg (· * _) (cst_one _ _).symm)).trans
    (ha j y hy)
  refine ⟨a, ea, fun a' h' => Chart.eq_of_loc fun p _ => ?_⟩
  obtain ⟨t₁, m₁, h₁⟩ := loc p
  have k : ∀ c, (∀ i, s'.f i = constFn t'.G.hom _ c * σ'.f i) → ∀ y j, m₁.φ y ∈ t'.PP.L.U j →
      gs m₁.φ y _ (s'.f j) = cst t₁.G.hom y (algebraMap K _ c) * gs m₁.φ y _ (σ'.f j) := fun c h y j hj => by
    rw [h, gs_mul _ y _ hj, gs_constFn _ _ _ y hj, m₁.cart.1.w, cst_comp]
  exact (h₁ s').unique (k _ h') (k _ ea)

set_option maxHeartbeats 1000000 in

theorem exists_gen_away (hS : SecBaseChangeAnySt) (hT : SecTwistSt) (o : Obj D l b s) {K : Type} [CommRing K] {x : Sp K ⟶ X}
    {t : SAB H (Sp K)} (n : SABMap t o.t x) (p : Ideal K) [p.IsPrime] : ∃ g ∉ p, ∀ (t' : SAB H (Sp (Localization.Away g)))
      (_ : SABMap t' t (spMap (algebraMap K _))), ∃ β : LB.Sec t'.PP.L, ∀ σ : LB.Sec t'.PP.L,
        ∃! a : Localization.Away g, ∀ i, σ.f i = constFn t'.G.hom _ a * β.f i := by
  have : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n.cart.1 o.proper
  have : CompactSpace t.G.left := QuasiCompact.compactSpace_of_compactSpace t.G.hom
  have := t.semi.smooth
  obtain ⟨t₁, ⟨m₁⟩⟩ := exists_sab (spMap (algebraMap K (Localization.AtPrime p))) t
  obtain ⟨n₁, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ n m₁
  obtain ⟨t₂, ⟨m₂⟩⟩ := exists_sab (spMap (IsLocalRing.residue (Localization.AtPrime p))) t₁
  obtain ⟨β, hβ⟩ := exists_sec_ne_obj hS o n₁ _ m₂.cart.1
  obtain ⟨w₁, g₁, -⟩ := m₁.lin
  obtain ⟨a, ha, σ, hσ⟩ := exists_extend p.primeCompl m₁.cart.1 t.PP.isLB t₁.PP.isLB ((isGen_iff w₁).1 g₁) β
  have := t₂.semi.smooth
  have : IsReduced t₂.G.left := isReduced_of_smooth t₂.G.hom
  obtain ⟨y, j, hj, hu⟩ : ∃ y j, ∃ _ : m₁.φ (m₂.φ y) ∈ t.PP.L.U j, m₁.φ (m₂.φ y) ∈ t.G.left.basicOpen (σ.f j) := by
    by_contra hc
    push Not at hc
    refine hβ fun y k hk => ?_
    obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m₁.φ (m₂.φ y))
    have z : ((m₂.φ ≫ m₁.φ).app _).hom (σ.f j) = 0 := eq_zero_of_basicOpen_eq_bot _ (by
      rw [← Scheme.preimage_basicOpen, eq_bot_iff]
      exact fun y' hy' => hc y' j (t.G.left.basicOpen_le _ hy') hy')
    have e := congrArg (m₂.φ.stalkMap y).hom (hσ (m₂.φ y) j k hj hk)
    rw [← gs_comp m₂.φ _ y _ hj, ← Category.id_comp (m₂.φ ≫ m₁.φ), ← gs_pull (𝟙 _) _ y _ hj, z, gs_zero _ y _ hj, map_mul, map_mul,
      ← gs_stalkMap m₂.φ y _ hk, m₁.cart.1.w, cst_comp] at e
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime p) (⟨a, ha⟩ : p.primeCompl)
    have u₁ : IsUnit (cst t₁.G.hom (m₂.φ y) (algebraMap K _ a)) := IsUnit.of_mul_eq_one (cst t₁.G.hom _ (↑u⁻¹)) (by
      rw [← cst_mul, ← show (u : Localization.AtPrime p) = algebraMap K _ a from hu, Units.mul_inv, cst_one])
    exact ((Units.isUnit _).map _).mul_right_eq_zero.1 ((u₁.map _).mul_right_eq_zero.1 e.symm)
  have hp : t.G.hom (m₁.φ (m₂.φ y)) = (⟨p, ‹_›⟩ : PrimeSpectrum K) := by
    have e : (m₂.φ ≫ m₁.φ) ≫ t.G.hom = t₂.G.hom ≫ spMap (IsLocalRing.residue _) ≫ spMap (algebraMap K _) := by
      rw [Category.assoc, m₁.cart.1.w, ← Category.assoc, m₂.cart.1.w, Category.assoc]
    refine (congrArg (fun q => q y) e).trans (PrimeSpectrum.ext ?_)
    show ((t₂.G.hom y).asIdeal.comap (IsLocalRing.residue _)).comap (algebraMap K _) = p
    have := (t₂.G.hom y).isPrime
    rw [Ideal.eq_bot_of_prime (t₂.G.hom y).asIdeal, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
    exact Localization.AtPrime.under_maximalIdeal
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hg, hW⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
    (⟨_, hu, hp⟩ : (⟨p, ‹_›⟩ : PrimeSpectrum K) ∈ t.G.hom '' (t.G.left.basicOpen (σ.f j) : Set _))
    (t.G.hom.isOpenMap _ (t.G.left.basicOpen (σ.f j)).2)
  refine ⟨g, hg, fun t' m => ?_⟩
  obtain ⟨n', -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ n m
  obtain ⟨w, gw', -⟩ := m.lin
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w).1 gw') t.PP.isLB t'.PP.isLB σ
  refine ⟨σ', gen_of_ne hT o n' σ' fun k _ χ t₃ m₃ h0 => ?_⟩
  let z : Sp k := IsLocalRing.closedPoint k
  obtain ⟨y', hy', e'⟩ := hW (show (spMap χ ≫ spMap (algebraMap K (Localization.Away g))) z ∈ PrimeSpectrum.basicOpen g from
    fun h => (show χ (algebraMap K _ g) ∈ IsLocalRing.maximalIdeal k from h) ((IsLocalization.Away.algebraMap_isUnit g).map χ))
  obtain ⟨y₃, e₃, -⟩ := Scheme.exists_preimage_of_isPullback (m₃.cart.1.paste_horiz m.cart.1) y' z e'
  have hj' : (m₃.φ ≫ m.φ) y₃ ∈ t.PP.L.U j := e₃ ▸ t.G.left.basicOpen_le _ hy'
  obtain ⟨i, hi⟩ := exists_chart t'.PP.isLB (m₃.φ y₃)
  have v := hσ' _ m₃.φ y₃ j i hj' hi
  rw [h0 y₃ i hi, mul_zero, gs_eq _ y₃ _ hj'] at v
  have := ((Scheme.mem_basicOpen _ _ _ hj').1 (e₃ ▸ hy')).map ((m₃.φ ≫ m.φ).stalkMap y₃).hom
  exact not_isUnit_zero (v ▸ (Scheme.Hom.germ_stalkMap_apply (m₃.φ ≫ m.φ) _ y₃ hj' (σ.f j)) ▸ this)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
