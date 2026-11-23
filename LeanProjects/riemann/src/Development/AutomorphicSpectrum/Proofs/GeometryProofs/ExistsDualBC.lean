import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkLoc
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.BT hiding genPt
open GlobalTheory.CompanionTheory.Ar.HTTie
open GlobalTheory.CompanionTheory.Ar.HTChart (dual_comp snd_epsMul)

section Alg

variable {A Ω : Type} [CommRing A] [Field Ω] [Algebra A Ω] {L₀ : Type} [AddCommGroup L₀] [Module A L₀]

theorem clear_denom [Module.Finite A L₀] (hinj : Function.Injective (algebraMap A Ω)) (B : Subring Ω)
    (hB : ∀ b ∈ B, ∃ u a : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      algebraMap A Ω u * b = algebraMap A Ω a)
    (w : L₀ →ₗ[A] Ω) (hw : ∀ b, w b ∈ B) :
    ∃ (u : A) (w₀ : Module.Dual A L₀), algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      ∀ b, algebraMap A Ω (w₀ b) = algebraMap A Ω u * w b := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := L₀)
  have key : ∀ s : Finset L₀, ∃ u : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      ∀ b ∈ s, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp, by simp, by simp⟩
    | insert b s _ ih =>
      obtain ⟨u, h1, h2, h3⟩ := ih
      obtain ⟨u', a, h1', h2', h3'⟩ := hB _ (hw b)
      refine ⟨u * u', by rw [map_mul]; exact mul_ne_zero h1 h1', by rw [map_mul, mul_inv]; exact mul_mem h2 h2',
        fun c hc => ?_⟩
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact ⟨u * a, by rw [map_mul, map_mul, ← h3']; ring⟩
      · obtain ⟨a', ha'⟩ := h3 c hc
        exact ⟨u' * a', by rw [map_mul, map_mul, ha']; ring⟩
  obtain ⟨u, h1, h2, h3⟩ := key s
  have hall : ∀ b, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b := by
    intro b
    have hb : b ∈ Submodule.span A (s : Set L₀) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem c hc => exact h3 c hc
    | zero => exact ⟨0, by simp⟩
    | add c d _ _ hc hd =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨a', ha'⟩ := hd
      exact ⟨a + a', by rw [map_add, map_add, ha, ha', mul_add]⟩
    | smul r c _ hc =>
      obtain ⟨a, ha⟩ := hc
      exact ⟨r * a, by rw [map_mul, map_smul, ha, Algebra.smul_def]; ring⟩
  choose w₀ hw₀ using hall
  refine ⟨u, ⟨⟨w₀, fun a b => hinj ?_⟩, fun r a => hinj ?_⟩, h1, h2, hw₀⟩
  · rw [map_add, hw₀, hw₀, hw₀, map_add, mul_add]
  · show algebraMap A Ω (w₀ (r • a)) = algebraMap A Ω (r * w₀ a)
    rw [map_mul, hw₀, hw₀, map_smul, Algebra.smul_def]; ring

variable {Li : Type} [AddCommGroup Li] [Module Ω Li] [Module A Li] [IsScalarTower A Ω Li]

theorem exists_dualBC [IsDomain A] [IsFractionRing A Ω] [Module.Finite A L₀] (j₀ : L₀ →ₗ[A] Li)
    (hj₀ : IsBaseChange Ω j₀) :
    ∃ j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li, IsBaseChange Ω j ∧
      ∀ w b, j w (j₀ b) = algebraMap A Ω (w b) := by
  have hinj := IsFractionRing.injective A Ω
  let J : Module.Dual A L₀ → Module.Dual Ω Li := fun w => hj₀.lift (Algebra.linearMap A Ω ∘ₗ w)
  have hJ : ∀ w b, J w (j₀ b) = algebraMap A Ω (w b) := fun w b => hj₀.lift_eq _ b
  have hext : ∀ w w' : Module.Dual Ω Li, (∀ b, w (j₀ b) = w' (j₀ b)) → w = w' := fun w w' h => hj₀.algHom_ext _ _ h
  have hsm : ∀ (a : A) (w : Module.Dual Ω Li) e, (a • w) e = algebraMap A Ω a * w e := fun a w e => by
    rw [← algebraMap_smul Ω a w]; rfl
  let j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li :=
    { toFun := J
      map_add' := fun w w' => hext _ _ fun b => by simp [hJ]
      map_smul' := fun a w => hext _ _ fun b => by simp [hJ, hsm] }
  refine ⟨j, (isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) Ω j).1 ⟨fun s => ?_, fun w => ?_, ?_⟩, hJ⟩
  · have hs : algebraMap A Ω s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    refine ⟨fun w w' h => ?_, fun w => ⟨(algebraMap A Ω s)⁻¹ • w, ?_⟩⟩
    · have h' : (s : A) • w = (s : A) • w' := h
      rw [← algebraMap_smul Ω, ← algebraMap_smul Ω (s : A) w'] at h'
      exact smul_right_injective _ hs h'
    · show (s : A) • ((algebraMap A Ω s)⁻¹ • w) = w
      rw [← algebraMap_smul Ω, smul_smul, mul_inv_cancel₀ hs, one_smul]
  · obtain ⟨u, w₀, h1, -, h3⟩ := clear_denom hinj ⊤ (fun b _ => by
      obtain ⟨a, u, hu, rfl⟩ := IsFractionRing.div_surjective (A := A) b
      have := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := Ω) hu
      exact ⟨u, a, this, trivial, by field_simp⟩) ((w.restrictScalars A) ∘ₗ j₀) (fun _ => trivial)
    refine ⟨⟨w₀, ⟨u, mem_nonZeroDivisors_of_ne_zero fun h => h1 (by rw [h, map_zero])⟩⟩, hext _ _ fun b => ?_⟩
    show ((u : A) • w) (j₀ b) = J w₀ (j₀ b)
    rw [hsm, hJ, h3]; rfl
  · intro w w' h
    refine ⟨1, ?_⟩
    have : w = w' := LinearMap.ext fun b => hinj (by rw [← hJ, ← hJ]; exact LinearMap.congr_fun h _)
    rw [this]

end Alg

section Geo

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {A : Type} [CommRing A] [Algebra A Ω] {x : Spec (CommRingCat.of A) ⟶ X}

theorem regAt_frac (hξ : IsCptGen ξ) (hk : Function.Injective (algebraMap A Ω))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) (p : PrimeSpectrum A) (q : Cpt ξ) (hp : x p = q.1)
    (hsub : ∀ a, algebraMap A Ω a ∈ regAt ξ q) :
    (∀ u ∉ p.asIdeal, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ regAt ξ q) ∧
      ∀ b ∈ regAt ξ q, ∃ u a : A, u ∉ p.asIdeal ∧ algebraMap A Ω u * b = algebraMap A Ω a := by
  obtain ⟨_, hS, -, hg⟩ := stalk_loc hξ _ hk x hx p q hp hsub
  have hg' : ∀ a, genMap ξ q (algebraMap A _ a) = algebraMap A Ω a := RingHom.congr_fun hg
  refine ⟨fun u hu => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := (IsLocalization.map_units (X.presheaf.stalk q.1)
      (⟨u, hu⟩ : p.asIdeal.primeCompl)).exists_right_inv
    have h1 : algebraMap A Ω u * genMap ξ q t = 1 := by rw [← hg', ← map_mul, ht, map_one]
    exact ⟨left_ne_zero_of_mul_eq_one h1, t, (eq_inv_of_mul_eq_one_right h1)⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj p.asIdeal.primeCompl c
    exact ⟨s, a, s.2, by rw [← hg', ← hg', ← h, map_mul, mul_comm]⟩

variable {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  (M : LieModel G ξ Li) {L₀ : Type} [AddCommGroup L₀] [Module A L₀] (M₀ : LieModel G x L₀)

omit [IsCommMonObj G] in
theorem exists_lieBC (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) [Module A Li]
    [IsScalarTower A Ω Li] : ∃ j₀ : L₀ →ₗ[A] Li, IsBaseChange Ω j₀ ∧ ∀ v, (M.pt (j₀ v)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left := by
  subst hx
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear X G A Ω (algebraMap A Ω) x L₀ Li M₀ M
  have hj' : ∀ v, (M.pt (j v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left :=
    fun v => (Category.comp_id _).symm.trans (hj v)
  let j₀ : L₀ →ₗ[A] Li :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a v => by rw [j.map_smulₛₗ, algebraMap_smul]; rfl }
  exact ⟨j₀, (lie_proj X G A x L₀ M₀).2.2 Ω Li M j₀ hj', hj'⟩

omit [IsCommMonObj G] [Smooth G.hom] in
theorem tan_ext {O : Type} [CommRing O] [Algebra A O] {z : Spec (CommRingCat.of O) ⟶ X}
    (hzs : Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ x = z) (g : O →+* Ω)
    (hg : g.comp (algebraMap A O) = algebraMap A Ω) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (b : L₀) : ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧
      (M.pt (j₀ b)).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left := by
  let ψ := LieCarrier.epsHom (algebraMap A O) x _ hzs
  have hleft : (ψ ≫ M₀.pt b).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap A O))) ≫ (M₀.pt b).left := rfl
  refine ⟨ψ ≫ M₀.pt b, ?_, ?_⟩
  · have t : _ ≫ (M₀.pt b).left = _ := M₀.tan b
    rw [one_left] at t
    show _ ≫ (ψ ≫ M₀.pt b).left = _
    rw [hleft, one_left, ← Category.assoc, ← spec_comp, dual_fst, spec_comp, Category.assoc, t]
    simp only [Over.mk_hom]
    rw [← Category.assoc, hzs]
  · rw [hleft, hj, ← Category.assoc, ← spec_comp, dual_comp, hg]

theorem tan_denom {O : Type} [CommRing O] [Algebra A O] (S : Submonoid A) [IsLocalization S O]
    {z : Spec (CommRingCat.of O) ⟶ X}
    (hzs : Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ x = z) (g : O →+* Ω)
    (hg : g.comp (algebraMap A O) = algebraMap A Ω) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (e : Li) (v : epsAt z ⟶ G) (hv : IsTanAt G z v)
    (he' : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left) :
    ∃ u ∈ S, ∃ b, algebraMap A Ω u • e = j₀ b := by
  obtain ⟨u, hu, b, hub⟩ := exists_denom lie_proj G S x M₀ hzs v hv
  have hgu : g (algebraMap A O u) = algebraMap A Ω u := RingHom.congr_fun hg u
  refine ⟨u, hu, b, hgu ▸ M.inj (Over.OverMorphism.ext ?_)⟩
  rw [M.smul, he', hj, ← hg, ← dual_comp, spec_comp, Category.assoc, ← hub, ← Category.assoc, ← Category.assoc,
    ← spec_comp, ← spec_comp, dual_eps]

theorem mem_omLat_iff (hξ : IsCptGen ξ) (hk : Function.Injective (algebraMap A Ω))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (q : Cpt ξ) (hq : q.1 ∈ Set.range x) (hsub : ∀ a, algebraMap A Ω a ∈ regAt ξ q) (w : Module.Dual Ω Li) :
    w ∈ M.omLat q ↔ ∀ b, w (j₀ b) ∈ regAt ξ q := by
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum A, x p = q.1 := hq
  obtain ⟨_, hS, hzs, hg⟩ := stalk_loc hξ _ hk x hx p q hp hsub
  have hlat := (lieLat_carrier X G Ω ξ Li M q).1
  refine ⟨fun h b => h _ ((hlat _).2 ?_), fun h e he => ?_⟩
  · exact tan_ext M M₀ hzs (genMap ξ q) hg j₀ hj b
  · obtain ⟨v, hv, he'⟩ := (hlat e).1 he
    obtain ⟨u, hu, b, hje⟩ := tan_denom M M₀ p.asIdeal.primeCompl hzs (genMap ξ q) hg j₀ hj e v hv he'
    obtain ⟨h1, h2⟩ := (regAt_frac hξ hk hx p q hp hsub).1 u hu
    have : w e = (algebraMap A Ω u)⁻¹ * w (j₀ b) := by
      rw [← hje, map_smul, smul_eq_mul, ← _root_.mul_assoc, inv_mul_cancel₀ h1, _root_.one_mul]
    rw [this]
    exact mul_mem h2 (h b)

end Geo

end GlobalTheory.CompanionTheory.HtLink
