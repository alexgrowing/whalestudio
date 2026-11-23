import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLatticeUniformisationOfPrimThetaStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransportThetaLevelUniformisationCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDiagonalCoordinatesOfDeterminantConditionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodLatticeInGenusStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosedStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPeriod

theorem linear_eq_zero_of_mem_discrete {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, F z ∈ Λ) (z : Fin g → ℂ) : F z = 0 := by
  have hc : Continuous fun w => (⟨F w, h w⟩ : Λ) := F.continuous_of_finiteDimensional.subtype_mk _
  have := PreconnectedSpace.constant inferInstance hc (x := z) (y := 0)
  simpa using congrArg Subtype.val this

theorem sub_mem_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {z w : Fin g → ℂ} (h : u.ex z = u.ex w) : z - w ∈ u.Λ := by
  rw [← u.ker]
  have := u.ex_add (z - w) w
  rw [sub_add_cancel, h] at this
  exact mul_eq_right.1 this.symm

open Matrix in

theorem exists_coord {g : ℕ} {La La' : Type} [AddCommGroup La] [AddCommGroup La'] (Q : La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : La' ≃+ La) (Q' : La' →+ (Fin g → ℂ))
    (hQ : ∀ x, h (Q' x) = Q (e x)) (inj : Function.Injective Q) (disc : DiscreteTopology Q.range)
    (span : Submodule.span ℝ (Set.range Q) = ⊤) (herm : Hm.IsHermitian)
    (pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    ∃ Hm' : Matrix (Fin g) (Fin g) ℂ, Function.Injective Q' ∧ DiscreteTopology Q'.range ∧
      Submodule.span ℝ (Set.range Q') = ⊤ ∧ Hm'.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) ∧
      ∀ x y, hermForm Hm' (Q' x) (Q' y) = hermForm Hm (Q (e x)) (Q (e y)) := by
  let L := h.toLinearMap
  let M := LinearMap.toMatrix' L
  have key : ∀ z w, hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [← LinearMap.toMatrix'_mulVec L z, ← LinearMap.toMatrix'_mulVec L w, hermForm, hermForm, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, star_mulVec, ← mulVec_transpose]
    rfl
  refine ⟨Mᵀ * Hm * Mᵀᴴ, fun x y hxy => e.injective (inj (by rw [← hQ, ← hQ, hxy])), ?_, ?_,
    isHermitian_mul_mul_conjTranspose _ herm, fun z hz => ?_, fun x y => ?_⟩
  · let m : Q'.range → Q.range := fun z => ⟨h z, by
      obtain ⟨_, x, rfl⟩ := z
      exact ⟨e x, (hQ x).symm⟩⟩
    have hm : Continuous m :=
      (L.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hm fun z w hzw =>
      Subtype.ext (h.injective (congrArg Subtype.val hzw))
  · have r : Set.range Q' = (h.symm.toLinearMap.restrictScalars ℝ) '' Set.range Q := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨_, ⟨e x, rfl⟩, by simp [← hQ]⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨e.symm x, h.injective (by simp [hQ])⟩
    rw [r, Submodule.span_image, span, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  · rw [key]
    exact pos _ fun h0 => hz (h.injective (h0.trans (map_zero h).symm))
  · rw [key, ← hQ, ← hQ]
    rfl

theorem exists_module {O : Type} [CommRing O] {g : ℕ} {La : Type} [AddCommGroup La] (ty : Fin g → (O →+* ℂ))
    (Q : La →+ (Fin g → ℂ)) (inj : Function.Injective Q) (st : ∀ c x, ∃ y, ∀ i, Q y i = ty i c * Q x i) :
    ∃ _ : Module O La, ∀ (c : O) x i, Q (c • x) i = ty i c * Q x i := by
  choose sm hsm using st
  letI : SMul O La := ⟨sm⟩
  have hs : ∀ (c : O) x i, Q (c • x) i = ty i c * Q x i := hsm
  refine ⟨{ one_smul := fun x => inj (funext fun i => by simp [hs])
            mul_smul := fun c d x => inj (funext fun i => by simp [hs, _root_.mul_assoc])
            smul_zero := fun c => inj (funext fun i => by simp [hs])
            smul_add := fun c x y => inj (funext fun i => by simp [hs, mul_add])
            add_smul := fun c d x => inj (funext fun i => by simp [hs, add_mul])
            zero_smul := fun x => inj (funext fun i => by simp [hs]) }, hs⟩

theorem exists_period : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)), a w = H.w0 → a w' = H.bar H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → PELClass D a bas ρ em t → ∃ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) ∧ IsPeriod D' ty Q ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro l1 l2 l3 l4 E _ _ _ H D o _ g k J b em w w' a bas ρ ty t hw hw' hρ hty hP
  obtain ⟨La, _, EF, lam, ac, Q₀, Hm₀, hbij, hpol, -, u, χ, hAH, hΛ, hχ, hpt, hac⟩ :=
    GlobalTheory.T.exists_lattice_uniformisation_of_prim_theta l1 l2 l3 l4 o g k J b em w w' t ((GlobalTheory.T.pelObjectClass_prim_and_iso_closed E H D o g k J b em w w' a bas ρ t hP).1 hw hw')
  obtain ⟨act, haj, hdet, hadj, I, hζ, hev⟩ := exists_act hP
  change OAct (𝓞 E) t.A at act
  rw [hρ] at hdet
  obtain ⟨h, hh⟩ : ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ (c : 𝓞 E) z,
      u.ex (h (fun i => ty i (c : E) * z i)) = u.ex (h z) ≫ act.act c :=
    GlobalTheory.T.exists_diagonal_coordinates_of_determinantCondition l1 l2 l3 l4 E H D t.pol u Hm₀ χ act ty hAH hty hdet
  obtain ⟨inj, disc, span, herm, pos, him⟩ := id hpol
  let F : 𝓞 E → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) := fun c =>
    h.toLinearMap ∘ₗ (LinearMap.pi fun i => ty i (c : E) • LinearMap.proj i) ∘ₗ h.symm.toLinearMap
  have hF₀ : ∀ c z, F c z = h fun i => ty i (c : E) * h.symm z i := fun c z => rfl
  have hF : ∀ c z, u.ex (F c z) = u.ex z ≫ act.act c := fun c z => by
    have := hh c (h.symm z)
    rw [h.apply_symm_apply] at this
    exact this
  let Q₁ : La →+ (Fin g → ℂ) := h.symm.toLinearMap.toAddMonoidHom.comp Q₀
  have hQ₁ : ∀ x, h (Q₁ x) = Q₀ x := fun x => h.apply_symm_apply _
  obtain ⟨Hm₁, inj₁, disc₁, span₁, herm₁, pos₁, him₁⟩ :=
    exists_coord Q₀ Hm₀ h (AddEquiv.refl _) Q₁ hQ₁ inj disc span herm pos
  obtain ⟨_, hs⟩ := exists_module (fun i => (ty i).comp (algebraMap (𝓞 E) E)) Q₁ inj₁ (fun c x => by
    haveI := act.hom c
    have h1 : u.ex (Q₀ x) = 1 := (u.ker _).2 ((hΛ _).2 ⟨x, rfl⟩)
    have h2 : u.ex (F c (Q₀ x)) = 1 := by
      rw [hF, h1]
      exact MonObj.one_comp _
    obtain ⟨y, hy⟩ := (hΛ _).1 ((u.ker _).1 h2)
    refine ⟨y, fun i => ?_⟩
    show h.symm (Q₀ y) i = _
    rw [hy, hF₀, h.symm_apply_apply]
    rfl)
  have hs₀ : ∀ c x, Q₀ (c • x) = F c (Q₀ x) := fun c x => by
    rw [← hQ₁, hF₀]
    exact congrArg h (funext fun i => hs c x i)
  have adj : ∀ (c : 𝓞 E) x y, EF (c • x) y = EF x (H.bar c • y) := fun c x y => by
    have := (GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint l1 l2 l3 l4 t.pol u Hm₀ χ _ _ (F c) (F (H.bar c)) hAH (act.hom _) (act.hom _)
      (hF c) (hF _)).1 (hadj c) (Q₀ x) (Q₀ y)
    have h2 : ((EF (c • x) y : ℤ) : ℝ) = EF x (H.bar c • y) := by
      rw [← him, ← him, hs₀, hs₀]
      exact congrArg Complex.im this
    exact_mod_cast h2
  obtain ⟨D', e, hp, hq, hEF⟩ := GlobalTheory.PeriodDatum.exists_datum E H La EF D.p D.q g ty Q₁ Hm₁ hty hbij adj hs inj₁
    disc₁ span₁ herm₁ pos₁ (fun x y => by rw [him₁]; exact him x y)
  let Q₂ : D'.La →+ (Fin g → ℂ) := Q₀.comp e.toLinearMap.toAddMonoidHom
  have hQ₂ : ∀ x, Q₂ x = Q₀ (e x) := fun x => rfl
  obtain ⟨f, ν, hgen, hf⟩ := GlobalTheory.T.period_lattice_in_genus_alt l1 l2 l3 l4 E H D D' t.pol u Hm₀ χ act Q₂ hp hq hAH
    (inj.comp e.injective)
    (fun z => (hΛ z).trans ⟨fun ⟨x, hx⟩ => ⟨e.symm x, (congrArg Q₀ (e.apply_symm_apply x)).trans hx⟩,
      fun ⟨x, hx⟩ => ⟨e x, hx⟩⟩)
    (fun x y => by rw [hEF]; exact him _ _)
    (fun c n x => by
      have := hF c ((n : ℂ)⁻¹ • Q₀ (e x))
      rw [map_smul, ← hs₀, ← map_smul e] at this
      exact this) I
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  obtain ⟨hζ', hev'⟩ := hf k (Nat.pos_of_ne_zero (Nat.cast_ne_zero.1 hk))
  let Q : D'.La →+ (Fin g → ℂ) := Q₁.comp e.toLinearMap.toAddMonoidHom
  obtain ⟨Hm, inj', disc', span', herm', pos', him'⟩ :=
    exists_coord Q₀ Hm₀ h e.toAddEquiv Q (fun x => hQ₁ _) inj disc span herm pos
  have him'' : ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y := fun x y => by
    rw [him', hEF]; exact him _ _
  refine ⟨D', f, ν, Q, Hm, hgen, hζ.symm.trans hζ', ⟨fun c x i => ?_, inj', disc', span', Hm, herm', pos', him''⟩,
    ⟨inj', disc', span', herm', pos', him''⟩, ?_⟩
  · show Q₁ (e (c • x)) i = _ * Q₁ (e x) i
    rw [map_smul]
    exact hs _ _ _
  · refine GlobalTheory.T.transport_thetaLevel_uniformisation_coordinates o g k J b em w w' t La EF lam ac Q₀ Hm₀ D'.La D'.EF
      (fun i => f k (bas (Pi.single i 1))) (fun j x => a j • x) Q Hm e.symm.toAddEquiv h.symm hpol
      ⟨inj', disc', span', herm', pos', him''⟩ (fun x => ?_) (fun x y => ?_) (fun j x => ?_) (fun i => ?_)
      ⟨u, χ, hAH, hΛ, hχ, hpt, hac⟩
    · show Q₁ (e (e.symm x)) = _
      rw [e.apply_symm_apply]
      rfl
    · show D'.EF (e.symm x) (e.symm y) = _
      rw [hEF, e.apply_symm_apply, e.apply_symm_apply]
    · show e.symm (ac j x) = a j • e.symm x
      rw [← map_smul]
      congr 1
      obtain ⟨G, hG, hG'⟩ := hac j
      haveI := u.discrete
      have h0 := linear_eq_zero_of_mem_discrete u.Λ (G - F (a j))
        (fun z => sub_mem_of_ex_eq u (by rw [hG', hF, haj])) (Q₀ x)
      apply inj
      rw [hs₀, ← hG]
      exact sub_eq_zero.1 h0
    · have h1 : u.ex ((k : ℂ)⁻¹ • Q₀ (lam i)) = u.ex ((k : ℂ)⁻¹ • Q₂ (f k (bas (Pi.single i 1)))) :=
        Over.OverMorphism.ext ((hpt i).symm.trans ((hev i).symm.trans (hev' _)))
      obtain ⟨y, hy⟩ := (hΛ _).1 (sub_mem_of_ex_eq u h1)
      refine ⟨e.symm y, e.injective (inj ?_)⟩
      show Q₀ (e (e.symm (lam i))) = Q₀ (e (f k (bas (Pi.single i 1)) + k • e.symm y))
      rw [e.apply_symm_apply, map_add, map_nsmul, e.apply_symm_apply, map_add, map_nsmul, hy, hQ₂, ← smul_sub,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk, one_smul]
      abel

end GlobalTheory.PELPeriod
