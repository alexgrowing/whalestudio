import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuccessiveMinimaPositiveNormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousInvariantsNormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteExtensionSplittingTorsionStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.LineNorm.WedgeMax

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_poly (A A' : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [CommRing A']
    [IsDomain A'] [Algebra A A'] [Module.Finite A A'] (hinj : Function.Injective (algebraMap A A')) (g k : ℕ)
    (J : Type) [Fintype J] (h : J → Fin g → A') (c : ℕ) (hc : c ≠ 0) (hh : ∀ i, ∃ j, h j = Pi.single i (c : A')) :
    ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial (Fin k → Fin g) A), (∀ i, (B i).IsHomogeneous d) ∧
      (∀ s, ∃ (i : Fin n) (c : ℕ), c ≠ 0 ∧
        B i = MvPolynomial.C (c : A) * (MvPolynomial.X s : MvPolynomial (Fin k → Fin g) A) ^ (d : ℕ)) ∧
      ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : A →+* C)
        (m : ℕ) (hk : k ≤ m) (a : Fin m → Fin g → C), LinearIndependent C a → ∀ N : Fin m → ℝ,
        (∀ x' : A' →+* C, x'.comp (algebraMap A A') = x → ∀ l, N l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧
          (∀ l', l < l' → cf l' = 0) ∧ (∀ j, ‖∑ i, x' (h j i) * ∑ l', cf l' * a l' i‖ ≤ 1) ∧ r = ‖cf l‖⁻¹}) →
        ((d : ℕ) : ℝ) * ∑ l : Fin k, Real.log (N (Fin.castLE hk l)) =
          Real.log (⨆ i, ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) := by
  classical
  obtain ⟨d, n, B, hB, hN⟩ := GlobalTheory.T.exists_homogeneous_invariants_norms A A' hinj (Fin k → Fin g) (Fin k → J) fun σ s => ∏ i, h (σ i) (s i)
  let e := Fintype.equivFin (Fin n ⊕ (Fin k → Fin g))
  let B' : Fin n ⊕ (Fin k → Fin g) → MvPolynomial (Fin k → Fin g) A :=
    Sum.elim B fun s => MvPolynomial.C (((c ^ k) ^ (d : ℕ) : ℕ) : A) * MvPolynomial.X s ^ (d : ℕ)
  refine ⟨d, _, fun i => B' (e.symm i), fun i => ?_,
    fun s => ⟨e (Sum.inr s), (c ^ k) ^ (d : ℕ), pow_ne_zero _ (pow_ne_zero _ hc), by simp [B']⟩, ?_⟩
  · show (B' (e.symm i)).IsHomogeneous d
    rcases e.symm i with i | s
    · exact hB i
    · exact (MvPolynomial.isHomogeneous_X_pow s _).C_mul _
  intro C _ _ _ _ x m hk a ha N hx
  obtain ⟨x', hx'⟩ : ∃ x' : A' →+* C, x'.comp (algebraMap A A') = x := by
    by_contra h0
    have h1 := (hN C x (minor a hk) 0 fun y hy => absurd ⟨y, hy⟩ h0).trans
      (hN C x (minor a hk) 1 fun y hy => absurd ⟨y, hy⟩ h0).symm
    simp at h1
  have cov := fun (y : A' →+* C) (hy : y.comp (algebraMap A A') = x) =>
    GlobalTheory.T.successive_minima_positive_norms C g J (fun j i => y (h j i)) (fun b hb => funext fun i => by
      obtain ⟨j, hj⟩ := hh i
      have := hb j
      rw [Finset.sum_eq_single i (fun i' _ hi => by simp [hj, Pi.single_eq_of_ne hi]) (by simp)] at this
      simpa [hj, hc] using this) m a ha N (hx y hy)
  have hP := hN C x (minor a hk) (∏ l : Fin k, N (Fin.castLE hk l)) fun y hy => by
    simp only [map_prod]
    exact ((cov y hy).2 k hk).symm
  have hpos := (cov x' hx').1
  have hP0 : 0 ≤ ∏ l : Fin k, N (Fin.castLE hk l) := Finset.prod_nonneg fun l _ => (hpos _).le
  rw [← Real.log_prod fun l _ => (hpos _).ne', ← Real.log_pow,
    e.symm.iSup_comp (g := fun i => ‖MvPolynomial.eval₂ x (minor a hk) (B' i)‖)]
  congr 1
  refine le_antisymm ?_ (Real.iSup_le ?_ (pow_nonneg hP0 _))
  · rw [hP]
    exact Real.iSup_le (fun i => le_ciSup (f := fun i => ‖MvPolynomial.eval₂ x (minor a hk) (B' i)‖)
      (Finite.bddAbove_range _) (Sum.inl i)) (Real.iSup_nonneg fun _ => norm_nonneg _)
  · rintro (i | s)
    · rw [hP]
      exact le_ciSup (f := fun i => ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) (Finite.bddAbove_range _) i
    · have e1 : ‖MvPolynomial.eval₂ x (minor a hk) (B' (Sum.inr s))‖ = ‖(c : C) ^ k * minor a hk s‖ ^ (d : ℕ) := by
        simp [B', mul_pow]
      rw [e1]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      choose j hj using hh
      rw [(cov x' hx').2 k hk]
      refine le_trans (le_of_eq ?_) (le_ciSup (Finite.bddAbove_range _) fun i => j (s i))
      rw [Finset.sum_eq_single s (fun s' _ hs => ?_) (by simp)]
      · simp [hj]
      · obtain ⟨i, hi⟩ := Function.ne_iff.1 hs
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hj, Pi.single_eq_of_ne hi]), zero_mul]

theorem spMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (dualMap (ψ.comp φ)) = spMap (dualMap ψ) ≫ spMap (dualMap φ) := by
  rw [← spMap_comp]
  congr 1
  exact RingHom.ext fun x => by ext <;> simp [dualMap]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem isTanBasis_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {x : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : IsTanBasis t x e) :
    IsTanBasis t (spMap φ ≫ x) fun i => spMap (dualMap φ) ≫ e i := by
  refine ⟨fun i => GlobalTheory.LieMet.isTan_map φ rfl (he.1 i), fun T _ ψ w => ?_⟩
  have := he.2 T (ψ.comp φ) w
  simpa only [spMap_comp, spMap_dual_comp, Category.assoc] using this

theorem exists_comb {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hu : ∀ l, IsTanAtG t x (u l)) (cf : Fin m → S) : ∃ w, IsTanAtG t x w ∧ IsCombAtG t x u cf w :=
  ⟨_, GlobalTheory.LieMet.isTan_tv (∑ l, cf l • GlobalTheory.LieMet.tanOf (hu l)),
    (GlobalTheory.LieMet.isComb_iff (fun l => GlobalTheory.LieMet.tanOf (hu l)) cf _).2 rfl⟩

theorem comb_unique {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hu : ∀ l, IsTanAtG t x (u l)) {cf : Fin m → S} {w w' : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x u cf w) (h' : IsCombAtG t x u cf w') : w = w' :=
  ((isCombAtG_iff t _ (fun j => ovT (hu j)) _ _).1 h).symm.trans ((isCombAtG_iff t _ (fun j => ovT (hu j)) _ _).1 h')

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

omit [IsUltrametricDist C] in

theorem grNorm_eq {x : Sp C ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber C) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)} {P : (Fin g → C) → Prop}
    (hΛ : ∀ b w, IsCombAtG t x e b w → (w ∈ Λ ↔ P b)) {u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}
    {a : Fin m → Fin g → C} (hu : ∀ l, IsCombAtG t x e (a l) (u l)) (l : Fin m) :
    GlobalTheory.ShFam.Pad.grNorm t x Λ u l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧
      P (fun i => ∑ l', cf l' * a l' i) ∧ r = ‖cf l‖⁻¹} := by
  have hut : ∀ l, IsTanAtG t x (u l) := fun l => by
    obtain ⟨w, hw, hw'⟩ := exists_comb t he (a l)
    exact comb_unique t he hw' (hu l) ▸ hw
  have key : ∀ cf w, IsCombAtG t x u cf w → (w ∈ Λ ↔ P fun i => ∑ l', cf l' * a l' i) := fun cf w hw => by
    refine hΛ _ w ?_
    have := tanLinG e he u (Matrix.of fun i l => a l i) cf w hu hw
    convert this using 2 with i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  unfold GlobalTheory.ShFam.Pad.grNorm
  congr 1
  ext r
  refine exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ => ?_
  refine ⟨fun ⟨w, h1, h2⟩ => (key cf w h2).1 h1, fun hP => ?_⟩
  obtain ⟨w, -, hw⟩ := exists_comb t hut cf
  exact ⟨w, (key cf w hw).2 hP, hw⟩

theorem ext_intO (hX : X.IsSeparated) (x x' : Sp ↥(intO C) ⟶ X)
    (h : spMap (intO C).subtype ≫ x' = spMap (intO C).subtype ≫ x) : x' = x := by
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro z hz
    have : z = 0 := Subtype.ext hz
    simp [this])⟩
  exact ext_of_isDominant (spMap (intO C).subtype) h

theorem mem_latDR (hX : X.IsSeparated) {x : Sp ↥(intO C) ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber ↥(intO C)) ⟶ t.G.left)} (he : IsTanBasis t x e) (b : Fin g → C)
    (w : Sp (DualNumber C) ⟶ t.G.left)
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ x) (fun i => spMap (dualMap (intO C).subtype) ≫ e i) b w) :
    w ∈ latDR t (spMap (intO C).subtype ≫ x) ↔ ∀ i, ‖b i‖ ≤ 1 := by
  have h1 : spMap (RingHom.id ↥(intO C)) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id ↥(intO C)) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id ↥(intO C))) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have hD0 := he.2 _ (RingHom.id ↥(intO C))
  simp only [h1, h3, Category.id_comp] at hD0
  have hDk := (isTanBasis_map t (intO C).subtype he).1
  refine ⟨?_, fun hc => ?_⟩
  · rintro ⟨xO', hx, vO, hv, rfl⟩
    obtain rfl := ext_intO hX _ xO' hx
    obtain ⟨a, ha, -⟩ := hD0 vO hv
    have e := (he.2 C _ _ (GlobalTheory.LieMet.isTan_map (intO C).subtype rfl hv)).unique hw
      (GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha)
    intro i
    rw [e]
    exact (a i).2
  · obtain ⟨v, hv, ha⟩ := exists_comb t he.1 fun i => (⟨b i, hc i⟩ : ↥(intO C))
    exact ⟨x, rfl, v, hv, comb_unique t hDk (GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha) hw⟩

theorem norm_le_one {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] [Module.Finite A A'] (x' : A' →+* C)
    (hx : ∀ a, ‖x' (algebraMap A A' a)‖ ≤ 1) (b : A') : ‖x' b‖ ≤ 1 := by
  have hi : ∀ z : C, z ∈ (NormedField.valuation (K := C)).integer ↔ ‖z‖ ≤ 1 := fun z => by
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast Iff.rfl
  let y : A →+* (NormedField.valuation (K := C)).integer :=
    (x'.comp (algebraMap A A')).codRestrict _ fun a => (hi _).2 (hx a)
  exact (hi _).1 ((Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral
    (IsIntegral.map_of_comp_eq y x' rfl (Algebra.IsIntegral.isIntegral (R := A) b)))

theorem of_covectors {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] (x₀ : Sp A ⟶ X) {g : ℕ}
    {e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)} (he : IsTanBasis t x₀ e) (q k : ℕ) (A' : Type) [CommRing A']
    [IsDomain A'] [Algebra A A'] [Module.Finite A A'] (hinj : Function.Injective (algebraMap A A'))
    (J : Type) [Fintype J] (h : J → Fin g → A') (c : ℕ) (hc : c ≠ 0) (hh : ∀ i, ∃ j, h j = Pi.single i (c : A'))
    (hΛ : ∀ (p : ℕ) [Fact p.Prime] (y : A' →+* ↥(intO ℂ_[p])) (b : Fin g → ℂ_[p])
      (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
      IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ spMap y ≫ spMap (algebraMap A A') ≫ x₀)
        (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ spMap (dualMap y) ≫ spMap (dualMap (algebraMap A A')) ≫ e i)
        b w →
      (w ∈ lat t p (spMap (intO ℂ_[p]).subtype ≫ spMap y ≫ spMap (algebraMap A A') ≫ x₀) (decide (p = q)) ↔
        ∀ j, ‖∑ i, (y (h j i) : ℂ_[p]) * b i‖ ≤ 1)) :
    ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial (Fin k → Fin g) A), (∀ i, (B i).IsHomogeneous d) ∧ (∀ s, ∃ (i : Fin n) (c : ℕ), c ≠ 0 ∧ B i = MvPolynomial.C (c : A) * (MvPolynomial.X s : MvPolynomial (Fin k → Fin g) A) ^ (d : ℕ)) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : A →+* ℂ_[p]), (∀ a, ‖x a‖ ≤ 1) → ∀ (m : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap x ≫ x₀) (fun i => spMap (dualMap x) ≫ e i) (a l) (u l)) → ((d : ℕ) : ℝ) * ∑ l : Fin k, Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap x ≫ x₀) (lat t p (spMap x ≫ x₀) (decide (p = q))) u (Fin.castLE hk l)) = Real.log (⨆ i, ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) := by
  obtain ⟨d, n, B, h1, h2, h3⟩ := exists_poly A A' hinj g k J h c hc hh
  refine ⟨d, n, B, h1, h2, fun p _ x hx m hk u a ha hu => h3 ℂ_[p] x m hk a ha _ fun x' hx' l => ?_⟩
  subst hx'
  let y : A' →+* ↥(intO ℂ_[p]) := x'.codRestrict _ fun b => norm_le_one x' hx b
  have e1 : x' = (intO ℂ_[p]).subtype.comp y := rfl
  refine grNorm_eq t (isTanBasis_map t _ he).1 (P := fun b => ∀ j, ‖∑ i, x' (h j i) * b i‖ ≤ 1) ?_ hu l
  have := hΛ p y
  rw [e1]
  simpa only [spMap_comp, spMap_dual_comp, Category.assoc, RingHom.comp_apply, Subring.coe_subtype] using this

theorem norm_sum_single {g : ℕ} {A' : Type} [CommRing A'] (y : A' →+* ↥(intO C)) (c : ℕ) (b : Fin g → C) (i : Fin g) :
    ∑ i', (y ((Pi.single i (c : A') : Fin g → A') i') : C) * b i' = c * b i := by
  rw [Finset.sum_eq_single i (fun i' _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
  simp

theorem wedge_norm_max : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (x₀ : Sp A ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)), IsTanBasis t x₀ e → ∀ q k : ℕ, ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial (Fin k → Fin g) A), (∀ i, (B i).IsHomogeneous d) ∧ (∀ s, ∃ (i : Fin n) (c : ℕ), c ≠ 0 ∧ B i = MvPolynomial.C (c : A) * (MvPolynomial.X s : MvPolynomial (Fin k → Fin g) A) ^ (d : ℕ)) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : A →+* ℂ_[p]), (∀ a, ‖x a‖ ≤ 1) → ∀ (m : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap x ≫ x₀) (fun i => spMap (dualMap x) ≫ e i) (a l) (u l)) → ((d : ℕ) : ℝ) * ∑ l : Fin k, Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap x ≫ x₀) (lat t p (spMap x ≫ x₀) (decide (p = q))) u (Fin.castLE hk l)) = Real.log (⨆ i, ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) := by
  intro hHT E _ _ _ H X _ t hX A _ _ _ _ _ x₀ g e he q k
  by_cases hq : q.Prime
  · obtain ⟨A', _, _, _, _, hinj, _, hζ, hsp⟩ := GlobalTheory.T.exists_finite_extension_splitting_torsion E H X t A x₀ q hq.ne_zero
    have : CharZero A' := charZero_of_injective_algebraMap hinj
    have he' := isTanBasis_map t (algebraMap A A') he
    obtain ⟨n, h, hh⟩ := GlobalTheory.T.exists_tangent_presentation_prime E H X t A' _ g _ he' q hq hζ hsp
    refine of_covectors t x₀ he q k A' hinj (Fin n ⊕ Fin g) (Sum.elim h fun i => Pi.single i (q : A')) q hq.ne_zero
      (fun i => ⟨Sum.inr i, rfl⟩) fun p _ y b w hw => ?_
    simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, norm_sum_single]
    have hn : ∀ r : ℕ, ‖(r : ℂ_[p])‖ = ‖(r : ℚ_[p])‖ := fun r => by
      rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    by_cases hp : p = q
    · subst hp
      rw [decide_eq_true rfl]
      exact GlobalTheory.T.unique_integral_lift_norm_p_inverse hHT E H X t p ℂ_[p] (by rw [hn, Padic.norm_p]) _ (ext_intO hX _) g _
        (isTanBasis_map t y he') n (fun j i => y (h j i)) (hh ℂ_[p] y).1 (hh ℂ_[p] y).2 b w hw
    · rw [decide_eq_false hp]
      have h1 : ‖(q : ℂ_[p])‖ = 1 := by
        rw [hn, Padic.norm_natCast_eq_one_iff]
        exact (Nat.coprime_primes Fact.out hq).2 hp
      refine (mem_latDR t hX (isTanBasis_map t y he') b w hw).trans ?_
      simp only [norm_mul, h1, _root_.one_mul]
      refine ⟨fun hb => ⟨fun j => ?_, hb⟩, fun hb => hb.2⟩
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (y (h j i)).2 (norm_nonneg _) (hb i)
  · have he' := isTanBasis_map t (algebraMap A A) he
    refine of_covectors t x₀ he q k A (fun _ _ h => h) (Fin g) (fun i => Pi.single i ((1 : ℕ) : A)) 1 one_ne_zero
      (fun i => ⟨i, rfl⟩) fun p hp y b w hw => ?_
    simp only [norm_sum_single]
    rw [decide_eq_false fun h : p = q => hq (h ▸ hp.out)]
    simp only [Nat.cast_one, _root_.one_mul]
    exact mem_latDR t hX (isTanBasis_map t y he') b w hw

end GlobalTheory.LineNorm.WedgeMax
