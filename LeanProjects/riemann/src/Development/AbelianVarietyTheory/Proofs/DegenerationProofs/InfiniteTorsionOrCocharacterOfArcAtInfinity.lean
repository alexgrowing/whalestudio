import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineUnitChartSmoothGroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasicOpenFactorFieldPointAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcQuotientTwoVariableCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SubstTwoVariablesIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLeadingQuotientWeightedArcsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.InfinitePowCharEqOneOfAdditiveFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOneParameterSubgroupOfRationalFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcExtendsOfRegularSecondAxisStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PowerSeriesGenericRelationChainStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightedOrderSlopeComparisonStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.ArcInf
variable {k : Type} [Field k]

abbrev toK (k : Type) [Field k] : PowerSeries k →ₐ[k] FractionRing (PowerSeries k) :=
  IsScalarTower.toAlgHom k (PowerSeries k) (FractionRing (PowerSeries k))

theorem toK_injective : Function.Injective (toK k) := IsFractionRing.injective (PowerSeries k) _

def ev0 (k : Type) [Field k] : PowerSeries k →ₐ[k] k :=
  { PowerSeries.constantCoeff (R := k) with commutes' := fun c => by simp [PowerSeries.algebraMap_apply] }

theorem laurentCoeffEvalLinear_apply (x : PowerSeries k) : ev0 k x = PowerSeries.constantCoeff x := rfl

section Red
variable {G : Over (Sp k)}

def Red (x : algOver k (FractionRing (PowerSeries k)) ⟶ G) (c : algOver k k ⟶ G) : Prop :=
  ∃ b : algOver k (PowerSeries k) ⟶ G, algOverHom (toK k) ≫ b = x ∧ algOverHom (ev0 k) ≫ b = c

theorem Red.unique (hG : IsSeparated G.hom) {x : algOver k (FractionRing (PowerSeries k)) ⟶ G}
    {c c' : algOver k k ⟶ G} (h : Red x c) (h' : Red x c') : c = c' := by
  obtain ⟨b, h1, rfl⟩ := h
  obtain ⟨b', h2, rfl⟩ := h'
  have hd : IsDominant (algOverHom (toK k)).left := by
    rw [algOverHom_left]
    refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 ?_⟩
    intro x hx
    have : x = 0 := toK_injective (hx.trans (map_zero _).symm)
    simp [this]
  have hr : IsReduced (algOver k (PowerSeries k)).left := inferInstanceAs (IsReduced (Sp (PowerSeries k)))
  have : b = b' := by
    ext1
    refine ext_of_isDominant_of_isSeparated G.hom ?_ (algOverHom (toK k)).left ?_
    · rw [Over.w, Over.w]
    · rw [← Over.comp_left, ← Over.comp_left, h1, h2]
  rw [this]

variable [GrpObj G]

theorem Red.mul {x y : algOver k (FractionRing (PowerSeries k)) ⟶ G} {c c' : algOver k k ⟶ G}
    (h : Red x c) (h' : Red y c') : Red (x * y) (c * c') := by
  obtain ⟨b, rfl, rfl⟩ := h
  obtain ⟨b', rfl, rfl⟩ := h'
  exact ⟨b * b', MonObj.comp_mul _ _ _, MonObj.comp_mul _ _ _⟩

theorem Red.inv {x : algOver k (FractionRing (PowerSeries k)) ⟶ G} {c : algOver k k ⟶ G}
    (h : Red x c) : Red x⁻¹ c⁻¹ := by
  obtain ⟨b, rfl, rfl⟩ := h
  exact ⟨b⁻¹, GrpObj.comp_inv _ _, GrpObj.comp_inv _ _⟩

end Red

theorem exists_sig {z : PowerSeries k} (h : PowerSeries.constantCoeff z = 0 ∧ z ≠ 0) :
    ∃ σ : FractionRing (PowerSeries k) →ₐ[k] FractionRing (PowerSeries k),
      ∀ x : PowerSeries k, σ (algebraMap _ _ x) = toK k (x.subst z) := by
  have hs : PowerSeries.HasSubst z := PowerSeries.HasSubst.of_constantCoeff_zero' h.1
  obtain ⟨σ, hσ⟩ := exists_lift ((toK k).comp (PowerSeries.substAlgHom hs)) (by
    rw [AlgHom.comp_apply, PowerSeries.substAlgHom_X]
    exact IsUnit.mk0 _ fun e => h.2 (toK_injective (e.trans (map_zero _).symm)))
  exact ⟨σ, fun x => by rw [hσ, AlgHom.comp_apply, PowerSeries.coe_substAlgHom]⟩

open scoped Classical in

def sig (z : PowerSeries k) : FractionRing (PowerSeries k) →ₐ[k] FractionRing (PowerSeries k) :=
  if h : PowerSeries.constantCoeff z = 0 ∧ z ≠ 0 then (exists_sig h).choose else AlgHom.id k _

theorem sig_apply {z : PowerSeries k} (h : PowerSeries.constantCoeff z = 0) (h0 : z ≠ 0) (x : PowerSeries k) :
    sig z (algebraMap _ _ x) = toK k (x.subst z) := by
  rw [sig, dif_pos ⟨h, h0⟩]
  exact (exists_sig ⟨h, h0⟩).choose_spec x

section Rel
variable {G : Over (Sp k)} [GrpObj G] (a : algOver k (FractionRing (PowerSeries k)) ⟶ G)

def Rel (z w : PowerSeries k) (c : algOver k k ⟶ G) : Prop :=
  Red ((algOverHom (sig w) ≫ a) * (algOverHom (sig z) ≫ a)⁻¹) c

variable {a}

theorem Rel.trans {x y z : PowerSeries k} {c c' : algOver k k ⟶ G} (h : Rel a x y c) (h' : Rel a y z c') :
    Rel a x z (c' * c) := by
  have := Red.mul h' h
  rwa [_root_.mul_assoc, inv_mul_cancel_left] at this

theorem Rel.symm {x y : PowerSeries k} {c : algOver k k ⟶ G} (h : Rel a x y c) : Rel a y x c⁻¹ := by
  have := Red.inv h
  rwa [mul_inv_rev, inv_inv] at this

variable {A : Type} [CommRing A] [Algebra k A] {j : algOver k A ⟶ G} {ε : A →ₐ[k] k} {r : ℕ} {f : Fin r → A}
  {h : Fin r → MvPowerSeries (Fin 2) k} {d : MvPowerSeries (Fin 2) k}

theorem TwoVar.arc (ht : TwoVar j f a h d) {z w : PowerSeries k} (hz : PowerSeries.constantCoeff z = 0)
    (hw : PowerSeries.constantCoeff w = 0) (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hd : MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0) :
    ∃ χ : A →ₐ[k] FractionRing (PowerSeries k),
      (∀ i, χ (f i) * toK k (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d) =
        toK k (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i))) ∧
      (algOverHom (sig w) ≫ a) * (algOverHom (sig z) ≫ a)⁻¹ = algOverHom χ ≫ j := by
  have hs : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> assumption
  have hτ : ∀ x : MvPowerSeries (Fin 2) k, ((toK k).comp (MvPowerSeries.substAlgHom hs)) x =
      toK k (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) x) := fun x => by
    rw [AlgHom.comp_apply, MvPowerSeries.coe_substAlgHom]
  obtain ⟨χ, h1, h2⟩ := ht _ ((toK k).comp (MvPowerSeries.substAlgHom hs)) (sig z) (sig w)
    (by rw [hτ]; exact fun e => hd (toK_injective (e.trans (map_zero _).symm)))
    (fun x => by rw [hτ, sig_apply hz hz0, ((GlobalTheory.T.subst_two_variables_identities_alt k).2 x z w hz hw).1])
    (fun x => by rw [hτ, sig_apply hw hw0, ((GlobalTheory.T.subst_two_variables_identities_alt k).2 x z w hz hw).2])
  exact ⟨χ, fun i => by rw [← hτ, ← hτ]; exact h1 i, by rw [h2, mul_inv_cancel_right]⟩

theorem TwoVar.rel (hc : IsChart G j ε f) (ht : TwoVar j f a h d) {z w : PowerSeries k}
    (hz : PowerSeries.constantCoeff z = 0)
    (hw : PowerSeries.constantCoeff w = 0) (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hd : MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0) (y : Fin r → PowerSeries k)
    (hy : ∀ i, y i * MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d =
      MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i)) :
    ∃ χ : A →ₐ[k] k, (∀ i, χ (f i) = PowerSeries.constantCoeff (y i)) ∧ Rel a z w (algOverHom χ ≫ j) := by
  obtain ⟨χ, h1, h2⟩ := ht.arc hz hw hz0 hw0 hd
  have hf : ∀ i, χ (f i) = toK k (y i) := fun i => by
    have := h1 i
    rw [← hy i, map_mul] at this
    exact mul_right_cancel₀ (fun e => hd (toK_injective (e.trans (map_zero _).symm))) this
  have hm : ∀ x, χ x ∈ (toK k).range := fun x => by
    have : Algebra.adjoin k (Set.range f) ≤ (toK k).range.comap χ :=
      Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact ⟨y i, (hf i).symm⟩)
    exact this (hc.2.2.1 ▸ Algebra.mem_top)
  let χ₀ : A →ₐ[k] PowerSeries k :=
    (AlgEquiv.ofInjective (toK k) toK_injective).symm.toAlgHom.comp (χ.codRestrict _ hm)
  have e : (toK k).comp χ₀ = χ := by
    ext x
    exact congrArg Subtype.val ((AlgEquiv.ofInjective (toK k) toK_injective).apply_symm_apply ⟨χ x, hm x⟩)
  refine ⟨(ev0 k).comp χ₀, fun i => ?_, algOverHom χ₀ ≫ j, ?_, ?_⟩
  · have : χ₀ (f i) = y i := toK_injective ((AlgHom.congr_fun e (f i)).trans (hf i))
    rw [AlgHom.comp_apply, this, laurentCoeffEvalLinear_apply]
  · rw [h2, ← Category.assoc, ← algOverHom_comp, e]
  · rw [← Category.assoc, ← algOverHom_comp]

theorem TwoVar.of_rel_one (hc : IsChart G j ε f) (ht : TwoVar j f a h d) {z w : PowerSeries k}
    (hz : PowerSeries.constantCoeff z = 0)
    (hw : PowerSeries.constantCoeff w = 0) (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hd : MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0) (hr : Rel a z w 1) (i : Fin r) :
    ∃ y : PowerSeries k, PowerSeries.constantCoeff y = 0 ∧
      y * MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d =
      MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i) := by
  obtain ⟨χ, h1, h2⟩ := ht.arc hz hw hz0 hw0 hd
  obtain ⟨b, hb1, hb2⟩ := hr
  obtain ⟨e, he, hl⟩ := GlobalTheory.T.exists_basicOpen_factor_fieldPoint_affineOpen k G A (PowerSeries k) k j b (ev0 k) ε hc.1 (hb2.trans hc.2.1.symm)
  obtain ⟨χ₀, h0⟩ := hl (PowerSeries k) (AlgHom.id k _)
    (PowerSeries.isUnit_iff_constantCoeff.2 (IsUnit.mk0 _ he))
  rw [algOverHom_id, Category.id_comp] at h0
  subst h0
  rw [← Category.assoc, ← algOverHom_comp] at hb1 hb2
  have e1 := eq_of_comp_eq hc.1 (hb1.trans h2)
  have e2 := eq_of_comp_eq hc.1 (hb2.trans hc.2.1.symm)
  refine ⟨χ₀ (f i), (AlgHom.congr_fun e2 (f i)).trans (hc.2.2.2 i), toK_injective ?_⟩
  rw [map_mul, ← h1 i, ← e1, AlgHom.comp_apply]

theorem const_of_le {m : ℕ} (hm : 1 ≤ m) {z : PowerSeries k} (hz : (m : ℕ∞) ≤ z.order) :
    PowerSeries.constantCoeff z = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast hm) hz)

theorem le_order_mon (t : k) (n : ℕ) : (n : ℕ∞) ≤ (PowerSeries.C t * PowerSeries.X ^ n : PowerSeries k).order :=
  PowerSeries.nat_le_order _ _ fun i hi => by simp [PowerSeries.coeff_X_pow, hi.ne]

theorem coeff_mon (t : k) (n : ℕ) : PowerSeries.coeff n (PowerSeries.C t * PowerSeries.X ^ n : PowerSeries k) = t := by
  simp [PowerSeries.coeff_X_pow]

theorem order_mon {t : k} (ht : t ≠ 0) (n : ℕ) : (PowerSeries.C t * PowerSeries.X ^ n : PowerSeries k).order = n :=
  le_antisymm (PowerSeries.order_le n (by rwa [coeff_mon])) (le_order_mon t n)

theorem ne_zero_of_coeff {n : ℕ} {z : PowerSeries k} (hz : PowerSeries.coeff n z ≠ 0) : z ≠ 0 := by
  rintro rfl
  simp at hz

theorem coeff_ne_of_order {n : ℕ} {z : PowerSeries k} (hz : z.order = n) : PowerSeries.coeff n z ≠ 0 :=
  (PowerSeries.order_eq_nat.1 hz).1

theorem le_order_sub {n : ℕ∞} {z w : PowerSeries k} (hz : n ≤ z.order) (hw : n ≤ w.order) : n ≤ (z - w).order := by
  rw [sub_eq_add_neg]
  refine le_trans (le_min hz ?_) (PowerSeries.min_order_le_order_add _ _)
  rwa [PowerSeries.order_neg]

variable [IsAlgClosed k]

theorem TwoVar.lt_of_rel (hc : IsChart G j ε f) (ht : TwoVar j f a h d) (hd : d ≠ 0) {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hr : ∀ z w : PowerSeries k, z.order = m → w.order = n → Rel a z w 1) (i : Fin r) :
    MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i) := by
  by_contra hlt
  have hle := not_lt.1 hlt
  have hi : h i ≠ 0 := by
    intro e
    rw [e, MvPowerSeries.weightedOrder_zero, top_le_iff, MvPowerSeries.weightedOrder_eq_top_iff] at hle
    exact hd hle
  obtain ⟨P₁, Q₁, hP₁, -, h₁⟩ := GlobalTheory.T.exists_leading_quotient_weighted_arcs k m n hm hn 1 (fun _ => d) (h i) hi (fun _ => hle)
  obtain ⟨P₂, Q₂, hP₂, -, h₂⟩ := GlobalTheory.T.exists_leading_quotient_weighted_arcs k m n hm hn 0 Fin.elim0 d hd (fun i => i.elim0)
  obtain ⟨t, ht0⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card (Polynomial.X * P₁ * P₂)
    (mul_ne_zero (mul_ne_zero Polynomial.X_ne_zero hP₁) hP₂)
    (lt_of_lt_of_le Cardinal.natCast_lt_aleph0 (Cardinal.aleph0_le_mk k))
  simp only [Polynomial.eval_mul, Polynomial.eval_X, ne_eq, mul_eq_zero, not_or] at ht0
  have c1 : PowerSeries.coeff m (PowerSeries.C (1 : k) * PowerSeries.X ^ m : PowerSeries k) = 1 ^ m := by
    rw [coeff_mon, one_pow]
  have c2 : PowerSeries.coeff n (PowerSeries.C t * PowerSeries.X ^ n : PowerSeries k) = 1 ^ n * t := by
    rw [coeff_mon, one_pow, _root_.one_mul]
  obtain ⟨-, y, hy⟩ := h₁ 1 t _ _ one_ne_zero (le_order_mon 1 m) (le_order_mon t n) c1 c2 ht0.1.2
  obtain ⟨hD, -⟩ := h₂ 1 t _ _ one_ne_zero (le_order_mon 1 m) (le_order_mon t n) c1 c2 ht0.2
  obtain ⟨y', hy0, hy'⟩ := ht.of_rel_one hc (const_of_le hm (le_order_mon 1 m)) (const_of_le hn (le_order_mon t n))
    (ne_zero_of_coeff (n := m) (by rw [coeff_mon]; exact one_ne_zero))
    (ne_zero_of_coeff (n := n) (by rw [coeff_mon]; exact ht0.1.1)) hD
    (hr _ _ (order_mon one_ne_zero m) (order_mon ht0.1.1 n)) i
  have e := (hy 0).1
  rw [← hy', ← _root_.mul_assoc] at e
  have e1 : y 0 * y' = 1 := mul_right_cancel₀ hD (e.trans (_root_.one_mul _).symm)
  have e2 := congrArg PowerSeries.constantCoeff e1
  simp [hy0] at e2

theorem TwoVar.gen_of_lt (hc : IsChart G j ε f) (ht : TwoVar j f a h d) (hd : d ≠ 0) {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hq : ∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i))
    (z : PowerSeries k) (hz : z.order = m) :
    ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → Rel a z (PowerSeries.C t * PowerSeries.X ^ n) 1 := by
  obtain ⟨Pd, P, hPd, hP, hg⟩ := GlobalTheory.T.exists_leading_quotient_weighted_arcs k m n hm hn r h d hd (fun i => (hq i).le)
  have hz0 := coeff_ne_of_order hz
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (PowerSeries.coeff m z) (n := m) hm
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hs
    exact hz0 hs.symm
  refine ⟨insert 0 ((fun t => s ^ n * t) '' {t | Pd.IsRoot t}),
    ((Polynomial.finite_setOf_isRoot hPd).image _).insert _, fun t hS => ?_⟩
  have e : s ^ n * (t / s ^ n) = t := mul_div_cancel₀ _ (pow_ne_zero _ hs0)
  have ht0 : t ≠ 0 := fun e => hS (Or.inl e)
  have hp : Pd.eval (t / s ^ n) ≠ 0 := fun e' => hS (Or.inr ⟨_, e', e⟩)
  obtain ⟨hD, y, hy⟩ := hg s (t / s ^ n) z _ hs0 hz.ge (le_order_mon t n) hs.symm (by rw [coeff_mon, e]) hp
  obtain ⟨χ, h1, h2⟩ := ht.rel hc (const_of_le hm hz.ge) (const_of_le hn (le_order_mon t n)) (ne_zero_of_coeff hz0)
    (ne_zero_of_coeff (n := n) (by rwa [coeff_mon])) hD y (fun i => (hy i).1)
  have : χ = ε := hc.hom_ext fun i => by
    have := (hy i).2
    rw [(hP i).2 (hq i), Polynomial.eval_zero, mul_eq_zero] at this
    rw [h1, hc.2.2.2, this.resolve_right hp]
  rwa [this, hc.2.1] at h2

theorem TwoVar.shear (hc : IsChart G j ε f) (ht : TwoVar j f a h d) (hd : (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) ≠ 0) {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hq : ∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))) :
    ∃ (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), Pd ≠ 0 ∧
      (∀ i, P i = 0 ↔ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))) ∧
      ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (n : ℕ∞) ≤ (w - z).order →
        PowerSeries.coeff m z = s ^ m → PowerSeries.coeff n (w - z) = s ^ n * t → Pd.eval t ≠ 0 → w ≠ 0 →
        (∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) ∧ Rel a z w (algOverHom (ψ t) ≫ j) := by
  classical
  obtain ⟨Pd, P, hPd, hP, hg⟩ := GlobalTheory.T.exists_leading_quotient_weighted_arcs k m n hm hn r _ _ hd hq
  refine ⟨Pd, P, fun t => if e : ∃ χ : A →ₐ[k] k, ∀ i, χ (f i) * Pd.eval t = (P i).eval t then e.choose else ε,
    hPd, hP, fun s t z w hs hz hw cz cw hp hw0 => ?_⟩
  obtain ⟨hD, y, hy⟩ := hg s t z (w - z) hs hz hw cz cw hp
  have z0 := const_of_le hm hz
  have w0 := const_of_le hn hw
  have key : ∀ x : MvPowerSeries (Fin 2) k, MvPowerSeries.subst (![z, w - z] : Fin 2 → PowerSeries k) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) x) =
      MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) x := fun x => by
    rw [((GlobalTheory.T.subst_two_variables_identities_alt k).1 x).2 z (w - z) z0 w0, add_sub_cancel]
  simp only [key] at hD hy
  obtain ⟨χ, h1, h2⟩ := ht.rel hc z0 (by rwa [map_sub, z0, sub_zero] at w0)
    (ne_zero_of_coeff (n := m) (by rw [cz]; exact pow_ne_zero _ hs)) hw0 hD y (fun i => (hy i).1)
  have e : ∃ χ : A →ₐ[k] k, ∀ i, χ (f i) * Pd.eval t = (P i).eval t := ⟨χ, fun i => by rw [h1, (hy i).2]⟩
  simp only [dif_pos e]
  have : e.choose = χ := hc.hom_ext fun i =>
    mul_right_cancel₀ hp (by rw [e.choose_spec i, h1, (hy i).2])
  exact ⟨e.choose_spec, by rwa [this]⟩

omit [IsAlgClosed k] in

theorem add_step {m n : ℕ} (hmn : m < n) {Pd : Polynomial k} {P : Fin r → Polynomial k} {ψ : k → (A →ₐ[k] k)}
    (hg : ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (n : ℕ∞) ≤ (w - z).order →
        PowerSeries.coeff m z = s ^ m → PowerSeries.coeff n (w - z) = s ^ n * t → Pd.eval t ≠ 0 → w ≠ 0 →
        (∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) ∧ Rel a z w (algOverHom (ψ t) ≫ j)) (u t : k) (ht : Pd.eval t ≠ 0) :
    (∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) ∧
      Rel a (PowerSeries.C 1 * PowerSeries.X ^ m + PowerSeries.C u * PowerSeries.X ^ n)
        (PowerSeries.C 1 * PowerSeries.X ^ m + PowerSeries.C (t + u) * PowerSeries.X ^ n) (algOverHom (ψ t) ≫ j) := by
  have c : ∀ v : k, PowerSeries.coeff m
      (PowerSeries.C (1 : k) * PowerSeries.X ^ m + PowerSeries.C v * PowerSeries.X ^ n : PowerSeries k) = 1 := by
    intro v
    simp [PowerSeries.coeff_X_pow, hmn.ne]
  have e : (PowerSeries.C 1 * PowerSeries.X ^ m + PowerSeries.C (t + u) * PowerSeries.X ^ n : PowerSeries k) -
      (PowerSeries.C 1 * PowerSeries.X ^ m + PowerSeries.C u * PowerSeries.X ^ n) =
      PowerSeries.C t * PowerSeries.X ^ n := by
    rw [map_add]; ring
  refine hg 1 t _ _ one_ne_zero ?_ ?_ ?_ ?_ ht (ne_zero_of_coeff (n := m) (by rw [c]; exact one_ne_zero))
  · refine le_trans (le_min (le_order_mon 1 m) (le_trans ?_ (le_order_mon u n))) (PowerSeries.min_order_le_order_add _ _)
    exact_mod_cast hmn.le
  · rw [e]; exact le_order_mon t n
  · rw [c, one_pow]
  · rw [e, coeff_mon, one_pow, _root_.one_mul]

theorem mul_step {m : ℕ} (hm : 1 ≤ m) {Pd : Polynomial k} {P : Fin r → Polynomial k} {ψ : k → (A →ₐ[k] k)}
    (hg : ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (m : ℕ∞) ≤ (w - z).order →
        PowerSeries.coeff m z = s ^ m → PowerSeries.coeff m (w - z) = s ^ m * t → Pd.eval t ≠ 0 → w ≠ 0 →
        (∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) ∧ Rel a z w (algOverHom (ψ t) ≫ j)) (z : PowerSeries k) (hz : z.order = m) (t : k) (h0 : t ≠ 0) (ht : Pd.eval (t - 1) ≠ 0) :
    (∀ i, ψ (t - 1) (f i) * Pd.eval (t - 1) = (P i).eval (t - 1)) ∧
      Rel a z (PowerSeries.C (t * PowerSeries.coeff m z) * PowerSeries.X ^ m) (algOverHom (ψ (t - 1)) ≫ j) := by
  have hz0 := coeff_ne_of_order hz
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (PowerSeries.coeff m z) (n := m) hm
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hs
    exact hz0 hs.symm
  refine hg s (t - 1) _ _ hs0 hz.ge (le_order_sub (le_order_mon _ m) hz.ge) hs.symm ?_ ht
    (ne_zero_of_coeff (n := m) (by rw [coeff_mon]; exact mul_ne_zero h0 hz0))
  rw [map_sub, coeff_mon, hs]; ring

omit [IsAlgClosed k] in
theorem comp_sub_one_eq_zero {q : Polynomial k} : q.comp (Polynomial.X - Polynomial.C 1) = 0 ↔ q = 0 :=
  ⟨fun e => by
      have e' : (q.comp (Polynomial.X - Polynomial.C 1)).comp (Polynomial.X + Polynomial.C (1 : k)) = 0 := by
        rw [e, Polynomial.zero_comp]
      rw [Polynomial.comp_assoc] at e'
      simpa using e',
    fun e => by rw [e, Polynomial.zero_comp]⟩

theorem dichotomy_alg (p : ℕ) [CharP k p] (hG : SmConn G)
    (hna : ¬ ∃ b : algOver k (PowerSeries k) ⟶ G, algOverHom (toK k) ≫ b = a) :
    Infinite {x : (algOver k k ⟶ G) // x ^ p = 1} ∨ ∃ f : Gm (Sp k) ⟶ G, IsMonHom f ∧ f ≠ 1 := by
  obtain ⟨A, _, _, j, ε, r, f, hc⟩ := GlobalTheory.T.exists_affineUnitChart_smoothGroupScheme k G hG
  obtain ⟨h, d, hd1, hh1, ht⟩ := GlobalTheory.T.exists_arcQuotient_twoVariable_coords k G A j ε r f hc a
  have hsep := hG.2.2.1
  have hXd := mt ((GlobalTheory.T.subst_two_variables_identities_alt k).1 d).1.1 hd1
  have hXh := fun i => ((GlobalTheory.T.subst_two_variables_identities_alt k).1 (h i)).1.2 (hh1 i)
  have hd' : (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) ≠ 0 := fun e => hXd (e ▸ dvd_zero _)
  have hd : d ≠ 0 := by
    rintro rfl
    apply hd1
    rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
      fun i => by fin_cases i <;> exact PowerSeries.constantCoeff_X), map_zero]
  by_cases hQ : ∀ i, MvPowerSeries.weightedOrder (![1, 1] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) < MvPowerSeries.weightedOrder (![1, 1] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))
  · exfalso
    obtain ⟨Pd, P, ψ, hPd, hP, hg⟩ := ht.shear hc hd' le_rfl le_rfl (fun i => (hQ i).le)
    obtain ⟨ch1, ch2⟩ := GlobalTheory.T.relation_of_gen_of_order_eq k (fun z w => Rel a z w 1)
      (fun m n => ∀ z : PowerSeries k, z.order = (m : ℕ∞) →
        ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → Rel a z (PowerSeries.C t * PowerSeries.X ^ n) 1)
      (fun z w h => by simpa using h.symm) (fun x y z h h' => by simpa using h.trans h') (fun _ _ h => h)
    have g11 := ch1 1 1 (fun z hz => by
      have hz0 := coeff_ne_of_order hz
      refine ⟨insert 0 ((fun t => (t + 1) * PowerSeries.coeff 1 z) '' {t | Pd.IsRoot t}),
        ((Polynomial.finite_setOf_isRoot hPd).image _).insert _, fun t hS => ?_⟩
      have e : t / PowerSeries.coeff 1 z * PowerSeries.coeff 1 z = t := div_mul_cancel₀ _ hz0
      have ht0 : t ≠ 0 := fun e => hS (Or.inl e)
      have hp : Pd.eval (t / PowerSeries.coeff 1 z - 1) ≠ 0 := fun e' =>
        hS (Or.inr ⟨_, e', by simp only [sub_add_cancel, e]⟩)
      obtain ⟨h1, h2⟩ := mul_step le_rfl hg z hz _ (div_ne_zero ht0 hz0) hp
      have : ψ (t / PowerSeries.coeff 1 z - 1) = ε := hc.hom_ext fun i => by
        have := h1 i
        rw [(hP i).2 (hQ i), Polynomial.eval_zero, mul_eq_zero] at this
        rw [hc.2.2.2, this.resolve_right hp]
      rwa [this, hc.2.1, e] at h2)
    obtain ⟨-, s2, s3, s4⟩ := GlobalTheory.T.weightedOrder_slope_comparison_alt k r h d hd _ (fun _ _ => Iff.rfl)
    obtain ⟨m₀, hm₀⟩ := s2 (ht.lt_of_rel hc hd le_rfl le_rfl g11)
    have all := ch2 (m₀ + 1) fun m hm =>
      ht.gen_of_lt hc hd (m := m) (n := m + 1) (by omega) (by omega) (hm₀ m (by omega))
    refine hna (GlobalTheory.T.arc_extends_of_regular_second_axis k G A j ε r f hc a h d hd ht (s4 fun n hn => ?_))
    refine (s3 1 n (m₀ + 1) (by omega)).1 (ht.lt_of_rel hc hd (by omega) (Nat.mul_pos (by omega) hn) ?_)
    intro z w hz hw
    exact all _ _ z w (by omega) (Nat.le_mul_of_pos_right _ hn) hz hw
  · obtain ⟨m, n, hm, hmn, hle, i, hi⟩ := (GlobalTheory.T.weightedOrder_slope_comparison_alt k r (fun i => (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))) _ hd' _
      (fun _ _ => Iff.rfl)).1 hXh hXd ⟨1, 1, le_rfl, le_rfl, hQ⟩
    obtain ⟨Pd, P, ψ, hPd, hP, hg⟩ := ht.shear hc hd' hm (hm.trans hmn) hle
    have hPi : P i ≠ 0 := fun e => ((hP i).1 e).ne hi
    rcases hmn.lt_or_eq with hlt | rfl
    · left
      refine GlobalTheory.T.infinite_pth_roots_of_additive_family k p _ A r f ε (fun χ => algOverHom χ ≫ j) Pd P ψ hc.2.2.1 hc.2.2.2
        (fun _ _ e => eq_of_comp_eq hc.1 e) hc.2.1 hPd ⟨i, hPi⟩ (fun t ht => (add_step hlt hg 0 t ht).1)
        fun t t' h1 h2 h3 => ?_
      have e1 := (add_step hlt hg 0 t' h2).2
      have e2 := (add_step hlt hg (t' + 0) t h1).2
      have e3 := (add_step hlt hg 0 (t + t') h3).2
      rw [_root_.add_assoc] at e3
      exact Red.unique hsep (e1.trans e2) e3
    · right
      have ev : ∀ (q : Polynomial k) (t : k), (q.comp (Polynomial.X - Polynomial.C 1)).eval t = q.eval (t - 1) :=
        fun q t => by simp
      refine GlobalTheory.T.exists_oneParameterSubgroup_of_rational_family k G A j ε r f (Pd.comp (Polynomial.X - Polynomial.C 1))
        (fun i => (P i).comp (Polynomial.X - Polynomial.C 1)) (fun t => ψ (t - 1)) hG hc
        (mt comp_sub_one_eq_zero.1 hPd) ⟨i, mt comp_sub_one_eq_zero.1 hPi⟩ (fun t h0 h1 => ?_)
        fun t t' h0 h0' h1 h2 h3 => ?_
      · simp only [ev] at h1 ⊢
        exact (mul_step hm hg _ (order_mon one_ne_zero m) t h0 h1).1
      · rw [ev] at h1 h2 h3
        have e1 := (mul_step hm hg _ (order_mon one_ne_zero m) t' h0' h2).2
        have e3 := (mul_step hm hg _ (order_mon one_ne_zero m) _ (mul_ne_zero h0 h0') h3).2
        rw [coeff_mon, _root_.mul_one] at e1 e3
        have e2 := (mul_step hm hg _ (order_mon h0' m) t h0 h1).2
        rw [coeff_mon] at e2
        exact Red.unique hsep (e1.trans e2) e3

end Rel

end GlobalTheory.SS.ArcInf

namespace GlobalTheory.SS
open ArcInf

theorem infinite_torsion_or_cocharacter : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ a : Sp (FractionRing (PowerSeries k)) ⟶ G.left, a ≫ G.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) → (¬ ∃ b : Sp (PowerSeries k) ⟶ G.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a) → Infinite {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ p = 1} ∨ ∃ f : Gm (Sp k) ⟶ G, IsMonHom f ∧ f ≠ 1 := by
  intro k _ _ p _ _ G _ hG a ha hna
  let a' : algOver k (FractionRing (PowerSeries k)) ⟶ G := Over.homMk a ha
  refine (dichotomy_alg (a := a') p hG ?_).imp_left fun (hI : Infinite {x : (algOver k k ⟶ G) // x ^ p = 1}) => ?_
  · rintro ⟨b, hb⟩
    exact hna ⟨b.left, congrArg (fun x => x.left) hb⟩
  · let e : 𝟙_ (Over (Sp k)) ≅ algOver k k := Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ spMap (RingHom.id k) = 𝟙 _
      rw [Category.id_comp]
      exact Spec.map_id _)
    refine @Infinite.of_injective _ _ hI (fun x : {x : (algOver k k ⟶ G) // x ^ p = 1} =>
      (⟨e.hom ≫ x.1, by rw [← MonObj.comp_pow, x.2, MonObj.comp_one]⟩ : {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ p = 1})) ?_
    intro x y hxy
    exact Subtype.ext ((cancel_epi e.hom).1 (congrArg Subtype.val hxy))

end GlobalTheory.SS
end
