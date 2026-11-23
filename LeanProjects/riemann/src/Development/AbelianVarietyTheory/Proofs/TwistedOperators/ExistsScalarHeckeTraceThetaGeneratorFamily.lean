import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelSumEqCardTorsionMulTraceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKernelOfGeometricFibresReducedBaseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatioLocalFunctionsGeometricFibreDescendsBaseStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGenerates
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRigidifiedThetaIsoBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedMulPullbackCommutesBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValuePulledBackAlongGroupMapStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslationCommutesCanonicalBaseChangeMapStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalPointThetaGeneratorNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PulledBackLocalFunctionEqMulOfValuesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChartPulledBackFunctionNeZeroOfValueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PullConstantToPointEqRingImageStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeScal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem exists_sums {T : Type} [CommRing T] {x x' : Sp T ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {p n : ℕ}
    {σ : Fin n → (Over.mk x ⟶ Xo.univ.t.G)} {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2))}
    (hβ : β.IsGen) (hσ : ∀ j, σ j ∈ transKer Xo.univ.t.G Ψ)
    (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))) (s₀ : LB.Sec (PPx x')) :
    ∃ t t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (J), Good Xo.univ.t.PP.L z J →
        sv Xo.univ.t.G Xo.univ.t.PP t r z J = (val β r z J).val *
          ∑ j, ((val β (r ≫ (translT Xo.univ.t.G (σ j)).left) z J)⁻¹).val *
            sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G (σ j)).left) z J ∧
        sv Xo.univ.t.G Xo.univ.t.PP t₀ r z J =
          sv Xo.univ.t.G Xo.univ.t.PP s₀ (r ≫ Ψ) z J * (val β r z J).val := by
  obtain ⟨t₀, ht₀⟩ := exists_isCarried (A := Xo.univ.t.G) (L := Xo.univ.t.PP) hβ s₀
  choose U hc hU using fun j => exists_isDescLift (L := Xo.univ.t.PP) hβ (hσ j)
  choose F hF using fun j => exists_isActOf (U j) s₁
  let t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x)) :=
    SecM.toSec Xo.univ.t.G (∑ j, SecM.ofSec Xo.univ.t.G (F j))
  have ht : ∀ i, t.f i = ∑ j, (F j).f i := fun i => by
    show (∑ j, SecM.ofSec Xo.univ.t.G (F j) : SecM _ _ _ _).1 i = _
    rw [Submodule.coe_sum, Finset.sum_apply]; rfl
  refine ⟨t, t₀, fun Z r z J hJ => ⟨?_, ht₀.val r z hJ⟩⟩
  rw [sv_sum ht r z hJ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [act_val (hF j) r z hJ, (hU j).val r z hJ, hc j, Units.val_mul]
  ring

theorem card_tors_mul {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {P : Ideal (𝓞 E)} {p i n : ℕ}
    {C : Subgroup (Over.mk x₁ ⟶ Xo.univ.t.G)} (hp : 0 < p) (hC : Xo.univ.t.HeckeKer (Over.mk x₁) Dw P p i C)
    (e : Fin n ≃ C) : Nat.card {a // a ∈ C ∧ a ^ p = 1} * Ideal.absNorm P ^ i = n := by
  haveI : Finite C := Finite.of_equiv _ e
  obtain ⟨k, r, hr⟩ := exists_isRepsModTors C p
  have h1 := hr.card
  have h2 := card_reps hp hC hr
  rw [Nat.card_congr e.symm, Nat.card_fin] at h1
  rw [h1, h2]

theorem card_tors_pos {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {p : ℕ}
    {C : Subgroup (Over.mk x₁ ⟶ Xo.univ.t.G)} [Finite C] : 0 < Nat.card {a // a ∈ C ∧ a ^ p = 1} := by
  haveI : Finite {a // a ∈ C ∧ a ^ p = 1} :=
    Finite.of_injective (fun a => (⟨a.1, a.2.1⟩ : C)) (by intro a b h; apply Subtype.ext; simpa using congrArg Subtype.val h)
  exact Nat.card_pos_iff.2 ⟨⟨⟨1, C.one_mem, one_pow p⟩⟩, inferInstance⟩

end GlobalTheory.HeckeScal

namespace GlobalTheory.HeckeScal

theorem rigIso_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} {pm : Gx x₁ ⟶ Gx x} {pm' : Gx x₁' ⟶ Gx x'} {k : ℤ} {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ k)}, IsCan χ pm → IsCan χ pm' → Ψ₁ ≫ pm' = pm ≫ Ψ → Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ k β → ∃ β₁ : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ₁ k), IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ₁ k β₁ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → val β₁ r z J = val β (r ≫ pm) z J := GlobalTheory.T.exists_rigidified_theta_iso_base_change

theorem mulPull_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} {p : ℕ} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)} {s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))}, IsCan χ pm → (∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J) → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∃ s₁' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x₁)), IsMulPull Xo.univ.t.G Xo.univ.t.PP p s' s₁' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s₁' r z J = sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ pm) z J := GlobalTheory.T.normalized_mul_pullback_commutes_base_change

theorem sv_of_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x₁ : Sp T ⟶ Xo.X} (pm : Gx x₁ ⟶ Gx x) {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)}, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₁) Xo.univ.t.G).left → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (hi : (PPx x₁).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ hi).hom (s.f i) = s'.f i) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J := GlobalTheory.T.section_value_pulled_back_along_group_map

theorem translT_comp_can : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} (c : Over.mk x ⟶ Xo.univ.t.G) (c₁ : Over.mk x₁ ⟶ Xo.univ.t.G), IsCan χ pm → c₁.left = spMap χ ≫ c.left → (translT Xo.univ.t.G c₁).left ≫ pm = pm ≫ (translT Xo.univ.t.G c).left := GlobalTheory.T.translation_commutes_canonical_baseChange_map

theorem exists_ratPt_sv_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {s : LB.Sec (PPx x₁)}, IsThGen x₁ s → ∃ w : Sp Ω ⟶ Gx x₁, w ≫ (fst (Over.mk x₁) Xo.univ.t.G).left = 𝟙 _ ∧ ∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s w z J ≠ 0 := GlobalTheory.T.exists_rationalPoint_thetaGenerator_ne_zero

theorem appLE_eq_of_sv : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (α : Ω), (∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t w z J = gs (𝟙 (Sp Ω)) z ⊤ (toΓ Ω α) * sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J) → ∀ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t.f i) = toΓ Ω α * (w.appLE _ ⊤ hi).hom (t₀.f i) := GlobalTheory.T.pulledBack_local_function_eq_mul_of_values

theorem appLE_ne_zero_of_sv : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [Field Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J ≠ 0 → ∃ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t₀.f i) ≠ 0 := GlobalTheory.T.exists_chart_pulledBack_function_ne_zero_of_value

theorem appLE_toΓ : ∀ {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {Y : Scheme.{0}} (q : Y ⟶ Sp T) (U : Y.Opens) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U), w ≫ q = spMap χ → ∀ a : T, (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) = toΓ Ω (χ a) := GlobalTheory.T.pull_constant_to_point_eq_ring_image

end GlobalTheory.HeckeScal

namespace GlobalTheory.HeckeScal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem absNorm_pow_pos {P : Ideal (𝓞 E)} {p i : ℕ} (h : admitted l P p) : 0 < Ideal.absNorm P ^ i := by
  refine pow_pos (Nat.pos_of_ne_zero fun h0 => ?_) _
  rw [Ideal.absNorm_eq_zero_iff] at h0
  have hp := h.2.2.2.1
  rw [h0, Ideal.mem_bot, Nat.cast_eq_zero] at hp
  exact h.2.2.1.ne_zero hp

theorem fibre {c : Coeff l} {P : Ideal (𝓞 E)} {p i n : ℕ} {T : Type} [CommRing T] [Algebra c.F T]
    {y : FrPt Xo c T} {x' : Sp T ⟶ Xo.X} {Ψ : Gx y.x ⟶ Gx x'} {σ : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)}
    {s₀ : LB.Sec (PPx x')} (hadm : admitted l P p) (hfam : IsHeckeFam P p i Ψ) (hlist : IsListed Ψ σ)
    (hgen : SecGen x' s₀) {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2))}
    (hβ : IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ _ β)
    {s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk y.x))}
    (hs₁ : IsMulPull Xo.univ.t.G Xo.univ.t.PP p y.s s₁)
    {t t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk y.x))}
    (ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx y.x) (z : Z) (J), Good Xo.univ.t.PP.L z J →
        sv Xo.univ.t.G Xo.univ.t.PP t r z J = (val β r z J).val *
          ∑ j, ((val β (r ≫ (translT Xo.univ.t.G (σ j)).left) z J)⁻¹).val *
            sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G (σ j)).left) z J ∧
        sv Xo.univ.t.G Xo.univ.t.PP t₀ r z J =
          sv Xo.univ.t.G Xo.univ.t.PP s₀ (r ≫ Ψ) z J * (val β r z J).val)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω)
    (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁') (s' : LB.Sec (PPx x₁')) (hFr : FrMap χ y y₁)
    (hΨ₁ : IsFib χ.toRingHom Ψ Ψ₁) (hth : IsThGen x₁' s')
    (htr : IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s') :
    n / Ideal.absNorm P ^ i ≠ 0 ∧ ∃ (α' : Ω) (s₀₁ : LB.Sec (PPx x₁')), SecBC χ.toRingHom 1 x' x₁' s₀ s₀₁ ∧
      (∀ j, s'.f j = scal x₁' α' j * s₀₁.f j) ∧
      (∀ w : Sp Ω ⟶ Gx y.x, w ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = spMap χ.toRingHom →
        ∀ j (hj : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk y.x)).U j),
          (w.appLE _ ⊤ hj).hom (t.f j) =
            toΓ Ω (((n / Ideal.absNorm P ^ i : ℕ) : Ω) * α') * (w.appLE _ ⊤ hj).hom (t₀.f j)) ∧
      ∃ (j : (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk y.x)).ι) (w : Sp Ω ⟶ Gx y.x) (hj : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk y.x)).U j),
        w ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = spMap χ.toRingHom ∧ (w.appLE _ ⊤ hj).hom (t₀.f j) ≠ 0 := by
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hp : 0 < p := hadm.2.2.1.pos
  obtain ⟨-, -, pm, pms, pmf, pmv⟩ := hFr
  obtain ⟨pm₁, pm', hpm, hpm', hc, hf⟩ := id hΨ₁
  obtain rfl : pm = pm₁ := GlobalTheory.HeckeFrCompare.gx_ext (by rw [pmf, hpm.2.2]) (by rw [pms, hpm.2.1])
  have hsy := sv_of_pull pm pms pmv
  obtain ⟨hker, hisog⟩ := hfam.2.2.2.2 Ω χ.toRingHom y₁.x x₁' Ψ₁ hΨ₁
  obtain ⟨e, he⟩ := hlist Ω χ.toRingHom y₁.x x₁' Ψ₁ hΨ₁
  obtain ⟨β₁, hβ₁, hvβ⟩ := rigIso_baseChange χ.toRingHom hpm hpm' hc hf hβ
  obtain ⟨s₁₁, hs₁₁, hvs⟩ := mulPull_baseChange χ.toRingHom hpm hsy hs₁
  have heps := GlobalTheory.T.heckeKernel_sum_eq_card_torsion_mul_trace E H Dw l Xo Ω y₁.x x₁' Ψ₁ p n y₁.s s' β₁ s₁₁ e hisog hth htr hβ₁ hs₁₁
  haveI : Finite (transKer Xo.univ.t.G Ψ₁) := Finite.of_equiv _ e
  have hm := card_tors_mul hp hker e
  have hmpos := card_tors_pos (C := transKer Xo.univ.t.G Ψ₁) (p := p)
  have hmeq : Nat.card {a // a ∈ transKer Xo.univ.t.G Ψ₁ ∧ a ^ p = 1} = n / Ideal.absNorm P ^ i := by
    rw [← hm, Nat.mul_div_cancel _ (absNorm_pow_pos hadm)]

  obtain ⟨s₀₁, hs₀₁, -⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo T Ω χ.toRingHom 1 x' x₁' hpm'.1 s₀
  have hg₀₁ : SecGen x₁' s₀₁ := GlobalTheory.Frames.secGen_of_secNZ hB E H Dw l Xo Ω x₁' s₀₁
    (NonzeroGenerates.secNZ_pull hpm'.1 hs₀₁ (GlobalTheory.Frames.secNZ_of_secGen hB E H Dw l Xo T x' s₀ hgen))
  have hv₀ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁') (z : Z) (J), Good Xo.univ.t.PP.L z J →
      sv Xo.univ.t.G Xo.univ.t.PP s₀₁ r z J = sv Xo.univ.t.G Xo.univ.t.PP s₀ (r ≫ pm') z J := by
    obtain ⟨pmB, sB, fB, vB⟩ := hs₀₁
    obtain rfl : pmB = pm' := GlobalTheory.HeckeFrCompare.gx_ext (by rw [fB, hpm'.2.2]) (by rw [sB, hpm'.2.1])
    exact sv_of_pull pmB sB fun j hj => by
      have := vB j hj
      erw [NonzeroGenerates.scal_one, _root_.one_mul] at this
      exact this
  obtain ⟨α', hα', -⟩ := hg₀₁ s'

  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx y₁.x) (z : Z) (J), Good Xo.univ.t.PP.L z J →
      sv Xo.univ.t.G Xo.univ.t.PP t (r ≫ pm) z J = ((n / Ideal.absNorm P ^ i : ℕ) : Z.presheaf.stalk z) *
        gs (r ≫ (fst (Over.mk y₁.x) Xo.univ.t.G).left) z ⊤ (toΓ Ω α') *
          sv Xo.univ.t.G Xo.univ.t.PP t₀ (r ≫ pm) z J := by
    intro Z r z J hJ
    obtain ⟨h1, h2⟩ := ht Z (r ≫ pm) z J hJ
    have hsum : ∑ j, ((val β ((r ≫ pm) ≫ (translT Xo.univ.t.G (σ j)).left) z J)⁻¹).val *
        sv Xo.univ.t.G Xo.univ.t.PP s₁ ((r ≫ pm) ≫ (translT Xo.univ.t.G (σ j)).left) z J =
        (Nat.card {a // a ∈ transKer Xo.univ.t.G Ψ₁ ∧ a ^ p = 1} : Z.presheaf.stalk z) *
          sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ₁) z J := by
      rw [heps Z r z J hJ]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e₁ : (r ≫ pm) ≫ (translT Xo.univ.t.G (σ j)).left = (r ≫ (translT Xo.univ.t.G (e j).1).left) ≫ pm := by
        rw [Category.assoc, Category.assoc, translT_comp_can χ.toRingHom (σ j) (e j).1 hpm (he j)]
      rw [e₁, ← hvβ _ _ z J hJ, ← hvs _ _ z J hJ]
    have hs' := sv_smul (A := Xo.univ.t.G) (L := Xo.univ.t.PP) (T := Over.mk x₁') (a := toΓ Ω α') hα' (r ≫ Ψ₁) z hJ
    have h0 : sv Xo.univ.t.G Xo.univ.t.PP s₀ ((r ≫ pm) ≫ Ψ) z J = sv Xo.univ.t.G Xo.univ.t.PP s₀₁ (r ≫ Ψ₁) z J := by
      rw [hv₀ _ _ z J hJ, Category.assoc, Category.assoc, hc]
    rw [h1, h2, hsum, hs', h0, hmeq, Category.assoc, hf]
    ring
  refine ⟨(Nat.pos_of_ne_zero (by rw [← hmeq]; exact hmpos.ne')).ne', α', s₀₁, hs₀₁, hα', ?_, ?_⟩
  · intro w hw j hj
    let b : Over.mk y₁.x ⟶ Xo.univ.t.G := Over.homMk (w ≫ (snd (Over.mk y.x) Xo.univ.t.G).left) (by
      show (w ≫ (snd (Over.mk y.x) Xo.univ.t.G).left) ≫ Xo.univ.t.G.hom = y₁.x
      rw [Category.assoc, GlobalTheory.HeckeFrCompare.snd_hom, reassoc_of% hw, hpm.1])
    have hw₁f : (lift (𝟙 (Over.mk y₁.x)) b).left ≫ (fst (Over.mk y₁.x) Xo.univ.t.G).left = 𝟙 _ :=
      GlobalTheory.HeckeFrCompare.lift_l_fst _ _
    have hw₁ : (lift (𝟙 (Over.mk y₁.x)) b).left ≫ pm = w := GlobalTheory.HeckeFrCompare.gx_ext
      (by rw [Category.assoc, hpm.2.2, reassoc_of% hw₁f]; exact hw.symm)
      (by rw [Category.assoc, hpm.2.1, GlobalTheory.HeckeFrCompare.lift_l_snd]; rfl)
    refine appLE_eq_of_sv w t t₀ _ (fun z J hJ => ?_) j hj
    rw [← hw₁, hv _ _ z J hJ, hw₁f, map_mul, gs_mul (𝟙 (Sp Ω)) z ⊤ trivial, map_natCast]
    congr 2
    rw [gs_eq (𝟙 (Sp Ω)) z ⊤ trivial, map_natCast, map_natCast]
  · obtain ⟨w', hw'f, hw'nz⟩ := exists_ratPt_sv_ne_zero (hg₀₁ : IsThGen x₁' s₀₁)
    let b' : Over.mk x₁' ⟶ Xo.univ.t.G := Over.homMk (w' ≫ (snd (Over.mk x₁') Xo.univ.t.G).left) (by
      show (w' ≫ (snd (Over.mk x₁') Xo.univ.t.G).left) ≫ Xo.univ.t.G.hom = x₁'
      rw [Category.assoc, GlobalTheory.HeckeFrCompare.snd_hom, reassoc_of% hw'f])
    obtain ⟨a, ha⟩ := hisog.2.2.1 b'
    have hb' : (lift (𝟙 (Over.mk x₁')) b').left = w' := GlobalTheory.HeckeFrCompare.gx_ext
      (by rw [GlobalTheory.HeckeFrCompare.lift_l_fst, hw'f]; rfl) (by rw [GlobalTheory.HeckeFrCompare.lift_l_snd]; rfl)
    have hr₁ : (lift (𝟙 (Over.mk y₁.x)) a).left ≫ Ψ₁ = w' := ha.trans hb'
    obtain ⟨z⟩ : Nonempty (Sp Ω) := ⟨show PrimeSpectrum Ω from ⟨⊥, Ideal.isPrime_bot⟩⟩
    choose I hI using fun ψ : Sp Ω ⟶ Xo.univ.t.G.left => exists_chart Xo.univ.t.PP.isLB (ψ z)
    have hJ : Good Xo.univ.t.PP.L z I := hI
    have hwq : ((lift (𝟙 (Over.mk y₁.x)) a).left ≫ pm) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left =
        spMap χ.toRingHom := by
      rw [Category.assoc, hpm.2.2, GlobalTheory.HeckeFrCompare.lift_l_fst_assoc]; exact Category.id_comp _
    have hne : sv Xo.univ.t.G Xo.univ.t.PP t₀ ((lift (𝟙 (Over.mk y₁.x)) a).left ≫ pm) z I ≠ 0 := by
      rw [(ht _ _ z I hJ).2, Category.assoc, ← hc, ← Category.assoc, ← hv₀ _ _ z I hJ, hr₁]
      intro h0
      exact hw'nz z I hJ (by simpa using congrArg (· * ((val β ((lift (𝟙 (Over.mk y₁.x)) a).left ≫ pm) z I)⁻¹).val) h0)
    obtain ⟨j, hj, hne'⟩ := appLE_ne_zero_of_sv _ t₀ z I hJ hne
    exact ⟨j, _, hj, hwq, hne'⟩

end GlobalTheory.HeckeScal

open GlobalTheory.HeckeScal in

theorem GlobalTheory.HeckeScal.exists_scal_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i n : ℕ) (T : Type) [CommRing T] [IsReduced T] [Algebra c.F T] (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (σ : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (s₀ : LB.Sec (PPx x')), admitted l P p → IsHeckeFam P p i Ψ → IsListed Ψ σ → SecGen x' s₀ → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁'), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → ∃ s', IsThGen x₁' s' ∧ IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s') → ∃ a : T, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁') (s' : LB.Sec (PPx x₁')), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → IsThGen x₁' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s' → SecBC χ.toRingHom a x' x₁' s₀ s' := by
  intro E _ _ _ H Dw l Xo c P p i n T _ _ _ y x' Ψ σ s₀ hadm hfam hlist hgen hex
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  obtain ⟨hlin, -, -, ⟨β, hβ⟩, -⟩ := id hfam
  have hσ : ∀ j, σ j ∈ transKer Xo.univ.t.G Ψ := fun j =>
    GlobalTheory.T.mem_kernel_of_geometric_fibres_reduced_base E H Dw l Xo T y.x x' Ψ (σ j) hlin.1 fun Ω _ _ χ x₁ x₁' Ψ₁ hF => by
      obtain ⟨e, he⟩ := hlist Ω χ x₁ x₁' Ψ₁ hF
      exact ⟨(e j).1, (e j).2, he j⟩
  obtain ⟨s₁, hs₁⟩ := exists_isMulPull p y.s
  obtain ⟨t, t₀, ht⟩ := exists_sums hβ.2.1 hσ s₁ s₀
  have hsm : Smooth (fst (Over.mk y.x) Xo.univ.t.G).left := by
    have := Xo.univ.t.semi.smooth
    show Smooth (pullback.fst y.x Xo.univ.t.G.hom)
    infer_instance
  obtain ⟨a', ha'⟩ := GlobalTheory.T.ratio_localFunctions_geometricFibre_descends_base T (Gx y.x) (fst (Over.mk y.x) Xo.univ.t.G).left _
    (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk y.x)).U t.f t₀.f hsm fun Ω _ _ χ => by
      letI : Algebra c.F Ω := (χ.comp (algebraMap c.F T)).toAlgebra
      let χ' : T →ₐ[c.F] Ω := { χ with commutes' := fun _ => rfl }
      obtain ⟨y₁, hy₁⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c T Ω χ' y
      obtain ⟨Ψ₁, hΨ₁⟩ := exists_isFib (Xo := Xo) χ hy₁.1 rfl Ψ hlin.1
      obtain ⟨s', hs'g, hs'⟩ := hex Ω χ' y₁ (spMap χ ≫ x') Ψ₁ hy₁ hΨ₁
      obtain ⟨-, α', -, -, -, hval, j, w, hj, hw, hne⟩ :=
        fibre hadm hfam hlist hgen hβ hs₁ ht χ' y₁ _ Ψ₁ s' hy₁ hΨ₁ hs'g hs'
      exact ⟨_, fun j w h hw => hval w hw j h, j, w, hj, hw, hne⟩
  refine ⟨algebraMap c.F T ((n / Ideal.absNorm P ^ i : ℕ) : c.F)⁻¹ * a', ?_⟩
  intro Ω _ _ _ χ y₁ x₁' Ψ₁ s' hFr hΨ₁ hth htr
  obtain ⟨hm0, α', s₀₁, hbc, hα', hval, j, w, hj, hw, hne⟩ :=
    fibre hadm hfam hlist hgen hβ hs₁ ht χ y₁ x₁' Ψ₁ s' hFr hΨ₁ hth htr
  obtain ⟨pm, pm', hpm, hpm', -, -⟩ := hΨ₁
  have hφ : ∀ u : Ω, (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (toΓ Ω u) = u := fun u => by
    show ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom u = u
    rw [Iso.inv_hom_id]; rfl
  have hχa : χ a' = ((n / Ideal.absNorm P ^ i : ℕ) : Ω) * α' := by
    have e1 := congrArg (fun f => (w.appLE _ ⊤ hj).hom f) (ha' j)
    simp only [map_mul] at e1
    rw [appLE_toΓ χ.toRingHom _ _ w hj hw a', hval w hw j hj] at e1
    have e2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom e1
    simp only [map_mul, hφ] at e2
    have hne' : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((w.appLE _ ⊤ hj).hom (t₀.f j)) ≠ 0 := by
      intro h0
      apply hne
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom h0
      rw [map_zero] at this
      rw [← this]
      show _ = ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv).hom _
      rw [Iso.hom_inv_id]; rfl
    exact (mul_right_cancel₀ hne' e2).symm
  have hχ : χ (algebraMap c.F T ((n / Ideal.absNorm P ^ i : ℕ) : c.F)⁻¹ * a') = α' := by
    rw [map_mul, χ.commutes, hχa, ← _root_.mul_assoc, ← map_natCast (algebraMap c.F Ω), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hm0), map_one, _root_.one_mul]
  exact (NonzeroGenerates.pull_mul_iff hpm'.1 hbc).2 fun j => by
    rw [hα' j]
    congr 2
    exact hχ.symm
