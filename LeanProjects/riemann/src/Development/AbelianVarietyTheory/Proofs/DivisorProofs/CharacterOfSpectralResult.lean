import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionPullback

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
open scoped TensorProduct NNReal

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HalfGeo

open GlobalTheory.HTMap GlobalTheory.HtChar

theorem tors_sect_of_local {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} [IsLocallyNoetherian X] {t : SAB H X} {K : Type} [Field K] [CharZero K] {q : ℕ} (hq : q ≠ 0)
    {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K]
    (x : Sp R ⟶ X) (hs : SplitK t (spMap (algebraMap R K) ≫ x) q) {p : ℕ} [Fact p.Prime]
    (ψ : R →+* ↥(intO ℂ_[p])) [IsLocalHom ψ]
    (w : Over.mk (spMap (algebraMap ↥(intO ℂ_[p]) ↥(intO ℂ_[p])) ≫ spMap ψ ≫ x) ⟶ t.G) (hw : w ^ q = 1) :
    ∃ σ : Over.mk x ⟶ t.G, σ ^ q = 1 ∧ w.left = spMap ψ ≫ σ.left := by
  haveI : CharZero R := ⟨fun m n h => Nat.cast_injective (R := K) (by simpa using congrArg (algebraMap R K) h)⟩
  have hF := ex_full hq (splitTors_of_splitK x q hs)
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  obtain ⟨P, hP⟩ := hF ((IsLocalRing.maximalIdeal _).comap ψ) inferInstance
  have hA : IsUnit P.f := by
    by_contra hn; exact hP.1 (by rw [IsLocalRing.maximalIdeal_comap ψ]; exact hn)
  obtain ⟨β, hβ⟩ := hP.at_fin _ w hw
  obtain ⟨β₀, hβ₀, rfl⟩ := sect_of hA _ hβ
  have hσA : P.At (RingHom.id R) (spMap β₀ ≫ P.u.left) β₀ := ⟨hβ₀, rfl⟩
  let σ : Over.mk x ⟶ t.G := mkPt (spMap β₀ ≫ P.u.left) (hσA.over.trans (by rw [spMap_id', Category.id_comp]))
  have hσ : σ ^ q = 1 := FP.At.tors (w := σ) hσA
  refine ⟨σ, hσ, ?_⟩
  rw [← hβ.2, Algebra.algebraMap_self, RingHom.id_comp, ← spc_assoc]; rfl

theorem charSt_of_specSt : SpecSt → CharSt := by
  intro hSpec
  intro E _ _ _ H Dw l Xo c O _ β Z _ K _ _ ξ₀ ξ hξ q hq hζK hs R _ _ _ _ _ _ x hx R' _ r u x₀ hu hur hx₀ hux₀
    p _ ψ ψ' z yy _ hψ' hz hyy s s' s'' hs't hss' hs'' χ ch hW hI
  subst hx hux₀ hz hyy
  intro w a hw ha
  obtain ⟨σ, hσ, hwσ⟩ := tors_sect_of_local hq x hs ψ w hw

  let k : TorsK Z.t (spMap (algebraMap R K) ≫ x) q :=
    ⟨pull (spMap (algebraMap R K)) rfl σ, MonoidHom.mem_ker.2 (by
      rw [powMonoidHom_apply, ← map_pow, hσ, map_one])⟩
  have hk : k.1.left = spMap (algebraMap R K) ≫ σ.left := rfl
  have hkq : ((χ k : Kˣ) : K) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ker_pow, map_one, Units.val_one]
  obtain ⟨a₀, ha₀⟩ := root_mem (R := R) hq hkq
  have ha₀q : a₀ ^ q = 1 := IsFractionRing.injective R K (by rw [map_pow, ha₀, hkq, map_one])
  have hval : (ch.χ _ w : ↥(intO ℂ_[p])) = ψ a₀ := hI σ k a₀ w hσ hk hwσ ha₀
  let r₀ : Rˣ := (IsUnit.of_pow_eq_one ha₀q hq).unit
  have hr₀ : (r₀ : R) = a₀ := rfl

  have hw₁ : (spMap r ≫ σ.left) ≫ Z.t.G.hom = x₀ ≫ Z.j := by
    rw [Category.assoc, over_w σ, hx₀]
  let w₁ : Over.mk ((Over.mk x₀).hom ≫ Z.j) ⟶ Z.t.G := mkPt (spMap r ≫ σ.left) hw₁
  have hw₁q : w₁ ^ q = 1 := tors_of (g := spMap r) (w := σ) rfl hσ
  obtain ⟨σ', hσ'φ, hσ't⟩ := GlobalTheory.grpPullback_lift_torsion _ _ Z.oF.t.G Z.t.G _ Z.m.cm.F Z.m.cart (Over.mk x₀) w₁
  have hσ'q : σ' ^ q = 1 := hσ't q hw₁q
  have hσ'φ' : σ'.left ≫ Z.m.φ = spMap r ≫ σ.left := hσ'φ

  let aK : Over.mk (spMap u ≫ x₀) ⟶ Z.oF.t.G := pull (spMap u) rfl σ'
  have haK : aK.left ≫ Z.m.φ = k.1.left := by
    show (spMap u ≫ σ'.left) ≫ Z.m.φ = _
    rw [Category.assoc, hσ'φ', spc_assoc, hur, hk]
  have hWK := hW k aK haK
  let r₁ : R'ˣ := Units.map r.toMonoidHom r₀
  have hr₁K : Units.map u.toMonoidHom r₁ = χ k := by
    ext
    show u (r a₀) = _
    rw [← RingHom.comp_apply, hur, ha₀]
  rw [← hr₁K] at hWK

  have haσ' : a.left = spMap ψ' ≫ σ'.left := by
    refine Z.m.cart.1.hom_ext ?_ ?_
    · change a.left ≫ Z.m.φ = (spMap ψ' ≫ σ'.left) ≫ Z.m.φ
      rw [ha, Category.assoc, hσ'φ', hwσ, spc_assoc, spc_assoc, hψ']
    · rw [Over.w a, Category.assoc, Over.w σ']
      rfl
  have hC := hSpec E H Dw l Xo c O β Z R' K ℂ_[p] u ψ' hu x₀ (spMap u ≫ x₀) (spMap ψ' ≫ x₀) q hq σ' s' aK s a s''
    hσ'q hs't rfl hss' haσ' hs'' r₁ hWK
  have hfin : Units.map ψ'.toMonoidHom r₁ = Units.map (intO ℂ_[p]).subtype.toMonoidHom (ch.χ _ w) := by
    ext
    show ψ' (r a₀) = ((ch.χ _ w : ↥(intO ℂ_[p])) : ℂ_[p])
    rw [hval, ← RingHom.comp_apply, hψ']
    rfl
  rw [← hfin]
  exact hC

end GlobalTheory.HalfGeo
