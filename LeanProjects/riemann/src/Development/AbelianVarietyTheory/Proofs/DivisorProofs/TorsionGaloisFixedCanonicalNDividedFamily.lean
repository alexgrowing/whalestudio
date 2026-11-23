import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GaloisHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivalentIdempotentImageFixedTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageNDividedPointGaloisConjEquivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CanonTors

theorem galois_fixed : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hD hQ G _ _ P hC σ x hx
  obtain ⟨-, D', F, A', G', _, _, U', oA, oG, inc, pr, hG', hlin, hinc, hpr, hip, hpi, -⟩ := hC
  haveI : CharZero R := hCN.2.2.2
  have hadm : AdmBase R (maximalIdeal R) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  obtain ⟨y, hy0⟩ : ∃ y : (Over.map (jK R)).obj (TFK (R := R) (AlgebraicClosure (FractionRing R))) ⟶ G', y = x ≫ inc := ⟨_, rfl⟩
  obtain ⟨h, hh0⟩ : ∃ h : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ (Over.pullback (jK R)).obj G',
    h = (Over.mapPullbackAdj (jK R)).unit.app _ ≫ (Over.pullback (jK R)).map y := ⟨_, rfl⟩
  have hy : y ^ n = 1 := by
    rw [hy0, ← MonObj.pow_comp, hx, MonObj.one_comp]
  have hmp : ∀ m : ℕ, (Over.pullback (jK R)).map (y ^ m) = ((Over.pullback (jK R)).map y) ^ m := by
    intro m
    induction m with
    | zero => simp [Functor.map_one]
    | succ m ih => rw [pow_succ, Functor.map_mul, ih, pow_succ]
  have hh : h ^ n = 1 := by
    rw [hh0, ← MonObj.comp_pow, ← hmp, hy, Functor.map_one, MonObj.comp_one]
  haveI := U'.gen_hom
  obtain ⟨a, ha0⟩ : ∃ a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A, a = h ≫ U'.gen.hom := ⟨_, rfl⟩
  have ha : a ^ n = 1 := by
    rw [ha0, ← MonObj.pow_comp, hh, MonObj.one_comp]
  have hye : y ≫ oG.act F.e = y := by
    rw [hy0, ← hpi, Category.assoc, ← Category.assoc inc, hip, Category.id_comp]
  have hae : a ≫ oA.act F.e = a := by
    rw [ha0, Category.assoc, ← hlin.ext, hh0]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hye]
  obtain ⟨f, hT, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hadm D' A' G' hG' U'
    (AlgebraicClosure (FractionRing R)) n hn
  obtain ⟨p, hp⟩ := hT.2.1 a ha
  obtain ⟨p₁, hy₁, hg₁, he₁⟩ := GlobalTheory.T.exists_equivalent_idempotent_image_fixed_torsion R hCN n hn hnu Q D' F A' G' U' oA oG hG' hlin a ha hae p ((hT.1 p a).2 hp.symm)
  have hf₁ : f p₁ = a := ((hT.2.2.1 p₁ p).2 he₁).trans hp
  obtain ⟨⟨p₁', hext⟩, hpt, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hadm D' A' G' hG' U'
    (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing R)) σ.toAlgHom n hn p₁
  obtain ⟨a', ha'⟩ := hpt a
  have h2 := (hiff p₁' a a' hext ha').1 ((hT.1 p₁ a).2 hf₁.symm)
  have heq := GlobalTheory.T.idempotent_image_nDividedPoint_galoisConj_equiv T R iw s ε n hCN hn hnu ζ hζ Q e hD hQ D' F A' G' U' oA oG hG' hlin σ p p₁ p₁' hy₁ hg₁ hext
  have haa : a' = a := ((hT.1 p₁' a').1 h2).trans (((hT.2.2.1 p₁ p₁').2 heq).symm.trans hf₁)
  rw [haa] at ha'
  have e1 : (Over.mapPullbackAdj (jK R)).homEquiv _ _ y = h := by rw [Adjunction.homEquiv_unit, hh0]
  have hyl : y.left = h.left ≫ ((Over.mapPullbackAdj (jK R)).counit.app G').left := by
    have e2 : y = (Over.map (jK R)).map h ≫ (Over.mapPullbackAdj (jK R)).counit.app G' := by
      conv_lhs => rw [← ((Over.mapPullbackAdj (jK R)).homEquiv _ _).symm_apply_apply y, e1]
      exact Adjunction.homEquiv_counit _ _ _ _
    rw [e2, Over.comp_left]
    rfl
  have hhl : spMap σ.toAlgHom.toRingHom ≫ h.left = h.left := by
    have := congrArg (· ≫ U'.gen.inv.left) ha'
    simp only [ha0, Over.comp_left, Category.assoc] at this
    rw [← Over.comp_left _ _ _ U'.gen.hom U'.gen.inv, Iso.hom_inv_id, Over.id_left, Category.comp_id] at this
    exact this.symm
  have hyx : spMap σ.toAlgHom.toRingHom ≫ y.left = y.left := by
    rw [hyl, ← Category.assoc, hhl]
  have := congrArg (· ≫ pr.left) hyx
  simp only [hy0, Over.comp_left, Category.assoc] at this
  rw [← Over.comp_left _ _ _ inc pr, hip, Over.id_left, Category.comp_id] at this
  exact this
end GlobalTheory.Mum.CanonTors
