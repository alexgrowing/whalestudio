import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointNthMultipleGaloisFixedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterValuesGaloisFixedOfIdempotentTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGtPointInvolutionActionSubOfIdempotentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.TorusExt
attribute [local instance] GlobalTheory.TorusExt.gtGroup

namespace GlobalTheory.Mum.RatChar

theorem charFixed : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → (∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left) → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (p.g.s χ) (LB.pullGen D'.toPre.P.L _ _ (p.g.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ p₀ p hy hact hb χ
  let f : AlgebraicClosure (FractionRing R) →+* AlgebraicClosure (FractionRing R) := σ.toAlgHom.toRingHom
  have hf : f.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) = algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R)) := σ.toAlgHom.comp_algebraMap
  have hB := D'.tau_bimult
  obtain ⟨h, ⟨hhb, hhs⟩, ⟨z, hz, hzι⟩, hhe⟩ := GlobalTheory.T.lattice_point_nth_multiple_galois_fixed_point T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ (F.xp p₀.y)
  have hya : p.y = F.xi (F.xp p₀.y) := by rw [hy, F.xi_xp]
  have hg : n • p.g = iota hB _ p.y := by
    obtain ⟨z', hz', hz'ι⟩ := p.eq
    rw [← (isNsmul_iff_eq _ _ _).1 hz', ← (isIota_iff_eq hB _ _).1 hz'ι]
  have hh : n • h = iota hB _ p.y := by
    rw [hya, ← (isNsmul_iff_eq _ _ _).1 hz, ← (isIota_iff_eq hB _ _).1 hzι]
  set t := p.g - h with ht
  have htn : n • t = 0 := by rw [ht, nsmul_sub, hg, hh, sub_self]
  have hte : GtPtAct F.o F.e t t :=
    GlobalTheory.T.isGtPointInvolutionAction_sub_of_idempotent F.o F.e F.idem p₀.g p.g h t hact hhe ((isAdd_iff_eq _ _ _).2 (sub_add_cancel p.g h).symm)
  have hfixh : gtExt D'.toPre f hf h = h := ((eq_gtExt_iff f hf h h).2 ⟨hhb.symm, hhs⟩).symm
  have hgb : extMap f hf ≫ p.g.b = p.g.b := by
    obtain ⟨b, hb⟩ := hb
    apply Over.OverMorphism.ext
    rw [Over.comp_left, extMap_left, hb, ← Category.assoc]
    congr 1
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
  have htb : extMap f hf ≫ t.b = t.b := by
    have e1 : gtExt D'.toPre f hf t = gtExt D'.toPre f hf p.g - h := by rw [ht, map_sub, hfixh]
    have e2 := congrArg GtPtF.b e1
    rw [gtExt_b, sub_eq_add_neg, add_b, neg_b, gtExt_b, hgb] at e2
    rw [e2, ht, sub_eq_add_neg, add_b, neg_b]
  have htb' : spMap f ≫ t.b.left = t.b.left := by
    have := congrArg (fun q => q.left) htb
    simpa [Over.comp_left, extMap_left] using this
  have hts := GlobalTheory.T.characterValues_galoisFixed_of_idempotent_torsion T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ t hte ⟨0, (isNsmul_iff_eq _ _ _).2 htn.symm, (isZero_iff_eq _).2 rfl⟩ htb'
  have hfixt : gtExt D'.toPre f hf t = t := ((eq_gtExt_iff f hf t t).2 ⟨htb'.symm, hts⟩).symm
  have hfixg : gtExt D'.toPre f hf p.g = p.g := by
    have : p.g = t + h := (sub_add_cancel p.g h).symm
    rw [this, map_add, hfixt, hfixh]
  exact ((eq_gtExt_iff f hf p.g p.g).1 hfixg.symm).2 χ

end GlobalTheory.Mum.RatChar
