import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSiegAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepAdjointActionLevelSiegelPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateLociClosedSiegelPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateConditionsIffPullbacksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOverLieTateLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectMapOfCommonPullbackStatement

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem relRep_htPull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (Z : Scheme.{0}) (π : Z ⟶ S) (u : Obj b N (π ≫ t)) (φu : u.A.left ⟶ c.A.left) (φ₂u : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A c.A π φu ∧ IsSquare φu φ₂u ∧ LBIso u.P (c.P.pull φ₂u) ∧ IsFinite π ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (t' : T ⟶ Sp R) (o : Obj b N t') (φ : o.A.left ⟶ c.A.left) (φ₂ : (G2 o.A).left ⟶ (G2 c.A).left), g ≫ t = t' → IsGrpPullback o.A c.A g φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → ∃! z : T ⟶ Z, z ≫ π = g ∧ ∃ m : ObjMap o u z, m.φ ≫ φu = φ := by
  intro p _ D R _ b N hN hNp h M B _ ζ S _ s₁ t c e he hc
  obtain ⟨E, πE, AE, _, _, φE, φ₂E, actE, ηE, hEn, hEf, pbE, sqE, rosE, etaE, univE⟩ :=
    GlobalTheory.T.exists_rep_adjointAction_level_siegelPullback p D R b N hNp h M B ζ S s₁ t c e he hc
  obtain ⟨Z, j, hj, hZ⟩ := GlobalTheory.T.harrisTaylor_lie_tate_loci_closed_siegelPullback p D R b N hN hNp h M B ζ S s₁ t c e he hc E πE AE φE φ₂E actE ηE
    pbE sqE rosE etaE
  have hZj := (hZ Z j).1 ⟨𝟙 Z, Category.id_comp _⟩
  obtain ⟨u, ψ, ψ₂, pbu, squ, isou, actu, etau⟩ := GlobalTheory.T.exists_harrisTaylorObject_over_lieTate_locus p D R b N hN hNp h M B ζ S s₁ t c e he hc E πE AE
    φE φ₂E actE ηE pbE sqE rosE etaE Z j hZj.1 hZj.2
  haveI : IsFinite πE := hEf
  haveI : Mono j := inferInstance
  refine ⟨Z, j ≫ πE, u, ψ ≫ φE, ψ₂, pbu.comp pbE, squ, isou, inferInstance, ?_⟩
  intro T g t' o φ φ₂ hgt pbo sqo isoo
  have rosO : RosatiFor D o.act (c.P.pull φ₂) :=
    RosatiFor.of_iso o.isLB (pull_isLB c.isLB _) isoo o.rosatiFor
  obtain ⟨z₀, ⟨hz₀, ψ₀, pb₀, hψ₀, act₀, eta₀⟩, uniq₀⟩ := univE T g o.A φ φ₂ o.act o.eta pbo sqo rosO o.etaOK
  have pbo' : IsGrpPullback o.A c.A (z₀ ≫ πE) φ := by rw [hz₀]; exact pbo
  have tr := GlobalTheory.T.harrisTaylorLie_tate_conditions_iff_pullbacks p D R b N S c.A c.P c.isLB E T πE z₀ AE o.A φE φ₂E φ φ₂ ψ₀ actE o.act ηE o.eta o.P
    o.isLB pbE sqE pbo' sqo pb₀ hψ₀ isoo act₀ eta₀
  have hpt : ∀ {R' : Type} [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ z₀ ≫ πE ≫ t = spMap β →
      x ≫ t' = spMap β := fun β x hx => by
    rw [← hgt, ← hz₀]; simpa [Category.assoc] using hx
  obtain ⟨z, hz⟩ := (hZ T z₀).2 ⟨fun R' _ β x hx => (tr.1 R' β x).1 (o.lieHer R' β x (hpt β x hx)),
    fun k _ _ x β hx => (tr.2 k x).1 (o.geomAt k x β (hpt β x hx))⟩
  have w : ψ₀ ≫ AE.hom = (o.A.hom ≫ z) ≫ j := by rw [pb₀.1.w, Category.assoc, hz]
  let ψ' := pbu.1.lift ψ₀ (o.A.hom ≫ z) w
  have h1 : ψ' ≫ ψ = ψ₀ := pbu.1.lift_fst _ _ _
  have h2 : ψ' ≫ u.A.hom = o.A.hom ≫ z := pbu.1.lift_snd _ _ _
  have hact : ∀ a : D.O, (o.act.act a).left ≫ ψ' = ψ' ≫ (u.act.act a).left := fun a => by
    apply pbu.1.hom_ext
    · rw [Category.assoc, h1, act₀, Category.assoc, actu, ← Category.assoc, h1]
    · rw [Category.assoc, h2, Category.assoc, Over.w (u.act.act a), h2, ← Category.assoc,
        Over.w (o.act.act a)]
  have heta : ∀ y, (o.eta y).left ≫ ψ' = z ≫ (u.eta y).left := fun y => by
    apply pbu.1.hom_ext
    · rw [Category.assoc, h1, eta₀, Category.assoc, etau, ← Category.assoc, hz]
    · rw [Category.assoc, h2, Category.assoc, Over.w (u.eta y), ← Category.assoc, Over.w (o.eta y)]
      simp
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_harrisTaylorObjectMap_of_common_pullback p D R b N S c.A c.P c.isLB T Z t' ((j ≫ πE) ≫ t) o u g (j ≫ πE) z φ φ₂
    (ψ ≫ φE) ψ₂ ψ' pbo sqo isoo (pbu.comp pbE) squ isou (by rw [← Category.assoc, hz, hz₀])
    (by rw [← Category.assoc, h1, hψ₀]) h2 hact heta
  refine ⟨z, ⟨by rw [← Category.assoc, hz, hz₀], m, by rw [hm, ← Category.assoc, h1, hψ₀]⟩, ?_⟩
  rintro z' ⟨hz', m', hm'⟩
  have e₀ : z' ≫ j = z₀ := uniq₀ (z' ≫ j) ⟨by rw [Category.assoc]; exact hz', m'.φ ≫ ψ, m'.cart.comp pbu,
    by rw [Category.assoc]; exact hm',
    fun a => by rw [← Category.assoc, m'.act a, Category.assoc, actu]; exact (Category.assoc _ _ _).symm,
    fun y => by rw [← Category.assoc, m'.eta y, Category.assoc, etau]; exact (Category.assoc _ _ _).symm⟩
  exact (cancel_mono j).1 (e₀.trans hz.symm)

end GlobalTheory.UPel.HT
