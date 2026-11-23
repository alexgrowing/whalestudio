import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.kerRead_of :
    KerU → FFRead → LiftFF → PullKer → WVal → KerRead := by
  intro hKU hFF hLF hPK hWV p _ D O _ _ _ _ f b N r w _ hS M j T V _ _ _ _ hp x z hz σ o₁ m₁ P
  haveI := M.smooth
  haveI := T.fin
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : LocallyOfFiniteType M.s := inferInstance
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : IsLocallyNoetherian T.Y := LocallyOfFiniteType.isLocallyNoetherian T.s
  have hcz : CharZero (FractionRing V) := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ M.s)
    have key : ∀ n : ℕ, n ≠ 0 → (n : V) ≠ 0 := by
      intro n hn
      obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
      have hmu : IsUnit (m : O) :=
        b.unit m ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hm).symm
      have hmV : IsUnit (m : V) := by simpa using hmu.map φ.hom
      push_cast
      exact mul_ne_zero (pow_ne_zero _ hp) hmV.ne_zero
    refine charZero_of_inj_zero fun n hn => by_contra fun h => key n h ?_
    rw [← map_natCast (algebraMap V (FractionRing V))] at hn
    exact IsFractionRing.injective V (FractionRing V) (by simpa using hn)
  obtain ⟨-, hmon, hact, -, -, ψ', hmon', h1, h2⟩ := T.isog
  obtain ⟨hRep, -, hKill⟩ := hKU p D O b N r w (Ideal.IsMaximal.ne_top ‹_›) hS.ule T.Y (T.s ≫ M.s)
    T.o T.o' T.ψ ψ' (f * j) hmon hmon' hact h1 h2
  have ukerComp : ∀ {T1 T2 : Over T.Y} (u : T1 ⟶ T2) (g : T2 ⟶ T.o.A),
      UKer r T.o T.ψ T2 g → UKer r T.o T.ψ T1 (u ≫ g) := by
    intro T1 T2 u g hg
    obtain ⟨hg1, e, hg2⟩ := hg
    exact ⟨by rw [Category.assoc, hg1, comp_one], e, fun c hc => by rw [Category.assoc, hg2 c hc, comp_one]⟩
  have compat : ∀ (T' : Over (Sp (IsLocalRing.ResidueField V))) (g : T' ⟶ o₁.A)
      (g₀ : Over.mk (T'.hom ≫ resPt V ≫ z) ⟶ T.o.A), g₀.left = g.left ≫ P.m₀.φ →
      (UKer r o₁ P.ψ T' g ↔ UKer r T.o T.ψ (Over.mk (T'.hom ≫ resPt V ≫ z)) g₀) := by
    intro T' g g₀ hg
    obtain ⟨hA, -, hC⟩ := (hPK _ _ _ _ _ _ _ _ _ _ _ _ _ _ P.m₀ P.m' T.ψ P.ψ P.sq).1 T'
      (Over.mk (T'.hom ≫ resPt V ≫ z)) rfl g g₀ (by simpa using hg)
    simp only [UKer, hA, hC]
  have HT := (hPK _ _ _ _ _ _ _ _ _ _ _ _ _ _ T.ms T.ms (𝟙 M.univ.A) (𝟙 T.o.A) (by simp)).1
  have hwu : ∀ (T' : Over T.Y) (g : T' ⟶ T.o.A), KilledBy T.o w g →
      (UKer r T.o T.ψ T' g ↔ g ≫ T.ψ = 1) := by
    intro T' g hg
    exact ⟨fun h => h.1, fun h => ⟨h, 1, fun c hc => hg c (hS.ule (by simpa using hc))⟩⟩
  have hcard : Nat.card {g // UKer r T.o T.ψ
      (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z)) g} = (p ^ f) ^ j := by
    have htj := T.tj (FractionRing V) (spMap (algebraMap V (FractionRing V)) ≫ z)
    have he : ∀ g, UKer r T.o T.ψ (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z)) g ↔
        (g ≫ T.ψ = 1 ∧ KilledBy T.o w g) := by
      intro g
      constructor
      · intro hg
        exact ⟨hg.1, htj.1 g hg.1 hg.2⟩
      · intro hg
        exact (hwu _ g hg.2).mpr hg.1
    rw [Nat.card_congr (Equiv.subtypeEquivRight he), htj.2, hS.norm, hS.m1, _root_.one_mul]
  refine ⟨?_, fun a => ?_⟩
  · have hc : ((p ^ (f * j) : ℕ) : V) ≠ 0 := by
      push_cast
      exact pow_ne_zero _ hp
    have hR := hFF T.Y T.o.A T.o.ab (UKer r T.o T.ψ) hRep (p ^ (f * j)) hKill V hc z o₁.A P.m₀.φ
      P.m₀.cart.1 (UKer r o₁ P.ψ) compat
    rwa [hcard] at hR
  have hw0 : (a.left ≫ P.m₀.φ) ≫ T.o.A.hom = (Over.mk ((𝟙_ (Over _)).hom ≫ resPt V ≫ z)).hom := by
    rw [Category.assoc, P.m₀.cart.1.w, ← Category.assoc, Over.w a]
    rfl
  let a₀ : Over.mk ((𝟙_ (Over _)).hom ≫ resPt V ≫ z) ⟶ T.o.A := Over.homMk (a.left ≫ P.m₀.φ) hw0
  have hiff : UKer r o₁ P.ψ _ a ↔ UKer r T.o T.ψ _ a₀ := compat _ a a₀ rfl
  rw [hiff]
  constructor
  · intro ha₀
    obtain ⟨K, i, -, hfin, hflat, hK⟩ := hRep
    obtain ⟨y0, hy0⟩ := (hK _ a₀).mpr ha₀
    obtain ⟨g', hg'1, hg'2⟩ := hLF T.Y K.left K.hom hfin hflat V z y0.left
      ((Over.w y0).trans (Category.id_comp _))
    have hw1 : (g' ≫ i.left) ≫ T.o.A.hom = (Over.mk z).hom := by
      rw [Category.assoc, Over.w i, hg'1]
      rfl
    let a' : Over.mk z ⟶ T.o.A := Over.homMk (g' ≫ i.left) hw1
    have ha' : UKer r T.o T.ψ _ a' := (hK _ a').mp ⟨Over.homMk g' hg'1, by
      apply Over.OverMorphism.ext
      simp [a']⟩
    have hUi : resPt V ≫ a'.left = a.left ≫ P.m₀.φ := by
      have e1 := congrArg CommaMorphism.left hy0
      simp only [Over.comp_left, Over.homMk_left, a₀] at e1
      simp only [a', Over.homMk_left]
      rw [← Category.assoc, hg'2, e1]
    have hw2 : (a'.left ≫ T.ms.φ) ≫ M.univ.A.hom = (Over.mk x).hom := by
      rw [Category.assoc, T.ms.cart.1.w, ← Category.assoc, Over.w a']
      exact hz
    let g : Over.mk x ⟶ M.univ.A := Over.homMk (a'.left ≫ T.ms.φ) hw2
    refine ⟨g, ?_, ?_, ?_⟩
    · obtain ⟨ρ, hρl, -, hρk, -⟩ := hWV p D O b N M w V x
      rw [hρk]
      let rz : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ Over.mk z :=
        Over.homMk (spMap (algebraMap V (FractionRing V))) rfl
      have hag := ukerComp rz a' ha'
      have hkill := (T.tj (FractionRing V) (spMap (algebraMap V (FractionRing V)) ≫ z)).1
        (rz ≫ a') hag.1 hag.2
      refine ((HT (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z))
        (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x)) rfl (rz ≫ a') (ρ g) ?_).2.2 w).mp hkill
      rw [hρl]
      simp [rz, g]
    · intro a'' ha''
      have e : a'' = a' := by
        apply Over.OverMorphism.ext
        exact T.ms.cart.1.hom_ext (by simpa [g] using ha'') ((Over.w a'').trans (Over.w a').symm)
      rw [e]
      exact ha'.1
    · simp only [g, Over.homMk_left]
      rw [← P.tri, ← Category.assoc, ← hUi, Category.assoc]
  · rintro ⟨g, hgk, hgker, hgeq⟩
    have hw3 : g.left ≫ M.univ.A.hom = z ≫ T.s := (Over.w g).trans hz.symm
    let a' : Over.mk z ⟶ T.o.A := Over.homMk (T.ms.cart.1.lift g.left z hw3) (T.ms.cart.1.lift_snd _ _ _)
    have ha'l : a'.left ≫ T.ms.φ = g.left := T.ms.cart.1.lift_fst _ _ _
    have hk' : KilledBy T.o w a' :=
      ((HT (Over.mk z) (Over.mk x) rfl a' g (by simp [ha'l])).2.2 w).mpr hgk
    have ha' : UKer r T.o T.ψ _ a' := (hwu _ a' hk').mpr (hgker a' ha'l)
    let rp : Over.mk ((𝟙_ (Over _)).hom ≫ resPt V ≫ z) ⟶ Over.mk z :=
      Over.homMk (resPt V) (Category.id_comp _).symm
    have e : a₀ = rp ≫ a' := by
      apply Over.OverMorphism.ext
      simp only [a₀, rp, Over.homMk_left, Over.comp_left]
      apply T.ms.cart.1.hom_ext
      · rw [Category.assoc, P.tri, Category.assoc, ha'l, hgeq]
      · rw [hw0, Category.assoc, Over.w a']
        exact Category.id_comp _
    rw [e]
    exact ukerComp rp a' ha'
