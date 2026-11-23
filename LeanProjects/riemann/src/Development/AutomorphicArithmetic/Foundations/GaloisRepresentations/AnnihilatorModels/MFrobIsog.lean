import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isIso_spMap_pow {K : Type} [Field K] [IsAlgClosed K] (φ : K →+* K) {n : ℕ} (hn : 0 < n)
    (hφ : ∀ a, φ a = a ^ n) : IsIso (spMap φ) := by
  have hbij : Function.Bijective φ := by
    refine ⟨φ.injective, fun x => ?_⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x hn
    exact ⟨z, by rw [hφ, hz]⟩
  haveI : IsIso (CommRingCat.ofHom φ) := (RingEquiv.ofBijective φ hbij).toCommRingCatIso.isIso_hom
  unfold spMap
  infer_instance

private theorem cls_hecke_pow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h : (Hecke.lbPow L n).IsLB) :
    GlobalTheory.CechPic.cls (Hecke.lbPow L n) h = n • GlobalTheory.CechPic.cls L hL := by
  refine (GlobalTheory.CechPic.cls_linComb hL _ _ h).trans ?_
  simp [GlobalTheory.CechPic.pull_id]

private theorem square_map_fst_left {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (g : A ⟶ B) : sq2 g ≫ (fst B B).left = (fst A A).left ≫ g.left := by
  simp only [sq2, ← Over.comp_left, lift_fst]

private theorem square_map_snd_left {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (g : A ⟶ B) : sq2 g ≫ (snd B B).left = (snd A A).left ≫ g.left := by
  simp only [sq2, ← Over.comp_left, lift_snd]

private theorem tensor_left_ext {S X : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (u v : X ⟶ (A ⊗ A).left)
    (h₁ : u ≫ (fst A A).left = v ≫ (fst A A).left) (h₂ : u ≫ (snd A A).left = v ≫ (snd A A).left) : u = v := by
  have hw : u ≫ (A ⊗ A).hom = v ≫ (A ⊗ A).hom := by
    rw [← Over.w (fst A A), ← Category.assoc, h₁, Category.assoc]
  have key : (Over.homMk u rfl : Over.mk (u ≫ (A ⊗ A).hom) ⟶ A ⊗ A) = Over.homMk v hw.symm := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa using h₁
    · ext
      simpa using h₂
  simpa using congrArg CommaMorphism.left key

theorem UpperTheory.Gal.crystallineComparison.Mod.frobIsog_of :
    FrobHom → FrobFin → PicFrob → QuasiInv → FrobIsog := by
  intro hHom hFin hPic hQI p _ D R _ b N f κ _ _ _ s φ hφ hs o
  have hp : Nat.Prime p := Fact.out
  have hκ := GlobalTheory.SS.FrobField.cast_zero_sp κ (p := p) (CharP.cast_eq_zero κ p)
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N (Sp κ) (Sp κ) s (spMap φ) o
  revert o₁ m₁
  rw [hs]
  intro o₁ m₁
  have hA := GlobalTheory.SS.FrobField.cast_zero_of_hom o.A.hom hκ
  obtain ⟨F, hFm, hFφ, hFk⟩ := hHom p f hp κ φ hφ o.A o₁.A m₁.φ m₁.cart hA
  have hn : 0 < p ^ f := pow_pos hp.pos f
  haveI : IsIso (spMap φ) := isIso_spMap_pow φ hn hφ
  haveI : IsIso m₁.φ := m₁.cart.1.isIso_fst_of_isIso
  have hFsp : GlobalTheory.SS.FrobField.absFrob (Sp κ) p f hp hκ = spMap φ :=
    GlobalTheory.SS.FrobField.absFrob_spec κ p f hp hκ φ hφ
  have hFφ' : ∀ {Z : Scheme} (h : o.A.left ⟶ Z),
      Over.Hom.left F ≫ m₁.φ ≫ h = GlobalTheory.SS.FrobField.absFrob o.A.left p f hp hA ≫ h := by
    intro Z h
    rw [← Category.assoc, hFφ]
  have hpt : ∀ (a : 𝟙_ (Over (Sp κ)) ⟶ o.A),
      Over.Hom.left a ≫ Over.Hom.left F ≫ m₁.φ = spMap φ ≫ Over.Hom.left a := by
    intro a
    rw [hFφ, ← GlobalTheory.SS.FrobField.absFrob_nat (Over.Hom.left a) p f hp hκ hA]
    exact congrArg (· ≫ Over.Hom.left a) hFsp
  have hact : ∀ c, o.act.act c ≫ F = F ≫ o₁.act.act c := by
    intro c
    ext1
    rw [← cancel_mono m₁.φ]
    simp only [Over.comp_left, Category.assoc, m₁.act, hFφ, hFφ']
    exact (GlobalTheory.SS.FrobField.absFrob_nat _ p f hp hA hA).symm
  have heta : ∀ x, o₁.eta x = o.eta x ≫ F := by
    intro x
    ext1
    rw [← cancel_mono m₁.φ, m₁.eta, Over.comp_left, Category.assoc, hpt]
  have hG := GlobalTheory.SS.FrobField.cast_zero_of_hom (G2 o.A).hom hκ
  have hsq : sq2 F ≫ m₁.φ₂ = GlobalTheory.SS.FrobField.absFrob (G2 o.A).left p f hp hG := by
    apply tensor_left_ext
    · rw [Category.assoc, m₁.sq.1, ← Category.assoc, square_map_fst_left, Category.assoc, hFφ]
      exact (GlobalTheory.SS.FrobField.absFrob_nat _ p f hp hG hA).symm
    · rw [Category.assoc, m₁.sq.2, ← Category.assoc, square_map_snd_left, Category.assoc, hFφ]
      exact (GlobalTheory.SS.FrobField.absFrob_nat _ p f hp hG hA).symm
  have hpol : Nonempty (LBIso (Hecke.lbPow o.P (p ^ f)) (o₁.P.pull (sq2 F))) := by
    have h1 : (Hecke.lbPow o.P (p ^ f)).IsLB :=
      LB.isLB_linComb o.isLB (fun _ : Fin (p ^ f) => 𝟙 _) (fun _ => (1 : ℤ))
    have h2 := pull_isLB o₁.isLB (sq2 F)
    have h3 := pull_isLB o.isLB m₁.φ₂
    have e1 : GlobalTheory.CechPic.cls o₁.P o₁.isLB = GlobalTheory.CechPic.pull m₁.φ₂ (GlobalTheory.CechPic.cls o.P o.isLB) := by
      rw [(GlobalTheory.CechPic.cls_eq_iff o₁.isLB h3).mpr m₁.pol, GlobalTheory.CechPic.cls_pull]
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff h1 h2).mp ?_⟩
    rw [cls_hecke_pow o.isLB, GlobalTheory.CechPic.cls_pull o₁.isLB, e1, ← GlobalTheory.CechPic.pull_comp, hsq, hPic]
  have hFl : Over.Hom.left F = GlobalTheory.SS.FrobField.absFrob o.A.left p f hp hA ≫ inv m₁.φ := by
    rw [← hFφ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hlft : LocallyOfFiniteType o.A.hom := by
    haveI := o.ab
    haveI : Smooth o.A.hom := IsAbelianScheme.smooth
    infer_instance
  obtain ⟨hfin, hsurj⟩ := hFin p f hp κ o.A.left o.A.hom hlft hA
  have hfin' : IsFinite (Over.Hom.left F) := by
    rw [hFl]
    infer_instance
  have hsurj' : Surjective (Over.Hom.left F) := by
    rw [hFl]
    infer_instance
  have hker : ∀ (K : Type) [Field K] [IsAlgClosed K] (z : Sp K ⟶ Sp κ) (g : Over.mk z ⟶ o.A),
      g ≫ F = 1 → g = 1 := by
    intro K _ _ z g hg
    have hT := GlobalTheory.SS.FrobField.cast_zero_of_hom z hκ
    haveI : CharP K p := charP_of_injective_ringHom (Spec.preimage z).hom.injective p
    haveI : ExpChar K p := ExpChar.prime hp
    have hτ : ∀ c : K, iterateFrobenius K p f c = c ^ p ^ f := by
      intro c
      simp [iterateFrobenius_def]
    haveI : IsIso (spMap (iterateFrobenius K p f)) := isIso_spMap_pow _ hn hτ
    have hFK : GlobalTheory.SS.FrobField.absFrob (Over.mk z).left p f hp hT = spMap (iterateFrobenius K p f) :=
      GlobalTheory.SS.FrobField.absFrob_spec K p f hp hT _ hτ
    have hk := (hFk _ g).mp hg hT
    rw [hFK, cancel_epi] at hk
    exact Over.OverMorphism.ext hk
  obtain ⟨ψ', hψm, e1, e2⟩ := hQI p D R b N κ s (p ^ f) hn o o₁ F hFm hfin' hsurj' hpol hker
  refine ⟨o₁, m₁, F, ⟨⟨f, rfl⟩, hFm, hact, heta, hpol, ψ', hψm, e1, e2⟩, ?_, hFk⟩
  intro a
  rw [Over.comp_left, Category.assoc]
  exact hpt a
