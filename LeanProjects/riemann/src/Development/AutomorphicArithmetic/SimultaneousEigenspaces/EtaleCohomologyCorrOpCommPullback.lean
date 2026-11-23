import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClosD
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtInj
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.Int.Geo TensorProduct

private theorem l_unit_of_charZero (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] :
    IsUnit (l : Γ(UpperTheory.Gal.G3.sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have h2 : IsUnit (l : Ω) := isUnit_iff_ne_zero.mpr h1
  have h3 := h2.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm
  simpa using h3

private theorem pullTot_comp_apply (l : ℕ) [Fact l.Prime] {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x) :
    pullTot l (sch.map (f ≫ g)) x = pullTot l (sch.map f) (pullTot l (sch.map g) x) := by
  rw [Functor.map_comp, pullTot_comp]; rfl

open UpperTheory.Gal.G3 in
theorem UpperTheory.etaleCohomology_corrOp_comm_pullback :
    ∀ (l : ℕ) [Fact l.Prime] (Ω' : Type) [Field Ω'] [CharZero Ω'] {Z Y Z₁ Y₁ : Scheme.{0}} (s t : Y ⟶ Z) [IsFinite s] [Etale s] (s₁ t₁ : Y₁ ⟶ Z₁) (q₁ : Z₁ ⟶ Spec (CommRingCat.of Ω')) (u : Z₁ ⟶ Z) (v : Y₁ ⟶ Y), IsPullback v s₁ s u → v ≫ t = t₁ ≫ u → t₁ ≫ q₁ = s₁ ≫ q₁ → ∀ (A : Htot l (sch.obj Z) →ₗ[ℚ_[l]] Htot l (sch.obj Z)) (A₁ : Htot l (sch.obj Z₁) →ₗ[ℚ_[l]] Htot l (sch.obj Z₁)), IsCorrOp l s t A → IsCorrOp l s₁ t₁ A₁ → pullTot l (sch.map u) ∘ₗ A = A₁ ∘ₗ pullTot l (sch.map u) := by
  intro l _ Ω' _ _ Z Y Z₁ Y₁ s t _ _ s₁ t₁ q₁ u v hv hvt hq A A₁ hA hA₁
  obtain ⟨W, c, G, _, _, a, J, _, σ, hG, hS, hc⟩ := hA
  have SB : SplitsBasic := pSplitsBasic (pSplitsPts pIsoPts) pPtsOfSplits
  have FB : FEtBasic := pFEtBasic pPtsOfSplits
  have hT : (et l (sp Ω')).Good := pEtGood (pEtnGood FB pEtTr) l _ (l_unit_of_charZero l Ω')
  have OE : OpEx.{1} := pOpEx pOpTr
  have FI : FEtInj.{1} := pFEtInj (pGalClosD (pSplitsPts pIsoPts) (pOrdEx pOrdStep))
  haveI : IsFinite s₁ := MorphismProperty.of_isPullback (P := @IsFinite) hv ‹_›
  haveI : Etale s₁ := MorphismProperty.of_isPullback (P := @Etale) hv ‹_›
  obtain ⟨hσ, -⟩ := id hS
  have e : ∀ j, (pullback.fst c u ≫ σ j) ≫ s = pullback.snd c u ≫ u := by
    intro j
    rw [Category.assoc, hσ j, pullback.condition]
  let σ₁ : J → (pullback c u ⟶ Y₁) := fun j => hv.lift (pullback.fst c u ≫ σ j) (pullback.snd c u) (e j)
  have σ₁v : ∀ j, σ₁ j ≫ v = pullback.fst c u ≫ σ j := fun j => hv.lift_fst _ _ _
  have σ₁s : ∀ j, σ₁ j ≫ s₁ = pullback.snd c u := fun j => hv.lift_snd _ _ _
  have hS0 : Splits s (pullback.snd c u ≫ u) fun j => σ₁ j ≫ v := by
    have h := SB.1 s c J σ (pullback.fst c u) hS
    simp only [σ₁v]
    rw [← pullback.condition]
    exact h
  have hS₁ : Splits s₁ (pullback.snd c u) σ₁ := (SB.2 v s₁ s u hv (pullback.snd c u) J σ₁ σ₁s).2 hS0
  have hOp : (et l (sp Ω')).IsOp q₁ q₁ s₁ t₁ A₁ := (pOpEt l q₁ q₁ s₁ t₁ hq A₁).2 hA₁
  have key := (OE _ hT q₁ q₁ s₁ t₁ hq).2 A₁ hOp _ (pullback.snd c u ≫ q₁) (pullback.snd c u) rfl J σ₁
    (fun j => by rw [Category.assoc, hq, ← Category.assoc, σ₁s]) hS₁
  have key' : ∀ y, pullTot l (sch.map (pullback.snd c u)) (A₁ y) =
      ∑ j, pullTot l (sch.map (σ₁ j ≫ t₁)) y := fun y => key y
  have hfet : FEt c (Nat.card G) := FB.2.2 c G a hG
  have hfet₁ : FEt (pullback.snd c u) (Nat.card G) :=
    FB.1 (pullback.fst c u) (pullback.snd c u) c u _ (IsPullback.of_hasPullback c u) hfet
  have hinj : Function.Injective (pullTot l (sch.map (pullback.snd c u))) :=
    FI _ hT q₁ (pullback.snd c u ≫ q₁) (pullback.snd c u) rfl _ Nat.card_pos hfet₁
  refine LinearMap.ext fun x => hinj ?_
  show pullTot l (sch.map (pullback.snd c u)) (pullTot l (sch.map u) (A x)) =
    pullTot l (sch.map (pullback.snd c u)) (A₁ (pullTot l (sch.map u) x))
  rw [key', ← pullTot_comp_apply, ← pullback.condition, pullTot_comp_apply, hc, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pullTot_comp_apply, ← pullTot_comp_apply]
  have hm : pullback.fst c u ≫ σ j ≫ t = (σ₁ j ≫ t₁) ≫ u := by
    rw [Category.assoc, ← hvt, ← Category.assoc (σ₁ j), σ₁v, Category.assoc]
  rw [hm]
