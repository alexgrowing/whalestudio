import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoRestrictAlongSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMovedToTraitSideStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMovedToCoverSideStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupPowValueEqOfConjugateTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetryValueEqOfConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionCompatFibreIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitFibreIsoCommTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitFibreIsoCommNegStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem GlobalTheory.ThetaMove.ptSec_transl' {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (p x : T ⟶ A) :
    (ptSecT A p).left ≫ (translT A x).left = (ptSecT A (x * p)).left := by
  rw [← Over.comp_left]
  congr 1
  rw [ptSecT, translT, comp_lift, lift_fst, ptSecT, translPt_eq, MonObj.comp_mul, lift_fst_assoc, Category.id_comp,
    lift_snd]

theorem GlobalTheory.ThetaMove.translT_inv {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (x : T ⟶ A) :
    (translT A x).left ≫ (translT A x⁻¹).left = 𝟙 _ ∧ (translT A x⁻¹).left ≫ (translT A x).left = 𝟙 _ := by
  constructor
  · rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, inv_mul_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]
  · rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, mul_inv_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]

example (R : Type) [CommRing R] [IsDomain R] (W : Type) [CommRing W] [IsDomain W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] : jFK (R := W) F ≫ jK W = spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
  unfold jFK jK spMap
  rw [← Spec.map_comp]
  rfl

theorem GlobalTheory.ThetaMove.transport_symLift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A), (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left → x' ^ (C.n ^ j) = 1 → ((∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ') → ∃ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ) ∧ ∀ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ → ∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ' ∧ ∀ (σ σ' : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j)) (τ τ' : SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ' p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ' q z Jt) → IsActOf T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) θ' σ σ' → IsActOf C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) θ τ τ' := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ hφ f hf hf1 hf2 w₀ hw₀ x' x hx hx'
  have hPL := C.P.L.isLB
  have hAL := C.A.isLB
  have hGL := T.U.LG.isLB
  have hTL := T.A.isLB
  have hgi : T.U.gen.inv.left ≫ T.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  obtain ⟨w, hw, hgw⟩ := GlobalTheory.T.exists_lineBundleIso_restrict_along_section hGL hTL hgi w₀ hw₀
  have h₁ : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α =
      (snd (TFK (R := W) F) T.A.A).left ≫ (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.β := by
    rw [Category.assoc]; exact hf2
  have hT1 := GlobalTheory.T.traitFibreIso_comm_translation C T F f hf1 hf2 x' x hx
  have hneg := GlobalTheory.T.traitFibreIso_comm_neg C T F f hf1 hf2
  have hinv : f ≫ (translT C.A.A x⁻¹).left = (translT T.A.A x'⁻¹).left ≫ f := by
    calc f ≫ (translT C.A.A x⁻¹).left
        = ((translT T.A.A x'⁻¹).left ≫ (translT T.A.A x').left) ≫ f ≫ (translT C.A.A x⁻¹).left := by
          rw [(translT_inv x').2, Category.id_comp]
      _ = (translT T.A.A x'⁻¹).left ≫ (f ≫ (translT C.A.A x).left) ≫ (translT C.A.A x⁻¹).left := by
          rw [hT1]; simp only [Category.assoc]
      _ = (translT T.A.A x'⁻¹).left ≫ f := by
          rw [Category.assoc, (translT_inv x).1, Category.comp_id]
  have hpt : ∀ i : ℕ, (ptSecT T.A.A (x' ^ i)).left ≫ f = (ptSecT C.A.A (x ^ i)).left := by
    intro i
    induction i with
    | zero =>
      rw [pow_zero, pow_zero, ← inv_mul_cancel x', ← inv_mul_cancel x, ← ptSec_transl', ← ptSec_transl',
        Category.assoc, ← hinv, ← Category.assoc, hx]
    | succ i ih =>
      rw [pow_succ', pow_succ', ← ptSec_transl', ← ptSec_transl', Category.assoc, ← hT1, ← Category.assoc, ih]
  have hpow : ∀ i : ℕ, f ≫ (translT C.A.A (x ^ i)).left = (translT T.A.A (x' ^ i)).left ≫ f :=
    fun i => GlobalTheory.T.traitFibreIso_comm_translation C T F f hf1 hf2 _ _ (hpt i)
  have hG0 : ((snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.G.hom =
      (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    have e1 : T.U.gen.inv.left ≫ pullback.snd T.G.hom (jK W) = T.A.A.hom := Over.w T.U.gen.inv
    have e2 : (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom = (fst (TFK (R := W) F) T.A.A).left ≫ jFK (R := W) F :=
      (Over.w (snd (TFK (R := W) F) T.A.A)).trans (Over.w (fst (TFK (R := W) F) T.A.A)).symm
    have e3 : jFK (R := W) F ≫ jK W = spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
      unfold jFK jK spMap
      rw [← Spec.map_comp]
      rfl
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc T.U.gen.inv.left, e1, ← Category.assoc,
      e2, Category.assoc, e3]
  let JPc : ∀ {Z : Scheme.{0}} (z : Z), (Z ⟶ C.G.left) → C.P.L.L.ι := fun z ψ => (exists_chart hPL (ψ z)).choose
  have gJP : ∀ {Z : Scheme.{0}} (z : Z), Good C.P.L.L z (JPc z) := fun z ψ => (exists_chart hPL (ψ z)).choose_spec
  let JGc : ∀ {Z : Scheme.{0}} (z : Z), (Z ⟶ T.G.left) → T.U.LG.L.ι := fun z ψ => (exists_chart hGL (ψ z)).choose
  have gJG : ∀ {Z : Scheme.{0}} (z : Z), Good T.U.LG.L z (JGc z) := fun z ψ => (exists_chart hGL (ψ z)).choose_spec
  let Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (TFK (R := W) F ⊗ T.A.A).left) → ∀ z : Z, ((Z ⟶ C.A.A.left) → C.A.L.ι) →
      ((Z ⟶ T.A.A.left) → T.A.L.ι) → (Z.presheaf.stalk z)ˣ := fun q z JA Jt =>
    tf wA T.ℓ w f (snd (TFK (R := R) F) C.A.A).left (snd (TFK (R := W) F) T.A.A).left q z (JPc z) JA (JGc z) Jt
  have conv : ∀ (σ : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j))
      (τ : SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) →
      ∀ (Z : Scheme.{0}) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left) (z : Z) JA Jt, Good C.A.L z JA → Good T.A.L z Jt →
        sval τ (q ≫ f) z JA = (Ψ q z JA Jt ^ ((C.n ^ j : ℕ) : ℤ)).val * sval σ q z Jt := by
    intro σ τ hr Z q z JA Jt hJA hJt
    have e := hr Z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) (q ≫ f) q
      rfl (by simp only [Category.assoc]; rw [hf2]) (by rw [Category.assoc, hG0]) z (JPc z) JA (JGc z) Jt (gJP z) hJA
      (gJG z) hJt
    simp only [Category.assoc] at e
    show sval τ (q ≫ f) z JA = ((tf wA T.ℓ w f (snd (TFK (R := R) F) C.A.A).left (snd (TFK (R := W) F) T.A.A).left
      q z (JPc z) JA (JGc z) Jt) ^ ((C.n ^ j : ℕ) : ℤ)).val * sval σ q z Jt
    simp only [tf, hgw, Category.assoc]
    rw [zpow_natCast, mul_pow, mul_pow, inv_pow, Units.val_mul, Units.val_mul]
    calc sval τ (q ≫ f) z JA
        = (((gw wA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left) z
            (JPc z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β))
            (JA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left))) ^ (C.n ^ j))⁻¹).val *
          ((gw wA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left) z
            (JPc z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β))
            (JA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ (q ≫ f) z JA) := by
          rw [← _root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.one_mul]
      _ = _ := by rw [e]; ring
  have hs₂ : ∀ p : TFK (R := W) F ⟶ T.A.A, (translT T.A.A p).left ≫ (snd (TFK (R := W) F) T.A.A).left =
      (translPt T.A.A p).left := fun p => by rw [← Over.comp_left, translT, lift_snd]
  have hn₂ : (negT T.A.A (TFK (R := W) F)).left ≫ (snd (TFK (R := W) F) T.A.A).left =
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left := by rw [← Over.comp_left, negT, lift_snd]
  have hn₃ : (negT T.A.A (TFK (R := W) F)).left ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left =
      f ≫ (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left := by
    rw [← Category.assoc, ← hneg, Category.assoc, ← Over.comp_left, negT, lift_snd]
  have hs₃ : (translT T.A.A x').left ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left = f ≫ (translPt C.A.A x).left := by
    rw [← Category.assoc, ← hT1, Category.assoc, ← Over.comp_left, translT, lift_snd]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨pt', φ', hφ'⟩, hs'⟩
    have e0 : pt' = x' := hs'.pt_eq
    subst e0
    obtain ⟨u, hu, hvu⟩ := GlobalTheory.T.exists_generator_moved_to_cover_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (translPt C.A.A x).left (snd (TFK (R := W) F) T.A.A).left (translPt T.A.A pt').left (translT T.A.A pt').left h₁
      (hs₂ pt') hs₃ ((C.n ^ j : ℕ) : ℤ) φ' hφ'
    obtain ⟨ν', hν', hsym'⟩ := hs'.sym
    obtain ⟨ν, hν, hvν⟩ := GlobalTheory.T.exists_generator_moved_to_cover_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left (snd (TFK (R := W) F) T.A.A).left
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left (negT T.A.A (TFK (R := W) F)).left h₁ hn₂ hn₃
      ((C.n ^ j : ℕ) : ℤ) ν' hν'
    have Hu := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvu Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    have Hν := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvν Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    refine ⟨⟨x, u, hu⟩, ⟨rfl, corr_of_val hAL fun y J hJ => ?_, ν, hν, corr_of_val hAL fun y J hJ => ?_⟩⟩
    · have hJt : Good T.A.L y (fun ψ => (exists_chart hTL (ψ y)).choose) := fun ψ => (exists_chart hTL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion f _ (C.n ^ j) ⟨x, u, hu⟩ ⟨pt', φ', hφ'⟩ Ψ hpow hx' Hu _ (inv f) y J _ hJ hJt
      rw [IsIso.inv_hom_id] at e
      rw [e, val_corr hJt hs'.pow_eq (inv f), val_one, val_one]
    · have hJt : Good T.A.L y (fun ψ => (exists_chart hTL (ψ y)).choose) := fun ψ => (exists_chart hTL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate f _ ⟨x, u, hu⟩ ⟨pt', φ', hφ'⟩ ν ν' Ψ hinv hneg Hu Hν _ (inv f) y J _ hJ hJt
      rw [IsIso.inv_hom_id] at e
      rw [e, val_corr hJt hsym' (inv f), val_one, val_one]
  · rintro ⟨pt, φ, hφ⟩ hs
    have e0 : pt = x := hs.pt_eq
    subst e0
    obtain ⟨u', hu', hvu'⟩ := GlobalTheory.T.exists_generator_moved_to_trait_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (translPt C.A.A pt).left (snd (TFK (R := W) F) T.A.A).left (translPt T.A.A x').left (translT T.A.A x').left h₁
      (hs₂ x') hs₃ ((C.n ^ j : ℕ) : ℤ) φ hφ
    obtain ⟨ν, hν, hsym⟩ := hs.sym
    obtain ⟨ν', hν', hvν'⟩ := GlobalTheory.T.exists_generator_moved_to_trait_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left (snd (TFK (R := W) F) T.A.A).left
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left (negT T.A.A (TFK (R := W) F)).left h₁ hn₂ hn₃
      ((C.n ^ j : ℕ) : ℤ) ν hν
    have Hu := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvu' Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    have Hν := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvν' Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    refine ⟨⟨x', u', hu'⟩, ⟨rfl, corr_of_val hTL fun y J' hJ' => ?_, ν', hν', corr_of_val hTL fun y J' hJ' => ?_⟩, ?_⟩
    · have hJA : Good C.A.L y (fun ψ => (exists_chart hAL (ψ y)).choose) := fun ψ => (exists_chart hAL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion f _ (C.n ^ j) ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ Ψ hpow hx' Hu _ (𝟙 _) y _ J' hJA hJ'
      rw [← e, val_corr hJA hs.pow_eq, val_one, val_one]
    · have hJA : Good C.A.L y (fun ψ => (exists_chart hAL (ψ y)).choose) := fun ψ => (exists_chart hAL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate f _ ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ ν ν' Ψ hinv hneg Hu Hν _ (𝟙 _) y _ J' hJA hJ'
      rw [← e, val_corr hJA hsym, val_one, val_one]
    · intro σ σ' τ τ' hr hr' hact
      exact GlobalTheory.T.thetaGroupAction_compat_fibreIso hAL hTL f _ ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ Ψ hT1 Hu σ σ' τ τ' (conv σ τ hr) (conv σ' τ' hr') hact
