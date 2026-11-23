import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnramifiedRepresentingPolarizedHomsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomAgreeLocusClosedSubschemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemePullbackAdjointEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommMonObjOfGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBiextensionHypPullbackOfGroupPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixWeightedPairBundleRigidifiedAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPullbackPowerIsRigidifiedRelAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeFiniteIntersectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeIntersectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeRingActionIffEndomorphismRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionOnGroupSchemeIntCombinationEqProdZpowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionAdjointOfAdjointOnSpanningFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeBaseChangeHomOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackPowObjProjectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfComponentsIntoGroupSchemeProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeEndProductPowersTransportGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormBundlePullbackAdjointActionEqDiagonalPowerStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin
open ReciprocityTheory.ChartRestriction.G.Out

theorem qHyp_pull : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left) (Q : LB (A ⊗ A).left), IsGrpPullback A' A f φ → IsSquare φ φ₂ → QHyp A Q → QHyp A' (Q.pull φ₂) :=
  GlobalTheory.T.symmetricBiextensionHyp_pullback_of_groupPullback

theorem formLB_props : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsAbelianScheme (Out.powObj A r) ∧ (formLB A Q (Out.powPr A (n := r)) W).IsLB ∧ Out.Rigidified (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) ∧ Out.RelAmple (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) :=
  GlobalTheory.T.matrixWeightedPairBundle_rigidified_ample

theorem diagPow_props : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (d : ℕ), 0 < d → (diagPow A Q d).IsLB ∧ Out.Rigidified A (diagPow A Q d) ∧ Out.RelAmple A (diagPow A Q d) :=
  GlobalTheory.T.diagonalPullbackPower_isRigidified_relAmple

theorem closed_inter : ∀ (H : Scheme.{0}) (Idx : Type) [Finite Idx] (Z : Idx → Scheme.{0}) (i : ∀ k, Z k ⟶ H), (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h :=
  GlobalTheory.T.exists_closedSubscheme_finite_intersection

theorem closed_inter₂ : ∀ (H Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ H) (i₂ : Z₂ ⟶ H), IsClosedImmersion i₁ → IsClosedImmersion i₂ → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ (∃ z, z ≫ i₁ = h) ∧ ∃ z, z ≫ i₂ = h :=
  GlobalTheory.T.exists_closedSubscheme_intersection

theorem exists_act_iff_rels : ∀ (O : Type) [Ring O] (r : ℕ) (e : Fin r → O), Submodule.span ℤ (Set.range e) = ⊤ → ∃ (m : ℕ) (N : Fin m → Fin r → ℤ) (c1 : Fin r → ℤ) (cm : Fin r → Fin r → Fin r → ℤ), ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (f : Fin r → (A ⟶ A)), (∀ k, IsMonHom (f k)) → ((∃ act : O → (A ⟶ A), IsRAct A act ∧ ∀ k, act (e k) = f k) ↔ ((∀ j, ∏ k, f k ^ N j k = 1) ∧ ∏ k, f k ^ c1 k = 𝟙 A ∧ ∀ i j, f i ≫ f j = ∏ k, f k ^ cm i j k)) :=
  GlobalTheory.T.groupScheme_ringAction_iff_endomorphism_relations

theorem act_sum_smul : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [Ring O] (act : O → (A ⟶ A)), IsRAct A act → ∀ (r : ℕ) (e : Fin r → O) (c : Fin r → ℤ), act (∑ k, c k • e k) = ∏ k, act (e k) ^ c k :=
  GlobalTheory.T.ringActionOnGroupScheme_intCombination_eq_prod_zpow

theorem adj_of_span : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ∀ (act : O → (A ⟶ A)), IsRAct A act → (∀ i, LBIso (Q.pull (lift (fst A A ≫ act (e i)) (snd A A)).left) (Q.pull (lift (fst A A) (snd A A ≫ act (bar (e i)))).left)) → Adj A Q bar act :=
  GlobalTheory.T.ringAction_adjoint_of_adjoint_on_spanning_family

theorem lbIso_pull_congr : ∀ (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X), Q₁.IsLB → Q₂.IsLB → LBIso Q₁ Q₂ → LBIso (Q₁.pull m) (Q₁.pull m') → LBIso (Q₂.pull m) (Q₂.pull m') :=
  GlobalTheory.T.lineBundleIso_pullback_pair_transfer

theorem exists_hom_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G A : Over S) [GrpObj G] [GrpObj A] (G' A' : Over S') [GrpObj G'] [GrpObj A'] (φG : G'.left ⟶ G.left) (φA : A'.left ⟶ A.left) (p : G ⟶ A), IsGrpPullback G' G f φG → IsGrpPullback A' A f φA → IsMonHom p → ∃ p' : G' ⟶ A', IsMonHom p' ∧ p'.left ≫ φA = φG ≫ p.left :=
  GlobalTheory.T.exists_groupScheme_baseChange_hom_of_grpPullback

theorem exists_pow_baseChange : ∀ (S T : Scheme.{0}) (t : T ⟶ S) (A : Over S) [GrpObj A] (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left) (B' : Over T) [GrpObj B'] (r : ℕ) (φB : B'.left ⟶ (Out.powObj A r).left), IsGrpPullback A' A t φ' → IsGrpPullback B' (Out.powObj A r) t φB → ∃ pr' : Fin r → (B' ⟶ A'), (∀ u, IsMonHom (pr' u)) ∧ (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) ∧ ∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u :=
  GlobalTheory.T.exists_grpPullback_powObj_projections

theorem isMonHom_of_components : ∀ (T : Scheme.{0}) (A' B' C : Over T) [GrpObj A'] [GrpObj B'] [GrpObj C] (r : ℕ) (pr' : Fin r → (B' ⟶ A')), (∀ u, IsMonHom (pr' u)) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ Φ : C ⟶ B', (∀ u, IsMonHom (Φ ≫ pr' u)) → IsMonHom Φ :=
  GlobalTheory.T.isMonHom_of_components_into_groupScheme_product

theorem prodPow_transport : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A t φ → ∀ (r : ℕ) (g : Fin r → (A' ⟶ A')) (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ), (∀ k, (g k).left ≫ φ = φ ≫ (f k).left) → (∏ k, g k ^ c k).left ≫ φ = φ ≫ (∏ k, f k ^ c k).left :=
  GlobalTheory.T.groupSchemeEndProductPowers_transport_grpPullback

theorem homFix_iso_of_act : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (B' : Over T) [GrpObj B'] (φB : B'.left ⟶ (Out.powObj A r).left) (pr' : Fin r → (B' ⟶ A')), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → IsGrpPullback B' (Out.powObj A r) t φB → (∀ u, IsMonHom (pr' u)) → (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ (act : O → (A' ⟶ A')), IsRAct A' act → Adj A' (Q.pull φ₂') bar act → ∀ Φ : A' ⟶ B', (∀ u, Φ ≫ pr' u = act (e u)) → LBIso ((diagPow A Q d).pull φ') (((formLB A Q (Out.powPr A (n := r)) W).pull φB).pull Φ.left) :=
  GlobalTheory.T.formBundle_pullback_adjointAction_eq_diagonalPower

end GlobalTheory.ActFin

namespace GlobalTheory.ActFin
open ReciprocityTheory.ChartRestriction.G.Out

theorem exists_actRep_finite : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∃ R : ActRep A Q bar, IsFinite R.π := by
  intro S _ A _ _ Q hab hQ hr1 hr2 hsym hamp O _ bar r e W d hbar hspan hW hd hcas
  have hQQ : QHyp A Q := ⟨hab, hQ, hr1, hr2, hsym, hamp⟩
  obtain ⟨hGab, hMLB, hMrig, hMamp⟩ := formLB_props S A Q hQQ r W hW
  obtain ⟨hLLB, hLrig, hLamp⟩ := diagPow_props S A Q hQQ d hd
  obtain ⟨R, hfin, -⟩ := GlobalTheory.T.exists_finite_unramified_representing_polarizedHoms S A (Out.powObj A r) (diagPow A Q d) (formLB A Q (Out.powPr A (n := r)) W)
    hab hGab hLLB hMLB hLrig hMrig hLamp hMamp
  haveI : IsFinite R.π := hfin
  haveI : IsLocallyNoetherian R.H := LocallyOfFiniteType.isLocallyNoetherian R.π
  haveI : IsCommMonObj R.AH := GlobalTheory.isCommMonObj_of_grpPullback _ _ A R.AH R.π R.φA R.pbA
  let φ₂H := sqMap R.π R.φA R.pbA.1.w
  have hsqH : IsSquare R.φA φ₂H := isSquare_sqMap _ _ _
  obtain ⟨habH, hQHLB, hr1H, hr2H, hsymH, hampH⟩ := qHyp_pull S R.H R.π A R.AH R.φA φ₂H Q R.pbA hsqH hQQ
  obtain ⟨prH, hprHhom, hprH, -⟩ := exists_pow_baseChange S R.H R.π A R.AH R.φA R.BH r R.φB R.pbA R.pbB
  let f : Fin r → (R.AH ⟶ R.AH) := fun k => R.Φ ≫ prH k
  have hfhom : ∀ k, IsMonHom (f k) := fun k => by
    haveI := R.hom; haveI := hprHhom k; exact inferInstanceAs (IsMonHom (R.Φ ≫ prH k))
  obtain ⟨m, N, c1, cm, halg⟩ := exists_act_iff_rels O r e hspan
  have hcb : ∀ i, ∃ c : Fin r → ℤ, ∑ k, c k • e k = bar (e i) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hspan ▸ Submodule.mem_top)
  choose cb hcb using hcb
  have hN := fun j => GlobalTheory.T.abelianScheme_homAgreeLocus_closedSubscheme R.H R.AH R.AH (∏ k, f k ^ N j k) 1 habH habH
    (isMonHom_prodPow f hfhom _) GlobalTheory.Serre.isMonHom_one
  choose ZN iN hiN hZN using hN
  obtain ⟨Z1, i1, hi1, hZ1⟩ := GlobalTheory.T.abelianScheme_homAgreeLocus_closedSubscheme R.H R.AH R.AH (∏ k, f k ^ c1 k) (𝟙 _) habH habH
    (isMonHom_prodPow f hfhom _) inferInstance
  have hM := fun ij : Fin r × Fin r => GlobalTheory.T.abelianScheme_homAgreeLocus_closedSubscheme R.H R.AH R.AH (f ij.1 ≫ f ij.2) (∏ k, f k ^ cm ij.1 ij.2 k) habH habH
    (by haveI := hfhom ij.1; haveI := hfhom ij.2; exact inferInstance) (isMonHom_prodPow f hfhom _)
  choose ZM iM hiM hZM using hM
  have hA := fun i : Fin r => GlobalTheory.T.exists_closedSubscheme_pullback_adjoint_endomorphism_pair R.H R.AH (Q.pull φ₂H) habH hQHLB hr1H hr2H hsymH hampH (f i)
    (∏ k, f k ^ cb i k) (hfhom i) (isMonHom_prodPow f hfhom _)
  choose ZA iA hiA hZA using hA
  obtain ⟨ZN0, iN0, hiN0, hZN0⟩ := closed_inter R.H (Fin m) ZN iN hiN
  obtain ⟨ZM0, iM0, hiM0, hZM0⟩ := closed_inter R.H (Fin r × Fin r) ZM iM hiM
  obtain ⟨ZA0, iA0, hiA0, hZA0⟩ := closed_inter R.H (Fin r) ZA iA hiA
  obtain ⟨Y1, j1, hj1, hY1⟩ := closed_inter₂ R.H ZN0 Z1 iN0 i1 hiN0 hi1
  obtain ⟨Y2, j2, hj2, hY2⟩ := closed_inter₂ R.H Y1 ZM0 j1 iM0 hj1 hiM0
  obtain ⟨Z, iZ, hiZ, hZ⟩ := closed_inter₂ R.H Y2 ZA0 j2 iA0 hj2 hiA0
  have key : ∀ (T : Scheme.{0}) (h : T ⟶ R.H) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (ψ : A'.left ⟶ R.AH.left)
      (ψ₂ : (A' ⊗ A').left ⟶ (R.AH ⊗ R.AH).left) (g : Fin r → (A' ⟶ A')), IsGrpPullback A' R.AH h ψ →
      IsSquare ψ ψ₂ → (∀ k, (g k).left ≫ ψ = ψ ≫ (f k).left) →
      ((∃ z : T ⟶ Z, z ≫ iZ = h) ↔ ((∀ j, ∏ k, g k ^ N j k = 1) ∧ ∏ k, g k ^ c1 k = 𝟙 A' ∧
        (∀ i j, g i ≫ g j = ∏ k, g k ^ cm i j k)) ∧
        ∀ i, LBIso (((Q.pull φ₂H).pull ψ₂).pull (lift (fst A' A' ≫ g i) (snd A' A')).left)
          (((Q.pull φ₂H).pull ψ₂).pull (lift (fst A' A') (snd A' A' ≫ ∏ k, g k ^ cb i k)).left)) := by
    intro T h A' _ _ ψ ψ₂ g hpb hsq hg
    have canc : ∀ (a b : A' ⟶ A'), a.left ≫ ψ = b.left ≫ ψ → a = b := fun a b hab =>
      Over.OverMorphism.ext (hpb.1.hom_ext hab (by rw [Over.w a, Over.w b]))
    have tr := fun c => prodPow_transport R.H T h R.AH A' ψ hpb r g f c hg
    have t0 : (1 : A' ⟶ A').left ≫ ψ = ψ ≫ (1 : R.AH ⟶ R.AH).left := by
      simpa using tr (fun _ => 0)
    have eN : ∀ j, (∃ z, z ≫ iN j = h) ↔ ∏ k, g k ^ N j k = 1 := fun j => by
      rw [← hZN j T h A' ψ hpb, ← tr, ← t0]
      exact ⟨canc _ _, fun e => by rw [e]⟩
    have e1 : (∃ z, z ≫ i1 = h) ↔ ∏ k, g k ^ c1 k = 𝟙 A' := by
      rw [← hZ1 T h A' ψ hpb, ← tr, Over.id_left, Category.comp_id]
      refine ⟨fun e => canc _ _ (by rw [e, Over.id_left, Category.id_comp]), fun e => by rw [e, Over.id_left, Category.id_comp]⟩
    have eM : ∀ ij : Fin r × Fin r, (∃ z, z ≫ iM ij = h) ↔ g ij.1 ≫ g ij.2 = ∏ k, g k ^ cm ij.1 ij.2 k := fun ij => by
      rw [← hZM ij T h A' ψ hpb, ← tr]
      have : (g ij.1 ≫ g ij.2).left ≫ ψ = ψ ≫ (f ij.1 ≫ f ij.2).left := by
        rw [Over.comp_left, Over.comp_left, Category.assoc, hg, ← Category.assoc, hg, Category.assoc]
      rw [← this]
      exact ⟨canc _ _, fun e => by rw [e]⟩
    have eA : ∀ i, (∃ z, z ≫ iA i = h) ↔ LBIso (((Q.pull φ₂H).pull ψ₂).pull (lift (fst A' A' ≫ g i) (snd A' A')).left)
          (((Q.pull φ₂H).pull ψ₂).pull (lift (fst A' A') (snd A' A' ≫ ∏ k, g k ^ cb i k)).left) := fun i =>
      (hZA i T h A' ψ ψ₂ (g i) (∏ k, g k ^ cb i k) hpb hsq (hg i) (tr (cb i))).symm
    rw [hZ, hY2, hY1, hZN0, hZM0, hZA0]
    constructor
    · rintro ⟨⟨⟨hN', h1'⟩, hM'⟩, hA'⟩
      exact ⟨⟨fun j => (eN j).1 (hN' j), e1.1 h1', fun i j => (eM (i, j)).1 (hM' (i, j))⟩, fun i => (eA i).1 (hA' i)⟩
    · rintro ⟨⟨hN', h1', hM'⟩, hA'⟩
      exact ⟨⟨⟨fun j => (eN j).2 (hN' j), e1.2 h1'⟩, fun ij => (eM ij).2 (hM' ij.1 ij.2)⟩, fun i => (eA i).2 (hA' i)⟩

  haveI : IsClosedImmersion iZ := hiZ
  let AZ : Over Z := (Over.pullback iZ).obj R.AH
  let ψZ : AZ.left ⟶ R.AH.left := pullback.fst R.AH.hom iZ
  have pbZ : IsGrpPullback AZ R.AH iZ ψZ := isGrpPullback_pullback R.AH iZ
  haveI : IsCommMonObj AZ := GlobalTheory.isCommMonObj_of_grpPullback _ _ R.AH AZ iZ ψZ pbZ
  let ψ₂Z := sqMap iZ ψZ pbZ.1.w
  have hsqZ : IsSquare ψZ ψ₂Z := isSquare_sqMap _ _ _
  have hgZ := fun k => exists_hom_baseChange R.H Z iZ R.AH R.AH AZ AZ ψZ ψZ (f k) pbZ pbZ (hfhom k)
  choose gZ hgZhom hgZ using hgZ
  obtain ⟨hrelZ, hadjZ⟩ := (key Z iZ AZ ψZ ψ₂Z gZ pbZ hsqZ hgZ).1 ⟨𝟙 Z, Category.id_comp _⟩
  obtain ⟨actZ, hactZ, hactZe⟩ := (halg Z AZ gZ hgZhom).2 hrelZ
  have hbZ : ∀ i, ∏ k, gZ k ^ cb i k = actZ (bar (e i)) := fun i => by
    rw [← hcb i, act_sum_smul Z AZ O actZ hactZ r e (cb i)]
    simp only [hactZe]
  have hQZ : QHyp AZ (Q.pull (ψ₂Z ≫ φ₂H)) :=
    qHyp_pull S Z (iZ ≫ R.π) A AZ (ψZ ≫ R.φA) (ψ₂Z ≫ φ₂H) Q (pbZ.comp R.pbA) (isSquare_comp hsqZ hsqH) hQQ
  have isoZ : LBIso ((Q.pull φ₂H).pull ψ₂Z) (Q.pull (ψ₂Z ≫ φ₂H)) :=
    GlobalTheory.ArcDataDescent.lbIso_pull_pull hQ _ _ rfl
  have hadjZ' : Adj AZ (Q.pull (ψ₂Z ≫ φ₂H)) bar actZ := adj_of_span Z AZ _ hQZ O bar r e hbar hspan actZ hactZ fun i => by
    have := lbIso_pull_congr _ _ _ _ _ _ (pull_isLB (pull_isLB hQ _) _) hQZ.2.1 isoZ (hadjZ i)
    rwa [hbZ i, ← hactZe i] at this
  refine ⟨{
      H := Z
      π := iZ ≫ R.π
      AH := AZ
      φ := ψZ ≫ R.φA
      φ₂ := ψ₂Z ≫ φ₂H
      pb := pbZ.comp R.pbA
      sq := isSquare_comp hsqZ hsqH
      act := actZ
      isAct := hactZ
      adj := hadjZ'
      rep := ?_ }, ?_⟩
  · intro T t A' _ φ' φ₂' act' hpb hsq hact hadj
    haveI : IsCommMonObj A' := GlobalTheory.isCommMonObj_of_grpPullback _ _ A A' t φ' hpb
    let B' := (Over.pullback t).obj (Out.powObj A r)
    let φB : B'.left ⟶ (Out.powObj A r).left := pullback.fst _ t
    have hB : IsGrpPullback B' (Out.powObj A r) t φB := isGrpPullback_pullback _ t
    obtain ⟨pr', hpr'hom, hpr', hprod'⟩ := exists_pow_baseChange S T t A A' φ' B' r φB hpb hB
    obtain ⟨Φ', hΦ', -⟩ := hprod' A' (fun u => act' (e u))
    have hΦhom : IsMonHom Φ' := isMonHom_of_components T A' B' A' r pr' hpr'hom hprod' Φ' fun u => by
      rw [hΦ' u]; exact hact.1 _
    have hiso := homFix_iso_of_act S A Q hQQ O bar r e W d hbar hspan hW hd hcas T t A' φ' φ₂' B' φB pr' hpb hsq hB hpr'hom hpr'
      hprod' act' hact hadj Φ' hΦ'
    obtain ⟨h₀, ⟨hh₀, ψA, ψB, hψA, hψB, hψAφ, hψBφ, hΦψ⟩, huniq⟩ := R.rep T t A' B' φ' φB Φ' hpb hB hΦhom hiso
    let g : Fin r → (A' ⟶ A') := fun k => act' (e k)
    have hprc : ∀ k, (pr' k).left ≫ ψA = ψB ≫ (prH k).left := fun k => by
      apply R.pbA.1.hom_ext
      · simp only [Category.assoc, hψAφ, hprH k]
        rw [hpr' k, ← Category.assoc, hψBφ]
      · simp only [Category.assoc, hψA.1.w, Over.w (prH k), hψB.1.w]
        rw [← Category.assoc, Over.w (pr' k)]
    have hg : ∀ k, (g k).left ≫ ψA = ψA ≫ (f k).left := fun k => by
      show (act' (e k)).left ≫ ψA = ψA ≫ (R.Φ ≫ prH k).left
      rw [← hΦ' k, Over.comp_left, Over.comp_left, Category.assoc, hprc k, ← Category.assoc, hΦψ, Category.assoc]
    let ψ₂A := sqMap h₀ ψA hψA.1.w
    have hsqA : IsSquare ψA ψ₂A := isSquare_sqMap _ _ _
    have hrel' := (halg T A' g (fun k => hact.1 _)).1 ⟨act', hact, fun k => rfl⟩
    have e₂ : φ₂' = ψ₂A ≫ φ₂H := by
      have hc : IsSquare φ' (ψ₂A ≫ φ₂H) := hψAφ ▸ isSquare_comp hsqA hsqH
      exact pullback.hom_ext (hsq.1.trans hc.1.symm) (hsq.2.trans hc.2.symm)
    have isoA : LBIso (Q.pull φ₂') ((Q.pull φ₂H).pull ψ₂A) := by
      rw [e₂]; exact LBIso.symm (GlobalTheory.ArcDataDescent.lbIso_pull_pull hQ _ _ rfl)
    have hadj' : ∀ i, LBIso (((Q.pull φ₂H).pull ψ₂A).pull (lift (fst A' A' ≫ g i) (snd A' A')).left)
        (((Q.pull φ₂H).pull ψ₂A).pull (lift (fst A' A') (snd A' A' ≫ ∏ k, g k ^ cb i k)).left) := fun i => by
      have hb : ∏ k, g k ^ cb i k = act' (bar (e i)) := by
        rw [← hcb i, act_sum_smul T A' O act' hact r e (cb i)]
      rw [hb]
      exact lbIso_pull_congr _ _ _ _ _ _ (pull_isLB hQ _) (pull_isLB (pull_isLB hQ _) _) isoA (hadj (e i))
    obtain ⟨z₀, hz₀⟩ := (key T h₀ A' ψA ψ₂A g hψA hsqA hg).2 ⟨hrel', hadj'⟩
    let ψ : A'.left ⟶ AZ.left := pullback.lift ψA (A'.hom ≫ z₀) (by rw [hψA.1.w, Category.assoc, hz₀])
    have hψ1 : ψ ≫ ψZ = ψA := pullback.lift_fst _ _ _
    have hpbψ : IsGrpPullback A' AZ z₀ ψ :=
      IsGrpPullback.cancel pbZ (IsGrpPullback.congr hψA hz₀.symm hψ1.symm) (pullback.lift_snd _ _ _)
    have hgψ : ∀ k, (g k).left ≫ ψ = ψ ≫ (gZ k).left := fun k => by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hψ1, hgZ k, ← Category.assoc, hψ1, hg k]
      · rw [Category.assoc, Category.assoc]
        erw [pullback.lift_snd, Over.w (gZ k), pullback.lift_snd]
        rw [← Category.assoc, Over.w (g k)]
    refine ⟨z₀, ⟨by rw [← Category.assoc, hz₀, hh₀], ψ, hpbψ, by rw [← Category.assoc, hψ1, hψAφ], fun a => ?_⟩, ?_⟩
    · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hspan ▸ Submodule.mem_top : a ∈ Submodule.span ℤ (Set.range e))
      rw [← hc, act_sum_smul T A' O act' hact r e c, act_sum_smul Z AZ O actZ hactZ r e c]
      simp only [hactZe]
      exact prodPow_transport Z T z₀ AZ A' ψ hpbψ r g gZ c hgψ
    · rintro h ⟨hπ, ψ₁, hpb₁, hφ₁, hact₁⟩
      have hpb₁' := hpb₁.comp pbZ
      let ψB₁ : B'.left ⟶ R.BH.left := R.pbB.1.lift φB (B'.hom ≫ h ≫ iZ) (by
        rw [hB.1.w, ← hπ]; simp only [Category.assoc])
      have hψB₁φ : ψB₁ ≫ R.φB = φB := R.pbB.1.lift_fst _ _ _
      have hB₁ : IsGrpPullback B' R.BH (h ≫ iZ) ψB₁ :=
        IsGrpPullback.cancel R.pbB (IsGrpPullback.congr hB (by rw [Category.assoc, hπ]) hψB₁φ.symm)
          (by rw [R.pbB.1.lift_snd])
      have hcomp : ∀ k, (g k).left ≫ (ψ₁ ≫ ψZ) = (ψ₁ ≫ ψZ) ≫ (f k).left := fun k => by
        rw [← Category.assoc, hact₁ (e k), Category.assoc, hactZe k, hgZ k, Category.assoc]
      have hH : Φ'.left ≫ ψB₁ ≫ R.BH.hom = ψ₁ ≫ ψZ ≫ R.Φ.left ≫ R.BH.hom := by
        have w1 := hpb₁'.1.w
        have w2 := Over.w Φ'
        have w3 := Over.w R.Φ
        have w4 : ψB₁ ≫ R.BH.hom = B'.hom ≫ h ≫ iZ := R.pbB.1.lift_snd _ _ _
        simp only [Category.assoc] at w1 w4 ⊢
        rw [w4, w3, w1, ← Category.assoc, w2]
      have hΦ₁ : Φ'.left ≫ ψB₁ = (ψ₁ ≫ ψZ) ≫ R.Φ.left := by
        apply R.pbB.1.hom_ext
        · apply powext A r
          · have := congrArg (· ≫ R.π) hH
            simp only [Category.assoc] at this ⊢
            rw [R.pbB.1.w]
            simpa only [Category.assoc] using this
          · intro k
            have l1 : Φ'.left ≫ φB ≫ (Out.powPr A k).left = (g k).left ≫ φ' := by
              rw [← hpr' k, ← Category.assoc, ← Over.comp_left, hΦ' k]
            have l2 : R.Φ.left ≫ R.φB ≫ (Out.powPr A k).left = (f k).left ≫ R.φA := by
              rw [← hprH k, ← Category.assoc, ← Over.comp_left]
            have hc := hcomp k
            simp only [Category.assoc] at hc ⊢
            rw [← Category.assoc ψB₁ R.φB, hψB₁φ, l1, l2, ← hφ₁]
            rw [show (g k).left ≫ ψ₁ ≫ ψZ ≫ R.φA = ((g k).left ≫ ψ₁ ≫ ψZ) ≫ R.φA by simp only [Category.assoc], hc]
            simp only [Category.assoc]
        · simpa only [Category.assoc] using hH
      have e₀ : h ≫ iZ = h₀ := huniq (h ≫ iZ) ⟨by rw [Category.assoc, hπ], ψ₁ ≫ ψZ, ψB₁, hpb₁', hB₁,
        by rw [Category.assoc, hφ₁], hψB₁φ, hΦ₁⟩
      exact (cancel_mono iZ).1 (e₀.trans hz₀.symm)
  · show IsFinite (iZ ≫ R.π)
    infer_instance

end GlobalTheory.ActFin
