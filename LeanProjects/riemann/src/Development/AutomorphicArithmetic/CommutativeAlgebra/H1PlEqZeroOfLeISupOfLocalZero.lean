import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsMayerVietorisConnectingExact
import Development.AutomorphicArithmetic.CommutativeAlgebra.TwistedSectionEqNsmulGeneratorOfConnected
import Development.EtaleCohomology.EtaleTrace.LocalSplitting.Cover2
import Development.EtaleCohomology.EtaleSheaves.LeafAffCoverVanishPfEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.Cb.SeparatedH1Cohomology

private theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (k : V ⟶ U) (n : ℕ)
    (a : Sec F U) : Sec.res k (n • a) = n • Sec.res k a :=
  map_nsmul (F.obj.map k.op).hom n a

private theorem exists_h0_restriction_eq_of_le_open {q : ℕ} [NeZero q] {X E : Scheme.{0}} [IsIntegral X] (ζ : Prim q Γ(X, ⊤))
    (j : E ⟶ X) [IsOpenImmersion j] {O P : E.Opens} (h : P ≤ O) (c : Ht q (sch.obj P) 0 1) :
    ∃ a : Ht q (sch.obj O) 0 1, pl q 1 (E.homOfLE h) 0 a = c := by
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q 1)
  by_cases hP : Nonempty (P : Scheme.{0})
  · haveI : IsIntegral (P : Scheme.{0}) := isIntegral_of_isOpenImmersion (P.ι ≫ j)
    haveI : ConnectedSpace (P : Scheme.{0}) := inferInstance
    obtain ⟨k, hk⟩ := UpperTheory.twisted_section_eq_nsmul_generator_of_connected q 1 (P : Scheme.{0}) (ζ.map (P.ι ≫ j).appTop.hom) ((e P).symm c)
    refine ⟨e O (k • twGen 1 (ζ.map (O.ι ≫ j).appTop.hom)), ?_⟩
    have h1 : c = e P (k • twGen 1 (ζ.map (P.ι ≫ j).appTop.hom)) := by
      rw [← hk, AddEquiv.apply_symm_apply]
    have hk : E.homOfLE h ≫ O.ι ≫ j = P.ι ≫ j := by simp
    rw [h1, he, res_nsmul', (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1, ← hk]
    congr 1
  · have hb : P = ⊥ := le_bot_iff.1 fun p hp => (hP ⟨(⟨p, hp⟩ : P)⟩).elim
    subst hb
    haveI := LateralTheory.E.E8.leafEmptyVanish (ZMod q) (X := E) (tw q 1) 0
    exact ⟨0, Subsingleton.elim _ _⟩

private theorem two {q : ℕ} [NeZero q] {X E : Scheme.{0}} [IsIntegral X] (ζ : Prim q Γ(X, ⊤))
    (j : E ⟶ X) [IsOpenImmersion j] (O₁ O₂ : E.Opens) (hcov : O₁ ⊔ O₂ = ⊤) (y : Ht q (sch.obj E) 1 1)
    (h₁ : pl q 1 O₁.ι 1 y = 0) (h₂ : pl q 1 O₂.ι 1 y = 0) : y = 0 := by
  obtain ⟨d, hd, -⟩ := UpperTheory.Cb.exists_mayerVietoris_connecting_exact (ZMod q) (tw q 1)
  have hc : Cover2 (ZMod q) (sch.map O₁.ι) (sch.map O₂.ι) := LateralTheory.EtaleTrace.LSplitPf.Sch.cover2 (ZMod q) O₁ O₂ hcov
  have : PreservesLimitsOfShape WalkingCospan sch := by
    unfold sch
    infer_instance
  let e := ((isPullback_opens_inf O₁ O₂).map sch).isoPullback
  obtain ⟨-, hz, hx⟩ := hd _ _ hc 0
  obtain ⟨c, hcy⟩ := (hx y).1 ⟨h₁, h₂⟩
  obtain ⟨a, ha⟩ := exists_h0_restriction_eq_of_le_open ζ j (inf_le_left : O₁ ⊓ O₂ ≤ O₁) (pull (ZMod q) e.hom (tw q 1) 0 c)
  have hf : pullback.fst (sch.map O₁.ι) (sch.map O₂.ι) = e.inv ≫ sch.map (E.homOfLE inf_le_left) := by
    simp [e]
  have h0 : d _ _ hc 0 c = 0 := by
    refine (hz c).2 ⟨a, 0, ?_⟩
    rw [map_zero, sub_zero, hf, pull_comp]
    change c = pull _ e.inv _ 0 (pl q 1 _ 0 a)
    rw [ha, ← pull_comp, e.inv_hom_id, pull_id]
  exact hcy.symm.trans h0

private theorem step {q : ℕ} [NeZero q] {X : Scheme.{0}} [IsIntegral X] (ζ : Prim q Γ(X, ⊤))
    (A B : X.Opens) (x : Ht q (sch.obj X) 1 1) (hA : pl q 1 A.ι 1 x = 0) (hB : pl q 1 B.ι 1 x = 0) :
    pl q 1 (A ⊔ B).ι 1 x = 0 := by
  have key : ∀ C : X.Opens, pl q 1 C.ι 1 x = 0 →
      pl q 1 ((A ⊔ B).ι ⁻¹ᵁ C).ι 1 (pl q 1 (A ⊔ B).ι 1 x) = 0 := by
    intro C hC
    have h1 : ((A ⊔ B).ι ⁻¹ᵁ C).ι ≫ (A ⊔ B).ι = ((A ⊔ B).ι ∣_ C) ≫ C.ι := (morphismRestrict_ι _ _).symm
    change pull _ _ _ _ (pull _ _ _ _ x) = 0
    rw [← pull_comp, ← sch.map_comp, h1, sch.map_comp, pull_comp]
    change pull _ _ _ _ (pl q 1 C.ι 1 x) = 0
    rw [hC, map_zero]
  refine two ζ (A ⊔ B).ι ((A ⊔ B).ι ⁻¹ᵁ A) ((A ⊔ B).ι ⁻¹ᵁ B) ?_ _ (key A hA) (key B hB)
  refine eq_top_iff.2 fun p _ => ?_
  have hp : (A ⊔ B).ι p ∈ A ⊔ B := p.2
  exact TopologicalSpace.Opens.mem_sup.2 (TopologicalSpace.Opens.mem_sup.1 hp)

end UpperTheory.Cb.SeparatedH1Cohomology

theorem UpperTheory.h1_pl_eq_zero_of_le_iSup_of_local_zero :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X], Nonempty (Prim q Γ(X, ⊤)) → IsUnit (q : Γ(X, ⊤)) → ∀ (n : ℕ) (U : Fin n → X.Opens) (V : X.Opens), V ≤ ⨆ i, U i → ∀ x : Ht q (sch.obj X) 1 1, (∀ i, pl q 1 (U i).ι 1 x = 0) → pl q 1 V.ι 1 x = 0 := by
  intro q _ X _ hζ _ n
  obtain ⟨ζ⟩ := hζ
  induction n with
  | zero =>
    intro U V hV x _
    have hb : V = ⊥ := le_bot_iff.1 (hV.trans (iSup_of_empty U).le)
    subst hb
    haveI := LateralTheory.E.E8.leafEmptyVanish (ZMod q) (X := X) (tw q 1) 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    intro U V hV x hx
    have hW := ih (fun i => U i.castSucc) (⨆ i : Fin n, U i.castSucc) le_rfl x (fun i => hx _)
    have hS := UpperTheory.Cb.SeparatedH1Cohomology.step ζ _ _ x hW (hx (Fin.last n))
    have hle : V ≤ (⨆ i : Fin n, U i.castSucc) ⊔ U (Fin.last n) := hV.trans (iSup_le fun i => by
      induction i using Fin.lastCases with
      | last => exact le_sup_right
      | cast i => exact le_sup_of_le_left (le_iSup (fun i : Fin n => U i.castSucc) i))
    have hι : V.ι = X.homOfLE hle ≫ ((⨆ i : Fin n, U i.castSucc) ⊔ U (Fin.last n)).ι := by simp
    rw [hι]
    change pull _ (sch.map _) _ _ x = 0
    rw [sch.map_comp, pull_comp]
    change pull _ _ _ _ (pl q 1 _ 1 x) = 0
    rw [hS, map_zero]
