import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

namespace GlobalTheory.AmpleSeparateOverRing

theorem isSeparated_toSpecZ (R : Type) [CommRing R] (n : ℕ) :
    IsSeparated (specZIsTerminal.from (PSpace R n)) := by
  have : IsProper (PSpace.str R n) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R n
  rw [specZIsTerminal.hom_ext (specZIsTerminal.from (PSpace R n)) (PSpace.str R n ≫ specZIsTerminal.from _)]
  infer_instance

theorem exists_ample_model (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R)
    (ι : Type) (L : ι → LB X) (hL : ∀ i, (L i).IsLB) (M : ι → ℕ)
    (t : ∀ i, Fin (M i + 1) → (L i).Sec)
    (ht : ∀ i, ⨆ m, nonzeroLocus (t i m) = ⊤) (w : ι → ℕ) (hw : ∀ i, 1 ≤ w i)
    (T : Finset ι) :
    ∃ (Q : Scheme.{0}) (Ψ : X ⟶ Q) (r : Q ⟶ Sp R) (N : LB Q) (hN : IsAmpleLB N), IsSeparated r ∧
      Ψ ≫ r = f ∧
      CechPic.cls (N.pull Ψ) (LB.isLB_pull hN.isLB Ψ) = ∑ i ∈ T, (w i : ℤ) • CechPic.cls (L i) (hL i) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (a a' : Sp K ⟶ X), a ≫ Ψ = a' ≫ Ψ →
        a ≫ f = a' ≫ f ∧ ∀ i ∈ T,
          a ≫ ProjSpace.toProj f (t i) (ht i) = a' ≫ ProjSpace.toProj f (t i) (ht i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨Sp R, f, 𝟙 _, LB.triv _, isAmpleLB_of_isAffine (LB.isLB_triv _), inferInstance,
      Category.comp_id _, ?_, ?_⟩
    · rw [Finset.sum_empty]
      exact map_zero (CechPic.pull f)
    · intro K _ _ a a' h
      exact ⟨h, by simp⟩
  | insert i T hi ih =>
    obtain ⟨Q, Ψ, r, N, hN, hr, hΨ, hc, hinj⟩ := ih
    have hO1 := ProjSpace.O1_isLB R (M i)
    have hO : IsAmpleLB (lbPow (ProjSpace.O1 R (M i)) (w i)) :=
      (isAmpleLB_pow_iff hO1 (hw i)).2 (isAmple_projective_O_one R (M i))
    have : IsSeparated (specZIsTerminal.from (PSpace R (M i))) := isSeparated_toSpecZ R (M i)
    have hNp := LB.isLB_pull hN.isLB (pullback.fst (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i))))
    have hOq := LB.isLB_pull hO.isLB (pullback.snd (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i))))
    have hN' := CechPic.isLB_tens hNp hOq
    have hA : IsAmpleLB (CechPic.tens
        (N.pull (pullback.fst (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))))
        ((lbPow (ProjSpace.O1 R (M i)) (w i)).pull
          (pullback.snd (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))))) := by
      refine hN.box hO hN' (IsPullback.of_hasPullback _ _) ?_
      refine (CechPic.cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN' hNp) hOq)).1 ?_
      rw [CechPic.cls_div (LB.isLB_div hN' hNp) hOq, CechPic.cls_div hN' hNp, CechPic.cls_tens hNp hOq]
      abel
    refine ⟨_, pullback.lift Ψ (ProjSpace.toProj f (t i) (ht i)) (specZIsTerminal.hom_ext _ _),
      pullback.fst _ _ ≫ r, _, hA, inferInstance, by rw [← Category.assoc, pullback.lift_fst, hΨ], ?_, ?_⟩
    · rw [Finset.sum_insert hi, ← hc]
      have e := (CechPic.cls_eq_iff (LB.isLB_pull hO1 (ProjSpace.toProj f (t i) (ht i))) (hL i)).2
        (ProjSpace.lbIso_pullback_O1_toProj f (t i) (ht i))
      rw [← e, CechPic.cls_pull hN' _, CechPic.cls_tens hNp hOq, map_add, CechPic.cls_pull hN.isLB,
        CechPic.cls_pull hO.isLB, ← CechPic.pull_comp, ← CechPic.pull_comp, pullback.lift_fst,
        pullback.lift_snd, CechPic.cls_lbPow hO1, map_nsmul, CechPic.cls_pull hN.isLB,
        CechPic.cls_pull hO1, add_comm, natCast_zsmul]
    · intro K _ _ a a' h
      have h1 : a ≫ Ψ = a' ≫ Ψ := by
        have := congrArg (· ≫ pullback.fst (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))) h
        simp only [Category.assoc] at this
        rwa [pullback.lift_fst] at this
      have h2 : a ≫ ProjSpace.toProj f (t i) (ht i) = a' ≫ ProjSpace.toProj f (t i) (ht i) := by
        have := congrArg (· ≫ pullback.snd (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))) h
        simp only [Category.assoc] at this
        rwa [pullback.lift_snd] at this
      obtain ⟨e1, e2⟩ := hinj K a a' h1
      refine ⟨e1, fun j hj => ?_⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact h2
      · exact e2 j hj

theorem isAmpleLB_of_separating : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsProper f →
    ∀ (ι : Type) [Fintype ι] (L : ι → LB X) (hL : ∀ i, (L i).IsLB) (M : ι → ℕ)
    (t : ∀ i, Fin (M i + 1) → (L i).Sec) (ht : ∀ i, ⨆ m, nonzeroLocus (t i m) = ⊤),
    (∀ (K : Type) [Field K] [IsAlgClosed K] (a a' : Sp K ⟶ X), a ≫ f = a' ≫ f →
      (∀ i, a ≫ GlobalTheory.ProjSpace.toProj f (t i) (ht i) = a' ≫ GlobalTheory.ProjSpace.toProj f (t i) (ht i)) →
        a = a') →
    ∀ (w : ι → ℕ), (∀ i, 1 ≤ w i) → ∀ (N : LB X) (hN : N.IsLB),
    GlobalTheory.CechPic.cls N hN = ∑ i, w i • GlobalTheory.CechPic.cls (L i) (hL i) → GlobalTheory.IsAmpleLB N := by
  intro R _ X f hf ι _ L hL M t ht hsep w hw N hN hcls
  obtain ⟨Q, Ψ, r, P, hP, hr, hΨ, hc, hinj⟩ :=
    exists_ample_model R X f ι L hL M t ht w hw Finset.univ
  have : LocallyOfFiniteType (Ψ ≫ r) := by rw [hΨ]; infer_instance
  have : LocallyOfFiniteType Ψ := locallyOfFiniteType_of_comp Ψ r
  have : IsProper (Ψ ≫ r) := by rw [hΨ]; infer_instance
  have : IsProper Ψ := IsProper.of_comp Ψ r
  have : LocallyQuasiFinite Ψ := GlobalTheory.locallyQuasiFinite_of_finite_geometric_points Ψ fun K _ _ y => by
    have : Subsingleton {x : Spec (.of K) ⟶ X // x ≫ Ψ = y} := ⟨fun x x' => Subtype.ext (by
      obtain ⟨e1, e2⟩ := hinj K x.1 x'.1 (x.2.trans x'.2.symm)
      exact hsep K x.1 x'.1 e1 fun i => e2 i (Finset.mem_univ i))⟩
    infer_instance
  have := IsFinite.of_isProper_of_locallyQuasiFinite Ψ
  have hcls' : CechPic.cls (P.pull Ψ) (LB.isLB_pull hP.isLB Ψ) = CechPic.cls N hN := by
    rw [hc, hcls]
    exact Finset.sum_congr rfl fun i _ => natCast_zsmul _ _
  exact (isAmpleLB_congr (LB.isLB_pull hP.isLB Ψ) hN
    ((CechPic.cls_eq_iff _ _).1 hcls')).1 (hP.pull_of_isAffineHom Ψ)

end GlobalTheory.AmpleSeparateOverRing
