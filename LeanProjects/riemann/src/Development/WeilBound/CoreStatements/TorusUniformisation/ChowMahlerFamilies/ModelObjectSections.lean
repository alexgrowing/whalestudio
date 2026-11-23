import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalDim
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TateIsomorphismDescends
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.ModelSectionsTransport

theorem exists_common {F K L : Type} [Field F] [Field K] [Field L] (g : F →+* K) (h : F →+* L) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (j : L →+* Ω), i.comp g = j.comp h := by
  letI := g.toAlgebra
  letI := h.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[F] L)
  letI : Field ((K ⊗[F] L) ⧸ m) := Ideal.Quotient.field m
  let q : K ⊗[F] L →+* AlgebraicClosure ((K ⊗[F] L) ⧸ m) :=
    (algebraMap ((K ⊗[F] L) ⧸ m) (AlgebraicClosure ((K ⊗[F] L) ⧸ m))).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure ((K ⊗[F] L) ⧸ m), inferInstance, inferInstance,
    q.comp Algebra.TensorProduct.includeLeftRingHom,
    q.comp (Algebra.TensorProduct.includeRight : L →ₐ[F] K ⊗[F] L).toRingHom, ?_⟩
  have e := Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := F) (A := K) (B := L)
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  exact congrArg (q.comp ·) e

theorem exists_transport {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {F K L : Type} [Field F] [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L] [CharZero F]
    (t : SAB H (Sp F)) (ht : IsPrincipal t) (g : F →+* K) (h : F →+* L)
    (I : TateIso D L (Over.mk (spMap h) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))) :
    ∃ J : TateIso D K (Over.mk (spMap g) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      ∀ n, 0 < n → ∀ v (s : 𝟙_ (Over (Sp F)) ⟶ t.G), toUnit _ ≫ s = I.ev n v → toUnit _ ≫ s = J.ev n v := by
  obtain ⟨Ω, _, _, i, j, hij⟩ := exists_common g h
  haveI : CharZero K := charZero_of_injective_ringHom g.injective
  haveI : CharZero L := charZero_of_injective_ringHom h.injective
  let uK : Over.mk (spMap (i.comp g)) ⟶ Over.mk (spMap g) :=
    Over.homMk (spMap i) (spMap_comp g i).symm
  let uL : Over.mk (spMap (i.comp g)) ⟶ Over.mk (spMap h) :=
    Over.homMk (spMap j) (by rw [hij, spMap_comp]; rfl)
  obtain ⟨I', -, hI'⟩ := GlobalTheory.FullPoint.exists_tateIso_up (D := D)
    GlobalTheory.abelianSchemeLaws_all.1 (SabModel.pol t ht) t.act.act j uL rfl I
  obtain ⟨J, hJ⟩ := PositivityTheory.Xgn.tate_isomorphism_descends E H D (Sp F) (SabModel.pol t ht)
    t.act.act t.act.hom K Ω i _ _ uK rfl I'
  refine ⟨J, fun n hn v s hs => ?_⟩
  apply GlobalTheory.TorsionFieldExt.comp_injective uK t.G
  show uK ≫ (toUnit _ ≫ s) = uK ≫ J.ev n v
  rw [← hJ n v hn, hI' n v, ← hs, ← Category.assoc,
    toUnit_unique (uK ≫ toUnit _) (uL ≫ toUnit _), Category.assoc]
  rfl

end PositivityTheory.Xgn.ModelSectionsTransport

theorem PositivityTheory.Xgn.model_object_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (F : IntermediateField ℚ ℂ) (hK : KA l ≤ F) (t : SAB H (Sp F)), IsPrincipal t → l.A = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : F →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.p) ∧ (τ H.rt ≠ g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.q)) → ∀ I : TateIso D ℂ (Over.mk (spMap (algebraMap F ℂ)) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (∀ a : D.La, ∃ s : 𝟙_ (Over (Sp F)) ⟶ t.G, toUnit _ ≫ s = I.ev l.M a) → ∃ o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hK).toRingHom), o.t = t := by
  intro E _ _ _ H D l F hK t ht hA hLie I hsec
  obtain ⟨hpr, ham, hkt⟩ := id ht
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨e, he, e', he', hee⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp l.coprime)
  choose eta heta using fun a => hsec (e' • a)
  have inj := GlobalTheory.TorsionFieldExt.comp_injective (x := 𝟙 (Sp F))
    (toUnit (Over.mk (spMap (algebraMap F ℂ)))) t.G
  refine ⟨⟨t, hpr, ham, hkt, eta, fun a c => inj ?_, fun a ha => inj ?_, fun _ => 1,
    fun _ _ => (mul_one 1).symm, fun _ => rfl, ?_⟩, rfl⟩
  · show toUnit _ ≫ eta (a + c) = toUnit _ ≫ (eta a * eta c)
    rw [comp_mul, heta, heta, heta, smul_add, I.add]
  · show toUnit _ ≫ eta a = toUnit _ ≫ 1
    rw [MonObj.comp_one, heta]
    obtain ⟨c, hc⟩ := GlobalTheory.FullPoint.exists_eq_nsmul (D := D) l ((mul_comm _ _).trans l.prod) he' ha
    exact (I.ker _ hM _).mpr ⟨c, hc⟩
  intro k _ _ x β hx
  obtain ⟨g, rfl⟩ : ∃ g : F →+* k, x = spMap g :=
    ⟨(Spec.preimage x).hom, by simp [spMap, Spec.map_preimage]⟩
  have hβ : β = g.comp (IntermediateField.inclusion hK).toRingHom :=
    GlobalTheory.FullPoint.spMap_inj (by rw [spMap_comp]; exact hx.symm)
  subst hβ
  obtain ⟨J, hJ⟩ := PositivityTheory.Xgn.ModelSectionsTransport.exists_transport D t ht g (algebraMap F ℂ) I
  refine ⟨fun τ => hLie k g τ, J, ?_, fun a => ?_, fun a ha => ?_⟩
  · have a1 : J.ζ l.A = 1 := by
      have h := J.ζ_prim l.A l.A_pos
      rw [hA] at h ⊢
      exact IsPrimitiveRoot.one_right_iff.mp h
    have b1 : (baseKA l).ζ = 1 := by
      have h := (baseKA l).ζ_prim
      rw [hA] at h
      exact IsPrimitiveRoot.one_right_iff.mp h
    rw [a1, b1, map_one, Units.val_one]
  · simp only [MonObj.comp_one]
    symm
    rw [hA]
    exact (J.ker 1 one_pos a).mpr ⟨a, (one_smul ℕ a).symm⟩
  · rw [hJ l.M hM (e' • a) (eta a) (heta a)]
    obtain ⟨c, hc⟩ := GlobalTheory.FullPoint.exists_eq_nsmul (D := D) l l.prod he ha
    have h0 : J.ev l.M (e • a) = 1 := (J.ker _ hM _).mpr ⟨c, hc⟩
    calc J.ev l.M (e' • a) = J.ev l.M (e • a) * J.ev l.M (e' • a) := by rw [h0, _root_.one_mul]
      _ = J.ev l.M a := by rw [← J.add, ← add_smul, hee, one_smul]
