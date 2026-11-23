import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCorrFormPullTensorForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeFrobeniusGrpSchemeCharPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecFieldSmoothOfRelativeDimensionStatement

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.FrobAdjoint

theorem UpperTheory.Gal.Ord.rankV :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ : k →+* k) (V : A.left ⟶ A.left) (m : SMor A σ V), (∀ x, σ x ^ p = x) →
      GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ V = ((𝟙 A) ^ p : A ⟶ A).left → ∀ y, m.pull y = 0 → ∃ z, frobDR p k hk A z = y := by
  intro p _ k _ _ hk A _ _ hA σ V m hσ hV y hy
  obtain ⟨e, he, -⟩ := GlobalTheory.deRhamVectorExtension p
  have hn : IsNilpotent (p : k) := ⟨1, by rw [pow_one, hk]⟩
  obtain ⟨g, hg⟩ : ∃ g, SmoothOfRelativeDimension g A.hom := GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA
  obtain ⟨G, t, -⟩ := GlobalTheory.AbelianTower.exists_pDivGroup_tower p k hn A g hA hg
  let A₁ := (Over.pullback (spMap (frobR p k hk))).obj A
  have hπ : IsGrpPullback A₁ A _ _ := isGrpPullback_pullback A (spMap (frobR p k hk))
  have hA₁ : IsAbelianScheme A₁ := isAbelianScheme_pullback_obj _ A hA
  obtain ⟨F, hFm, hF⟩ := GlobalTheory.T.exists_relativeFrobenius_grpScheme_charP p k hk A A₁ _ hπ
  obtain ⟨t₁, ht⟩ := exists_tower hk t hπ
  have mπ := grpMor_of_isGrpPullback hπ
  have hid : (frobR p k hk).comp σ = RingHom.id k := RingHom.ext fun x => (frobR_apply p k hk _).trans (hσ x)
  have hb : spMap (frobR p k hk) ≫ spMap σ = 𝟙 _ := by rw [← GlobalTheory.Cris.spMap_comp, hid, GlobalTheory.Cris.spMap_id]
  have mc := m.comp mπ
  let V₁ : A₁ ⟶ A := Over.homMk (_ ≫ V) (mc.w.trans (by rw [hb, Category.comp_id]))
  have hm : IsMonHom V₁ := isMonHom_of_mul _ fun T x x' => by
    have hw : (T.hom ≫ spMap (frobR p k hk) ≫ spMap σ) = T.hom := by rw [hb, Category.comp_id]
    let j : Over.mk (T.hom ≫ spMap (frobR p k hk) ≫ spMap σ) ⟶ T := Over.homMk (𝟙 _) (by simpa using hw.symm)
    have h := mc.mul T x x' (j ≫ x ≫ V₁) (j ≫ x' ≫ V₁) (by simp [j, V₁]) (by simp [j, V₁])
    rw [← MonObj.comp_mul] at h
    refine Over.OverMorphism.ext ?_
    simpa [j, V₁] using h.symm
  have hFV : F ≫ V₁ = 𝟙 A ^ p := Over.OverMorphism.ext (by
    change F.left ≫ _ ≫ V = _
    rw [← Category.assoc, hF, hV])
  have h0 : primPull (dp0 k) (𝟙 _) V₁ y = 0 := by
    have h1 := GrpMor.pull_pull m mπ (homMor (dp0 k) (𝟙 _) V₁) (fun r => RingHom.congr_fun hid r) rfl y
    rw [hy, map_zero] at h1
    exact h1.symm
  have h1 : rigExtMap (verschiebung hk G) (e hn hA t y) = 0 := by
    rw [← map_eq_verschiebung hk t t₁ ht F V₁ hF hFV, ← he.primPull hn hA₁ hA t₁ t, h0, map_zero]
  obtain ⟨-, -, -, -, -, h2, h3⟩ := rigExt_field_of_charP p k hk G
  have h4 : e hn hA t y ∈ Submodule.span k (Set.range (absFrob hk G).rig) := h3 ▸ h2 ▸ h1
  have h5 : ∀ z, e hn hA t (frobDR p k hk A z) = (absFrob hk G).rig (e hn hA t z) := fun z => by
    rw [(t.eq_semiOf_iff t (frobMor p k hk A (cast_left p k hk A)) (absFrob hk G)).2 (absFrob_y hk t)]
    exact he hn hn hA hA t t _ z
  have h6 : ∀ u ∈ Submodule.span k (Set.range (absFrob hk G).rig), ∃ z, e hn hA t (frobDR p k hk A z) = u := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨v, rfl⟩ := hu
      exact ⟨(e hn hA t).symm v, by rw [h5, LinearEquiv.apply_symm_apply]⟩
    | zero => exact ⟨0, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, rfl⟩ := hv
      exact ⟨a + b, by rw [map_add, map_add]⟩
    | smul l u _ hu =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨r, rfl⟩ := IsAlgClosed.exists_pow_nat_eq l (Fact.out : p.Prime).pos
      exact ⟨r • a, by rw [map_smulₛₗ, map_smul, frobR_apply]⟩
  obtain ⟨z, hz⟩ := h6 _ h4
  exact ⟨z, (e hn hA t).injective hz⟩
