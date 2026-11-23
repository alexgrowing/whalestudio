import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransComp :
    MultBasic → RelComp → TateDiff → TateTwist → TransComp := by
  intro hMB hRC hTD hTT p _ D G L R _ _ gb S s N₁ N₂ N₃ o₁ o₂ o₃ ψ₁ ψ₂ h₁ h₂ hI hA t1 t2
  obtain ⟨m1, a1, ⟨ψ₁', d₁, m1', a1', e1, e1', cp1⟩, ⟨c₁, cc1, ⟨iso1⟩, hm1⟩, g1⟩ := t1
  obtain ⟨m2, a2, ⟨ψ₂', d₂, m2', a2', e2, e2', cp2⟩, ⟨c₂, cc2, ⟨iso2⟩, hm2⟩, g2⟩ := t2
  haveI := m1
  haveI := m2
  haveI := m1'
  haveI := m2'
  refine ⟨inferInstance, ?_, ⟨ψ₂' ≫ ψ₁', d₁ * d₂, inferInstance, ?_, ?_, ?_, Nat.Coprime.mul cp1 cp2⟩,
    ⟨c₂ * c₁, Nat.Coprime.mul cc2 cc1, ⟨?_⟩, ?_⟩, ?_⟩
  · intro c
    rw [← Category.assoc, a1 c, Category.assoc, a2 c, Category.assoc]
  · intro c
    rw [← Category.assoc, a2' c, Category.assoc, a1' c, Category.assoc]
  · rw [Category.assoc, ← Category.assoc ψ₂, e2, MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, e1, pow_mul]
  · rw [Category.assoc, ← Category.assoc ψ₁', e1', MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, e2', mul_comm, pow_mul]
  · have hlb : (Hecke.lbPow o₁.P (c₂ * c₁)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hpl : (o₃.P.pull (Hecke.sq2 (ψ₁ ≫ ψ₂))).IsLB := pull_isLB o₃.isLB _
    have hl1 : (Hecke.lbPow o₁.P c₁).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hl2 : (Hecke.lbPow o₂.P c₂).IsLB := LB.isLB_linComb o₂.isLB _ _
    have k1 := (GlobalTheory.CechPic.cls_eq_iff hl1 (pull_isLB o₂.isLB (Hecke.sq2 ψ₁))).2 iso1
    have k2 := (GlobalTheory.CechPic.cls_eq_iff hl2 (pull_isLB o₃.isLB (Hecke.sq2 ψ₂))).2 iso2
    rw [Hecke.Comp.cls_lbPow' o₁.isLB, GlobalTheory.CechPic.cls_pull o₂.isLB] at k1
    rw [Hecke.Comp.cls_lbPow' o₂.isLB, GlobalTheory.CechPic.cls_pull o₃.isLB] at k2
    apply (GlobalTheory.CechPic.cls_eq_iff hlb hpl).1
    rw [Hecke.Comp.cls_lbPow' o₁.isLB, GlobalTheory.CechPic.cls_pull o₃.isLB, Hecke.Comp.grpSchemeSquareProductMap_comp,
      GlobalTheory.CechPic.pull_comp, ← k2, map_nsmul, ← k1, smul_smul]
  · exact (hMB p).2.1 _ _ _ _ hm2 hm1
  · intro k _ _ t β hts
    obtain ⟨I1', I1'', ind1', ind1'', rel1⟩ := g1 k t β hts
    obtain ⟨I2', I2'', ind2', ind2'', rel2⟩ := g2 k t β hts
    obtain ⟨u, hu, ru⟩ := hTD p D G L R gb S s N₂ o₂ k t I1'' I2' ind1'' ind2'
    have hint : ∀ {M : ℕ} {g : G.GAf}, g ∈ L.KN M → Integ L g := fun hg =>
      UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hg)
    have rA := (hRC p D G L R gb S s N₁ N₂ N₂ o₁ o₂ o₂ k t I1' I1'' I2' ψ₁ (𝟙 _) h₁ u
      inferInstance inferInstance (hint hu)).2 rel1 ru
    have rB := (hRC p D G L R gb S s N₁ N₂ N₃ o₁ o₂ o₃ k t I1' I2' I2'' (ψ₁ ≫ 𝟙 _) ψ₂ (u * h₁) h₂
      inferInstance inferInstance hI).2 rA rel2
    have hu' : (h₂ * u * h₂⁻¹)⁻¹ ∈ L.KN N₃ := inv_mem (hA u hu)
    obtain ⟨J, indJ, rJ⟩ := hTT p D G L R gb S s N₃ o₃ k t I2'' ind2'' _ hu'
    have rC := (hRC p D G L R gb S s N₁ N₃ N₃ o₁ o₃ o₃ k t I1' I2'' J ((ψ₁ ≫ 𝟙 _) ≫ ψ₂) (𝟙 _)
      (h₂ * (u * h₁)) _ inferInstance inferInstance (hint hu')).2 rB rJ
    have hg : (h₂ * u * h₂⁻¹)⁻¹ * (h₂ * (u * h₁)) = h₂ * h₁ := by group
    rw [hg] at rC
    simp only [Category.comp_id] at rC
    exact ⟨I1', J, ind1', indJ, rC⟩
