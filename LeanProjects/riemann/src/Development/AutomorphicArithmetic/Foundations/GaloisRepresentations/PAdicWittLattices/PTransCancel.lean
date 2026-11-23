import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem square_map_comp {S : Scheme.{0}} {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [GrpObj C] [IsCommMonObj C] (f : A ⟶ B) (g : B ⟶ C) :
    Hecke.sq2 f ≫ Hecke.sq2 g = Hecke.sq2 (f ≫ g) := by
  unfold Hecke.sq2
  rw [← Over.comp_left]
  congr 1
  ext <;> simp

private theorem square_map_id {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] :
    Hecke.sq2 (𝟙 A) = 𝟙 _ := by
  simp [Hecke.sq2]

private theorem cls_pow' {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) (n : ℕ) (h : (Hecke.lbPow P n).IsLB) :
    GlobalTheory.CechPic.cls (Hecke.lbPow P n) h = n • GlobalTheory.CechPic.cls P hP := by
  unfold Hecke.lbPow at h ⊢
  rw [GlobalTheory.CechPic.cls_linComb hP]
  simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

private theorem bundle_cancel {S : Scheme.{0}} {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [GrpObj C] [IsCommMonObj C] (θ : A ⟶ B) [IsIso θ] (χ : B ⟶ C) (P : LB (G2 A).left) (Q : LB (G2 B).left)
    (T : LB (G2 C).left) (hP : P.IsLB) (hQ : Q.IsLB) (hT : T.IsLB) (c : ℕ)
    (h₁ : LBIso (Hecke.lbPow P 1) (Q.pull (Hecke.sq2 θ)))
    (h₂ : LBIso (Hecke.lbPow P c) (T.pull (Hecke.sq2 (θ ≫ χ)))) :
    LBIso (Hecke.lbPow Q c) (T.pull (Hecke.sq2 χ)) := by
  have hQθ := pull_isLB hQ (Hecke.sq2 θ)
  have hTχ := pull_isLB hT (Hecke.sq2 χ)
  have hTθχ := pull_isLB hT (Hecke.sq2 (θ ≫ χ))
  have hP1 : (Hecke.lbPow P 1).IsLB := LB.isLB_linComb hP _ _
  have hPc : (Hecke.lbPow P c).IsLB := LB.isLB_linComb hP _ _
  have hQc : (Hecke.lbPow Q c).IsLB := LB.isLB_linComb hQ _ _
  rw [← GlobalTheory.CechPic.cls_eq_iff hP1 hQθ, cls_pow' hP, GlobalTheory.CechPic.cls_pull hQ] at h₁
  rw [← GlobalTheory.CechPic.cls_eq_iff hPc hTθχ, cls_pow' hP, GlobalTheory.CechPic.cls_pull hT] at h₂
  rw [← GlobalTheory.CechPic.cls_eq_iff hQc hTχ, cls_pow' hQ, GlobalTheory.CechPic.cls_pull hT]
  have key : ∀ x, GlobalTheory.CechPic.pull (Hecke.sq2 (inv θ)) (GlobalTheory.CechPic.pull (Hecke.sq2 θ) x) = x := by
    intro x
    rw [← GlobalTheory.CechPic.pull_comp, square_map_comp, IsIso.inv_hom_id, square_map_id, GlobalTheory.CechPic.pull_id]
  rw [← key (c • _), ← key (GlobalTheory.CechPic.pull (Hecke.sq2 χ) _), map_nsmul, ← h₁, one_smul, h₂,
    ← square_map_comp, GlobalTheory.CechPic.pull_comp]

theorem UpperTheory.Gal.G3.pTransCancel :
    MultBasic → RelComp → TateDiff → TateTwist → TransIso → TransCancel := by
  intro hMB hRC hTD hTT hTI p _ D G L R _ _ gb S s M N' N o o₁ o₂ θ χ h hint hadm hθ hθχ
  have hθiso : IsIso θ := hTI p D G L R gb S s M N' o o₁ θ 1 (one_mem _) hθ
  obtain ⟨hθm, hθa, ⟨θ', d₁, hθ'm, hθ'a, hθθ', hθ'θ, hd₁⟩, ⟨c₁, hc₁, ⟨hPθ⟩, t₁, t₁', ht₁, ht₁', htt₁, hc₁e⟩, hθpt⟩ := hθ
  obtain ⟨hχm₀, hχa₀, ⟨ω, d, hωm, hωa, hχω, hωχ, hd⟩, ⟨c, hc, ⟨hPχ⟩, t, t', ht, ht', htt, hce⟩, hχpt⟩ := hθχ
  have hinvm : IsMonHom (inv θ) := by
    constructor
    · rw [← cancel_mono θ]
      simp
    · rw [← cancel_mono θ]
      simp [IsMonHom.mul_hom]
  have hχm : IsMonHom χ := by
    have e : χ = inv θ ≫ (θ ≫ χ) := by simp
    rw [e]
    infer_instance
  have hc1 : c₁ = 1 :=
    (hMB p).1 _ c₁ 1 hc₁ (Nat.coprime_one_left p) ⟨t₁, t₁', ht₁, ht₁', htt₁, hc₁e⟩
      ((hMB p).2.2 D G L 1 (one_mem _))
  subst hc1
  refine ⟨hχm, ?_, ⟨ω ≫ θ, d, inferInstance, ?_, ?_, ?_, hd⟩,
    ⟨c, hc, ⟨bundle_cancel θ χ o.P o₁.P o₂.P o.isLB o₁.isLB o₂.isLB c hPθ hPχ⟩, t, t', ht, ht', htt, hce⟩, ?_⟩
  · intro e
    rw [← cancel_epi θ, ← Category.assoc, ← hθa e, Category.assoc, hχa₀ e, Category.assoc]
  · intro e
    rw [← Category.assoc, hωa e, Category.assoc, hθa e, Category.assoc]
  · rw [← cancel_epi θ]
    simp only [← Category.assoc]
    rw [hχω, MonObj.pow_comp, MonObj.comp_pow]
    simp
  · rw [Category.assoc]
    exact hωχ
  · intro k _ _ tt β htβ
    obtain ⟨I, I₁, hI, hI₁, hr₁⟩ := hθpt k tt β htβ
    obtain ⟨J, J₂, hJ, hJ₂, hr₂⟩ := hχpt k tt β htβ
    obtain ⟨u, hu, hIJ⟩ := hTD p D G L R gb S s M o k tt I J hI hJ
    obtain ⟨J', hJ', hJJ'⟩ := hTT p D G L R gb S s N o₂ k tt J₂ hJ₂ (h * u⁻¹ * h⁻¹) (hadm _ (inv_mem hu))
    have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
    have hu'1 : h * u⁻¹ * h⁻¹ ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) (hadm _ (inv_mem hu))
    have r0 : UpperTheory.Gal.G3.Rel L I₁ I (inv θ) 1 := by
      intro n hn hnp x y
      have e : I₁.ev n x ≫ inv θ = I.ev n y ↔ I.ev n y ≫ θ = I₁.ev n x := by
        constructor
        · intro e
          rw [← e]
          simp
        · intro e
          rw [← e]
          simp
      rw [e, hr₁ n hn hnp y x]
      simp only [map_one, Module.End.one_apply]
      constructor
      · rintro ⟨v, hv, e⟩
        exact ⟨-v, neg_mem hv, by rw [e]; simp⟩
      · rintro ⟨v, hv, e⟩
        exact ⟨-v, neg_mem hv, by rw [e]; simp⟩
    have r1 := (hRC p D G L R gb S s N' M M o₁ o o k tt I₁ I J (inv θ) (𝟙 o.A) 1 u inferInstance
      inferInstance (UpperTheory.Gal.Int.Geo.integ_of_mem hu1)).2 r0 hIJ
    have r2 := (hRC p D G L R gb S s N' M N o₁ o o₂ k tt I₁ J J₂ (inv θ ≫ 𝟙 o.A) (θ ≫ χ) (u * 1) h
      inferInstance inferInstance hint).2 r1 hr₂
    have r3 := (hRC p D G L R gb S s N' N N o₁ o₂ o₂ k tt I₁ J₂ J' ((inv θ ≫ 𝟙 o.A) ≫ (θ ≫ χ))
      (𝟙 o₂.A) (h * (u * 1)) (h * u⁻¹ * h⁻¹) inferInstance inferInstance
      (UpperTheory.Gal.Int.Geo.integ_of_mem hu'1)).2 r2 hJJ'
    have e1 : ((inv θ ≫ 𝟙 o.A) ≫ (θ ≫ χ)) ≫ 𝟙 o₂.A = χ := by simp
    have e2 : h * u⁻¹ * h⁻¹ * (h * (u * 1)) = h := by group
    rw [e1, e2] at r3
    exact ⟨I₁, J', hI₁, hJ', r3⟩
