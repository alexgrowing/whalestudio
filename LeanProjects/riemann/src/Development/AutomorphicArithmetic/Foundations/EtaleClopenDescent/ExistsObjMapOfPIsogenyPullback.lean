import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfPullbackQuasiInverseIsogenyTrivialAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTrivialityOfNoetherianDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem UpperTheory.Cb.exists_objMap_of_p_isogeny_pullback :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ o₁' : Obj b N s₁) (o o' : Obj b N s) (m : ObjMap o₁ o t) (ψ₁ : o₁.A ⟶ o₁'.A) (ψ : o.A ⟶ o'.A) (θ : o₁'.A.left ⟶ o'.A.left), IsUnit ((p : ℕ) : R) → IsPIsog c o₁ o₁' ψ₁ → IsPIsog c o o' ψ → IsGrpPullback o₁'.A o'.A t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → ∃ m' : ObjMap o₁' o' t, m'.φ = θ := by
  intro p _ D R _ b N c T Y s₁ s t o₁ o₁' o o' m ψ₁ ψ θ hp hψ₁ hψ hcart hmc
  obtain ⟨θ₂, hθ₂1, hθ₂2⟩ : ∃ θ₂ : (G2 o₁'.A).left ⟶ (G2 o'.A).left,
      θ₂ ≫ (fst o'.A o'.A).left = (fst o₁'.A o₁'.A).left ≫ θ ∧
      θ₂ ≫ (snd o'.A o'.A).left = (snd o₁'.A o₁'.A).left ≫ θ := by
    refine ⟨Limits.pullback.lift (Limits.pullback.fst _ _ ≫ θ) (Limits.pullback.snd _ _ ≫ θ) ?_,
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
    rw [Category.assoc, Category.assoc, hcart.1.w, ← Category.assoc, ← Category.assoc,
      Limits.pullback.condition]
  have ext2 : ∀ {Z : Scheme} (f g : Z ⟶ (G2 o'.A).left),
      f ≫ (fst o'.A o'.A).left = g ≫ (fst o'.A o'.A).left →
      f ≫ (snd o'.A o'.A).left = g ≫ (snd o'.A o'.A).left → f = g :=
    fun f g h1 h2 => Limits.pullback.hom_ext h1 h2
  obtain ⟨ψ₁', hq⟩ := hψ₁.exists_quasiInv
  have hc : 0 < c := hψ₁.pos
  haveI := (SiegUniqBase.flat_surjective_qc_pow T o₁'.A o₁'.ab c hc).1
  haveI := (SiegUniqBase.flat_surjective_qc_pow T o₁'.A o₁'.ab c hc).2.1
  have hepi : Epi (Over.Hom.left (𝟙 o₁'.A ^ c)) := Flat.epi_of_flat_of_surjective _
  have he : Over.Hom.left (𝟙 o₁'.A ^ c) = ψ₁'.left ≫ ψ₁.left := by
    rw [← hq.2.2.2, Over.comp_left]
  have hone : (1 : o₁'.A ⟶ o₁'.A).left ≫ θ = θ ≫ (1 : o'.A ⟶ o'.A).left := by
    have h := GlobalTheory.LocTrivDescent.one_left_comp hcart
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left, Hom.one_def, Over.comp_left, Over.toUnit_left] at h
    rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left]
    rw [Category.assoc, ← Category.assoc θ, hcart.1.w, Category.assoc]
    congr 1
  have hs2 : ∀ {S : Scheme} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
      (f : A ⟶ A'), sq2 f ≫ (fst A' A').left = (fst A A).left ≫ f.left ∧
        sq2 f ≫ (snd A' A').left = (snd A A).left ≫ f.left := by
    intro S A A' _ _ _ _ f
    constructor <;> (rw [sq2, ← Over.comp_left]; simp)
  have hsq : sq2 ψ₁ ≫ θ₂ = m.φ₂ ≫ sq2 ψ := by
    apply ext2
    · simp only [Category.assoc]
      rw [hθ₂1, (hs2 ψ).1, ← Category.assoc (sq2 ψ₁), (hs2 ψ₁).1, ← Category.assoc m.φ₂, m.sq.1]
      simp only [Category.assoc, hmc]
    · simp only [Category.assoc]
      rw [hθ₂2, (hs2 ψ).2, ← Category.assoc (sq2 ψ₁), (hs2 ψ₁).2, ← Category.assoc m.φ₂, m.sq.2]
      simp only [Category.assoc, hmc]
  have hQ : (o'.P.pull θ₂).IsLB := pull_isLB o'.isLB θ₂
  have hcu : IsUnit ((c : ℕ) : Γ(T, ⊤)) := by
    obtain ⟨kk, rfl⟩ := hψ₁.exists_eq_pow
    rw [Nat.cast_pow]
    refine IsUnit.pow _ ?_
    have := hp.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s₁.appTop).hom
    simpa using this
  have hone2 : (lift 1 (𝟙 o₁'.A)).left ≫ θ₂ = θ ≫ (lift 1 (𝟙 o'.A)).left := by
    apply ext2
    · rw [Category.assoc, hθ₂1, ← Category.assoc, ← Over.comp_left, lift_fst, hone, Category.assoc, ← Over.comp_left, lift_fst]
    · rw [Category.assoc, hθ₂2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp, Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id]
  have hone3 : (lift (𝟙 o₁'.A) 1).left ≫ θ₂ = θ ≫ (lift (𝟙 o'.A) 1).left := by
    apply ext2
    · rw [Category.assoc, hθ₂1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp, Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
    · rw [Category.assoc, hθ₂2, ← Category.assoc, ← Over.comp_left, lift_snd, hone, Category.assoc, ← Over.comp_left, lift_snd]
  have r1 : ∃ t : ((o'.P.pull θ₂).pull (lift 1 (𝟙 o₁'.A)).left).Gen, t.IsGen := by
    rw [GlobalTheory.LocTrivDescent.triv_iff hQ, GlobalTheory.CechPic.cls_pull o'.isLB θ₂ hQ, ← GlobalTheory.CechPic.pull_comp,
      hone2, GlobalTheory.CechPic.pull_comp, (GlobalTheory.LocTrivDescent.triv_iff o'.isLB _).1 o'.rig₁, map_zero]
  have r2 : ∃ t : ((o'.P.pull θ₂).pull (lift (𝟙 o₁'.A) 1).left).Gen, t.IsGen := by
    rw [GlobalTheory.LocTrivDescent.triv_iff hQ, GlobalTheory.CechPic.cls_pull o'.isLB θ₂ hQ, ← GlobalTheory.CechPic.pull_comp,
      hone3, GlobalTheory.CechPic.pull_comp, (GlobalTheory.LocTrivDescent.triv_iff o'.isLB _).1 o'.rig₂, map_zero]
  have hiso : LBIso (o₁'.P.pull (sq2 ψ₁)) ((o'.P.pull θ₂).pull (sq2 ψ₁)) := by
    rw [← GlobalTheory.CechPic.cls_eq_iff (pull_isLB o₁'.isLB _) (pull_isLB hQ _)]
    obtain ⟨hI⟩ := hψ₁.2.2.2.2.1
    obtain ⟨hI'⟩ := hψ.2.2.2.2.1
    have e1 : c • GlobalTheory.CechPic.cls o₁.P o₁.isLB =
        GlobalTheory.CechPic.cls (o₁'.P.pull (sq2 ψ₁)) (pull_isLB o₁'.isLB _) := by
      rw [← GlobalTheory.LocTrivDescent.cls_lbPow_eq o₁.isLB c (LB.isLB_linComb o₁.isLB _ _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 hI
    have e2 : c • GlobalTheory.CechPic.cls o.P o.isLB =
        GlobalTheory.CechPic.cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB _) := by
      rw [← GlobalTheory.LocTrivDescent.cls_lbPow_eq o.isLB c (LB.isLB_linComb o.isLB _ _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 hI'
    have e3 := (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol
    rw [← e1, GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull o'.isLB, ← GlobalTheory.CechPic.pull_comp, hsq,
      GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _), ← e2,
      map_nsmul, ← GlobalTheory.CechPic.cls_pull o.isLB _ (pull_isLB o.isLB _), ← e3]
  refine ⟨⟨θ, θ₂, hcart, ⟨hθ₂1, hθ₂2⟩, ?_, ?_, ?_⟩, rfl⟩
  · intro c'
    rw [← cancel_epi (Over.Hom.left (𝟙 o₁'.A ^ c)), he]
    have h1 := congrArg Over.Hom.left (hψ₁.2.2.1 c')
    have h2 := congrArg Over.Hom.left (hψ.2.2.1 c')
    simp only [Over.comp_left] at h1 h2
    simp only [Category.assoc]
    rw [← reassoc_of% h1, ← hmc, reassoc_of% (m.act c'), h2, reassoc_of% hmc]
  · exact GlobalTheory.QuasiInvPull.lbIso_of_pullback_quasiInverseIsogeny_trivial_axes T o₁.A o₁'.A c ψ₁ ψ₁' o₁'.P (o'.P.pull θ₂) o₁'.ab hc hcu
      hq (isAxesTriv_obj o₁') ⟨hQ, r1, r2⟩ hiso
  · intro y
    rw [hψ₁.2.2.2.1 y, Over.comp_left, Category.assoc, ← hmc, ← Category.assoc, m.eta y,
      Category.assoc, ← Over.comp_left, ← hψ.2.2.2.1 y]
