import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransUniqPt :
    MultBasic → IsogFEt → TransKer → QuotUniq → PolUniq → MapOfIso → TransUniqPt := by
  intro hMB hFE hTK hQU hPU hMI p _ D G L R _ _ gb k _ _ s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm tr₁ tr₂
  have hK := hTK p D G L R gb (Sp k) s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm tr₁ tr₂
  obtain ⟨mon₁, -, ⟨ψ₁', d₁, mon₁', -, e₁, e₁', cop₁⟩, ⟨c₁, hc₁, ⟨lb₁⟩, t₁, t₁', i₁, i₁', tt₁, hm₁⟩, -⟩ := id tr₁
  obtain ⟨mon₂, -, ⟨ψ₂', d₂, mon₂', -, e₂, e₂', cop₂⟩, ⟨c₂, hc₂, ⟨lb₂⟩, t₂, t₂', i₂, i₂', tt₂, hm₂⟩, -⟩ := id tr₂
  have dpos : ∀ d : ℕ, d.Coprime p → 0 < d := fun d hd => Nat.pos_of_ne_zero fun h0 => by
    subst h0
    exact (Fact.out : p.Prime).one_lt.ne' (by simpa using hd)
  obtain ⟨f₁, et₁, sj₁⟩ := hFE R (Sp k) s o.A o₁.A o.ab o₁.ab ψ₁ ψ₁' d₁ (dpos _ cop₁) mon₁ mon₁' e₁ e₁'
  obtain ⟨f₂, et₂, sj₂⟩ := hFE R (Sp k) s o.A o₂.A o.ab o₂.ab ψ₂ ψ₂' d₂ (dpos _ cop₂) mon₂ mon₂' e₂ e₂'
  obtain ⟨θ, isoθ, monθ, hθ⟩ := hQU k o.A o₁.A o₂.A o.ab o₁.ab o₂.ab ψ₁ ψ₂ mon₁ mon₂ f₁ et₁ sj₁ f₂ et₂ sj₂
    (fun Ω _ _ t a => (hK Ω t).1 a)
  have lin₁ := tr₁.2.1
  have lin₂ := tr₂.2.1
  haveI := f₁
  haveI := et₁
  haveI := sj₁
  haveI : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have cancel : ∀ {X : Over (Sp k)} (a b : o₁.A ⟶ X), ψ₁ ≫ a = ψ₁ ≫ b → a = b := fun a b e =>
    Over.OverMorphism.ext ((cancel_epi ψ₁.left).1 (by simpa using congrArg (·.left) e))
  have lin : ∀ c, o₁.act.act c ≫ θ = θ ≫ o₂.act.act c := fun c => cancel _ _ (by
    rw [← Category.assoc, ← lin₁ c, Category.assoc, hθ, lin₂ c, ← hθ, Category.assoc])
  have hcc : c₁ = c₂ := (hMB p).1 (mul h) c₁ c₂ hc₁ hc₂ ⟨t₁, t₁', i₁, i₁', tt₁, hm₁⟩ ⟨t₂, t₂', i₂, i₂', tt₂, hm₂⟩
  subst hcc
  have hPo := o.isLB
  have hP1 := o₁.isLB
  have hP2 := o₂.isLB
  have hQ : (o₂.P.pull (Hecke.sq2 θ)).IsLB := pull_isLB hP2 _
  have sqc : Hecke.sq2 ψ₁ ≫ Hecke.sq2 θ = Hecke.sq2 ψ₂ := by
    rw [← hθ]
    simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc]
  have key : LBIso (o₁.P.pull (Hecke.sq2 ψ₁)) ((o₂.P.pull (Hecke.sq2 θ)).pull (Hecke.sq2 ψ₁)) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP1 _) (pull_isLB hQ _)).1 ?_
    have a1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hPo _ _) (pull_isLB hP1 _)).2 lb₁
    have a2 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hPo _ _) (pull_isLB hP2 _)).2 lb₂
    rw [← a1, a2, GlobalTheory.CechPic.cls_pull hP2, GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2,
      ← GlobalTheory.CechPic.pull_comp, sqc]
  have r₁ : ∃ t : ((o₂.P.pull (Hecke.sq2 θ)).pull (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left).Gen, t.IsGen := by
    refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ _)).1 ?_
    have e : (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left ≫ Hecke.sq2 θ =
        θ.left ≫ (lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)).left := by
      simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
        Category.comp_id, one_comp, comp_one]
    rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hP2 _ (pull_isLB hP2 _), (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _)).2 o₂.rig₁, map_zero]
  have r₂ : ∃ t : ((o₂.P.pull (Hecke.sq2 θ)).pull (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left).Gen, t.IsGen := by
    refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ _)).1 ?_
    have e : (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left ≫ Hecke.sq2 θ =
        θ.left ≫ (lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A)).left := by
      simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
        Category.comp_id, one_comp, comp_one]
    rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hP2 _ (pull_isLB hP2 _), (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _)).2 o₂.rig₂, map_zero]
  have pol : LBIso o₁.P (o₂.P.pull (Hecke.sq2 θ)) :=
    hPU (Sp k) o.A o₁.A o.ab o₁.ab ψ₁ mon₁ f₁ et₁ sj₁ o₁.P _ hP1 hQ o₁.rig₁ o₁.rig₂ r₁ r₂ key
  have lev : ∀ y, o₁.eta y ≫ θ = o₂.eta y := by
    intro y
    obtain ⟨v, hv⟩ := sj₁.surj (UpperTheory.Gal.TranscendenceTraces.pt (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y).left)
    obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds ψ₁.left k (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y).left v hv
    let a : Over.mk (𝟙 (Sp k)) ⟶ o.A := Over.homMk z (by
      have w1 := Over.w ψ₁
      have w2 := Over.w (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y)
      simp only [Over.mk_hom] at w2 ⊢
      rw [← w1, ← Category.assoc, hz, w2])
    have ha : a ≫ ψ₁ = toUnit _ ≫ o₁.eta y := Over.OverMorphism.ext hz
    have hb := ((hK k (𝟙 _)).2 a y).1 ha
    have e : toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y ≫ θ = toUnit (Over.mk (𝟙 (Sp k))) ≫ o₂.eta y := by
      rw [← Category.assoc, ← ha, Category.assoc, hθ, hb]
    let i : 𝟙_ (Over (Sp k)) ⟶ Over.mk (𝟙 (Sp k)) := Over.mkIdTerminal.from _
    have hi : i ≫ toUnit (Over.mk (𝟙 (Sp k))) = 𝟙 _ := toUnit_unique _ _
    have e' := congrArg (i ≫ ·) e
    simpa [← Category.assoc, hi] using e'
  obtain ⟨m, hm⟩ := hMI D.toG R gb (Sp k) s N.1 o₁ o₂ θ isoθ monθ lin pol lev
  exact ⟨m, by rw [hm, ← hθ, Over.comp_left]⟩
