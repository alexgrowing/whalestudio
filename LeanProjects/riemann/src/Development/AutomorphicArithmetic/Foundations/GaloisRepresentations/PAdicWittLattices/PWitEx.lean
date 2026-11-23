import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLevelObjPullbackOfCharZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

open GlobalTheory.UPel.HT.Hecke in

private theorem gObjMap_comp_keep {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) :
    ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have e₁ : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have e₂ : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ => h₂.φ₂) (fun _ => 1) h₁.φ₂) e₁
  refine ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, ?_, ?_,
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol e₂, ?_⟩, rfl⟩
  · exact ⟨by simp only [Category.assoc, h₂.sq.1, reassoc_of% h₁.sq.1],
      by simp only [Category.assoc, h₂.sq.2, reassoc_of% h₁.sq.2]⟩
  · intro c
    simp only [← Category.assoc, h₁.act c]
    simp only [Category.assoc, h₂.act c]
  · intro y
    simp only [reassoc_of% h₁.eta y, h₂.eta y, Category.assoc]

theorem UpperTheory.Gal.G3.pWitEx :
    KNBasic → GenSm → Rigid → WitForget → WitDeep → DescMap → TransIso → TransCancel → TransDesc → WitEx := by
  intro _ hSm hRig hWF hWD hDM hTI hTC hTD p _ D G L R _ _ gb X N' N h hI hA
  obtain ⟨M, hdiv, hAM, π₁, Φ₁, hs₁, o₁, ψ₁, φ₁, ht₁, hΦ₁⟩ := hWD p D G L R gb X N' N h hI
  obtain ⟨c, Φc, hw, hfin, het, hsur⟩ := hWF p D G L R gb N' M hdiv (X N') (X M)
  have hA1 : AdmK L (↑M) (↑N') 1 := by
    intro u hu
    simpa using UpperTheory.Gal.Int.Geo.KN_anti hdiv hu
  obtain ⟨π, Φ, hcπ, hΦ, hπs, hΦw⟩ :=
    hDM p D G L R gb M N' N (X M) (X N') (X N) h hI hA hA1 c Φc π₁ Φ₁ hw hfin het hsur
      ⟨hs₁, o₁, ψ₁, φ₁, ht₁, hΦ₁⟩
  subst hcπ
  obtain ⟨hsc, oc, ψc, φc, htc, hΦc⟩ := hw
  obtain ⟨o, ⟨φ⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (X N').s π hπs (X N).univ
  let ψl : (X N').univ.A.left ⟶ o.A.left :=
    φ.cart.1.lift Φ (X N').univ.A.hom hΦw
  have hψ₁ : ψl ≫ φ.φ = Φ := φ.cart.1.lift_fst _ _ _
  have hψ₂ : ψl ≫ o.A.hom = (X N').univ.A.hom := φ.cart.1.lift_snd _ _ _
  let ψ : (X N').univ.A ⟶ o.A := Over.homMk ψl hψ₂
  refine ⟨π, Φ, hπs, o, ψ, φ, ?_, hψ₁.symm⟩
  obtain ⟨m₂⟩ := BaseChange.gObjMap_cancel φ₁ φ
  haveI := hTI p D G L R gb (X M).X (X M).s M N' (X M).univ oc ψc 1 (one_mem _) htc
  have htr : IsTrans L h oc o₁ (inv ψc ≫ ψ₁) :=
    hTC p D G L R gb (X M).X (X M).s M N' N (X M).univ oc o₁ ψc (inv ψc ≫ ψ₁) h hI hAM htc
      (by simpa using ht₁)
  haveI : Smooth (X M).s := (hSm p D R gb M (X M)).1
  haveI : AlgebraicGeometry.IsReduced (X M).X := GlobalTheory.isReduced_of_smooth_of_isReduced (X M).s
  have hcomp : m₂.φ ≫ φ.φ = φ₁.φ := by
    obtain ⟨m, hm⟩ := gObjMap_comp_keep m₂ φ
    rw [← hm]
    exact hRig p D R gb (X N).X (X M).X (X N).s (X M).s (c ≫ π)
      (by rw [Category.assoc, hπs, hsc]) N (X N).univ o₁ m φ₁
  refine hTD p D G L R gb (X N').X (X M).X (X N').s (X M).s c hsc N' N (X N').univ o oc o₁ φc m₂ ψ
    (inv ψc ≫ ψ₁) h ?_ htr
  have key : ψc.left ≫ φc.φ ≫ Φ = ψ₁.left ≫ φ₁.φ := by
    rw [← Category.assoc, ← hΦc, hΦ, hΦ₁]
  apply φ.cart.1.hom_ext
  · simp only [Category.assoc, hcomp, ψ, Over.homMk_left, hψ₁, Over.comp_left]
    rw [← key, ← Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left, Category.id_comp]
  · simp only [Category.assoc, ψ, Over.homMk_left, hψ₂, Over.comp_left]
    rw [m₂.cart.1.w, φc.cart.1.w, ← Over.comp_left_assoc, Over.w_assoc]
