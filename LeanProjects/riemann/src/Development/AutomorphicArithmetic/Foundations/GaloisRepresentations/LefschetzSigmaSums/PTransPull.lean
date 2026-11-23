import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit

open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (IsTrans TIso)

private theorem pt_ext {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G R} {N : ℕ}
    {S S₁ T : Scheme.{0}} {s : S ⟶ Sp R} {s₁ : S₁ ⟶ Sp R} {f : S₁ ⟶ S} {o : GObj b N s} {o₁ : GObj b N s₁}
    (m : GObjMap o₁ o f) {t : T ⟶ S₁} (x y : Over.mk t ⟶ o₁.A) (h : x.left ≫ m.φ = y.left ≫ m.φ) : x = y := by
  letI := o.grp
  letI := o₁.grp
  apply GlobalTheory.SiegelPull.push_injective m.cart (Over.mk t)
  exact Over.OverMorphism.ext h

theorem UpperTheory.Gal.LocalSmoothExtension.transPull_of :
    HomEx → PolPull → TatePull → TransPull := by
  intro hHom hPol hTate p _ D G L R _ _ b N N' S S₁ s s₁ f hfs o' o'' o₁' o₁'' m' m'' h ψ hT
  obtain ⟨hψ, hact, ⟨ψ', d, hψ', hact', hc1, hc2, hd⟩, hpolc, hgeo⟩ := hT
  obtain ⟨c, hcp, hpol, hrest⟩ := hpolc
  letI := o'.grp
  letI := o''.grp
  letI := o₁'.grp
  letI := o₁''.grp
  obtain ⟨hlift, huniq, hpow⟩ := hHom D.toG R b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m''
  obtain ⟨hlift', huniq', hpow'⟩ := hHom D.toG R b N' N S S₁ s s₁ f o'' o' o₁'' o₁' m'' m'
  have hu₁ := (hHom D.toG R b N' N' S S₁ s s₁ f o' o' o₁' o₁' m' m').2.1
  have hu₂ := (hHom D.toG R b N N S S₁ s s₁ f o'' o'' o₁'' o₁'' m'' m'').2.1
  obtain ⟨ψ₁, hψ₁, hcomm⟩ := hlift ψ hψ
  obtain ⟨ψ₁', hψ₁', hcomm'⟩ := hlift' ψ' hψ'
  refine ⟨ψ₁, hcomm, hψ₁, ?_, ⟨ψ₁', d, hψ₁', ?_, ?_, ?_, hd⟩,
    ⟨c, hcp, hPol D.toG R b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m'' ψ ψ₁ hcomm c hpol, hrest⟩, ?_⟩
  · intro e
    apply huniq
    simp only [Over.comp_left, Category.assoc, reassoc_of% hcomm, hcomm, reassoc_of% (m'.act e),
      m'.act e, m''.act e]
    rw [← Over.comp_left, ← Over.comp_left, hact e]
  · intro e
    apply huniq'
    simp only [Over.comp_left, Category.assoc, reassoc_of% hcomm', hcomm', reassoc_of% (m''.act e),
      m''.act e, m'.act e]
    rw [← Over.comp_left, ← Over.comp_left, hact' e]
  · apply hu₁
    simp only [Over.comp_left, Category.assoc, hcomm', reassoc_of% hcomm, hpow d, ← hc1]
  · apply hu₂
    simp only [Over.comp_left, Category.assoc, hcomm, reassoc_of% hcomm', hpow' d, ← hc2]
  · intro k _ _ t β ht
    have htf : (t ≫ f) ≫ s = spMap β := by rw [Category.assoc, hfs, ht]
    obtain ⟨I', I'', h1, h2, h3⟩ := hgeo k (t ≫ f) β htf
    obtain ⟨I₁', k₁⟩ := hTate p D R b N' S S₁ s s₁ f o' o₁' m' k t I'
    obtain ⟨I₁'', k₂⟩ := hTate p D R b N S S₁ s s₁ f o'' o₁'' m'' k t I''
    have hu : ∀ {X : Scheme} (g : Sp k ⟶ X), Over.Hom.left (toUnit (Over.mk g)) = g := by
      intro X g
      simpa using Over.w (toUnit (Over.mk g))
    refine ⟨I₁', I₁'', fun y => ?_, fun y => ?_, fun n hn hp x y => ?_⟩
    · apply pt_ext m'
      simp only [Over.comp_left, Category.assoc, m'.eta, k₁, ← h1, hu]
    · apply pt_ext m''
      simp only [Over.comp_left, Category.assoc, m''.eta, k₂, ← h2, hu]
    · refine Iff.trans ?_ (h3 n hn hp x y)
      have e : Over.Hom.left (I₁'.ev n x ≫ ψ₁) ≫ m''.φ = Over.Hom.left (I'.ev n x ≫ ψ) := by
        rw [Over.comp_left, Category.assoc, hcomm, ← Category.assoc, k₁ n x, Over.comp_left]
      constructor
      · intro hxy
        apply Over.OverMorphism.ext
        rw [← e, hxy]
        exact k₂ n y
      · intro hxy
        apply pt_ext m''
        rw [e, hxy]
        exact (k₂ n y).symm
