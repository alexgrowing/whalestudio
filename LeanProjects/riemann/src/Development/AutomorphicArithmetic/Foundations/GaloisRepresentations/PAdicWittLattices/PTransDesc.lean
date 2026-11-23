import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem epi_of_isGrpPullback_etale_surjective {S S' : Scheme} (c : S' ⟶ S) [Etale c] [Surjective c] (A : Over S)
    (A' : Over S') [GrpObj A] [GrpObj A'] (a : A'.left ⟶ A.left) (ha : IsGrpPullback A' A c a) : Epi a := by
  haveI : Etale a := MorphismProperty.of_isPullback (P := @Etale) ha.1.flip ‹Etale c›
  haveI : Surjective a := MorphismProperty.of_isPullback (P := @Surjective) ha.1.flip ‹Surjective c›
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective a

private theorem comp_eq_comp_of_over_left_comm {S S' : Scheme} {A B : Over S} {A' B' : Over S'}
    (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left) [Epi a] (u : A ⟶ A) (v : B ⟶ B) (u' : A' ⟶ A')
    (v' : B' ⟶ B') (f : A ⟶ B) (f' : A' ⟶ B')
    (hf : Over.Hom.left f' ≫ b = a ≫ Over.Hom.left f)
    (hu : Over.Hom.left u' ≫ a = a ≫ Over.Hom.left u)
    (hv : Over.Hom.left v' ≫ b = b ≫ Over.Hom.left v) (h' : u' ≫ f' = f' ≫ v') : u ≫ f = f ≫ v := by
  apply Over.OverMorphism.ext
  rw [← cancel_epi a]
  have e3 : Over.Hom.left u' ≫ Over.Hom.left f' = Over.Hom.left f' ≫ Over.Hom.left v' := by
    rw [← Over.comp_left, h', Over.comp_left]
  simp only [Over.comp_left]
  calc a ≫ Over.Hom.left u ≫ Over.Hom.left f
        = Over.Hom.left u' ≫ Over.Hom.left f' ≫ b := by rw [← reassoc_of% hu, ← hf]
    _ = Over.Hom.left f' ≫ Over.Hom.left v' ≫ b := by rw [reassoc_of% e3]
    _ = a ≫ Over.Hom.left f ≫ Over.Hom.left v := by rw [hv, reassoc_of% hf]

theorem UpperTheory.Gal.G3.pTransDesc :
    IsogFEt → TatePull → HomDesc → PolDesc → TransDesc := by
  intro hIsog hTate hHom hPol p _ D G L R _ _ gb S S' _ s s' c _ _ _ hcs N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' h hsq hT
  obtain ⟨hmon', hact', ⟨χ', d, hχmon', hχact', hd1', hd2', hdp⟩, ⟨e, hep, hpol', hint⟩, hgeo'⟩ := hT
  haveI : Epi m₁.φ := epi_of_isGrpPullback_etale_surjective c o₁.A o₁'.A m₁.φ m₁.cart
  haveI : Epi m₂.φ := epi_of_isGrpPullback_etale_surjective c o₂.A o₂'.A m₂.φ m₂.cart
  have hH := hHom S S' c o₁.A o₂.A o₁'.A o₂'.A o₁.ab o₂.ab o₂'.ab m₁.φ m₂.φ m₁.cart m₂.cart ψ ψ' hsq hmon'
  have hmon : IsMonHom ψ := hH.1
  have hdpos : 0 < d := Nat.pos_of_ne_zero (by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' ((Nat.coprime_zero_left p).mp hdp))
  obtain ⟨hfin, -, hsurj⟩ := hIsog R S' s' o₁'.A o₂'.A o₁'.ab o₂'.ab ψ' χ' d hdpos hmon' hχmon' hd1' hd2'
  obtain ⟨χ, hχsq, hd1, hd2⟩ := hH.2 χ' d hχmon' hsurj hfin hd1' hd2'
  have hχmon : IsMonHom χ := (hHom S S' c o₂.A o₁.A o₂'.A o₁'.A o₂.ab o₁.ab o₁'.ab m₂.φ m₁.φ
    m₂.cart m₁.cart χ χ' hχsq hχmon').1
  refine ⟨hmon, fun b => comp_eq_comp_of_over_left_comm m₁.φ m₂.φ _ _ _ _ ψ ψ' hsq (m₁.act b) (m₂.act b) (hact' b),
    ⟨χ, d, hχmon, fun b => comp_eq_comp_of_over_left_comm m₂.φ m₁.φ _ _ _ _ χ χ' hχsq (m₂.act b) (m₁.act b) (hχact' b),
      hd1, hd2, hdp⟩,
    ⟨e, hep, hPol D.toG R gb S S' s s' c N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' hmon hsq e hpol', hint⟩, ?_⟩
  intro k _ _ t β htβ
  obtain ⟨v, hv⟩ := ‹Surjective c›.surj (UpperTheory.Gal.TranscendenceTraces.pt t)
  obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds c k t v hv
  subst hz
  have hz' : z ≫ s' = spMap β := by
    rw [← hcs, ← Category.assoc]
    exact htβ
  obtain ⟨I₁', I₂', hI₁', hI₂', hiff'⟩ := hgeo' k z β hz'
  obtain ⟨-, hT1⟩ := hTate p D R gb S S' s s' c N₁ o₁ o₁' m₁ k z
  obtain ⟨-, hT2⟩ := hTate p D R gb S S' s s' c N₂ o₂ o₂' m₂ k z
  obtain ⟨I₁, hInd₁, hev₁⟩ := hT1 I₁'
  obtain ⟨I₂, hInd₂, hev₂⟩ := hT2 I₂'
  refine ⟨I₁, I₂, hInd₁ hI₁', hInd₂ hI₂', fun n hn hnp x y => ?_⟩
  have e1 : Over.Hom.left (I₁'.ev n x) ≫ m₁.φ = Over.Hom.left (I₁.ev n x) := hev₁ n x
  have e2 : Over.Hom.left (I₂'.ev n y) ≫ m₂.φ = Over.Hom.left (I₂.ev n y) := hev₂ n y
  rw [← hiff' n hn hnp x y]
  constructor
  · intro hxy
    apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hsq, ← Category.assoc, e1, ← Over.comp_left, hxy, e2]
    · rw [Over.w, Over.w]
  · intro hxy
    apply Over.OverMorphism.ext
    rw [Over.comp_left, ← e1, ← e2, Category.assoc, ← hsq, ← Category.assoc, ← Over.comp_left, hxy]
