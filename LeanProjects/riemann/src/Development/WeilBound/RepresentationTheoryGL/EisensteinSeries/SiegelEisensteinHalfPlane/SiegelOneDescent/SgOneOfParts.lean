import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing

namespace PositivityTheory.RgEis.So

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

theorem sgOne_of_parts (hB : BaseCM) (hE : JEx) (hT : JTop) (hC : JCpt) (hP : JPar) (hI : JIwa) (hR : JRat) (hS : JSec)
    (hCh : JCh) (hM : JMir) (hD : Descend2) (hTw : Twist) (hSc : Scale) (hG : CMGood) (hGT : GrpTop) (hPL : ParLaw)
    (hMG : MirGen) : SgOne := by
  intro F E _ _ _ _ _ σ χ c h h' hχ hc ε ι _ _ hι hiw W _ _ _ ρ hρ
  obtain ⟨r, δ, α, ω, hb⟩ := hB F E σ χ c h h' hχ hc ε
  have hg := hG F E σ χ c h h' hχ hc
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.1 hι
  obtain ⟨j, hj⟩ := hE F E _ _ ε _ r δ α ω ι i hb hi
  obtain ⟨jc, t2, lc, sc⟩ := hT F E _ _ ε _ r δ α ω ι i j hg hb hi hj
  have kc := hC F E _ _ ε _ r δ α ω ι i j hg hb hi hj
  obtain ⟨p1, p2, -⟩ := hP F E _ _ ε _ r δ α ω ι i j hg hb hi hj
  have iw := hI F E _ _ ε _ r δ α ω ι i j hg hb hi hj
  obtain ⟨rm, -⟩ := hR F E _ _ ε _ r δ α ω ι i j hg hb hi hj
  obtain ⟨s, sc1, sc2, sc3⟩ := hS F E _ _ ε _ r δ α ω ι i j hg hb hi hj
  obtain ⟨ch0, htl⟩ := hCh F E _ _ ε _ r δ α ω ι i j hg hb hi hj
  have md := hM F E _ _ ε _ r δ α ω ι i j hg hb hi hj hiw
  obtain ⟨-, -, -, u2, ulc, -, ukc⟩ := hGT E _ (adCM σ χ) hg ι ε
  have e : (adCM σ χ).uQ ε (Set.univ : Set ι) ⊓ (adCM σ χ).uQ ε Set.univ = (adCM σ χ).uQ ε Set.univ := inf_idem _
  obtain ⟨par, ht, -⟩ := (hPL E _ (adCM σ χ) hg ι ε Set.univ).2 (e.symm ▸ hiw)
  rw [e] at par
  have hβ : IsHt ((adCM σ χ).uΓ ε ι) ((adCM σ χ).uK ε ι) ((adCM σ χ).uQ ε Set.univ)
      fun g => (Fintype.card ι : ℝ) * (adCM σ χ).uH ε Set.univ g := by
    simpa [hι] using ht
  refine hD _ W _ ρ ukc hρ _ j _ _ (cΓ _ _ ι) (cK α j) _ _ _ _ s jc kc inf_le_left rm sc1 sc2 sc3 (p2 ▸ iw) par ht ht hβ ?_
  have par1 := md.par
  have w1 : AllRep (cK α j) fun ρ₁ => HasWall (cΓ _ _ ι) (cK α j) ((stab 𝔸[F] {Sum.inl i}).comap (prj _ _ ι))
      ((stab 𝔸[F] {Sum.inl i}).comap (prj _ _ ι)) (c1 j) (fun x => ((adCM σ χ).uH ε Set.univ (j x) + ld x) / 2)
      (fun x => ((adCM σ χ).uH ε Set.univ (j x) - ld x) / 2)
      (fun x => ld x + (Fintype.card (ι ⊕ ι) : ℝ) * (((adCM σ χ).uH ε Set.univ (j x) - ld x) / 2)) ρ₁ := by
    intro W₁ _ _ _ ρ₁ hρ₁
    have := (hMG _ W₁ (cK α j) ρ₁ kc hρ₁ F (ι ⊕ ι) _ _ _ _ ω _ _ _ _ _ sc md).1
    rwa [p1] at this
  have w2 := (hTw _ _ _ _ _ _ _ c0 _ _ _ (fun _ => 0) 0 kc ch0 par1 par1 par1).1 w1
  intro W₁ _ _ _ ρ₁ hρ₁
  have hl : IsHt (cΓ (adCM σ χ) (nuCM F E) ι) (cK α j) ⊤ fun x => -(ld x) / 2 :=
    ⟨fun p hp g => by rw [htl.left p hp g]; ring, fun g k hk => by rw [htl.right g k hk],
      fun γ a b => by rw [htl.rat γ a b]; simp, htl.cont.neg.div_const 2⟩
  have w3 := hSc _ W₁ (cK α j) ρ₁ kc hρ₁ _ _ _ _ _ _ _ _ 2 two_pos hl (w2 W₁ ρ₁ hρ₁)
  rw [p2]
  convert w3 using 2
  · funext x
    have : (c0 x : ℂ) ≠ 0 := Circle.coe_ne_zero _
    simp [c1, this]
  · simp only [Function.comp]; ring
  · simp only [Function.comp]; ring
  · simp only [Function.comp, Fintype.card_sum, hι]; push_cast; ring

end PositivityTheory.RgEis.So
