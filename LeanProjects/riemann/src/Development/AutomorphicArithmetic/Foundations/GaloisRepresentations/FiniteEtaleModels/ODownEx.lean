import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OLevDown
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtModelForgetFiniteEtale

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.O.downEx :
    UpperTheory.Gal.FiniteEtaleModels.O.DownEx := by
  intro p _ D hm _ E _ _ gb w q _ r 𝔴 𝔫 S N₀ κ 𝔟₁ 𝔟₂ X₁ X₂ ε h
  obtain ⟨h3, -, -, -, -⟩ := X₂.lev
  obtain ⟨-, hcq₁, -, -, e₁, he₁⟩ := X₁.lev
  have hd : N₀ ∣ N₀ * κ := dvd_mul_right N₀ κ
  have hne : 𝔟₁ ≠ ⊥ := by
    intro h0
    have hq : ((q : 𝓞 D.F)) ∈ uId D q r := Ideal.subset_span (Set.mem_insert _ _)
    have hmem : ((q : 𝓞 D.F)) ^ e₁ ∈ 𝔟₁ := he₁ (Ideal.pow_mem_pow hq e₁)
    rw [h0, Ideal.mem_bot] at hmem
    have hq0 : ((q : 𝓞 D.F)) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    exact pow_ne_zero e₁ hq0 hmem
  have hL := UpperTheory.Gal.FiniteEtaleModels.O.levDown q (datAt S.atq S.sp) hm (Ow w) S.b (N₀ * κ) X₁.Y.X X₁.Y.s
    X₁.Y.univ 𝔟₁ 𝔟₂ ε hne h X₁.Y.lv X₁.Y.isLev
  obtain ⟨t, ⟨ht, m, hmt⟩, -⟩ := X₂.Y.rep X₁.Y.X X₁.Y.s (X₁.Y.univ.forget N₀ hd hcq₁)
    (fun y => X₁.Y.lv ((algebraMap (𝓞 D.F) D.O) ε • y)) hL
  obtain ⟨u, ⟨hu, ⟨mu⟩⟩, -⟩ := X₂.M.rep X₁.M.X X₁.M.s (X₁.M.univ.forget N₀ hd hcq₁)
  obtain ⟨hfu, heu, -⟩ := GlobalTheory.T.harrisTaylor_levelForgetting_finite_etale_surjective q (datAt S.atq S.sp) (Ow w) S.b N₀ (N₀ * κ) hd hcq₁ h3
    X₂.M X₁.M u hu ⟨mu⟩
  have hsq : t ≫ X₂.π = X₁.π ≫ u := by
    obtain ⟨v, -, huniq⟩ := X₂.M.rep X₁.Y.X X₁.Y.s (X₁.Y.univ.forget N₀ hd hcq₁)
    have e1 := huniq (t ≫ X₂.π) ⟨by rw [Category.assoc, X₂.ov, ht], ⟨m.comp X₂.mπ⟩⟩
    have e2 := huniq (X₁.π ≫ u)
      ⟨by rw [Category.assoc, hu, X₁.ov], ⟨(LevForget.forgetMap X₁.mπ N₀ hd hcq₁).comp mu⟩⟩
    rw [e1, e2]
  haveI := X₁.fin
  haveI := X₁.et
  haveI := X₂.fin
  haveI := X₂.et
  haveI : IsFinite (t ≫ X₂.π) := by rw [hsq]; infer_instance
  haveI : Etale (t ≫ X₂.π) := by rw [hsq]; infer_instance
  exact ⟨t, m, ht, IsFinite.of_comp t X₂.π, Etale.of_comp t X₂.π, hmt⟩
