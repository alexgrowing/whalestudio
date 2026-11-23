import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPolarized
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SGoodOfLevelShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompAtEqOneOfTameAt
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SphNonSplit
set_option maxHeartbeats 2000000 in
theorem sphAU_of_not_split_m_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), ¬ IsSplitPl D.host w → D.nbc.sphAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _hCS hMI _hstar _hE hsp _hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop P w hns
  set v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w with hv
  have hover : NG.OverPl w v := rfl
  rw [A.au.sph (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 _ w v hns hover]
  obtain ⟨h1, h2⟩ := X.nd.j_range i
  let j : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = X.nd.j i := by simp only [j]; omega
  have hvB := not_mem_bad D cf C tp hsp (X.nd.w i) j w v hover hns
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j)) := by
    have key : ∀ (μ : D.what₂.Tup) (jj : ℕ) (k1 : 1 ≤ jj) (k2 : jj ≤ D.R.m), μ = D.what₂.muTw (X.nd.w i) → jj = j.1 + 1 →
        NG.HypOutside (M μ jj k1 k2).J (M μ jj k1 k2).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j)) := by
      rintro μ jj k1 k2 rfl rfl
      exact hMI.hyp (X.nd.w i) j
    exact key _ _ _ _ (X.nd.mu_w i) hj.symm
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (hne P)
  have hry : (mlX M X i).real y ≠ 0 := fun h0 =>
    hy0 ((mlX M X i).real_inj (h0.trans (map_zero (mlX M X i).real).symm))
  have hT : (mlX M X i).real y ∈ NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ := by
    rw [← (mlX M X i).real_range]; exact LinearMap.mem_range_self _ _
  obtain ⟨f, hfS, hf0, hfix⟩ := GlobalTheory.T.fixed_vector_of_mem_isotypic_component (mlX M X i).wt.ρ (F P)
    {κ | κ ∈ Umax D.host.E D.R.nV ∧ TrivOutside {v} κ} (irr P) _ hy hry (by
      rintro κ ⟨hU, htr⟩
      have ht : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j))ᶜ κ := fun u hu =>
        htr u (by rintro rfl; exact hu hvB)
      have hJ : κ ∈ (mlX M X i).J := ((hyp κ ht).1).2 hU
      rw [hT.2 ⟨κ, hJ⟩, (hyp κ ht).2 hJ, Units.val_one, one_smul])
  have hsh : ∀ (μ : D.what₂.Tup) (jj : ℕ) (k1 : 1 ≤ jj) (k2 : jj ≤ D.R.m), μ = D.what₂.muTw (X.nd.w i) → jj = j.1 + 1 →
      ∀ s : SplitPlace D.host.E, s.v ∈ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j) → ∃ s₀ : SplitPlace D.host.E, s₀.v = s.v ∧
      ((∃ (r : ℕ) (ξ : (s₀.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.LevelPara (M μ jj k1 k2).J (M μ jj k1 k2).χ s₀ r ξ) ∨
      ((∃ (g : ℕ) (_ : Fact g.Prime) (e : ℚ_[g] ≃+* s.w.adicCompletion D.host.E), Continuous e) ∧
        ∃ (r : ℕ) (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
          (ξ : (s₀.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.LevelUni (M μ jj k1 k2).J (M μ jj k1 k2).χ s₀ r ψ₀ ξ ∧ NG.IsPsi0 s₀ ψ₀ ∧
          ∀ u : (s₀.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
            Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 → ξ u = 1)) := by
    rintro μ jj k1 k2 rfl rfl s hs
    by_cases hg : s.v ∈ gPl D
    · obtain ⟨k, v', s₀, hw, hv'⟩ := GlobalTheory.PlaceUnderFixed.exists_splitPlace_under_plGw D s hg
      obtain ⟨ψ₀, ξ, hψ, hc, hU⟩ := hMI.uni (X.nd.w i) j k v' s₀ hw
      refine ⟨s₀, hv', Or.inr ⟨GlobalTheory.SplitTypeCompl.exists_padic_equiv D s hg, D.R.r, ψ₀, ξ, hU, hψ,
        GlobalTheory.AVGood.compAt_eq_one_of_tameAt s₀ _ (fun x hx hx' => ?_) ξ hc⟩⟩
      rw [TupTied.tup, HChar.loc_mul, (cf.isMu0 j).tame _ x hx hx', tp.xi_tame _ _ x hx hx', one_mul]
    · obtain ⟨s₀, ξ, hv', -, hP⟩ := hMI.para (X.nd.w i) j s.v (hs.resolve_left hg)
      exact ⟨s₀, hv', Or.inl ⟨D.R.r, ξ, hP⟩⟩
  have hlev : GlobalTheory.RecT.Thread.LevelShape ({ (mlX M X i).wt with S := F P, irrS := irr P } : NG.AutRep D.host.E D.R.nV) :=
    ⟨(mlX M X i).J, (mlX M X i).χ, _, (mlX M X i).J_open, hyp, ⟨_, hy, hT, hry⟩, hsh _ _ _ _ (X.nd.mu_w i) hj.symm⟩
  have h0 : _root_.UpperTheory.One.M.New.Sph0 ({ (mlX M X i).wt with S := F P, irrS := irr P } : NG.AutRep D.host.E D.R.nV) v :=
    ⟨f, hfS, hf0, fun κ hU htr => hfix κ ⟨hU, htr⟩⟩
  exact _root_.UpperTheory.One.M.New.sphMk h0 fun _ =>
    GlobalTheory.RecT.Thread.good_of_levelShape UpperTheory.Zero.LLC.Pr.bz UpperTheory.Zero.LLC.Pr.zel _ hlev
end GlobalTheory.SphNonSplit
end
end
