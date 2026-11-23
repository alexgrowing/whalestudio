import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOnPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsDualBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeightSmoothNormalization
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ShFam.Pad GlobalTheory.FlatSecCover

set_option maxHeartbeats 800000 in

theorem GlobalTheory.FlatSecCover.norms_flat_comb : ∀ (D : D7) (O : Setup D) (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (B : ℝ) (τ : D.what₂.Tau) (c : O.s.Comp)
    (g : (T.M c).Fun) (ε : (𝓞 D.what₂.LL →+* ℂ) → Fin ((T.M c).n + 1))
    (π : ∀ σ, GlobalTheory.CxPts (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p σ → (T.M c).X (ε σ)),
    (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.IsDown (h.man c) ε π →
    ∀ (hu : ∀ σ y, GlobalTheory.CxPts.CInfAt ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ) y)
      (hc : ∀ σ σ', (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ)).IsConj
        (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ')))
      (gY : ∀ σ : D.what₂.LL →+* ℂ, Pts (O.var c) σ → ℝ), (∀ a z, gY ((h.man c).ε a) ((h.man c).pt a z) = g a z) →
    ∃ l : ∀ v : HeightOneSpectrum (𝓞 D.what₂.LL), Ext v → AlgPt (O.var c) → ℝ,
      GlobalTheory.CoverNorm.Norms (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V (comb (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc)
      ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (1 : ℤ) fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℤ) else 0))
        (detFn O c B τ) (fun σ y => detLn O c B τ σ y - (gY σ y - O.Y.htDetT B c τ)) l := by
  intro D O A T H hR B τ c g ε π hd hu hc gY hgY
  classical

  have hline : ∀ st, (letterOf O.S.Dw st).isSome →
      GlobalTheory.CoverNorm.Norms (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V ((hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).line (GlobalTheory.FlagAr.setB O.Y B) st) (fun z => genAt (lineAdl O c B st).D z ^ 1)
        (fun σ y => ((1 : ℕ) : ℝ) * lnAdl (lineAdl O c B st) σ y) (fun v e y => ((1 : ℕ) : ℝ) * (lineAdl O c B st).lg v e y) :=
    fun st hs => GlobalTheory.CoverNorm.norms_of_induces ((hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).line_spec _ subset_rfl st hs)
  have hs1 : ∀ (τ' : D.what₂.Tau) (i : Fin O.N), (i : ℕ) < O.j →
      (letterOf O.S.Dw (.inl (DV.tauEmb D τ', (i : ℕ)))).isSome := by
    intro τ' i hi
    have hm : O.S.Dw.mult (DV.tauEmb D τ') = O.j := (GlobalTheory.Harm.mult_of_mem O.S.Dw (O.A.cm τ')).trans O.S.p_eq
    have hlt : (i : ℕ) < O.S.Dw.mult (DV.tauEmb D τ') := by rw [hm]; exact hi
    simp [letterOf, hlt]
  have hs2 : ∀ (τ' : D.what₂.Tau) (i : Fin O.N), ¬ (i : ℕ) < O.j →
      (letterOf O.S.Dw (.inl (conjEmb (DV.tauEmb D τ'), O.N - 1 - (i : ℕ)))).isSome := by
    intro τ' i hi
    have hm : O.S.Dw.mult (conjEmb (DV.tauEmb D τ')) = O.S.Dw.q := GlobalTheory.Harm.mult_conjEmb_of_mem O.S.Dw (O.A.cm τ')
    have h1 := O.S.p_eq
    have h2 := O.S.rank_eq
    have h3 := i.isLt
    have hlt : O.N - 1 - (i : ℕ) < O.S.Dw.mult (conjEmb (DV.tauEmb D τ')) := by rw [hm]; omega
    simp [letterOf, hlt]

  have hroot : ∀ x : D.what₂.Tau × Fin O.N, ∃ l, GlobalTheory.CoverNorm.Norms (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V ((hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B) (some x))
      (fun z => (rootFn O c B x z)⁻¹) (fun σ y => -rootLn O c B x σ y) l := by
    intro x
    by_cases hx : (x.2 : ℕ) < O.j
    · have h1 := GlobalTheory.CoverNorm.Norms.dual _ _ _ _ _ _ _ (hline _ (hs1 x.1 x.2 hx))
      rw [show (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B) (some x) = ((hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).root (GlobalTheory.FlagAr.setB O.Y B) x).dual from rfl,
        GlobalTheory.Mean4O.Setup.LatModel.root, if_pos hx]
      exact ⟨_, h1.congr (fun z => by simp [rootFn, hx, lineAdl]) (fun σ y => by simp [rootLn, hx, lineAdl])
        (fun _ _ _ => rfl)⟩
    · have h1 := GlobalTheory.CoverNorm.Norms.dual _ _ _ _ _ _ _
        (GlobalTheory.CoverNorm.Norms.dual _ _ _ _ _ _ _ (hline _ (hs2 x.1 x.2 hx)))
      rw [show (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B) (some x) = ((hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).root (GlobalTheory.FlagAr.setB O.Y B) x).dual from rfl,
        GlobalTheory.Mean4O.Setup.LatModel.root, if_neg hx]
      exact ⟨_, h1.congr (fun z => by simp [rootFn, hx, lineAdl]) (fun σ y => by simp [rootLn, hx, lineAdl])
        (fun _ _ _ => rfl)⟩

  obtain ⟨fa, aa, la, hla⟩ : ∃ fa aa la, GlobalTheory.CoverNorm.Norms (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).amp fa aa la :=
    ⟨_, _, _, GlobalTheory.CoverNorm.norms_of_induces (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).amp_spec⟩

  have key : ∀ (a : Fin ((T.M c).n + 1)) (x : (T.M c).X a) (σ : D.what₂.LL →+* ℂ) (y : Pts (O.var c) σ),
      (hR.man c).ε a = σ → ((hR.man c).pt a x).1 = y.1 → gY σ y = g a x := by
    intro a x σ y h1 h2
    subst h1
    rw [← hgY a x]
    congr 1
    exact (Subtype.ext h2).symm
  have hmono : Mono (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.j := by
    have : Mono (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) := by
      have : Epi (CommRingCat.ofHom (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) :=
        IsLocalization.epi (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL
      exact Scheme.Spec.map_mono (CommRingCat.ofHom _).op
    rw [← (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.pb.isoPullback_hom_fst]
    infer_instance
  have ha : ∀ (σ : D.what₂.LL →+* ℂ) (z : CxPts ((hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.π ≫ (O.var c).str) σ) (y : Pts (O.var c) σ)
      (y' : CxPts (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p (σ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))), y.1 = z.1 ≫ (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.π → y'.1 = z.1 ≫ (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.j →
      -(gY σ y - O.Y.htDetT B c τ) = -((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) _ y' / 2) := by
    intro σ z y y' e1 e2
    obtain ⟨hε, hw⟩ := hd (σ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))
    obtain ⟨w, hw1, hw2⟩ := hw y'
    have hσ : (hR.man c).ε (ε (σ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) = σ :=
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.what₂.LL)) hε
    have hwz : w = z.1 := (cancel_mono (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.j).1 (hw1.trans e2)
    have hpt := key _ _ σ y hσ (by rw [← hw2, hwz, e1])
    simp only [GlobalTheory.Mean4O.Man.pull, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hpt]
    ring
  have hB := (GlobalTheory.CoverNorm.norms_triv_fnB _ _ (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V).2 _ hu hc (fun σ y => -(gY σ y - O.Y.htDetT B c τ)) ha
  choose lr hlr using hroot
  have hall := GlobalTheory.CoverNorm.norms_comb (V := (hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V)
    (L := fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc)
      ((hR.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B)))
    (f := fun o => o.elim (fun _ => 1) fun o' => o'.elim fa fun x z => (rootFn O c B x z)⁻¹)
    (a := fun o => o.elim (fun σ y => -(gY σ y - O.Y.htDetT B c τ)) fun o' => o'.elim aa fun x σ y => -rootLn O c B x σ y)
    (l := fun o => o.elim (fun _ _ _ => 0) fun o' => o'.elim la lr)
    (fun o => match o with
      | none => hB
      | some none => hla
      | some (some x) => hlr x)
    (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (1 : ℤ) fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℤ) else 0)
  refine ⟨_, hall.congr (fun z => ?_) (fun σ y => ?_) (fun _ _ _ => rfl)⟩
  · simp only [Fintype.prod_option, Option.elim, zpow_zero, one_zpow, one_mul, Fintype.prod_prod_type, detFn]
    rw [Finset.prod_eq_single τ (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  · simp only [Fintype.sum_option, Option.elim, Fintype.sum_prod_type, detLn]
    rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
    ring
