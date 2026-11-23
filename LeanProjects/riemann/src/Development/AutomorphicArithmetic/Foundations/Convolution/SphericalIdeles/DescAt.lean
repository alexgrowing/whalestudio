import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDesc
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

theorem _root_.UpperTheory.ConvolutionTheory.Sph.descAt (hCI : CI) (hGM : GM.GM) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure] (μF : Measure (normOneGL F n)) [μF.IsHaarMeasure] (θ : Twist μE),
      IsGalTwist σ θ → ∀ (V : Submodule ℂ (LL μE)) Λ t (S₀ : Set (Pl E)), IsSummand μE V →
      V.map (θ.U : LL μE →ₗ[ℂ] LL μE) = V → S₀.Finite → At μE S₀ V Λ t → OffAll F n Λ t → ∀ u₀ : Pl F, GM.Unr E u₀ →
      (∀ w : Pl E, w.under (𝓞 F) = u₀ → w ∉ S₀) →
      ∃ (V₀ : Submodule ℂ (LL μF)) (Λ₀ : (F →+* ℂ) → Multiset ℂ) (t₀ : Pl F → Multiset ℂ), IsSummand μF V₀ ∧ AtAE μF V₀ Λ₀ t₀ ∧
        Λ = bcInf Λ₀ ∧ (∀ᶠ u in cofinite, t u = bcSat t₀ u) ∧ SSat μF V₀ u₀ (t₀ u₀) ∧
        ∀ w : Pl E, w.under (𝓞 F) = u₀ → t w = bcSat t₀ w := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ θ hθ V Λ t S₀ hV hVθ hS₀ hA0 hOffA u₀ hu₀ hu₁
  have hAbs := absLast
  have hPull := pullBack
  have hUnit := unitTrace
  have hOne := oneTerm
  have hSum := sideSum
  have hPI := pickInf
  have hTy := tyEx
  have hTE := termE
  have hGood := goodEx
  have hPl := places
  have hOcc := C.occursBasics
  have hEig := L1.eigBasic
  obtain ⟨hInf, hUnr, hNe, -, -, -⟩ := places F E hp
  obtain ⟨-, -, h0⟩ := Dp.parEx E n hn μE V hV
  obtain ⟨v, hv, hvu⟩ := (hInf.diff (Set.finite_singleton u₀)).nonempty
  obtain ⟨w⟩ := hNe v
  obtain ⟨τ', hτ'⟩ : ∃ τ', Occurs μE V w.1 τ' := by
    letI : MeasurableSpace (Gw n w.1) := borel _
    haveI : BorelSpace (Gw n w.1) := ⟨rfl⟩
    exact (hOcc E n μE V w.1 Measure.haar hV).1
  have hfin := ((hS₀.image (fun w => w.under (𝓞 F))).union (Filter.eventually_cofinite.1 hUnr)).union (Set.finite_singleton v)
  obtain ⟨q, hq, hqS'⟩ := (hInf.diff (hfin.union (Set.finite_singleton u₀))).nonempty
  obtain ⟨w₀⟩ := hNe q
  obtain ⟨S, hSdef⟩ : ∃ S, S = hfin.toFinset := ⟨_, rfl⟩
  have hsub : ∀ w : Pl E, w.under (𝓞 F) ∉ S → w ∉ S₀ := fun w hw hw0 =>
    hw (hSdef ▸ hfin.mem_toFinset.2 (Or.inl (Or.inl ⟨w, hw0, rfl⟩)))
  have hvS : v ∈ S := hSdef ▸ hfin.mem_toFinset.2 (Or.inr rfl)
  have hqS : q ∉ S := fun h => hqS' (Or.inl (hfin.mem_toFinset.1 (hSdef ▸ h)))
  have huq : u₀ ≠ q := fun h => hqS' (Or.inr h.symm)
  have huS : u₀ ∉ S := fun h => by
    rcases hfin.mem_toFinset.1 (hSdef ▸ h) with (⟨y, hy, e⟩ | h) | h
    · exact hu₁ y e hy
    · exact h hu₀
    · exact hvu h.symm
  have hunr : ∀ u ∉ S, GM.Unr E u := fun u hu => by
    by_contra h
    exact hu (hSdef ▸ hfin.mem_toFinset.2 (Or.inl (Or.inr h)))
  have hsph : ∀ w : Pl E, w.under (𝓞 F) ∉ S → V ⊓ fixL μE w (GLnLocal.integralGL (w.adicCompletion E) n) ≠ ⊥ :=
    fun w hw => (hA0.2 w (hsub w hw)).2.1
  have hS' : ∀ S' : Set (Pl E), (∀ w, w ∈ S' ↔ w.under (𝓞 F) ∈ S ∨ w.under (𝓞 F) = q) →
      At μE S' V Λ t ∧ (∀ τ, (Λ τ).card = n) ∧ ∀ w ∉ S', (t w).card = n ∧ 0 ∉ t w := fun S' hS' => by
    have hS : ∀ w, w ∉ S' → w ∉ S₀ := fun w hw => hsub w fun h => hw ((hS' w).2 (Or.inl h))
    exact ⟨⟨hA0.1, fun w hw => hA0.2 w (hS w hw)⟩, fun τ => (hA0.1 τ).1,
      fun w hw => ⟨(hA0.2 w (hS w hw)).1, h0 w _ (hA0.2 w (hS w hw))⟩⟩
  clear hSdef hvu
  have hne := (hPl F E hp).2.2.1
  obtain ⟨T, hTS, hmk, htyped, hrank, c, f₀, UF, hUF, hL⟩ := hTy F E σ hσ hp n hn μE V hV q w₀ hq S hqS hunr hsph
    (Function.update (fun u => (hne u).some) v w)
  have hw : T.mk' v = w := by rw [hmk, Function.update_self]
  clear hmk
  subst hw
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 htyped
  obtain ⟨m, hm, D, s, hs, νE, iE, νF, iF, b, a, aE, aF, hposition, harch, hAE, hAF, hpair, hua⟩ :=
    hPI F E σ hσ hp n hn μE μF u hu0
  letI : ∀ x : Pl E, MeasurableSpace (Gw n x) := fun _ => borel _
  haveI : ∀ x : Pl E, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩
  letI : ∀ x : Pl F, MeasurableSpace (Gw n x) := fun _ => borel _
  haveI : ∀ x : Pl F, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩
  have hmE : ∀ x : Pl E, ∃ mm : Measure (Gw n x), mm.IsHaarMeasure := fun x => (haar_norm E n x).imp fun _ h => h.1
  have hmF : ∀ x : Pl F, ∃ mm : Measure (Gw n x), mm.IsHaarMeasure ∧ mm (GLnLocal.integralGL (x.adicCompletion F) n) = 1 :=
    fun x => haar_norm F n x
  choose mE hmE using hmE
  choose mF hmF using hmF
  have hτ : ∀ x : Pl E, ∃ τ : SmIrr (Gw n x), Occurs μE V x τ := fun x => by
    haveI := hmE x
    exact (hOcc E n μE V x (mE x) hV).1
  choose τ₁ hτ₁ using hτ
  obtain ⟨τ, hτ, hτw⟩ : ∃ τ : ∀ x : Pl E, SmIrr (Gw n x), (∀ x, Occurs μE V x (τ x)) ∧ τ (T.mk' v).1 = τ' := by
    refine ⟨Function.update τ₁ (T.mk' v).1 τ', fun x => ?_, Function.update_self ..⟩
    by_cases h : x = (T.mk' v).1
    · subst h; rw [Function.update_self]; exact hτ'
    · rw [Function.update_of_ne h]; exact hτ₁ x
  subst hτw
  obtain ⟨ν, hν⟩ := hGood n hn
  obtain ⟨x, cE, Z₀, hx, hcE, hZ₀, hZ0, hE⟩ := hTE F E σ hσ hp n hn m hm μE θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq T V hV
    hVθ hrank ⟨u, hu, hua⟩ mE hmE τ hτ ν hν.1.antitone
  obtain ⟨κ, hκ, hG⟩ := hGM F E σ hσ hp n hn μE μF θ hθ q w₀ hq νE νF aE aF 1 one_pos hAE hAF hpair
  set SF : Set (Pl F) := {y | y ∈ S ∨ y = q} with hSF
  set SE : Set (Pl E) := {y | y.under (𝓞 F) ∈ SF} with hSE
  obtain ⟨ι, _, V₀, τ₀, bF, Z, hι, hF⟩ := hSum F E σ n (Module.finrank F E) hn μF νF mF hmF aF q w₀ S UF ν hν.1.antitone
    (fun V₀ => ∃ Λ' t', At μF SF V₀ Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ y ∉ SE, t y = bcSat t' y) x hx
  have hvsp : v ∈ T.sp := Finset.mem_filter.2 ⟨hTS ▸ hvS, hv⟩
  obtain ⟨τv, r, hr, hiso, htr, hlev⟩ := hPull F E n v (T.mk' v) (hv _) (mF v) (mE _) (hmF v).1 (hmE _) (τ _)
  obtain ⟨hCO, hfix, hφ⟩ := hlev (T.J _) (UF v) (T.co _) (hUF v hvsp)
  have hunit : ∀ y ∈ T.sp, _ := fun y hy => hUnit E n μE V hV (T.mk' y).1 (mE _) (hmE _) (τ _) (T.J _) (hτ _) (T.co _) (by
    refine (Submodule.ne_bot_iff _).2 ⟨u, ⟨hu.1, ?_⟩, hu0⟩
    have h1 : u ∈ eigL μE (T.mk' y).1 (T.J _) (T.χ _) := (Submodule.mem_iInf _).1 hu.2 _
    rw [T.triv y (Finset.mem_filter.1 hy).2 (T.mk' y)] at h1
    have h2 := T.chr (T.mk' y).1
    rw [T.triv y (Finset.mem_filter.1 hy).2 (T.mk' y)] at h2
    rwa [(hEig E n μE _ _ _ (T.co _) h2).2.1] at h1)
  have hsu : ∀ y : Pl F, ∃ z : ℂ, y ∈ T.sp → z ≠ 0 ∧ HasTrace (mE _) (τ (T.mk' y).1).ρ
      ((T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator 1) z := fun y => by
    by_cases hy : y ∈ T.sp
    · obtain ⟨z, hz⟩ := (hunit y hy).2.2.2
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose su hsu using hsu
  let ψ₁ : ∀ y : Pl F, Gw n (T.mk' y).1 → ℂ := fun y => (T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator 1
  obtain ⟨L₁, hfit₁, -, hL₁s, hL₁n⟩ := hL ψ₁ fun y hy => ⟨(hunit y hy).2.1, (hunit y hy).2.2.1⟩
  have hL₁S : L₁.S = S := hfit₁.S_eq.trans hTS
  have hs₁ : ∀ i (y : Pl F), ∃ z : ℂ, y ∈ S → HasTrace (mF y) (τ₀ i y).ρ (L₁.f y) z := fun i y => by
    by_cases hy : y ∈ S
    · haveI := (hmF y).1
      have ht := L₁.test y (hL₁S ▸ hy)
      obtain ⟨z, hz⟩ := (hOcc F n μF (V₀ i) y (mF y) (hι i).1).2.2 _ ((hι i).2.2.2 y) (L₁.f y) ⟨ht.2.2.1, ht.2.2.2⟩
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose s₁ hs₁ using hs₁
  haveI := (hmF v).1
  obtain ⟨i, hi⟩ := hAbs F n v (mF v) (UF v) hCO ι (fun i => τ₀ i v)
    (fun i => (κ * ∏ y ∈ S, c y) * bF i * ∏ y ∈ S.erase v, s₁ i y) Z τv (cE * r * ∏ y ∈ T.sp.erase v, su y) Z₀
    (mul_ne_zero (mul_ne_zero hcE hr) (Finset.prod_ne_zero_iff.2 fun y hy => (hsu y (Finset.mem_of_mem_erase hy)).1))
    hZ₀ hZ0 (fun i => (hι i).2.2.1) (hfix (hunit v hvsp).1) (by
      intro φ s₀ sF hφt hφi hs₀ hsF
      obtain ⟨ψv, hψt, hψi, rfl⟩ := hφ φ hφt hφi
      obtain ⟨L, hfit, hLc, hLs, hLn⟩ := hL (Function.update ψ₁ v ψv) fun y hy => by
        by_cases h : y = v
        · subst h; rw [Function.update_self]; exact ⟨hψt, hψi⟩
        · rw [Function.update_of_ne h]; exact ⟨(hunit y hy).2.1, (hunit y hy).2.2.1⟩
      have hLS : L.S = S := hfit.S_eq.trans hTS
      obtain ⟨𝔢, 𝔣, h𝔢, h𝔣, hgeo⟩ := hG L ν hν
      have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hLS]; rfl
      have hfS : 𝔣.S = SF := Set.ext fun y => by rw [h𝔣.2.2.1, hLS]; rfl
      obtain ⟨hAt', hc1, hc2⟩ := hS' 𝔢.S fun y => by rw [h𝔢.2.2.1, hLS]
      have hoff : OffFam F n 𝔢.S 𝔣.S Λ t := by
        rw [heS, hfS]
        exact hOffA SF ((S.finite_toSet.union (Set.finite_singleton q)).subset fun y hy => hy)
      filter_upwards [hCI F E n _ hn hp.pos μE μF θ 𝔢 𝔣 _ hgeo Λ t hc1 hc2 hoff x hx] with j hj
      rw [hOne E n _ hn μE θ 𝔢 V Λ t hV hVθ hAt' x j,
        hE L _ hfit _ 𝔢 h𝔢 (Function.update su v (r * s₀)) (fun y hy => by
          by_cases h : y = v
          · subst h; rw [Function.update_self, Function.update_self]; exact htr _ _ hs₀
          · rw [Function.update_of_ne h, Function.update_of_ne h]; exact (hsu y hy).2) j, heS, hfS,
        hF L 𝔣 hLS (fun y hy => (hLc y hy).2) h𝔣 (fun i => Function.update (s₁ i) v (sF i)) (fun i y hy => by
          by_cases h : y = v
          · subst h
            rw [Function.update_self, hLs y hvsp, Function.update_self]; exact hsF i
          · rw [Function.update_of_ne h]
            have e : L.f y = L₁.f y := by
              by_cases hy' : GM.Split E y
              · have hys : y ∈ T.sp := Finset.mem_filter.2 ⟨hTS ▸ hy, hy'⟩
                rw [hLs y hys, hL₁s y hys, Function.update_of_ne h]
              · rw [hLn y hy hy', hL₁n y hy hy']
            rw [e]; exact hs₁ i y hy) j, hLS, Finset.prod_congr rfl fun y hy => (hLc y hy).1,
        Finset.prod_update_of_mem hvsp, Finset.mul_sum] at hj
      simp only [Finset.prod_update_of_mem hvS, Finset.sdiff_singleton_eq_erase] at hj
      calc _ = cE * (Z₀.map (· ^ j)).sum * (r * s₀ * ∏ y ∈ T.sp.erase v, su y) := by ring
        _ = _ := hj
        _ = _ := Finset.sum_congr rfl fun i _ => by ring)
  obtain ⟨Λ', t', hA, hΛ, ht⟩ := (hι i).2.1
  have hSFf : SF.Finite := (S.finite_toSet.union (Set.finite_singleton q)).subset fun y hy => hy
  have huF : u₀ ∉ SF := fun h => h.elim huS huq
  refine ⟨V₀ i, Λ', t', (hι i).1, ⟨SF, hSFf, hA⟩, hΛ, ?_, hA.2 u₀ huF, fun y hy => ht y fun h => huF (hy ▸ h)⟩
  obtain ⟨𝔢, -, h𝔢, -⟩ := hG L₁ ν hν
  have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hL₁S]; rfl
  exact Filter.mem_of_superset (heS ▸ 𝔢.finS : SE.Finite).compl_mem_cofinite fun y hy => ht y hy

end UpperTheory.ConvolutionTheory.T
