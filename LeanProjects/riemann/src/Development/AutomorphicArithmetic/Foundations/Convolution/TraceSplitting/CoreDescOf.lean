import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

theorem haar_norm (K : Type) [Field K] [NumberField K] (n : ℕ) (x : Pl K) [MeasurableSpace (Gw n x)] [BorelSpace (Gw n x)] :
    ∃ mm : Measure (Gw n x), mm.IsHaarMeasure ∧ mm (GLnLocal.integralGL (x.adicCompletion K) n) = 1 := by
  have hc := GLnLocal.isCompact_integralGL (x.adicCompletion K) n
  have ho := GLnLocal.isOpen_integralGL (x.adicCompletion K) n
  let P : TopologicalSpace.PositiveCompacts (Gw n x) := ⟨⟨_, hc⟩, by
    change (interior (GLnLocal.integralGL (x.adicCompletion K) n : Set (Gw n x))).Nonempty
    rw [ho.interior_eq]; exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure P, inferInstance, Measure.haarMeasure_self⟩

theorem coreDesc_of (hAbs : AbsLast) (hPull : PullBack) (hUnit : UnitTrace) (hOne : OneTerm) (hSum : SideSum) (hPS : PickS)
    (hPI : PickInf) (hTy : TyEx) (hTE : TermE) (hGood : GoodEx) (hPl : Places) (hOcc : OccursBasics)
    (hEig : EigBasic) (hCI : CI) (hGM : GM.GM) : CoreDesc := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ θ hθ V Λ t hV hVθ hAt hOffA v w hv τ' hτ'
  obtain ⟨S, q, w₀, hvS, hqS, hq, hunr, hsph, hS'⟩ := hPS F E σ hσ hp n hn μE V Λ t hV hAt v
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
  refine ⟨V₀ i, Λ', t', (hι i).1, ⟨SF, hSFf, hA⟩, hΛ, ?_, τ₀ i v, (hι i).2.2.2 v, hiso _ hi⟩
  obtain ⟨𝔢, -, h𝔢, -⟩ := hG L₁ ν hν
  have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hL₁S]; rfl
  exact Filter.mem_of_superset (heS ▸ 𝔢.finS : SE.Finite).compl_mem_cofinite fun y hy => ht y hy

end UpperTheory.ConvolutionTheory.T
