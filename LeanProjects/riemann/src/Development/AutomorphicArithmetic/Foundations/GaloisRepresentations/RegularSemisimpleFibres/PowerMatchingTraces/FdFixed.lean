import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.TrBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.TrEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.LevEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.CmpIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCutAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.FibTrace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.BaseTw
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.PowNe
import Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Outright
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TermEV
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocGalEx
import GroundTheory.AutomorphicForms.LocallyProfinite

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G
open UpperTheory.ConvolutionTheory.T
open scoped ComplexConjugate

private theorem fd_fixed {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    (m : Measure G) (ρ : Representation ℂ G V) (J : Subgroup G) (hJ : MeasurableSet (J : Set G))
    (h1 : m (J : Set G) = 1) (A : V →ₗ[ℂ] V) (hA : IsIntegralOp m ρ ((J : Set G).indicator 1) A)
    (hf : FiniteDimensional ℂ (LinearMap.range A)) : FiniteDimensional ℂ (fixedVectors ρ J) := by
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range A) fun x hx => ?_
  have hAx : A x = x := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, (hA x l).2, sub_eq_zero]
    have e : (fun g => ((J : Set G).indicator (1 : G → ℂ)) g * l (ρ g x)) =
        (J : Set G).indicator fun _ => l x := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · have hgx : ρ g x = x := hx g hg
        simp [Set.indicator_of_mem hg, hgx]
      · simp [Set.indicator_of_notMem hg]
    rw [e, integral_indicator hJ]
    simp [Measure.real, h1]
  exact ⟨x, hAx⟩

private theorem under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem small {K : Type} [Field K] [NumberField K] (n : ℕ) (v : Pl K) :
    ∀ N ∈ nhds (1 : Gw n v), ∃ U : Subgroup (Gw n v), IsOpen (U : Set (Gw n v)) ∧ (U : Set (Gw n v)) ⊆ N := fun N hN => by
  obtain ⟨U, -, hU⟩ := exists_openSubgroup_isCompact_subset hN
  exact ⟨U, U.isOpen, hU⟩

private theorem scale {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (m : Measure G) (hm : m.IsHaarMeasure) (J : Subgroup G) (hJ : CO J) :
    ∃ d : ENNReal, d ≠ 0 ∧ d ≠ ⊤ ∧ (d • m).IsHaarMeasure ∧ (d • m) J = 1 := by
  have h0 : m J ≠ 0 := hJ.2.measure_ne_zero _ ⟨1, one_mem _⟩
  have hT : m J ≠ ⊤ := hJ.1.measure_lt_top.ne
  refine ⟨(m J)⁻¹, ENNReal.inv_ne_zero.2 hT, ENNReal.inv_ne_top.2 h0,
    Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hT) (ENNReal.inv_ne_top.2 h0), ?_⟩
  simp [ENNReal.inv_mul_cancel h0 hT]

private theorem updLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E ≃ₐ[F] E} {n : ℕ}
    {q : Pl F} {w₀ : PlacesOver E q} (L : GM.Loc σ n q w₀) (v : Pl F) (hv : v ∈ L.S)
    (φ : GL (Fin n) (CompletionsOver E v) → ℂ) (f : Gw n v → ℂ) (c : ℂ) (UE : Subgroup (GL (Fin n) (CompletionsOver E v)))
    (UF : Subgroup (Gw n v)) (h1 : Test φ) (h2 : Test f) (h3 : GM.MatchAt σ v c φ f)
    (h4 : IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧ (UE : Set _) ⊆ unitSet E n v ∧
      IsOpen (UF : Set (Gw n v)) ∧ UF ≤ GLnLocal.integralGL (v.adicCompletion F) n)
    (h5 : (∀ u ∈ UE, ∀ g, φ (u * g) = φ g) ∧ ∀ u ∈ UF, ∀ g, f (u * g) = f g) :
    ∃ L' : GM.Loc σ n q w₀, L'.S = L.S ∧ L'.φ = Function.update L.φ v φ ∧ L'.f = Function.update L.f v f ∧
      L'.c = Function.update L.c v c ∧ L'.UE = Function.update L.UE v UE ∧ L'.UF = Function.update L.UF v UF := by
  have hq : q ≠ v := fun h => L.q_not (h ▸ hv)
  refine ⟨⟨L.S, L.q_not, L.unr, Function.update L.φ v φ, Function.update L.f v f, Function.update L.c v c,
    Function.update L.UE v UE, Function.update L.UF v UF, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, ?_,
    fun y hy hyq => ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · by_cases h : y = v
    · subst h; simp only [Function.update_self]; exact ⟨h1.1, h1.2, h2.1, h2.2⟩
    · simp only [Function.update_of_ne h]; exact L.test y hy
  · by_cases h : y = v
    · subst h; simp only [Function.update_self]; exact h4
    · simp only [Function.update_of_ne h]; exact L.lev y hy
  · by_cases h : y = v
    · subst h; simp only [Function.update_self]; exact h5
    · simp only [Function.update_of_ne h]; exact L.inv y hy
  · by_cases h : y = v
    · subst h; simp only [Function.update_self]; exact h3
    · simp only [Function.update_of_ne h]; exact L.mat y hy
  · simp only [Function.update_of_ne hq]; exact L.at_q
  · have h : y ≠ v := fun h => hy (h ▸ hv)
    simp only [Function.update_of_ne h]; exact L.off y hy hyq

set_option maxHeartbeats 1600000 in
theorem UpperTheory.Gal.InertialTypesAlt.G.core :
    UpperTheory.Gal.InertialTypesAlt.G.Core := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ π P V hC hP hW v w hv iF bF iE bE mF mE hmF hmE τ τ' hτ hτ' s₀ I₀ hs₀ hI₀
  obtain rfl := bF.measurable_eq
  obtain rfl := bE.measurable_eq
  letI : ∀ x : Pl E, MeasurableSpace (Gw n x) := fun _ => borel _
  haveI : ∀ x : Pl E, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩
  letI : ∀ x : Pl F, MeasurableSpace (Gw n x) := fun _ => borel _
  haveI : ∀ x : Pl F, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩
  let μF : Measure (normOneGL F n) := Measure.haar
  have hV := hC.summand
  obtain ⟨-, hAtE, -, -, hnp, θ, hθ, hst⟩ := carryLift F E σ hσ hp n hn μE μF
  obtain ⟨Λ, t, hAt⟩ := hAtE V hV
  have hVθ := (hst P V hC).1 hP
  have hOffA : OffAll F n Λ t := by
    by_contra hc
    exact hnp _ V Λ t hC hAt (famParts F E σ hσ hp n hn
      (fun m hm _ => liftAll (liftStep (coreLift UpperTheory.ConvolutionTheory.ci GM.gm)) F E σ hσ hp m hm) Λ t hc)
  have hocc' : Occurs μE V w.1 τ' := (occursIff E n μE V hV w.1 τ').2 ((Dp.locIff E n μE P V hC w.1 τ').1 hτ')
  obtain ⟨S, q, w₀, hvS, hqS, hq, hunr, hsph, hS'⟩ := pickS F E σ hσ hp n hn μE V Λ t hV hAt v
  obtain ⟨-, -, hne, huniq, -⟩ := places F E hp
  obtain ⟨T, hTS, -, htyped, hrank, c, f₀, UF, -, hL⟩ := tyEx F E σ hσ hp n hn μE V hV q w₀ hq S hqS hunr hsph
    fun u => (hne u).some
  obtain rfl : w = T.mk' v := huniq v hv _ _
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 htyped
  obtain ⟨k, hk, D, s, hs, νE, jE, νF, jF, b, a, aE, aF, hposition, harch, hAE, hAF, hpair, hua⟩ :=
    pickInf F E σ hσ hp n hn μE μF u hu0
  have heig : ∀ x, V ⊓ eigL μE x (T.J x) (T.χ x) ≠ ⊥ := fun x =>
    (Submodule.ne_bot_iff _).2 ⟨u, ⟨hu.1, (Submodule.mem_iInf _).1 hu.2 x⟩, hu0⟩
  have hmk : ∀ y ∈ S, (T.mk' y).1 ≠ w₀.1 := fun y hy h =>
    hqS ((by rw [← under_eq (T.mk' y), h, under_eq w₀] : y = q) ▸ hy)
  have hcoI : CO (GLnLocal.iwahori (w₀.1.adicCompletion E) n) := T.at_q w₀ ▸ T.co w₀.1
  obtain ⟨m, hm, hm1, hm2⟩ : ∃ m : ∀ x : Pl E, Measure (Gw n x), (∀ x, (m x).IsHaarMeasure) ∧
      m w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) = 1 ∧ m (T.mk' v).1 = mE := by
    choose m₁ hm₁ _ using fun x : Pl E => haar_norm E n x
    obtain ⟨d, -, -, hd, hd1⟩ := scale (m₁ w₀.1) (hm₁ _) _ hcoI
    refine ⟨Function.update (Function.update m₁ w₀.1 (d • m₁ w₀.1)) (T.mk' v).1 mE, fun x => ?_, ?_, Function.update_self ..⟩
    · by_cases h : x = (T.mk' v).1
      · subst h; rw [Function.update_self]; exact hmE
      · rw [Function.update_of_ne h]
        by_cases h' : x = w₀.1
        · subst h'; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne h']; exact hm₁ x
    · rw [Function.update_of_ne (hmk v hvS).symm, Function.update_self]; exact hd1
  obtain ⟨d, hd0, hdT, hdH, hd1⟩ := scale mF hmF (GLnLocal.integralGL (v.adicCompletion F) n)
    ⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩
  obtain ⟨m', hm', hm2'⟩ : ∃ m : ∀ x : Pl F, Measure (Gw n x), (∀ x, (m x).IsHaarMeasure ∧
      m x (GLnLocal.integralGL (x.adicCompletion F) n) = 1) ∧ m v = d • mF := by
    choose m₁ hm₁ using fun x : Pl F => haar_norm F n x
    refine ⟨Function.update m₁ v (d • mF), fun x => ?_, Function.update_self ..⟩
    by_cases h : x = v
    · subst h; rw [Function.update_self]; exact ⟨hdH, hd1⟩
    · rw [Function.update_of_ne h]; exact hm₁ x
  have hoccE : ∀ x : Pl E, ∃ ρ : SmIrr (Gw n x), Occurs μE V x ρ := fun x => by
    haveI := hm x
    exact (occursBasics E n μE V x (m x) hV).1
  obtain ⟨X, hX, hXv⟩ : ∃ X : ∀ y : Pl F, Σ ρ : SmIrr (Gw n (T.mk' y).1), (Gw n (T.mk' y).1 →* Gw n (T.mk' y).1) × (ρ.V ≃ₗ[ℂ] ρ.V),
      (∀ y, Occurs μE V (T.mk' y).1 (X y).1 ∧ (¬ GM.Split E y → IsLocGal σ (T.mk' y) (X y).2.1 ∧
        ∀ g x, (X y).2.2 ((X y).1.ρ g x) = (X y).1.ρ ((X y).2.1 g) ((X y).2.2 x))) ∧ X v = ⟨τ', s₀, I₀⟩ := by
    have hex : ∀ y : Pl F, ∃ Y : Σ ρ : SmIrr (Gw n (T.mk' y).1), (Gw n (T.mk' y).1 →* Gw n (T.mk' y).1) × (ρ.V ≃ₗ[ℂ] ρ.V),
        Occurs μE V (T.mk' y).1 Y.1 ∧ (¬ GM.Split E y → IsLocGal σ (T.mk' y) Y.2.1 ∧
          ∀ g x, Y.2.2 (Y.1.ρ g x) = Y.1.ρ (Y.2.1 g) (Y.2.2 x)) := fun y => by
      obtain ⟨ρ, hρ⟩ := hoccE (T.mk' y).1
      by_cases hy : GM.Split E y
      · exact ⟨⟨ρ, MonoidHom.id _, LinearEquiv.refl _ _⟩, hρ, fun h => absurd hy h⟩
      · obtain ⟨-, g, hg, hg'⟩ := locGalEx F E σ hp n y (T.mk' y) hy
        obtain ⟨J, hJ⟩ := (hg' μE θ hθ).2 V ρ hV hVθ hρ
        exact ⟨⟨ρ, g, J⟩, hρ, fun _ => ⟨hg, hJ⟩⟩
    choose X₁ hX₁ using hex
    refine ⟨Function.update X₁ v ⟨τ', s₀, I₀⟩, fun y => ?_, Function.update_self ..⟩
    by_cases h : y = v
    · subst h; rw [Function.update_self]; exact ⟨hocc', fun _ => ⟨hs₀, hI₀⟩⟩
    · rw [Function.update_of_ne h]; exact hX₁ y
  obtain ⟨τ₀, hτ₀⟩ := hoccE w₀.1
  obtain ⟨y₀, hy₀, hY⟩ := (twistY F E σ hσ k n hk hn μE θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq T V hV hVθ hrank).1
    ⟨u, hu, hua⟩
  obtain ⟨cE, hcE, hE⟩ := termEV F E σ hσ k n hk (hk ▸ hp) hn μE θ hθ D s hs hposition νE νF b a aE aF harch m hm q w₀ hq T V hV hVθ
    (fun y hy hy' x => ⟨hrank y hy hy' x, heig _⟩) τ₀ (fun y => (X y).1) (fun y => (X y).2.1) (fun y => (X y).2.2) hτ₀
    (fun y _ => (hX y).1) (fun y _ hy => (hX y).2 hy) y₀ hy₀
  have hYZ : T.Y μE V (fun i => OComponent μE (s i) (hs i) νF a) y₀ ≤ T.Z μE V (fun i => OComponent μE (s i) (hs i) νF a) y₀ := by
    unfold Ty.Y Ty.Z Ty.typed
    exact inf_le_inf_left _ (le_iInf₂ fun w _ => iInf_le _ w)
  replace hcE := hcE fun h => hY (le_bot_iff.1 (h ▸ hYZ))
  have hfixS : ∀ y, GM.Split E y → ∀ x : PlacesOver E y, V ⊓ fixL μE x.1 (T.J x.1) ≠ ⊥ := fun y hy x => by
    have h1 := heig x.1
    have h2 := T.chr x.1
    rw [T.triv y hy x] at h1 h2
    rwa [(eigBasic E n μE _ _ _ (T.co _) h2).2.1] at h1
  obtain ⟨ν, hν⟩ := goodEx n hn
  obtain ⟨Z₀, hZ0, hZ₀, hZ⟩ : ∃ Z : Multiset ℂ, 0 ∉ Z ∧ Z ≠ 0 ∧ ∀ j : ℕ,
      HasTrace (m w₀.1) τ₀.ρ ((GM.iwCoset w₀.1 (j • ν)).indicator 1) (Z.map (· ^ j)).sum := by
    haveI := hm w₀.1
    obtain ⟨hfx, -, -, -, -, A, hA, hfin, -⟩ := unitTrace E n μE V hV w₀.1 (m w₀.1) (hm _) τ₀ _ hτ₀ hcoI
      (T.at_q w₀ ▸ hfixS q hq w₀)
    have fd := fd_fixed (m w₀.1) τ₀.ρ _ hcoI.2.measurableSet hm1 A hA hfin
    obtain ⟨Z, h0, hcard, hZ⟩ := iwPow E n w₀.1 (m w₀.1) hm1 τ₀ ν hν.1.antitone fd
    refine ⟨Z, h0, ?_, hZ⟩
    rintro rfl
    exact hfx (Submodule.finrank_eq_zero.1 (by simpa using hcard.symm))
  let ψ : ∀ y : Pl F, Gw n (T.mk' y).1 → ℂ := fun y =>
    (T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator fun x => conj (T.χ (T.mk' y).1 x)
  have hψs : ∀ y, GM.Split E y → ψ y = (T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator 1 := fun y hy => by
    simp only [ψ, T.triv y hy (T.mk' y)]
    congr 1
    funext x
    simp
  have hunit := fun y (hy : GM.Split E y) =>
    unitTrace E n μE V hV (T.mk' y).1 (m _) (hm _) (X y).1 (T.J _) (hX y).1 (T.co _) (hfixS y hy _)
  have hbase := fun y (hyS : y ∈ T.S) (hy : ¬ GM.Split E y) =>
    baseTw F E σ hσ hp n hn μE V hV q w₀ T y (fun x => huniq y hy _ _) (hrank y hyS hy _) (heig _) (m _) (hm _) (X y).1 (X y).2.1
      (X y).2.2 (hX y).1 ((hX y).2 hy).1 ((hX y).2 hy).2
  have htb : ∀ y : Pl F, ∃ z : ℂ, y ∈ T.S → z ≠ 0 ∧ (GM.Split E y → HasTrace (m _) (X y).1.ρ (ψ y) z) ∧
      (¬ GM.Split E y → HasTwTrace (m _) (X y).1 (X y).2.2 (ψ y) z) := fun y => by
    by_cases hyS : y ∈ T.S
    · by_cases hy : GM.Split E y
      · obtain ⟨z, h1, h2⟩ := (hunit y hy).2.2.2
        exact ⟨z, fun _ => ⟨h1, fun _ => hψs y hy ▸ h2, fun h => absurd hy h⟩⟩
      · obtain ⟨z, h1, h2⟩ := (hbase y hyS hy).2
        exact ⟨z, fun _ => ⟨h1, fun h => absurd h hy, fun _ => h2⟩⟩
    · exact ⟨0, fun h => absurd h hyS⟩
  choose tb htb using htb
  obtain ⟨L₁, hfit, -, -, -⟩ := hL ψ fun y hy => by
    have hy' := (Finset.mem_filter.1 hy).2
    rw [hψs y hy']
    exact ⟨(hunit y hy').2.1, (hunit y hy').2.2.1⟩
  have hL₁S : L₁.S = S := hfit.S_eq.trans hTS
  have hvT : v ∈ T.S := hTS ▸ hvS
  obtain ⟨⟨e, he⟩, hint, -⟩ := cmpIso F E n v (T.mk' v) fun x => huniq v hv _ _
  have hφn : ∀ y ∈ T.S, ¬ GM.Split E y → L₁.φ y = fun g => ψ y (GM.cmp (T.mk' y) g) := fun y hy hy' => by
    rw [hfit.nonsplit y hy hy', (cmpIso F E n y (T.mk' y) fun x => huniq y hy' _ _).2.2]
  obtain ⟨κ, hκ, hG⟩ := GM.gm F E σ hσ hp n hn μE μF θ hθ q w₀ hq νE νF aE aF 1 one_pos hAE hAF hpair
  set SF : Set (Pl F) := {y | y ∈ S ∨ y = q} with hSF
  set SE : Set (Pl E) := {y | y.under (𝓞 F) ∈ SF} with hSE
  have hSFf : SF.Finite := (S.finite_toSet.union (Set.finite_singleton q)).subset fun y hy => hy
  have hSEf : SE.Finite := by
    obtain ⟨𝔢, -, h𝔢, -⟩ := hG L₁ ν hν
    have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hL₁S]; rfl
    exact heS ▸ 𝔢.finS
  have key : ∀ U : Subgroup (Gw n v), IsOpen (U : Set (Gw n v)) → U ≤ GLnLocal.integralGL (v.adicCompletion F) n →
      ∃ B : ℕ → ℂ, ∀ (φ : Gw n (T.mk' v).1 → ℂ) (f : Gw n v → ℂ) (c₁ z r : ℂ), Test φ → Test f →
        GM.MatchAt σ v c₁ (fun g => φ (GM.cmp (T.mk' v) g)) f → (∀ g, f g ≠ 0 → g ∈ normSet E n v) → HasTrace mF τ.ρ f z →
        HasTwTrace mE τ' I₀ φ r → (∀ x ∈ U, ∀ g, f (x * g) = f g) →
        ∀ᶠ j : ℕ in atTop, cE * (Z₀.map (· ^ j)).sum * (∏ y ∈ T.S.erase v, tb y) * r = B j * (c₁ * z) := by
    intro U hU1 hU2
    obtain ⟨ι, _, V₀, ρ, bF, Z, hι, hF⟩ := sideSum F E σ n (Module.finrank F E) hn μF νF m' hm' aF q w₀ S
      (Function.update L₁.UF v U) ν hν.1.antitone
      (fun V₀ => ∃ Λ' t', At μF SF V₀ Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ y ∉ SE, t y = bcSat t' y) (y₀ ^ (k + 1)) (pow_pos hy₀ _)
    have hs₁ : ∀ i (y : Pl F), ∃ z : ℂ, y ∈ S → HasTrace (m' y) (ρ i y).ρ (L₁.f y) z := fun i y => by
      by_cases hy : y ∈ S
      · haveI := (hm' y).1
        have ht := L₁.test y (hL₁S ▸ hy)
        obtain ⟨z, hz⟩ := (occursBasics F n μF (V₀ i) y (m' y) (hι i).1).2.2 _ ((hι i).2.2.2 y) (L₁.f y) ⟨ht.2.2.1, ht.2.2.2⟩
        exact ⟨z, fun _ => hz⟩
      · exact ⟨0, fun h => absurd h hy⟩
    choose s₁ hs₁ using hs₁
    refine ⟨fun j => (κ * ∏ y ∈ S.erase v, L₁.c y) * (d.toReal : ℂ) *
      ∑ i, bF i * ((Z i).map (· ^ j)).sum * ∏ y ∈ S.erase v, s₁ i y, fun φ f c₁ z r hφ hf hmat hsup hz hr hinv => ?_⟩
    obtain ⟨U', hU'1, hU'2, hU'3⟩ := levEx _ (GLnLocal.integralGL ((T.mk' v).1.adicCompletion E) n) φ
      (GLnLocal.isOpen_integralGL _ n) (small n _) hφ
    have hce : (fun g => GM.cmp (n := n) (T.mk' v) g) = e := funext fun g => (he g).symm
    have hφt : Test fun g => φ (GM.cmp (T.mk' v) g) := by
      have : (fun g => φ (GM.cmp (T.mk' v) g)) = φ ∘ e.toHomeomorph := funext fun g => congrArg φ (he g).symm
      rw [this]
      exact ⟨hφ.1.comp_continuous e.continuous, hφ.2.comp_homeomorph _⟩
    obtain ⟨L, l1, l2, l3, l4, l5, l6⟩ := updLoc L₁ v (hL₁S ▸ hvS) _ f c₁ (U'.comap (GM.cmp (T.mk' v))) U hφt hf hmat
      ⟨hU'1.preimage (show Continuous fun g => GM.cmp (n := n) (T.mk' v) g from hce ▸ e.continuous),
        fun g hg => (hint g).2 (hU'2 hg), hU1, hU2⟩
      ⟨fun x hx g => by rw [map_mul]; exact hU'3 _ hx _, hinv⟩
    have hLS : L.S = S := l1.trans hL₁S
    have hns : ∀ y ∈ T.sp, y ≠ v := fun y hy h => hv (h ▸ (Finset.mem_filter.1 hy).2)
    have hfv : FitsV T L (Function.update ψ v φ) := by
      refine ⟨l1.trans hfit.S_eq, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy hy' g => ?_⟩
      · by_cases h : y = v
        · subst h; rw [Function.update_self]; exact hφ
        · rw [Function.update_of_ne h]
          by_cases hy' : GM.Split E y
          · exact (hfit.test y (Finset.mem_filter.2 ⟨hy, hy'⟩)).1
          · exact (hbase y hy hy').1
      · rw [Function.update_of_ne (hns y hy)]; exact (hfit.test y hy).2
      · rw [l2, l5, Function.update_of_ne (hns y hy), Function.update_of_ne (hns y hy), Function.update_of_ne (hns y hy)]
        exact hfit.split y hy
      · rw [l2]
        by_cases h : y = v
        · subst h; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne h, Function.update_of_ne h, hφn y hy hy']
    obtain ⟨𝔢, 𝔣, h𝔢, h𝔣, hgeo⟩ := hG L ν hν
    have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hLS]; rfl
    have hfS : 𝔣.S = SF := Set.ext fun y => by rw [h𝔣.2.2.1, hLS]; rfl
    obtain ⟨hAt', hc1, hc2⟩ := hS' 𝔢.S fun y => by rw [h𝔢.2.2.1, hLS]
    have hoff : OffFam F n 𝔢.S 𝔣.S Λ t := by
      rw [heS, hfS]
      exact hOffA SF hSFf
    have hz' : ∀ i, HasTrace (m' v) (ρ i v).ρ f ((d.toReal : ℂ) * z) := fun i => by
      obtain ⟨Λ', t', hA, hΛ, ht⟩ := (hι i).2.1
      rw [hm2']
      exact fibTrace F E σ hσ hp n hn μE μF π P V Λ t hC hAt hW (V₀ i) Λ' t' (hι i).1 ⟨SF, hSFf, hA⟩ hΛ
        (Filter.mem_of_superset hSEf.compl_mem_cofinite fun y hy => ht y hy) v _ τ _ hτ ((hι i).2.2.2 v) f _ hsup
        (((trBasic _ mF τ (LinearEquiv.refl _ _) f).2.2 d hdT).1 z hz)
    filter_upwards [UpperTheory.ConvolutionTheory.ci F E n _ hn hp.pos μE μF θ 𝔢 𝔣 _ hgeo Λ t hc1 hc2 hoff (y₀ ^ (k + 1)) (pow_pos hy₀ _)] with j hj
    rw [oneTerm E n _ hn μE θ 𝔢 V Λ t hV hVθ hAt' _ j,
      hE L _ hfv ν _ 𝔢 hν.1.antitone h𝔢 j _ (Function.update tb v r) (hZ j) (fun y hy => by
        rw [Function.update_of_ne (hns y hy), Function.update_of_ne (hns y hy)]
        exact (htb y (Finset.mem_filter.1 hy).1).2.1 (Finset.mem_filter.1 hy).2) (fun y hy hy' => by
        by_cases h : y = v
        · subst h
          rw [Function.update_self, Function.update_self, hm2]
          have : ∀ Y : Σ ρ : SmIrr (Gw n (T.mk' y).1), (Gw n (T.mk' y).1 →* Gw n (T.mk' y).1) × (ρ.V ≃ₗ[ℂ] ρ.V),
              Y = ⟨τ', s₀, I₀⟩ → HasTwTrace mE Y.1 Y.2.2 φ r := by rintro _ rfl; exact hr
          exact this _ hXv
        · rw [Function.update_of_ne h, Function.update_of_ne h]; exact (htb y hy).2.2 hy'), heS, hfS,
      hF L 𝔣 hLS (fun y _ => by rw [l6]) h𝔣 (fun i => Function.update (s₁ i) v ((d.toReal : ℂ) * z)) (fun i y hy => by
        rw [l3]
        by_cases h : y = v
        · subst h; rw [Function.update_self, Function.update_self]; exact hz' i
        · rw [Function.update_of_ne h, Function.update_of_ne h]; exact hs₁ i y hy) j, hLS, l4,
      Finset.prod_update_of_mem hvT, Finset.prod_update_of_mem hvS] at hj
    simp only [Finset.prod_update_of_mem hvS, Finset.sdiff_singleton_eq_erase] at hj
    have e2 : ∑ i, bF i * ((Z i).map (· ^ j)).sum * ((d.toReal : ℂ) * z * ∏ y ∈ S.erase v, s₁ i y) =
        (d.toReal : ℂ) * z * ∑ i, bF i * ((Z i).map (· ^ j)).sum * ∏ y ∈ S.erase v, s₁ i y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e2] at hj
    linear_combination hj
  have ht₁ := L₁.test v (hL₁S ▸ hvS)
  obtain ⟨hc1, hc2⟩ := matchCut F E σ hσ hp n hn v (L₁.c v) (L₁.φ v) (L₁.f v)
  have hb1 := hc2 ⟨ht₁.2.2.1, ht₁.2.2.2⟩
  have hb2 : GM.MatchAt σ v (L₁.c v) (fun g => ψ v (GM.cmp (T.mk' v) g)) ((normSet E n v).indicator (L₁.f v)) := by
    rw [← hφn v hvT hv]
    exact @hc1 (@GM.Loc.mat _ _ _ _ _ _ _ _ _ _ _ L₁ v (hL₁S ▸ hvS))
  have hb3 : ∀ g, (normSet E n v).indicator (L₁.f v) g ≠ 0 → g ∈ normSet E n v := fun g hg => Set.mem_of_indicator_ne_zero hg
  obtain ⟨z₀, hz₀⟩ := trEx F n hn π v mF hmF τ hτ _ hb1
  have hr₀ : HasTwTrace mE τ' I₀ (ψ v) (tb v) := by
    have h := (htb v hvT).2.2 hv
    rw [hm2] at h
    have : ∀ Y : Σ ρ : SmIrr (Gw n (T.mk' v).1), (Gw n (T.mk' v).1 →* Gw n (T.mk' v).1) × (ρ.V ≃ₗ[ℂ] ρ.V),
        Y = ⟨τ', s₀, I₀⟩ → HasTwTrace mE Y.1 Y.2.2 (ψ v) (tb v) → HasTwTrace mE τ' I₀ (ψ v) (tb v) := by rintro _ rfl h; exact h
    exact this _ hXv h
  have hr0 := (htb v hvT).1
  have main : ∀ (φ : Gw n (T.mk' v).1 → ℂ) (f : Gw n v → ℂ) (c₁ z r : ℂ), Test φ → Test f →
      GM.MatchAt σ v c₁ (fun g => φ (GM.cmp (T.mk' v) g)) f → (∀ g, f g ≠ 0 → g ∈ normSet E n v) → HasTrace mF τ.ρ f z →
      HasTwTrace mE τ' I₀ φ r → L₁.c v * z₀ ≠ 0 ∧ r * (L₁.c v * z₀) = tb v * (c₁ * z) := by
    intro φ f c₁ z r hφ hf hmat hsup hz hr
    obtain ⟨U₁, a1, a2, a3⟩ := levEx _ _ f (GLnLocal.isOpen_integralGL (v.adicCompletion F) n) (small n v) hf
    obtain ⟨U₂, b1, b2, b3⟩ := levEx _ U₁ _ a1 (small n v) hb1
    obtain ⟨B, hB⟩ := key U₂ b1 (b2.trans a2)
    obtain ⟨j, h0, h1, h2⟩ := ((powNe Z₀ hZ₀ hZ0).and_eventually ((hB φ f c₁ z r hφ hf hmat hsup hz hr fun x hx => a3 x (b2 hx)).and
      (hB (ψ v) _ _ z₀ (tb v) (hbase v hvT hv).1 hb1 hb2 hb3 hz₀ hr₀ b3))).exists
    have hA : cE * (Z₀.map (· ^ j)).sum * ∏ y ∈ T.S.erase v, tb y ≠ 0 :=
      mul_ne_zero (mul_ne_zero hcE h0) (Finset.prod_ne_zero_iff.2 fun y hy => (htb y (Finset.mem_of_mem_erase hy)).1)
    refine ⟨fun h => mul_ne_zero hA hr0 (by rw [h2, h, mul_zero]), mul_left_cancel₀ hA ?_⟩
    linear_combination (L₁.c v * z₀) * h1 - (c₁ * z) * h2
  have hne0 := (main (ψ v) _ _ z₀ (tb v) (hbase v hvT hv).1 hb1 hb2 hb3 hz₀ hr₀).1
  refine ⟨tb v / (L₁.c v * z₀), div_ne_zero hr0 hne0, fun φ f c₁ z hφ hf hmat hsup hz => ?_⟩
  haveI := hmE
  obtain ⟨z', hz'⟩ := (occursBasics E n μE V (T.mk' v).1 mE hV).2.2 τ' hocc' φ hφ
  obtain ⟨r, hr⟩ := (trBasic _ mE τ' I₀ φ).1 z' hz'
  have h := (main φ f c₁ z r hφ hf hmat hsup hz hr).2
  have : tb v / (L₁.c v * z₀) * c₁ * z = r := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hne0, h]; ring
  rw [this]
  exact hr
