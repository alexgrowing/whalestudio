import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace TorusPowerExponential

section Loc

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)

theorem torusPow_add (x y : Fin n → ℤ) :
    Iwasawa.torusPow F n (x + y) = Iwasawa.torusPow F n x * Iwasawa.torusPow F n y := by
  simp only [Iwasawa.torusPow, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

theorem conj_mem (x : Fin n → ℤ) {u : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n) :
    Iwasawa.torusPow F n x * u * (Iwasawa.torusPow F n x)⁻¹ ∈ Iwasawa.unipotent F n :=
  Iwasawa.diagGL_mul_mul_inv_mem_unipotent F n hu _

theorem exp_torus_mul (x : Fin n → ℤ) (h : GL (Fin n) F) :
    Iwasawa.iwasawaExponent F n (Iwasawa.torusPow F n x * h) = x + Iwasawa.iwasawaExponent F n h := by
  obtain ⟨u, hu, κ, hκ, e⟩ := Iwasawa.exists_eq_mul_torusPow_iwasawaExponent F n h
  have key : Iwasawa.torusPow F n x * h = (Iwasawa.torusPow F n x * u * (Iwasawa.torusPow F n x)⁻¹) *
      Iwasawa.torusPow F n (x + Iwasawa.iwasawaExponent F n h) * κ := by
    rw [torusPow_add]
    conv_lhs => rw [e]
    group
  rw [key, Iwasawa.iwasawaExponent_eq F n (conj_mem F n x hu) hκ]

theorem torusPow_zero : Iwasawa.torusPow F n 0 = 1 := by
  simpa using torusPow_add F n 0 0

end Loc

section Glob

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem countable_pl : Countable (Pl E) := by
  classical
  haveI : Countable (𝓞 E) := (RingOfIntegers.basis E).repr.toEquiv.injective.countable
  let f : Pl E → Finset (𝓞 E) := fun v ↦ (IsNoetherian.noetherian v.asIdeal).choose
  refine Function.Injective.countable (f := f) fun v w h ↦ ?_
  have hv := (IsNoetherian.noetherian v.asIdeal).choose_spec
  have hw := (IsNoetherian.noetherian w.asIdeal).choose_spec
  ext1
  rw [← hv, ← hw]
  exact congrArg (fun s : Finset (𝓞 E) ↦ Submodule.span (𝓞 E) (s : Set (𝓞 E))) h

def A (S : Finset (Pl E)) (l : Off E S →₀ (Fin k → ℤ)) : Set (GA E k) :=
  {g | ∀ w : Off E S, Iwasawa.iwasawaExponent _ k (cLoc w.1 g) = l w}

theorem A_zero (S : Finset (Pl E)) : A (k := k) S 0 = G0 S := by
  ext g
  simp only [A, G0, Set.mem_setOf_eq, Finsupp.coe_zero, Pi.zero_apply]
  exact ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w.1 w.2⟩

theorem A_cover (S : Finset (Pl E))
    (hfin : ∀ g : GA E k, {w | Iwasawa.iwasawaExponent _ k (cLoc w g) ≠ 0}.Finite) (g : GA E k) :
    ∃ l, g ∈ A S l :=
  ⟨Finsupp.ofSupportFinite (fun w : Off E S => Iwasawa.iwasawaExponent _ k (cLoc w.1 g))
    ((hfin g).preimage Subtype.val_injective.injOn), fun w => rfl⟩

theorem A_disj (S : Finset (Pl E)) : Pairwise (Function.onFun Disjoint (A (k := k) S)) := by
  intro l l' hne
  exact Set.disjoint_left.2 fun g h h' => hne (Finsupp.ext fun w => (h w).symm.trans (h' w))

theorem A_closed (S : Finset (Pl E))
    (hcl : ∀ (w : Pl E) (l : Fin k → ℤ), IsClopen {g : GA E k | Iwasawa.iwasawaExponent _ k (cLoc w g) = l})
    (l : Off E S →₀ (Fin k → ℤ)) : IsClosed (A S l) := by
  have : A S l = ⋂ w : Off E S, {g : GA E k | Iwasawa.iwasawaExponent _ k (cLoc w.1 g) = l w} := by
    ext; simp [A]
  rw [this]
  exact isClosed_iInter fun w => (hcl w.1 (l w)).isClosed

theorem cLoc_unip (u : GA E k) (hu : UU 0 u) (w : Pl E) : cLoc w u ∈ Iwasawa.unipotent _ k := by
  refine ⟨fun i c hci => ?_, fun i => ?_⟩
  · change ((pLoc E w).comp (pFin E)) (u.val i c) = 0
    rw [hu.1 i c hci, map_zero]
  · change ((pLoc E w).comp (pFin E)) (u.val i i) = 1
    rw [hu.2.1 i, map_one]

theorem A_mul (S : Finset (Pl E)) (l : Off E S →₀ (Fin k → ℤ)) (u g : GA E k) (hu : UU 0 u) :
    u * g ∈ A S l ↔ g ∈ A S l := by
  have h := fun w : Pl E => Iwasawa.iwasawaExponent_mul_of_mem_unipotent _ k (cLoc_unip u hu w) (cLoc w g)
  simp only [A, Set.mem_setOf_eq, map_mul, h]

theorem A_tr (S : Finset (Pl E))
    (hloc : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), cLoc w (fl k w u : GA E k) = u)
    (hoff : ∀ (w v : Pl E) (u : GL (Fin k) (w.adicCompletion E)), v ≠ w → cLoc v (fl k w u : GA E k) = 1)
    (l : Off E S →₀ (Fin k → ℤ)) (w : Off E S) (hw : l w = 0) (x : Fin k → ℤ) (g : GA E k) :
    fl k w.1 (Iwasawa.torusPow _ k x) * g ∈ A S (Finsupp.single w x + l) ↔ g ∈ A S l := by
  simp only [A, Set.mem_setOf_eq, map_mul]
  have key : ∀ v : Off E S, (Iwasawa.iwasawaExponent _ k (cLoc v.1 (fl k w.1 (Iwasawa.torusPow _ k x)) *
      cLoc v.1 g) = (Finsupp.single w x + l) v ↔ Iwasawa.iwasawaExponent _ k (cLoc v.1 g) = l v) := by
    intro v
    by_cases hv : v = w
    · subst hv
      rw [hloc, exp_torus_mul, Finsupp.add_apply, Finsupp.single_eq_same, hw, add_zero]
      constructor
      · intro h; simpa using h
      · intro h; rw [h, add_zero]
    · have e1 : (Finsupp.single w x + l) v = l v := by simp [Finsupp.single_apply, Ne.symm hv]
      rw [hoff w.1 v.1 _ (fun h => hv (Subtype.ext h)), one_mul, e1]
  exact forall_congr' key

theorem Phi_tr (S : Finset (Pl E)) (Φ : GA E k → ℂ) (a : Off E S → (Fin k → ℤ) → ℂ) (hlaw : LawOff S Φ a)
    (ha0 : ∀ w, a w 0 = 1)
    (hcomm : ∀ (w : Pl E) (g : GA E k), cLoc w g = 1 → ∀ u, g * fl k w u = fl k w u * g)
    (hdec : ∀ (w : Pl E) (g : GA E k), ∃ g' : GA E k, cLoc w g' = 1 ∧ g = g' * fl k w (cLoc w g))
    (w : Off E S) (x : Fin k → ℤ) (g : GA E k) (hg : Iwasawa.iwasawaExponent _ k (cLoc w.1 g) = 0) :
    Φ (fl k w.1 (Iwasawa.torusPow _ k x) * g) = a w x * Φ g := by
  obtain ⟨g', h1, hg'⟩ := hdec w.1 g
  obtain ⟨u, hu, κ, hκ, e⟩ := Iwasawa.exists_eq_mul_torusPow_iwasawaExponent _ k (cLoc w.1 g)
  rw [hg] at e
  have h0 : Φ g = Φ g' := by
    rw [hg', e, hlaw w g' h1 u hu κ hκ 0, ha0, mul_one]
  have h2 : fl k w.1 (Iwasawa.torusPow _ k x) * g = g' * fl k w.1
      ((Iwasawa.torusPow _ k x * u * (Iwasawa.torusPow _ k x)⁻¹) * Iwasawa.torusPow _ k x * κ) := by
    conv_lhs => rw [hg', e]
    rw [← mul_assoc, ← hcomm w.1 g' h1, mul_assoc, ← map_mul, torusPow_zero, mul_one]
    congr 2
    group
  rw [h2, hlaw w g' h1 _ (conj_mem _ k x hu) κ hκ x, h0, mul_comm]

end Glob

end TorusPowerExponential

theorem torus_exponential_of_open : jumpWindows.G0 → C0 → C1 → C2 := by
  intro hG hC0 hC1 E _ _ _ k μ _ hk β hβ S Φ a hΦm hΦu hlaw ha0 hint
  obtain ⟨-, -, -, hloc, hoff, -, -, hcomm, -⟩ := hG E k
  obtain ⟨-, -, -, -, hfin, hcl, hdec⟩ := hC0 E k S
  haveI := TorusPowerExponential.countable_pl (E := E)
  have hmeas : ∀ l, MeasurableSet (TorusPowerExponential.A (k := k) S l) := fun l => (TorusPowerExponential.A_closed S hcl l).measurableSet
  let c : Off E S → (Fin k → ℤ) → ℂ := fun w x => (nq w : ℂ) ^ rhoPair x * a w x
  have hc0 : ∀ w, c w 0 = 1 := fun w => by simp [c, rhoPair, ha0]
  have hstep : ∀ (f : Off E S →₀ (Fin k → ℤ)) (w : Off E S) (x : Fin k → ℤ), f w = 0 →
      ∫ g in TorusPowerExponential.A S (Finsupp.single w x + f), Φ g ∂μ.withDensity β =
        c w x * ∫ g in TorusPowerExponential.A S f, Φ g ∂μ.withDensity β := by
    intro f w x hw
    have hUU : ∀ u, UU 0 u → ∀ g, (TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ (u * g) =
        (TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ g := by
      intro u hu g
      by_cases hg : g ∈ TorusPowerExponential.A S (Finsupp.single w x + f)
      · rw [Set.indicator_of_mem ((TorusPowerExponential.A_mul S _ u g hu).2 hg), Set.indicator_of_mem hg, hΦu u hu g]
      · rw [Set.indicator_of_notMem (mt (TorusPowerExponential.A_mul S _ u g hu).1 hg), Set.indicator_of_notMem hg]
    obtain ⟨-, hE⟩ := hC1 E k μ hk β hβ w.1 x ((TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ)
      (hΦm.indicator (hmeas _))
      hUU
      (hint.indicator (hmeas _))
    rw [← integral_indicator (hmeas _), hE, ← integral_indicator (hmeas _)]
    have hpt : ∀ g, (TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ
        (fl k w.1 (Iwasawa.torusPow (w.1.adicCompletion E) k x) * g) =
        a w x * (TorusPowerExponential.A S f).indicator Φ g := by
      intro g
      by_cases hg : g ∈ TorusPowerExponential.A S f
      · rw [Set.indicator_of_mem ((TorusPowerExponential.A_tr S hloc hoff f w hw x g).2 hg), Set.indicator_of_mem hg,
          TorusPowerExponential.Phi_tr S Φ a hlaw ha0 hcomm (fun w g => (hdec w g).imp fun g' h => ⟨h.1, h.2.1⟩) w x g
            ((hg w).trans hw)]
      · rw [Set.indicator_of_notMem (fun h => hg ((TorusPowerExponential.A_tr S hloc hoff f w hw x g).1 h)),
          Set.indicator_of_notMem hg, mul_zero]
    simp only [hpt, c, nq]
    rw [integral_const_mul, mul_assoc]
  have hclaim : ∀ l : Off E S →₀ (Fin k → ℤ), ∫ g in TorusPowerExponential.A S l, Φ g ∂μ.withDensity β =
      (∏ w ∈ l.support, c w (l w)) * ∫ g in G0 S, Φ g ∂μ.withDensity β := by
    intro l
    induction l using Finsupp.induction with
    | zero => simp [TorusPowerExponential.A_zero]
    | single_add w x f hwf hx ih =>
      have hfw : f w = 0 := Finsupp.notMem_support_iff.1 hwf
      change _ = Finsupp.prod (Finsupp.single w x + f) c * _
      change _ = Finsupp.prod f c * _ at ih
      have hdisj : Disjoint (Finsupp.single w x).support f.support := by
        refine Finset.disjoint_left.2 fun v hv hv' => hwf ?_
        rw [Finsupp.support_single_ne_zero _ hx, Finset.mem_singleton] at hv
        exact hv ▸ hv'
      rw [Finsupp.prod_add_index_of_disjoint hdisj, Finsupp.prod_single_index (hc0 w), hstep f w x hfw, ih]
      simp only [c]
      ring
  have hU : ⋃ l, TorusPowerExponential.A (k := k) S l = Set.univ := Set.iUnion_eq_univ_iff.2 (TorusPowerExponential.A_cover S hfin)
  have hs := hasSum_integral_iUnion hmeas (TorusPowerExponential.A_disj S) hint.integrableOn
  rw [hU, setIntegral_univ] at hs
  have hfun : (fun l => ∫ g in TorusPowerExponential.A S l, Φ g ∂μ.withDensity β) =
      fun l : Off E S →₀ (Fin k → ℤ) => (∏ w ∈ l.support, c w (l w)) * ∫ g in G0 S, Φ g ∂μ.withDensity β :=
    funext hclaim
  rw [hfun] at hs
  exact hs

end PositivityTheory.AdelicQuotientData

end
