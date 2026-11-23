import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep
open scoped ComplexConjugate

namespace PositivityTheory.RgJS

namespace RigidityLemmas

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def twS (χ : HChar E) (p : Σ a, CG E a) : Σ a, CG E a := ⟨p.1, p.2.twist χ⟩

omit [IsTotallyComplex E] in
theorem unrAt_inv {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) : (χ⁻¹).UnrAt w := fun x hx => by
  show (χ⁻¹).loc w x = 1
  rw [HChar.loc_inv, h x hx, inv_one]

theorem exists_fin {d : ℕ} (B : Multiset ℂˣ) (hB : Multiset.card B = d) :
    ∃ f : Fin d → ℂˣ, Finset.univ.val.map f = B := by
  obtain ⟨l, rfl⟩ : ∃ l : List ℂˣ, (l : Multiset ℂˣ) = B := Quot.exists_rep B
  have hl : l.length = d := by simpa using hB
  subst hl
  refine ⟨l.get, ?_⟩
  rw [Fin.univ_val_map, List.ofFn_get]

theorem sum_pow {d : ℕ} (f : Fin d → ℂˣ) (c : ℂˣ) (k : ℕ) :
    (((Finset.univ.val.map f).map (· * c)).map fun z : ℂˣ => ((z : ℂ)) ^ k).sum = ∑ a, ((f a : ℂ) * (c : ℂ)) ^ k := by
  rw [Multiset.map_map, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

end RigidityLemmas

open RigidityLemmas in
theorem jacquet_shalika_rigidity_of_bound : AbsRig → UnitEx → SatTw → DetOne → PrimeOff → RSU → GlobalTheory.Published.JacquetShalikaBound →
    GlobalTheory.Published.JacquetShalikaRigidity := by
  intro hAR hUE hST hDO hPO hRSU hBd E _ _ _ ι κ _ _ m m' π π' hm hm' hw
  classical
  obtain ⟨ν, hν, hdec⟩ := hUE E
  choose π0 t hu0 hπ0 using fun i => hdec (m i) (π i) (hm i)
  choose π0' t' hu0' hπ0' using fun j => hdec (m' j) (π' j) (hm' j)
  set u : ι → Σ a, CG E a := fun i => ⟨m i, π0 i⟩ with hu
  set u' : κ → Σ a, CG E a := fun j => ⟨m' j, π0' j⟩ with hu'
  let X : Type := ↥(Set.range u ∪ Set.range u')
  have : Fintype X := Fintype.ofFinite X
  have hX : ∀ x : X, 1 ≤ x.1.1 ∧ x.1.2.IsUnitary := by
    rintro ⟨p, (⟨i, rfl⟩ | ⟨j, rfl⟩)⟩
    · exact ⟨hm i, hu0 i⟩
    · exact ⟨hm' j, hu0' j⟩
  set S1 : Finset (HeightOneSpectrum (𝓞 E)) := (Filter.eventually_cofinite.1 hw).toFinset with hS1
  choose S0 hS0 using fun x y : X => hRSU E x.1.1 y.1.1 x.1.2 y.1.2 (hX x).1 (hX y).1 (hX x).2 (hX y).2
  set S : Finset (HeightOneSpectrum (𝓞 E)) := S1 ∪ Finset.univ.biUnion (fun p : X × X => S0 p.1 p.2) with hS
  have hP : ∀ w : Off E S, ∃ (B : ι → Multiset ℂˣ) (B' : κ → Multiset ℂˣ),
      (∀ i, (π i).HasSat w.1 (B i)) ∧ (∀ j, (π' j).HasSat w.1 (B' j)) ∧ ∑ i, B i = ∑ j, B' j := by
    intro w
    by_contra h
    exact w.2 (Finset.mem_union_left _ (by rw [hS1, Set.Finite.mem_toFinset]; exact h))
  choose B B' hB hB' hsum using hP
  have hsat0 : ∀ (w : Off E S) (i : ι), (π0 i).HasSat w.1 ((B w i).map (· * ((ν (t i))⁻¹).val w.1)) := by
    intro w i
    have h := hST E (m i) (π i) ((ν (t i))⁻¹) w.1 (B w i) (unrAt_inv ((hν (t i)).1 w.1)) (hB w i)
    rw [hπ0 i, ← CG.twist_mul, mul_inv_cancel, CG.twist_one] at h
    exact h
  have hsat0' : ∀ (w : Off E S) (j : κ), (π0' j).HasSat w.1 ((B' w j).map (· * ((ν (t' j))⁻¹).val w.1)) := by
    intro w j
    have h := hST E (m' j) (π' j) ((ν (t' j))⁻¹) w.1 (B' w j) (unrAt_inv ((hν (t' j)).1 w.1)) (hB' w j)
    rw [hπ0' j, ← CG.twist_mul, mul_inv_cancel, CG.twist_one] at h
    exact h
  have hex : ∀ (x : X) (w : Off E S), ∃ f : Fin x.1.1 → ℂˣ, x.1.2.HasSat w.1 (Finset.univ.val.map f) := by
    rintro ⟨p, (⟨i, rfl⟩ | ⟨j, rfl⟩)⟩ w
    · obtain ⟨f, hf⟩ := exists_fin _ (hsat0 w i).card
      exact ⟨f, hf ▸ hsat0 w i⟩
    · obtain ⟨f, hf⟩ := exists_fin _ (hsat0' w j).card
      exact ⟨f, hf ▸ hsat0' w j⟩
  choose α hα using hex
  let d : X → ℕ := fun x => x.1.1
  let A : ∀ x : X, Off E S → Fin (d x) → ℂ := fun x w a => (α x w a : ℂ)
  have hsub : ∀ x y : X, S0 x y ⊆ S := fun x y z hz =>
    Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(x, y), Finset.mem_univ _, hz⟩)
  have hSys : Sys nq X d A := by
    refine ⟨hPO E S, fun x => (hX x).1, fun x w a => ?_, fun x w => ?_, fun x y => ?_⟩
    · have h := (hBd E x.1.1 x.1.2 (hX x).2 w.1 _ (hα x w) (α x w a)
        (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2
      show ‖((α x w a : ℂˣ) : ℂ)‖ ≤ Real.sqrt ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)
      rw [Real.sqrt_eq_rpow]
      exact h.le
    · have h := hDO E x.1.1 x.1.2 w.1 _ (hX x).2 (hα x w)
      rw [← Finset.prod_eq_multiset_prod, Units.coe_prod] at h
      exact h
    · obtain ⟨F, σ₀, hF, hFe⟩ := hS0 x y S (hsub x y) (α x) (α y) (hα x) (hα y)
      refine ⟨F, σ₀, hF, fun σ hσ => ?_⟩
      rw [hFe σ hσ]
      by_cases hxy : x = y
      · subst hxy
        rw [if_pos rfl, if_pos rfl]
        rfl
      · rw [if_neg (fun h => hxy (Subtype.ext (by simpa using h))), if_neg hxy]
        rfl
  let x : ι → X × ℝ := fun i => (⟨u i, Or.inl ⟨i, rfl⟩⟩, t i)
  let y : κ → X × ℝ := fun j => (⟨u' j, Or.inr ⟨j, rfl⟩⟩, t' j)
  have hBi : ∀ (w : Off E S) (i : ι), B w i = (Finset.univ.val.map (α (x i).1 w)).map (· * (ν (t i)).val w.1) := by
    intro w i
    have h1 := hST E (m i) (π0 i) (ν (t i)) w.1 _ ((hν (t i)).1 w.1) (hα (x i).1 w)
    rw [← hπ0 i] at h1
    exact (hB w i).unique h1
  have hBj : ∀ (w : Off E S) (j : κ), B' w j = (Finset.univ.val.map (α (y j).1 w)).map (· * (ν (t' j)).val w.1) := by
    intro w j
    have h1 := hST E (m' j) (π0' j) (ν (t' j)) w.1 _ ((hν (t' j)).1 w.1) (hα (y j).1 w)
    rw [← hπ0' j] at h1
    exact (hB' w j).unique h1
  have hRel : Rel nq A x y := by
    intro w k
    let φ : Multiset ℂˣ →+ ℂ := Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom fun z : ℂˣ => (z : ℂ) ^ k)
    have hφ : ∀ M : Multiset ℂˣ, φ M = (M.map fun z : ℂˣ => (z : ℂ) ^ k).sum := fun M => rfl
    have h := congrArg φ (hsum w)
    rw [map_sum, map_sum] at h
    simp only [hφ, hBi, hBj, sum_pow] at h
    have ev : ∀ τ : ℝ, (((ν τ).val w.1 : ℂˣ) : ℂ) = (nq w : ℂ) ^ (-(τ : ℂ)) := fun τ => (hν τ).2.1 w.1
    simp only [ev] at h
    exact h
  obtain ⟨s, hs⟩ := hAR (Off E S) nq X d A hSys ι κ x y hRel
  refine ⟨s, fun i => ?_⟩
  have h1 : u i = u' (s i) := congrArg (fun z : X × ℝ => z.1.1) (hs i)
  have h2 : t i = t' (s i) := congrArg Prod.snd (hs i)
  rw [hπ0 i, hπ0' (s i)]
  show twS (ν (t i)) (u i) = twS (ν (t' (s i))) (u' (s i))
  rw [h1, h2]

end PositivityTheory.RgJS
