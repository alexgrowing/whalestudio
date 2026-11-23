import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PoinOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HdHd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.InclFacts

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} {G : Dr.Geo Γ V S d} {q : ℕ}

private theorem fLim_add {w w' : ℕ → G.Om q} (h : FLim G w) (h' : FLim G w') : FLim G fun j => w j + w' j := by
  intro s K hK hc
  have := (h s K hK hc).add (h' s K hK hc)
  rw [add_zero] at this
  exact this

private theorem fLim_zsmul (n : ℤ) {w : ℕ → G.Om q} (h : FLim G w) : FLim G fun j => n • w j := by
  intro s K hK hKc
  have h1 := (uniformContinuous_id.const_smul n).comp_tendstoUniformlyOn (h s K hK hKc)
  convert h1 using 1
  · funext k x
    simp
  · funext x
    simp

private theorem fLim_sum {ι : Type} (T : Finset ι) {w : ι → ℕ → G.Om q} (h : ∀ i ∈ T, FLim G (w i)) :
    FLim G fun j => ∑ i ∈ T, w i j := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro s K _ _
    simp only [Finset.sum_empty, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
      Filter.Eventually.of_forall fun _ x _ => by simpa using hε
  | insert i T hi ih =>
    have hsum := fLim_add (h i (Finset.mem_insert_self i T))
      (ih fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))
    simpa [Finset.sum_insert hi] using hsum

end

theorem UpperTheory.V.Cj.H.zigLim :
    UpperTheory.V.Cj.H.ZigLim := by
  intro Γ V S _ _ _ _ d G hconv hne
  obtain ⟨p, hp⟩ := hne
  have hincl := inclFacts Γ V S d G hconv ⟨p, hp⟩
  have main : ∀ (q k : ℕ) (u : ℕ → List Γ → G.Om q), (∀ j, HCoc (G.act q) k (u j)) →
      (∀ j (x : List Γ), x.length = k + 1 → G.dOm q (u j x) = 0) →
      (∀ x : List Γ, x.length = k + 1 → FLim G fun j => u j x) →
      ∃ c : ℕ → List Γ → S → Fin d → ℂ, (∀ j, Zig G q k (u j) (c j)) ∧
        ∀ x : List Γ, x.length = k + q + 1 → ∀ s, Tendsto (fun j => c j x s) atTop (𝓝 0) := by
    intro q
    induction q with
    | zero =>
      intro k u _ hcl hlim
      classical
      have hex : ∀ j (x : List Γ), x.length = k + 1 → ∃ f, G.incl f = u j x :=
        fun j x hx => (hincl.2.2 (u j x)).mp (hcl j x hx)
      choose f hf using hex
      refine ⟨fun j x => if h : x.length = k + 1 then f j x h else 0, ?_, ?_⟩
      · intro j x hx
        show u j x = G.incl (if h : x.length = k + 1 then f j x h else 0)
        rw [dif_pos hx, hf j x hx]
      · intro x hx s
        have hx' : x.length = k + 1 := by simpa using hx
        have ht := (hlim x hx' s {p} (Set.singleton_subset_iff.2 hp)
          isCompact_singleton).tendsto_at (Set.mem_singleton p)
        have hc := ((continuous_eval_const (fun _ : Fin 0 => (0 : V))).tendsto _).comp ht
        have heq : ∀ j, ((u j x : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p) (fun _ => 0) =
            f j x hx' s := by
          intro j
          rw [← hf j x hx']
          simp [Dr.Geo.incl, Set.indicator_of_mem hp]
        simp only [dif_pos hx']
        have hfun : (fun j => f j x hx' s) =
            fun j => ((u j x : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p) (fun _ => 0) :=
          funext fun j => (heq j).symm
        rw [hfun]
        simp at hc
        exact hc
    | succ q ih =>
      intro k u hcoc hcl hlim
      obtain ⟨K, hK1, hK2, hK3⟩ := poinOp Γ V S d G hconv q
      have hpt : ∀ x : List Γ, G.ρ (x.headD 1) p ∈ G.Y := fun x => G.maps _ p hp
      have hbeq : ∀ j, HEquiv (G.act q) k (fun x => K (G.ρ (x.headD 1) p) (u j x)) := by
        intro j γ x hx
        have hne : x ≠ [] := by
          rintro rfl
          simp at hx
        obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
        have hu := (hcoc j).1 γ (y :: ys) hx
        simp only [List.map_cons] at hu
        simp only [List.map_cons, List.headD_cons, map_mul]
        rw [hu, hK2 γ _ (G.maps y p hp)]
        rfl
      have hlen : ∀ (x : List Γ) i, x.length = k + 1 + 1 → i ∈ Finset.range x.length →
          (x.eraseIdx i).length = k + 1 := by
        intro x i hx hi
        rw [List.length_eraseIdx_of_lt (Finset.mem_range.1 hi)]
        omega
      have hcl' : ∀ j (x : List Γ), x.length = k + 1 + 1 →
          G.dOm q (hd (fun x => K (G.ρ (x.headD 1) p) (u j x)) x) = 0 := by
        intro j x hx
        have h0 := (hcoc j).2 x hx
        simp only [hd, map_sum, map_zsmul] at h0 ⊢
        rw [← h0]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hK1 _ (hpt _) _ (hcl j _ (hlen x i hx hi))]
      have hlim' : ∀ x : List Γ, x.length = k + 1 + 1 →
          FLim G fun j => hd (fun x => K (G.ρ (x.headD 1) p) (u j x)) x := by
        intro x hx
        simp only [hd]
        apply fLim_sum
        intro i hi
        apply fLim_zsmul
        exact hK3 _ (hpt _) _ (hlim _ (hlen x i hx hi))
      obtain ⟨c, hc1, hc2⟩ := ih (k + 1) (fun j => hd (fun x => K (G.ρ (x.headD 1) p) (u j x)))
        (fun j => hdHd Γ (G.Om q) (G.act q) k _ (hbeq j)) hcl' hlim'
      refine ⟨c, fun j => ⟨_, hbeq j, fun x hx => hK1 _ (hpt _) _ (hcl j x hx), hc1 j⟩, ?_⟩
      intro x hx s
      exact hc2 x (by omega) s
  exact main
