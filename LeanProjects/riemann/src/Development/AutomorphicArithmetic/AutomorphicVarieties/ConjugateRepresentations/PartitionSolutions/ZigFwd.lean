import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.FwdStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.InclFacts
open UpperTheory.V.Cj.A UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.zigFwd :
    ZigFwd := by
  intro Γ V S I _ _ _ _ _ d G hc hne r hr C hC q
  obtain ⟨hdd, -, -, hmap, hloc, heq⟩ := hdFacts
  obtain ⟨hact, hinj, hex⟩ := inclFacts Γ V S d G hc hne
  induction q with
  | zero =>
    intro k n hn u hu hd0 hh hv
    obtain rfl : k = n := by simpa using hn
    have key : ∀ x : List I, ∃ f, x.length = k + 1 → u x = G.incl f := fun x => by
      by_cases hx : x.length = k + 1
      · obtain ⟨f, hf⟩ := (hex (u x)).1 (hd0 x hx)
        exact ⟨f, fun _ => hf.symm⟩
      · exact ⟨0, fun h => absurd h hx⟩
    choose c hcu using key
    refine ⟨c, hcu, fun γ x hx => hinj ?_, fun x hx => hinj ?_, fun x hx s p hp => ?_⟩
    · rw [hact, ← hcu x hx, ← hcu _ (by simpa using hx), hu γ x hx]
    · have h1 := hmap I _ _ G.incl.toAddMonoidHom c x
      have h2 := hloc I _ (fun y => G.incl.toAddMonoidHom (c y)) u x
        (fun y hy _ => (hcu y (by omega)).symm)
      rw [map_zero, ← hh x hx, ← h2, h1]
      rfl
    · obtain ⟨i, hi⟩ := List.exists_mem_of_length_eq_add_one hx
      have hY : p ∈ G.Y := hC.sub i s (hp i hi)
      rw [← G.incl_apply (c x) s hY Fin.elim0, ← hcu x hx, hv x hx s p trivial hp]
      rfl
  | succ q ih =>
    intro k n hn u hu hd0 hh hv
    obtain ⟨b, hb, hdb, hvb⟩ := fwdStep Γ V S I d G hc r hr C hC q k u hu hd0 hv
    obtain ⟨c, hz, hrest⟩ := ih (k + 1) n (by omega) (hd b) (heq Γ I _ (G.act q) k b hb)
      (fun x hx => by
        have h1 := hmap I _ _ (G.dOm q).toAddMonoidHom b x
        have h2 := hloc I _ (fun y => (G.dOm q).toAddMonoidHom (b y)) u x
          (fun y hy _ => hdb y (by omega))
        rw [← hh x hx, ← h2, h1]
        rfl)
      (fun x _ => hdd I _ b x)
      (fun x hx s p _ hp => by
        let ev : G.Om q →+ (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :=
          { toFun := fun w => w.1 s p, map_zero' := rfl, map_add' := fun _ _ => rfl }
        have h1 := hmap I _ _ ev b x
        have h2 := hloc I _ (fun y => ev (b y)) (fun y => ev ((fun _ => (0 : G.Om q)) y)) x
          (fun y hy hyx => hvb y (by omega) s p trivial fun i hi => hp i (hyx i hi))
        change ev (hd b x) = 0
        rw [← h1, h2]
        simp [hd])
    exact ⟨c, ⟨b, hb, hdb, hz⟩, hrest⟩
