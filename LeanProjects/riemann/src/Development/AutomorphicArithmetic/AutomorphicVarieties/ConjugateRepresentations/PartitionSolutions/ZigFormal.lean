import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.zigFormal :
    ZigFormal := by
  intro Γ V S I _ _ _ _ d G
  refine ⟨fun q k u u' c h hz => ?_, fun ι hι q => ?_⟩
  · cases q with
    | zero => exact fun x hx => (h x hx).symm.trans (hz x hx)
    | succ q =>
      obtain ⟨b, hb, hdb, hz⟩ := hz
      exact ⟨b, hb, fun x hx => (hdb x hx).trans (h x hx), hz⟩
  · induction q with
    | zero => exact fun k u c hz x hx => hz (x.map ι) (by rw [List.length_map, hx])
    | succ q ih =>
      rintro k u c ⟨b, hb, hdb, hz⟩
      refine ⟨fun x => b (x.map ι), fun γ x hx => ?_, fun x hx => hdb (x.map ι) (by rw [List.length_map, hx]), ?_⟩
      · have h := hb γ (x.map ι) (by rw [List.length_map, hx])
        refine Eq.trans ?_ h
        simp only [List.map_map]
        congr 2
        funext δ
        exact hι γ δ
      · have h := ih (k + 1) _ c hz
        have e : (fun x : List Γ => UpperTheory.V.Lit.Geo.hd b (x.map ι)) = UpperTheory.V.Lit.Geo.hd (fun x : List Γ => b (x.map ι)) :=
          funext fun x => (hdFacts.2.2.1 I Γ _ ι b x).symm
        rw [e] at h
        exact h
