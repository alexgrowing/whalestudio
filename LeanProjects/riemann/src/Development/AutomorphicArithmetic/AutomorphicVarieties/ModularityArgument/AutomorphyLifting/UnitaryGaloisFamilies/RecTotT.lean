import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem tw_sumList {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (s : ℝ) (L : List (WD h)) :
    (sumList L).lpTw s = sumList (L.map fun x => x.lpTw s) := by
  induction L with
  | nil =>
    change (WD.lpZero h).lpTw s = WD.lpZero h
    rw [WD.lpZero, WD.lpTw_mk]
    exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | cons x L ih =>
    change (x.lpSum (sumList L)).lpTw s = (x.lpTw s).lpSum (sumList (L.map fun x => x.lpTw s))
    rw [WD.lpTw_sum, ih]

theorem UpperTheory.V.Z.Win.Gu.recTotT :
    ProdT → SpehT → RecTotT := by
  intro hProd hSpeh E Ω _ _ _ _ _ _ n c a d hn P w ρ σ hpos hP hS τ e A h rc hrc
  have h1 := hProd E Ω n c (fun i => d i * a i) hn w σ (fun i => (hS i).2.1) τ e A h rc hrc
  have h2 : ∀ i, rc (cl (σ i)) = sumList ((List.range (d i)).map fun k : ℕ =>
      (rc (cl (ρ i))).lpTw (((d i : ℝ) - 1) / 2 - k)) := fun i =>
    hSpeh E Ω (a i) (d i) (P i) w (ρ i) (σ i) (hpos i).1 (hpos i).2 (hP i) (hS i).1 (hS i).2.2 A h rc hrc
  have h3 : rc (algNorm τ) = (rc (cl τ)).lpTw ((1 - (n : ℝ)) / 2) := by
    obtain ⟨_, _, L⟩ := hrc
    exact L.nu _ _
  rw [h3, h1, tw_sumList, List.map_ofFn]
  refine congrArg sumList (congrArg List.ofFn (funext fun i => ?_))
  rw [Function.comp_apply, h2, tw_sumList, List.map_map, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map]
  refine congrArg sumList (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp_apply, WD.lpTw_add]
  refine congrArg₂ WD.lpTw rfl ?_
  simp only [ex]
  push_cast
  ring
