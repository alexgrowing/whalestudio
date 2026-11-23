import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFormCongrOfEventuallyEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionPreservesFlatForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSymplecticTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteQuotientOfIsLatLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumUniquenessOnSimplyConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTwistByCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIndexPreservedByActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTransformUnderSymplecticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumTransformUnderUnipotentStatement

open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatInv

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

theorem riem_int {g : ℕ} {M : Submodule ℤ (Fl g)} (hle : M ≤ stdLat g) :
    ∀ l ∈ M, ∀ l' ∈ M, ∃ k : ℤ, riem l l' = k := by
  have hint : ∀ l ∈ stdLat g, ∀ i, ∃ k : ℤ, l i = k := by
    intro l hl i
    obtain ⟨k, hk⟩ := ((Pi.basisFun ℝ (Fin g ⊕ Fin g)).mem_span_iff_repr_mem ℤ l).1 hl i
    exact ⟨k, by simpa using hk.symm⟩
  intro l hl l' hl'
  choose a ha using hint l (hle hl)
  choose a' ha' using hint l' (hle hl')
  exact ⟨∑ i, (a (Sum.inr i) * a' (Sum.inl i) - a (Sum.inl i) * a' (Sum.inr i)), by
    simp [riem, ha, ha']⟩

theorem restrict {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} {M M' : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ}
    {h : Pt E g → ℝ} (hd : IsDatum B τ M' j h) (hM : IsLat M) (hle : M ≤ M') :
    IsDatum B τ M j h :=
  ⟨hd.1, hM, ⟨fun l hl => hd.2.2.1.1 l (hle hl), fun l hl l' hl' => hd.2.2.1.2 l (hle hl) l' (hle hl')⟩,
    ⟨hd.2.2.2.1, hd.2.2.2.2.1, fun l hl => hd.2.2.2.2.2 l (hle hl)⟩⟩

theorem cover_flat (hN : Naturality) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {g n : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hB : SimplyConnectedSpace B) {j : Fl g → Pt E g → ℂ} {m : Pt E g → ℝ}
    (hd : IsDatum B τ (stdLat g) j m) (hc : ChernIsFlat B τ m) {M : Submodule ℤ (Fl g)}
    (hM : IsLat M) (hle : M ≤ stdLat g) (β : Fin n → E) {b : E} (hb : b ∈ B) {T : Ext (n + n)}
    (hT : IsTorsionForm τ (stdLat g) j m β b T) :
    IsTorsionForm τ M j m β b (Nat.card (stdLat g ⧸ M.submoduleOf (stdLat g)) • T) := by
  have hfin : Finite (stdLat g ⧸ M.submoduleOf (stdLat g)) :=
    GlobalTheory.finite_quotient_of_isLat_le M (stdLat g) hM hd.2.1 hle
  have hall : ∀ χ : AddChar (stdLat g ⧸ M.submoduleOf (stdLat g)) ℂ,
      IsTorsionForm τ (stdLat g) (twistFactor M (stdLat g) χ j) m β b T := fun χ =>
    GlobalTheory.T.flat_datum_uniqueness_on_simply_connected hN.2.2.1 hN.2.2.2.1 E g n B τ hB (stdLat g) (riem_int le_rfl) j _ m m hd hc
      (GlobalTheory.T.datum_twist_by_character E g B τ M (stdLat g) j m hd hM hle χ) hc β b hb T hT
  have h := hN.2.2.2.2.2.1 E g n B τ M (stdLat g) j m hd hM hle β b hb (fun _ => T) hall
  have e : ∑ᶠ _ : AddChar (stdLat g ⧸ M.submoduleOf (stdLat g)) ℂ, T =
      Nat.card (stdLat g ⧸ M.submoduleOf (stdLat g)) • T := by
    have := Fintype.ofFinite (stdLat g ⧸ M.submoduleOf (stdLat g))
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, AddChar.card_eq,
      Nat.card_eq_fintype_card]
  rwa [e] at h

theorem univTorsion_ratInv : GlobalTheory.Published.BismutKoehlerTorsion → Naturality → ∀ (g : ℕ) (γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g),
    (∀ i l, ∃ r : ℚ, γ.mat i l = r) → ∀ s ∈ siegel g, actB γ s ∈ siegel g ∧
      ∀ (v : symMat g) (T : Ext (1 + 1)), IsUnivTorsion g (actB γ s) (fderiv ℂ (actB γ) s v) T →
        IsUnivTorsion g s v T := by
  intro hBK hN g γ hγ s hs
  obtain ⟨hU, hSC⟩ := GlobalTheory.T.siegel_period_map_simply_connected g
  have hτ' := GlobalTheory.SympBase.main hU γ
  have hsymm : ∀ s ∈ siegel g, tauU (actB γ s) = moeb γ (tauU s) := fun s hs =>
    GlobalTheory.UnivAction.tauU_symPart_of_isSymm (hτ'.1.2.2 s hs).1
  have hmaps : Set.MapsTo (actB γ) (siegel g) (siegel g) := fun s hs => by
    show IsSiegel (tauU (actB γ s))
    rw [hsymm s hs]
    exact hτ'.1.2.2 s hs
  refine ⟨hmaps hs, ?_⟩
  rintro v T ⟨j, m, hd, hc, hT⟩
  obtain ⟨M, hM, hMle, hL, hLle, hpos, hcard⟩ := GlobalTheory.T.lattice_index_preserved_by_action g γ hγ
  have hdiff : DifferentiableOn ℂ (actB γ) (siegel g) := by
    have h1 : DifferentiableOn ℂ (fun s : symMat g => fun i k => moeb γ (tauU s) i k) (siegel g) :=
      differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun k => hτ'.1.2.1 i k
    exact ((GlobalTheory.UnivAction.symPartL g).differentiable.comp_differentiableOn h1).congr
      fun s _ => rfl

  have h1 := cover_flat hN hSC hd hc hL hLle ![fderiv ℂ (actB γ) s v] (hmaps hs) hT

  have h2 := (hN.1 (symMat g) (symMat g) g 1 (siegel g) tauU (latAct M γ) j m
    (restrict hd hL hLle) (siegel g) (actB γ) hU.1 hdiff hmaps ![v] s hs _).2 (by
      have hβ : (fun i => fderiv ℂ (actB γ) s (![v] i)) = ![fderiv ℂ (actB γ) s v] := by
        funext i; fin_cases i; rfl
      rw [hβ]; exact h1)

  have h3 := GlobalTheory.T.isTorsionForm_congr_of_eventuallyEq (symMat g) g 1 (tauU ∘ actB γ) (fun s => moeb γ (tauU s)) _ _ _ _ s _
    (Filter.eventually_of_mem (hU.1.mem_nhds hs) fun s hs => hsymm s hs) h2

  have h4 := hN.2.2.2.2.1 (symMat g) g 1 (siegel g) tauU M γ _ _ hU (GlobalTheory.T.datum_transform_under_symplectic g γ (latAct M γ) hL hLle j m hd)
    ![v] s hs _ h3
  obtain ⟨hd2, hc2⟩ := GlobalTheory.T.flat_datum_transform_under_unipotent g γ M hM hLle j m hd hc
  have h5 := GlobalTheory.T.flat_datum_uniqueness_on_simply_connected hN.2.2.1 hN.2.2.2.1 (symMat g) g 1 (siegel g) tauU hSC M (riem_int hMle) _ j _ m
    hd2 hc2 (restrict hd hM hMle) hc ![v] s hs _ h4

  obtain ⟨T0, -, hT0⟩ := hBK (symMat g) g 1 (siegel g) tauU (stdLat g) j m hd
    (hN.2.2.2.2.2.2 (symMat g) g (siegel g) tauU (stdLat g) j m hd hc) ![v]
  have h6 := cover_flat hN hSC hd hc hM hMle ![v] hs (((hT0 s hs).1 _).2 rfl)
  obtain ⟨TM, -, hTM⟩ := hBK (symMat g) g 1 (siegel g) tauU M j m (restrict hd hM hMle)
    (hN.2.2.2.2.2.2 (symMat g) g (siegel g) tauU M j m (restrict hd hM hMle) hc) ![v]
  have e1 := ((hTM s hs).1 _).1 h5
  have e2 := ((hTM s hs).1 _).1 h6
  have e : T = T0 s := by
    rw [← hcard] at e1
    exact smul_right_injective _ hpos.ne' (e1.trans e2.symm)
  exact ⟨j, m, hd, hc, e ▸ ((hT0 s hs).1 _).2 rfl⟩

end GlobalTheory.RatInv
