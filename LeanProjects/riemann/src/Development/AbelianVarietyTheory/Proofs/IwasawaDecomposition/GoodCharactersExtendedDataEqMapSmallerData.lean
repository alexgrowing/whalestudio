import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAbsIrrCharMapRingHomStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

section GoodTransport

open Formalism.L2.DIV

theorem absIrr_one_ne_zero {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] {χ : G → K}
    (h : IsAbsIrrChar χ) : χ 1 ≠ 0 := by
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  intro h0
  have h1 : ρ.character 1 = (n : AlgebraicClosure K) := by
    rw [Representation.char_one]; simp
  rw [hχ, h0, map_zero] at h1
  have hn : n = 0 := by exact_mod_cast h1.symm
  subst hn
  obtain ⟨a, b, hab⟩ := hρ.toNontrivial.exists_pair_ne
  apply hab
  apply Subrepresentation.toSubmodule_injective
  exact Subsingleton.elim _ _

theorem eq_of_idemOf_eq {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] {X Y : Finset (G → K)}
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (hYX : Y ⊆ X) (h : idemOf Y = idemOf X) : X = Y := by
  classical
  by_contra hne
  obtain ⟨χ, hχX, hχY⟩ : ∃ χ ∈ X, χ ∉ Y := by
    by_contra hc
    push_neg at hc
    exact hne (Finset.Subset.antisymm hc hYX)
  have hsplit : idemOf (X \ Y) + idemOf Y = idemOf X := by
    unfold idemOf
    exact Finset.sum_sdiff hYX
  have h0 : idemOf (X \ Y) = 0 := by
    rw [h] at hsplit
    simpa using hsplit
  have hmem : χ ∈ X \ Y := Finset.mem_sdiff.2 ⟨hχX, hχY⟩
  have hprod : chiIdem χ * idemOf (X \ Y) = chiIdem χ := by
    unfold idemOf
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun χ' hχ' =>
      chiIdem_mul (hX χ hχX) (hX χ' (Finset.mem_sdiff.1 hχ').1)]
    rw [Finset.sum_ite_eq, if_pos hmem]
  rw [h0, mul_zero] at hprod
  have hc := congrArg (fun a : MonoidAlgebra K G => a.coeff 1) hprod
  simp only [coeff_chiIdem, inv_one] at hc
  have hne1 := absIrr_one_ne_zero (hX χ hχX)
  have hcard : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have : χ 1 / (Fintype.card G : K) * χ 1 ≠ 0 := mul_ne_zero (div_ne_zero hne1 hcard) hne1
  exact this (by simpa using hc.symm)

theorem good_transport {K K' G G' : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] [Group G] [Fintype G]
    [Group G'] [Fintype G'] (σ : K →+* ℂ) (σ' : K' →+* ℂ) (φ : K →+* K') (hφ : ∀ x, σ' (φ x) = σ x) (e : G ≃* G')
    (c : G → ℂ) (c' : G' → ℂ) (hc : ∀ g, c' (e g) = c g) (X : Finset (G → K)) (X' : Finset (G' → K'))
    (hX : ∀ χ, χ ∈ X ↔ IsAbsIrrChar χ ∧ ∑ g, c g * σ (χ g) = σ (χ 1)) (hX2 : ∀ g, σ ((idemOf X).coeff g) = c g)
    (hX' : ∀ χ, χ ∈ X' ↔ IsAbsIrrChar χ ∧ ∑ g, c' g * σ' (χ g) = σ' (χ 1)) (hX2' : ∀ g, σ' ((idemOf X').coeff g) = c' g)
    (χ' : G' → K') : χ' ∈ X' ↔ ∃ χ ∈ X, χ' = fun g => φ (χ (e.symm g)) := by
  classical
  have sup : ∀ χ ∈ X, (fun g => φ (χ (e.symm g))) ∈ X' := by
    intro χ hχ
    obtain ⟨hirr, hsum⟩ := (hX χ).1 hχ
    refine (hX' _).2 ⟨isAbsIrrChar_comp e.symm (GlobalTheory.T.isAbsIrrChar_map_ringHom φ χ hirr), ?_⟩
    rw [← Equiv.sum_comp e.toEquiv]
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.symm_apply_apply, hc, hφ, map_one]
    exact hsum
  refine ⟨fun hχ' => ?_, fun ⟨χ, hχ, he⟩ => he ▸ sup χ hχ⟩
  set F : (G → K) → (G' → K') := fun χ g => φ (χ (e.symm g)) with hF
  have hinj : Function.Injective F := by
    intro χ₁ χ₂ h12
    funext g
    have := congrFun h12 (e g)
    simp only [hF, MulEquiv.symm_apply_apply] at this
    exact φ.injective this
  have hYX : X.image F ⊆ X' := by
    intro ψ hψ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hψ
    exact sup χ hχ
  have hcard : (Fintype.card G' : ℂ) = (Fintype.card G : ℂ) := by
    rw [Fintype.card_congr e.toEquiv]
  have hid : idemOf (X.image F) = idemOf X' := by
    apply MonoidAlgebra.ext
    ext t
    apply σ'.injective
    rw [hX2', coeff_idemOf, Finset.sum_image fun a _ b _ h => hinj h, map_sum]
    have := hX2 (e.symm t)
    rw [coeff_idemOf, map_sum] at this
    rw [← hc (e.symm t), MulEquiv.apply_symm_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun χ _ => ?_
    simp only [hF, map_mul, map_div₀, map_natCast, hφ, map_one, map_inv, hcard]
  have := eq_of_idemOf_eq (fun ψ hψ => ((hX' ψ).1 hψ).1) hYX hid
  rw [this] at hχ'
  obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hχ'
  exact ⟨χ, hχ, rfl⟩

end GoodTransport

end GlobalTheory.Mem.R3.DefLatBC

namespace GlobalTheory.Mem.R3.DefLatBC

theorem bc_eq_of_heq {X : Type} [Group X] {E : Type} [Field E] [NumberField E] {r m : ℕ} {P P' : Finset (Pl E)} (hP : P' = P)
    (a : X ≃* Formalism.L2.DIV.G0 P r) (a' : X ≃* Formalism.L2.DIV.G0 P' r) (h : HEq a' a) (g : X) (Q : P) (Q' : P')
    (hQ : (Q' : Pl E) = Q) (i : ZMod m ≃+* kP Q.1) (i' : ZMod m ≃+* kP Q'.1) (x x' : GL (Fin r) (ZMod m))
    (hx : a g Q = Formalism.UG.bc (i : ZMod m →+* kP Q.1) x) (hx' : a' g Q' = Formalism.UG.bc (i' : ZMod m →+* kP Q'.1) x') : x' = x := by
  subst hP
  cases h
  obtain ⟨Q, hQm⟩ := Q
  obtain ⟨Q', hQm'⟩ := Q'
  dsimp only at hQ
  subst hQ
  have hi : (i' : ZMod m →+* kP Q') = (i : ZMod m →+* kP Q') := Subsingleton.elim _ _
  rw [hi] at hx'
  have h2 : Formalism.UG.bc (i : ZMod m →+* kP Q') x' = Formalism.UG.bc (i : ZMod m →+* kP Q') x := hx'.symm.trans hx
  have hinj : Function.Injective (i : ZMod m →+* kP Q') := i.injective
  apply Units.ext
  apply Matrix.ext
  intro s t
  have := congrArg (fun y : GL (Fin r) (kP Q') => (y : Matrix (Fin r) (Fin r) (kP Q')) s t) h2
  exact hinj (by simpa [Formalism.UG.bc] using this)

end GlobalTheory.Mem.R3.DefLatBC

namespace GlobalTheory.Mem.R3.DefLatBC

set_option maxHeartbeats 1000000 in

theorem goodIdempotents_agree_extendedData {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hB : B'.toPre = B.toPre) (hf : HEq f' f) (hp : HEq w'.px w.px) (hG : GrpTrue Z.N f) (hG' : GrpTrue Z'.N f')
    (hx : ExtN z z') (e : Gc B w.px ≃* Gc B' w'.px) (he : ∀ g, HEq (e g) g) (g : Gc B w.px) :
    (w'.st Z').toD7.ntypes.e0.coeff ((z'.R.eG.trans z'.cG) (e g)) =
      (w.st Z).toD7.ntypes.e0.coeff ((z.R.eG.trans z.cG) g) := by
  cases B
  cases B'
  dsimp only at hB
  subst hB
  cases hf
  have hpx : w'.px = w.px := eq_of_heq hp
  cases w'
  dsimp only at hpx
  subst hpx
  have heg : e g = g := eq_of_heq (he g)
  rw [heg]
  obtain ⟨plg, iso, hpl, -, -, hbc⟩ := z.pins.keep.grp
  obtain ⟨plg', iso', hpl', -, -, hbc'⟩ := z'.pins.keep.grp
  refine Eq.trans ?_ (TypesTrue.typeIdempotent_coeff_across_layers hG hG' ((z.R.eG.trans z.cG) g))
  congr 1
  funext kv'
  obtain ⟨k, v'⟩ := kv'
  obtain ⟨v, rfl⟩ : ∃ v, v' = plEquiv Z.N.naut Z'.N.naut k v := ⟨_, (Equiv.apply_symm_apply _ v').symm⟩
  show _ = ((z.R.eG.trans z.cG) g) ⟨k, (plEquiv Z.N.naut Z'.N.naut k).symm (plEquiv Z.N.naut Z'.N.naut k v)⟩
  rw [Equiv.symm_apply_apply]
  have hP : z'.R.Pg = z.R.Pg := eq_of_heq hx.Pg
  have hQ : (plg' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩).1 = (plg ⟨k, v⟩).1 := by
    rw [hpl', hpl]
    exact TypesTrue.plGw_plEquiv hG hG' k v
  exact bc_eq_of_heq hP z.R.eG z'.R.eG hx.eG g _ _ hQ (iso ⟨k, v⟩) (iso' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩) _ _
    (hbc g ⟨k, v⟩) (hbc' g ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩)

end GlobalTheory.Mem.R3.DefLatBC

theorem GlobalTheory.Mem.R3.DefLatBC.good_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∀ χ' : Gc B' w'.px → (w'.st Z').toD7.what₂.LL, χ' ∈ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).X ↔ ∃ χ ∈ ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).X, χ' = fun g => φ (χ (e.symm g))) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hp Z hX Wt z hG _ _ _ Z' hX' hG' _ _ z' _ hx j j' hj φ hφ e he χ' => ?_
  show χ' ∈ z'.Xg ↔ ∃ χ ∈ z.Xg, χ' = fun g => φ (χ (e.symm g))
  have g1 := (goodSet_iff _ _ _).1 z.good
  have g2 := (goodSet_iff _ _ _).1 z'.good
  exact GlobalTheory.Mem.R3.DefLatBC.good_transport (w.st Z).toD7.what₂.embLL (w'.st Z').toD7.what₂.embLL φ hφ e
    (fun g => (w.st Z).toD7.ntypes.e0.coeff ((z.R.eG.trans z.cG) g))
    (fun g => (w'.st Z').toD7.ntypes.e0.coeff ((z'.R.eG.trans z'.cG) g))
    (GlobalTheory.Mem.R3.DefLatBC.goodIdempotents_agree_extendedData z z' hE.1 hf hp hG hG' hx e he) z.Xg z'.Xg g1.1 g1.2 g2.1 g2.2 χ'
