import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumConjugationDictionaryRowGrid
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitScalarFourier
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntireEqOfMonomialDerivationsAtZeroEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOrbitVectorsMovedPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitVacuumStandardLatticesDefinitePair
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.SplitMoveFrames

set_option maxHeartbeats 1600000 in

private theorem moves_gen {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hθ : IsInfFam θ)
    (hSg : S.SigOK) (hTg : T.SigOK) (hcS : ∀ τ, IsCartanInv (gramAt D S τ) 1) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) 1)
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛS' : IsSelfDualC S ΛS') (hΛT : IsSelfDualC T ΛT) (hΛT' : IsSelfDualC T ΛT')
    {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {s : GA D S} {s' : GA D T} (hs : SuppAt e S s) (hs' : SuppAt e T s')
    {x₀ y₀ : (Formalism.L2.Theta.AE D)ˣ} (hx₀ : IsDetAt e S s x₀) (hy₀ : IsDetAt e T s' y₀)
    (hmove : ∀ u : WO S T, u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔
      ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u = actO S T s s' u₀)
    {V : Type} [AddCommGroup V] [Module ℂ V] {H : Formalism.L2.Th1.H.Sesq V} (hH : Formalism.L2.Th1.H.IsHerm H) {α : V → ℂ}
    (rd : (WO S T → ℂ) →ₗ[ℂ] (V → ℂ)) (P : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ V)
    (hrd : ∀ f, IsThetaFunO ψ S T f → ∀ γ, rd (heisO ψ S T (GlobalTheory.LatVac.finTens 1 γ) f) = Formalism.L2.Th1.H.opU H (P γ) (rd f))
    {A₁ A₂ : AddSubgroup V}
    (hA₁ : ∀ γ, GlobalTheory.LatVac.finTens 1 γ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ P γ ∈ A₁)
    (hA₂ : ∀ γ, GlobalTheory.LatVac.finTens 1 γ ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ P γ ∈ A₂)
    (hA₂γ : ∀ z ∈ A₂, ∃ γ, z = P γ) (hsd : Formalism.L2.Th1.H.IsSelfDual H A₂) (hα₁ : Formalism.L2.Th1.H.IsSemiChar H A₁ α)
    (hα₂ : Formalism.L2.Th1.H.IsSemiChar H A₂ α) (hidx : Formalism.L2.Th1.H.relIdx A₁ A₂ ≠ 0) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f)
    (hfix₁ : rd f ∈ Formalism.L2.Th1.H.fixedBy H α A₁) (hfix₂ : rd (om (s, s') f) ∈ Formalism.L2.Th1.H.fixedBy H α A₂)
    (hne : rd (om (s, s') f) ≠ 0) :
    rd (om (s, s') f) = fun z => (splitFacO χS χT x₀ y₀ : ℂ) * Formalism.L2.Th1.H.inter H α A₁ A₂ (rd f) z := by
  classical
  have hψ := hW.std
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he

  have hom := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) _ _ _ _ s s' (fun τ => by rw [GlobalTheory.SplitScalar.compAt_mt he hs])
    (fun τ => by rw [GlobalTheory.SplitScalar.compAt_mt he hs']) hmove f hf
  have hdΛ : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ u' ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ψ (symplO S T u u') = 1 := fun u hu u' hu' => GlobalTheory.LatVac.char_sympl_eq_one hψ hΛS hΛT hu hu'
  have hdΛ' : ∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ u' ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True),
      ψ (symplO S T u u') = 1 := fun u hu u' hu' => GlobalTheory.LatVac.char_sympl_eq_one hψ hΛS' hΛT' hu hu'
  have hst := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS ΛT _ he.1
  have hstc := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS ΛT _ he'.1
  have hst' := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS' ΛT' _ he.1
  have hstc' := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS' ΛT' _ he'.1
  have hoff : ∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True),
      (1 - (e + cA D e)) • u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := (hmove u).1 hu
    rw [GlobalTheory.SplitScalar.off_smul_actO hs hs', sub_smul, add_smul, one_smul]
    exact sub_mem hu₀ (add_mem (hst _ hu₀) (hstc _ hu₀))
  have hzsub : ∀ γ γ', P γ - P γ' =
      P (γ - γ') := fun γ γ' => by rw [map_sub]
  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ
  set Λ' := (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ'

  have : (A₁.addSubgroupOf A₂).FiniteIndex := ⟨hidx⟩
  letI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := Fintype.ofFinite _
  have hch : ∀ c : A₂ ⧸ A₁.addSubgroupOf A₂, ∃ γ, ((Quotient.out c : A₂) : V) =
      P γ := fun c => hA₂γ _ (Quotient.out c).2
  choose γc hγc using hch
  have hcov : ∀ u ∈ Λ', ∃ c ∈ (Finset.univ : Finset (A₂ ⧸ A₁.addSubgroupOf A₂)),
      u - GlobalTheory.LatVac.finTens 1 (γc c) ∈ Λ := by
    intro u hu
    obtain ⟨γ, l, hl, hl', hγ⟩ := GlobalTheory.LatApprox.exists_rat_sub_two_nsmul D S T ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' u hu
    have hx' : GlobalTheory.LatVac.finTens 1 γ ∈ Λ' := by
      rw [show GlobalTheory.LatVac.finTens 1 γ = u - 2 • l by rw [← hγ, sub_sub_cancel]]
      exact sub_mem hu (nsmul_mem hl' 2)
    have hz : P γ ∈ A₂ := (hA₂ γ).1 hx'
    refine ⟨QuotientAddGroup.mk (⟨_, hz⟩ : A₂), Finset.mem_univ _, ?_⟩
    have hq : P γ - P (γc (QuotientAddGroup.mk (⟨_, hz⟩ : A₂))) ∈ A₁ := by
      rw [← hγc]
      obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add (A₁.addSubgroupOf A₂) (⟨_, hz⟩ : A₂)
      rw [hh, AddSubgroup.coe_add, sub_add_cancel_left]
      exact neg_mem (AddSubgroup.mem_addSubgroupOf.1 h.2)
    rw [hzsub] at hq
    have h1 := (hA₁ _).2 hq
    rw [GlobalTheory.AdTh.SplitClass.finTens_sub] at h1
    have e1 : u - GlobalTheory.LatVac.finTens 1 (γc (QuotientAddGroup.mk (⟨_, hz⟩ : A₂))) =
        2 • l + (GlobalTheory.LatVac.finTens 1 γ - GlobalTheory.LatVac.finTens 1 (γc (QuotientAddGroup.mk (⟨_, hz⟩ : A₂)))) := by
      rw [← hγ]; abel
    rw [e1]
    exact add_mem (nsmul_mem hl 2) h1
  obtain ⟨R, hR, hRu⟩ := GlobalTheory.AdTh.SplitClass.exists_reps Λ (fun u => u ∈ Λ' ∧ IsHalf e u) Finset.univ
    (fun c => GlobalTheory.LatVac.finTens 1 (γc c)) fun u hu => hcov u hu.1
  obtain ⟨R', hR', hRu'⟩ := GlobalTheory.AdTh.SplitClass.exists_reps Λ (fun u => u ∈ Λ' ∧ IsHalf (cA D e) u) Finset.univ
    (fun c => GlobalTheory.LatVac.finTens 1 (γc c)) fun u hu => hcov u hu.1
  have hRu2 : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ := fun u hu hue => hRu u ⟨hu, hue⟩
  have hRu2' : ∀ u ∈ Λ', IsHalf (cA D e) u → ∃! v, v ∈ R' ∧ u - v ∈ Λ := fun u hu hue => hRu' u ⟨hu, hue⟩
  have hmain := GlobalTheory.SplitScalar.om_vacuum_eq_splitFac_smul_sum D ψ θ S T χS χT om hW hθ hSg hTg
    (fun _ => 1) (fun _ => 1) hcS hcT ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT'
    e he s s' hs hs' x₀ y₀ hx₀ hy₀ hmove R R' hR hRu2 hR' hRu2' f hf

  have hpair : ∀ p : WO S T × WO S T, ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ l : WO S T,
      p ∈ R ×ˢ R' → (l ∈ Λ ∧ l ∈ Λ' ∧ p.1 + p.2 - GlobalTheory.LatVac.finTens 1 γ = 2 • l) := by
    intro p
    by_cases hp : p ∈ R ×ˢ R'
    · obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
      obtain ⟨γ, l, h1, h2, h3⟩ := GlobalTheory.LatApprox.exists_rat_sub_two_nsmul D S T ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' (p.1 + p.2)
        (add_mem (hR _ hu).1 (hR' _ hu').1)
      exact ⟨γ, l, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, 0, fun h => absurd h hp⟩
  choose γ l hγl using hpair
  have hxeq : ∀ p ∈ R ×ˢ R', GlobalTheory.LatVac.finTens 1 (γ p) = p.1 + p.2 - 2 • l p := fun p hp => by
    rw [← (hγl p hp).2.2, sub_sub_cancel]
  have hxΛ' : ∀ p ∈ R ×ˢ R', GlobalTheory.LatVac.finTens 1 (γ p) ∈ Λ' := by
    intro p hp
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    rw [hxeq p hp]
    exact sub_mem (add_mem (hR _ hu).1 (hR' _ hu').1) (nsmul_mem (hγl p hp).2.1 2)
  have hwx : ∀ p ∈ R ×ˢ R', p.1 + p.2 = GlobalTheory.LatVac.finTens 1 (γ p) + 2 • l p := fun p hp => by
    rw [hxeq p hp, sub_add_cancel]
  have hz₂ : ∀ p ∈ R ×ˢ R', P (γ p) ∈ A₂ := fun p hp =>
    (hA₂ _).1 (hxΛ' p hp)

  have hpf : ∀ p ∈ R ×ˢ R', heisO ψ S T p.1 (heisO ψ S T p.2 f) =
      ψ (symplOH S T p.1 p.2) • heisO ψ S T (GlobalTheory.LatVac.finTens 1 (γ p)) f := by
    intro p hp
    rw [GlobalTheory.LatVac.heisO_heisO, hwx p hp, GlobalTheory.AdForm.SplitGen.heisO_add_two ψ (hf.2.lat.1 _ (hγl p hp).1)
      (hdΛ' _ (hxΛ' p hp) _ (hγl p hp).2.1)]

  have hph : ∀ p ∈ R ×ˢ R', ψ (symplOH S T p.1 p.2) = α (P (γ p)) := by
    intro p hp
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    have hF : heisO ψ S T p.1 (heisO ψ S T p.2 (om (s, s') f)) = om (s, s') f := by
      rw [hom.2.lat.2 _ he' p.2 (hR' _ hu').1 (hR' _ hu').2, hom.2.lat.2 _ he p.1 (hR _ hu).1 (hR _ hu).2]
    rw [GlobalTheory.LatVac.heisO_heisO, hwx p hp, GlobalTheory.AdForm.SplitGen.heisO_add_two ψ (hom.2.lat.1 _ (hγl p hp).2.1)
      (hdΛ' _ (hxΛ' p hp) _ (hγl p hp).2.1)] at hF
    have hG := congrArg rd hF
    rw [map_smul, hrd _ hom.2.theta] at hG
    obtain ⟨w, hw⟩ := Function.ne_iff.1 hne
    have h1 := congrFun hG w
    have h2 := hfix₂ _ (hz₂ p hp) w
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 hw
    have hU : Formalism.L2.Th1.H.opU H (P (γ p)) (rd (om (s, s') f)) w ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact hw h1.symm
    exact mul_right_cancel₀ hU (h1.trans h2.symm)

  have hinj : ∀ p ∈ R ×ˢ R', ∀ q ∈ R ×ˢ R', P (γ p) -
      P (γ q) ∈ A₁ → p = q := by
    intro p hp q hq hpq
    rw [hzsub] at hpq
    have h1 := (hA₁ _).2 hpq
    rw [GlobalTheory.AdTh.SplitClass.finTens_sub] at h1
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    obtain ⟨hv, hv'⟩ := Finset.mem_product.1 hq
    by_contra hne'
    refine GlobalTheory.SplitScalar.sum_sub_notMem he hst hstc hR hRu2 hR' hRu2' hu hv hu' hv'
      (by rw [Prod.mk.eta, Prod.mk.eta]; exact hne') ?_
    have e2 : p.1 + p.2 - (q.1 + q.2) = (GlobalTheory.LatVac.finTens 1 (γ p) - GlobalTheory.LatVac.finTens 1 (γ q)) +
        2 • (l p - l q) := by
      rw [hwx p hp, hwx q hq]; abel
    rw [e2]
    exact add_mem h1 (nsmul_mem (sub_mem (hγl p hp).1 (hγl q hq).1) 2)
  have hsurj : ∀ y ∈ A₂, ∃ p ∈ R ×ˢ R', y - P (γ p) ∈ A₁ := by
    intro y hy
    obtain ⟨γ₀, rfl⟩ := hA₂γ y hy
    have hv : GlobalTheory.LatVac.finTens 1 γ₀ ∈ Λ' := (hA₂ _).2 hy
    have hh1 : IsHalf e (e • GlobalTheory.LatVac.finTens 1 γ₀) :=
      (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_smul, he.1])
    have hh2 : IsHalf (cA D e) (cA D e • GlobalTheory.LatVac.finTens 1 γ₀) :=
      (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_smul, he'.1])
    obtain ⟨r, ⟨hr, hrΛ⟩, -⟩ := hRu2 _ (hst' _ hv) hh1
    obtain ⟨r', ⟨hr', hrΛ'⟩, -⟩ := hRu2' _ (hstc' _ hv) hh2
    have hp : (r, r') ∈ R ×ˢ R' := Finset.mem_product.2 ⟨hr, hr'⟩
    refine ⟨(r, r'), hp, ?_⟩
    rw [hzsub]
    refine (hA₁ _).1 ?_
    rw [GlobalTheory.AdTh.SplitClass.finTens_sub, hxeq _ hp]
    have e3 : GlobalTheory.LatVac.finTens 1 γ₀ - ((r, r').1 + (r, r').2 - 2 • l (r, r')) =
        (e • GlobalTheory.LatVac.finTens 1 γ₀ - r) + (cA D e • GlobalTheory.LatVac.finTens 1 γ₀ - r') +
        (1 - (e + cA D e)) • GlobalTheory.LatVac.finTens 1 γ₀ + 2 • l (r, r') := by
      simp only [sub_smul, add_smul, one_smul]; abel
    rw [e3]
    exact add_mem (add_mem (add_mem hrΛ hrΛ') (hoff _ hv)) (nsmul_mem (hγl _ hp).1 2)
  have hsum := GlobalTheory.ThetaInter.inter_eq_sum_reps H α A₁ A₂ hH hsd hα₁ hα₂ (R ×ˢ R')
    (fun p => P (γ p)) hz₂ hinj hsurj _ hfix₁

  have hF : rd (om (s, s') f) =
      ((splitFacO χS χT x₀ y₀ : ℂ) * ((Real.sqrt ((R.card : ℝ) * R'.card) : ℝ) : ℂ)⁻¹) •
      ∑ p ∈ R ×ˢ R', α (P (γ p)) •
        Formalism.L2.Th1.H.opU H (P (γ p)) (rd f) := by
    rw [hmain, map_smul, ← Finset.sum_product', map_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hpf p hp, map_smul, hrd _ hf.2.theta,
      hph p hp]
  funext w
  rw [hF, hsum w]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    Finset.card_product, Nat.cast_mul]
  ring

private theorem law_infRat {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : GlobalTheory.FockCompare.RW T S) :
    f (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T v)) =
      Complex.exp (-(Real.pi * Complex.I) * (-GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T v) z : ℝ)) *
        heisO ψ S T (GlobalTheory.VacUnique.finRat S T (-v)) f (GlobalTheory.FockCompare.iotaW σ T S z) := by
  have e : GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T v) =
      ratW T S v + (GlobalTheory.FockCompare.iotaW σ T S z + GlobalTheory.VacUnique.finRat S T (-v)) := by
    rw [GlobalTheory.VacUnique.ratW_eq h, AddMonoidHom.map_add, AddMonoidHom.map_neg]
    abel
  have e2 : symplOH S T (ratW T S v) (GlobalTheory.FockCompare.iotaW σ T S z + GlobalTheory.VacUnique.finRat S T (-v)) =
      symplOH S T (ratW T S v) (GlobalTheory.FockCompare.iotaW σ T S z) + symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v)) := by
    unfold symplOH
    rw [(GlobalTheory.T.symplecticAdelicForm_biadditive_alternating_rational D S T).2.1, mul_add]
  have e3 : heisO ψ S T (GlobalTheory.VacUnique.finRat S T (-v)) f (GlobalTheory.FockCompare.iotaW σ T S z) =
      f (GlobalTheory.FockCompare.iotaW σ T S z + GlobalTheory.VacUnique.finRat S T (-v)) := by
    show ψ (symplOH S T (GlobalTheory.FockCompare.iotaW σ T S z) _) * _ = _
    rw [GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ h.inf hψ S T _ _ (Or.inl (h.real_iota T S z)),
      GlobalTheory.VacUnique.piW_of_inf θ (GlobalTheory.VacUnique.finRat_inf S T _), LinearMap.map_zero]
    simp
  rw [e, hf.quasi, e3, e2, GlobalTheory.RatFinIso.symplOH_ratW_finRat_neg, add_zero,
    AddChar.map_neg_eq_inv ψ (symplOH S T (ratW T S v) (GlobalTheory.FockCompare.iotaW σ T S z)),
    GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ h.inf hψ S T _ _ (Or.inr (h.real_iota T S z)), GlobalTheory.VacUnique.piW_ratW h.inf, h.pi_iota,
    ← Complex.exp_neg]
  push_cast
  ring_nf

open GlobalTheory.ThetaLawOF in

private theorem exists_reading {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) {δ : ℂ} (hδ : δ ≠ 0) :
    ∃ (rd : (WO S T → ℂ) →ₗ[ℂ] (Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ))
      (P : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank),
      (∀ f, IsThetaFunO ψ S T f → ∀ γ, rd (heisO ψ S T (GlobalTheory.LatVac.finTens 1 γ) f) =
        Formalism.L2.Th1.H.opU (GlobalTheory.ThetaInter.sesqOf D (tor0 D D.host.ccK δ) S.rank T.rank) (P γ) (rd f)) ∧
      (∀ (f : WO S T → ℂ) (Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ),
        (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) →
        rd f = fun Y => Φ (δ⁻¹ • Y)) ∧
      (∀ v, P (-v) = δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) *
        GlobalTheory.FockPos.frAt frS τ) a b)) ∧ Function.Injective P := by
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let zf : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → GlobalTheory.FockCompare.RW T S :=
    fun Z τ => GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹
  let Gs : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ := fun Z =>
    Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ))
  have hGs : ∀ Z, Gs Z ≠ 0 := fun Z => Complex.exp_ne_zero _
  let Xf : Matrix (Fin T.rank) (Fin S.rank) D.host.E → Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := fun v τ a b =>
    ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b
  have hXadd : ∀ v v', Xf (v + v') = Xf v + Xf v' := fun v v' => by
    funext τ
    show (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T (v + v') τ) * GlobalTheory.FockPos.frAt frS τ = _
    rw [map_add]
    show (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) + Matrix.of (GlobalTheory.VacUnique.infRat S T v' τ)) *
      GlobalTheory.FockPos.frAt frS τ = _
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl
  have hzX : ∀ v, zf (Xf v) = GlobalTheory.VacUnique.infRat S T v := fun v => by
    funext τ
    show GlobalTheory.FockPos.frAt frT τ * ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) *
      GlobalTheory.FockPos.frAt frS τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ = Matrix.of (GlobalTheory.VacUnique.infRat S T v τ)
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, (frAt_inv frT τ).2, Matrix.one_mul, Matrix.mul_assoc, (frAt_inv frS τ).2,
      Matrix.mul_one]
  have hzadd : ∀ Z Z', zf (Z + Z') = zf Z + zf Z' := fun Z Z' => by
    funext τ
    show GlobalTheory.FockPos.frAt frT τ * (Matrix.of (Z τ) + Matrix.of (Z' τ)) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ = _
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl
  have hz1 : ∀ Z, GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (zf Z)) = Z := fun Z => by
    rw [zCo_iota hch]; funext τ; exact coord_back frS frT Z τ
  let rd : (WO S T → ℂ) →ₗ[ℂ] (Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ) :=
    { toFun := fun f Y => (Gs (δ⁻¹ • Y))⁻¹ * f (GlobalTheory.FockCompare.iotaW σ T S (zf (δ⁻¹ • Y)))
      map_add' := fun f g => by funext Y; simp only [Pi.add_apply, mul_add]
      map_smul' := fun c f => by funext Y; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  let P : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank :=
    AddMonoidHom.mk' (fun γ => δ • Xf (-γ)) fun a b => by rw [neg_add, hXadd, smul_add]
  have hP : ∀ v, P (-v) = δ • Xf v := fun v => by
    show δ • Xf (- -v) = _
    rw [neg_neg]
  refine ⟨rd, P, fun f hf γ => ?_, fun f Φ hΦ => ?_, hP, fun a b hab => ?_⟩
  · obtain ⟨v, rfl⟩ : ∃ v, γ = -v := ⟨-γ, (neg_neg γ).symm⟩
    funext Y
    obtain ⟨Z, rfl⟩ : ∃ Z, Y = δ • Z := ⟨δ⁻¹ • Y, by rw [smul_smul, mul_inv_cancel₀ hδ, one_smul]⟩
    have hZZ : ∀ Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank, δ⁻¹ • δ • Z = Z := fun Z => by
      rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
    rw [hP]
    show (Gs (δ⁻¹ • δ • Z))⁻¹ * heisO ψ S T (GlobalTheory.VacUnique.finRat S T (-v)) f (GlobalTheory.FockCompare.iotaW σ T S (zf (δ⁻¹ • δ • Z))) =
      (Gs (δ⁻¹ • (δ • Z + δ • Xf v)))⁻¹ * f (GlobalTheory.FockCompare.iotaW σ T S (zf (δ⁻¹ • (δ • Z + δ • Xf v)))) *
      Complex.exp (-(Real.pi : ℂ) * Hf D (tor0 D D.host.ccK δ) (δ • Z) (δ • Xf v) -
        (Real.pi : ℂ) * Hf D (tor0 D D.host.ccK δ) (δ • Xf v) (δ • Xf v) / 2)
    rw [← smul_add, hZZ, hZZ, hzadd, hzX, law_infRat hch hψ hf, torusHermitianForm_scaled_coordinate_eq hδ, torusHermitianForm_scaled_coordinate_eq hδ]
    have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T v) (zf Z) = ∑ τ, ∑ a, ∑ b,
        2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * (starRingEnd ℂ (Z τ a b) * Xf v τ a b)).re := by
      rw [omO_frame frS frT hS hT]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have := coord_back frS frT Z τ
      show (∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * (starRingEnd ℂ (((GlobalTheory.FockPos.frAt frT τ)⁻¹ *
        (GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹) * GlobalTheory.FockPos.frAt frS τ) a b) *
        Xf v τ a b)).re) = _
      rw [this]
      rfl
    rw [hom]
    generalize Xf v = X
    have kE : Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
        (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) * Gs Z *
        Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
          (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) =
        Gs (Z + X) := by
      simp only [Gs]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [Pi.add_apply]
      push_cast
      simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have h := entry (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
      push_cast at h ⊢
      linear_combination h
    rw [← kE]
    have := hGs Z
    field_simp
  · funext Y
    show (Gs (δ⁻¹ • Y))⁻¹ * f (GlobalTheory.FockCompare.iotaW σ T S (zf (δ⁻¹ • Y))) = _
    rw [hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, hz1, ← mul_assoc, inv_mul_cancel₀ (hGs _), one_mul]
  · have h1 : δ • Xf (-a) = δ • Xf (-b) := hab
    have h2 := congrArg zf (smul_right_injective _ hδ h1)
    rw [hzX, hzX] at h2
    exact neg_injective (GlobalTheory.VacUnique.infRat_injective S T h2)

private theorem mem_of_eigen {V : Type} [AddCommGroup V] [Module ℂ V] {H : Formalism.L2.Th1.H.Sesq V} (hH : Formalism.L2.Th1.H.IsHerm H)
    {α : V → ℂ} {A : AddSubgroup V} (hsd : Formalism.L2.Th1.H.IsSelfDual H A) (hα : Formalism.L2.Th1.H.IsSemiChar H A α) {F : V → ℂ}
    (hF : F ∈ Formalism.L2.Th1.H.fixedBy H α A) (hne : F ≠ 0) {x : V} {ε : ℂ} (hε : ε ≠ 0)
    (hx : Formalism.L2.Th1.H.opU H x F = ε • F) : x ∈ A := by
  refine hsd.le fun y hy => (GlobalTheory.ThetaInter.chi_eq_one_iff x y).1 ?_
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hne
  have h1 := GlobalTheory.ThetaInter.opU_comm hH x y F z
  have hx' : Formalism.L2.Th1.H.opU H x F = fun w => ε * F w := hx
  rw [hx', GlobalTheory.ThetaInter.opU_mul, GlobalTheory.ThetaInter.opU_of_fixed hα hF hy, GlobalTheory.ThetaInter.opU_mul, hx'] at h1
  have ha : α y ≠ 0 := left_ne_zero_of_mul_eq_one (GlobalTheory.ThetaInter.alpha_sq hα hy)
  have h0 : ε * (α y * F z) ≠ 0 := mul_ne_zero hε (mul_ne_zero ha hz)
  apply mul_right_cancel₀ h0
  rw [← h1]
  ring

private theorem jets_of_real {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) {δ : ℂ} (hδ : δ ≠ 0)
    (f : WO S T → ℂ) (Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ) (hΦd : Differentiable ℂ Φ)
    (hreal : ∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w))
    (k : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun τ => frS.1.map (tauE D τ))
        (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 =
        (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (fun Y => Φ (δ⁻¹ • Y)) := by
  have hdiff : Differentiable ℂ (fun Y : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank => Φ (δ⁻¹ • Y)) :=
    hΦd.comp ((differentiable_id).const_smul δ⁻¹)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ = fun Y => Φ (δ⁻¹ • Y) := ⟨_, rfl⟩
  rw [← hΘ] at hdiff ⊢
  have hΦeq : Φ = fun z => Θ (δ • z) := by
    funext z
    simp only [hΘ, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have hj := GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hψ hθ hS hT f Φ hΦd hreal k
  change pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) f
    (MvPolynomial.monomial k 1) 0 = _
  rw [hj, hΦeq, GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.applyAt0_monomial',
    GlobalTheory.FockPos.taylor_comp_smul' D _ hdiff]
  have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ =
      δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
    intro τ
    rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
  have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
      (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
    simp only [hper, Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hprod, mul_pow]
  ring

set_option maxHeartbeats 1600000 in

private theorem jets_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hSg : S.SigOK) (hTg : T.SigOK)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1)
    {δ : ℂ} (hC : Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ)
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {Ls Ls' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {Lt Lt' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hLs : SD D Ls) (hLs' : SD D Ls') (hLt : SD D Lt) (hLt' : SD D Lt')
    {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {s : GA D S} {s' : GA D T} (hs : SuppAt e S s) (hs' : SuppAt e T s')
    {x₀ y₀ : (Formalism.L2.Theta.AE D)ˣ} (hx₀ : IsDetAt e S s x₀) (hy₀ : IsDetAt e T s' y₀)
    (hmove : ∀ u : WO S T, u ∈ (latO S T (inV frS Ls') (inV frT Lt') fun _ => True) ↔
      ∃ u₀ ∈ (latO S T (inV frS Ls) (inV frT Lt) fun _ => True), u = actO S T s s' u₀)
    {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT (inV frS Ls) (inV frT Lt) f) :
    ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Θ ∧
      (∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ))
        (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 =
        (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ) ∧
      Differentiable ℂ (Iop D (tor0 D D.host.ccK δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt)
        (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls' Lt') Θ) ∧
      ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ))
        (fun τ => frT.1.map (tauE D τ)) (om (s, s') f) (MvPolynomial.monomial k 1) 0 =
        (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * ((splitFacO χS χT x₀ y₀ : ℂ) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (Iop D (tor0 D D.host.ccK δ)
            (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls' Lt') Θ)) := by
  have hδ : δ ≠ 0 := GlobalTheory.InertSign.delta_ne_zero hC
  have hsS := GlobalTheory.FockPos.cart_one frS hS hcS
  have hsT := GlobalTheory.FockPos.cart_one frT hT hcT
  subst hsS hsT
  have hψ := hf.1
  have hθ := hf.2.inf
  have hom := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) _ _ _ _ s s' (fun τ => by rw [GlobalTheory.SplitScalar.compAt_mt he hs])
    (fun τ => by rw [GlobalTheory.SplitScalar.compAt_mt he hs']) hmove f hf
  obtain ⟨rd, P, hrd, hrdΦ, hP, hPinj⟩ := exists_reading hψ hθ frS frT hS hT hδ
  have hH := GlobalTheory.ThetaInter.isHerm_sesqOf D (tor0 D D.host.ccK δ) S.rank T.rank
  have key : ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
      SD D Ls → SD D Lt → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (inV frS Ls) (inV frT Lt) f →
      rd f ∈ Formalism.MainNotions.TaylorLogMetric.Th D (tor0 D D.host.ccK δ) Ls Lt ∧ rd f ≠ 0 ∧
      (∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun τ => frS.1.map (tauE D τ))
        (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 =
        (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (rd f)) ∧
      (∀ γ, GlobalTheory.LatVac.finTens 1 γ ∈ (latO S T (inV frS Ls) (inV frT Lt) fun _ => True) ↔
        P γ ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt) ∧
      ∀ z ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt, ∃ γ, z = P γ := by
    intro Ls Lt hLs hLt f hf
    obtain ⟨Φ, hΦd, hreal⟩ := GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T frS frT _ _ hS hT f hf
    have hTh := GlobalTheory.T.unitVacuumEntireFactor_isTheta_movedLattices ψ θ S T frS frT hS hT δ hC hδ Ls Lt hLs hLt f hf Φ hΦd hreal
    have hr := hrdΦ f Φ hreal
    have hne : rd f ≠ 0 := by
      intro h0
      obtain ⟨w, hw, hfw⟩ := GlobalTheory.T.exists_finitePartZero_ne_of_isVacuum_orientedModel ψ θ S T _ _ _ _ f hf
      apply hfw
      have h1 := congrFun (hr.symm.trans h0) (δ • GlobalTheory.FockPos.zCo θ frS frT w)
      simp only [smul_smul, inv_mul_cancel₀ hδ, one_smul, Pi.zero_apply] at h1
      rw [hreal w hw, h1, mul_zero]
    obtain ⟨-, -, hsd, hα⟩ := GlobalTheory.ThetaInter.klat_facts hC (A := Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt)
      (Or.inr ⟨Ls, Lt, hLs, hLt, rfl⟩)
    rw [← hr] at hTh
    refine ⟨hTh, hne, fun k => by rw [hr]; exact jets_of_real hψ hθ frS frT hS hT hδ f Φ hΦd hreal k,
      fun γ => ⟨fun hγ => ?_, fun hγ => ?_⟩, fun z hz => ?_⟩
    · obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S frS hS Ls hLs
      obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T frT hT Lt hLt
      rw [← hΛS, ← hΛT] at hf hγ
      obtain ⟨ε, hε1, hε⟩ := (GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hSd hTd).2.2 f hf.2.lat _ hγ
      refine mem_of_eigen hH hsd hα hTh.2 hne (ε := ε) (by rcases hε1 with rfl | rfl <;> norm_num) ?_
      rw [← hrd f hf.2.theta, hε f hf.2.lat, map_smul]
    · obtain ⟨v, hv, hvx⟩ := GlobalTheory.ThetaLawMoved.mem_La_frame_sd S T frS frT hS hT Ls Lt hLs δ _ hγ
      rw [← hP] at hvx
      rw [hPinj hvx]
      have : GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (inV frS Ls) (inV frT Lt) fun _ => True := by
        rw [AddMonoidHom.map_neg]; exact neg_mem hv
      exact this
    · obtain ⟨v, -, hvx⟩ := GlobalTheory.ThetaLawMoved.mem_La_frame_sd S T frS frT hS hT Ls Lt hLs δ _ hz
      exact ⟨-v, hvx.trans (hP v).symm⟩
  obtain ⟨t1, -, j1, d1, -⟩ := key Ls Lt hLs hLt f hf
  obtain ⟨t2, n2, j2, d2, r2⟩ := key Ls' Lt' hLs' hLt' _ hom
  have hK1 : KLat D (tor0 D D.host.ccK δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt) := Or.inr ⟨Ls, Lt, hLs, hLt, rfl⟩
  have hK2 : KLat D (tor0 D D.host.ccK δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls' Lt') := Or.inr ⟨Ls', Lt', hLs', hLt', rfl⟩
  obtain ⟨-, -, -, hα₁⟩ := GlobalTheory.ThetaInter.klat_facts hC hK1
  obtain ⟨-, -, hsd₂, hα₂⟩ := GlobalTheory.ThetaInter.klat_facts hC hK2
  obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S frS hS Ls hLs
  obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T frT hT Lt hLt
  obtain ⟨ΛS', hΛS', hSd'⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S frS hS Ls' hLs'
  obtain ⟨ΛT', hΛT', hTd'⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T frT hT Lt' hLt'
  rw [← hΛS, ← hΛT] at hf d1 hmove
  rw [← hΛS', ← hΛT'] at d2 hmove
  have hidx := GlobalTheory.ThetaTriple.index_ne_zero hC hK1 hK2
  have hmain : rd (om (s, s') f) = fun z => (splitFacO χS χT x₀ y₀ : ℂ) * Iop D (tor0 D D.host.ccK δ)
      (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls' Lt') (rd f) z :=
    moves_gen hθ hSg hTg hcS hcT hW hSd hSd' hTd hTd' he hs hs' hx₀ hy₀ hmove hH rd P hrd d1 d2 r2 hsd₂ hα₁ hα₂
      hidx hf t1.2 t2.2 n2
  have hdI : Differentiable ℂ (Iop D (tor0 D D.host.ccK δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt)
      (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls' Lt') (rd f)) :=
    (GlobalTheory.theta_translation_intertwiner_unitary D D.host.ccK δ hC _ _ _ _ hK1 hK2 _ t1).2.1.1
  refine ⟨rd f, t1.1, j1, hdI, fun k => ?_⟩
  rw [j2 k, hmain, GlobalTheory.MovedKappa.applyAt0_const_mul D _ hdI]

private theorem latO_neg {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P = latO S T LS LT P := by
  refine le_antisymm ?_ (GlobalTheory.VacConj.latO_le S T LS LT P)
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

private theorem actO_mul {D : D7} (S T : HSp D) (g a : GA D S) (h b : GA D T) (w : WO S T) :
    actO S T (g * a) (h * b) w = actO S T g h (actO S T a b w) := by
  simp only [actO]
  rw [_root_.mul_inv_rev, GlobalTheory.LatMoveStd.mt_mul'', GlobalTheory.LatMoveStd.mt_mul'']
  simp only [Matrix.mul_assoc]

private theorem move_of_onto {D : D7} {S T : HSp D} {g a : GA D S} {h b : GA D T} {Λ₀ Λ Λ' : AddSubgroup (WO S T)}
    (h1 : (∀ w ∈ Λ₀, actO S T a b w ∈ Λ) ∧ ∀ w' ∈ Λ, ∃ w ∈ Λ₀, actO S T a b w = w')
    (h2 : (∀ w ∈ Λ₀, actO S T (g * a) (h * b) w ∈ Λ') ∧ ∀ w' ∈ Λ', ∃ w ∈ Λ₀, actO S T (g * a) (h * b) w = w') (u : WO S T) :
    u ∈ Λ' ↔ ∃ u₀ ∈ Λ, u = actO S T g h u₀ := by
  constructor
  · intro hu
    obtain ⟨w, hw, rfl⟩ := h2.2 u hu
    exact ⟨_, h1.1 w hw, actO_mul S T g a h b w⟩
  · rintro ⟨u₀, hu₀, rfl⟩
    obtain ⟨w, hw, rfl⟩ := h1.2 u₀ hu₀
    rw [← actO_mul]
    exact h2.1 w hw

private theorem exists_detAt {D : D7} {e : Formalism.L2.Theta.AE D} (he : e * e = e) (V : HSp D) (g : GA D V) :
    ∃ x : (Formalism.L2.Theta.AE D)ˣ, IsDetAt e V g x := by
  have hu : IsUnit (mt V g).det := (Matrix.isUnit_iff_isUnit_det _).1 (matHom V g).isUnit
  obtain ⟨d', hd⟩ := hu.exists_right_inv
  have h1 : (e * (mt V g).det + (1 - e)) * (e * d' + (1 - e)) = 1 := by
    linear_combination (e * e) * hd + (2 - (mt V g).det - d') * he
  exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

private theorem inv_shape {R : Type} [CommRing R] {e a : R} (he : e * e = e) {x : Rˣ} (hx : (x : R) = e * a + (1 - e)) :
    ((x⁻¹ : Rˣ) : R) = e * ((x⁻¹ : Rˣ) : R) + (1 - e) := by
  have h1 : (x : R) * ((x⁻¹ : Rˣ) : R) = 1 := x.mul_inv
  rw [hx] at h1
  linear_combination (1 - e) * h1 + ((a - 1) * ((x⁻¹ : Rˣ) : R)) * he

private theorem jets_transfer {D : D7} {N N' : ℕ} (T0 : Tor D) (A B : AddSubgroup (Formalism.MainNotions.TaylorLogMetric.VC D N N')) {δ : ℂ} (hδ : δ ≠ 0)
    {Θ₀ Θ : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ} (h0 : Differentiable ℂ Θ₀) (h : Differentiable ℂ Θ)
    (hI : Differentiable ℂ (Iop D T0 A B Θ₀)) {c : ℂ} (hc : c ≠ 0)
    (hj : ∀ k : FVar D N' N →₀ ℕ,
      (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ₀ =
      c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ))
    (a : ℂ) (k : FVar D N' N →₀ ℕ) :
    (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) *
        (a * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (Iop D T0 A B Θ₀)) =
      c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) *
        Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => a * Iop D T0 A B Θ z) := by
  have hper : ∀ k : FVar D N' N →₀ ℕ, (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) ≠ 0 := fun k => by
    refine Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (div_ne_zero hδ ?_)
    have : 0 < 2 * Real.pi * ‖tauE D v.1 D.host.xi0‖ := by
      rw [GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq]
      obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
      have : 0 < Formalism.L2.Pj.xiR D := by
        rw [hxi]
        have h1 : (0 : ℝ) < Ideal.absNorm D.host.ccK := by linarith
        have h2 : (0 : ℝ) < Real.sqrt D.host.d := by linarith
        positivity
      positivity
    exact_mod_cast (Real.sqrt_pos.2 this).ne'
  have e : Θ₀ = fun z => c * Θ z := by
    refine GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq _ _ h0 (h.const_mul c) fun k => ?_
    rw [GlobalTheory.MovedKappa.applyAt0_const_mul D _ h]
    apply mul_left_cancel₀ (hper k)
    rw [hj k]
    ring
  have e2 : Iop D T0 A B Θ₀ = fun z => c * Iop D T0 A B Θ z := by
    funext z
    rw [e]
    unfold Formalism.MainNotions.TaylorLogMetric.Iop
    rw [mul_left_comm, mul_finsum _ c]
    congr 1
    refine finsum_congr fun q => ?_
    simp only [Formalism.MainNotions.TaylorLogMetric.U]; ring
  have hI' : Differentiable ℂ (Iop D T0 A B Θ) := by
    have e3 : Iop D T0 A B Θ = fun z => c⁻¹ * Iop D T0 A B Θ₀ z := by
      funext z
      rw [e2, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [e3]
    exact hI.const_mul _
  rw [e2, GlobalTheory.MovedKappa.applyAt0_const_mul D _ hI', GlobalTheory.MovedKappa.applyAt0_const_mul D _ hI']
  ring

end GlobalTheory.SplitMoveFrames

open GlobalTheory.SplitMoveFrames in
set_option maxHeartbeats 1600000 in
theorem _root_.GlobalTheory.T.split_idempotent_lattice_pair : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ x₀ y₀ : (Formalism.L2.Theta.AE D)ˣ, (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) ∧ (∃ b : Formalism.L2.Theta.AE D, (y₀ : Formalism.L2.Theta.AE D) = e * b + (1 - e) ∨ (y₀ : Formalism.L2.Theta.AE D) = cA D e * b + (1 - cA D e)) ∧ ∃ ζ : ℂ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ ∃ r : ℝ, 0 < r ∧
      ∀ Θ : Formalism.MainNotions.TaylorLogMetric.VC D (ch.G.pS p).rank (ch.G.pT p).rank → ℂ, Differentiable ℂ Θ →
      (∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ, fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ)) →
      ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
        fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p (s : Formalism.L2.Theta.GA D (ch.G.V p.small)) (s' : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))) (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (fun z => (r : ℂ) * ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p (s * x) (s' * y)) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p (s * x) (s' * y))) Θ z)) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y e he s s' hs hs'
  have hC := ch.S.Z.crv
  have hδ : ch.S.Z.δ ≠ 0 := GlobalTheory.InertSign.delta_ne_zero hC
  have hsd := GlobalTheory.T.lattices_self_dual_moved_pair hP hI ch hch p hp x y
  have hsd' := GlobalTheory.T.lattices_self_dual_moved_pair hP hI ch hch p hp (s * x) (s' * y)
  have hvac := GlobalTheory.T.vacuum_vector_moved_pair hP hI ch hch p hp x y
  have hact := GlobalTheory.T.lattice_orbit_vectors_moved_pair hP hI ch hch p hp x y
  have hact' := GlobalTheory.T.lattice_orbit_vectors_moved_pair hP hI ch hch p hp (s * x) (s' * y)
  have hc0 : (ch.S.Z.c0 p : ℂ) ≠ 0 := Units.ne_zero _
  have hn := DefPair.nodes hp
  obtain ⟨x₀, hx₀⟩ := exists_detAt he.1 _ (s : Formalism.L2.Theta.GA D (ch.G.V p.small))
  obtain ⟨y₀, hy₀⟩ := exists_detAt he.1 _ (s' : Formalism.L2.Theta.GA D (ch.G.V p.big))
  rw [mul_assoc s, mul_assoc s', Subgroup.coe_mul _ s, Subgroup.coe_mul _ s'] at hact'
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have hW := GlobalTheory.ConjDict.weil_cjOm _ _ _ _ _ _ (ch.W.om_is (.chi i D.R.m) ⟨hi, le_rfl⟩)
    have hconj := GlobalTheory.T.isVacuum_conj_of_negHermitianSpace ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) _ _ _ hvac
    simp only [GridData.toPair, map_mul] at hact hact'
    have hmove := move_of_onto hact hact'
    rw [latO_neg, latO_neg] at hmove
    obtain ⟨Θ₀, hd0, hj0, hdI, hj1⟩ := jets_move (hn.2.sigOK ch.G) (hn.1.sigOK ch.G)
      (ch.W.cart_is _ ⟨hi, le_rfl⟩) (ch.W.cart_is _ ⟨by omega, le_rfl⟩)
      (ch.S.N.fr (.grid (i + 1) D.R.m)) (ch.S.N.fr (.grid i D.R.m))
      (ch.S.N.fr_on _ ⟨hi, rfl⟩) (ch.S.N.fr_on _ ⟨by omega, rfl⟩) hC hW hsd.1 hsd'.1 hsd.2 hsd'.2 he hs' hs hy₀ hx₀
      hmove hconj
    refine ⟨y₀⁻¹, x₀⁻¹, ⟨_, Or.inl (inv_shape he.1 hy₀)⟩, ⟨_, Or.inl (inv_shape he.1 hx₀)⟩, 1, ⟨1, one_pos, one_pow 1⟩,
      1, one_pos, fun Θ hΘ hjet k => ?_⟩
    have h2 := fun f k => GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.frC (.grid (i + 1) D.R.m))
      (ch.S.N.frC (.grid i D.R.m)) f ch.W.ψ_std ch.W.θ_is k 0
    have hc0' : starRingEnd ℂ (ch.S.Z.c0 (.chi i D.R.m) : ℂ) ≠ 0 := (map_ne_zero _).2 hc0
    have ht := jets_transfer _ _ _ hδ hd0 hΘ hdI hc0' (fun k => by
      have h3 := (h2 _ k).symm.trans (hjet k)
      erw [hj0 k] at h3
      have h4 := congrArg (starRingEnd ℂ) h3
      rw [Complex.conj_conj, map_mul] at h4
      exact h4.trans (congrArg _ (Complex.conj_conj _)))
      (splitFacO (ch.G.chrS (.chi i D.R.m))⁻¹ (ch.G.chrT (.chi i D.R.m))⁻¹ y₀ x₀ : ℂ) k
    have hj := hj1 k
    rw [GlobalTheory.ConjDict.cjOm_apply] at hj
    erw [GlobalTheory.ConjWeil.cj_id_cj_id] at hj
    refine (h2 _ k).trans ?_
    refine (congrArg (starRingEnd ℂ) (hj.trans ht)).trans ?_
    rw [map_mul, Complex.conj_conj]
    simp only [splitFacO, MonoidHom.inv_apply, map_inv, Complex.ofReal_one, one_mul]
    rfl
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    have hj1' : j + 1 ≤ D.R.m := hp
    have hW := ch.W.om_is (.top t j) (by show j + 1 ≤ D.R.m; exact hj1')
    have hmove := move_of_onto hact hact'
    obtain ⟨Θ₀, hd0, hj0, hdI, hj1⟩ := jets_move (hn.1.sigOK ch.G) (hn.2.sigOK ch.G)
      (ch.W.cart_is (.top j) (by show j ≤ D.R.m; omega)) (ch.W.cart_is (.top (j + 1)) hj1')
      (ch.S.N.fr (.top j)) (ch.S.N.fr (.top (j + 1)))
      (ch.S.N.fr_on (.top j) (by show j ≤ D.R.m; omega)) (ch.S.N.fr_on (.top (j + 1)) hj1') hC hW
      hsd.1 hsd'.1 hsd.2 hsd'.2 he hs hs' hx₀ hy₀ hmove hvac
    refine ⟨x₀, y₀, ⟨_, Or.inl hx₀⟩, ⟨_, Or.inl hy₀⟩, 1, ⟨1, one_pos, one_pow 1⟩, 1, one_pos, fun Θ hΘ hjet k => ?_⟩
    have ht := jets_transfer _ _ _ hδ hd0 hΘ hdI hc0 (fun k => (hj0 k).symm.trans (hjet k))
      (splitFacO (ch.G.chrS (.top t j)) (ch.G.chrT (.top t j)) x₀ y₀ : ℂ) k
    refine ((hj1 k).trans ht).trans ?_
    simp only [splitFacO, Complex.ofReal_one, one_mul]
    rfl

end
