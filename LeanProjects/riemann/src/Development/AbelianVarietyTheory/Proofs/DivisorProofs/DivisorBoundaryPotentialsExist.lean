import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundaryPotentialSnc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorPotentialIsSNCBoundary

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CurvInterp

namespace GlobalTheory.DivSec

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {m : ℕ} {C : Fin m → Closeds Y.X}
  {n : Fin m → Pts Y σ → ℝ} (hn : ∀ i, IsDivNorm (Y.an σ) (C i) (n i))

def compPot (i : Fin m) : LocPot (Pts Y σ) where
  U := (divPot hn).U
  isOpen_U := (divPot hn).isOpen_U
  mem_U := (divPot hn).mem_U
  φ y z := eqF hn i y z / 2

def compSec (i : Fin m) (y z : Pts Y σ) : ℂ := ev Y.str σ (eqV hn i y).1 (eqT hn i y) z

theorem norm_compSec_mul {i : Fin m} {y z : Pts Y σ} (hz : z ∈ (divPot hn).U y) :
    ‖compSec hn i y z‖ * Real.exp (-(compPot hn i).φ y z) = n i z := by
  have e := (eq_spec hn i y).2.2.2 z (mem_eqV hn hz i)
  have h0 := ((hn i).1 z).1
  have hx : Real.exp (-eqF hn i y z) = Real.exp (-eqF hn i y z / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hx, ← mul_pow] at e
  have h1 := (pow_left_inj₀ h0 (by positivity) two_ne_zero).1 e
  simp only [compSec, compPot]
  rw [h1, neg_div]

theorem isSection_compSec {B : FinHolAtlas Y.dim (Pts Y σ)} (hB : IsAlgAtlas B) (i : Fin m) :
    IsSection B (compPot hn i) (compSec hn i) :=
  ⟨fun y => (hB.holoOn_iff (Y.an σ) ((divPot hn).isOpen_U y)).2 fun j =>
      ((Y.an σ).holoOn_ev _ (eqT hn i y) j).mono fun v hv => ⟨hv.1, mem_eqV hn hv.2 i⟩,
    fun _ _ _ hz => by rw [norm_compSec_mul hn hz.1, norm_compSec_mul hn hz.2]⟩

theorem isPotential_compPot (B : FinHolAtlas Y.dim (Pts Y σ)) (hB : IsAlgAtlas B)
    (hsnc : ∀ y : Y.X, LSncAt Y.X C y) (i : Fin m) : IsPotential B (compPot hn i) := by
  have hgen := generic_not_mem hsnc
  refine ⟨fun x => (hB.smoothOn_iff (Y.an σ) ((divPot hn).isOpen_U x)).2 ?_, fun x x' y hy => ?_⟩
  · have h : (Y.an σ).SmoothOn ((divPot hn).U x) (fun z => eqF hn i x z / 2) := fun j =>
      (((eq_spec hn i x).2.2.1.mono fun z hz => mem_eqV hn hz i) j).div_const 2
    exact h
  · obtain ⟨W, hW, hyW, G, hG, he⟩ := GlobalTheory.T.smooth_ratio_of_local_generators F Y σ (C i) (n i) _ _ _ _ _ _ ⟨_, hgen i⟩
      (eq_spec hn i x).2.1 (eq_spec hn i x').2.1 (eq_spec hn i x).2.2.1 (eq_spec hn i x').2.2.1
      (eq_spec hn i x).2.2.2 (eq_spec hn i x').2.2.2 y ⟨mem_eqV hn hy.1 i, mem_eqV hn hy.2 i⟩
    refine ⟨W, hW, hyW, fun z => G z / 2, (hB.holoOn_iff (Y.an σ) hW).2 fun j => ?_, fun z hz => ?_⟩
    · exact ((hG j).mul_const (2⁻¹ : ℂ)).congr fun v _ => by simp [div_eq_mul_inv]
    · have h := he z ⟨⟨hz.1.1, mem_eqV hn hz.1.2 i⟩, mem_eqV hn hz.2 i⟩
      simp only [compPot]
      rw [← sub_div, h, Complex.div_ofNat_re]

theorem isSNC_compSec (B : FinHolAtlas Y.dim (Pts Y σ)) (hB : IsAlgAtlas B) (hsnc : ∀ y : Y.X, LSncAt Y.X C y)
    (i : Fin m) : IsSNC B (compPot hn i) (compSec hn i) (Pi.single i 1) (fun k => {z | LiesIn z (C k)}) := by

  classical
  intro x
  let S : Finset (Fin m) := Finset.univ.filter fun i => LiesIn x (C i)
  have hS : ∀ i, i ∈ S ↔ LiesIn x (C i) := fun i => by simp [S]
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := Y.dim) (p := Y.str) (σ := σ) x
  let W : Y.X.Opens := Finset.univ.inf fun i => (eqV hn i x).1
  have hWle : ∀ i, W ≤ (eqV hn i x).1 := fun i => Finset.inf_le (Finset.mem_univ i)
  have hmemI : ∀ (z : Pts Y σ) (s : Finset (Fin m)), z ∈ ptsIn Y.str σ (s.inf fun i => (eqV hn i x).1) ↔
      ∀ i ∈ s, z ∈ ptsIn Y.str σ (eqV hn i x).1 := by
    intro z s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.inf_insert, mem_ptsIn_inf, ih, Finset.forall_mem_insert]
  have hWU : ptsIn Y.str σ W = (divPot hn).U x := by
    ext z
    rw [hmemI z Finset.univ]
    simp only [divPot, Set.mem_iInter, Finset.mem_univ, true_implies]
  have hxW : x ∈ ptsIn Y.str σ W := hWU ▸ (divPot hn).mem_U x
  let ix : Fin S.card → Fin m := fun j => (S.equivFin.symm j).1
  have hix : Function.Injective ix := fun i j h => S.equivFin.symm.injective (Subtype.ext h)
  have hixS : ∀ j, LiesIn x (C (ix j)) := fun j => (hS _).1 (S.equivFin.symm j).2
  let g : Fin S.card → Γ(Y.X, W) := fun j => resG Y.X (hWle (ix j)) (eqT hn (ix j) x)
  have hgev : ∀ i z, z ∈ ptsIn Y.str σ W →
      ev Y.str σ W (resG Y.X (hWle i) (eqT hn i x)) z = ev Y.str σ _ (eqT hn i x) z :=
    fun i z hz => ev_res _ hz _
  have hzero : ∀ i z, z ∈ ptsIn Y.str σ W →
      (ev Y.str σ _ (eqT hn i x) z = 0 ↔ LiesIn z (C i)) := fun i z hz =>
    ev_eq_zero_iff (eq_spec hn i x).2.1 (ptsIn_mono (hWle i) hz)
  have h0 : ∀ j, ev Y.str σ W (g j) x = 0 := fun j => by
    simp only [g]; rw [hgev _ _ hxW]; exact (hzero _ _ hxW).2 (hixS j)
  have hliA := linearIndependent_fderiv_eqns F Y.X Y.str Y.dim σ inferInstance c x hc m C (hsnc _) (fun i => eqV hn i x)
    (fun i => eqT hn i x) (fun i => (eq_spec hn i x).1) (fun i => (eq_spec hn i x).2.1)
  have hli : LinearIndependent ℂ (fun j => fderiv ℂ (ev Y.str σ W (g j) ∘ c.e.symm) (c.e x)) := by
    have h2 := hliA.comp (fun j => (⟨ix j, hixS j⟩ : {i : Fin m // x.1 (IsLocalRing.closedPoint ℂ) ∈ C i}))
      (by intro a b h; exact hix (by simpa using congrArg Subtype.val h))
    convert h2 using 1
    funext j
    have e : ev Y.str σ W (g j) ∘ c.e.symm =ᶠ[nhds (c.e x)]
        ev Y.str σ _ (eqT hn (ix j) x) ∘ c.e.symm :=
      Filter.eventually_of_mem ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn W)).mem_nhds
        (GlobalTheory.ChartGlue.mem_over c.e hc hxW)) fun v hv => hgev _ _ hv.2
    simp only [Function.comp_apply]
    exact e.fderiv_eq
  have hcard : S.card ≤ Y.dim := by
    have := hli.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V Y.dim) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, -, hhol, hsymm, hev⟩ :=
    SncChart.exists_chart_of_fderiv F Y.X Y.str Y.dim σ c x hc W hxW S.card g h0 hli
  let O : Set (Pts Y σ) := (divPot hn).U x ∩ ⋂ k, {z | LiesIn x (C k) ∨ ¬ LiesIn z (C k)}
  have hO : IsOpen O := by
    refine ((divPot hn).isOpen_U x).inter (isOpen_iInter_of_finite fun k => ?_)
    by_cases h : LiesIn x (C k)
    · simp [h]
    · simpa [h] using isOpen_not_liesIn (p := Y.str) (σ := σ) (C k)
  let ψ := e.restrOpen O hO
  have hψs : ψ.source = e.source ∩ O := e.restrOpen_source O hO
  have hψa : ∀ z, ψ z = e z := fun z => rfl
  have hψW : ∀ z ∈ ψ.source, z ∈ ptsIn Y.str σ W := fun z hz => hsub (hψs ▸ hz).1
  have hψO : ∀ z ∈ ψ.source, z ∈ O := fun z hz => (hψs ▸ hz).2
  have hcompat : IsCompatChart B ψ := by
    refine isCompatChart_of_holAlong F Y.X Y.str σ Y.dim B hB ψ (fun j => ?_) ?_
    · intro V _ _ _ B' y hB' hy hm
      exact hhol j V B' y hB' hy (fun b hb => (hψs ▸ hm hb).1)
    · exact GlobalTheory.LocLift.isHolTo_mono hsymm ψ.open_target fun z hz => hz.1
  let pos : ∀ k, LiesIn x (C k) → Fin Y.dim := fun k hk =>
    ⟨S.equivFin ⟨k, (hS k).2 hk⟩, lt_of_lt_of_le (Fin.isLt _) hcard⟩
  let τ : Fin m → Option (Fin Y.dim) := fun k => if hk : LiesIn x (C k) then some (pos k hk) else none
  have hτ : ∀ k (hk : LiesIn x (C k)) z, z ∈ ψ.source → ψ z (pos k hk) = ev Y.str σ _ (eqT hn k x) z := by
    intro k hk z hz
    rw [hψa, hev z (hψs ▸ hz).1 (pos k hk) (S.equivFin ⟨k, (hS k).2 hk⟩).isLt]
    have hj : (⟨(pos k hk : ℕ), (S.equivFin ⟨k, (hS k).2 hk⟩).isLt⟩ : Fin S.card) = S.equivFin ⟨k, (hS k).2 hk⟩ := rfl
    have hk' : ix (S.equivFin ⟨k, (hS k).2 hk⟩) = k := by simp [ix]
    rw [hj]
    simp only [g]
    rw [hgev _ _ (hψW z hz)]
    rw [hk']
  refine ⟨ψ, hcompat, hψs ▸ ⟨hx0, (divPot hn).mem_U x, Set.mem_iInter.2 fun k => ?_⟩,
    fun z hz => (hψO z hz).1, τ, ?_, ?_, ?_⟩
  · by_cases h : LiesIn x (C k)
    · exact Or.inl h
    · exact Or.inr h
  · intro k k' i h1 h2
    simp only [τ] at h1 h2
    split_ifs at h1 h2 with hk hk'
    have := (Option.some.inj h1).trans (Option.some.inj h2).symm
    have h3 : S.equivFin ⟨k, (hS k).2 hk⟩ = S.equivFin ⟨k', (hS k').2 hk'⟩ := Fin.ext (by simpa [pos] using congrArg Fin.val this)
    exact congrArg Subtype.val (S.equivFin.injective h3)
  · intro k
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, τ]
    constructor
    · rintro ⟨hzk, hz⟩
      refine ⟨hz, ?_⟩
      by_cases hk : LiesIn x (C k)
      · refine ⟨pos k hk, by simp [hk], ?_⟩
        rw [hτ k hk z hz]
        exact (hzero k z (hψW z hz)).2 hzk
      · exact absurd hzk ((Set.mem_iInter.1 (hψO z hz).2 k).resolve_left hk)
    · rintro ⟨hz, i, hi, h0⟩
      refine ⟨?_, hz⟩
      by_cases hk : LiesIn x (C k)
      · simp only [hk, dite_true, Option.some.injEq] at hi
        subst hi
        rw [hτ k hk z hz] at h0
        exact (hzero k z (hψW z hz)).1 h0
      · simp [hk] at hi
  · by_cases hi : LiesIn x (C i)
    · refine ⟨fun _ => 1, fun j => by exact analyticOnNhd_const, fun _ _ => one_ne_zero, fun z hz => ?_⟩
      show compSec hn i x z = 1 * _
      rw [one_mul, Finset.prod_eq_single i (fun k _ hk => by simp only [τ]; split_ifs <;> simp [Pi.single_apply, hk]) (by simp)]
      simp only [τ, hi, dite_true, Pi.single_eq_same, pow_one]
      exact (hτ i hi z hz).symm
    · refine ⟨fun z => ev Y.str σ _ (eqT hn i x) z, ?_, fun z hz h => ?_, fun z hz => ?_⟩
      · refine (hB.holoOn_iff (Y.an σ) ψ.open_source).2 fun j => ?_
        exact ((Y.an σ).holoOn_ev _ (eqT hn i x) j).mono fun v hv => ⟨hv.1, ptsIn_mono (hWle i) (hψW _ hv.2)⟩
      · exact (Set.mem_iInter.1 (hψO z hz).2 i).resolve_left hi ((hzero i z (hψW z hz)).1 h)
      · rw [Finset.prod_eq_one fun k _ => ?_, mul_one]
        · rfl
        · by_cases hk : k = i
          · subst hk; simp only [τ, hi, dite_false]
          · simp only [τ]; split_ifs <;> simp [Pi.single_apply, hk]

end GlobalTheory.DivSec

namespace GlobalTheory.DivSec

theorem isBoundary_of_divNorm : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (m : ℕ) (C : Fin m → Closeds Y.X) (n : Fin m → Pts Y (I.ε a) → ℝ), Y.dim = e → (∀ y : Y.X, LSncAt Y.X C y) → (∀ i, IsDivNorm (Y.an (I.ε a)) (C i) (n i)) → ∃ (L : Fin m → LocPot (M.X a)) (t : Fin m → M.X a → M.X a → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.IsBoundary (M.A a) L t (fun i => {z | under (I.pt a z) ∈ C i}) ∧ ∀ i z, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.normSec (L i) (t i) z = n i (I.pt a z) := by
  intro F _ _ Y e M I a m C n hdim hsnc hn
  subst hdim
  have hA : ChartsAlg (M.A a) (I.pt a) := I.alg a
  refine ⟨fun i => (compPot hn i).pullback (I.pt a) (I.pt a).continuous,
    fun i x w => compSec hn i (I.pt a x) (I.pt a w), fun i =>
    ⟨isPotential_pullback hA (isPotential_compPot hn _ (isAlgAtlas_algAtlas hA) hsnc i),
     isSection_pullback hA (isSection_compSec hn (isAlgAtlas_algAtlas hA) i),
     isSNC_pullback hA (isSNC_compSec hn _ (isAlgAtlas_algAtlas hA) hsnc i), fun y => ?_⟩, fun i z => ?_⟩
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.normSec, LocPot.pullback]
    rw [norm_compSec_mul hn ((divPot hn).mem_U _)]
    exact ((hn i).1 _).2
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.normSec, LocPot.pullback]
    exact norm_compSec_mul hn ((divPot hn).mem_U _)

end GlobalTheory.DivSec
