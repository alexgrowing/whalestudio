import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverNormsPullbackPower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
open scoped TensorProduct NNReal

namespace GlobalTheory.HalfGeo

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_cover_over_models {F : Type} [Field F] [NumberField F] (Y : Var F) (M₀ : TrueGeo.Model Y)
    (h₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₀.X) :
    ∀ (n : ℕ) (M : Fin n → TrueGeo.Model Y), ∃ V : Cover Y, ∀ i, ∃ b : V.X ⟶ (M i).X, V.j ≫ b = V.π ≫ (M i).j := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨Cover.ofModel M₀ h₀, fun i => i.elim0⟩
  | succ n ih =>
    intro M
    obtain ⟨V, hV⟩ := ih (fun i => M i.castSucc)
    obtain ⟨V', a, g, b, -, -, e₁, e₂, -, e₃⟩ := CoverDom.exists_cover_dominating F Y V (M (Fin.last n))
    refine ⟨V', fun i => ?_⟩
    induction i using Fin.lastCases with
    | last => exact ⟨b, e₃⟩
    | cast i =>
      obtain ⟨c, hc⟩ := hV i
      refine ⟨a ≫ c, ?_⟩
      rw [← Category.assoc, e₁, Category.assoc, hc, ← Category.assoc, e₂]

theorem normsAt_pow {F : Type} [Field F] [NumberField F] {Y : Var F} {V : Cover Y} {L : LB V.X} {p : ℕ}
    {W : Y.X.Opens} {f : Y.X → Y.Fn} {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ}
    (h : NormsAt V L p W f l) (k : ℕ) :
    NormsAt V (lbPow L k) p W (fun y => f y ^ k) fun v e y => (k : ℝ) * l v e y := by
  obtain ⟨r, hr, hu, hf⟩ := h
  have key : ∀ (g : Y.Fn) (i : ((lbPow L k).pull V.j).ι),
      V.φ (g ^ k) * ((r (fun _ => i PUnit.unit PUnit.unit) ^ k : V.G.functionFieldˣ) : V.G.functionField) =
        (V.φ g * (r (fun _ => i PUnit.unit PUnit.unit) : V.G.functionField)) ^ k := by
    intro g i
    rw [map_pow, Units.val_pow_eq_pow_val, mul_pow]
  refine ⟨fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ k, isRatSec_pull_pow L V.j k hr, ?_, ?_⟩
  · intro i x hx
    show UnitAt x (V.φ (f (V.π x) ^ k) * _)
    erw [key]
    exact InducedPow.unitAt_pow (hu _ x (InducedPow.mem_chart L V.j k hx)) k
  · intro v hv e y hy z yt i e₁ e₂ hi
    have hi' : ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit PUnit.unit) := fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
    have H := hf v hv e y hy z yt (fun _ => i PUnit.unit PUnit.unit) e₁ e₂ hi'
    have hmem : below z ∈ (L.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.U (i PUnit.unit PUnit.unit) := by
        rw [← e₂]
        exact hi' (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have hU := hu _ _ hmem
    rw [hπ] at hU
    show (k : ℝ) * l v e y = Real.log (e.w (TrueGeo.valAt z (V.φ (f (below y.1) ^ k) * _)))
    erw [key, InducedPow.valAt_pow _ hU.regAt, map_pow, Real.log_pow, H]

theorem normsAt_pull {F : Type} [Field F] [NumberField F] {Y : Var F} {Δ : Y.Dv} {φ : PtFn Y}
    (M : TrueGeo.Model Y) (L : LB M.X) (m : ℕ+) (r : (L.pull M.j).ι → Y.Fnˣ)
    (hr : Presents ((m : ℕ) • Δ) (L.pull M.j) r)
    (hφ : ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X) (i : (L.pull M.j).ι),
      spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) →
      ((m : ℕ) : ℝ) * φ v e y =
        Real.log (e.w (TrueGeo.valAt y.1 (((eqn Δ (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn))))
    (V : Cover Y) (c : V.X ⟶ M.X) (hc : V.j ≫ c = V.π ≫ M.j) (p : ℕ) :
    NormsAt V (L.pull c) p ⊤ (fun y => genAt Δ y ^ (m : ℕ)) fun v e y => ((m : ℕ) : ℝ) * φ v e y := by
  haveI := M.ar.isIntegral
  obtain ⟨hη, e⟩ := V.φ_eq_fnMap
  set ψ := SmallSec.fnMap V.π hη with hψ
  have hφV : ∀ t, V.φ t = ψ t := fun t => by rw [e]
  have hg (x : Y.X) := generatesAt_genAt_pow Δ m x
  have hch : ∀ (i : ((L.pull c).pull V.j).ι), ∀ x ∈ ((L.pull c).pull V.j).U i,
      V.π x ∈ (L.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) := by
    intro i x hx
    have h1 := Set.mem_iInter.1 (InducedPull.chart_le L c V.j i hx) PUnit.unit
    have h2 : (V.j ≫ c) x = M.j (V.π x) := by rw [hc]; rfl
    refine Set.mem_iInter.2 fun _ => ?_
    show M.j (V.π x) ∈ L.U _
    rw [← h2]
    exact h1
  let r' : ((L.pull c).pull V.j).ι → V.G.functionFieldˣ :=
    fun i => Units.map ψ.toMonoidHom (r fun _ => i PUnit.unit PUnit.unit)
  have hr' : ∀ i, (r' i : V.G.functionField) = ψ (r fun _ => i PUnit.unit PUnit.unit) := fun _ => rfl
  refine ⟨r', ?_, ?_, ?_⟩
  · intro i j hij
    have hmem : V.π (genericPoint V.G) ∈ (L.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (L.pull M.j).U (fun _ => j PUnit.unit PUnit.unit) := ⟨hch i _ hij.1, hch j _ hij.2⟩
    have h0 : genericPoint Y.X ∈ (L.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (L.pull M.j).U (fun _ => j PUnit.unit PUnit.unit) :=
      (genericPoint_specializes _).mem_open (TopologicalSpace.Opens.isOpen _) hmem
    have le : ((L.pull c).pull V.j).U i ⊓ ((L.pull c).pull V.j).U j ≤
        V.π ⁻¹ᵁ ((L.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (L.pull M.j).U (fun _ => j PUnit.unit PUnit.unit)) :=
      fun x hx => ⟨hch i x hx.1, hch j x hx.2⟩
    rw [hr', hr', hr.isRatSec _ _ h0, map_mul, ← ProjSpace.fnOf_appLE V.π hη le h0 hij]
    congr 2
    have k1 := InducedPull.val_pull_g L M.j (fun _ => i PUnit.unit PUnit.unit) (fun _ => j PUnit.unit PUnit.unit)
      (InducedPull.inf_le _ _ _ _)
    have k2 := InducedPull.val_pull_g (L.pull c) V.j i j (InducedPull.inf_le _ _ _ _)
    have k3 := InducedPull.val_pull_g L c (i PUnit.unit) (j PUnit.unit) (InducedPull.inf_le _ _ _ _)
    refine (congrArg _ k1).trans (k2.trans ?_).symm
    refine (congrArg _ k3).trans ?_
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_apply_congr hc _ _ _ _ _
  · intro i x hx
    have hU := (hr.isEqn _ _ (hch i x hx)).generatesAt_iff.1 (hg (V.π x))
    rw [hr', hφV, ← map_mul]
    exact unitAt_fnMap_of V.π hη hU
  · intro v _ e y _ z yt i e₁ e₂ hi
    have e₂' : spMap e.O.subtype ≫ (yt ≫ c) = y.1 ≫ M.j := by
      rw [← Category.assoc, e₂, Category.assoc, hc, ← Category.assoc, e₁]
    have hi' : ⊤ ≤ (yt ≫ c) ⁻¹ᵁ L.U (i PUnit.unit PUnit.unit) :=
      fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
    have H := hφ v e y (yt ≫ c) (fun _ => i PUnit.unit PUnit.unit) e₂' hi'
    have hmem : below y.1 ∈ (L.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) := by
      have h1 : (y.1 ≫ M.j) (IsLocalRing.closedPoint _) ∈ L.U (i PUnit.unit PUnit.unit) := by
        rw [← e₂']
        exact hi' (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hU := (hr.isEqn _ _ hmem).generatesAt_iff.1 (hg (below y.1))
    have hπ₀ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have hU' : RegAt (V.π (below z)) (genAt Δ (below y.1) ^ (m : ℕ) * (r fun _ => i PUnit.unit PUnit.unit : Y.Fn)) := by
      rw [hπ₀]; exact hU.regAt
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at H
    rw [hr', hφV, ← map_mul, SmallSec.valAt_fnMap V.π hη z hU', e₁]
    exact H

theorem bundleSt : BundleSt := by
  intro F _ _ Y n Δ φ ⟨M₀, h₀⟩ hφ
  unfold FromModel at hφ
  choose M L m r hL hr hv using hφ
  obtain ⟨V₀, hV₀⟩ := exists_cover_over_models Y M₀ h₀ n M
  choose b hb using hV₀
  have hd : ∀ i, (m i : ℕ) * ((∏ j, (m j : ℕ)) / m i) = ∏ j, (m j : ℕ) := fun i =>
    Nat.mul_div_cancel' (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  refine ⟨V₀, ∏ i, (m i : ℕ), Finset.prod_pos fun i _ => (m i).pos, fun V a g _ hj hπ _ => ?_⟩
  refine ⟨fun i => lbPow ((L i).pull (a ≫ b i)) ((∏ j, (m j : ℕ)) / m i), fun i =>
    ⟨isLB_lbPow (LB.isLB_pull (hL i) _) _, fun p => ?_⟩⟩
  have hc : V.j ≫ a ≫ b i = V.π ≫ (M i).j := by
    rw [← Category.assoc, hj, Category.assoc, hb i, ← Category.assoc, hπ]
  refine GlobalTheory.TrivFlag.NormsAt.congr
    (normsAt_pow (normsAt_pull (M i) (L i) (m i) (r i) (hr i) (hv i) V (a ≫ b i) hc p) _) (fun y => ?_)
    (fun v _ e y => ?_)
  · rw [← pow_mul, hd i]
  · rw [← _root_.mul_assoc, ← Nat.cast_mul, mul_comm ((∏ j, (m j : ℕ)) / m i), hd i]

end GlobalTheory.HalfGeo
