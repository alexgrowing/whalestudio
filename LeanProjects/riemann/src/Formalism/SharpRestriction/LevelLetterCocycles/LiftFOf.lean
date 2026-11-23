import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T₁ T₂ : LocLat G Qp LL O}

theorem lc_pow (I : BaseId W) (e : ℕ) :
    I.Bs.lc ^ e = PowerSeries.C (((PD.p : ℕ) : O) ^ e) := by
  unfold Formalism.ExponentWindows.E.Base.lc
  rw [I.ℓ_eq, map_pow]

theorem map_mem_Z1DΔ (F : LatHom T₁.L T₂.L) (w : ↥(W.wachCocyclesDelta T₁)) :
    (W.map F (w : W.DD T₁ × W.DD T₁).1, W.map F (w : W.DD T₁ × W.DD T₁).2) ∈ W.wachCocyclesDelta T₂ := by
  obtain ⟨⟨x, y⟩, hw⟩ := w
  show (W.map F x, W.map F y) ∈ W.wachCocyclesDelta T₂
  simp only [Formalism.BasicNotions.LocWach.wachCocyclesDelta, Formalism.BasicNotions.herrZ1Δ, Formalism.BasicNotions.herrCocycles, Submodule.mem_inf,
    LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.coprod_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.id_apply, LinearMap.prodMap_apply] at hw ⊢
  obtain ⟨h1, h2⟩ := hw
  refine ⟨?_, fun d hd => ?_⟩
  · rw [← W.map_γ, ← W.map_φ, ← map_sub, ← map_sub, ← map_neg, ← map_add, h1, map_zero]
  · have h3 := h2 d hd
    rw [← W.map_γ, ← W.map_γ]
    simp only [Prod.mk_sub_mk, Prod.mk_eq_zero, sub_eq_zero] at h3 ⊢
    exact ⟨by rw [h3.1], by rw [h3.2]⟩

private theorem inv_lemma' {T : LocLat G Qp LL O} (w : ↥(W.wachCocyclesDelta T)) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γD T δ (w : W.DD T × W.DD T).1 = (w : W.DD T × W.DD T).1 ∧
      W.γD T δ (w : W.DD T × W.DD T).2 = (w : W.DD T × W.DD T).2 := by
  obtain ⟨⟨x, y⟩, hw⟩ := w
  simp only [Formalism.BasicNotions.LocWach.wachCocyclesDelta, Formalism.BasicNotions.herrZ1Δ, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.prodMap_apply,
    Prod.mk_sub_mk, Prod.mk_eq_zero, sub_eq_zero] at hw
  exact hw.2 δ hδ

theorem liftF_of {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂}
    (h : CoordHom C₁ C₂ F) (hs : W.s = 1) (hp : PD.p ≠ 2) (herr : Formalism.MainNotions.DeltaInvariantLattices.p2aK W T₂)
    (nat : W.ClKNat) (e : ℕ)
    (key : ∀ κ ∈ Zf C₂, ∃ κ₁ ∈ Zf C₁,
      (latOf C₂).IsCobound (I.Bs.lc ^ e • κ.1 - fun i => (latHomOf h).f (κ₁.1 i))
        (I.Bs.lc ^ e • κ.2 - fun i => (latHomOf h).f (κ₁.2 i))) :
    F.LiftF PD e := by
  intro c hc
  have hcZ : c ∈ latticeCocycles T₂.L := (Submodule.mem_inf.1 hc).1
  have hsurj : Function.Surjective (W.clK T₂) := (herr hs hp).1
  have hker : ∀ w : ↥(W.wachCocyclesDelta T₂), W.clK T₂ w = 0 ↔ ∃ m : W.DD T₂, Formalism.MainNotions.DeltaInvariantLattices.DInv W T₂ m ∧
      (w : W.DD T₂ × W.DD T₂) = (W.φD T₂ m - m, W.γD T₂ W.gamK m - m) := (herr hs hp).2
  obtain ⟨w, hw⟩ : ∃ w : ↥(W.wachCocyclesDelta T₂),
      W.clK T₂ w = Submodule.mkQ ((latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype) ⟨c, hcZ⟩ :=
    hsurj (Submodule.mkQ ((latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype) ⟨c, hcZ⟩)
  obtain ⟨y1, hy1⟩ := tot_surj C₂ (w : W.DD T₂ × W.DD T₂).1 (fun δ hδ => (inv_lemma' w δ hδ).1)
  obtain ⟨y2, hy2⟩ := tot_surj C₂ (w : W.DD T₂ × W.DD T₂).2 (fun δ hδ => (inv_lemma' w δ hδ).2)
  have hκ : ((y1, y2) : (ZMod n → C₂.V) × (ZMod n → C₂.V)) ∈ Zf C₂ := by
    show totP C₂ (y1, y2) ∈ ZfD W T₂
    have ht : totP C₂ (y1, y2) = (w : W.DD T₂ × W.DD T₂) := Prod.ext hy1 hy2
    rw [ht]
    refine ⟨w, ?_, rfl⟩
    show W.clK T₂ w ∈ latticeFiniteCohomology PD T₂.L
    rw [hw]
    exact ⟨⟨c, hcZ⟩, hc, rfl⟩
  obtain ⟨κ₁, hκ₁, hcob⟩ := key (y1, y2) hκ
  obtain ⟨m, hm1, hm2⟩ := hcob
  obtain ⟨w₁, hw₁, hw₁e⟩ : ∃ w₁, w₁ ∈ (latticeFiniteCohomology PD T₁.L).comap (W.clK T₁) ∧
      (W.wachCocyclesDelta T₁).subtype w₁ = totP C₁ κ₁ := hκ₁
  obtain ⟨z₁, hz₁, hz₁e⟩ : ∃ z₁, z₁ ∈ (latticeFiniteCocycles PD T₁.L).comap (latticeCocycles T₁.L).subtype ∧
      Submodule.mkQ ((latticeCoboundaries T₁.L).comap (latticeCocycles T₁.L).subtype) z₁ = W.clK T₁ w₁ := hw₁
  have hw1e1 : tot C₁ κ₁.1 = (w₁ : W.DD T₁ × W.DD T₁).1 := (congrArg Prod.fst hw₁e).symm
  have hw1e2 : tot C₁ κ₁.2 = (w₁ : W.DD T₁ × W.DD T₁).2 := (congrArg Prod.snd hw₁e).symm
  have e1 : (((PD.p : ℕ) : O) ^ e) • (w : W.DD T₂ × W.DD T₂).1 - W.map F (w₁ : W.DD T₁ × W.DD T₁).1
      = W.φD T₂ (tot C₂ m) - tot C₂ m := by
    have h1 : I.Bs.lc ^ e • y1 - (fun i => (latHomOf h).f (κ₁.1 i)) = (latOf C₂).dφ m := hm1
    have h1' := congrArg (tot C₂) h1
    rw [tot_sub, tot_smul, tot_map h κ₁.1, tot_dφ, lc_pow I e, BaseId.d_C, algebraMap_smul, hy1,
      hw1e1] at h1'
    exact h1'
  have e2 : (((PD.p : ℕ) : O) ^ e) • (w : W.DD T₂ × W.DD T₂).2 - W.map F (w₁ : W.DD T₁ × W.DD T₁).2
      = W.γD T₂ W.gamK (tot C₂ m) - tot C₂ m := by
    have h2 : I.Bs.lc ^ e • y2 - (fun i => (latHomOf h).f (κ₁.2 i)) = (latOf C₂).dγ m := hm2
    have h2' := congrArg (tot C₂) h2
    rw [tot_sub, tot_smul, tot_map h κ₁.2, tot_dγ, lc_pow I e, BaseId.d_C, algebraMap_smul, hy2,
      hw1e2] at h2'
    exact h2'
  obtain ⟨w₁', hw₁'⟩ : ∃ w' : ↥(W.wachCocyclesDelta T₂), (w' : W.DD T₂ × W.DD T₂) =
      (W.map F (w₁ : W.DD T₁ × W.DD T₁).1, W.map F (w₁ : W.DD T₁ × W.DD T₁).2) :=
    ⟨⟨_, map_mem_Z1DΔ F w₁⟩, rfl⟩
  have hnat := nat F w₁ w₁' hw₁'
  have hD : W.clK T₂ ((((PD.p : ℕ) : O) ^ e) • w - w₁') = 0 := by
    rw [hker]
    refine ⟨tot C₂ m, fun δ hδ => tot_Δ C₂ m δ hδ, Prod.ext ?_ ?_⟩
    · show (((PD.p : ℕ) : O) ^ e) • (w : W.DD T₂ × W.DD T₂).1 - (w₁' : W.DD T₂ × W.DD T₂).1 = _
      rw [hw₁']
      exact e1
    · show (((PD.p : ℕ) : O) ^ e) • (w : W.DD T₂ × W.DD T₂).2 - (w₁' : W.DD T₂ × W.DD T₂).2 = _
      rw [hw₁']
      exact e2
  have hD' : (((PD.p : ℕ) : O) ^ e) • W.clK T₂ w = W.clK T₂ w₁' := by
    have h0 : W.clK T₂ ((((PD.p : ℕ) : O) ^ e) • w) - W.clK T₂ w₁' = 0 :=
      (map_sub (W.clK T₂) _ _).symm.trans hD
    have hs : W.clK T₂ ((((PD.p : ℕ) : O) ^ e) • w) = (((PD.p : ℕ) : O) ^ e) • W.clK T₂ w :=
      map_smul (W.clK T₂) _ _
    rw [← hs]
    exact sub_eq_zero.1 h0
  rw [hw, ← hnat, ← hz₁e, ← map_smul] at hD'
  simp only [Formalism.WeaklyAdmissibleFiltrations.LatHom.H1map, Submodule.mkQ_apply, Submodule.mapQ_apply,
    Submodule.Quotient.eq] at hD'
  erw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hD'
  have hB : (((PD.p : ℕ) : O) ^ e) • c - F.post (z₁ : G → _) ∈ latticeCoboundaries T₂.L := hD'
  refine Submodule.mem_sup.2 ⟨F.post (z₁ : G → _), ⟨(z₁ : G → _), hz₁, rfl⟩, _, hB, ?_⟩
  abel

end Formalism.MainNotions.WachCoordinates.Br
