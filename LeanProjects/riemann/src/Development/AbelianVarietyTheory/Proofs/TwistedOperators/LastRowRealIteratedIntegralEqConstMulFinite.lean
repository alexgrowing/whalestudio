import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemValuationEq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowRealInt

theorem exists_mul_of_rel {I : Type*} (L r : I → ℂ)
    (h : ∀ x x' (α α' : ℂ), α * r x + α' * r x' = 0 → α * L x + α' * L x' = 0) : ∃ c : ℂ, ∀ x, L x = c * r x := by
  by_cases h0 : ∀ x, r x = 0
  · refine ⟨0, fun x => ?_⟩
    have hx := h x x 1 0 (by simp [h0 x])
    simpa using hx
  · push_neg at h0
    obtain ⟨x₀, hx₀⟩ := h0
    refine ⟨L x₀ / r x₀, fun x => ?_⟩
    have hx := h x x₀ (r x₀) (-r x) (by ring)
    rw [div_mul_eq_mul_div, eq_div_iff hx₀]
    linear_combination hx

theorem exists_mul_of_cellVan (hV : CellVan) {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)]
    [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
    [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)]
    [∀ i, BorelSpace (H i)] (A B R K : ∀ i, Subgroup (H i)) (l : List ι) (hl : l.Nodup)
    (hS : ∀ i ∈ l, Split (A i) (B i) (R i) (K i))
    (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (ρ' : ∀ i, Measure ((R i).subgroupOf (B i))) (μ' : ∀ i, Measure (B i))
    (hH : ∀ i ∈ l, (ρ i).IsHaarMeasure ∧ (μ i).IsHaarMeasure ∧ (ρ' i).IsHaarMeasure ∧ (μ' i).IsHaarMeasure)
    {I : Type*} (X : I → Type) (S : ∀ n, Finset (X n)) (b : ∀ n, X n → ∀ i, H i) (w : ∀ n, X n → ℂ) (q : I → (∀ i, H i) → ℂ)
    (L r : I → ℂ)
    (h1 : ∀ n, ∀ β ∈ S n, (∀ i, i ∉ l → b n β i = 1) ∧ ∃ hb : ∀ i, b n β i ∈ B i,
        w n β = (l.map fun i => cellWt (ρ' i) (μ' i) ((K i).subgroupOf (B i)) ⟨b n β i, hb i⟩).prod)
    (h2 : ∀ n, ∀ β ∈ S n, ∀ β' ∈ S n, InCells A R K l (b n β) (b n β') → β = β')
    (h3 : ∀ n, BiInv R K l (q n))
    (h4 : ∀ n h, (∀ i, i ∉ l → h i = 1) → q n h ≠ 0 → ∃ β ∈ S n, InCells A R K l (b n β) h)
    (h5 : ∀ n, NIter ρ μ (q n) l 1 (L n))
    (h6 : ∀ a : ∀ i, H i, (∀ i, a i ∈ A i) → (∀ i, i ∉ l → a i = 1) →
      ∃ e : ℂ, ∀ n, ∑ β ∈ S n, w n β * q n (a * b n β) = e * r n) :
    ∃ c : ℂ, ∀ n, L n = c * r n := by
  apply exists_mul_of_rel
  intro x x' α α' hrel
  have key := hV ι H A B R K l hl hS ρ μ ρ' μ' hH (fun k => X (![x, x'] k)) (fun k => S (![x, x'] k))
    (fun k => b (![x, x'] k)) (fun k => w (![x, x'] k)) (fun k => q (![x, x'] k)) (fun k => L (![x, x'] k)) ![α, α']
    (fun k => h1 _) (fun k => h2 _) (fun k => h3 _) (fun k => h4 _) (fun k => h5 _) (by
      intro a ha ha1
      obtain ⟨e, he⟩ := h6 a ha ha1
      simp only [Fin.sum_univ_two, he]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      linear_combination e * hrel)
  simpa [Fin.sum_univ_two] using key

theorem exists_haar_family {ι : Type} {H : ι → Type} [∀ i, Group (H i)]
    [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, MeasurableSpace (H i)]
    [∀ i, BorelSpace (H i)] (B R : ∀ i, Subgroup (H i)) (l : List ι)
    (hS : ∀ i ∈ l, IsClosed (B i : Set (H i)) ∧ IsClosed (R i : Set (H i))) :
    ∃ (ρ' : ∀ i, Measure ((R i).subgroupOf (B i))) (μ' : ∀ i, Measure (B i)),
      ∀ i ∈ l, (ρ' i).IsHaarMeasure ∧ (μ' i).IsHaarMeasure := by
  classical
  have e1 : ∀ i, ∃ m : Measure ((R i).subgroupOf (B i)), i ∈ l → m.IsHaarMeasure := by
    intro i
    by_cases hi : i ∈ l
    · haveI : LocallyCompactSpace (B i) := (hS i hi).1.locallyCompactSpace
      have hc : IsClosed (((R i).subgroupOf (B i) : Subgroup (B i)) : Set (B i)) := by
        rw [Subgroup.coe_subgroupOf]
        exact (hS i hi).2.preimage continuous_subtype_val
      haveI : LocallyCompactSpace ((R i).subgroupOf (B i)) := hc.locallyCompactSpace
      exact ⟨Measure.haar, fun _ => inferInstance⟩
    · exact ⟨0, fun h => absurd h hi⟩
  have e2 : ∀ i, ∃ m : Measure (B i), i ∈ l → m.IsHaarMeasure := by
    intro i
    by_cases hi : i ∈ l
    · haveI : LocallyCompactSpace (B i) := (hS i hi).1.locallyCompactSpace
      exact ⟨Measure.haar, fun _ => inferInstance⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose ρ' hρ' using e1
  choose μ' hμ' using e2
  exact ⟨ρ', μ', fun i hi => ⟨hρ' i hi, hμ' i hi⟩⟩

theorem sum_eq_mul_mul {X : Type} {s : Set X} (hs : s.Finite) (f g : X → ℂ) (e u : ℂ) (h : ∀ β ∈ s, f β = e * (u * g β)) :
    ∑ β ∈ hs.toFinset, f β = e * (u * ∑ β ∈ hs.toFinset, g β) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun β hβ => h β (hs.mem_toFinset.mp hβ)

theorem exists_mul_of_cellVan' (hV : CellVan) {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)]
    [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
    [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)]
    [∀ i, BorelSpace (H i)] (A B R K : ∀ i, Subgroup (H i)) (l : List ι) (hl : l.Nodup)
    (hS : ∀ i ∈ l, Split (A i) (B i) (R i) (K i))
    (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (ρ' : ∀ i, Measure ((R i).subgroupOf (B i))) (μ' : ∀ i, Measure (B i))
    (hH : ∀ i ∈ l, (ρ i).IsHaarMeasure ∧ (μ i).IsHaarMeasure ∧ (ρ' i).IsHaarMeasure ∧ (μ' i).IsHaarMeasure)
    {T N V : Type*} {X : T → Type} {Ta Pd Y : T → Type*} (F : ∀ t, N → Ta t → Prop) (Is : T → V → Prop)
    (Ok : ∀ t, N → X t → V → Prop) (Ok' : ∀ t, N → X t → Pd t → Prop) (S : ∀ t, N → Set (X t)) (fin : ∀ t a, (S t a).Finite)
    (b : ∀ t, X t → ∀ i, H i) (w : ∀ t, X t → ℂ) (q : ∀ t, N → Ta t → ∀ M, Is t M → Y t → (∀ i, H i) → ℂ)
    (L : ∀ t, N → Ta t → V → Y t → ℂ) (g : ∀ t, N → X t → V → Pd t → Y t → ℂ) (u : T → ℂ)
    (h1 : ∀ t β, (∀ i, i ∉ l → b t β i = 1) ∧ ∃ hb : ∀ i, b t β i ∈ B i,
        w t β = (l.map fun i => cellWt (ρ' i) (μ' i) ((K i).subgroupOf (B i)) ⟨b t β i, hb i⟩).prod)
    (h2 : ∀ t β β', InCells A R K l (b t β) (b t β') → β = β')
    (h3 : ∀ t a τ, F t a τ → ∀ M hM y, BiInv R K l (q t a τ M hM y))
    (h4 : ∀ t a τ, F t a τ → ∀ M hM y h, (∀ i, i ∉ l → h i = 1) → q t a τ M hM y h ≠ 0 →
      ∃ β ∈ S t a, InCells A R K l (b t β) h)
    (h5 : ∀ t a τ, F t a τ → ∀ M hM y, NIter ρ μ (q t a τ M hM y) l 1 (L t a τ M y))
    (h6 : ∀ p : ∀ i, H i, (∀ i, p i ∈ A i) → (∀ i, i ∉ l → p i = 1) →
      ∃ e : ℂ, ∀ t a τ, F t a τ → ∀ M hM, ∀ β ∈ S t a, ∀ M' τ', Ok t a β M' → Ok' t a β τ' → ∀ y,
        w t β * q t a τ M hM y (p * b t β) = e * (u t * g t a β M' τ' y)) :
    ∃ c : ℂ, ∀ t a τ, F t a τ → ∀ M, Is t M → ∀ (Mβ : X t → V) (τβ : X t → Pd t),
      (∀ β ∈ S t a, Ok t a β (Mβ β) ∧ Ok' t a β (τβ β)) → ∀ y,
        L t a τ M y = c * (u t * ∑ β ∈ (fin t a).toFinset, g t a β (Mβ β) (τβ β) y) := by
  obtain ⟨c, hc⟩ := exists_mul_of_cellVan hV A B R K l hl hS ρ μ ρ' μ' hH
    (I := {x : (t : T) × (a : N) × (τ : Ta t) × (M : V) × (Mβ : X t → V) × (τβ : X t → Pd t) × Y t //
        F x.1 x.2.1 x.2.2.1 ∧ Is x.1 x.2.2.2.1 ∧
          ∀ β ∈ S x.1 x.2.1, Ok x.1 x.2.1 β (x.2.2.2.2.1 β) ∧ Ok' x.1 x.2.1 β (x.2.2.2.2.2.1 β)})
    (fun n => X n.1.1) (fun n => (fin n.1.1 n.1.2.1).toFinset) (fun n => b n.1.1) (fun n => w n.1.1)
    (fun n => q n.1.1 n.1.2.1 n.1.2.2.1 n.1.2.2.2.1 n.2.2.1 n.1.2.2.2.2.2.2)
    (fun n => L n.1.1 n.1.2.1 n.1.2.2.1 n.1.2.2.2.1 n.1.2.2.2.2.2.2)
    (fun n => u n.1.1 * ∑ β ∈ (fin n.1.1 n.1.2.1).toFinset,
      g n.1.1 n.1.2.1 β (n.1.2.2.2.2.1 β) (n.1.2.2.2.2.2.1 β) n.1.2.2.2.2.2.2)
    (fun n β _ => h1 _ β) (fun n β _ β' _ => h2 _ β β') (fun n => h3 _ _ _ n.2.1 _ _ _)
    (fun n h hh hq => by
      obtain ⟨β, hβ, hin⟩ := h4 _ _ _ n.2.1 _ n.2.2.1 _ h hh hq
      exact ⟨β, (fin _ _).mem_toFinset.mpr hβ, hin⟩)
    (fun n => h5 _ _ _ n.2.1 _ _ _)
    (fun p hp hp1 => by
      obtain ⟨e, he⟩ := h6 p hp hp1
      refine ⟨e, fun n => ?_⟩
      exact sum_eq_mul_mul (fin _ _) (fun β => w n.1.1 β * q n.1.1 n.1.2.1 n.1.2.2.1 n.1.2.2.2.1 n.2.2.1
          n.1.2.2.2.2.2.2 (p * b n.1.1 β))
        (fun β => g n.1.1 n.1.2.1 β (n.1.2.2.2.2.1 β) (n.1.2.2.2.2.2.1 β) n.1.2.2.2.2.2.2) e (u n.1.1)
        fun β hβ => he _ _ _ n.2.1 _ n.2.2.1 β hβ _ _ (n.2.2.2 β hβ).1 (n.2.2.2 β hβ).2 _)
  exact ⟨c, fun t a τ hF M hM Mβ τβ hok y => hc ⟨⟨t, a, τ, M, Mβ, τβ, y⟩, hF, hM, hok⟩⟩

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem mem_of_isRep {ch : Choice R} {t : T} {s : ℤˣ} {β : CosFam ch.G t} {b : Pts ch.G} (h : IsRep t ch.S.B s β b) (j : ℕ) :
    b j ∈ GfC _ := by
  obtain ⟨h1, h2⟩ := h
  by_cases hj : j ∈ idx D
  · have hle : j ≤ D.R.m := by
      have := List.mem_range'_1.mp (show j ∈ List.range' 1 (D.R.m - 2) from hj)
      omega
    obtain ⟨δ, r, -, -, hfin⟩ := h2 j hj hle
    exact hfin.1
  · rw [h1 j hj]
    exact one_mem _

theorem wt_eq {ch : Choice R} (ρ : ∀ j, Measure ((rowGrp ch.G j).subgroupOf (GfC _)))
    (μ : ∀ j, Measure (GfC (ch.G.V (.grid D.R.m j)))) (b : Pts ch.G) (hb : ∀ j, b j ∈ GfC _) :
    wt ρ μ b = ((idx D).map fun j => cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, hb j⟩).prod := by
  unfold GlobalTheory.RowVal.wt
  congr 1
  exact List.map_congr_left fun j _ => dif_pos (hb j)

theorem exists_lhs_eq (hV : CellVan) (ch : Choice R) (hG : GrpAt ch) (hI : IterAt ch) (hInv : InvAt ch) (s : ℤˣ)
    (hSu : SuppOn ch s) (hRep : RepAt ch s) (hOK : ∀ t a, ch.S.SumOK t (ch.Phi a)) (z : T → ℂˣ)
    (P : PolRow ch.G × PolDown ch.G)
    (g : ∀ t : T, Fin ch.n → CosFam ch.G t → Vol ch.G → (PureDat ch.G t →₀ ℂ) → (R.HX t).H → ℂ)
    (hval : ∀ (ρ : ∀ j, Measure ((rowGrp ch.G j).subgroupOf (GfC _))) (μ : ∀ j, Measure (GfC (ch.G.V (.grid D.R.m j)))),
      (∀ j ∈ idx D, (ρ j).IsHaarMeasure ∧ (μ j).IsHaarMeasure) → ∀ (p : Pts ch.G), IsRealPt p →
      ∃ e : ℂ, ∀ t a τ, IsFlipFin t ch.S.B ch.rm (ch.Phi a) τ → ∀ (M : Vol ch.G) (hM : M.Is t),
        ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ b, IsRep t ch.S.B s β b → ∀ M' τ', IsTermVol t ch.S.toGridChoice (ch.Phi a) β M' →
          ch.S.IsExpansion t (ch.Phi a) β τ' → ∀ y,
          wt ρ μ b * tot ch.W hM P τ (colFn ch a) (formTop ch t y) (p * b) =
            e * ((z t : ℂ)⁻¹ * g t a β M' τ' y)) :
    ∃ c : ℂ, ∀ t a τ, IsFlipFin t ch.S.B ch.rm (ch.Phi a) τ → ∀ M : Vol ch.G, M.Is t →
      ∀ (Mβ : CosFam ch.G t → Vol ch.G) (τβ : CosFam ch.G t → PureDat ch.G t →₀ ℂ),
        (∀ β ∈ ch.S.supp t (ch.Phi a), IsTermVol t ch.S.toGridChoice (ch.Phi a) β (Mβ β) ∧ ch.S.IsExpansion t (ch.Phi a) β (τβ β)) →
        ∀ y, lhs ch t M (Finsupp.single P 1) τ a y =
          c * ((z t : ℂ)⁻¹ * ∑ β ∈ (hOK t a).fin.toFinset, g t a β (Mβ β) (τβ β) y) := by
  classical
  obtain ⟨ρ, μ, hH0, hIt⟩ := hI
  obtain ⟨ρ', μ', hH'⟩ := exists_haar_family (H := fun j => GA D (ch.G.V (.grid D.R.m j)))
    (fun j => GfC (ch.G.V (.grid D.R.m j))) (rowGrp ch.G) (idx D) fun j hj => ⟨(hG j hj).clB, (hG j hj).clR⟩
  have hRep' := hRep
  unfold RepAt at hRep'
  choose b hb using fun t => (hRep' t).1
  have hl : (idx D).Nodup := by
    unfold idx
    apply List.nodup_range'
    all_goals simp
  obtain ⟨c, hc⟩ := exists_mul_of_cellVan' hV (fun j => GinfC (ch.G.V (.grid D.R.m j)))
    (fun j => GfC (ch.G.V (.grid D.R.m j))) (rowGrp ch.G) (latGrp ch.G) (idx D) hl hG ρ μ ρ' μ'
    (fun j hj => ⟨(hH0 j hj).1, (hH0 j hj).2, (hH' j hj).1, (hH' j hj).2⟩)
    (X := CosFam ch.G) (F := fun t a τ => IsFlipFin t ch.S.B ch.rm (ch.Phi a) τ) (Is := fun t M => M.Is t)
    (Ok := fun t a β M' => IsTermVol t ch.S.toGridChoice (ch.Phi a) β M')
    (Ok' := fun t a β τ' => ch.S.IsExpansion t (ch.Phi a) β τ') (S := fun t a => ch.S.supp t (ch.Phi a))
    (fin := fun t a => (hOK t a).fin) (b := b) (w := fun t β => wt ρ' μ' (b t β))
    (q := fun t a τ M hM y => tot ch.W hM P τ (colFn ch a) (formTop ch t y))
    (L := fun t a τ M y => lhs ch t M (Finsupp.single P 1) τ a y) (g := g) (u := fun t => ((z t : ℂ))⁻¹)
    (h1 := fun t β => by
      obtain ⟨hb1, -⟩ := hb t β
      exact ⟨hb1, mem_of_isRep (hb t β), wt_eq ρ' μ' (b t β) (mem_of_isRep (hb t β))⟩)
    (h2 := fun t β β' h => (hRep' t).2 β β' _ _ (hb t β) (hb t β') h)
    (h3 := fun t a τ hF M hM y => hInv t a τ hF M hM P y)
    (h4 := fun t a τ hF M hM y h hh hq => hSu t a τ hF M hM P y (b t) (hb t) h hh hq)
    (h5 := fun t a τ hF M hM y => hIt t a τ hF M hM P y)
    (h6 := fun p hp hp1 => by
      have hp' : IsRealPt p := by
        unfold IsRealPt
        exact ⟨hp, hp1⟩
      obtain ⟨e, he⟩ := hval ρ' μ' hH' p hp'
      exact ⟨e, fun t a τ hF M hM β hβ M' τ' hM' hτ' y =>
        he t a τ hF M hM β hβ (b t β) (hb t β) M' τ' hM' hτ' y⟩)
  exact ⟨c, hc⟩

theorem unfoldAt_of (hV : CellVan) (ch : Choice R) (hG : GrpAt ch) (hI : IterAt ch) (hL : LinAt ch) (hInv : InvAt ch)
    (hs : ∃ s, SuppOn ch s ∧ RepAt ch s ∧ ValAt ch s) (hR : RealLine ch) (hOK : ∀ t a, ch.S.SumOK t (ch.Phi a)) :
    UnfoldAt ch := by
  classical
  obtain ⟨s, hSu, hRep, hVal⟩ := hs
  have hR' := hR
  unfold RealLine at hR'
  obtain ⟨ell, -, hK, hsurj⟩ := hR'
  have hVal' := hVal
  unfold ValAt at hVal'
  obtain ⟨z, hz, hv⟩ := hVal'
  obtain ⟨σ₀, -, hσ₀⟩ := hsurj 1
  have hsA : ch.S.sAA ≠ 0 := (sAA_facts ch.W ch.S.toGridChoice fun w _ => hasConductor_psiAt_AA ch.W w).1
  have hdef : ∀ t a β, β ∈ ch.S.supp t (ch.Phi a) → ∀ M', IsTermVol t ch.S.toGridChoice (ch.Phi a) β M' →
      ∀ τ', ch.S.IsExpansion t (ch.Phi a) β τ' → ∀ y σ,
      defTot t ch.S.toGridChoice M' σ τ' (colFn ch a) (formTop ch t y) =
        (σ.sum fun P c => c * ell P) * defTot t ch.S.toGridChoice M' σ₀ τ' (colFn ch a) (formTop ch t y) := by
    intro t a β hβ M' hM' τ' hτ' y σ
    obtain ⟨K, hK'⟩ := hK t a (hOK t a) β hβ M' hM' τ' hτ' y
    rw [hK' σ, hK' σ₀, hσ₀, one_mul]
  have hc : ∀ P : PolRow ch.G × PolDown ch.G, ∃ c : ℂ, ∀ t a τ, IsFlipFin t ch.S.B ch.rm (ch.Phi a) τ →
      ∀ M : Vol ch.G, M.Is t → ∀ (Mβ : CosFam ch.G t → Vol ch.G) (τβ : CosFam ch.G t → PureDat ch.G t →₀ ℂ),
        (∀ β ∈ ch.S.supp t (ch.Phi a), IsTermVol t ch.S.toGridChoice (ch.Phi a) β (Mβ β) ∧
          ch.S.IsExpansion t (ch.Phi a) β (τβ β)) →
        ∀ y, lhs ch t M (Finsupp.single P 1) τ a y =
          c * ((z t : ℂ)⁻¹ * ∑ β ∈ (hOK t a).fin.toFinset, (∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) *
            defTot t ch.S.toGridChoice (Mβ β) σ₀ (τβ β) (colFn ch a) (formTop ch t y)) := by
    intro P
    refine exists_lhs_eq hV ch hG hI hInv s hSu hRep hOK z P
      (fun t a β M' τ' y => (∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) *
        defTot t ch.S.toGridChoice M' σ₀ τ' (colFn ch a) (formTop ch t y)) ?_
    intro ρ μ hH p hp
    obtain ⟨σ, hσ⟩ := hv ρ μ hH P p hp
    refine ⟨σ.sum fun P c => c * ell P, ?_⟩
    intro t a τ hF M hM β hβ b hb M' τ' hM' hτ' y
    rw [hσ t a τ hF M hM β hβ b hb M' τ' hM' hτ' y, hdef t a β hβ M' hM' τ' hτ' y σ]
    ring
  choose cP hcP using hc
  intro τi
  obtain ⟨σ, -, hσ⟩ := hsurj ((τi.sum fun P c => c * cP P) / ch.S.sAA)
  refine ⟨σ, z, fun t => ⟨hz t, ?_⟩⟩
  intro a τ hF M hM Mβ τβ hMτ y
  change lhs ch t M τi τ a y = _
  have hcP' := fun P => hcP P t a τ hF M hM Mβ τβ hMτ y
  have hrhs : (∑ᶠ β ∈ ch.S.supp t (ch.Phi a), (∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) *
        defTot t ch.S.toGridChoice (Mβ β) σ (τβ β) (colFn ch a) (formTop ch t y)) =
      (σ.sum fun P c => c * ell P) * ∑ β ∈ (hOK t a).fin.toFinset, (∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) *
        defTot t ch.S.toGridChoice (Mβ β) σ₀ (τβ β) (colFn ch a) (formTop ch t y) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ (hOK t a).fin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hβ' := (hOK t a).fin.mem_toFinset.mp hβ
    rw [hdef t a β hβ' _ (hMτ β hβ').1 _ (hMτ β hβ').2 y σ]
    ring
  have e : ∀ C x S0 : ℂ, x * ch.S.sAA * (C / ch.S.sAA * S0) = C * (x * S0) := by
    intro C x S0
    linear_combination (x * S0) * div_mul_cancel₀ C hsA
  rw [hL t a τ hF M hM τi y, hrhs, hσ, e, Finsupp.sum_mul]
  simp only [hcP']
  exact Finsupp.sum_congr fun P _ => by ring

theorem unfold_of_steps : CellVan → Big fun ch => GrpAt ch → IterAt ch → LinAt ch → InvAt ch →
    (∃ s, SuppOn ch s ∧ RepAt ch s ∧ ValAt ch s) → RealLine ch → (∀ t a, ch.S.SumOK t (ch.Phi a)) → UnfoldAt ch := by
  intro hV
  unfold Big
  exact ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ => unfoldAt_of hV ch⟩⟩

end GlobalTheory.RowRealInt

end
