import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepFinitelyManyCellsUniformProoStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExistsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySupportedSplitPlacesEqProdLocalParts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicTrivialAtPlacesSubgroupAntitone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAway
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QCells

section Groups

theorem prod_mul_inv_mem {G : Type} [Group G] (H : Subgroup G) : ∀ {n : ℕ} (f : Fin n → G) (i : Fin n),
    (∀ j, j ≠ i → f j ∈ H) → (∀ h ∈ H, f i * h = h * f i) → (List.ofFn f).prod * (f i)⁻¹ ∈ H := by
  intro n
  induction n with
  | zero => intro f i; exact i.elim0
  | succ n ih =>
    intro f i hf hc
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      have hR : (List.ofFn fun j : Fin n => f j.succ).prod ∈ H :=
        H.list_prod_mem fun b hb => by
          obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
          exact hf _ (Fin.succ_ne_zero j)
      rw [hc _ hR, mul_inv_cancel_right]
      exact hR
    | succ i =>
      rw [mul_assoc]
      exact H.mul_mem (hf 0 (Fin.succ_ne_zero i).symm)
        (ih (fun j => f j.succ) i (fun j hj => hf _ fun h => hj (Fin.succ_injective _ h)) hc)

theorem prod_ofFn_mul {G : Type} [Monoid G] : ∀ {n : ℕ} (f g : Fin n → G), (∀ i j, i ≠ j → Commute (g i) (f j)) →
    (List.ofFn fun i => f i * g i).prod = (List.ofFn f).prod * (List.ofFn g).prod := by
  intro n
  induction n with
  | zero => intro f g _; simp
  | succ n ih =>
    intro f g h
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih (fun i => f i.succ) (fun i => g i.succ) fun i j hij => h _ _ fun e => hij (Fin.succ_injective _ e)]
    have hc : Commute (g 0) (List.ofFn fun j : Fin n => f j.succ).prod :=
      Commute.list_prod_right _ _ fun b hb => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
        exact h _ _ (Fin.succ_ne_zero j).symm
    simp only [mul_assoc]
    rw [← mul_assoc (g 0), hc.eq, mul_assoc]

theorem cells_prod {G : Type} [Group G] {r : ℕ} (H : Fin (r + 1) → Type) [∀ i, Group (H i)] (φ : ∀ i, H i →* G)
    (O : Fin (r + 1) → Subgroup G) (hO : ∀ i j, j ≠ i → ∀ h, φ j h ∈ O i) (hc : ∀ i h, ∀ y ∈ O i, φ i h * y = y * φ i h)
    (A : Subgroup G) (hA : ∀ (i : Fin r) h, φ i.succ h ∈ A)
    (hA' : ∀ a ∈ A, ∃ x : ∀ i : Fin r, H i.succ, a = (List.ofFn fun i => φ i.succ (x i)).prod)
    (K : Subgroup G) (J : ∀ i, Subgroup (H i)) (R₀ : Subgroup (H 0)) (hR : ∀ h, φ 0 h ∈ K → h ∈ R₀) (N : G → Prop)
    (hN : ∀ i, ∃ T : Finset (H i), ∀ z ∈ O i, ∀ x, N (z * φ i x) → ∃ t ∈ T, ∃ ρ, φ i ρ ∈ K ∧ ∃ j ∈ J i, x = ρ * t * j) :
    ∃ T : Finset (A × H 0), ∀ x : A × H 0, N (x.1.1 * φ 0 x.2) → ∃ t ∈ T, ∃ ρ ∈ (K.subgroupOf A).prod R₀,
      ∃ κ ∈ ((⨆ i : Fin r, (J i.succ).map (φ i.succ)).subgroupOf A).prod (J 0), x = ρ * t * κ := by
  classical
  choose T hT using hN
  have hm : ∀ (B : Subgroup G) (x : ∀ i, H i), (∀ i : Fin r, φ i.succ (x i.succ) ∈ B) →
      (List.ofFn fun i : Fin r => φ i.succ (x i.succ)).prod ∈ B := fun B x hx =>
    B.list_prod_mem fun b hb => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
      exact hx j
  let mk : (∀ i, H i) → A × H 0 := fun x => (⟨_, hm A x fun i => hA i _⟩, x 0)
  have hmk : ∀ x y, mk (x * y) = mk x * mk y := fun x y => by
    refine Prod.ext (Subtype.ext ?_) rfl
    change (List.ofFn fun i : Fin r => φ i.succ (x i.succ * y i.succ)).prod =
      (List.ofFn fun i : Fin r => φ i.succ (x i.succ)).prod * (List.ofFn fun i : Fin r => φ i.succ (y i.succ)).prod
    simp only [map_mul]
    exact prod_ofFn_mul _ _ fun i j hij => hc _ _ _ (hO _ _ (fun e => hij (Fin.succ_injective _ e).symm) _)
  refine ⟨(Fintype.piFinset T).image mk, fun x hx => ?_⟩
  obtain ⟨x', hx'⟩ := hA' x.1.1 x.1.2
  let xs : ∀ i, H i := Fin.cons x.2 x'
  have hxs : x = mk xs := Prod.ext (Subtype.ext hx') rfl
  have hX : x.1.1 * φ 0 x.2 = (List.ofFn fun i => φ i (xs i)).prod := by
    rw [List.ofFn_succ, List.prod_cons]
    change _ = φ 0 x.2 * (List.ofFn fun i => φ i.succ (x' i)).prod
    rw [hx']
    exact (hc 0 _ _ (hm (O 0) xs fun i => hO _ _ (Fin.succ_ne_zero i) _)).symm
  have hloc : ∀ i, ∃ t ∈ T i, ∃ ρ, φ i ρ ∈ K ∧ ∃ j ∈ J i, xs i = ρ * t * j := fun i => by
    refine hT i (x.1.1 * φ 0 x.2 * (φ i (xs i))⁻¹) ?_ (xs i) (by rwa [inv_mul_cancel_right])
    rw [hX]
    exact prod_mul_inv_mem (O i) (fun i => φ i (xs i)) i (fun j hj => hO i j hj _) (hc i _)
  choose t ht ρ hρ j hj he using hloc
  refine ⟨mk t, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 ht), mk ρ, ⟨hm K ρ fun i => hρ _, hR _ (hρ 0)⟩, mk j,
    ⟨hm _ j fun i => Subgroup.mem_iSup_of_mem i (Subgroup.mem_map_of_mem _ (hj _)), hj 0⟩, ?_⟩
  rw [← hmk, ← hmk, hxs]
  exact congrArg mk (funext he)

theorem conv_support {G : Type} [Monoid G] : ∀ {n : ℕ} (H : Fin n → Type) (φ : ∀ i, H i → G) (e : ∀ i, H i →₀ ℂ),
    ∀ a ∈ (conv (List.ofFn fun i => (e i).mapDomain (φ i))).support,
      ∃ b : ∀ i, H i, (∀ i, b i ∈ (e i).support) ∧ a = (List.ofFn fun i => φ i (b i)).prod := by
  classical
  intro n
  induction n with
  | zero =>
    intro H φ e a ha
    refine ⟨fun i => i.elim0, fun i => i.elim0, ?_⟩
    simpa [conv] using Finsupp.support_single_subset ha
  | succ n ih =>
    intro H φ e a ha
    rw [List.ofFn_succ, conv, List.foldr_cons] at ha
    obtain ⟨x, hx, h2⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum ha)
    obtain ⟨y, hy, h3⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum h2)
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset h3)
    obtain ⟨b, hb, rfl⟩ := ih (fun i => H i.succ) (fun i => φ i.succ) (fun i => e i.succ) y hy
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    refine ⟨Fin.cons b₀ b, fun i => Fin.cases hb₀ hb i, ?_⟩
    rw [List.ofFn_succ, List.prod_cons]
    rfl

theorem aconv_support {G : Type} [AddMonoid G] (p : G → Prop) (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y)) :
    ∀ l : List (G →₀ ℂ), (∀ c ∈ l, ∀ u ∈ c.support, p u) → ∀ u ∈ (aconv l).support, p u := by
  classical
  intro l
  induction l with
  | nil =>
    intro _ u hu
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hu)
    exact h0
  | cons c l ih =>
    intro h u hu
    rw [aconv, List.foldr_cons] at hu
    obtain ⟨x, hx, h2⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hu)
    obtain ⟨y, hy, h3⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum h2)
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset h3)
    exact hadd _ _ (h c List.mem_cons_self x hx) (ih (fun c hc => h c (List.mem_cons_of_mem _ hc)) y hy)

end Groups

section Combinations

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem comb_aconv_cons (c : WO S T →₀ ℂ) (l : List (WO S T →₀ ℂ))
    (h : ∀ x ∈ c.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (c :: l)) f = comb ψ S T c (comb ψ S T (aconv l) f) := by
  classical
  have e : aconv (c :: l) = ∑ x ∈ c.support, ∑ y ∈ (aconv l).support, Finsupp.single (x + y) (c x * aconv l y) := rfl
  rw [e, GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum]
  rw [← Finsupp.sum_finset_sum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finsupp.sum_finset_sum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T x y = 0 := by
    unfold symplOH
    rw [h x hx y hy, mul_zero]
  rw [Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T (x + y) f)), GlobalTheory.WeilVacMove.heisO_heisO, h0,
    AddChar.map_zero_eq_one, one_smul]

def Off (e : AE D) (u : WO S T) : Prop := IsHalf (1 - e) u ∧ u.map (infPart D) = 0

theorem off_zero (e : AE D) : Off S T e 0 := ⟨fun _ _ => mul_zero _, by ext i j; exact map_zero (infPart D)⟩

theorem off_add (e : AE D) (x y : WO S T) (hx : Off S T e x) (hy : Off S T e y) : Off S T e (x + y) := by
  refine ⟨fun i j => ?_, ?_⟩
  · change (1 - e) * (x i j + y i j) = x i j + y i j
    rw [mul_add, hx.1, hy.1]
  · ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx.2 i) j
    have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy.2 i) j
    change infPart D (x i j + y i j) = 0
    rw [RingHom.map_add, h1, h2, add_zero]

theorem off_of_half {e e' : AE D} (h : e * e' = 0) (hi : infPart D e' = 0) (u : WO S T) (hu : IsHalf e' u) : Off S T e u := by
  refine ⟨fun i j => ?_, ?_⟩
  · rw [sub_mul, one_mul, ← hu i j, ← mul_assoc e, h, zero_mul, sub_zero]
  · ext i j
    change infPart D (u i j) = 0
    rw [← hu i j, map_mul, hi, zero_mul]

theorem symplO_off {e : AE D} (hc : cA D e = e) (he : e * e = e) {x y : WO S T} (hx : IsHalf e x) (hy : Off S T e y) :
    symplO S T x y = 0 :=
  GlobalTheory.HeisComb.symplO_half S T e (1 - e) x y hc (by rw [mul_sub, mul_one, he, sub_self]) hx hy.1

theorem comb_aconv_strip : ∀ {n : ℕ} (E : Fin n → AE D) (c : Fin n → WO S T →₀ ℂ), (∀ i, cA D (E i) = E i) →
    (∀ i, E i * E i = E i) → (∀ i j, i ≠ j → E i * E j = 0) → (∀ i, infPart D (E i) = 0) →
    (∀ i, ∀ u ∈ (c i).support, IsHalf (E i) u) → ∀ i, ∃ c' : WO S T →₀ ℂ, (∀ u ∈ c'.support, Off S T (E i) u) ∧
      ∀ f, comb ψ S T (aconv (List.ofFn c)) f = comb ψ S T (c i) (comb ψ S T c' f) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ i; exact i.elim0
  | succ n ih =>
    intro E c hc he ho hi hs i
    have ht : ∀ u ∈ (aconv (List.ofFn fun j : Fin n => c j.succ)).support, Off S T (E 0) u :=
      aconv_support _ (off_zero S T _) (off_add S T _) _ fun d hd u hu => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hd
        exact off_of_half S T (ho _ _ (Fin.succ_ne_zero j).symm) (hi _) u (hs _ u hu)
    have h1 := comb_aconv_cons ψ S T (c 0) _ fun x hx y hy => symplO_off S T (hc 0) (he 0) (hs 0 x hx) (ht y hy)
    rw [List.ofFn_succ]
    cases i using Fin.cases with
    | zero => exact ⟨_, ht, h1⟩
    | succ i =>
      obtain ⟨c', hc', e'⟩ := ih (fun j => E j.succ) (fun j => c j.succ) (fun j => hc _) (fun j => he _)
        (fun a b hab => ho _ _ fun e => hab (Fin.succ_injective _ e)) (fun j => hi _) (fun j => hs _) i
      obtain ⟨c'', hc'', e''⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (c 0) c'
      refine ⟨c'', fun u hu => ?_, fun f => ?_⟩
      · obtain ⟨x, hx, y, hy, rfl⟩ := hc'' u hu
        exact off_add S T _ _ _ (off_of_half S T (ho _ _ (Fin.succ_ne_zero i)) (hi _) x (hs 0 x hx)) (hc' y hy)
      · rw [h1, e', e'', (GlobalTheory.HeisComb.main D ψ S T).2.1 (c 0) (c i.succ) fun x hx y hy =>
          symplO_off S T (hc 0) (he 0) (hs 0 x hx) (off_of_half S T (ho _ _ (Fin.succ_ne_zero i).symm) (hi _) y (hs _ y hy))]

def combL (c : WO S T →₀ ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem comb_single (y : WO S T) (f : WO S T → ℂ) : comb ψ S T (Finsupp.single y 1) f = heisO ψ S T y f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T y f)), one_smul]

theorem model_comb (hψ : IsStdChar D ψ (-1)) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (hc : cA D (p.e + cA D p.e) = p.e + cA D p.e)
    (he : (p.e + cA D p.e) * (p.e + cA D p.e) = p.e + cA D p.e) (c : WO S T →₀ ℂ)
    (h : ∀ u ∈ c.support, Off S T (p.e + cA D p.e) u) (f : WO S T → ℂ)
    (hf : ∃ M O, p.IsModel ψ FS FT M ∧ IsOne O ∧ M O = f) : ∃ M O, p.IsModel ψ FS FT M ∧ IsOne O ∧ M O = comb ψ S T c f := by
  obtain ⟨M, O, hM, hO, rfl⟩ := hf
  refine ⟨combL ψ S T c ∘ₗ M, O, (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k p Y Y' S T FS FT ψ hψ).2.1 M hM _ (fun f hf => ?_) (fun f _ y hy => ?_),
    hO, rfl⟩
  · exact (GlobalTheory.HeisComb.main D ψ S T).2.2.1 c f hf (fun u hu => (h u hu).2) hψ
  · change comb ψ S T c (heisO ψ S T y f) = heisO ψ S T y (comb ψ S T c f)
    rw [← comb_single, ← comb_single]
    refine ((GlobalTheory.HeisComb.main D ψ S T).2.1 _ c (fun x hx z hz => ?_) f).symm
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hx)
    exact symplO_off S T hc he hy (h z hz)

end Combinations

section Places

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

open GlobalTheory.SplitCut GlobalTheory.LocWeil.PlaceIdem in
theorem sum_eq_eFin {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : q.e + cA D q.e = algebraMap (AF D.host.F) (AE D) (eFin D.host.F q.v) := by
  obtain ⟨ε, hε, h⟩ := q.above
  rw [h, eFin_of_placeIdem hε]

open GlobalTheory.SplitCut GlobalTheory.LocWeil.PlaceIdem in

theorem exists_vac (hψ : IsStdChar D ψ (-1)) {r : ℕ} (Q : Fin r → QStep S) (hinj : Function.Injective fun i => (Q i).q.v)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (hv : ∀ i, (Q i).Vac f₁ f₂) (i : Fin r) :
    ∃ f₁' f₂', (Q i).Vac f₁' f₂' ∧ comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₁)) f₁ = comb ψ _ _ (Q i).D₁ f₁' ∧
      comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₂)) f₂ = comb ψ _ _ (Q i).D₂ f₂' := by
  let E : Fin r → AE D := fun i => (Q i).q.e + cA D (Q i).q.e
  have hE : ∀ i, E i = algebraMap (AF D.host.F) (AE D) (eFin D.host.F (Q i).q.v) := fun i => sum_eq_eFin (Q i).q
  have hc : ∀ i, cA D (E i) = E i := fun i => by rw [hE]; exact cA_algebraMap _
  have he : ∀ i, E i * E i = E i := fun i => by rw [hE, ← map_mul, eFin_idem]
  have ho : ∀ i j, i ≠ j → E i * E j = 0 := fun i j hij => by
    rw [hE, hE, ← map_mul, eFin_mul_eFin _ (fun h => hij (hinj h)), map_zero]
  have hi : ∀ i, infPart D (E i) = 0 := fun i =>
    (RingHom.mem_ker).1 (Ideal.mem_inf.1 (GlobalTheory.FinPl.FrameLat.sum_mem_idAt (p := (Q i).q))).1
  obtain ⟨c₁, h₁, e₁⟩ := comb_aconv_strip ψ _ _ E (fun i => (Q i).D₁) hc he ho hi (fun i => (Q i).dat₁.1) i
  obtain ⟨c₂, h₂, e₂⟩ := comb_aconv_strip ψ _ _ E (fun i => (Q i).D₂) hc he ho hi (fun i => (Q i).dat₂.1) i
  exact ⟨comb ψ _ _ c₁ f₁, comb ψ _ _ c₂ f₂, ⟨model_comb ψ _ _ hψ (ofSplit (Q i).q) _ _ (hc i) (he i) c₁ h₁ f₁ (hv i).1,
    model_comb ψ _ _ hψ (ofSplit (Q i).q) _ _ (hc i) (he i) c₂ h₂ f₂ (hv i).2⟩, e₁ f₁, e₂ f₂⟩

theorem con_ne_zero {c₁ c₂ Φ₁ Φ₂ φ f g h₁ h₂} (h : S.val c₁ c₂ Φ₁ Φ₂ φ f g h₁ h₂ ≠ 0) : S.con Φ₁ Φ₂ g h₁ h₂ ≠ 0 := by
  intro h0
  apply h
  have e1 : biComb ψ _ _ _ c₁ c₂ (0 : WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ) = 0 := by
    funext u v
    simp [biComb, comb, heisO]
  have e2 : biLift S.oma S.omb S.B.vA S.J.v0 φ 0 = 0 := by
    funext z
    have e3 : ∀ p, (fun _ : WO S.J.W₀ S.B'.A => S.oma p (fun _ => (0 : ℂ)) 0) = 0 := fun p => by
      funext v
      exact congrFun (map_zero (S.oma p)) 0
    simp only [biLift, Pi.zero_apply, e3, map_zero, mul_zero, integral_zero]
  rw [Dbl2.val, h0, e1, e2]
  simp [BesLev.per, besPer, besFun]

theorem flat_ne_zero {Φ₁ Φ₂ g h₁ h₂} (h : S.con Φ₁ Φ₂ g h₁ h₂ ≠ 0) : flatBF S.s₁ (S.s₁.om (g, h₁) Φ₁) ≠ 0 := by
  intro h0
  apply h
  funext u v
  rw [Dbl2.con, h0]
  simp [GlobalTheory.Unf.contr]

section Family

variable {V : HSp D} {r : ℕ} {k : Fin r → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)]
  [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) {Y : Fin r → Type} [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (Y i)] (F : ∀ i, Frame (k i) V.rank (Y i)) (gl : ∀ i, GL (Y i) (k i) →* GA D V)

theorem gl_mem_at (h : ∀ i g, (ofSplit (q i)).IsLoc (F i) (gl i g) g) {P : GlobalTheory.FinPl.Pl D → Prop} (i : Fin r) (hP : P (q i).v)
    (g : GL (Y i) (k i)) : gl i g ∈ GlobalTheory.FinPl.grpAt V P :=
  GlobalTheory.CellLevels.grpAt_le_of_imp V (fun _ hv => hv ▸ hP) ((GlobalTheory.FinPl.Model.mem_grpAt_iff (q i) V _).2 (h i g).1)

theorem gl_mem_off (hinj : Function.Injective fun i => (q i).v) (h : ∀ i g, (ofSplit (q i)).IsLoc (F i) (gl i g) g) (i j : Fin r)
    (hij : j ≠ i) (g : GL (Y j) (k j)) : gl j g ∈ GlobalTheory.FinPl.grpOff V (· = (q i).v) :=
  GlobalTheory.FinPl.SetCut.grpAt_le_grpOff V (· = (q j).v) _ (fun _ h1 h2 => hij (hinj (h1.symm.trans h2)))
    (gl_mem_at q F gl h (P := (· = (q j).v)) j rfl g)

theorem gl_comm (h : ∀ i g, (ofSplit (q i)).IsLoc (F i) (gl i g) g) (i : Fin r) (g : GL (Y i) (k i)) :
    ∀ y ∈ GlobalTheory.FinPl.grpOff V (· = (q i).v), gl i g * y = y * gl i g :=
  (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (k i) (q i) V (Y i) (F i) (gl i) (h i)).2.2.2.1 g

theorem exists_prod (hinj : Function.Injective fun i => (q i).v) (h : ∀ i g, (ofSplit (q i)).IsLoc (F i) (gl i g) g) :
    ∀ a ∈ GlobalTheory.FinPl.grpAt V fun v => ∃ i, (q i).v = v, ∃ x : ∀ i, GL (Y i) (k i), a = (List.ofFn fun i => gl i (x i)).prod := by
  intro a ha
  obtain ⟨y, hy, e⟩ := GlobalTheory.SplitDecomp.prod_of_grpAt D V r k q hinj a
    (GlobalTheory.CellLevels.grpAt_le_of_imp V (fun _ ⟨i, hi⟩ => ⟨i, hi.symm⟩) ha)
  have hr : ∀ i, ∃ x, gl i x = y i := fun i => by
    have := (GlobalTheory.FinPl.Model.mem_grpAt_iff (q i) V _).2 (hy i)
    rw [← (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (k i) (q i) V (Y i) (F i) (gl i) (h i)).2.1] at this
    exact this
  choose x hx using hr
  exact ⟨x, by rw [e, List.ofFn_eq_map, funext hx]⟩

end Family

open GlobalTheory.QVal GlobalTheory.FinPl

theorem exists_con {r : ℕ} (Q : Fin r → QStep S) (hinj : Function.Injective fun i => (Q i).q.v)
    {c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y} (hg : g ∈ grpOff S.B.V (places Q)) (h : integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y ≠ 0) (i : Fin r) :
    ∃ a ∈ (Q i).e₀.support, ∃ g' ∈ grpOff S.B.V (· = (Q i).q.v),
      S.con (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₁)) f₁) (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₂)) f₂)
        (g' * (Q i).gl₀ a) (h₁ * x) (h₂ * y) ≠ 0 := by
  obtain ⟨a, ha, h'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, hb, rfl⟩ := conv_support _ (fun i => ⇑(Q i).gl₀) (fun i => (Q i).e₀) a ha
  refine ⟨b i, hb i, g * ((List.ofFn fun i => (Q i).gl₀ (b i)).prod * ((Q i).gl₀ (b i))⁻¹), Subgroup.mul_mem _ ?_ ?_, ?_⟩
  · exact grpOff_anti D _ _ _ (fun v hv => ⟨i, hv.symm⟩) hg
  · exact prod_mul_inv_mem _ (fun i => (Q i).gl₀ (b i)) i
      (fun j hj => gl_mem_off (fun i => (Q i).q) (fun i => (Q i).F.G₀) (fun i => (Q i).gl₀) hinj (fun i => (Q i).loc₀) i j hj _)
      (gl_comm (fun i => (Q i).q) (fun i => (Q i).F.G₀) (fun i => (Q i).gl₀) (fun i => (Q i).loc₀) i _)
  · rw [mul_assoc, inv_mul_cancel_right]
    exact con_ne_zero (right_ne_zero_of_mul h')

theorem cells_first (hψ : IsStdChar D ψ (-1)) {r : ℕ} (Q : Fin r → QStep S) (hinj : Function.Injective fun i => (Q i).q.v)
    {c₁ c₂ f₁ f₂ φ f g h₁ h₂} (hH : Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) (i : Fin r) :
    ∃ T : Finset (GL ((Q i).n₁ ⊕ Fin ((Q i).c + 1 + 1)) (Q i).k), ∀ z ∈ grpOff S.J.W (· = (Q i).q.v), ∀ x,
      (∃ y, integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (z * (Q i).gl₁ x) y ≠ 0) →
        ∃ t ∈ T, ∃ ρ, (Q i).gl₁ ρ ∈ jacGrp S.J.d ∧ ∃ j ∈ (Q i).L₁.J, x = ρ * t * j := by
  classical
  obtain ⟨-, -, -, hv, -, -, -, hg, hh₁, -⟩ := hH
  obtain ⟨f₁', f₂', hv', e₁, -⟩ := exists_vac hψ Q hinj f₁ f₂ hv i
  choose T hT _ using GlobalTheory.T.splitPlaceDoubleStepFinitelyManyCellsUniform_proof D ψ hψ σ S (Q i)
  refine ⟨(Q i).e₀.support.biUnion T, fun z hz x ⟨y, hy⟩ => ?_⟩
  obtain ⟨a, ha, g', hg', hc⟩ := exists_con Q hinj hg hy i
  have hf := flat_ne_zero hc
  rw [e₁, ← mul_assoc] at hf
  obtain ⟨t, ht, h⟩ := hT a f₁' f₂' hv' g' hg' (h₁ * z)
    (Subgroup.mul_mem _ (grpOff_anti D _ _ _ (fun v hv => ⟨i, hv.symm⟩) hh₁) hz) x hf
  exact ⟨t, Finset.mem_biUnion.2 ⟨a, ha, ht⟩, h⟩

theorem cells_second (hψ : IsStdChar D ψ (-1)) {r : ℕ} (Q : Fin r → QStep S) (hinj : Function.Injective fun i => (Q i).q.v)
    {c₁ c₂ f₁ f₂ φ f g h₁ h₂} (hH : Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) (x : GA D S.J.W) (i : Fin r) :
    ∃ T : Finset (GL ((Q i).n₂ ⊕ Fin ((Q i).c + 1)) (Q i).k), ∀ z ∈ grpOff S.B'.V (· = (Q i).q.v), ∀ y,
      integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x (z * (Q i).gl₂ y) ≠ 0 →
        ∃ t ∈ T, ∃ ρ, (Q i).gl₂ ρ ∈ besGrp S.B'.d S.B'.o ∧ ∃ j ∈ (Q i).L₂.J, y = ρ * t * j := by
  classical
  obtain ⟨-, -, -, hv, -, -, -, hg, -, hh₂⟩ := hH
  obtain ⟨f₁', f₂', hv', e₁, e₂⟩ := exists_vac hψ Q hinj f₁ f₂ hv i
  obtain ⟨x₀, hx₀, -⟩ := (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (Q i).k (Q i).q S.J.W _ (Q i).F.G₁ (Q i).gl₁ (Q i).loc₁).2.2.1 (h₁ * x)
  choose _ _ T hT using GlobalTheory.T.splitPlaceDoubleStepFinitelyManyCellsUniform_proof D ψ hψ σ S (Q i)
  refine ⟨(Q i).e₀.support.biUnion fun a => T a x₀, fun z hz y hy => ?_⟩
  obtain ⟨a, ha, g', hg', hc⟩ := exists_con Q hinj hg hy i
  rw [e₁, e₂, ← mul_assoc, ← inv_mul_cancel_right (h₁ * x) ((Q i).gl₁ x₀)] at hc
  obtain ⟨t, ht, h⟩ := hT a x₀ f₁' f₂' hv' g' hg' _ hx₀ (h₂ * z)
    (Subgroup.mul_mem _ (grpOff_anti D _ _ _ (fun v hv => ⟨i, hv.symm⟩) hh₂) hz) y hc
  exact ⟨t, Finset.mem_biUnion.2 ⟨a, ha, ht⟩, h⟩

end Places

open GlobalTheory.QVal GlobalTheory.FinPl in
set_option maxHeartbeats 1000000 in

theorem finite_cells : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → (∃ T : Finset (grpAt S.J.W (places fun i => Q i.succ) × GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k), ∀ x y, pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y ≠ 0 → ∃ t ∈ T, ∃ r ∈ ((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ))).prod (RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1)), ∃ κ ∈ (levJ fun i => Q i.succ).prod (Q 0).L₁.J, x = r * t * κ) ∧ ∀ x, ∃ T : Finset (grpAt S.B'.V (places fun i => Q i.succ) × GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k), ∀ y, pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y ≠ 0 → ∃ t ∈ T, ∃ r ∈ ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ))).prod (R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1)), ∃ κ ∈ (levB fun i => Q i.succ).prod (Q 0).L₂.J, y = r * t * κ := by
  intro D ψ hψ σ S r Q hinj c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  have hinj' : Function.Injective fun i : Fin r => (Q i.succ).q.v := fun i j h => Fin.succ_injective _ (hinj h)
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨T, hT⟩ := cells_prod _ (fun i => (Q i).gl₁) (fun i => grpOff S.J.W (· = (Q i).q.v))
      (gl_mem_off (fun i => (Q i).q) (fun i => (Q i).F.G₁) _ hinj fun i => (Q i).loc₁)
      (gl_comm (fun i => (Q i).q) (fun i => (Q i).F.G₁) _ fun i => (Q i).loc₁) (grpAt S.J.W (places fun i => Q i.succ))
      (fun i => gl_mem_at (fun i => (Q i).q) (fun i => (Q i).F.G₁) _ (fun i => (Q i).loc₁) i.succ ⟨i, rfl⟩)
      (exists_prod (fun i : Fin r => (Q i.succ).q) (fun i => (Q i.succ).F.G₁) _ hinj' fun i => (Q i.succ).loc₁)
      (jacGrp S.J.d) (fun i => (Q i).L₁.J) (RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1))
      (fun h => (((GlobalTheory.T.periodLocalGroups_normalFrames_splitPlace D (Q 0).k (Q 0).q (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1)).1 S.J _ _ _ _ (Q 0).gl₁ (Nat.le_add_left 1 σ)
        (Q 0).F.s_ne (GlobalTheory.LocMod.Witness.hz_ne _ S.B) (Q 0).F.jac (Q 0).loc₁).1 h).1)
      (fun x => ∃ y, integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y ≠ 0) (cells_first hψ Q hinj hH)
    exact ⟨T, fun x y h => hT x ⟨_, h⟩⟩
  · exact cells_prod _ (fun i => (Q i).gl₂) (fun i => grpOff S.B'.V (· = (Q i).q.v))
      (gl_mem_off (fun i => (Q i).q) (fun i => (Q i).F.G₂) _ hinj fun i => (Q i).loc₂)
      (gl_comm (fun i => (Q i).q) (fun i => (Q i).F.G₂) _ fun i => (Q i).loc₂) (grpAt S.B'.V (places fun i => Q i.succ))
      (fun i => gl_mem_at (fun i => (Q i).q) (fun i => (Q i).F.G₂) _ (fun i => (Q i).loc₂) i.succ ⟨i, rfl⟩)
      (exists_prod (fun i : Fin r => (Q i.succ).q) (fun i => (Q i.succ).F.G₂) _ hinj' fun i => (Q i.succ).loc₂)
      (besGrp S.B'.d S.B'.o) (fun i => (Q i).L₂.J) (R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1))
      (fun h => (((GlobalTheory.T.periodLocalGroups_normalFrames_splitPlace D (Q 0).k (Q 0).q (Q 0).n₂ ((Q 0).c + 1) σ).2 S.B' _ _ _ (Q 0).gl₂
        (mul_ne_zero (Q 0).F.s_ne (GlobalTheory.LocMod.Witness.xi_ne _)) (Q 0).F.bes' (Q 0).loc₂).1 h).1)
      (fun y => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x.1.1 * (Q 0).gl₁ x.2) y ≠ 0) (cells_second hψ Q hinj hH _)

end GlobalTheory.QCells
