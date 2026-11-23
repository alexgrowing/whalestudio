import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeRename
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.IndexOffRange
import Formalism.ThetaLogCoordinates.JacobiPathWeights.FinalP
import Formalism.LocalToGlobal.GroupLattices.FockModels.WeylDim
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.GrowthBounds.CornerGLContinuity
import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.FirstTermSizeBound

noncomputable section
open Finset Formalism.MainNotions.G

namespace Formalism.MainNotions.G.Joints.Lit

theorem antitone_of_succ {n : ℕ} (μ : Fin n → ℤ) (h : ∀ (a : Fin n) (ha : a.1 + 1 < n), μ ⟨a.1 + 1, ha⟩ ≤ μ a) :
    Antitone μ := by
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have hab' : a ≤ b := hab
  clear hab
  revert hb
  induction b, hab' using Nat.le_induction with
  | base => intro hb; exact le_rfl
  | succ k hak ih =>
    intro hb
    exact (h ⟨k, by omega⟩ hb).trans (ih (by omega))

theorem stCount_eq_dGT (n : ℕ) (μ : Fin n → ℤ) (hμ : Antitone μ) :
    Formalism.MainNotions.SelectionLemmas.stCount n μ = Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT n μ := by
  unfold Formalism.MainNotions.SelectionLemmas.stCount
  rw [← (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.stdCountGT n μ hμ).2]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun I => Formalism.MainNotions.G.ColumnFamilies.restStd n 0 (fun _ => μ) I)

theorem weyl_dimension_formula_index_sets (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.SelectionLemmas.admB3 D := by
  intro n N mu hdom
  have e : Nat.card {I : ℤ → Finset (Fin n) // IsSt mu I} =
      Nat.card {I : ℤ → Finset (Fin n) // Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsStd (pEnd mu) I} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun I => Formalism.MainNotions.G.ColumnFamilies.restStd n N mu I)
  rw [e, (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.stdCountGT n (pEnd mu) hdom).2]
  exact Formalism.L2.G.Model.weylQ n (pEnd mu) hdom

theorem branching_rule_count_form (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.SelectionLemmas.ColumnFamilyLowerSet D := by
  intro m ν hν
  rw [stCount_eq_dGT (m + 1) ν hν]
  simp only [Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT, Formalism.InvariantFactorPaths.GelfandTsetlinBases.gtBox]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [Fintype.mem_piFinset] at hμ
  refine (stCount_eq_dGT m μ (antitone_of_succ μ fun a ha => ?_)).symm
  have h1 := (Finset.mem_Icc.mp (hμ ⟨a.1 + 1, ha⟩)).2
  have h2 := (Finset.mem_Icc.mp (hμ a)).1
  have e : (Fin.castSucc (⟨a.1 + 1, ha⟩ : Fin m)) = a.succ := by ext; simp
  rw [e] at h1
  exact h1.trans h2

theorem strip_up_antitone {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (hν : Antitone ν) (h : HStrip ν μ b) : Antitone μ :=
  by
    obtain ⟨h1, h2, -⟩ := h
    exact antitone_of_succ μ fun a ha => (h2 a ha).trans (h1 a)

theorem strip_down_antitone {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (hν : Antitone ν) (h : HStrip μ ν b) : Antitone μ :=
  by
    obtain ⟨h1, h2, -⟩ := h
    exact antitone_of_succ μ fun a ha => (h1 ⟨a.1 + 1, ha⟩).trans (h2 a ha)

open Classical in

theorem pieri_rule_count_form (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.SelectionLemmas.GenericProjectionCriterion D := by
  intro m ν b hν
  obtain ⟨hup, hdown⟩ := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.gtPieri (m + 1) ν b hν
  have hc : (m + 1 + b - 1).choose b = (b + m).choose m := by
    rw [show m + 1 + b - 1 = b + m by omega, Nat.choose_symm_add]
  rw [stCount_eq_dGT (m + 1) ν hν]
  constructor
  · rw [← hc, ← hup]
    unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp
    symm
    refine Finset.sum_congr ?_ fun μ hμ => ?_
    · ext μ
      simp only [Finset.mem_filter]
      exact and_congr Iff.rfl (Formalism.MainNotions.G.ColumnFamilies.hstrip_iff ν μ b).symm
    · have hs := (Finset.mem_filter.1 hμ).2
      exact stCount_eq_dGT (m + 1) μ (strip_up_antitone hν ((Formalism.MainNotions.G.ColumnFamilies.hstrip_iff ν μ b).1 hs))
  · rw [← hc, ← hdown]
    unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsDown
    symm
    refine Finset.sum_congr ?_ fun μ hμ => ?_
    · ext μ
      simp only [Finset.mem_filter]
      exact and_congr Iff.rfl (Formalism.MainNotions.G.ColumnFamilies.hstrip_iff μ ν b).symm
    · have hs := (Finset.mem_filter.1 hμ).2
      exact stCount_eq_dGT (m + 1) μ (strip_down_antitone hν ((Formalism.MainNotions.G.ColumnFamilies.hstrip_iff μ ν b).1 hs))

end Formalism.MainNotions.G.Joints.Lit

namespace Formalism.MainNotions.G.Joints.Lit

open IsDedekindDomain Formalism.BasicNotions

theorem span_inf_span {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (w : HeightOneSpectrum A) {O Kf : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [IsFractionRing O Kf] (σ : K →+* Kf)
    (hσ : ∀ x : K, w.valuation K x ≤ 1 ↔ σ x ∈ Set.range (algebraMap O Kf))
    {V W ι : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W]
    (φ : V →+ W) (hφ : ∀ (a : K) x, φ (a • x) = σ a • φ x) (b : Module.Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) (L1 L2 : Submodule A V) :
    Submodule.span O (φ '' (L1 : Set V)) ⊓ Submodule.span O (φ '' (L2 : Set V)) =
      Submodule.span O (φ '' ((L1 ⊓ L2 : Submodule A V) : Set V)) := by
  apply le_antisymm
  swap
  · exact le_inf (Submodule.span_mono (Set.image_mono inf_le_left)) (Submodule.span_mono (Set.image_mono inf_le_right))
  rintro z ⟨hz1, hz2⟩
  let φ' : V × V →+ W × W := φ.prodMap φ
  have hφ' : ∀ (a : K) (x : V × V), φ' (a • x) = σ a • φ' x := fun a x => Prod.ext (hφ a x.1) (hφ a x.2)
  let b' := b.prod b
  have hb' : LinearIndependent Kf (φ' ∘ b') := by
    have h := linearIndependent_inl_union_inr' (R := Kf) hb hb
    convert h using 1
    funext i
    rcases i with i | i
    · ext <;> simp [φ', b', Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd]
    · ext <;> simp [φ', b', Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd]
  let U : Submodule K (V × V) := LinearMap.range ((LinearMap.id : V →ₗ[K] V).prod LinearMap.id)
  have key := (FBC.flat_ext (V := V × V) (W := W × W) w σ hσ φ' hφ' b' hb').2 (L1.prod L2) U
  have hL : ∀ y ∈ Submodule.span O (φ '' (L1 : Set V)), (y, (0 : W)) ∈ Submodule.span O (φ' '' ((L1.prod L2 : Submodule A (V × V)) : Set (V × V))) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      exact Submodule.subset_span ⟨(v, 0), ⟨hv, L2.zero_mem⟩, by simp [φ']⟩
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
  have hR : ∀ y ∈ Submodule.span O (φ '' (L2 : Set V)), ((0 : W), y) ∈ Submodule.span O (φ' '' ((L1.prod L2 : Submodule A (V × V)) : Set (V × V))) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      exact Submodule.subset_span ⟨(0, v), ⟨L1.zero_mem, hv⟩, by simp [φ']⟩
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
  have hD : ∀ y ∈ Submodule.span O (φ '' (L1 : Set V)), (y, y) ∈ Submodule.span Kf (φ' '' (U : Set (V × V))) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, _, rfl⟩ := hx
      exact Submodule.subset_span ⟨(v, v), ⟨v, rfl⟩, by simp [φ']⟩
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have := Submodule.smul_mem _ (algebraMap O Kf c) hx
      simpa [algebraMap_smul] using this
  have hzz : (z, z) ∈ Submodule.span O (φ' '' ((L1.prod L2 : Submodule A (V × V)) : Set (V × V))) ⊓
      (Submodule.span Kf (φ' '' (U : Set (V × V)))).restrictScalars O := by
    refine ⟨?_, hD z hz1⟩
    have := Submodule.add_mem _ (hL z hz1) (hR z hz2)
    simpa using this
  rw [key] at hzz
  have hmap := Submodule.mem_map_of_mem (f := LinearMap.fst O W W) hzz
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨x, ⟨hx1, hx2⟩, rfl⟩, rfl⟩
  obtain ⟨v, hv⟩ := hx2
  have hxv : x = (v, v) := hv.symm
  subst hxv
  exact ⟨v, ⟨hx1.1, hx1.2⟩, by simp [φ']⟩

end Formalism.MainNotions.G.Joints.Lit

open Formalism.BasicNotions Formalism.MainNotions.G IsDedekindDomain NumberField Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.Joints.Lit

variable {D : D7}

def YvRat (c : LatCmp D) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (D.gat u w hg).P.nV),
    ∃ yL : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.fm u).lat 0).V,
      ∀ x, (D.gat u w hg).yv v (c.cmp u w hg x) = c.cmp u w hg (yL x)

theorem iter_rat {α β : Type*} (f : α → α) (g : β → β) (φ : β → α) (h : ∀ x, f (φ x) = φ (g x)) (k : ℕ) (x : β) :
    f^[k] (φ x) = φ (g^[k] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, h]

theorem foldr_rat {α β ι : Type*} (F : ι → α → α) (G : ι → β → β) (φ : β → α) (h : ∀ i x, F i (φ x) = φ (G i x))
    (l : List ι) (x : β) :
    (l.map F).foldr (fun f g => f ∘ g) id (φ x) = φ ((l.map G).foldr (fun f g => f ∘ g) id x) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons, List.foldr_cons, Function.comp_apply, ih, h]

theorem span_image_spanA (c : LatCmp D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf] (T : Set ((D.fm u).lat 0).V) :
    Submodule.span (D.gat u w hg).O (c.cmp u w hg '' (Submodule.span (𝓞 D.what₂.LL) T : Set ((D.fm u).lat 0).V)) =
      Submodule.span (D.gat u w hg).O (c.cmp u w hg '' T) := by
  refine le_antisymm ?_ (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have e : a • x = (algebraMap (𝓞 D.what₂.LL) D.what₂.LL a) • x := (algebraMap_smul D.what₂.LL a x).symm
    rw [e, c.cmp_smul]
    have e2 : c.embW u w hg (algebraMap (𝓞 D.what₂.LL) D.what₂.LL a) =
        algebraMap (D.gat u w hg).O (D.gat u w hg).Kf
          (FBC.toO (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) a) :=
      (FBC.toO_spec (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) a).symm
    rw [e2, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx

def yProdL {p : ℕ} (G : GAtP p) (vs : List (Fin G.P.nV)) (m : ℕ) : Module.End G.O G.Fn :=
  (vs.map (fun v => yEnd G v ^ m)).prod

theorem yProdL_apply {p : ℕ} (G : GAtP p) (vs : List (Fin G.P.nV)) (m : ℕ) (F : G.Fn) :
    yProdL G vs m F = (vs.map (fun v => (G.yv v)^[m])).foldr (fun f g => f ∘ g) id F := by
  have hp : ∀ (v : Fin G.P.nV) (k : ℕ) (F : G.Fn), (yEnd G v ^ k) F = (G.yv v)^[k] F := by
    intro v k
    induction k with
    | zero => intro F; rfl
    | succ k ih =>
      intro F
      rw [pow_succ', Function.iterate_succ_apply', ← ih]
      rfl
  unfold yProdL
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, Function.comp_apply, ← ih, ← hp]
    all_goals rfl

theorem iter_smul {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f : M →ₗ[R] M) (k : ℕ) (a : R) (x : M) :
    (⇑f)^[k] (a • x) = a • (⇑f)^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_smul]

theorem foldr_smul {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f : ι → M →ₗ[R] M) (k : ℕ)
    (l : List ι) (a : R) (x : M) :
    (l.map (fun i => (⇑(f i))^[k])).foldr (fun g h => g ∘ h) id (a • x) =
      a • (l.map (fun i => (⇑(f i))^[k])).foldr (fun g h => g ∘ h) id x := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons, List.foldr_cons, Function.comp_apply, ih, iter_smul]

set_option maxHeartbeats 1000000 in
open Classical in

theorem NPDesc_of (c : LatCmp D) {L : SizeData₂ D} (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts)
    (hv : c.VramDef Y) (hy : YvRat c) : c.NPDesc X Y K := by
  intro u w hg _
  haveI := LatCmp.frac_of_ties hT u w hg
  choose yL hyL using hy u w hg
  have hpow : ∀ (k : ℕ) (x : ((D.fm u).lat 0).V),
      c.cmp u w hg (((D.what₂.places.resChar w : D.what₂.LL) ^ k) • x) =
        (((D.what₂.places.resChar w : (D.gat u w hg).O) ^ k)) • c.cmp u w hg x := by
    intro k x
    rw [c.cmp_smul, ← algebraMap_smul (D.gat u w hg).Kf ((D.what₂.places.resChar w : (D.gat u w hg).O) ^ k)]
    congr 1
    simp
  let yLP : Finset (HH D) → ((D.fm u).lat 0).V → ((D.fm u).lat 0).V := fun VV' =>
    (VV'.toList.map (fun t0 => (⇑(yL (Y.vOf u w hg t0)))^[D.R.m])).foldr (fun f g => f ∘ g) id
  have hrat : ∀ VV' x, yProd Y u w hg VV' (c.cmp u w hg x) = c.cmp u w hg (yLP VV' x) := by
    intro VV' x
    unfold yProd
    exact foldr_rat _ _ (c.cmp u w hg) (fun t0 x => iter_rat _ _ _ (hyL (Y.vOf u w hg t0)) D.R.m x) VV'.toList x
  have hyLsmul : ∀ VV' (a : D.what₂.LL) x, yLP VV' (a • x) = a • yLP VV' x := fun VV' a x =>
    foldr_smul (fun t0 => yL (Y.vOf u w hg t0)) D.R.m VV'.toList a x
  have hyP : ∀ VV' F, yProd Y u w hg VV' F = yProdL (D.gat u w hg) (VV'.toList.map (Y.vOf u w hg)) D.R.m F := by
    intro VV' F
    rw [yProdL_apply, List.map_map]
    rfl
  have hM : (D.gat u w hg).M =
      Submodule.span (D.gat u w hg).O (c.cmp u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) :=
    (c.cmp_M u w hg).symm
  let s : Finset (HH D) → ℕ := fun VV' =>
    ∑ t0 ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w) \ VV', ⌈Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉.toNat
  let τ : ℕ := ⌈tauP X K (aL L) (bL L) (D.what₂.places.resChar w)⌉.toNat
  let T1 : Set ((D.fm u).lat 0).V := {z | ∃ VV' ⊆ VV X K (aL L) (bL L) (D.what₂.places.resChar w),
    ∃ x ∈ ((D.fm u).lat 0).L, z = yLP VV' (((D.what₂.places.resChar w : D.what₂.LL) ^ s VV') • x)}
  let T2 : Set ((D.fm u).lat 0).V := {z | ∃ x ∈ ((D.fm u).lat 0).L, z = ((D.what₂.places.resChar w : D.what₂.LL) ^ τ) • x}
  have hS1 : Submodule.span (D.gat u w hg).O {F' | ∃ VV' ⊆ VV X K (aL L) (bL L) (D.what₂.places.resChar w),
      ∃ F ∈ (D.gat u w hg).M,
      F' = yProd Y u w hg VV' (((D.what₂.places.resChar w : (D.gat u w hg).O) ^ s VV') • F)} =
      Submodule.span (D.gat u w hg).O (c.cmp u w hg '' T1) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨VV', hVV', F, hF, rfl⟩
      let Q : Module.End (D.gat u w hg).O (D.gat u w hg).Fn :=
        ((D.what₂.places.resChar w : (D.gat u w hg).O) ^ s VV') •
          yProdL (D.gat u w hg) (VV'.toList.map (Y.vOf u w hg)) D.R.m
      have hQ : yProd Y u w hg VV' (((D.what₂.places.resChar w : (D.gat u w hg).O) ^ s VV') • F) = Q F := by
        rw [hyP, map_smul]; rfl
      rw [SetLike.mem_coe, hQ]
      rw [hM] at hF
      have := Submodule.mem_map_of_mem (f := Q) hF
      rw [Submodule.map_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨yLP VV' (((D.what₂.places.resChar w : D.what₂.LL) ^ s VV') • x), ⟨VV', hVV', x, hx, rfl⟩, ?_⟩
      show c.cmp u w hg _ = Q (c.cmp u w hg x)
      rw [hyLsmul, hpow, ← hrat, hyP]
      rfl
    · rw [Submodule.span_le]
      rintro _ ⟨z, ⟨VV', hVV', x, hx, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨VV', hVV', c.cmp u w hg x, ?_, ?_⟩
      · rw [hM]; exact Submodule.subset_span ⟨x, hx, rfl⟩
      · rw [hyLsmul, hpow, ← hrat, hyP, hyP, map_smul]
  have hS2 : (D.gat u w hg).M.map (((D.what₂.places.resChar w : (D.gat u w hg).O) ^ τ) • LinearMap.id) =
      Submodule.span (D.gat u w hg).O (c.cmp u w hg '' T2) := by
    rw [hM, Submodule.map_span]
    congr 1
    ext F
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, by rw [hpow]; rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, by rw [hpow]; rfl⟩
  have hVr : Y.Vram u w hg = (Submodule.span (D.gat u w hg).Kf
      (c.cmp u w hg '' ((D.fm u).ramSub : Set ((D.fm u).lat 0).V))).restrictScalars (D.gat u w hg).O :=
    SetLike.coe_injective (hv u w hg)
  have hflat := FBC.flat_ext (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) (c.cmp u w hg) (c.cmp_smul u w hg)
    ((D.fm u).lat 0).b (c.cmp_li u w hg)
  have hinf := span_inf_span (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) (c.cmp u w hg) (c.cmp_smul u w hg)
    ((D.fm u).lat 0).b (c.cmp_li u w hg) (Submodule.span (𝓞 D.what₂.LL) T1) (Submodule.span (𝓞 D.what₂.LL) T2)
  have hNP : NP X Y K u w hg = Submodule.span (D.gat u w hg).O (c.cmp u w hg ''
      (((Submodule.span (𝓞 D.what₂.LL) T1 ⊓ Submodule.span (𝓞 D.what₂.LL) T2) ⊓
        (D.fm u).ramSub.restrictScalars (𝓞 D.what₂.LL) : Submodule (𝓞 D.what₂.LL) ((D.fm u).lat 0).V) :
          Set ((D.fm u).lat 0).V)) := by
    show Submodule.span (D.gat u w hg).O _ ⊓ _ ⊓ _ = _
    rw [hS1, hS2, hVr, ← span_image_spanA c u w hg T1, ← span_image_spanA c u w hg T2, hinf]
    exact hflat.2 _ _
  calc NP X Y K u w hg = _ := hNP
    _ ≤ _ := by
      apply Submodule.span_mono
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨y, ⟨hy.2, ?_⟩, rfl⟩
      rw [hNP]
      exact Submodule.subset_span ⟨y, hy, rfl⟩

def YvRatU (c : LatCmp D) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (D.gat u w hg).P.nV),
    ∃ (yL : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.fm u).lat 0).V) (ε : (D.gat u w hg).Oˣ),
      ∀ x, (D.gat u w hg).yv v (c.cmp u w hg x) = (ε : (D.gat u w hg).O) • c.cmp u w hg (yL x)

theorem yProdL_ratU {p : ℕ} (G : GAtP p) {V : Type*} (φ : V → G.Fn) (yL : Fin G.P.nV → V → V)
    (ε : Fin G.P.nV → G.Oˣ) (h : ∀ v x, G.yv v (φ x) = (ε v : G.O) • φ (yL v x)) (m : ℕ) (vs : List (Fin G.P.nV))
    (x : V) :
    yProdL G vs m (φ x) = (((vs.map (fun v => ε v ^ m)).prod : G.Oˣ) : G.O) •
      φ ((vs.map (fun v => (yL v)^[m])).foldr (fun f g => f ∘ g) id x) := by
  have hstep : ∀ (v : Fin G.P.nV) (k : ℕ) (y : V),
      (G.yv v)^[k] (φ y) = (((ε v ^ k : G.Oˣ)) : G.O) • φ ((yL v)^[k] y) := by
    intro v k
    have hlin : ∀ (c : G.O) (F : G.Fn), G.yv v (c • F) = c • G.yv v F :=
      fun c F => map_smul (yEnd G v) c F
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', hlin, h, smul_smul,
        pow_succ, Units.val_mul]
  rw [yProdL_apply]
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons, List.foldr_cons, Function.comp_apply, List.prod_cons]
    rw [ih]
    have hi : ∀ (c : G.O) (F : G.Fn), (G.yv v)^[m] (c • F) = c • (G.yv v)^[m] F :=
      fun c F => iter_smul (yEnd G v) m c F
    rw [hi, hstep, smul_smul, Units.val_mul, mul_comm]
set_option maxHeartbeats 1000000 in
open Classical in

theorem NPDesc_ofU (c : LatCmp D) {L : SizeData₂ D} (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts)
    (hv : c.VramDef Y) (hy : YvRatU c) : c.NPDesc X Y K := by
  intro u w hg _
  haveI := LatCmp.frac_of_ties hT u w hg
  choose yL ε hyL using hy u w hg
  have hpow : ∀ (k : ℕ) (x : ((D.fm u).lat 0).V),
      c.cmp u w hg (((D.what₂.places.resChar w : D.what₂.LL) ^ k) • x) =
        (((D.what₂.places.resChar w : (D.gat u w hg).O) ^ k)) • c.cmp u w hg x := by
    intro k x
    rw [c.cmp_smul, ← algebraMap_smul (D.gat u w hg).Kf ((D.what₂.places.resChar w : (D.gat u w hg).O) ^ k)]
    congr 1
    simp
  let yLP : Finset (HH D) → ((D.fm u).lat 0).V → ((D.fm u).lat 0).V := fun VV' =>
    (VV'.toList.map (fun t0 => (⇑(yL (Y.vOf u w hg t0)))^[D.R.m])).foldr (fun f g => f ∘ g) id
  have hyLsmul : ∀ VV' (a : D.what₂.LL) x, yLP VV' (a • x) = a • yLP VV' x := fun VV' a x =>
    foldr_smul (fun t0 => yL (Y.vOf u w hg t0)) D.R.m VV'.toList a x
  have hyP : ∀ VV' F, yProd Y u w hg VV' F = yProdL (D.gat u w hg) (VV'.toList.map (Y.vOf u w hg)) D.R.m F := by
    intro VV' F
    rw [yProdL_apply, List.map_map]
    rfl
  let E : Finset (HH D) → (D.gat u w hg).Oˣ := fun VV' =>
    ((VV'.toList.map (Y.vOf u w hg)).map (fun v => ε v ^ D.R.m)).prod
  have hrat : ∀ VV' x, yProd Y u w hg VV' (c.cmp u w hg x) = ((E VV' : (D.gat u w hg).Oˣ) : (D.gat u w hg).O) •
      c.cmp u w hg (yLP VV' x) := by
    intro VV' x
    rw [hyP, yProdL_ratU (D.gat u w hg) (c.cmp u w hg) (fun v => ⇑(yL v)) ε hyL D.R.m]
    simp only [E, yLP, List.map_map, Function.comp_def]
  have hM : (D.gat u w hg).M =
      Submodule.span (D.gat u w hg).O (c.cmp u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) :=
    (c.cmp_M u w hg).symm
  let s : Finset (HH D) → ℕ := fun VV' =>
    ∑ t0 ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w) \ VV', ⌈Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉.toNat
  let τ : ℕ := ⌈tauP X K (aL L) (bL L) (D.what₂.places.resChar w)⌉.toNat
  let T1 : Set ((D.fm u).lat 0).V := {z | ∃ VV' ⊆ VV X K (aL L) (bL L) (D.what₂.places.resChar w),
    ∃ x ∈ ((D.fm u).lat 0).L, z = yLP VV' (((D.what₂.places.resChar w : D.what₂.LL) ^ s VV') • x)}
  let T2 : Set ((D.fm u).lat 0).V := {z | ∃ x ∈ ((D.fm u).lat 0).L, z = ((D.what₂.places.resChar w : D.what₂.LL) ^ τ) • x}
  have hS1 : Submodule.span (D.gat u w hg).O {F' | ∃ VV' ⊆ VV X K (aL L) (bL L) (D.what₂.places.resChar w),
      ∃ F ∈ (D.gat u w hg).M,
      F' = yProd Y u w hg VV' (((D.what₂.places.resChar w : (D.gat u w hg).O) ^ s VV') • F)} =
      Submodule.span (D.gat u w hg).O (c.cmp u w hg '' T1) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨VV', hVV', F, hF, rfl⟩
      let Q : Module.End (D.gat u w hg).O (D.gat u w hg).Fn :=
        ((D.what₂.places.resChar w : (D.gat u w hg).O) ^ s VV') •
          yProdL (D.gat u w hg) (VV'.toList.map (Y.vOf u w hg)) D.R.m
      have hQ : yProd Y u w hg VV' (((D.what₂.places.resChar w : (D.gat u w hg).O) ^ s VV') • F) = Q F := by
        rw [hyP, map_smul]; rfl
      rw [SetLike.mem_coe, hQ]
      rw [hM] at hF
      have := Submodule.mem_map_of_mem (f := Q) hF
      rw [Submodule.map_span] at this
      refine (Submodule.span_le.2 ?_) this
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hQx : Q (c.cmp u w hg x) = ((E VV' : (D.gat u w hg).Oˣ) : (D.gat u w hg).O) •
          c.cmp u w hg (yLP VV' (((D.what₂.places.resChar w : D.what₂.LL) ^ s VV') • x)) := by
        show ((D.what₂.places.resChar w : (D.gat u w hg).O) ^ s VV') •
          yProdL (D.gat u w hg) (VV'.toList.map (Y.vOf u w hg)) D.R.m (c.cmp u w hg x) = _
        rw [← hyP, hrat, hyLsmul, hpow, smul_comm]
      rw [SetLike.mem_coe, hQx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨VV', hVV', x, hx, rfl⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨z, ⟨VV', hVV', x, hx, rfl⟩, rfl⟩
      have hx' : c.cmp u w hg x ∈ (D.gat u w hg).M := by rw [hM]; exact Submodule.subset_span ⟨x, hx, rfl⟩
      have hmem : yProd Y u w hg VV' (((D.what₂.places.resChar w : (D.gat u w hg).O) ^ s VV') • c.cmp u w hg x) ∈
          Submodule.span (D.gat u w hg).O {F' | ∃ VV' ⊆ VV X K (aL L) (bL L) (D.what₂.places.resChar w),
            ∃ F ∈ (D.gat u w hg).M,
            F' = yProd Y u w hg VV' (((D.what₂.places.resChar w : (D.gat u w hg).O) ^ s VV') • F)} :=
        Submodule.subset_span ⟨VV', hVV', c.cmp u w hg x, hx', rfl⟩
      have he : yProd Y u w hg VV' (((D.what₂.places.resChar w : (D.gat u w hg).O) ^ s VV') • c.cmp u w hg x) =
          ((E VV' : (D.gat u w hg).Oˣ) : (D.gat u w hg).O) •
            c.cmp u w hg (yLP VV' (((D.what₂.places.resChar w : D.what₂.LL) ^ s VV') • x)) := by
        rw [hyP, map_smul, ← hyP, hrat, hyLsmul, hpow, smul_comm]
      rw [he] at hmem
      have := Submodule.smul_mem _ (((E VV')⁻¹ : (D.gat u w hg).Oˣ) : (D.gat u w hg).O) hmem
      rwa [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at this
  have hS2 : (D.gat u w hg).M.map (((D.what₂.places.resChar w : (D.gat u w hg).O) ^ τ) • LinearMap.id) =
      Submodule.span (D.gat u w hg).O (c.cmp u w hg '' T2) := by
    rw [hM, Submodule.map_span]
    congr 1
    ext F
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, by rw [hpow]; rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, by rw [hpow]; rfl⟩
  have hVr : Y.Vram u w hg = (Submodule.span (D.gat u w hg).Kf
      (c.cmp u w hg '' ((D.fm u).ramSub : Set ((D.fm u).lat 0).V))).restrictScalars (D.gat u w hg).O :=
    SetLike.coe_injective (hv u w hg)
  have hflat := FBC.flat_ext (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) (c.cmp u w hg) (c.cmp_smul u w hg)
    ((D.fm u).lat 0).b (c.cmp_li u w hg)
  have hinf := span_inf_span (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) (c.cmp u w hg) (c.cmp_smul u w hg)
    ((D.fm u).lat 0).b (c.cmp_li u w hg) (Submodule.span (𝓞 D.what₂.LL) T1) (Submodule.span (𝓞 D.what₂.LL) T2)
  have hNP : NP X Y K u w hg = Submodule.span (D.gat u w hg).O (c.cmp u w hg ''
      (((Submodule.span (𝓞 D.what₂.LL) T1 ⊓ Submodule.span (𝓞 D.what₂.LL) T2) ⊓
        (D.fm u).ramSub.restrictScalars (𝓞 D.what₂.LL) : Submodule (𝓞 D.what₂.LL) ((D.fm u).lat 0).V) :
          Set ((D.fm u).lat 0).V)) := by
    show Submodule.span (D.gat u w hg).O _ ⊓ _ ⊓ _ = _
    rw [hS1, hS2, hVr, ← span_image_spanA c u w hg T1, ← span_image_spanA c u w hg T2, hinf]
    exact hflat.2 _ _
  calc NP X Y K u w hg = _ := hNP
    _ ≤ _ := by
      apply Submodule.span_mono
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨y, ⟨hy.2, ?_⟩, rfl⟩
      rw [hNP]
      exact Submodule.subset_span ⟨y, hy, rfl⟩

end Formalism.MainNotions.G.Joints.Lit

namespace Formalism.MainNotions.G.Joints.Lit

theorem pNonUnit {D : D7} (c : LatCmp D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ¬ IsUnit ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) := by
  rintro ⟨t, ht⟩
  have hp0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D.what₂.places.resChar_prime w).ne_zero
  have hmem : c.embW u w hg ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)⁻¹ ∈
      Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf) := by
    refine ⟨((t⁻¹ : (D.gat u w hg).Oˣ) : (D.gat u w hg).O), ?_⟩
    rw [map_inv₀, map_natCast]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_natCast (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf), ← ht, ← map_mul, Units.inv_mul,
      map_one]
  have h0 := (c.embW_int u w hg _).mpr hmem
  have h2 : D.what₂.places.val w (((D.what₂.places.resChar w : ℕ) : D.what₂.LL) *
      ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)⁻¹) = 0 := by
    rw [mul_inv_cancel₀ hp0, AddValuation.map_one]
  rw [AddValuation.map_mul, D.what₂.places.val_resChar w] at h2
  have h3 : ((((D.what₂.places.ramIdx w : ℕ) : ℤ)) : WithTop ℤ) ≤ 0 := by
    calc ((((D.what₂.places.ramIdx w : ℕ) : ℤ)) : WithTop ℤ)
        ≤ ((((D.what₂.places.ramIdx w : ℕ) : ℤ)) : WithTop ℤ) +
          D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)⁻¹ := le_add_of_nonneg_right h0
      _ = 0 := h2
  have h4 := D.what₂.places.ramIdx_pos w
  have h5 : ((D.what₂.places.ramIdx w : ℕ) : ℤ) ≤ 0 := by exact_mod_cast h3
  omega

end Formalism.MainNotions.G.Joints.Lit

namespace Formalism.MainNotions.G.Joints.Lit

theorem mertens_bound (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CornerGLContinuity.MertensBound D := by
  intro y hy
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy
  have hterm : ∀ p ∈ (Finset.range ⌈y⌉₊).filter Nat.Prime, Real.log p / p ≤ Real.log y / p := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    have hpy : (p : ℝ) < y := Nat.lt_ceil.1 (Finset.mem_range.1 hp1)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp2.pos
    exact div_le_div_of_nonneg_right (Real.log_le_log hp0 hpy.le) hp0.le
  by_cases h4 : (4 : ℝ) ≤ y
  · have hc : (4 : ℕ) ≤ ⌈y⌉₊ := by
      have : (4 : ℝ) ≤ (⌈y⌉₊ : ℝ) := h4.trans (Nat.le_ceil y)
      exact_mod_cast this
    set n := ⌈y⌉₊ - 1 with hndef
    have hn : ⌈y⌉₊ = n + 1 := by omega
    have hS : (Finset.range ⌈y⌉₊).filter Nat.Prime = Nat.primesLE n := by
      rw [hn]; rfl
    rw [hS]
    have h1 := Formalism.MainNotions.WeilJacquetShalikaLaw.Proof.sz_mertens n (by omega)
    have hny : (n : ℝ) ≤ y := by
      have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ y by linarith)
      rw [hn] at h
      push_cast at h
      linarith
    have hn0 : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    have h2 : Real.log n ≤ Real.log y := Real.log_le_log hn0 hny
    have h3 : Real.log 4 ≤ Real.log y := Real.log_le_log (by norm_num) h4
    linarith
  · have hc : ⌈y⌉₊ ≤ 4 := Nat.ceil_le.2 (by push_cast; linarith)
    calc ∑ p ∈ (Finset.range ⌈y⌉₊).filter Nat.Prime, Real.log p / p
        ≤ ∑ p ∈ (Finset.range ⌈y⌉₊).filter Nat.Prime, Real.log y / 2 := by
          refine Finset.sum_le_sum fun p hp => (hterm p hp).trans ?_
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
          exact div_le_div_of_nonneg_left hly (by norm_num) hp2
      _ = ((Finset.range ⌈y⌉₊).filter Nat.Prime).card * (Real.log y / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 * (Real.log y / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : ((Finset.range ⌈y⌉₊).filter Nat.Prime).card ≤ 4 :=
            le_trans (Finset.card_filter_le _ _) (by simpa using hc)
          exact_mod_cast hcard
      _ = 2 * Real.log y := by ring

theorem mertens_bound_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Formalism.MainNotions.CornerGLContinuity.FamilyMertensBound Fm :=
  by
    intro x i
    exact mertens_bound _

end Formalism.MainNotions.G.Joints.Lit
