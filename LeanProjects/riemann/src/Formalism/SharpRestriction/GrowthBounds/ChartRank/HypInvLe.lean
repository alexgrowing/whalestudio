import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypRankGe
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfRatInv
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LowestInvariantLeDelta
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ProdMemSpan
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CastGLSymmBc
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PInvLe

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms NumberField Module Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard
  Formalism.MainNotions.G.CmpJ.PRankGe

section Gen

variable {LL K C Y WK V : Type} [Field LL] [Field K] [Field C] (e : LL →+* K)
  [AddCommGroup Y] [Module LL Y] [AddCommGroup WK] [Module K WK] [AddCommGroup V] [Module C V]

theorem finrank_le_transfer (φK : Y →+ WK) (hK : ∀ (a : LL) y, φK (a • y) = e a • φK y)
    (φC : Y →+ V) [FiniteDimensional C V]
    (hind : ∀ (k : ℕ) (y : Fin k → Y), LinearIndependent LL y → LinearIndependent C (φC ∘ y))
    (N : Submodule K WK) (hN : N ≤ Submodule.span K (Set.range φK)) :
    FiniteDimensional K N ∧ finrank K N ≤ finrank C V := by
  have hr : Module.rank LL Y ≤ (finrank C V : Cardinal) := by
    refine rank_le fun s hs => ?_
    have h := hind s.card (fun j => ((s.equivFin.symm j : s) : Y)) (hs.comp _ s.equivFin.symm.injective)
    simpa using h.fintype_card_le_finrank
  have : FiniteDimensional LL Y := Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt hr Cardinal.natCast_lt_aleph0)
  let b := Module.finBasis LL Y
  have hsp : Submodule.span K (Set.range φK) ≤ Submodule.span K (Set.range fun j => φK (b j)) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [← b.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [hK]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hle := hN.trans hsp
  have : FiniteDimensional K (Submodule.span K (Set.range fun j => φK (b j))) :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  have : FiniteDimensional K N := Submodule.finiteDimensional_of_le hle
  refine ⟨this, ?_⟩
  calc finrank K N ≤ finrank K (Submodule.span K (Set.range fun j => φK (b j))) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (finrank LL Y)) := finrank_range_le_card _
    _ = finrank LL Y := Fintype.card_fin _
    _ ≤ finrank C V := by
      have h := hind _ (fun j => b j) b.linearIndependent
      simpa using h.fintype_card_le_finrank

end Gen

section RatPts

variable {LL Kf : Type} [Field LL] [Field Kf] (e : LL →+* Kf)

theorem mapE_smul {σ : Type} (r : LL) (Q : MvPolynomial σ LL) :
    MvPolynomial.map e (r • Q) = e r • MvPolynomial.map e Q := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

theorem ker_desc {σ τ : Type} (Ts : Set (MvPolynomial σ Kf →ₗ[Kf] MvPolynomial τ Kf))
    (hT : ∀ T ∈ Ts, ∀ Q : MvPolynomial σ LL, ∃ Q' : MvPolynomial τ LL, MvPolynomial.map e Q' = T (MvPolynomial.map e Q))
    {ξ : MvPolynomial σ Kf} (hξ : ∀ T ∈ Ts, T ξ = 0) :
    ξ ∈ Submodule.span Kf (MvPolynomial.map e '' {Q | ∀ T ∈ Ts, T (MvPolynomial.map e Q) = 0}) := by
  let φ : MvPolynomial σ LL × MvPolynomial τ LL →+ MvPolynomial σ Kf × MvPolynomial τ Kf :=
    AddMonoidHom.prodMap (MvPolynomial.map e).toAddMonoidHom (MvPolynomial.map e).toAddMonoidHom
  let ev : (σ →₀ ℕ) ⊕ (τ →₀ ℕ) → (MvPolynomial σ Kf × MvPolynomial τ Kf) →ₗ[Kf] Kf :=
    Sum.elim (fun m => (MvPolynomial.lcoeff Kf m).comp (LinearMap.fst Kf _ _))
      (fun m => (MvPolynomial.lcoeff Kf m).comp (LinearMap.snd Kf _ _))
  have hsep : ∀ F, (∀ t, ev t F = 0) → F = 0 := by
    intro F h
    refine Prod.ext (MvPolynomial.ext _ _ fun m => ?_) (MvPolynomial.ext _ _ fun m => ?_)
    · simpa [ev] using h (Sum.inl m)
    · simpa [ev] using h (Sum.inr m)
  have hsm : ∀ (a : LL) x, φ (a • x) = e a • φ x := fun a x =>
    Prod.ext (mapE_smul e a x.1) (mapE_smul e a x.2)
  have hval : ∀ x, IsRat e ev (φ x) := by
    rintro x (m | m)
    · exact ⟨MvPolynomial.coeff m x.1, by simp [ev, φ, MvPolynomial.coeff_map]⟩
    · exact ⟨MvPolynomial.coeff m x.2, by simp [ev, φ, MvPolynomial.coeff_map]⟩
  let S : Set ((MvPolynomial σ Kf × MvPolynomial τ Kf) →ₗ[Kf] (MvPolynomial σ Kf × MvPolynomial τ Kf)) :=
    {Tm | ∃ T ∈ Ts, Tm = LinearMap.id + (LinearMap.inr Kf _ _).comp (T.comp (LinearMap.fst Kf _ _))}
  have hS : ∀ Tm ∈ S, ∀ x, ∃ y, φ y = Tm (φ x) := by
    rintro Tm ⟨T, hT', rfl⟩ x
    obtain ⟨Q', hQ'⟩ := hT T hT' x.1
    refine ⟨(x.1, x.2 + Q'), Prod.ext ?_ ?_⟩ <;> simp [φ, hQ']
  have key : ∀ p : MvPolynomial σ Kf, (p, (0 : MvPolynomial τ Kf)) ∈ Submodule.span Kf (Set.range φ) := by
    intro p
    refine MvPolynomial.induction_on' p (fun m c => ?_) (fun p q hp hq => ?_)
    · have h1 : (MvPolynomial.monomial m c, (0 : MvPolynomial τ Kf)) = c • φ (MvPolynomial.monomial m 1, 0) := by
        simp [φ, MvPolynomial.smul_monomial]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have h2 : (p + q, (0 : MvPolynomial τ Kf)) = (p, 0) + (q, 0) := by simp
      rw [h2]
      exact Submodule.add_mem _ hp hq
  have hinv : ∀ Tm ∈ S, Tm (ξ, 0) = (ξ, 0) := by
    rintro Tm ⟨T, hT', rfl⟩
    simp [hξ T hT']
  have h := span_inv e ev φ hsep hsm hval S hS (key ξ) hinv
  have h' := Submodule.mem_map_of_mem (f := LinearMap.fst Kf (MvPolynomial σ Kf) (MvPolynomial τ Kf)) h
  rw [Submodule.map_span] at h'
  refine Submodule.span_mono ?_ h'
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨x.1, fun T hT' => ?_, rfl⟩
  have := congrArg Prod.snd (hx _ ⟨T, hT', rfl⟩)
  simpa [φ] using this

theorem whc_map {σ M : Type} [AddCommMonoid M] [DecidableEq M] (w : σ → M) (n : M) (Q : MvPolynomial σ LL) :
    MvPolynomial.map e (MvPolynomial.weightedHomogeneousComponent w n Q) =
      MvPolynomial.weightedHomogeneousComponent w n (MvPolynomial.map e Q) := by
  ext d
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem isWH_iff {σ M R : Type} [CommSemiring R] [AddCommMonoid M] [DecidableEq M] (w : σ → M) (n : M) (f : MvPolynomial σ R) :
    MvPolynomial.IsWeightedHomogeneous w f n ↔ MvPolynomial.weightedHomogeneousComponent w n f = f := by
  constructor
  · intro h
    ext d
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    split_ifs with hd
    · rfl
    · by_contra hc
      exact hd (h (Ne.symm hc))
  · intro h d hd
    rw [← h, MvPolynomial.coeff_weightedHomogeneousComponent] at hd
    by_contra hc
    exact hd (if_neg hc)

theorem colAddGen_map {r n : ℕ} (l j : Fin n) (Q : MvPolynomial (Fin r × Fin n) LL) :
    MvPolynomial.map e (Formalism.GradedWeylDivisibility.colAddGen LL l j Q) = Formalism.GradedWeylDivisibility.colAddGen Kf l j (MvPolynomial.map e Q) := by
  induction Q using MvPolynomial.induction_on
  · rename_i a
    simp [Formalism.GradedWeylDivisibility.colAddGen]
  · rename_i p q hp hq
    simp only [map_add, hp, hq]
  · rename_i p v hp
    simp only [map_mul]
    rw [hp, MvPolynomial.map_X]
    congr 1
    simp only [Formalism.GradedWeylDivisibility.colAddGen, MvPolynomial.aeval_X]
    split_ifs <;> simp

theorem dualWeyl_desc {r n : ℕ} (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl Kf r n ν ≤
      Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈ Formalism.GradedWeylDivisibility.dualWeyl Kf r n ν}) := by
  let Ts : Set (MvPolynomial (Fin r × Fin n) Kf →ₗ[Kf] MvPolynomial (Option (Fin r × Fin n)) Kf) :=
    {T | T = (MvPolynomial.rename some).toLinearMap.comp
        (LinearMap.id - MvPolynomial.weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.colW r n) ν)} ∪
      {T | ∃ l j : Fin n, l < j ∧ T = (Formalism.GradedWeylDivisibility.colAddGen Kf l j).toLinearMap - (MvPolynomial.rename some).toLinearMap}
  have hiff : ∀ f, f ∈ Formalism.GradedWeylDivisibility.dualWeyl Kf r n ν ↔ ∀ T ∈ Ts, T f = 0 := by
    intro f
    rw [Formalism.GradedWeylDivisibility.mem_dualWeyl_iff, isWH_iff]
    constructor
    · rintro ⟨h1, h2⟩ T (hT | ⟨l, j, hlj, hT⟩)
      · rw [hT]
        simp [h1]
      · rw [hT]
        simp [h2 l j hlj]
    · intro h
      refine ⟨?_, fun l j hlj => ?_⟩
      · have := h _ (Or.inl rfl)
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply] at this
        have h0 := MvPolynomial.rename_injective some (Option.some_injective _) (this.trans (map_zero _).symm)
        exact (sub_eq_zero.1 h0).symm
      · have := h _ (Or.inr ⟨l, j, hlj, rfl⟩)
        simpa [sub_eq_zero] using this
  have hT : ∀ T ∈ Ts, ∀ Q : MvPolynomial (Fin r × Fin n) LL, ∃ Q' : MvPolynomial (Option (Fin r × Fin n)) LL,
      MvPolynomial.map e Q' = T (MvPolynomial.map e Q) := by
    rintro T (hT | ⟨l, j, hlj, hT⟩) Q <;> rw [hT]
    · exact ⟨MvPolynomial.rename some (Q - MvPolynomial.weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.colW r n) ν Q), by
        simp [MvPolynomial.map_rename, whc_map]⟩
    · exact ⟨Formalism.GradedWeylDivisibility.colAddGen LL l j Q - MvPolynomial.rename some Q, by
        simp [MvPolynomial.map_rename, colAddGen_map]⟩
  intro ξ hξ
  refine Submodule.span_mono ?_ (ker_desc e Ts hT ((hiff ξ).1 hξ))
  rintro _ ⟨Q, hQ, rfl⟩
  exact ⟨Q, (hiff _).2 hQ, rfl⟩

theorem prod_desc {S : Type} [Fintype S] {σ : S → Type} {τ : Type} (f : ∀ s, σ s → τ)
    (Ms : ∀ s, Submodule Kf (MvPolynomial (σ s) Kf))
    (hM : ∀ s, Ms s ≤ Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈ Ms s})) :
    Submodule.span Kf {Z | ∃ F : ∀ s, MvPolynomial (σ s) Kf, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} ≤
      Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈ Submodule.span Kf
        {Z | ∃ F : ∀ s, MvPolynomial (σ s) Kf, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)}}) := by
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  let A : S → Set (MvPolynomial τ Kf) := fun s =>
    {y | ∃ Q : MvPolynomial (σ s) LL, MvPolynomial.map e Q ∈ Ms s ∧ y = MvPolynomial.rename (f s) (MvPolynomial.map e Q)}
  have hx : ∀ s ∈ Finset.univ, MvPolynomial.rename (f s) (F s) ∈ Submodule.span Kf (A s) := by
    intro s _
    have h1 := Submodule.mem_map_of_mem (f := (MvPolynomial.rename (R := Kf) (f s)).toLinearMap) (hM s (hF s))
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨Q, hQ, rfl⟩, rfl⟩
    exact ⟨Q, hQ, rfl⟩
  have h := prod_mem_span Finset.univ A _ hx
  refine Submodule.span_mono ?_ h
  rintro _ ⟨a, ha, rfl⟩
  choose Q hQ hQe using fun s => ha s (Finset.mem_univ s)
  refine ⟨∏ s, MvPolynomial.rename (f s) (Q s), ?_, ?_⟩
  · change MvPolynomial.map e (∏ s, MvPolynomial.rename (f s) (Q s)) ∈ Submodule.span Kf
      {Z | ∃ F : ∀ s, MvPolynomial (σ s) Kf, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)}
    rw [map_prod]
    refine Submodule.subset_span ⟨fun s => MvPolynomial.map e (Q s), hQ, ?_⟩
    simp [MvPolynomial.map_rename]
  · rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hQe s, MvPolynomial.map_rename]

theorem vsp_desc {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Vsp Kf lam0 ≤ Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈ Vsp Kf lam0}) := by
  have hM : ∀ s : Fin n', (if Antitone (lamAt lam0 s) then Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥) ≤
      Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈
        (if Antitone (lamAt lam0 s) then Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥)}) := by
    intro s
    split_ifs
    · exact dualWeyl_desc e _
    · exact bot_le
  exact prod_desc e (σ := fun _ => Fin (m + 1) × Fin (m + 1)) (fun s v => (s, v)) _ hM

end RatPts

section Inv

variable {p : ℕ} (H : GAtP p) {LL : Type} [Field LL] (e : LL →+* H.Kf)

abbrev YR (H : GAtP p) (LL : Type) [Field LL] : Type :=
  MvPolynomial (Σ v : Fin H.P.nV, Fin (H.P.n' v) × (Fin (H.P.m + 1) × Fin (H.P.m + 1))) LL

theorem map_smul_e (r : LL) (Q : YR H LL) : MvPolynomial.map e (r • Q) = e r • MvPolynomial.map e Q := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

def YInv (a : H.comp) (L : H.P.Tup) : Submodule LL (YR H LL) where
  carrier := {Q | MvPolynomial.map e Q ∈ H.P.Vtup ∧ ∀ γ : (H.lev a).Γ, (H.lev a).smul γ L = L →
    ((H.lev a).χ γ : H.O) • (H.lev a).actX γ (MvPolynomial.map e Q) = MvPolynomial.map e Q}
  add_mem' := fun {Q Q'} h h' => by
    simp only [Set.mem_ofPred_eq, map_add] at h h' ⊢
    exact ⟨Submodule.add_mem _ h.1 h'.1, fun γ hγ => by rw [smul_add, h.2 γ hγ, h'.2 γ hγ]⟩
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact ⟨Submodule.zero_mem _, fun γ _ => by rw [smul_zero]⟩
  smul_mem' := fun r Q h => by
    simp only [Set.mem_ofPred_eq] at h ⊢
    rw [map_smul_e]
    refine ⟨Submodule.smul_mem _ _ h.1, fun γ hγ => ?_⟩
    rw [map_smul, ← algebraMap_smul H.Kf, smul_smul, mul_comm, ← smul_smul, algebraMap_smul, h.2 γ hγ]

def SpanRat : Prop :=
  H.P.Vtup ≤ Submodule.span H.Kf (MvPolynomial.map e '' {Q : YR H LL | MvPolynomial.map e Q ∈ H.P.Vtup})

def ActRat (a : H.comp) (L : H.P.Tup) : Prop :=
  ∀ γ : (H.lev a).Γ, (H.lev a).smul γ L = L → ∀ Q : YR H LL, MvPolynomial.map e Q ∈ H.P.Vtup →
    ∃ Q' : YR H LL, MvPolynomial.map e Q' ∈ H.P.Vtup ∧
      MvPolynomial.map e Q' = ((H.lev a).χ γ : H.O) • (H.lev a).actX γ (MvPolynomial.map e Q)

theorem spanRat_holds : SpanRat H e :=
  prod_desc e (σ := fun v => Fin (H.P.n' v) × (Fin (H.P.m + 1) × Fin (H.P.m + 1)))
    (fun v x => (⟨v, x⟩ : Σ v : Fin H.P.nV, Fin (H.P.n' v) × (Fin (H.P.m + 1) × Fin (H.P.m + 1))))
    (fun v => Vsp H.Kf (H.P.lam0 v)) (fun v => vsp_desc e (H.P.lam0 v))

theorem span_HtupW_le {L : H.P.Tup} (hL : H.P.IsLatTup L) :
    Submodule.span H.Kf (H.P.HtupW L : Set H.P.Xsp) ≤ H.P.Vtup :=
  Submodule.span_le.2 fun z hz => Formalism.MainNotions.FormalGroupSystem.Pf.vt_HtupW_le H.P L hL z hz

theorem inv_le_span {a : H.comp} {L : H.P.Tup} (hL : H.P.IsLatTup L) (h1 : SpanRat H e) (h2 : ActRat H e a L) :
    InvK H a L ≤ Submodule.span H.Kf (MvPolynomial.map e '' (YInv H e a L : Set (YR H LL))) := by
  intro ξ hξ
  let Vr : Submodule LL (YR H LL) :=
    { carrier := {Q | MvPolynomial.map e Q ∈ H.P.Vtup}
      add_mem' := fun {Q Q'} h h' => by
        simp only [Set.mem_ofPred_eq, map_add] at h h' ⊢
        exact Submodule.add_mem _ h h'
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        exact Submodule.zero_mem _
      smul_mem' := fun r Q h => by
        simp only [Set.mem_ofPred_eq] at h ⊢
        rw [map_smul_e]
        exact Submodule.smul_mem _ _ h }
  let φ : Vr →+ H.P.Xsp := (MvPolynomial.map e).toAddMonoidHom.comp Vr.subtype.toAddMonoidHom
  let Sx : Set (H.P.Xsp →ₗ[H.Kf] H.P.Xsp) :=
    {Tm | ∃ γ : (H.lev a).Γ, (H.lev a).smul γ L = L ∧ Tm = algebraMap H.O H.Kf ((H.lev a).χ γ : H.O) • (H.lev a).actX γ}
  have hsm : ∀ (r : LL) (x : Vr), φ (r • x) = e r • φ x := fun r x => map_smul_e H e r x.1
  have hval : ∀ x : Vr, IsRat e (evX H) (φ x) := fun x m =>
    ⟨MvPolynomial.coeff m x.1, by simp [φ, evX, MvPolynomial.lcoeff_apply, MvPolynomial.coeff_map]⟩
  have hT : ∀ Tm ∈ Sx, ∀ x : Vr, ∃ y : Vr, φ y = Tm (φ x) := by
    rintro Tm ⟨γ, hγ, rfl⟩ x
    obtain ⟨Q', hQ', e'⟩ := h2 γ hγ x.1 x.2
    refine ⟨⟨Q', hQ'⟩, ?_⟩
    simp only [φ, LinearMap.smul_apply, algebraMap_smul]
    exact e'
  have hξs : ξ ∈ Submodule.span H.Kf (Set.range φ) := by
    refine Submodule.span_mono ?_ (h1 (span_HtupW_le H hL hξ.1))
    rintro _ ⟨Q, hQ, rfl⟩
    exact ⟨⟨Q, hQ⟩, rfl⟩
  have hinv : ∀ Tm ∈ Sx, Tm ξ = ξ := by
    rintro Tm ⟨γ, hγ, rfl⟩
    simp only [LinearMap.smul_apply, algebraMap_smul]
    exact hξ.2 γ hγ
  have h := span_inv e (evX H) φ (evX_sep H) hsm hval Sx hT hξs hinv
  refine Submodule.span_mono ?_ h
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x.1, ⟨x.2, fun γ hγ => ?_⟩, rfl⟩
  have := hx _ ⟨γ, hγ, rfl⟩
  simp only [LinearMap.smul_apply, algebraMap_smul] at this
  exact this

end Inv

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem isLatTup_of_repOk {S : StepIn M i hi G} {β : S.Ch} {rep : {c // S.chOf c = β} → S.cmpt β × (Hc S β).P.Tup}
    (hok : RepOk S β rep) (c : {c // S.chOf c = β}) : (Hc S β).P.IsLatTup (rep c).2 := by
  obtain ⟨g, -, -, -, hg, -⟩ := hok c
  intro v
  exact ⟨(g v : Matrix _ _ _), (Matrix.isUnit_iff_isUnit_det _).1 (g v).isUnit, hg v⟩

def ActRatOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c, ActRat (Hc S β) e (rep c).1 (rep c).2

theorem actRat_of_core {S : StepIn M i hi G} {e : D.what₂.LL →+* G.Kf} {β : S.Ch} (H : S.Core e β) (hS : BlockRationalityField)
    (a : S.cmpt β) (L : (Hc S β).P.Tup) : ActRat (Hc S β) e a L := by
  intro γ _ Q hQ
  obtain ⟨κ, hκ⟩ := (H.toHyp hS).away a γ
  obtain ⟨r, -, hr⟩ := H.chi a γ κ hκ
  have hχ : algebraMap G.O G.Kf (((Hc S β).lev a).χ γ : G.O) = e r⁻¹ := by
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hr
  refine ⟨r⁻¹ • natActR (Hc S β).P D.what₂.LL (blkLL (S.loc β) (sigD D) (tEL D) S.pos ((S.loc β).gamI a γ)) Q, ?_, ?_⟩
  · rw [mapE_smul, map_natActR]
    exact Submodule.smul_mem _ _ (natActR_VtupR (Hc S β).P G.Kf _ _ hQ)
  · rw [mapE_smul, ← actX_map (S.loc β) (tEL D) S.pos e H.actB H.pos_emb a γ Q, ← hχ, algebraMap_smul]

theorem actRatOf_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : ActRatOf S e :=
  fun hS H _ β rep _ c => actRat_of_core (H β) hS (rep c).1 (rep c).2

def ValLiftOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c,
    ∃ Φ : YInv (Hc S β) e (rep c).1 (rep c).2 →+ FiBc S β c,
      ∀ (k : ℕ) (Q : Fin k → YInv (Hc S β) e (rep c).1 (rep c).2), LinearIndependent D.what₂.LL Q → LinearIndependent ℂ (Φ ∘ Q)

theorem invLeOf_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hR : ActRatOf S e) (hV : ValLiftOf S e) : InvLeOf S e := by
  intro hS H X β rep hok c
  have h2 := hR hS H X β rep hok c
  obtain ⟨Φ, hΦ⟩ := hV hS H X β rep hok c
  have : FiniteDimensional ℂ (FiBc S β c) := by
    have := finDim_FiB S β (c.2 ▸ chOf_mem S c.1)
    exact Module.Finite.map _ _
  let Yc := YInv (Hc S β) e (rep c).1 (rep c).2
  refine finrank_le_transfer e ((MvPolynomial.map e).toAddMonoidHom.comp Yc.subtype.toAddMonoidHom)
    (fun r Q => map_smul_e (Hc S β) e r Q.1) Φ hΦ _ ?_
  refine (inv_le_span (Hc S β) e (isLatTup_of_repOk hok c) (spanRat_holds (Hc S β) e) h2).trans (Submodule.span_mono ?_)
  rintro _ ⟨Q, hQ, rfl⟩
  exact ⟨⟨Q, hQ⟩, rfl⟩

theorem invLeOf_of_lift (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ValLiftOf S e) : InvLeOf S e :=
  invLeOf_of S e (actRatOf_holds S e) hV

def InvVal (S : StepIn M i hi G) (β : S.Ch) (c : {c // S.chOf c = β}) : Set (Formalism.L2.Forms.Frames (gramC (gramN D i hi) (embT D)) → ℂ) :=
  {v | v ∈ ValC (gramC (gramN D i hi) (embT D)) (lamTG M i) ∧
    ∀ γ : GL (Fin (D.R.N i)) D.host.E, γ ∈ Formalism.UG.UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → ∀ κ : (S.K β).lev.U,
      ((S.K β).y c).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * ((S.K β).y c).1 * κ.1 →
      ∀ y y' : Formalism.L2.Forms.Frames (gramC (gramN D i hi) (embT D)), IsTr (atInf (embT D) γ) y' y → v y = ((S.K β).lev.chi κ : ℂ) * v y'}

def FormsOnClassOf (S : StepIn M i hi G) : Prop :=
  ∀ β (c : {c // S.chOf c = β}) v, v ∈ InvVal S β c → v ∈ FiBc S β c

def CmpLiftOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c,
    ∃ Φ : YInv (Hc S β) e (rep c).1 (rep c).2 →+ (Formalism.L2.Forms.Frames (gramC (gramN D i hi) (embT D)) → ℂ), (∀ Q, Φ Q ∈ InvVal S β c) ∧
      ∀ (k : ℕ) (Q : Fin k → YInv (Hc S β) e (rep c).1 (rep c).2), LinearIndependent D.what₂.LL Q → LinearIndependent ℂ (Φ ∘ Q)

theorem valLiftOf_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (h1 : FormsOnClassOf S) (h2 : CmpLiftOf S e) :
    ValLiftOf S e := by
  intro hS H X β rep hok c
  obtain ⟨Φ, hΦ, hind⟩ := h2 hS H X β rep hok c
  refine ⟨(Φ.codRestrict (FiBc S β c).toAddSubgroup fun Q => h1 β c _ (hΦ Q)), fun k Q hQ => ?_⟩
  exact LinearIndependent.of_comp (FiBc S β c).subtype (hind k Q hQ)

theorem invLeOf_of_two (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (h1 : FormsOnClassOf S) (h2 : CmpLiftOf S e) :
    InvLeOf S e :=
  invLeOf_of_lift S e (valLiftOf_of S e h1 h2)

theorem chartRankGe_of_lift [IsFractionRing G.O G.Kf] (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β)
    (hS : BlockRationalityField) (X : KAat.ChX S) (hV : ValLiftOf S e) : ChartRankGe S :=
  chartRankGe_of S e H hS X (invLeOf_of_lift S e hV)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

theorem cmpJHyp_of_lift (c : LatCmp D) {I : CmpJIn Tw u μ w h Lv} (Gt : GatTies D) (hS : BlockRationalityField)
    (core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β) (ok : ∀ j hj, (I.at' j hj).st.okW w)
    (twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β) (valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w)
    (iwF : ∀ j hj β, (I.at' j hj).st.IwF β) (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses)
    (X : ∀ j hj, KAat.ChX (I.at' j hj).st) (hV : ∀ j hj, ValLiftOf (I.at' j hj).st (c.embW u w h)) : CmpJHyp c I :=
  cmpJHyp_of_ge c Gt hS core ok twUnit valIntN iwF hfin fun j hj => by
    have : IsFractionRing (gatJ Lv (j + 1)).O (gatJ Lv (j + 1)).Kf := ((D.gat u w h).P.setting (plc Gt u w h)).frac_O
    exact chartRankGe_of_lift _ _ (core j hj) hS (X j hj) (hV j hj)

theorem cmpJHyp_of_two (c : LatCmp D) {I : CmpJIn Tw u μ w h Lv} (Gt : GatTies D) (hS : BlockRationalityField)
    (core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β) (ok : ∀ j hj, (I.at' j hj).st.okW w)
    (twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β) (valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w)
    (iwF : ∀ j hj β, (I.at' j hj).st.IwF β) (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses)
    (X : ∀ j hj, KAat.ChX (I.at' j hj).st) (h1 : ∀ j hj, FormsOnClassOf (I.at' j hj).st)
    (h2 : ∀ j hj, CmpLiftOf (I.at' j hj).st (c.embW u w h)) : CmpJHyp c I :=
  cmpJHyp_of_lift c Gt hS core ok twUnit valIntN iwF hfin X fun j hj => valLiftOf_of _ _ (h1 j hj) (h2 j hj)

end Card

end Formalism.MainNotions.G.CmpJ.PInvLe
