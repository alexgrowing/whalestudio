import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathArgsOfNotMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem kerA_sum_of_grid {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) {ι : Type} (L : Finset ι) (w : ι → ℂ)
    (gs : ι → Sch G a) (g₀ : GA D (G.V a.src)) (h : GA D (G.V a.tgt)) :
    W.kerA a (∑ l ∈ L, w l • gs l) g₀ h = ∑ l ∈ L, w l * W.kerA a (gs l) g₀ h := by
  rcases ha with ⟨i, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;>
    simp [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_sum, map_smul, Finset.sum_apply]

theorem liftA_sum_datum (M : Vol G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) {ι : Type} (L : Finset ι)
    (w : ι → ℂ) (gs : ι → Sch G a) (F : Fn G a.src) (hc : ∀ l ∈ L, LiftConv W M a (gs l) F) :
    liftA W M a (∑ l ∈ L, w l • gs l) F = ∑ l ∈ L, w l • liftA W M a (gs l) F := by
  funext h
  simp only [liftA_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, kerA_sum_of_grid ha, Finset.sum_mul]
  rw [integral_finsetSum _ fun l hl => ?_]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    ring
  · have := (hc l hl h).const_mul (w l)
    refine this.congr (.of_forall fun x => ?_)
    simp only
    ring

theorem liftA_sum_form (M : Vol G) (a : Arrow T) (f : Sch G a) {ι : Type} (s : Finset ι) (w : ι → ℂ)
    (Fs : ι → Fn G a.src) (hc : ∀ k ∈ s, LiftConv W M a f (Fs k)) :
    liftA W M a f (∑ k ∈ s, w k • Fs k) = ∑ k ∈ s, w k • liftA W M a f (Fs k) := by
  funext h
  simp only [liftA_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun k hk => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    ring
  · have := (hc k hk h).const_mul (w k)
    refine this.congr (.of_forall fun x => ?_)
    simp only
    ring

theorem liftA_zero_form (M : Vol G) (a : Arrow T) (f : Sch G a) : liftA W M a f 0 = 0 := by
  have := liftA_smul W M a f 0 0
  rwa [zero_smul, zero_smul] at this

theorem sum_liftP_eq_zero {μ₀ : T} (hL : L.Is μ₀) (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (hC : CuspStep W M ρ t) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ {ι : Type} (s : Finset ι) (c : ι → ℂ) (φ d : ι → PureT G p),
      (∀ k ∈ s, VecAll ρ e p (φ k) (d k)) → (∀ x : ArgT G p, HalfAll e p x → ∑ k ∈ s, c k * famProd p (φ k) x = 0) →
      ∀ (P : PolT G p) (F : Fn G X), IsCuspListed W.θ X F →
      ∑ k ∈ s, c k • liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (d k) P) F = 0
  | _, .nil, _, ι, s, c, φ, d, _, hsum, P, F, _ => by
    have h0 : ∑ k ∈ s, c k = 0 := by
      have := hsum () trivial
      simpa [famProd] using this
    show ∑ k ∈ s, c k • F = 0
    rw [← Finset.sum_smul, h0, zero_smul]
  | _, .snoc a p, hg, ι, s, c, φ, d, hv, hsum, P, F, hF => by
    classical
    obtain ⟨Tm, h1, -, h3⟩ := exists_arrowModel ρ hL he hg.last
    have hmem : ∀ k ∈ s, (φ k).2 ∈ LocTensor.sbSpace e (latA G a) := fun k hk => ((h1 _ _).1 (hv k hk).2).1
    have hd2 : ∀ k ∈ s, (d k).2 = Tm (φ k).2 := fun k hk => ((h1 _ _).1 (hv k hk).2).2
    let b := Module.Basis.ofVectorSpace ℂ (LocTensor.sbSpace e (latA G a))
    let v : ι → LocTensor.sbSpace e (latA G a) := fun k => if h : (φ k).2 ∈ LocTensor.sbSpace e (latA G a) then ⟨_, h⟩ else 0
    have hv' : ∀ k ∈ s, ((v k : LocTensor.sbSpace e (latA G a)) : Sch G a) = (φ k).2 := fun k hk => by
      simp only [v, dif_pos (hmem k hk)]
    let r : ι → Module.Basis.ofVectorSpaceIndex ℂ (LocTensor.sbSpace e (latA G a)) → ℂ := fun k l => b.repr (v k) l
    let Ls := s.biUnion fun k => (b.repr (v k)).support
    have hexp : ∀ k ∈ s, (φ k).2 = ∑ l ∈ Ls, r k l • ((b l : LocTensor.sbSpace e (latA G a)) : Sch G a) := by
      intro k hk
      rw [← hv' k hk]
      conv_lhs => rw [← b.linearCombination_repr (v k)]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun k => (b.repr (v k)).support) hk)
          (fun i (x : ℂ) => x • b i) (fun _ _ => zero_smul _ _), Submodule.coe_sum]
      rfl
    let Fk : ι → Fn G a.src := fun k => liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (d k).1 P.1) F
    have hFk : ∀ k ∈ s, IsCuspListed W.θ a.src (Fk k) := fun k hk =>
      (pathConv_zip_fock M ρ t he hC p hg.init (φ k).1 (d k).1 (hv k hk).1 P.1 F hF).2
    let g : Module.Basis.ofVectorSpaceIndex ℂ (LocTensor.sbSpace e (latA G a)) → Sch G a :=
      fun l => W.fock a.pair (Tm (b l)) P.2
    have hconv : ∀ l, ∀ k ∈ s, LiftConv W M a (g l) (Fk k) := fun l k hk =>
      (hC a hg.last e he (b l) (Tm (b l)) ((h1 _ _).2 ⟨(b l).2, rfl⟩) P.2 (Fk k) (hFk k hk)).1
    have hstep : ∀ k ∈ s, W.fock a.pair (d k).2 P.2 = ∑ l ∈ Ls, r k l • g l := by
      intro k hk
      rw [hd2 k hk, hexp k hk, map_sum]
      simp only [map_smul]
      exact GlobalTheory.SpecFac.pureTensorO_sum W.ψ_std W.θ_is _ _ _ _ Ls (r k) (fun l => Tm (b l))
        (fun l _ => h3 _ (b l).2) P.2
    have hIH : ∀ l, ∑ k ∈ s, (c k * r k l) • Fk k = 0 := by
      intro l
      refine sum_liftP_eq_zero hL M ρ t he hC p hg.init s (fun k => c k * r k l) (fun k => (φ k).1) (fun k => (d k).1)
        (fun k hk => (hv k hk).1) (fun x hx => ?_) P.1 F hF
      have hV : ∑ k ∈ s, (c k * famProd p (φ k).1 x) • v k = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        funext y
        rw [Finset.sum_apply]
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply]
        rw [Finset.sum_congr rfl fun k hk => by rw [hv' k hk]]
        by_cases hy : IsHalf e y
        · have := hsum (x, y) ⟨hx, hy⟩
          rw [← this]
          refine Finset.sum_congr rfl fun k _ => ?_
          show _ = c k * (famProd p (φ k).1 x * (φ k).2 y)
          ring
        · refine Finset.sum_eq_zero fun k hk => ?_
          have : (φ k).2 y = 0 := by
            by_contra h0
            exact hy ((hmem k hk).1 y h0)
          rw [this, mul_zero]
      have := congrArg (fun z => b.repr z l) hV
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
        map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [r]
      ring
    show ∑ k ∈ s, c k • liftA W M a (W.fock a.pair (d k).2 P.2) (Fk k) = 0
    calc ∑ k ∈ s, c k • liftA W M a (W.fock a.pair (d k).2 P.2) (Fk k)
        = ∑ k ∈ s, ∑ l ∈ Ls, (c k * r k l) • liftA W M a (g l) (Fk k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [hstep k hk, liftA_sum_datum M hg.last Ls (r k) g (Fk k) fun l _ => hconv l k hk, Finset.smul_sum]
          simp only [smul_smul]
      _ = ∑ l ∈ Ls, liftA W M a (g l) (∑ k ∈ s, (c k * r k l) • Fk k) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [liftA_sum_form M a (g l) s _ Fk fun k hk => hconv l k hk]
      _ = 0 := by
          refine Finset.sum_eq_zero fun l _ => ?_
          rw [hIH l, liftA_zero_form]

theorem liftT_tensE_expand (M : Vol G) {X Y : Node} (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ : TotT G p) (F : Fn G X) :
    liftT W M p (tensE W p Q τ) F =
      ∑ P ∈ (Q.mapDomain fun P => restrictPol P p).support, (Q.mapDomain fun P => restrictPol P p) P •
        ∑ d ∈ τ.support, τ d • liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) F := by
  unfold tensE tensT
  rw [Finsupp.sum, liftT_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finsupp.sum, liftT_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [liftT_single, mul_smul]

theorem liftT_tensE_eq_of_famProd : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ₁ τ₂ : TotT G p) (φ₁ φ₂ : PureT G p → PureT G p), (∀ d ∈ τ₁.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₁ d) d) → (∀ d ∈ τ₂.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₂ d) d) → (∀ x : GlobalTheory.FlipRun.ArgT G p, GlobalTheory.FlipRun.HalfAll e p x → (τ₁.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₁ d) x) = τ₂.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₂ d) x) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₁) F = liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₂) F := by
  intro D T L sc G μ₀ hL W M ρ t e he hC X Y p hg τ₁ τ₂ φ₁ φ₂ hv₁ hv₂ heq F hF Q
  classical
  rw [liftT_tensE_expand, liftT_tensE_expand]
  refine Finset.sum_congr rfl fun P _ => ?_
  congr 1
  have key := sum_liftP_eq_zero hL M ρ t he hC p hg (τ₁.support.disjSum τ₂.support)
    (Sum.elim (fun d => τ₁ d) fun d => -τ₂ d) (Sum.elim φ₁ φ₂) (Sum.elim id id)
    (by
      rintro (k | k) hk
      · exact hv₁ k (Finset.inl_mem_disjSum.1 hk)
      · exact hv₂ k (Finset.inr_mem_disjSum.1 hk))
    (fun x hx => by
      rw [Finset.sum_disjSum]
      have := heq x hx
      simp only [Finsupp.sum] at this
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, this, add_neg_cancel])
    P F hF
  rw [Finset.sum_disjSum] at key
  simp only [Sum.elim_inl, Sum.elim_inr, id, neg_smul, Finset.sum_neg_distrib] at key
  exact sub_eq_zero.1 ((sub_eq_add_neg _ _).trans key)

end GlobalTheory.FlipRun

end
