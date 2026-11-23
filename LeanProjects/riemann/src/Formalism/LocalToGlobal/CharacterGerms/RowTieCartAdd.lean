import Formalism.LocalToGlobal.CharacterGerms.RowTieCartFB

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section IntSec

variable {V : VF C} {τ : Type}

theorem IntS.mul {f g : MvPowerSeries τ C} (hf : IntS V f) (hg : IntS V g) : IntS V (f * g) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  refine VF.Ge.sum fun p _ => ?_
  have hp := (hf p.1).mul (hg p.2)
  simpa using hp

theorem IntS.one : IntS V (1 : MvPowerSeries τ C) := by
  intro μ
  rw [MvPowerSeries.coeff_one]
  split_ifs
  all_goals simp [VF.Ge]

theorem IntS.pow {f : MvPowerSeries τ C} (hf : IntS V f) (n : ℕ) : IntS V (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact IntS.one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem IntS.subst {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C}
    (hf : IntS V f) : IntS V (MvPowerSeries.subst a f) := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  intro μ
  rw [MvPowerSeries.coeff_subst hA]
  have hterm : ∀ d : σ →₀ ℕ,
      V.Ge 0 (MvPowerSeries.coeff d f • MvPowerSeries.coeff μ (d.prod fun s e => a s ^ e)) := by
    intro d
    have hp : IntS V (d.prod fun s e => a s ^ e) := by
      show IntS V (∏ s ∈ d.support, a s ^ d s)
      exact Finset.prod_induction _ (fun p => IntS V p) (fun _ _ hx hy => IntS.mul hx hy) IntS.one
        (fun s _ => IntS.pow (ha s) _)
    have h2 := (hf d).mul (hp μ)
    simpa [smul_eq_mul] using h2
  by_cases hfin : (Function.support fun d : σ →₀ ℕ =>
      MvPowerSeries.coeff d f • MvPowerSeries.coeff μ (d.prod fun s e => a s ^ e)).Finite
  · rw [finsum_eq_sum _ hfin]
    exact VF.Ge.sum fun d _ => hterm d
  · rw [finsum_of_infinite_support hfin]
    simp [VF.Ge]

theorem intS_ps {f : PowerSeries C} : IntS V f ↔ ∀ n, V.Ge 0 (PowerSeries.coeff n f) := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h μ
    have hμ : μ = Finsupp.single () (μ ()) := by
      ext
      simp [Finsupp.single_apply]
    rw [hμ]
    exact h (μ ())

end IntSec

section Kill

variable {dd : ℕ}

theorem subst_ev_kill (h : PS C 2 dd) (g : Fin 2) (a : Fin 2 → Pt C 1 dd) (hag : a g = 0)
    (hao : ∀ g', g' ≠ g → a g' = pt C dd 0) :
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd => (MvPowerSeries.X (1 - g, q.2) : PS C 2 dd)) (ev a h) =
      MvPowerSeries.rescale (fun s : Fin 2 × Fin dd => if s.1 = g then (0 : C) else 1) h := by
  have hbS : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => (MvPowerSeries.X (1 - g, q.2) : PS C 2 dd)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => MvPowerSeries.constantCoeff_X _
  have haS : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin dd => a p.1 p.2) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    by_cases hs : s.1 = g
    · rw [hs, hag]; simp
    · rw [hao _ hs]; exact MvPowerSeries.constantCoeff_X _
  unfold ev
  rw [MvPowerSeries.subst_comp_subst_apply haS hbS, MvPowerSeries.rescale_eq_subst]
  congr 1
  funext s
  by_cases hs : s.1 = g
  · have h1 : a s.1 s.2 = 0 := by rw [hs, hag]; rfl
    rw [h1, ← MvPowerSeries.coe_substAlgHom hbS, map_zero]
    simp [hs]
  · have h1 : a s.1 s.2 = MvPowerSeries.X ((0 : Fin 1), s.2) := by rw [hao _ hs]; rfl
    rw [h1, MvPowerSeries.subst_X hbS]
    have h2 : s = (1 - g, s.2) := Prod.ext (fin_two_eq_one_sub_of_ne' g s.1 hs) rfl
    simp only [Pi.smul_apply', if_neg hs, one_smul]
    rw [← h2]

theorem coeff_eval_second_zero (G : PS C 2 dd) (μ : Fin dd →₀ ℕ) :
    MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (ev (n := 1) ![pt C dd 0, 0] G) =
      MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 2), x)) G := by
  have hk := subst_ev_kill G 1 ![pt C dd 0, 0] rfl (by
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
    rfl)
  have hinj : Function.Injective (fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) :=
    fun a b h => snd_injective_fin_one (Prod.mk.inj (show (((1 : Fin 2) - 1, a.2) : Fin 2 × Fin dd) = ((1 : Fin 2) - 1, b.2) from h)).2
  have h1 := coeff_subst_rename_inj (C := C) (fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) hinj
    (ev (n := 1) ![pt C dd 0, 0] G) (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x))
  rw [hk, ← Finsupp.mapDomain_comp, MvPowerSeries.coeff_rescale] at h1
  rw [← h1]
  have h2 : ((fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) ∘ fun x : Fin dd => ((0 : Fin 1), x)) =
      fun x : Fin dd => ((0 : Fin 2), x) := by
    funext x
    rfl
  rw [h2]
  have h3 : ((μ.mapDomain fun x : Fin dd => ((0 : Fin 2), x)).prod
      fun s m => (if s.1 = 1 then (0 : C) else 1) ^ m) = 1 := by
    unfold Finsupp.prod
    apply Finset.prod_eq_one
    intro s hs
    have hs' := Finsupp.mapDomain_support hs
    rw [Finset.mem_image] at hs'
    obtain ⟨x, _, rfl⟩ := hs'
    show (if (0 : Fin 2) = 1 then (0 : C) else 1) ^ _ = 1
    rw [if_neg (by decide), one_pow]
  rw [h3, one_mul]

end Kill

section SgSec

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

theorem FBChart.raw_sg (v : Fin dd → C) : (Y.raw p).sg v = un1 (Y.sgP v) := by
  ext μ
  show -∑ i, v i * MvPowerSeries.coeff (μ.mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) +
      Finsupp.single ((1 : Fin 2), i) 1) Y.h =
    MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.sgP v)
  simp only [FBChart.sgP, map_neg, map_sum, MvPowerSeries.coeff_C_mul, coeff_eval_second_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [MvPowerSeries.coeff_pderiv, Finsupp.mapDomain_notin_range]
  · simp
  · rintro ⟨x, hx⟩
    simp at hx

end SgSec

section AddSec

variable {dd : ℕ}

theorem pts_eq_X : (fun p : Fin 2 × Fin dd => ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] p.1 p.2) = MvPowerSeries.X := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> first | rfl | simp [pt]

theorem addOf_pts (F : Fin dd → PS C 2 dd) (j : Fin dd) :
    addOf F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j = F j := by
  simp only [addOf, ev]
  rw [pts_eq_X, MvPowerSeries.subst_self]
  rfl

end AddSec

theorem addCvFB_of
    (hG : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
      (Y : FBChart C V O dd), GermISt Y) : AddCvFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p γ γ' hγ hγ'
  set ρ : Fin 2 × Fin dd → PowerSeries C := fun q => ![γ, γ'] q.1 q.2 with hρ
  have hρ0 : ∀ q, MvPowerSeries.constantCoeff (ρ q) = 0 := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact (hγ j).1
    · exact (hγ' j).1
  have hρI : ∀ q, IntS V (ρ q) := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact intS_ps.2 (hγ j).2
    · exact intS_ps.2 (hγ' j).2
  have hρS := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  set γ'' : Fin dd → PowerSeries C := fun j => MvPowerSeries.subst ρ (Y.B.G.F j) with hγ''
  have hγ''0 : ∀ j, MvPowerSeries.constantCoeff (γ'' j) = 0 := fun j =>
    constantCoeff_subst_zero hρ0 (Y.B.G.const j)
  have hγ''I : IsCv V γ'' := fun j => ⟨hγ''0 j, intS_ps.1 (IntS.subst hρ0 hρI (Y.intF j))⟩

  have hev : ∀ (a : Pt C 2 dd), (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f : PS C 1 dd,
      MvPowerSeries.subst ρ (ev ![a] f) = alongCv (fun j => MvPowerSeries.subst ρ (a j)) (un1 f) := by
    intro a ha f
    unfold alongCv
    rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => ha q.2) hρS,
      subst_singlePointUncurry (fun j => constantCoeff_subst_zero hρ0 (ha j))]
  have hp0 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 0 j)) = γ := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((0 : Fin 2), j)) = γ j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hp1 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 1 j)) = γ' := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((1 : Fin 2), j)) = γ' j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hpa : (fun j => MvPowerSeries.subst ρ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j)) = γ'' := by
    funext j
    rw [addOf_pts]
  have hc0 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 0 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hc1 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 1 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hca : ∀ j, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j) = 0 :=
    fun j => by rw [addOf_pts]; exact Y.B.G.const j
  refine ⟨γ'', hγ''I, ?_, ?_⟩
  · intro i
    have h := congrArg (MvPowerSeries.subst ρ) (Y.lg_add i)
    rw [← MvPowerSeries.coe_substAlgHom hρS, map_add, MvPowerSeries.coe_substAlgHom hρS, hev _ hca, hev _ hc0,
      hev _ hc1, hpa, hp0, hp1] at h
    exact h
  · intro v hv
    have hsg0 : MvPowerSeries.constantCoeff ((Y.raw p).sg v) = 0 := (Y.raw p).constantCoeff_sg (Y.raw_axis0 p) v
    refine ⟨?_, ?_⟩
    · rw [map_sub, map_sub]
      have e1 : PowerSeries.constantCoeff (alongCv γ'' ((Y.raw p).sg v)) = 0 := constantCoeff_subst_zero hγ''0 hsg0
      have e2 : PowerSeries.constantCoeff (alongCv γ ((Y.raw p).sg v)) = 0 :=
        constantCoeff_subst_zero (fun i => (hγ i).1) hsg0
      have e3 : PowerSeries.constantCoeff (alongCv γ' ((Y.raw p).sg v)) = 0 :=
        constantCoeff_subst_zero (fun i => (hγ' i).1) hsg0
      rw [e1, e2, e3]
      simp
    · have h := IntS.subst hρ0 hρI (hG C V O dd Y v hv)
      rw [← MvPowerSeries.coe_substAlgHom hρS, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hρS, hev _ hca,
        hev _ hc0, hev _ hc1, hpa, hp0, hp1, ← Y.raw_sg p v] at h
      exact intS_ps.1 h

end Formalism.L2.FormalSeriesBounds
