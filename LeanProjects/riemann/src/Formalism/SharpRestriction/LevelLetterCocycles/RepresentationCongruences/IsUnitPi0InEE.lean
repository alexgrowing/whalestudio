import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsBis
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.TC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem inFr_congr {a : ZMod n} {num num' den den' : LetA O n} {f : W.EE} (h1 : num = num') (h2 : den = den')
    (h : InFr W a num den f) : InFr W a num' den' f := by
  subst h1 h2
  exact h

theorem inFr_mulO {a : ZMod n} {num den : LetA O n} {f : W.EE} (x : O) (h : InFr W a num den f) :
    InFr W a num den (f * algebraMap O W.EE x) := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨u * algebraMap O (LetA O n) x, mul_mem hu (Subalgebra.algebraMap_mem _ x), ?_⟩
  rw [← mul_assoc, h, IsScalarTower.algebraMap_apply O (LetA O n) W.EE x, ← map_mul, mul_assoc]

theorem lE_eq (κ : ℕ) : lE W κ = algebraMap (LetA O n) W.EE (lA W ^ κ) := by
  unfold lE lA
  rw [map_pow, map_natCast]

theorem inFr_lE {a : ZMod n} {num den : LetA O n} {f : W.EE} (κ : ℕ) (h : InFr W a num den f) :
    InFr W a num den (lE W κ * f) := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨u * lA W ^ κ, mul_mem hu (pow_mem (by unfold lA; exact natCast_mem _ _) _), ?_⟩
  rw [lE_eq, mul_left_comm, h, ← map_mul]
  congr 1
  ring

theorem inFr_den {a : ZMod n} {num den den' R : LetA O n} {f : W.EE} (hR : R ∈ W.AΔ) (he : den' = den * R)
    (h : InFr W a num den f) : InFr W a num den' f := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨u * R, mul_mem hu hR, ?_⟩
  rw [he, map_mul, mul_comm (algebraMap (LetA O n) W.EE den), mul_assoc, h, ← map_mul]
  congr 1
  ring

theorem inFr_div {a : ZMod n} {num den : LetA O n} {y : W.EE}
    (hu : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    (h : InFr W a (W.π₀ * num) den (algebraMap (LetA O n) W.EE W.π₀ * y)) : InFr W a num den y := by
  obtain ⟨u, hu', h⟩ := h
  refine ⟨u, hu', ?_⟩
  apply hu.mul_left_cancel
  simp only [map_mul] at h ⊢
  linear_combination h

theorem dv_eq_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T e b c₀ = ∑ k, c₀ k • dv W T e b (Pi.single k 1) := by
  unfold dv
  simp only [Finset.smul_sum, Pi.single_apply, ite_smul, one_smul, zero_smul, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem lam_mem_Ps (A : ArcP n) (a : ZMod n) (e : ℕ) : abelian₂ W A a e ∈ Ps W := by
  unfold abelian₂ Ps
  exact Submonoid.prod_mem _ fun s _ => Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_range_self s)) _

theorem prod_range_ite (ell : ℕ) (Si : Finset ℕ) (hsub : Si ⊆ Finset.range ell) (m : ℕ → ℕ) :
    ∏ s ∈ Finset.range ell, ps W s ^ (if s ∈ Si then m s else 0) = ∏ s ∈ Si, ps W s ^ m s := by
  have e : ∀ s, ps W s ^ (if s ∈ Si then m s else 0) = if s ∈ Si then ps W s ^ m s else 1 := by
    intro s
    split_ifs <;> simp
  rw [Finset.prod_congr rfl fun s _ => e s, Finset.prod_ite_mem, Finset.inter_eq_right.2 hsub]

theorem num0 (ell : ℕ) (Si : Finset ℕ) (m : ℕ → ℕ) :
    ∏ t ∈ Finset.range ell, ps W t ^ (-(((if t ∈ Si then m t else 0 : ℕ)) : ℤ)).toNat = 1 := by
  refine Finset.prod_eq_one fun t _ => ?_
  split_ifs <;> simp

theorem den0 (ell : ℕ) (Si : Finset ℕ) (m : ℕ → ℕ) :
    ∏ t ∈ Finset.range ell, ps W t ^ (-(-(((if t ∈ Si then m t else 0 : ℕ)) : ℤ))).toNat =
      ∏ t ∈ Finset.range ell, ps W t ^ (if t ∈ Si then m t else 0) := by
  refine Finset.prod_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem numS (ell : ℕ) (Si : Finset ℕ) (m : ℕ → ℕ) {s : ℕ} (hs : s < ell) (K : ℕ) :
    ∏ t ∈ Finset.range ell, ps W t ^
      (if t = s then (K : ℤ) else -(((if t ∈ Si then m t else 0 : ℕ)) : ℤ)).toNat = ps W s ^ K := by
  rw [Finset.prod_eq_single s (fun t _ ht => by rw [if_neg ht]; split_ifs <;> simp)
    (fun h => absurd (Finset.mem_range.2 hs) h)]
  simp

theorem denS (ell : ℕ) (Si : Finset ℕ) (m : ℕ → ℕ) {s : ℕ} (hsSi : s ∉ Si) (K : ℕ) :
    ∏ t ∈ Finset.range ell, ps W t ^
      (-(if t = s then (K : ℤ) else -(((if t ∈ Si then m t else 0 : ℕ)) : ℤ))).toNat =
      ∏ t ∈ Finset.range ell, ps W t ^ (if t ∈ Si then m t else 0) := by
  refine Finset.prod_congr rfl fun t _ => ?_
  by_cases ht : t = s
  · subst ht
    simp [hsSi]
  · rw [if_neg ht, neg_neg]
    split_ifs <;> simp

theorem up_le_Hs (A : ArcP n) (hA : A.OK) {c : ZMod n} (hc : c ∈ A.cuts) {s bs : ℕ} (hs : s < A.len c)
    (hty : A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs) : bs ≤ A.Hs c (A.len c) s := by
  obtain ⟨-, -, hcut, -, -, -, -, hthick, hlast⟩ := hA
  obtain ⟨hl1, -, hcm, -⟩ := hcut c hc
  unfold ArcP.Hs
  have hnt : A.ty (c - (s : ZMod n)) ≠ Formalism.MainNotions.LocalTheoryWindows.LT.thin := by
    rw [hty]
    exact fun h => by cases h
  have hpos : c - ((A.len c : ℕ) : ZMod n) + (((A.len c - s : ℕ)) : ZMod n) = c - (s : ZMod n) := by
    rw [Nat.cast_sub hs.le]
    ring
  split_ifs with h
  · rcases h with h | h
    · exact absurd h hnt
    · rcases hlast with hl | ⟨hj, -, hG⟩
      · exfalso
        have := hl _ hcm (A.len c - s) (by omega) h
        rw [hpos] at this
        exact hnt this
      · have hk : A.len c - s = 1 := by omega
        rw [hk, Nat.cast_one] at hpos
        have := hG _ hcm
        rw [hpos, hty] at this
        simp only [Formalism.MainNotions.LocalTheoryWindows.LT.size] at this
        omega
  · have := hthick (c - (s : ZMod n)) (by rw [hty]; rfl)
    rw [hty] at this
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.size] at this
    omega

theorem den_dvd_Lam (A : ArcP n) (hA : A.OK) {c : ZMod n} (hc : c ∈ A.cuts) (Si : Finset ℕ)
    (hSi : ∀ s ∈ Si, s < A.len c ∧ ∃ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs) (m : ℕ → ℕ)
    (hm : ∀ s ∈ Si, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs → m s = bs) :
    ∃ R ∈ W.AΔ, abelian₂ W A c (A.len c) = (∏ s ∈ Si, ps W s ^ m s) * R := by
  have hsub : Si ⊆ Finset.range (A.len c) := fun s hs => Finset.mem_range.2 (hSi s hs).1
  have hle : ∀ s ∈ Finset.range (A.len c), (if s ∈ Si then m s else 0) ≤ A.Hs c (A.len c) s := by
    intro s hs
    split_ifs with h
    · obtain ⟨hlt, bs, hbs⟩ := (hSi s h)
      rw [hm s h bs hbs]
      exact up_le_Hs A hA hc hlt hbs
    · exact Nat.zero_le _
  have hps : ∀ s, ps W s ∈ W.AΔ := fun s => by
    first
    | exact TypesA.ps_mem W s
    | exact TypesA.ps_mem s
  refine ⟨∏ s ∈ Finset.range (A.len c), ps W s ^ (A.Hs c (A.len c) s - (if s ∈ Si then m s else 0)),
    prod_mem fun s _ => pow_mem (hps s) _, ?_⟩
  rw [← prod_range_ite W (A.len c) Si hsub m, ← Finset.prod_mul_distrib]
  unfold abelian₂
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [← pow_add, Nat.add_sub_cancel' (hle s hs)]

theorem isUnit_pi0_in_EE (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T : LocLat G Qp LL O}
    (hT : IsCrys PD T.ρ) : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
  obtain ⟨hbij, hs, hp2⟩ := hcase
  have h9 := hP9 T hT hs hp2
  have hfr : Module.finrank K₀ K = 1 :=
    (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hbij).finrank_eq.symm.trans (Module.finrank_self K₀)
  have hR : GS.RD W := by
    first
    | exact GS.rd_of W (h9.2.2 hfr).1
    | exact GS.rd_of (h9.2.2 hfr).1
  first
  | exact GS.isUnit_π₀ W hR
  | exact GS.isUnit_π₀ hR

section Main

variable [FiniteDimensional Qp LL]

variable (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

theorem C_typeT_of (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hSec : ArcSecMapCoreT W) (hGL : ArcGamLiftCoreT W) (hFL : ArcFilLowCoreT W)
    (hArc : ArcCore W) (hW₁ : Win W A T₁) (hW₂ : Win W A T₂)
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol)
    (Si : Finset ℕ) (hSi : ∀ s ∈ Si, s < A.len c ∧ ∃ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O) (s₀ : ℕ)
    (hlt : ∀ s ∈ Si, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dvO W T₁ (A.len c) b₁ c₁ ∈ FilS W T₁ c s bs)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ s₀) • dv W T₂ (A.len c) b (Pi.single k₀ 1))
    (f : W.EE) (hf : InFr W c 1 (∏ s ∈ Si, ps W s ^ (match A.ty (c - (s : ZMod n)) with
        | .up bs => bs | _ => 0)) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x))
    (hup : ∀ s < A.len c, s ∉ Si → ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ A.η) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    LiftsAtT W A F c b sol k₀ f (s₀ + A.σ PD.p) := by
  classical
  have hjl := hA.2.2.2.1 c hc
  have hSec' := hSec hcase hl A hA c hc (A.len c) hjl le_rfl
  have hGL' := hGL hcase hl A hA c hc (A.len c) hjl le_rfl
  have hFL' := hFL hcase hl A hA c hc (A.len c) hjl le_rfl
  simp only [sub_add_cancel] at hSec' hGL' hFL'

  let m : ℕ → ℕ := fun s => match A.ty (c - (s : ZMod n)) with | .up bs => bs | _ => 0
  have hm : ∀ s ∈ Si, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs → m s = bs := by
    intro s _ bs h
    simp only [m, h]
  have hsub : Si ⊆ Finset.range (A.len c) := fun s hs => Finset.mem_range.2 (hSi s hs).1
  have hdenE : ∏ t ∈ Finset.range (A.len c), ps W t ^ (if t ∈ Si then m t else 0) = ∏ s ∈ Si, ps W s ^ m s :=
    prod_range_ite W _ Si hsub m
  have hf' : InFr W c 1 (∏ s ∈ Si, ps W s ^ m s) f := hf
  obtain ⟨R, hR, hΛ⟩ := den_dvd_Lam W A hA hc Si hSi m hm

  have hu := isUnit_pi0_in_EE W hcase hP9 hW₁.1
  obtain ⟨U, hU⟩ := hu

  let α₀ : ℕ → ℤ := fun t => -(((if t ∈ Si then m t else 0 : ℕ)) : ℤ)
  have hf₀ : InId W c (A.len c) α₀ f :=
    inFr_congr W (num0 W _ Si m).symm ((den0 W _ Si m).trans hdenE).symm hf'
  have hg₀ := (gamma_fraction_in_ideal W hcase hP9 c (A.len c) α₀ f hf₀).2
  let f₂ : W.EE := ((U⁻¹ : W.EEˣ) : W.EE) * (W.γE W.gam f - f)
  have hγf : W.γE W.gam f - f = algebraMap (LetA O n) W.EE W.π₀ * f₂ := by
    simp only [f₂, ← hU, Units.mul_inv_cancel_left]
  have hf₂ : InFr W c 1 (∏ s ∈ Si, ps W s ^ m s) f₂ := by
    refine inFr_div W (hU ▸ U.isUnit) ?_
    rw [← hγf]
    exact inFr_congr W (congrArg (W.π₀ * ·) (num0 W _ Si m)) ((den0 W _ Si m).trans hdenE) hg₀
  have hfΛ : ∀ x : O, InFr W c 1 (abelian₂ W A c (A.len c)) (f * algebraMap O W.EE x) :=
    fun x => inFr_den W hR hΛ (inFr_mulO W x hf')
  have hf₂Λ : ∀ x : O, InFr W c 1 (abelian₂ W A c (A.len c)) (f₂ * algebraMap O W.EE x) :=
    fun x => inFr_den W hR hΛ (inFr_mulO W x hf₂)

  have mono : ∀ (s κ : ℕ) (α : ℕ → ℤ), InId W c (A.len c) α (lE W κ * f₂) →
      dvO W T₁ (A.len c) b₁ c₁ ∈ FilS W T₁ c s (-(α s)) →
      ∃ κ : ℕ, SecIn W c (A.len c) (fun α c₀ => dvO W T₁ (A.len c) b₁ c₀ ∈ FilS W T₁ c s (-(α s)))
        (fun k => lE W κ * (f₂ * algebraMap O W.EE (c₁ k))) := fun s κ α h1 h2 =>
    ⟨κ, 1, fun _ => lE W κ * f₂, fun _ => c₁, fun _ => α, fun _ => ⟨h1, h2⟩, fun k => by simp [mul_assoc]⟩
  have gen : ∀ (s : ℕ), s < A.len c → s ∉ Si → ∀ (K κ : ℕ) (x : O),
      InFr W c (ps W s ^ K) (∏ s' ∈ Si, ps W s' ^ m s')
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x) →
      dvO W T₁ (A.len c) b₁ c₁ ∈ FilS W T₁ c s (-(K : ℤ)) →
      ∃ κ : ℕ, SecIn W c (A.len c) (fun α c₀ => dvO W T₁ (A.len c) b₁ c₀ ∈ FilS W T₁ c s (-(α s)))
        (fun k => lE W κ * (f₂ * algebraMap O W.EE (c₁ k))) := by
    intro s hs hsSi K κ x hy hfil
    let α : ℕ → ℤ := fun t => if t = s then (K : ℤ) else -(((if t ∈ Si then m t else 0 : ℕ)) : ℤ)
    have hyα : InId W c (A.len c) α (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x) :=
      inFr_congr W (numS W _ Si m hs K).symm ((denS W _ Si m hsSi K).trans hdenE).symm hy
    have hg := (gamma_fraction_in_ideal W hcase hP9 c (A.len c) α _ hyα).2
    have e1 : W.γE W.gam (lE W κ) = lE W κ := by simp [lE]
    have e2 : W.γE W.gam (algebraMap (LetA O n) W.EE (letE c)) = algebraMap (LetA O n) W.EE (letE c) := by
      rw [GS.γE_ι, GS.γA_letE]
    have e3 : W.γE W.gam (algebraMap O W.EE x) = algebraMap O W.EE x := AlgHom.commutes _ x
    have hγy : W.γE W.gam (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x) -
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x) =
        algebraMap (LetA O n) W.EE W.π₀ * (lE W κ * f₂) := by
      rw [map_sub, map_mul, map_mul, e1, e2, e3]
      linear_combination (lE W κ) * hγf
    rw [hγy] at hg
    have h2 : InFr W c (ps W s ^ K) (∏ s' ∈ Si, ps W s' ^ m s') (lE W κ * f₂) :=
      inFr_div W (hU ▸ U.isUnit)
        (inFr_congr W (congrArg (W.π₀ * ·) (numS W _ Si m hs K)) ((denS W _ Si m hsSi K).trans hdenE) hg)
    refine mono s κ α (inFr_congr W (numS W _ Si m hs K).symm ((denS W _ Si m hsSi K).trans hdenE).symm h2) ?_
    have : α s = (K : ℤ) := by simp [α]
    rw [this]
    exact hfil
  have hlev : ∀ s < A.len c, ∃ κ : ℕ, SecIn W c (A.len c)
      (fun α c₀ => dvO W T₁ (A.len c) b₁ c₀ ∈ FilS W T₁ c s (-(α s)))
      (fun k => lE W κ * (f₂ * algebraMap O W.EE (c₁ k))) := by
    intro s hs
    by_cases hsSi : s ∈ Si
    · obtain ⟨-, bs, hty⟩ := hSi s hsSi
      refine mono s 0 α₀ ?_ ?_
      · have e : lE W 0 * f₂ = f₂ := by simp [lE]
        rw [e]
        exact inFr_congr W (num0 W _ Si m).symm ((den0 W _ Si m).trans hdenE).symm hf₂
      · have e : -(α₀ s) = (bs : ℤ) := by simp [α₀, hsSi, hm s hsSi bs hty]
        rw [e]
        exact hlt s hsSi bs hty
    · have hth := hthick s hs
      have hfil := (hFL' T₁ hW₁ d₁ b₁ sol₁ hb₁ c₁ s hs).1
      cases hty : A.ty (c - (s : ZMod n)) with
      | thin => rw [hty] at hth; exact absurd hth (by simp [Formalism.MainNotions.LocalTheoryWindows.LT.thick])
      | up bs =>
        obtain ⟨κ, x, hκ⟩ := hup s hs hsSi bs hty
        refine gen s hs hsSi A.η κ x hκ (hfil _ fun a ha => ?_)
        rw [hty] at ha
        simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at ha
        omega
      | down bs =>
        obtain ⟨κ, x, hκ⟩ := hdown s hs bs hty
        have hok := hA.2.2.2.2.1 (c - (s : ZMod n))
        rw [hty] at hok
        simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok
        refine gen s hs hsSi (bs + A.S) κ x hκ (hfil _ fun a ha => ?_)
        rw [hty] at ha
        simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at ha
        push_cast
        omega

  have hγg : ∀ k, W.γE W.gam (f * algebraMap O W.EE (c₁ k)) - f * algebraMap O W.EE (c₁ k) =
      algebraMap (LetA O n) W.EE W.π₀ * (f₂ * algebraMap O W.EE (c₁ k)) := by
    intro k
    rw [map_mul, AlgHom.commutes]
    linear_combination (algebraMap O W.EE (c₁ k)) * hγf
  obtain ⟨w, hwI, hwP, hwR⟩ := hGL' T₁ hW₁ d₁ b₁ sol₁ hb₁
    (fun k => f * algebraMap O W.EE (c₁ k)) (fun k => hfΛ (c₁ k))
    ⟨fun k => f₂ * algebraMap O W.EE (c₁ k), hγg, fun k => hf₂Λ (c₁ k), hlev⟩

  obtain ⟨hFP, μ, hμ, hsec⟩ := hSec' T₁ T₂ F hW₁ hW₂ d₁ b₁ sol₁ hb₁ d b sol hb
  have hT₂ := hsec w (fun k => lE W (A.σ PD.p) * (f * algebraMap O W.EE (c₁ k))) hwP
    (fun k => inFr_lE W _ (hfΛ (c₁ k))) hwR

  have hAC := hArc hcase hl A hA c hc (A.len c) hjl le_rfl
  simp only [sub_add_cancel] at hAC
  obtain ⟨-, hAC⟩ := hAC
  have hPN₁ := (hAC T₁ hW₁).1
  have hli := ((hAC T₂ hW₂).2.2.2 d b sol hb).1.1

  have hcoef : ∀ k, ∑ m', c₁ m' * μ m' k = if k = k₀ then ((PD.p : ℕ) : O) ^ s₀ else 0 := by
    have e1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
        ∑ k, algebraMap O LL (∑ m', c₁ m' * μ m' k) • dv W T₂ (A.len c) b (Pi.single k 1) := by
      have h0 : dvO W T₁ (A.len c) b₁ c₁ =
          ∑ m', algebraMap O LL (c₁ m') • dv W T₁ (A.len c) b₁ (Pi.single m' 1) := dv_eq_sum W T₁ _ b₁ _
      have h2 : ∀ m', dvO W T₂ (A.len c) b (μ m') =
          ∑ k, algebraMap O LL (μ m' k) • dv W T₂ (A.len c) b (Pi.single k 1) := fun m' => dv_eq_sum W T₂ _ b _
      rw [h0, map_sum]
      simp_rw [map_smul, hμ, h2, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [map_sum, map_mul, Finset.sum_smul]
    have e2 : ((PD.p : LL) ^ s₀) • dv W T₂ (A.len c) b (Pi.single k₀ 1) =
        ∑ k, (if k = k₀ then (PD.p : LL) ^ s₀ else 0) • dv W T₂ (A.len c) b (Pi.single k 1) := by
      simp [ite_smul]
    have hz : ∑ k, (algebraMap O LL (∑ m', c₁ m' * μ m' k) - if k = k₀ then (PD.p : LL) ^ s₀ else 0) •
        dv W T₂ (A.len c) b (Pi.single k 1) = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, ← e1, ← e2, hpr, sub_self]
    intro k
    have hk := sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli
      (fun k => algebraMap O LL (∑ m', c₁ m' * μ m' k) - if k = k₀ then (PD.p : LL) ^ s₀ else 0) hz k)
    apply TypesA.alg_inj W
    rw [hk]
    split_ifs <;> simp
  refine ⟨w, 0, hwI, ⟨abelian₂ W A c (A.len c) * abelian₂ W A c (A.len c),
    Submonoid.mul_mem _ (lam_mem_Ps W A c _) (lam_mem_Ps W A c _), ?_⟩, ?_,
    ⟨0, (W.NΔ T₂).zero_mem, smul_zero _, (smul_zero _).symm⟩, ?_⟩
  · obtain ⟨y, hy, hyw⟩ := hwP
    rw [mul_smul, hyw, one_smul]
    exact hPN₁ y hy
  · have h := hFP _ hwP
    rwa [TypesA.map_smulA] at h
  · refine TypesA.RepVV_congr W hT₂ (sub_zero _).symm fun k => ?_
    have h1 : ∑ m', lE W (A.σ PD.p) * (f * algebraMap O W.EE (c₁ m')) * algebraMap O W.EE (μ m' k) =
        lE W (A.σ PD.p) * f * algebraMap O W.EE (∑ m', c₁ m' * μ m' k) := by
      rw [map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m' _ => by rw [map_mul]; ring
    rw [h1, hcoef k]
    split_ifs
    · simp only [lE, map_pow, map_natCast, pow_add]
      ring
    · simp

end Main

end Formalism.MainNotions.N.FrobeniusPowerSeries.TC
