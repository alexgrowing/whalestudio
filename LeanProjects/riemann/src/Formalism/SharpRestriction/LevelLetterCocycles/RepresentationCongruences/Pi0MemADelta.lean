import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCoreT

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace TypesA

variable (W : LocWach PD LL O v n)

theorem lA_pow_smul {T : LocLat G Qp LL O} (k : ℕ) (x : W.DD T) :
    lA W ^ k • x = (PD.p ^ k) • x := by
  unfold lA
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

theorem natA_smul {T : LocLat G Qp LL O} (N : ℕ) (x : W.DD T) : ((N : ℕ) : LetA O n) • x = N • x :=
  Nat.cast_smul_eq_nsmul _ _ _

theorem pO_smul {T : LocLat G Qp LL O} (j : ℕ) (x : W.DD T) :
    ((PD.p : ℕ) : O) ^ j • x = lA W ^ j • x := by
  rw [lA_pow_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

theorem lA_pow_mem (j : ℕ) : lA W ^ j ∈ W.AΔ := by
  unfold lA
  rw [← Nat.cast_pow]
  exact natCast_mem _ _

include W in

theorem alg_inj : Function.Injective (algebraMap O LL) := by
  rw [injective_iff_map_eq_zero]
  intro d hd
  obtain ⟨e, he, hL⟩ := W.one_line
  haveI := W.one.L.free
  let β := Module.Free.chooseBasis O W.one.L.T
  have hkill : ∀ t : W.one.L.T, d • t = 0 := by
    intro t
    apply Subtype.ext
    show d • (t : W.one.V) = 0
    rw [← algebraMap_smul LL d (t : W.one.V), hd, zero_smul]
  have heT : e ∈ W.one.L.T := by rw [hL]; exact Submodule.mem_span_singleton_self e
  have hne : Nonempty (Module.Free.ChooseBasisIndex O W.one.L.T) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : (⟨e, heT⟩ : W.one.L.T) = 0 := β.repr.injective (Subsingleton.elim _ _)
    exact he (congrArg Subtype.val h0)
  obtain ⟨i⟩ := hne
  have := congrArg (fun t => β.repr t i) (hkill (β i))
  simpa using this

theorem delF_mul {g h : W.Gam} (hg : g ∈ W.DelF) (hh : h ∈ W.DelF) : g * h ∈ W.DelF := by
  rw [W.DelF_def] at hg hh ⊢
  obtain ⟨k, hk, hgk⟩ := hg
  obtain ⟨m, hm, hhm⟩ := hh
  refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  rw [mul_pow, pow_mul, hgk, one_pow, mul_comm k m, pow_mul, hhm, one_pow, one_mul]

theorem delF_inv {g : W.Gam} (hg : g ∈ W.DelF) : g⁻¹ ∈ W.DelF := by
  rw [W.DelF_def] at hg ⊢
  obtain ⟨k, hk, hgk⟩ := hg
  exact ⟨k, hk, by rw [inv_pow, hgk, inv_one]⟩

theorem pi0_mem_ADelta : W.π₀ ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀
  intro δ hδ
  funext i
  show W.γ₀ δ W.π₀₁ = W.π₀₁
  simp only [LocWach.π₀₁, map_add, map_sub, map_one, map_natCast, map_sum]
  congr 1
  refine Finset.sum_nbij' (δ * ·) (δ⁻¹ * ·) (fun g hg => delF_mul W hδ hg)
    (fun g hg => delF_mul W (delF_inv W hδ) hg) (fun g _ => by simp) (fun g _ => by simp) (fun g _ => ?_)
  rw [map_mul, AlgHom.mul_apply]

theorem NΔ_smul {T : LocLat G Qp LL O} {a : LetA O n} (ha : a ∈ W.AΔ) {y : W.DD T} (hy : y ∈ W.NΔ T) :
    a • y ∈ W.NΔ T := by
  have hy' : y ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ y = y := hy
  have ha' : ∀ δ ∈ W.DelF, W.γA δ a = a := ha
  show a • y ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (a • y) = a • y
  refine ⟨(W.N T).smul_mem a hy'.1, fun δ hδ => ?_⟩
  rw [← algebraMap_smul W.EE a y, W.γD_smul, W.γE_ext, hy'.2 δ hδ]
  have h := ha' δ hδ
  simp only [LocWach.γA] at h
  rw [h]

theorem map_smulA {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (a : LetA O n) (x : W.DD T₁) :
    W.map F (a • x) = a • W.map F x := by
  rw [← algebraMap_smul W.EE a x, map_smul, algebraMap_smul]

theorem map_NΔ {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hT₁ : IsCrys PD T₁.ρ) (hT₂ : IsCrys PD T₂.ρ)
    {y : W.DD T₁} (hy : y ∈ W.NΔ T₁) :
    W.map F y ∈ W.NΔ T₂ := by
  have hy' : y ∈ W.N T₁ ∧ ∀ δ ∈ W.DelF, W.γD T₁ δ y = y := hy
  show W.map F y ∈ W.N T₂ ∧ ∀ δ ∈ W.DelF, W.γD T₂ δ (W.map F y) = W.map F y
  exact ⟨W.map_N F hT₁ hT₂ y hy'.1, fun δ hδ => by rw [← W.map_γ, hy'.2 δ hδ]⟩

section Closure

variable {T : LocLat G Qp LL O}

theorem InFNc_add {c : ZMod n} {f : LetA O n} {x x' : W.DD T} (h : InFNc W T c f x)
    (h' : InFNc W T c f x') : InFNc W T c f (x + x') := by
  obtain ⟨y, hy, hyc, rfl⟩ := h
  obtain ⟨y', hy', hyc', rfl⟩ := h'
  exact ⟨y + y', add_mem hy hy', by rw [smul_add, hyc, hyc'], (smul_add f y y').symm⟩

theorem InFNc_neg {c : ZMod n} {f : LetA O n} {x : W.DD T} (h : InFNc W T c f x) :
    InFNc W T c f (-x) := by
  obtain ⟨y, hy, hyc, rfl⟩ := h
  exact ⟨-y, neg_mem hy, by rw [smul_neg, hyc], (smul_neg f y).symm⟩

theorem InFNc_smul {c : ZMod n} {f a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T} (h : InFNc W T c f x) :
    InFNc W T c f (a • x) := by
  obtain ⟨y, hy, hyc, rfl⟩ := h
  exact ⟨a • y, NΔ_smul W ha hy, by rw [smul_smul, mul_comm, ← smul_smul, hyc],
    by rw [smul_smul, smul_smul, mul_comm]⟩

theorem InFNc_one_smul {c : ZMod n} {f : LetA O n} {x : W.DD T} (hf : f ∈ W.AΔ) (h : InFNc W T c f x) :
    InFNc W T c 1 x := by
  obtain ⟨y, hy, hyc, rfl⟩ := h
  exact ⟨f • y, NΔ_smul W hf hy, by rw [smul_smul, mul_comm, ← smul_smul, hyc], (one_smul _ _).symm⟩

theorem Pp_smul {c : ZMod n} {e : ℕ} {a : LetA O n} (ha : a ∈ W.AΔ) {y : W.DD T} (hy : y ∈ Pp W T c e) :
    a • y ∈ Pp W T c e := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a * a', mul_mem ha ha', x, hx, by rw [mul_smul]⟩
  | zero => simpa using (Pp W T c e).zero_mem
  | add y₁ y₂ _ _ h₁ h₂ =>
    rw [smul_add]
    exact (Pp W T c e).add_mem h₁ h₂
  | neg y _ h =>
    rw [smul_neg]
    exact (Pp W T c e).neg_mem h

theorem inMultiple_add {c : ZMod n} {e : ℕ} {f : LetA O n} {x x' : W.DD T} (h : InFP W T c e f x)
    (h' : InFP W T c e f x') : InFP W T c e f (x + x') := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨y', hy', rfl⟩ := h'
  exact ⟨y + y', (Pp W T c e).add_mem hy hy', (smul_add f y y').symm⟩

theorem inMultiple_neg {c : ZMod n} {e : ℕ} {f : LetA O n} {x : W.DD T} (h : InFP W T c e f x) :
    InFP W T c e f (-x) := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨-y, (Pp W T c e).neg_mem hy, (smul_neg f y).symm⟩

theorem inMultiple_sub {c : ZMod n} {e : ℕ} {f : LetA O n} {x x' : W.DD T} (h : InFP W T c e f x)
    (h' : InFP W T c e f x') : InFP W T c e f (x - x') := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨y', hy', rfl⟩ := h'
  exact ⟨y - y', (Pp W T c e).sub_mem hy hy', (smul_sub f y y').symm⟩

theorem inMultiple_smul {c : ZMod n} {e : ℕ} {f a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T}
    (h : InFP W T c e f x) : InFP W T c e f (a • x) := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨a • y, Pp_smul W ha hy, by rw [smul_smul, smul_smul, mul_comm]⟩

theorem InI_zero {c : ZMod n} : InI W T c 0 := by
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (0 : W.DD T) = 0
    exact smul_zero _
  · show ∀ δ ∈ W.DelF, W.γD T δ 0 = 0
    intro δ _; exact map_zero _
  · rw [map_zero, sub_zero]
    exact ⟨0, zero_mem _, smul_zero _, (smul_zero _).symm⟩

theorem InI_add {c : ZMod n} {w w' : W.DD T} (h : InI W T c w) (h' : InI W T c w') :
    InI W T c (w + w') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  have h1 : (letE (O := O) c : LetA O n) • w = w := h1
  have h1' : (letE (O := O) c : LetA O n) • w' = w' := h1'
  have h2 : ∀ δ ∈ W.DelF, W.γD T δ w = w := h2
  have h2' : ∀ δ ∈ W.DelF, W.γD T δ w' = w' := h2'
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (w + w') = w + w'
    rw [smul_add, h1, h1']
  · show ∀ δ ∈ W.DelF, W.γD T δ (w + w') = w + w'
    intro δ hδ; rw [map_add, h2 δ hδ, h2' δ hδ]
  · have : W.γ T (w + w') - (w + w') = (W.γ T w - w) + (W.γ T w' - w') := by rw [map_add]; abel
    rw [this]; exact InFNc_add W h3 h3'

theorem InI_neg {c : ZMod n} {w : W.DD T} (h : InI W T c w) : InI W T c (-w) := by
  obtain ⟨h1, h2, h3⟩ := h
  have h1 : (letE (O := O) c : LetA O n) • w = w := h1
  have h2 : ∀ δ ∈ W.DelF, W.γD T δ w = w := h2
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (-w) = -w
    rw [smul_neg, h1]
  · show ∀ δ ∈ W.DelF, W.γD T δ (-w) = -w
    intro δ hδ; rw [map_neg, h2 δ hδ]
  · have : W.γ T (-w) - (-w) = -(W.γ T w - w) := by rw [map_neg]; abel
    rw [this]; exact InFNc_neg W h3

theorem InI_nat {c : ZMod n} (N : ℕ) {w : W.DD T} (h : InI W T c w) :
    InI W T c (((N : ℕ) : LetA O n) • w) := by
  obtain ⟨h1, h2, h3⟩ := h
  have h1 : (letE (O := O) c : LetA O n) • w = w := h1
  have h2 : ∀ δ ∈ W.DelF, W.γD T δ w = w := h2
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (((N : ℕ) : LetA O n) • w) = ((N : ℕ) : LetA O n) • w
    rw [smul_comm, h1]
  · show ∀ δ ∈ W.DelF, W.γD T δ (((N : ℕ) : LetA O n) • w) = ((N : ℕ) : LetA O n) • w
    intro δ hδ; rw [natA_smul, map_nsmul, h2 δ hδ]
  · have : W.γ T (((N : ℕ) : LetA O n) • w) - ((N : ℕ) : LetA O n) • w =
        ((N : ℕ) : LetA O n) • (W.γ T w - w) := by
      rw [natA_smul, natA_smul, map_nsmul, smul_sub]
    rw [this]; exact InFNc_smul W (natCast_mem _ _) h3

theorem InI_map {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hT₁ : IsCrys PD T₁.ρ) (hT₂ : IsCrys PD T₂.ρ)
    {c : ZMod n} {w : W.DD T₁}
    (h : InI W T₁ c w) : InI W T₂ c (W.map F w) := by
  obtain ⟨h1, h2, ⟨y, hy, hyc, hxy⟩⟩ := h
  have h1 : (letE (O := O) c : LetA O n) • w = w := h1
  have h2 : ∀ δ ∈ W.DelF, W.γD T₁ δ w = w := h2
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • W.map F w = W.map F w
    rw [← map_smulA, h1]
  · show ∀ δ ∈ W.DelF, W.γD T₂ δ (W.map F w) = W.map F w
    intro δ hδ; rw [← W.map_γ, h2 δ hδ]
  · refine ⟨W.map F y, map_NΔ W F hT₁ hT₂ hy, by rw [← map_smulA, hyc], ?_⟩
    show W.γD T₂ W.gam (W.map F w) - W.map F w = W.π₀ • W.map F y
    rw [← W.map_γ, ← map_sub, ← map_smulA, ← hxy]
    rfl

end Closure

section Rep

variable {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ} {b : Fin d → W.DD T}
  {sol : Fin d → ℕ → Fin d → LL}

theorem φA_pow_mem {a : LetA O n} (ha : a ∈ W.AΔ) (s : ℕ) : (W.φA ^ s) a ∈ W.AΔ := by
  induction s with
  | zero => simpa using ha
  | succ s ih =>
    have ih' : ∀ δ ∈ W.DelF, W.γA δ ((W.φA ^ s) a) = (W.φA ^ s) a := ih
    rw [pow_succ', AlgHom.mul_apply]
    show ∀ δ ∈ W.DelF, W.γA δ (W.φA ((W.φA ^ s) a)) = W.φA ((W.φA ^ s) a)
    intro δ hδ
    rw [← W.φA_γA, ih' δ hδ]

theorem ps_mem (s : ℕ) : ps W s ∈ W.AΔ := by
  have hq : qA W ∈ W.AΔ := by
    unfold qA lA
    exact add_mem (pi0_mem_ADelta W) (natCast_mem _ _)
  exact φA_pow_mem W hq s

theorem Ps_mem {x : LetA O n} (hx : x ∈ Ps W) : x ∈ W.AΔ := by
  have key : Ps W ≤ W.AΔ.toSubmonoid := by
    unfold Ps
    rw [Submonoid.closure_le]
    rintro _ ⟨s, rfl⟩
    exact ps_mem W s
  exact key hx

theorem RepVV_congr {x x' : W.DD T} {f f' : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f)
    (hx : x = x') (hf : ∀ k, f k = f' k) : RepVV W T c' e M Λ b sol x' f' := by
  subst hx
  have hff : f = f' := funext hf
  subst hff
  exact h

theorem IsHorTr_smul {R κ : ℕ} {k : Fin d} {x : W.DD T} (j : ℕ) (h : IsHorTr W T b sol R κ k x) :
    IsHorTr W T b sol R (κ + j) k (lA W ^ j • x) := by
  obtain ⟨y, hy, rfl⟩ := h
  refine ⟨fun r m => ((PD.p : ℕ) : O) ^ j * y r m, fun r hr m => ?_, ?_⟩
  · rw [map_mul, hy r hr m, map_pow, map_natCast, pow_add]
    ring
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Formalism.MainNotions.LiftingTheory.vecB, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul, pO_smul, smul_comm (W.π₀ ^ r) (lA W ^ j)]

theorem IsHorTr_unique {R κ : ℕ} {k : Fin d} {x x' : W.DD T} (h : IsHorTr W T b sol R κ k x)
    (h' : IsHorTr W T b sol R κ k x') : x = x' := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨y', hy', rfl⟩ := h'
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.1 hr
  have hyy : y r = y' r := funext fun m => alg_inj W ((hy r hr' m).trans (hy' r hr' m).symm)
  rw [hyy]

theorem RepVV_nat (N : ℕ) {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (((N : ℕ) : LetA O n) • x) (fun k => ((N : ℕ) : W.EE) * f k) := by
  obtain ⟨κ, κ', H, a, hH, ha, hP⟩ := h
  refine ⟨κ, κ', H, fun k => ((N : ℕ) : LetA O n) * a k, hH,
    fun k => ⟨mul_mem (natCast_mem _ _) (ha k).1, ?_⟩, ?_⟩
  · rw [map_mul, map_natCast, ← (ha k).2]
    ring
  · have hs : ∑ k, (((N : ℕ) : LetA O n) * a k) • ((W.φD T) ^ e) (H k) =
        ((N : ℕ) : LetA O n) • ∑ k, a k • ((W.φD T) ^ e) (H k) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_smul _ _ _
    rw [hs]
    have key : lA W ^ κ' • (lA W ^ κ • Λ • (((N : ℕ) : LetA O n) • x) -
          ((N : ℕ) : LetA O n) • ∑ k, a k • ((W.φD T) ^ e) (H k)) =
        ((N : ℕ) : LetA O n) • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (H k))) := by
      simp only [smul_add, smul_sub, smul_neg, smul_smul, sub_neg_eq_add, neg_sub, neg_add_rev, neg_neg]
      ring_nf
      try abel
    rw [key]
    exact inMultiple_smul W (natCast_mem _ _) hP

theorem RepVV_neg {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (-x) (fun k => -f k) := by
  obtain ⟨κ, κ', H, a, hH, ha, hP⟩ := h
  refine ⟨κ, κ', H, fun k => -a k, hH,
    fun k => ⟨neg_mem (ha k).1, by rw [mul_neg, map_neg, (ha k).2]⟩, ?_⟩
  have hs : ∑ k, (-a k) • ((W.φD T) ^ e) (H k) = -∑ k, a k • ((W.φD T) ^ e) (H k) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => neg_smul _ _
  rw [hs]
  have key : lA W ^ κ' • (lA W ^ κ • Λ • (-x) - -∑ k, a k • ((W.φD T) ^ e) (H k)) =
      -(lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (H k))) := by
    simp only [smul_add, smul_sub, smul_neg, smul_smul, sub_neg_eq_add, neg_sub, neg_add_rev, neg_neg]
    ring_nf
    try abel
  rw [key]
  exact inMultiple_neg W hP

theorem RepVV_add {x x' : W.DD T} {f f' : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f)
    (h' : RepVV W T c' e M Λ b sol x' f') :
    RepVV W T c' e M Λ b sol (x + x') (fun k => f k + f' k) := by
  obtain ⟨κ₁, κ₁', H₁, a₁, hH₁, ha₁, hP₁⟩ := h
  obtain ⟨κ₂, κ₂', H₂, a₂, hH₂, ha₂, hP₂⟩ := h'
  have hHeq : ∀ k, lA W ^ κ₂ • H₁ k = lA W ^ κ₁ • H₂ k := fun k => by
    have e1 := IsHorTr_smul W κ₂ (hH₁ k)
    have e2 := IsHorTr_smul W κ₁ (hH₂ k)
    rw [add_comm κ₂ κ₁] at e2
    exact IsHorTr_unique W e1 e2
  refine ⟨κ₁ + κ₂, κ₁' + κ₂', fun k => lA W ^ κ₂ • H₁ k, fun k => a₁ k + a₂ k,
    fun k => IsHorTr_smul W κ₂ (hH₁ k),
    fun k => ⟨add_mem (ha₁ k).1 (ha₂ k).1, by rw [mul_add, map_add, (ha₁ k).2, (ha₂ k).2]⟩, ?_⟩
  have hφ : ∀ (j : ℕ) (z : W.DD T), ((W.φD T) ^ e) (lA W ^ j • z) = lA W ^ j • ((W.φD T) ^ e) z := by
    intro j z
    rw [lA_pow_smul, lA_pow_smul, map_nsmul]
  have hsum : ∑ k, (a₁ k + a₂ k) • ((W.φD T) ^ e) (lA W ^ κ₂ • H₁ k) =
      lA W ^ κ₂ • ∑ k, a₁ k • ((W.φD T) ^ e) (H₁ k) + lA W ^ κ₁ • ∑ k, a₂ k • ((W.φD T) ^ e) (H₂ k) := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [add_smul]
    congr 1
    · rw [hφ, smul_comm]
    · rw [hHeq k, hφ, smul_comm]
  rw [hsum]
  have key : lA W ^ (κ₁' + κ₂') • (lA W ^ (κ₁ + κ₂) • Λ • (x + x') -
        (lA W ^ κ₂ • ∑ k, a₁ k • ((W.φD T) ^ e) (H₁ k) + lA W ^ κ₁ • ∑ k, a₂ k • ((W.φD T) ^ e) (H₂ k))) =
      lA W ^ (κ₂' + κ₂) • (lA W ^ κ₁' • (lA W ^ κ₁ • Λ • x - ∑ k, a₁ k • ((W.φD T) ^ e) (H₁ k))) +
      lA W ^ (κ₁' + κ₁) • (lA W ^ κ₂' • (lA W ^ κ₂ • Λ • x' - ∑ k, a₂ k • ((W.φD T) ^ e) (H₂ k))) := by
    simp only [smul_add, smul_sub, smul_neg, smul_smul, sub_neg_eq_add, neg_sub, neg_add_rev, neg_neg]
    ring_nf
    try abel
  rw [key]
  exact inMultiple_add W (inMultiple_smul W (lA_pow_mem W _) hP₁) (inMultiple_smul W (lA_pow_mem W _) hP₂)

end Rep

end TypesA

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

theorem LiftsAtT.mono {f : W.EE} {e e' : ℕ} (he : e ≤ e') (h : LiftsAtT W A F c b sol k₀ f e) :
    LiftsAtT W A F c b sol k₀ f e' := by
  unfold LiftsAtT at h ⊢
  obtain ⟨w₁, z, hw, ⟨Λ', hΛ', hΛw⟩, hP, hz, hR⟩ := h
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = PD.p ^ (e' - e) := ⟨_, rfl⟩
  refine ⟨((N : ℕ) : LetA O n) • w₁, ((N : ℕ) : LetA O n) • z, TypesA.InI_nat W N hw, ⟨Λ', hΛ', ?_⟩, ?_,
    TypesA.InFNc_smul W (natCast_mem _ _) hz, ?_⟩
  · rw [smul_comm]
    exact TypesA.InFNc_smul W (natCast_mem _ _) hΛw
  · rw [TypesA.map_smulA, smul_comm]
    exact TypesA.inMultiple_smul W (natCast_mem _ _) hP
  · rw [TypesA.map_smulA, ← smul_sub]
    refine TypesA.RepVV_congr W (TypesA.RepVV_nat W N hR) rfl fun k => ?_
    rcases eq_or_ne k k₀ with rfl | hk
    · rw [if_pos rfl, if_pos rfl]
      unfold lE
      rw [hN, Nat.cast_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel he]
    · rw [if_neg hk, if_neg hk, mul_zero]

theorem LiftsAtT.add {f f' : W.EE} {e : ℕ} (h : LiftsAtT W A F c b sol k₀ f e)
    (h' : LiftsAtT W A F c b sol k₀ f' e) : LiftsAtT W A F c b sol k₀ (f + f') e := by
  unfold LiftsAtT at h h' ⊢
  obtain ⟨w₁, z, hw, ⟨Λ₁, hΛ₁, hΛw₁⟩, hP, hz, hR⟩ := h
  obtain ⟨w₁', z', hw', ⟨Λ₂, hΛ₂, hΛw₂⟩, hP', hz', hR'⟩ := h'
  refine ⟨w₁ + w₁', z + z', TypesA.InI_add W hw hw', ⟨Λ₁ * Λ₂, mul_mem hΛ₁ hΛ₂, ?_⟩, ?_,
    TypesA.InFNc_add W hz hz', ?_⟩
  · have hsplit : (Λ₁ * Λ₂) • (w₁ + w₁') = Λ₂ • (Λ₁ • w₁) + Λ₁ • (Λ₂ • w₁') := by
      rw [smul_add, mul_smul, mul_smul, smul_comm Λ₁ Λ₂ w₁]
    rw [hsplit]
    exact TypesA.InFNc_add W (TypesA.InFNc_smul W (TypesA.Ps_mem W hΛ₂) hΛw₁)
      (TypesA.InFNc_smul W (TypesA.Ps_mem W hΛ₁) hΛw₂)
  · rw [map_add, smul_add]
    exact TypesA.inMultiple_add W hP hP'
  · refine TypesA.RepVV_congr W (TypesA.RepVV_add W hR hR') (by rw [map_add]; abel) fun k => ?_
    rcases eq_or_ne k k₀ with rfl | hk
    · rw [if_pos rfl, if_pos rfl, if_pos rfl, mul_add]
    · rw [if_neg hk, if_neg hk, if_neg hk, add_zero]

end Formalism.MainNotions.N.FrobeniusPowerSeries
