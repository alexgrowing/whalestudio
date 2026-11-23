import Mathlib
import Formalism.DistinguishedUnitIdeals.ArcLiftOfLocalizationData

noncomputable section

namespace Formalism.ExponentWindows.E.IteratedPhiHomomorphisms

open PowerSeries

section gen
variable {O : Type} [CommRing O]
variable {V V' : Type} [AddCommGroup V] [Module (PowerSeries O) V] [AddCommGroup V']
  [Module (PowerSeries O) V']

theorem mem_sm {a : PowerSeries O} {S : Submodule (PowerSeries O) V} {v : V} :
    v ∈ sm a S ↔ ∃ u ∈ S, a • u = v := by
  simp [sm, Submodule.mem_map]

theorem mem_dv {a : PowerSeries O} {S : Submodule (PowerSeries O) V} {v : V} :
    v ∈ dv a S ↔ a • v ∈ S := by
  simp [dv, Submodule.mem_comap]

theorem sm_le (a : PowerSeries O) (S : Submodule (PowerSeries O) V) : sm a S ≤ S := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := mem_sm.1 hv
  exact S.smul_mem _ hu

theorem le_dv (a : PowerSeries O) (S : Submodule (PowerSeries O) V) : S ≤ dv a S := by
  intro v hv
  exact mem_dv.2 (S.smul_mem _ hv)

theorem lc_pow (B : Base O) (K : ℕ) : B.lc ^ K = C ((B.ℓ : O) ^ K) := by
  simp [Base.lc]

theorem lc_smul_mem (B : Base O) (K : ℕ) (D : AddSubgroup V) {d : V} (hd : d ∈ D) :
    B.lc ^ K • d ∈ D := by
  have : B.lc ^ K = ((B.ℓ ^ K : ℕ) : PowerSeries O) := by simp [Base.lc]
  rw [this, Nat.cast_smul_eq_nsmul]
  exact D.nsmul_mem hd _

theorem InSum.mono {D : AddSubgroup V} {S S' : Submodule (PowerSeries O) V} (h : S ≤ S') {e : V}
    (he : InSum D S e) : InSum D S' e := by
  obtain ⟨d, hd, hm⟩ := he
  exact ⟨d, hd, h hm⟩

theorem polyAct_map (f : V →ₗ[PowerSeries O] V') (γ : V →+ V) (γ' : V' →+ V')
    (hf : ∀ v, f (γ v) = γ' (f v)) (P : Polynomial O) (v : V) :
    f (polyAct P γ v) = polyAct P γ' (f v) := by
  have hit : ∀ (k : ℕ) (v : V), f ((⇑γ)^[k] v) = (⇑γ')^[k] (f v) := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih => intro v; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hf]
  unfold polyAct
  rw [Polynomial.sum_def, Polynomial.sum_def, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hit]

theorem polyAct_shift (γ : V →+ V) (U : Submodule (PowerSeries O) V) (hU : ∀ u ∈ U, γ u ∈ U)
    (P : Polynomial O) {w : V} (hw : γ w - w ∈ U) :
    polyAct P γ w - C (P.eval 1) • w ∈ U := by
  have hit : ∀ k : ℕ, (⇑γ)^[k] w - w ∈ U := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have : γ ((⇑γ)^[k] w) - w = γ ((⇑γ)^[k] w - w) + (γ w - w) := by
        rw [map_sub]; abel
      rw [this]
      exact U.add_mem (hU _ ih) hw
  unfold polyAct
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Polynomial.sum_def, map_sum, Finset.sum_smul,
    ← Finset.sum_sub_distrib]
  refine U.sum_mem fun k _ => ?_
  rw [one_pow, mul_one, ← smul_sub]
  exact U.smul_mem _ (hit k)

theorem inv_of_congr (γ : V →+ V) (U : Submodule (PowerSeries O) V) (hU : ∀ u ∈ U, γ u ∈ U)
    (a : PowerSeries O) (ha : ∀ v, γ (a • v) = a • γ v) {v w : V} (hw : γ w - w ∈ U)
    (hv : v - a • w ∈ U) : γ v - v ∈ U := by
  have e : γ v - v = (γ (v - a • w) - (v - a • w)) + a • (γ w - w) := by
    rw [map_sub, ha, smul_sub]; abel
  rw [e]
  exact U.add_mem (U.sub_mem (hU _ hv) hv) (U.smul_mem _ hw)

def gW (γ : V →+ V) (W : Submodule (PowerSeries O) V) (h : ∀ w ∈ W, γ w ∈ W) : ↥W →+ ↥W where
  toFun w := ⟨γ w, h w w.2⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

end gen

section lat
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V V' : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] [AddCommGroup V'] [Module (PowerSeries O) V']

theorem γ_C (L : Lat B n V) (i : ZMod n) (a : O) (v : V) : L.γ i (C a • v) = C a • L.γ i v := by
  rw [L.γ_semi]
  congr 1
  exact B.γ.commutes a

theorem γ_XN (L : Lat B n V) (c : ZMod n) (hX : B.GamX) (hN : L.GamN c) :
    ∀ u ∈ sm X (L.N c), L.γ c u ∈ sm X (L.N c) := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := mem_sm.1 hu
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hX
  have hγv : L.γ c v ∈ L.N c := by
    have : L.γ c v = (L.γ c v - v) + v := by abel
    rw [this]
    exact (L.N c).add_mem (sm_le _ _ (hN v hv)) hv
  rw [L.γ_semi, ← ha, mul_comm, mul_smul]
  exact mem_sm.2 ⟨a • L.γ c v, (L.N c).smul_mem _ hγv, rfl⟩

theorem gamma_mem_latticeW (L : Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (h : L.GammaCongruentArc c ell Λ) :
    ∀ w ∈ L.W c ell Λ, L.γ c w ∈ L.W c ell Λ := by
  intro w hw
  have : L.γ c w = (L.γ c w - w) + w := by abel
  rw [this]
  exact (L.W c ell Λ).add_mem (sm_le _ _ (h w hw)) hw

theorem hom_phiIt {L : Lat B n V} {L' : Lat B n V'} (h : LatHom L L') (i : ZMod n) (k : ℕ) (v : V) :
    h.f (L.phiIt i k v) = L'.phiIt i k (h.f v) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Lat.phiIt]; rw [h.φ_comm, ih]

theorem map_mem_arcSpan {L : Lat B n V} {L' : Lat B n V'} (h : LatHom L L') (c : ZMod n) (ell : ℕ)
    (Λ : PowerSeries O) : ∀ v ∈ L.W c ell Λ, h.f v ∈ L'.W c ell Λ := by
  have hp : L.pull (c - (ell : ZMod n)) ell ≤ (L'.pull (c - (ell : ZMod n)) ell).comap h.f := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, rfl⟩
    show h.f (L.phiIt _ _ u) ∈ L'.pull _ _
    rw [hom_phiIt]
    exact Submodule.subset_span ⟨h.f u, h.map_N _ u hu, rfl⟩
  intro v hv
  have h1 : Λ • v ∈ L.pull (c - (ell : ZMod n)) ell := mem_dv.1 hv
  have h2 := hp h1
  refine mem_dv.2 ?_
  rw [← map_smul]
  exact h2

end lat

section core
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₁ V₂ : Type} [AddCommGroup V₁]
  [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
  {L₁ : Lat B n V₁} {L₂ : Lat B n V₂} {h : LatHom L₁ L₂} {c : ZMod n} {ell : ℕ}
  {Λ : PowerSeries O} {r₁ r₂ : ℕ} {S₁ : LevelData L₁ c ell Λ r₁} {S₂ : LevelData L₂ c ell Λ r₂}

theorem step2 (g : ℕ) (PP : Polynomial O) (hGX : B.GamX) (hGN : L₂.GamN c)
    (hP4c : L₂.GammaCongruentArc c ell Λ) (hEq : S₂.Equiv) (hK2 : S₂.K2iii) (hRD : S₂.RD g)
    (hK3 : S₂.K3a2 g PP) (hP4b : S₂.XMulIff) (w : V₂) (hwI : L₂.Ic c w) (hwW : w ∈ L₂.W c ell Λ) :
    ∃ x' : ↥(L₂.W c ell Λ), L₂.Ic c (x' : V₂) ∧
      (x' : V₂) - C (PP.eval 1) • w ∈ sm X (L₂.N c) ∧
      ∀ s < ell, InSum (S₂.Dc s) (S₂.Nb s) (S₂.loc s x') := by
  have hU := γ_XN L₂ c hGX hGN
  have hW := gamma_mem_latticeW L₂ c ell Λ hP4c
  let G := gW (L₂.γ c) (L₂.W c ell Λ) hW
  let x : ↥(L₂.W c ell Λ) := ⟨w, hwW⟩
  have hval : ((polyAct PP G x : ↥(L₂.W c ell Λ)) : V₂) = polyAct PP (L₂.γ c) w :=
    polyAct_map (L₂.W c ell Λ).subtype G (L₂.γ c) (fun _ => rfl) PP x
  have h2a : ((polyAct PP G x : ↥(L₂.W c ell Λ)) : V₂) - C (PP.eval 1) • w ∈ sm X (L₂.N c) := by
    rw [hval]; exact polyAct_shift (L₂.γ c) _ hU PP hwI
  refine ⟨polyAct PP G x, ?_, h2a, ?_⟩
  · exact inv_of_congr (L₂.γ c) _ hU (C (PP.eval 1)) (γ_C L₂ c _) hwI h2a
  · intro s hs
    have hG : ∀ v, S₂.loc s (G v) = S₂.gE s (S₂.loc s v) := fun v => hEq s hs v.1 v.2 _
    rw [polyAct_map (S₂.loc s) G (S₂.gE s) hG PP x]
    refine hK3 s hs _ (InSum.mono (hRD s hs).2 (hK2 s hs x ?_))
    have hm : ((G x - x : ↥(L₂.W c ell Λ)) : V₂) ∈ sm X (L₂.N c) := hwI
    have := ((hP4b (G x - x)).1 hm).2 s hs
    rwa [map_sub, hG] at this

theorem step3 (m : LevelMap h S₁ S₂) (g sig rr a₀ : ℕ) (ϖ : O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
    (U₁ : ℕ → Submodule O (Fin r₁ → O)) (U₂ : ℕ → Submodule O (Fin r₂ → O))
    (hRD₁ : S₁.RD g) (hRD₂ : S₂.RD g) (hPa₁ : S₁.Partner sig) (hPa₂ : S₂.Partner sig)
    (hP3₁ : S₁.P3) (hP3₂ : S₂.P3) (hP4a₁ : S₁.DivisibleIff g) (hP4a₂ : S₂.DivisibleIff g)
    (hBr₁ : S₁.Bridge ϖ H b kind U₁) (hBr₂ : S₂.Bridge ϖ H b kind U₂) (hFl : m.MapFl)
    (hP4d : h.LiftsDivisible c ell g rr) (hCL : ConstLift ϖ B.ℓ B.p H b kind U₁ U₂ ell a₀ m.prL)
    (x' : ↥(L₂.W c ell Λ)) (hx' : ∀ s < ell, InSum (S₂.Dc s) (S₂.Nb s) (S₂.loc s x')) :
    ∃ z : ↥(L₁.W c ell Λ), h.f (z : V₁) = B.lc ^ (2 * sig + 2 * a₀ + rr) • (x' : V₂) ∧
      ∀ s < ell, InSum (S₁.Dc s) (dv (B.p s ^ g) (S₁.Nl s)) (S₁.loc s z) := by
  obtain ⟨y, hy⟩ := hPa₂.1 x'
  have hyII : ∀ s < ell, InSum (S₂.Dc s) (S₂.Nb s) (S₂.locL s y) := by
    intro s hs
    obtain ⟨d, hd, hm⟩ := hx' s hs
    refine ⟨B.lc ^ sig • d, lc_smul_mem B sig _ hd, ?_⟩
    have e : S₂.locL s y - B.lc ^ sig • d
        = (S₂.locL s y - B.lc ^ sig • S₂.loc s x') + B.lc ^ sig • (S₂.loc s x' - d) := by
      rw [smul_sub]; abel
    rw [e]
    exact (S₂.Nb s).add_mem ((hP3₂ s hs).2 (hy s hs)) ((S₂.Nb s).smul_mem _ hm)
  obtain ⟨y₁, ν, hII₁, hNN, hyeq⟩ := hCL y ((hBr₂.2 y).1 hyII)
  have hy₁ := (hBr₁.2 y₁).2 hII₁
  have hν := (hBr₂.1 ν).2 hNN
  obtain ⟨x₁, hx₁⟩ := hPa₁.2 y₁
  let hx : ↥(L₂.W c ell Λ) := ⟨h.f x₁, map_mem_arcSpan h c ell Λ _ x₁.2⟩
  let Δ : ↥(L₂.W c ell Λ) := B.lc ^ (2 * sig + 2 * a₀) • x' - hx
  have hΔ : ∀ s < ell, S₂.loc s Δ ∈ S₂.Nb s := by
    intro s hs
    have a1 := (hP3₂ s hs).2 (hy s hs)
    have a2 := (hP3₂ s hs).2 (hFl s hs _ (hx₁ s hs))
    rw [map_sub, map_smul, m.loc_comm s hs x₁.1 x₁.2 (map_mem_arcSpan h c ell Λ _ x₁.2),
      m.locL_comm s hs] at a2
    have heq := congrArg (S₂.locL s) hyeq
    rw [map_add, map_smul, map_smul, ← lc_pow] at heq
    have key : S₂.loc s Δ = -(B.lc ^ (sig + 2 * a₀) • (S₂.locL s y - B.lc ^ sig • S₂.loc s x'))
        - (S₂.loc s hx - B.lc ^ sig • S₂.locL s (extL m.prL y₁))
        + (B.lc ^ sig * B.lc ^ (2 * a₀)) • S₂.locL s ν := by
      show S₂.loc s (B.lc ^ (2 * sig + 2 * a₀) • x' - hx) = _
      have h1 : B.lc ^ (sig + 2 * a₀) • S₂.locL s y = B.lc ^ sig • S₂.locL s (extL m.prL y₁)
          + (B.lc ^ sig * B.lc ^ (2 * a₀)) • S₂.locL s ν := by
        rw [pow_add, mul_smul, heq, smul_add, mul_smul]
      have h2 : B.lc ^ (sig + 2 * a₀) • B.lc ^ sig • S₂.loc s x'
          = B.lc ^ (2 * sig + 2 * a₀) • S₂.loc s x' := by
        rw [smul_smul, ← pow_add]
        congr 2
        omega
      rw [map_sub, map_smul, smul_sub, h1, h2]
      abel
    rw [key]
    exact (S₂.Nb s).add_mem ((S₂.Nb s).sub_mem ((S₂.Nb s).neg_mem ((S₂.Nb s).smul_mem _ a1)) a2)
      ((S₂.Nb s).smul_mem _ (hν s hs))
  have hΔTh : (Δ : V₂) ∈ dv (B.Th ell g) (L₂.N c) :=
    (hP4a₂.2 Δ).2 fun s hs => (hRD₂ s hs).1 (hΔ s hs)
  obtain ⟨Δ₁, hΔ₁, hΔim⟩ := hP4d _ hΔTh
  let D1 : ↥(L₁.W c ell Λ) := ⟨Δ₁, hP4a₁.1 hΔ₁⟩
  have hD1 := (hP4a₁.2 D1).1 hΔ₁
  refine ⟨B.lc ^ rr • x₁ + D1, ?_, ?_⟩
  · show h.f (B.lc ^ rr • (x₁ : V₁) + Δ₁) = _
    rw [map_add, map_smul, hΔim]
    show B.lc ^ rr • h.f x₁ + B.lc ^ rr • (B.lc ^ (2 * sig + 2 * a₀) • (x' : V₂) - h.f x₁) = _
    rw [smul_sub, smul_smul, ← pow_add, add_sub_cancel, add_comm rr]
  · intro s hs
    obtain ⟨d, hd, hm⟩ := hy₁ s hs
    refine ⟨B.lc ^ rr • B.lc ^ sig • d, lc_smul_mem B rr _ (lc_smul_mem B sig _ hd), ?_⟩
    have e : S₁.loc s (B.lc ^ rr • x₁ + D1) - B.lc ^ rr • B.lc ^ sig • d
        = B.lc ^ rr • (S₁.loc s x₁ - B.lc ^ sig • S₁.locL s y₁)
          + B.lc ^ rr • B.lc ^ sig • (S₁.locL s y₁ - d) + S₁.loc s D1 := by
      rw [map_add, map_smul]
      simp only [smul_sub]
      abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ((hRD₁ s hs).1 hm)))) (hD1 s hs)
    exact le_dv _ _ ((hP3₁ s hs).1 (hx₁ s hs))

theorem step4 (g : ℕ) (PP' : Polynomial O) (hP4c : L₁.GammaCongruentArc c ell Λ) (hEq : S₁.Equiv)
    (hK3 : S₁.K3a4 g PP') (hDc : S₁.DcFix) (hP4b : S₁.XMulIff) (z : ↥(L₁.W c ell Λ))
    (hz : ∀ s < ell, InSum (S₁.Dc s) (dv (B.p s ^ g) (S₁.Nl s)) (S₁.loc s z)) :
    polyAct PP' (L₁.γ c) (z : V₁) ∈ L₁.W c ell Λ ∧ L₁.Ic c (polyAct PP' (L₁.γ c) (z : V₁)) := by
  have hW := gamma_mem_latticeW L₁ c ell Λ hP4c
  let G := gW (L₁.γ c) (L₁.W c ell Λ) hW
  have hval : ((polyAct PP' G z : ↥(L₁.W c ell Λ)) : V₁) = polyAct PP' (L₁.γ c) z :=
    polyAct_map (L₁.W c ell Λ).subtype G (L₁.γ c) (fun _ => rfl) PP' z
  rw [← hval]
  refine ⟨(polyAct PP' G z).2, ?_⟩
  set zt := polyAct PP' G z with hzt
  have : ((G zt - zt : ↥(L₁.W c ell Λ)) : V₁) ∈ sm X (L₁.N c) := by
    refine (hP4b (G zt - zt)).2 ⟨hP4c zt zt.2, ?_⟩
    intro s hs
    have hG : ∀ v, S₁.loc s (G v) = S₁.gE s (S₁.loc s v) := fun v => hEq s hs v.1 v.2 _
    obtain ⟨d, hd, hm⟩ := hK3 s hs _ (hz s hs)
    rw [← polyAct_map (S₁.loc s) G (S₁.gE s) hG PP' z, ← hzt] at hm
    have e : S₁.loc s (G zt - zt) = S₁.gE s (S₁.loc s zt - d) - (S₁.loc s zt - d) := by
      rw [map_sub, hG, map_sub, (hDc s hs).1 d hd]; abel
    rw [e]
    exact (S₁.Nl s).sub_mem ((hDc s hs).2 _ hm) hm
  exact this

end core

end Formalism.ExponentWindows.E.IteratedPhiHomomorphisms

namespace Formalism.ExponentWindows.E

open PowerSeries IteratedPhiHomomorphisms

theorem arc_lift_of_localization_data : ArcLiftOfLocalizationData := by
  intro O _ B n _ Cu abelian₂ g sig rr a₀ kap V₁ V₂ _ _ _ _ L₁ L₂ h c r₁ r₂ S₁ S₂ m ϖ H b kind U₁ U₂
    PP PP' _ hGX hGN hP4c₁ hP4c₂ hEq₁ hEq₂ hK2 hRD₁ hRD₂ hK32 hK34 hDc hPa₁ hPa₂ hP3₁ hP3₂
    hP4a₁ hP4a₂ hP4b₁ hP4b₂ hBr₁ hBr₂ hFl hP4d hCL hPP w hw
  obtain ⟨k, ε, hk, hε⟩ := hPP
  obtain ⟨x', hx'I, hx'c, hx'l⟩ := step2 g PP hGX hGN hP4c₂ hEq₂ hK2 hRD₂ hK32 hP4b₂ w hw.1 hw.2
  obtain ⟨z, hzim, hzl⟩ := step3 m g sig rr a₀ ϖ H b kind U₁ U₂ hRD₁ hRD₂ hPa₁ hPa₂ hP3₁ hP3₂
    hP4a₁ hP4a₂ hBr₁ hBr₂ hFl hP4d hCL x' hx'l
  obtain ⟨h4W, h4I⟩ := step4 g PP' hP4c₁ hEq₁ hK34 hDc hP4b₁ z hzl
  refine ⟨polyAct PP' (L₁.γ c) (z : V₁), k, ε, hk, ⟨h4I, h4W⟩, ?_⟩
  have hU := γ_XN L₂ c hGX hGN
  rw [polyAct_map h.f (L₁.γ c) (L₂.γ c) (h.γ_comm c) PP' z, hzim, lc_pow]
  have hsm : polyAct PP' (L₂.γ c) (C ((B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr)) • (x' : V₂))
      = C ((B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr)) • polyAct PP' (L₂.γ c) (x' : V₂) :=
    (polyAct_map (LinearMap.lsmul (PowerSeries O) V₂ (C ((B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr))))
      (L₂.γ c) (L₂.γ c) (fun v => (γ_C L₂ c _ v).symm) PP' (x' : V₂)).symm
  rw [hsm]
  have h1 := polyAct_shift (L₂.γ c) _ hU PP' hx'I
  have e : C ((B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr)) • polyAct PP' (L₂.γ c) (x' : V₂)
      - C ((ε : O) * (B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr + k)) • w
      = C ((B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr)) •
        ((polyAct PP' (L₂.γ c) (x' : V₂) - C (PP'.eval 1) • (x' : V₂))
          + C (PP'.eval 1) • ((x' : V₂) - C (PP.eval 1) • w)) := by
    have hc : C ((ε : O) * (B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr + k))
        = C ((B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr)) * (C (PP'.eval 1) * C (PP.eval 1)) := by
      rw [← map_mul, ← map_mul, mul_comm (PP'.eval 1), hε]
      congr 1
      ring
    rw [hc]
    simp only [smul_sub, smul_add, mul_smul]
    abel
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ h1 (Submodule.smul_mem _ _ hx'c))

end Formalism.ExponentWindows.E

namespace Formalism.ExponentWindows.E.CL

open PowerSeries

variable {O : Type} [CommRing O]

theorem extL_cst {r₁ r₂ : ℕ} (f : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) (v : Fin r₁ → O) :
    extL f (cst v) = cst (f v) := by
  ext1 i
  have h := RingHom.map_mulVec (C : O →+* PowerSeries O) (LinearMap.toMatrix' f) v i
  rw [LinearMap.toMatrix'_mulVec] at h
  simp only [extL, Matrix.toLin'_apply, cst]
  exact h.symm

theorem cst_smul {r : ℕ} (a : O) (v : Fin r → O) : cst (a • v) = C a • cst v := by
  ext1 i
  simp [cst]

theorem levelCond_zero {r : ℕ} (ϖ : O) (p : PowerSeries O) (H b : ℕ) (k : Kind)
    (V : Submodule O (Fin r → O)) : LevelCond ϖ p H b k V 0 := by
  cases k
  · exact ⟨0, 0, by simp⟩
  · exact ⟨0, 0, 0, Submodule.zero_mem _, by simp⟩
  · exact ⟨0, 0, 0, Submodule.zero_mem _, by simp⟩

theorem NN_zero {r : ℕ} (ϖ : O) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
    (V : ℕ → Submodule O (Fin r → O)) (ell : ℕ) : NN ϖ p H b kind V ell 0 :=
  fun _ _ => levelCond_zero _ _ _ _ _ _

theorem II_zero {r : ℕ} (ϖ : O) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
    (V : ℕ → Submodule O (Fin r → O)) (ell : ℕ) : II ϖ p H b kind V ell 0 := by
  intro s _
  refine ⟨0, 0, ?_⟩
  have : C (ϖ ^ 0) • (0 : Fin r → PowerSeries O) - abelian₂ p H ell • cst 0 = 0 := by
    ext1 i; simp [cst]
  rw [this]
  exact levelCond_zero _ _ _ _ _ _

theorem lift_L {r₁ r₂ : ℕ} {ℓ rr a₀ : ℕ} {prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)}
    (h : LLift ℓ rr prL) (hr : rr ≤ 2 * a₀) (v : Fin r₂ → O) :
    ∃ v₁ : Fin r₁ → O, prL v₁ = (ℓ : O) ^ (2 * a₀) • v := by
  obtain ⟨v₁, hv₁⟩ := h v
  refine ⟨(ℓ : O) ^ (2 * a₀ - rr) • v₁, ?_⟩
  rw [map_smul, hv₁, smul_smul, ← pow_add, Nat.sub_add_cancel hr]

theorem extL_term {r₁ r₂ : ℕ} (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) (a : PowerSeries O) (e : O)
    {v₁ : Fin r₁ → O} {v : Fin r₂ → O} (h : prL v₁ = e • v) :
    extL prL (a • cst v₁) = C e • (a • cst v) := by
  rw [map_smul, extL_cst, h, cst_smul, smul_comm]

theorem lifts_mod_const_of_no_down : ConstLiftNone := by
  intro hM O _ _ _ ϖ hϖ ℓ ell r₁ r₂ a₀ p H b kind U₁ U₂ prL hS hk y hy
  obtain ⟨h2, hP, -, hs₂, hup⟩ := hS
  refine ⟨0, y, II_zero _ _ _ _ _ _ _, (hM O ϖ hϖ ℓ ell r₂ p H b kind U₂ h2 hP hs₂ hup hk y).1 hy, ?_⟩
  simp

theorem lifts_mod_const_of_one_down : ConstLiftD := by
  intro hM O _ _ _ ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₁ hs₁ hk₁ hth y hy
  obtain ⟨h2, hP, hsat₁, hsat₂, hup⟩ := hS
  obtain ⟨lam, ν, hν, rfl⟩ :=
    (hM O ϖ hϖ ℓ ell r₂ p H b kind U₂ h2 hP hsat₂ hup s₁ hs₁ hk₁ hth y).1 hy
  obtain ⟨lam₁, h₁⟩ := lift_L hL hr lam
  refine ⟨abelian₂ p H ell • cst lam₁, ν,
    (hM O ϖ hϖ ℓ ell r₁ p H b kind U₁ h2 hP hsat₁ hup s₁ hs₁ hk₁ hth _).2
      ⟨lam₁, 0, NN_zero _ _ _ _ _ _ _, by simp⟩, hν, ?_⟩
  rw [extL_term prL _ _ h₁, smul_add]

theorem lifts_mod_const_of_down_up : ConstLiftDU := by
  intro hM O _ _ _ ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₀ s₁ h01 hs₁ hk₁ hk₀ hth
    hb y hy
  obtain ⟨h2, hP, hsat₁, hsat₂, hup⟩ := hS
  obtain ⟨lam, ν, hν, rfl⟩ :=
    (hM O ϖ hϖ ℓ ell r₂ p H b kind U₂ h2 hP hsat₂ hup s₀ s₁ h01 hs₁ hk₁ hk₀ hth hb y).1 hy
  obtain ⟨lam₁, h₁⟩ := lift_L hL hr lam
  refine ⟨abelian₂ p H ell • cst lam₁, ν,
    (hM O ϖ hϖ ℓ ell r₁ p H b kind U₁ h2 hP hsat₁ hup s₀ s₁ h01 hs₁ hk₁ hk₀ hth hb _).2
      ⟨lam₁, 0, NN_zero _ _ _ _ _ _ _, by simp⟩, hν, ?_⟩
  rw [extL_term prL _ _ h₁, smul_add]

theorem lifts_mod_const_of_down_down : ConstLiftDD := by
  intro hM O _ _ _ ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₀ s₁ h01 hs₁ hk₁ hk₀ hth
    ρ fρ hρ hmin hf₁ hf₀ y hy
  obtain ⟨h2, hP, hsat₁, hsat₂, hup⟩ := hS
  obtain ⟨lam, lam', ν, hν, rfl⟩ :=
    (hM O ϖ hϖ ℓ ell r₂ p H b kind U₂ h2 hP hsat₂ hup s₀ s₁ h01 hs₁ hk₁ hk₀ hth ρ fρ hρ hmin hf₁
      hf₀ y).1 hy
  obtain ⟨lam₁, h₁⟩ := lift_L hL hr lam
  obtain ⟨lam₁', h₁'⟩ := lift_L hL hr lam'
  refine ⟨abelian₂ p H ell • cst lam₁ + (abelian₂ p H ell * fρ) • cst lam₁', ν,
    (hM O ϖ hϖ ℓ ell r₁ p H b kind U₁ h2 hP hsat₁ hup s₀ s₁ h01 hs₁ hk₁ hk₀ hth ρ fρ hρ hmin hf₁
      hf₀ _).2 ⟨lam₁, lam₁', 0, NN_zero _ _ _ _ _ _ _, by simp⟩, hν, ?_⟩
  rw [map_add, extL_term prL _ _ h₁, extL_term prL _ _ h₁', smul_add, smul_add]

theorem lifts_mod_const_of_up_down : ConstLiftUD := by
  intro hM O _ _ _ ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₀ s₁ h01 hs₁ hk₁ hk₀ hth
    hC c α β hc hnc y hy
  obtain ⟨h2, hP, hsat₁, hsat₂, hup⟩ := hS
  obtain ⟨lam, lam', ν, hlam', hν, rfl⟩ :=
    (hM O ϖ hϖ ℓ ell r₂ p H b kind U₂ h2 hP hsat₂ hup s₀ s₁ h01 hs₁ hk₁ hk₀ hth c α β hc hnc y).1 hy
  obtain ⟨lam₁, h₁⟩ := lift_L hL hr lam
  obtain ⟨lam₁', hm₁', h₁'⟩ := hC lam' hlam'
  refine ⟨abelian₂ p H ell • cst lam₁ + (α * LamLess p H ell s₁ (b s₁)) • cst lam₁', ν,
    (hM O ϖ hϖ ℓ ell r₁ p H b kind U₁ h2 hP hsat₁ hup s₀ s₁ h01 hs₁ hk₁ hk₀ hth c α β hc hnc _).2
      ⟨lam₁, lam₁', 0, hm₁', NN_zero _ _ _ _ _ _ _, by simp⟩, hν, ?_⟩
  rw [map_add, extL_term prL _ _ h₁, extL_term prL _ _ h₁', smul_add, smul_add]

theorem lifts_mod_const_of_words : ConstLiftOf :=
  ⟨lifts_mod_const_of_no_down, lifts_mod_const_of_one_down, lifts_mod_const_of_down_up, lifts_mod_const_of_down_down, lifts_mod_const_of_up_down⟩

end Formalism.ExponentWindows.E.CL
