import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InclWFrobIter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLaws

noncomputable section

namespace GlobalTheory.NL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def LevLaws (W : LocWach PD LL O v n) : Prop :=
  (∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
    IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
    ζ' = ζ ^ a → ∀ f : LetA O n,
    W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f)) ∧
  ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
    W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f)

theorem root_pow {p : ℕ} (hp : p.Prime) {ζ : LL} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (p ^ j)) (a : ℕ) :
    ∃ j : ℕ, IsPrimitiveRoot (ζ ^ a) (p ^ j) := by
  obtain ⟨j, hj⟩ := h
  have h1 : (ζ ^ a) ^ (p ^ j) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hj.pow_eq_one, one_pow]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨k, hk ▸ IsPrimitiveRoot.orderOf (ζ ^ a)⟩

def gamOf (W : LocWach PD LL O v n) {s : ℕ} (hs : W.s = s) : WGam PD LL O v n s :=
  { W with
    s_pos := hs ▸ W.s_pos
    s_two := hs ▸ W.s_two
    gam_gen := hs ▸ W.gam_gen
    gamK_eq_one := hs ▸ W.gamK_eq_one
    GKs_def := hs ▸ W.GKs_def }

open Classical in

def levOf (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) : LetA O n →ₐ[O] PowerSeries LL :=
  if ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j) then W.lev i ζ else W.lev i 1

theorem levOf_root (W : LocWach PD LL O v n) (i : ZMod n) {ζ : LL} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    levOf W i ζ = W.lev i ζ := if_pos h

theorem levOf_cases (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) : ∃ ζ', levOf W i ζ = W.lev i ζ' := by
  unfold levOf; split_ifs <;> exact ⟨_, rfl⟩

def serOf (W : LocWach PD LL O v n) {s : ℕ} (hs : W.s = s) (hp : PD.p.Prime) (hL : LevLaws W) :
    WSer (gamOf W hs) :=
  { W with
    lev := levOf W
    lev_letter := fun i ζ a ha => by
      obtain ⟨ζ', e⟩ := levOf_cases W i ζ
      rw [e]; exact W.lev_letter i ζ' a ha
    lev_π := fun i ζ h => by rw [levOf_root W i h]; exact W.lev_π i ζ h
    lev_cont := fun i ζ a k r => by
      obtain ⟨ζ', e⟩ := levOf_cases W i ζ
      rw [e]; exact W.lev_cont i ζ' a k r
    lev_Γ := fun g i ζ ζ' j a h1 h2 h3 f => by
      rw [levOf_root W i ⟨j, h1⟩, levOf_root W i (h3 ▸ root_pow hp ⟨j, h1⟩ a)]
      exact hL.1 g i ζ ζ' j a h1 h2 h3 f
    lev_φ := fun i ζ h f => by
      rw [levOf_root W i h, levOf_root W (i - 1) (root_pow hp h PD.p)]
      exact hL.2 i ζ h f
    lev_junk := fun i ζ h => by
      rw [levOf_root W i (ζ := 1) ⟨0, by simp⟩]; exact if_neg h }

variable {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

def IoLaws {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  (∀ e, E.ioE (W.φE e) = φR (E.ioE e)) ∧ ∀ (g : G) e, E.ioE (W.γE (W.resΓ g) e) = gR g (E.ioE e)

variable {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) {s : ℕ} (hs : W.s = s)
  (hp : PD.p.Prime) (hL : LevLaws W) (hI : IoLaws E)

def ioOf : WIo (serOf W hs hp hL) RA RW inclR φR gR πA :=
  { E with ioE_φ := hI.1, ioE_γ := hI.2 }

set_option maxHeartbeats 1000000 in

def etOf : WEt (ioOf E hs hp hL hI) := { W, E with }

set_option maxHeartbeats 1000000 in

def clOf : WCl (etOf E hs hp hL hI) := { W, E with }

open Classical in

def nOf (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Submodule (LetA O n) (W.DD T) :=
  if IsCrys PD T.ρ then W.N T else ⊥

theorem nOf_crys (W : LocWach PD LL O v n) {T : LocLat G Qp LL O} (h : IsCrys PD T.ρ) : nOf W T = W.N T := if_pos h

theorem nOf_ind (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (p : Submodule (LetA O n) (W.DD T) → Prop)
    (h1 : p (W.N T)) (h0 : p ⊥) : p (nOf W T) := by
  unfold nOf; split_ifs <;> assumption

set_option maxHeartbeats 1000000 in

def latOf {Zl : Type} [CommRing Zl] (zl : PowerSeries Zl →+* LetA O n) (h1 : IsCrys PD W.one.ρ)
    (hP : ∀ T, @Module.Projective (PowerSeries Zl) _ ↥(W.N T) _ (Module.compHom _ zl)) :
    WN (etOf E hs hp hL hI) zl where
  N := nOf W
  N_base := fun T hT => by
    have := W.N_base T hT
    rw [← nOf_crys W hT] at this
    exact this
  N_φ := fun T => by
    subst hs
    exact nOf_ind W T (fun S => ∀ x ∈ S, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ S) (W.N_φ T)
      (fun x hx => ⟨0, by rw [(Submodule.mem_bot _).1 hx]; simp⟩)
  N_φinv := fun T => by
    subst hs
    exact nOf_ind W T (fun S => ∀ y ∈ S, ∃ k : ℕ, W.Q ^ k • y ∈
      Submodule.span (LetA O n) (W.φD T '' (S : Set (W.DD T)))) (W.N_φinv T)
      (fun x hx => ⟨0, by rw [(Submodule.mem_bot _).1 hx]; simp⟩)
  N_fg := fun T => nOf_ind W T (fun S => S.FG) (W.N_fg T) Submodule.fg_bot
  N_Γ := fun T g => nOf_ind W T (fun S => ∀ x ∈ S, W.γD T g x ∈ S) (W.N_Γ T g)
      (fun x hx => by rw [(Submodule.mem_bot _).1 hx]; simp)
  N_π := fun T g => nOf_ind W T (fun S => ∀ x ∈ S, ∃ y ∈ S, W.γD T g x - x = (letπ : LetA O n) • y) (W.N_π T g)
      (fun x hx => ⟨0, Submodule.zero_mem _, by rw [(Submodule.mem_bot _).1 hx]; simp⟩)
  map_N := fun {T T'} f hT hT' x hx => by
    have hx' : x ∈ W.N T := (nOf_crys W hT) ▸ hx
    have := W.map_N f hT hT' x hx'
    rw [← nOf_crys W hT'] at this
    exact this
  one_e := by
    obtain ⟨e, e₀, a, b, c⟩ := E.one_e
    exact ⟨e, e₀, a, b, (nOf_crys W h1).trans c⟩
  N_proj := fun T => nOf_ind W T (fun S => @Module.Projective (PowerSeries Zl) _ ↥S _ (Module.compHom _ zl)) (hP T)
      (by
        letI : Module (PowerSeries Zl) ↥(⊥ : Submodule (LetA O n) (W.DD T)) := Module.compHom _ zl
        exact Module.Projective.of_free)
  N_junk := fun T hT => if_neg hT

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
  {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)

structure Laws : Prop where
  lev : LevLaws (H.W K s LL h)
  io : IoLaws (F.E K s LL h).tie
  one : IsCrys (P.PD K) (H.W K s LL h).one.ρ

theorem p_prime (P : LocPrime l) (K : FinExt l) : (P.PD K).p.Prime := (P.PD_p K).symm ▸ (Fact.out : l.Prime)

abbrev GamL := gamOf (H.W K s LL h) (H.W_s K s LL h)

variable (hL : Laws H F h)

set_option maxHeartbeats 400000 in

abbrev SerL := serOf (H.W K s LL h) (H.W_s K s LL h) (p_prime P K) hL.lev

set_option maxHeartbeats 400000 in

abbrev IoL := ioOf (F.E K s LL h).tie (H.W_s K s LL h) (p_prime P K) hL.lev hL.io

set_option maxHeartbeats 400000 in

theorem ioW : IoW (Γ := GamL H h) (R := SerL H F h hL) (IoL H F h hL) := (F.E K s LL h).inertia_action_on_roots

set_option maxHeartbeats 400000 in

abbrev EtL := etOf (F.E K s LL h).tie (H.W_s K s LL h) (p_prime P K) hL.lev hL.io

set_option maxHeartbeats 400000 in

abbrev ClL := clOf (F.E K s LL h).tie (H.W_s K s LL h) (p_prime P K) hL.lev hL.io

set_option maxHeartbeats 400000 in

abbrev LatL :=
  latOf (F.E K s LL h).tie (H.W_s K s LL h) (p_prime P K) hL.lev hL.io _ hL.one (H.W_proj K s LL h)

set_option maxHeartbeats 400000 in

theorem latL_N {T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (hT : IsCrys (P.PD K) T.ρ) :
    (LatL H F h hL).N T = (H.W K s LL h).N T := nOf_crys _ hT

theorem apply_layers (p : ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (E : WEt I), NS E → Prop)
    (hp : ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (Mo : NS E), p Γ R I E Mo) :
    p (GamL H h) (SerL H F h hL) (IoL H F h hL) (EtL H F h hL) (LatL H F h hL) :=
  hp _ _ _ (ioW H F h hL) _ _

end Concrete

namespace Holds

open PowerSeries GlobalTheory.HWL.Ser

section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR}
    {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L] [Algebra ℤ_[l] O]
    [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] {v : AddValuation L (WithTop ℚ)}
    [Algebra Qp L] [TopologicalSpace L] {n : ℕ}

def evL (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
  (W.lev i ζ).comp (AlgHom.pi fun _ => AlgHom.id O O⟦X⟧)

omit [CharZero L] [Algebra ℚ L] in

theorem lev_eq_evL (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) (a : LetA O n) :
    W.lev i ζ a = evL W i ζ (a i) := by
  have := W.lev_letter i ζ (a - fun _ => a i) (by simp)
  rw [map_sub, sub_eq_zero] at this
  exact this

theorem evL_X (W : LocWach PD L O v n) (i : ZMod n) {ζ : L} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    evL W i ζ X = C ζ * exp L - 1 := by
  obtain ⟨E, h1, h2, h3⟩ := W.lev_π i ζ h
  have : E = exp L := ode_unique 1 (by simpa using h2) (by simpa using derivative_exp L) (by simpa using h1)
  rw [← this, ← h3, add_sub_cancel_left]
  rfl

theorem levLaws_of (W : LocWach PD L O v n) (hp : PD.p = l) (c : W.Gam → ℤ_[l])
    (hc : ∀ g, algebraMap ℤ_[l] O (c g) = (W.χΓ g : O)) (hγ : ∀ g, W.γ₀ g = GlobalTheory.Fon.gam O (c g))
    (hv : ∀ (c : ℤ_[l]) (j a : ℕ), (j : WithTop ℚ) ≤ v (algebraMap ℤ_[l] L c - (a : L)) →
      (l : ℤ_[l]) ^ j ∣ c - a) (H : EvLaw l (O := O) v inferInstance) : LevLaws W := by
  have hc' : ∀ g, algebraMap O L (W.χΓ g : O) = algebraMap ℤ_[l] L (c g) :=
    fun g => by rw [← hc, ← IsScalarTower.algebraMap_apply]
  have hφ : W.φ₀ = GlobalTheory.Fon.gam O (l : ℤ_[l]) := by
    have h0 : W.φ₀ X = (1 + X) ^ l - 1 := by rw [W.φ₀_X, W.q₀_def, hp]
    rw [GlobalTheory.Fon.gam_l]
    exact GlobalTheory.Fon.algHom_ext_X (by rw [h0, GlobalTheory.Fon.cyclotomicFrobeniusPowerSeries_X]) (by rw [h0]; simp)
  refine ⟨?_, ?_⟩
  · rintro g i ζ _ j a h hj rfl f
    rw [lev_eq_evL, lev_eq_evL, hc'] at *
    change evL W i ζ (W.γ₀ g (f i)) = _
    rw [hγ]
    exact ev_gam H (hp ▸ h.pow_eq_one) _ (hv _ j a hj) (evL_X W i ⟨j, h⟩)
      (evL_X W i (root_pow PD.hp ⟨j, h⟩ a)) (f i)
  · rintro i ζ ⟨j, h⟩ f
    rw [lev_eq_evL, lev_eq_evL]
    change evL W i ζ (W.φ₀ (f (i - 1))) = _
    have := ev_gam H (hp ▸ h.pow_eq_one) (l : ℤ_[l]) (a := l) (by simp) (evL_X W i ⟨j, h⟩)
      (evL_X W (i - 1) (root_pow PD.hp ⟨j, h⟩ l)) (f (i - 1))
    rw [map_natCast] at this
    rw [hφ, hp]
    exact this
end Generic

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
  {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem levLaws : LevLaws (H.W K s LL h) := by
  obtain ⟨c, hc⟩ := exists_padic_char (GamL H h)
  obtain ⟨_, _, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  refine levLaws_of _ (P.PD_p K) (fun g => (c g : ℤ_[l])) hc (fun g => ?_) (dvd_of_le_v P) ?_
  · have h0 : (H.W K s LL h).φ₀ X = (1 + X) ^ l - 1 := by
      rw [(H.W K s LL h).φ₀_X, (H.W K s LL h).q₀_def, P.PD_p]
    exact (GlobalTheory.Cyc.act_unique l ↥(OL LL) hl0 hlu ((H.W K s LL h).γ₀ g) (H.W K s LL h).φ₀ (c g) h0
      ((H.W K s LL h).γ₀_comm _) ((H.W K s LL h).γ₀_X _).1
      (((H.W K s LL h).γ₀_X _).2.trans (hc g).symm)).2.trans (GlobalTheory.Cyc.act_eq_gam _ _ _)
  · convert evLaw_integers P LL using 1
    exact Algebra.algebra_ext _ _ fun r => PowerSeries.algebraMap_apply

theorem laws : Laws H F h := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact ⟨levLaws H h, ⟨fun e => GlobalTheory.TorsionBoundCompare.ioE_φ _ Subtype.val_injective e,
    fun g e => GlobalTheory.TorsionBoundCompare.ioE_γ _ Subtype.val_injective g e⟩,
    GlobalTheory.TrivCrys.isCrys_lat_of_trivial _ (H.W K s LL h).one_triv⟩

set_option maxHeartbeats 1000000 in

example : (LatL H F h (laws H F h)).N (H.W K s LL h).one = (H.W K s LL h).N (H.W K s LL h).one :=
  latL_N H F h _ (laws H F h).one

set_option maxHeartbeats 1000000 in

example (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) :
    (EtL H F h (laws H F h)).φD T = (H.W K s LL h).φD T ∧ (ClL H F h (laws H F h)).cl T = (H.W K s LL h).cl T :=
  ⟨rfl, rfl⟩

end Holds

end GlobalTheory.NL
