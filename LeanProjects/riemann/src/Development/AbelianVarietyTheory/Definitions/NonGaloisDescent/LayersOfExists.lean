import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial

noncomputable section

namespace GlobalTheory.HWL.Back

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
open scoped Classical

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def fixRoot (p : ℕ) (ζ : LL) : LL := if ∃ j : ℕ, IsPrimitiveRoot ζ (p ^ j) then ζ else 1

theorem fixRoot_of {p : ℕ} {ζ : LL} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (p ^ j)) : fixRoot p ζ = ζ := if_pos h

theorem fixRoot_not {p : ℕ} {ζ : LL} (h : ¬ ∃ j : ℕ, IsPrimitiveRoot ζ (p ^ j)) : fixRoot p ζ = 1 := if_neg h

theorem fixRoot_one (p : ℕ) : fixRoot p (1 : LL) = 1 := by unfold fixRoot; split_ifs <;> rfl

theorem prim_pow {p : ℕ} (hp : p.Prime) {ζ : LL} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (p ^ j)) (a : ℕ) :
    ∃ j : ℕ, IsPrimitiveRoot (ζ ^ a) (p ^ j) := by
  obtain ⟨j, hj⟩ := h
  have h1 : orderOf (ζ ^ a) ∣ p ^ j := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_comm, pow_mul, hj.pow_eq_one, one_pow]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp h1
  exact ⟨k, hk ▸ IsPrimitiveRoot.orderOf _⟩

def gam (W : LocWach PD LL O v n) : WGam PD LL O v n W.s := { W with }

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {W : LocWach PD LL O v n} {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA}
    {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

set_option maxHeartbeats 1000000 in

def ser (C : CmpTie W E ιdR p1 tS zS) : WSer (gam W) :=
  { W with
    lev := fun i ζ => W.lev i (fixRoot PD.p ζ)
    lev_letter := fun i _ a h => W.lev_letter i _ a h
    lev_π := fun i ζ h => by rw [fixRoot_of h]; exact W.lev_π i ζ h
    lev_cont := fun i _ => W.lev_cont i _
    lev_Γ := fun g i ζ ζ' j a h hv h' f => by
      rw [fixRoot_of ⟨j, h⟩, fixRoot_of (h' ▸ prim_pow PD.hp ⟨j, h⟩ a)]
      exact C.lev_Γ g i ζ ζ' j a h hv h' f
    lev_φ := fun i ζ h f => by
      rw [fixRoot_of h, fixRoot_of (prim_pow PD.hp h _)]
      exact C.lev_φ i ζ h f
    lev_junk := fun i ζ h => by rw [fixRoot_not h, fixRoot_one] }

theorem tmul_cancel (hO : Function.Injective (algebraMap O LL)) (W : LocWach PD LL O v n)
    (e₀ : ↥W.one.L.T) (h₀ : Submodule.span O {e₀} = ⊤) {r r' : RW}
    (h : (r ⊗ₜ[O] e₀ : TW RW W.one) = r' ⊗ₜ[O] e₀) : r = r' := by
  obtain ⟨e, he, hT⟩ := W.one_line
  have hne : (e₀ : W.one.V) ≠ 0 := by
    intro h0
    have heT : e ∈ W.one.L.T := hT ▸ Submodule.mem_span_singleton_self e
    have : (⟨e, heT⟩ : ↥W.one.L.T) ∈ Submodule.span O {e₀} := h₀ ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp this
    apply he
    have := congrArg Subtype.val ha
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact this.symm
  have hbij : Function.Bijective (LinearMap.toSpanSingleton O ↥W.one.L.T e₀) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      have := congrArg Subtype.val ha
      simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul, Submodule.coe_zero] at this
      rw [← algebraMap_smul LL a, smul_eq_zero] at this
      exact hO (by rw [this.resolve_right hne, map_zero])
    · rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, h₀]
  let ψ := (LinearEquiv.ofBijective _ hbij).symm
  have hψ : ψ e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp
  have := congrArg (fun x => TensorProduct.rid O RW (LinearMap.lTensor RW ψ.toLinearMap x)) h
  simpa [hψ] using this

theorem ioE_φ (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) (a : W.EE) : E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h₀, he, -⟩ := E.one_e
  have h1 := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, he] at h1
  simp only [TWmap, smul_tmul', smul_eq_mul, mul_one, map_tmul, AlgHom.toLinearMap_apply, map_one,
    LinearMap.id_apply] at h1
  exact tmul_cancel hO W e₀ h₀ h1

theorem ioE_γ (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h₀, he, -⟩ := E.one_e
  have h1 := E.jD_act W.one g (a • e)
  have h2 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, he] at h1
  simp only [TWact, smul_tmul', smul_eq_mul, mul_one, map_tmul, AlgHom.toLinearMap_apply, map_one,
    h2] at h1
  exact tmul_cancel hO W e₀ h₀ h1

def io (hO : Function.Injective (algebraMap O LL)) (C : CmpTie W E ιdR p1 tS zS) :
    WIo (ser C) (O ⊗[Zl] Ai) RW inclR φR gR πA :=
  { E with ioE_φ := ioE_φ hO E, ioE_γ := ioE_γ hO E }

set_option maxHeartbeats 1000000 in

def et (hO : Function.Injective (algebraMap O LL)) (C : CmpTie W E ιdR p1 tS zS) : WEt (io hO C) :=
  { W, E with }

set_option maxHeartbeats 1000000 in

def cl (hO : Function.Injective (algebraMap O LL)) (C : CmpTie W E ιdR p1 tS zS) : WCl (et hO C) :=
  { W, E with }

def Ncut (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Submodule (LetA O n) (W.DD T) :=
  if IsCrys PD T.ρ then W.N T else ⊥

theorem Ncut_of {T : LocLat G Qp LL O} (h : IsCrys PD T.ρ) : Ncut W T = W.N T := if_pos h

theorem Ncut_not {T : LocLat G Qp LL O} (h : ¬ IsCrys PD T.ρ) : Ncut W T = ⊥ := if_neg h

theorem Ncut_le (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Ncut W T ≤ W.N T := by
  unfold Ncut; split_ifs
  · exact le_rfl
  · exact bot_le

set_option maxHeartbeats 2000000 in

def wn [FiniteDimensional Qp LL] (hO : Function.Injective (algebraMap O LL)) (C : CmpTie W E ιdR p1 tS zS)
    {zl : PowerSeries Zl →+* LetA O n}
    (hproj : ∀ T, @Module.Projective (PowerSeries Zl) _ ↥(W.N T) _ (Module.compHom _ zl)) :
    WN (et hO C) zl where
  N := Ncut W
  N_base := fun T h => by
    have := W.N_base T h
    rw [← Ncut_of h] at this
    exact this
  N_φ := fun T => by
    change ∀ x ∈ Ncut W T, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ Ncut W T
    by_cases h : IsCrys PD T.ρ
    · rw [Ncut_of h]; exact W.N_φ T
    · rw [Ncut_not h]
      intro x hx
      obtain rfl := (Submodule.mem_bot _).mp hx
      exact ⟨0, by rw [map_zero, smul_zero]; exact Submodule.zero_mem _⟩
  N_φinv := fun T => by
    change ∀ y ∈ Ncut W T, ∃ k : ℕ, W.Q ^ k • y ∈
      Submodule.span (LetA O n) (W.φD T '' (Ncut W T : Set (W.DD T)))
    by_cases h : IsCrys PD T.ρ
    · rw [Ncut_of h]; exact W.N_φinv T
    · rw [Ncut_not h]
      intro x hx
      obtain rfl := (Submodule.mem_bot _).mp hx
      exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  N_fg := fun T => by
    by_cases h : IsCrys PD T.ρ
    · rw [Ncut_of h]; exact W.N_fg T
    · rw [Ncut_not h]; exact Submodule.fg_bot
  N_Γ := fun T => by
    change ∀ (g : W.Gam), ∀ x ∈ Ncut W T, W.γD T g x ∈ Ncut W T
    by_cases h : IsCrys PD T.ρ
    · rw [Ncut_of h]; exact W.N_Γ T
    · rw [Ncut_not h]
      intro g x hx
      obtain rfl := (Submodule.mem_bot _).mp hx
      rw [map_zero]; exact Submodule.zero_mem _
  N_π := fun T => by
    change ∀ (g : W.Gam), ∀ x ∈ Ncut W T, ∃ y ∈ Ncut W T, W.γD T g x - x = (letπ : LetA O n) • y
    by_cases h : IsCrys PD T.ρ
    · rw [Ncut_of h]; exact W.N_π T
    · rw [Ncut_not h]
      intro g x hx
      obtain rfl := (Submodule.mem_bot _).mp hx
      exact ⟨0, Submodule.zero_mem _, by rw [map_zero, smul_zero, sub_zero]⟩
  map_N := fun f h h' => by
    rw [Ncut_of h, Ncut_of h']; exact W.map_N f h h'
  one_e := by
    have h : IsCrys PD W.one.ρ := GlobalTheory.TrivCrys.isCrys_lat_of_trivial W.one W.one_triv
    obtain ⟨e, e₀, h1, h2, h3⟩ := E.one_e
    exact ⟨e, e₀, h1, h2, (Ncut_of h).trans h3⟩
  N_proj := fun T => by
    change @Module.Projective (PowerSeries Zl) _ ↥(Ncut W T) _ (Module.compHom _ zl)
    by_cases h : IsCrys PD T.ρ
    · have := hproj T
      rw [← Ncut_of h] at this
      exact this
    · letI : Module (PowerSeries Zl) ↥(Ncut W T) := Module.compHom _ zl
      haveI : Subsingleton ↥(Ncut W T) := by rw [Ncut_not h]; infer_instance
      exact Module.Projective.of_free
  N_junk := fun T h => Ncut_not h

def inc (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : ↥(Ncut W T) →+ ↥(W.N T) :=
  (Submodule.inclusion (Ncut_le W T)).toAddMonoidHom

set_option maxHeartbeats 4000000 in

def cm [FiniteDimensional Qp LL] (hO : Function.Injective (algebraMap O LL)) (C : CmpTie W E ιdR p1 tS zS)
    {zl : PowerSeries Zl →+* LetA O n}
    (hproj : ∀ T, @Module.Projective (PowerSeries Zl) _ ↥(W.N T) _ (Module.compHom _ zl))
    (hz : ∀ (ι : LL →ₐ[Qp] BdR) (ζ : LL), ι ζ = zS → ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    WCmp (wn hO C hproj) ιdR p1 tS zS where
  cmp := fun T => (W.cmp T).comp (inc W T)
  cmp_smul := fun T c x => W.cmp_smul T c (inc W T x)
  cmp_π := fun T x => W.cmp_π T (inc W T x)
  cmp_mem := fun T x => W.cmp_mem T (inc W T x)
  cmp_letter := fun T i x => W.cmp_letter T i (inc W T x)
  cmp_map := fun {T T'} f h h' x hx => W.cmp_map f h h' (inc W T x) (Ncut_le W T' hx)
  levN := fun T i ζ => (W.levN T i (fixRoot PD.p ζ)).comp (inc W T)
  levN_supp := fun T i _ x => W.levN_supp T i _ (inc W T x)
  levN_smul := fun T i _ a x k => W.levN_smul T i _ a (inc W T x) k
  levN_map := fun {T T'} f h h' i _ x hx k => W.levN_map f h h' i _ (inc W T x) (Ncut_le W T' hx) k
  levB := fun T i ζ => (C.levB T i (fixRoot PD.p ζ)).comp (inc W T)
  levB_mem := fun T i _ x k => C.levB_mem T i _ (inc W T x) k
  levB_supp := fun T i _ x => C.levB_supp T i _ (inc W T x)
  levN_eq := fun T i _ x k => C.levN_eq T i _ (inc W T x) k
  cmp_eq := fun T h i x => by
    rw [fixRoot_one]
    exact C.cmp_eq T h i (inc W T x)
  levB_φ := fun T h i ζ hζ x m hx k => by
    have := C.levB_φ T h i ζ hζ (inc W T x) m (Ncut_le W T hx) k
    change _ = ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i (fixRoot PD.p ζ) (W.Q ^ m)) • _
    rw [fixRoot_of hζ, fixRoot_of (prim_pow PD.hp hζ _)]
    exact this
  levB_Γ := fun T h g i ζ ζ' j a hζ hv h' x hx k => by
    have := C.levB_Γ T h g i ζ ζ' j a hζ hv h' (inc W T x) (Ncut_le W T hx) k
    rw [fixRoot_of ⟨j, hζ⟩, fixRoot_of (h' ▸ prim_pow PD.hp ⟨j, hζ⟩ a)]
    exact this
  βdR := C.βdR
  βdR_tmul := C.βdR_tmul
  levN_dR := fun T h i ζ ι h1 h2 x => by
    rw [fixRoot_of (hz ι ζ h2)]
    exact C.levN_dR T h i ζ ι h1 h2 (inc W T x)

theorem exists_layers [FiniteDimensional Qp LL] (hO : Function.Injective (algebraMap O LL))
    (C : CmpTie W E ιdR p1 tS zS) {zl : PowerSeries Zl →+* LetA O n}
    (hproj : ∀ T, @Module.Projective (PowerSeries Zl) _ ↥(W.N T) _ (Module.compHom _ zl))
    (hz : ∀ (ι : LL →ₐ[Qp] BdR) (ζ : LL), ι ζ = zS → ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j))
    {s : ℕ} (hs : W.s = s) :
    ∃ (Γ : WGam PD LL O v n s) (R : WSer Γ) (I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA) (E' : WEt I)
      (Mo : WN E' zl), Γ.emb = W.emb ∧ I.io = E.io ∧ Nonempty (WCl E') ∧
        Nonempty (WCmp Mo ιdR p1 tS zS) := by
  subst hs
  exact ⟨gam W, ser C, io hO C, et hO C, wn hO C hproj, rfl, rfl, ⟨cl hO C⟩, ⟨cm hO C hproj hz⟩⟩

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow (P : LocPrime l) (s : ℕ) : P.ζQ s ^ (l ^ s) = 1 := by
  induction s with
  | zero => simpa using P.ζQ_zero
  | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

set_option maxHeartbeats 2000000 in

theorem layers_of_exists (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P) (F : LocFon l P AI H)
    (C : LocCmpT l P AI H F) (K : FinExt l) (s : ℕ) (LL : FinExt l) (g : Good K s LL) :
    Nonempty (Layers P AI K s LL) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : Nontrivial P.R.BdR := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (P.PD K).not_mem_filtration_two
    rw [Subsingleton.elim ((P.PD K).ι (P.PD K).t) 0]
    exact Submodule.zero_mem _
  obtain ⟨Γ, R, I, E', Mo, h1, h2, ⟨Cl⟩, ⟨Cm⟩⟩ :=
    exists_layers (O := ↥(OL LL)) Subtype.val_injective (C.C K s LL g).tie (H.W_proj K s LL g)
      (fun ι ζ h => by
        have h1 : ζ ^ (l ^ s) = 1 := by
          apply ι.toRingHom.injective
          change ι (ζ ^ (l ^ s)) = ι 1
          rw [map_pow, h, ← map_pow, zeta_pow, map_one, map_one]
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).mp (orderOf_dvd_of_pow_eq_one h1)
        refine ⟨k, ?_⟩
        rw [P.PD_p, ← hk]
        exact IsPrimitiveRoot.orderOf _)
      (H.W_s K s LL g)
  refine ⟨⟨Γ, R, I, ?_, E', Mo, Cl, Cm⟩⟩
  intro c m hm hl hc xb hx o ho
  rw [h2]
  exact (F.E K s LL g).inertia_action_on_roots c m hm hl hc xb hx o (fun i => by rw [ho, h1])

end Concrete

end GlobalTheory.HWL.Back
