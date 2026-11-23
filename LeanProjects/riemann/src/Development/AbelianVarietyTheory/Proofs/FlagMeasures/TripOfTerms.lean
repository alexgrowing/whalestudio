import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermIsometryGraphModScalarFlagPairIota
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDefiniteSpaceIsometryOfAdaptedPairStatement

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.TermPair
open GlobalTheory.ModIdent GlobalTheory.DegAsm.AdaptInv
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  {H : HermSpace K V} {r : ℕ}

theorem perp_lift [FiniteDimensional K V] {F G : FlagD H r} {Λ : Submodule (𝓞 K) V} {g : ℕ} (hg : 1 ≤ g)
    (hU : IsUnimod H Λ) (h : IsAdm G F Λ (g : 𝓞 K)) {l : V} (hl : l ∈ Λ) (hp : ∀ x ∈ G.X, H.B x l = 0) :
    ∃ m ∈ Λ, l - (g : K) • m ∈ perp H F.X := by
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hdiv : ∀ x : ↥(Λ ⊓ rs (𝓞 K) F.X), IsIntegral ℤ ((g : K)⁻¹ * H.B x l) := by
    rintro ⟨x, hxΛ, hxS⟩
    obtain ⟨x', -, h1, h2⟩ := h (Fin.last r) 0 x hxΛ (by
      rw [zero_smul, sub_zero]; exact hxS)
    obtain ⟨n, hn, hxn⟩ := (mem_smulLat g Λ _).1 h2
    rw [zero_smul, sub_zero] at h1
    have a1 := hp x' h1
    have a5 : H.B (x' - x) l = g * H.B n l := by rw [hxn]; simp
    obtain ⟨c, hc⟩ := integral_of_unimod hU hn hl
    have : (g : K)⁻¹ * H.B x l = ((-c : 𝓞 K) : K) := by
      rw [inv_mul_eq_iff_eq_mul₀ hg0]
      change _ = (g : K) * (-(c : K))
      rw [hc]
      simp only [map_sub, LinearMap.sub_apply] at a5
      linear_combination a1 - a5
    show IsIntegral ℤ ((g : K)⁻¹ * H.B x l)
    rw [this]
    exact (-c).isIntegral_coe
  let φ : ↥(Λ ⊓ rs (𝓞 K) F.X) →ₗ[𝓞 K] 𝓞 K :=
    { toFun := fun x => ⟨(g : K)⁻¹ * H.B x l, hdiv x⟩
      map_add' := fun a b => by
        apply RingOfIntegers.ext
        show (g : K)⁻¹ * H.B ((a : V) + b) l = (g : K)⁻¹ * H.B a l + (g : K)⁻¹ * H.B b l
        simp [mul_add]
      map_smul' := fun a b => by
        apply RingOfIntegers.ext
        show (g : K)⁻¹ * H.B (a • (b : V)) l = algebraMap (𝓞 K) K a * ((g : K)⁻¹ * H.B b l)
        rw [← algebraMap_smul K a, map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring }
  obtain ⟨m, hm, hφ⟩ := GlobalTheory.UnimodQuot.exists_lattice_rep H hU F.X φ
  refine ⟨m, hm, (mem_perp_iff H _ _).2 fun u hu => orth_symm ?_⟩
  obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem ((isLatMod_top_bot_iff Λ).1 hU.1) u
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hs' : algebraMap (𝓞 K) K s • u ∈ Λ := by rw [algebraMap_smul]; exact hs
  have e : H.B (algebraMap (𝓞 K) K s • u) m = (g : K)⁻¹ * H.B (algebraMap (𝓞 K) K s • u) l :=
    hφ ⟨_, hs', F.X.smul_mem _ hu⟩
  rw [eq_inv_mul_iff_mul_eq₀ hg0] at e
  apply mul_left_cancel₀ hs0
  simp only [map_sub, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_natCast,
    smul_eq_mul] at e ⊢
  linear_combination -e

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem mem_X_iff {F G : FlagD H r} {γ : V ≃ₗ[K] V} (hγ : ∀ a, G.e a = γ (F.e a)) (x : V) :
    γ x ∈ G.X ↔ x ∈ F.X := by
  have : G.X = F.X.map (γ : V →ₗ[K] V) := by
    unfold FlagD.X FlagD.Xa
    rw [Submodule.map_span, Set.image_image]
    simp only [hγ]
    rfl
  rw [this, Submodule.mem_map_equiv]
  simp

omit [NumberField K] [StarRing K] in
theorem mem_smul_iff (γ : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (x : V) : γ x ∈ γ • Λ ↔ x ∈ Λ := by
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := γ.injective e
    exact this ▸ hy
  · exact fun h => ⟨x, h, rfl⟩

omit [NumberField K] in

theorem mem_graph {F G : FlagD H r} {HW : HermSpace K W} {e : W →ₗ[K] V} (he : IsEmb F HW e)
    (hI : ∀ v ∈ F.X, (∀ w ∈ V0 F G, H.B v w = 0) → v ∈ G.X)
    (hlift : ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ V0 F G, H.B v (w - x) = 0)
    {γ : V ≃ₗ[K] V} {h : W ≃ₗ[K] W} (hγ : ∀ a, G.e a = γ (F.e a)) (hh : IsH F G e γ h) (g : ℕ)
    (Λ' : Submodule (𝓞 K) V) (w v : W) :
    (h w, v) ∈ (datOf F G e g (γ • Λ')).2 ↔
      ∃ x ∈ Λ', ∃ m ∈ γ • Λ', e w - x ∈ F.X ∧ e v - (γ x + (g : K) • m) ∈ F.X := by
  obtain ⟨y, hy, hy1, hy2⟩ := hh w
  have hy' : ∀ u ∈ V0 F G, H.B y u = 0 := (mem_perp_iff H _ _).1 hy
  constructor
  · intro hm
    have hm' : (e (h w), e v) ∈ iotaGraph F G (γ • Λ') (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X) := hm
    obtain ⟨⟨a, b⟩, hab, ⟨s, t⟩, ⟨hs, ht⟩, hst⟩ := Submodule.mem_sup.1 hm'
    obtain ⟨e1, e2⟩ := Prod.mk.inj hst
    have hs : s ∈ F.X := hs
    have ht : t ∈ F.X := ht
    obtain ⟨ha, -, l, hl, m, hm, h1, h2⟩ := (mem_iota F G _ g a b).1 hab
    have ha' := ((mem_perp_lattice_flag_iff G F _ a).1 ha).1
    rw [jointSpan_comm] at ha'
    have k1 : y - a ∈ G.X := by
      refine hI _ ?_ fun u hu => by simp [hy' u hu, ha' u hu]
      have := F.X.add_mem hy1 hs
      rw [← e1] at this
      convert this using 1; abel
    refine ⟨γ.symm l, by rw [← mem_smul_iff γ]; simpa using hl, m, hm, ?_, ?_⟩
    · rw [← mem_X_iff hγ, map_sub, LinearEquiv.apply_symm_apply]
      have := G.X.sub_mem (G.X.add_mem k1 h1) hy2
      convert this using 1; abel
    · rw [LinearEquiv.apply_symm_apply, ← e2]
      have := F.X.add_mem h2 ht
      convert this using 1; abel
  · rintro ⟨x, hx, m, hm, h1, h2⟩
    have hx' := (mem_smul_iff γ Λ' x).2 hx
    obtain ⟨s, hs, hb⟩ := hlift (e v) ((he.2 _).2 (Submodule.mem_sup_left ⟨v, rfl⟩))
    have k1 : y - γ x ∈ G.X := by
      have := G.X.add_mem hy2 ((mem_X_iff hγ _).2 h1)
      rw [map_sub] at this
      convert this using 1; abel
    have k2 : e v - s - (γ x + (g : K) • m) ∈ F.X := by
      have := F.X.sub_mem h2 hs
      convert this using 1; abel
    show (e (h w), e v) ∈ iotaGraph F G (γ • Λ') (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X)
    refine Submodule.mem_sup.2 ⟨(y, e v - s), (mem_iota F G _ g _ _).2 ⟨?_, ?_, γ x, hx', m, hm, k1, k2⟩,
      (-(y - e (h w)), s), ⟨F.X.neg_mem hy1, hs⟩, by simp⟩
    · exact (mem_perp_lattice_flag_iff G F _ _).2 ⟨by rw [jointSpan_comm]; exact hy', _, hx', k1⟩
    · exact (mem_perp_lattice_flag_iff F G _ _).2 ⟨fun u hu => orth_symm (hb u hu), _,
        Submodule.add_mem _ hx' (gsmul_mem g hm), k2⟩

theorem geom [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F G : FlagD H r} {𝔡 : Ideal (𝓞 K)} {N : NF H r}
    (hN : Adapt F G 𝔡 N) :
    (∀ v ∈ F.X, (∀ w ∈ V0 F G, H.B v w = 0) → v ∈ G.X) ∧
    (∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ V0 F G, H.B v (w - x) = 0) := by
  obtain ⟨-, h, h'⟩ := hN
  obtain ⟨-, -, -, h1, -, -, -, hl, -⟩ := (GlobalTheory.DegCnt.NF.geometry K V H hK r N).1
  rw [sitesCommonSpace_v0_eq_Vp h h'] at h1 hl
  rw [x_eq h] at hl
  refine ⟨fun v hv hw => ?_, fun w hw => hl w fun a => ?_⟩
  · have := ((h1 v (isotropicSpan_le_jointSpan_left F G hv)).1 hw).2
    rwa [x_eq h'] at this
  · have k : N.F.e a - F.e a ∈ F.X := xa_mono F (Nat.le_of_lt_succ a.2) (h a)
    have := orth_of_mem_X F (fun b => hw b.castSucc) k
    rw [map_sub, LinearMap.sub_apply, hw a, sub_zero] at this
    exact this

end GlobalTheory.DegAsm.TermPair

namespace GlobalTheory.DegAsm
open GlobalTheory.ModIdent TermPair

theorem trip_of_terms : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G G' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N N' : NF H r) (g : ℕ) (Λ Λ' : Submodule (𝓞 K) V) (γ γ' : V ≃ₗ[K] V) (h h' : W ≃ₗ[K] W), 1 ≤ g → IsEmb F HW e → Adapt F G 𝔡 N → Adapt F G' 𝔡 N' → N.IsTerm g Λ → N'.IsTerm g Λ → γ ∈ isomGrp H → γ' ∈ isomGrp H → (∀ a, G.e a = γ (F.e a) ∧ G'.e a = γ' (F.e a)) → γ • Λ' = Λ → γ' • Λ' = Λ → IsH F G e γ h → IsH F G' e γ' h' → (∀ x ∈ Λ ⊓ rs (𝓞 K) (perp H F.X), γ' (γ.symm x) - x ∈ smulLat (g : 𝓞 K) Λ ⊔ (Λ ⊓ rs (𝓞 K) F.X)) → (datOf F G e g Λ, datOf F G' e g Λ, h * h'⁻¹) ∈ Trip HW g (lat0 F e Λ) r (N.gI g Λ) (N'.gI g Λ) := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F G G' 𝔡 N N' g Λ Λ' γ γ' h h' hg he hN hN' hT hT' hγ hγ' hE
    hΛ hΛ' hh hh' hβ
  obtain ⟨k, hk, -, hku, hkl⟩ := GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair K V W H HW e hK r F G 𝔡 N γ he hN hγ fun a => (hE a).1
  obtain ⟨k', hk', -, hku', hkl'⟩ := GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair K V W H HW e hK r F G' 𝔡 N' γ' he hN' hγ' fun a => (hE a).2
  obtain rfl := hku h hh
  obtain rfl := hku' h' hh'
  have d1 := hkl g Λ'
  have d2 := hkl' g Λ'
  rw [hΛ] at d1
  rw [hΛ'] at d2
  obtain ⟨⟨hU, hF, hG⟩, hA⟩ :=
    ((adapt_invariants K V H hK r F G 𝔡 N hN).2.2.2.2.2.2.2.2 g Λ).1.1 hT
  have hA' : IsAdm G F Λ (g : 𝓞 K) := by
    refine isAdm_symm (fun a => ?_) hA
    refine Fin.lastCases ?_ (fun b => ?_) a
    · rw [hF.2, hG.2]
    · rw [hF.1, hG.1]
  have key : ∀ w : W, ∀ x ∈ Λ', e w - x ∈ F.X → ∃ n ∈ Λ, γ' x - γ x - (g : K) • n ∈ F.X := by
    intro w x hx hw
    have hxΛ : γ x ∈ Λ := hΛ ▸ (mem_smul_iff γ Λ' x).2 hx
    have hp : ∀ u ∈ G.X, H.B u (γ x) = 0 := by
      intro u hu
      obtain ⟨u, rfl⟩ := γ.surjective u
      rw [mem_X_iff fun a => (hE a).1] at hu
      rw [(mem_isomGrp H γ).1 hγ]
      have a1 := X_iso F hu hw
      have a2 := orth_of_mem_X F (fun b => (he.2 (e w)).2 (Submodule.mem_sup_left ⟨w, rfl⟩) b.castSucc) hu
      rw [map_sub, a2] at a1
      simpa using a1
    obtain ⟨m, hm, hmp⟩ := perp_lift hg hU hA' hxΛ hp
    obtain ⟨s, hs, t, ⟨-, ht⟩, hst⟩ := Submodule.mem_sup.1 (hβ _ ⟨Λ.sub_mem hxΛ (gsmul_mem g hm), hmp⟩)
    obtain ⟨n, hn, rfl⟩ := (mem_smulLat g Λ s).1 hs
    have hm' : γ' (γ.symm m) ∈ Λ := by
      rw [← hΛ', mem_smul_iff, ← mem_smul_iff γ, hΛ]
      simpa using hm
    refine ⟨n + γ' (γ.symm m) - m, Λ.sub_mem (Λ.add_mem hn hm') hm, ?_⟩
    have ht : t ∈ F.X := ht
    convert ht using 1
    simp only [map_sub, map_smul, LinearEquiv.symm_apply_apply] at hst
    rw [smul_sub, smul_add, eq_sub_of_add_eq' hst]
    abel
  refine ⟨(GlobalTheory.T.embeddedDatum_of_term_definiteSpace K V W H HW e hK r F G 𝔡 N g Λ hg he hN hT).1,
    (GlobalTheory.T.embeddedDatum_of_term_definiteSpace K V W H HW e hK r F G' 𝔡 N' g Λ hg he hN' hT').1, mul_mem hk (inv_mem hk'), ?_, fun y v => ?_⟩
  · show imLat (h * h'⁻¹) (datOf F G' e g Λ).1 = (datOf F G e g Λ).1
    rw [d1, d2]
    unfold imLat
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv]
  · obtain ⟨w, rfl⟩ := h'.surjective y
    have e1 := mem_graph he (geom hK hN).1 (geom hK hN).2 (fun a => (hE a).1) hh g Λ' w v
    have e2 := mem_graph he (geom hK hN').1 (geom hK hN').2 (fun a => (hE a).2) hh' g Λ' w v
    rw [hΛ] at e1
    rw [hΛ'] at e2
    have e3 : (h * h'⁻¹) (h' w) = h w := by simp
    show (h' w, v) ∈ (datOf F G' e g Λ).2 ↔ ((h * h'⁻¹) (h' w), v) ∈ (datOf F G e g Λ).2
    rw [e3, e1, e2]
    constructor
    · rintro ⟨x, hx, m, hm, h1, h2⟩
      obtain ⟨n, hn, h3⟩ := key w x hx h1
      refine ⟨x, hx, m + n, Λ.add_mem hm hn, h1, ?_⟩
      have := F.X.add_mem h2 h3
      convert this using 1
      rw [smul_add]; abel
    · rintro ⟨x, hx, m, hm, h1, h2⟩
      obtain ⟨n, hn, h3⟩ := key w x hx h1
      refine ⟨x, hx, m - n, Λ.sub_mem hm hn, h1, ?_⟩
      have := F.X.sub_mem h2 h3
      convert this using 1
      rw [smul_sub]; abel

end GlobalTheory.DegAsm
