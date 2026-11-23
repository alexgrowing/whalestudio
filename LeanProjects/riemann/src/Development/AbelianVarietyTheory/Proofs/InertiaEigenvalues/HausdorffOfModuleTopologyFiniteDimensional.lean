import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorProperties

noncomputable section

namespace GlobalTheory.HerrNatural

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem hausdorff_of_module_topology_finite_dimensional (L V : Type) [Field L] [TopologicalSpace L] [IsTopologicalRing L]
    [T2Space L] [AddCommGroup V] [Module L V] [TopologicalSpace V] [IsModuleTopology L V]
    [FiniteDimensional L V] : T2Space V := by
  let b := Module.finBasis L V
  exact T2Space.of_injective_continuous (f := b.equivFun) b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)

theorem cocycle_eq_zero {G L V : Type} [Group G] [TopologicalSpace G] [Field L] [AddCommGroup V]
    [Module L V] [TopologicalSpace V] [T2Space V] (ρ : Representation L G V) (d : G → V)
    (hc : Continuous d) (hd : ∀ g h, d (g * h) = d g + ρ g (d h)) (H : Set G) (γ : G)
    (hH : ∀ h ∈ H, d h = 0) (hγ : d γ = 0)
    (hdense : Dense {x | ∃ h ∈ H, ∃ a : ℕ, x = h * γ ^ a}) : d = 0 := by
  have h1 : d 1 = 0 := by
    have := hd 1 1
    simpa using this
  have hpow : ∀ a : ℕ, d (γ ^ a) = 0 := by
    intro a
    induction a with
    | zero => simpa using h1
    | succ a ih => rw [pow_succ, hd, ih, hγ, map_zero, add_zero]
  refine Continuous.ext_on hdense hc continuous_const ?_
  rintro x ⟨h, hh, a, rfl⟩
  rw [hd, hH h hh, hpow, map_zero, add_zero]
  rfl

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def oneTensor (R : Type) [CommRing R] [Algebra O R] {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) :
    TW R T →ₗ[O] TW R T' :=
  TensorProduct.map (LinearMap.id : R →ₗ[O] R) ((f.f.restrictScalars O).restrict f.T_le)

theorem oneTensor_map {R : Type} [CommRing R] [Algebra O R] {T T' : LocLat G Qp LL O}
    (f : LatHom T.L T'.L) (φ : R →ₐ[O] R) (x : TW R T) :
    oneTensor R f (TWmap φ T x) = TWmap φ T' (oneTensor R f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [oneTensor, TWmap]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem oneTensor_act {R : Type} [CommRing R] [Algebra O R] {T T' : LocLat G Qp LL O}
    (f : LatHom T.L T'.L) (φ : R →ₐ[O] R) (g : G) (x : TW R T) :
    oneTensor R f (TWact φ T g x) = TWact φ T' g (oneTensor R f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    simp only [oneTensor, TWact, TensorProduct.map_tmul]
    congr 1
    exact Subtype.ext (f.equiv g t)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem one_tmul_inj {R : Type} [CommRing R] [Algebra O R] (hR : Function.Injective (algebraMap O R))
    (T : LocLat G Qp LL O) (t t' : ↥T.L.T) (h : (1 : R) ⊗ₜ[O] t = (1 : R) ⊗ₜ[O] t') : t = t' := by
  haveI := T.L.free
  have hi := Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T)
    (Algebra.linearMap O R) hR
  have : (1 : O) ⊗ₜ[O] t = (1 : O) ⊗ₜ[O] t' := hi (by simpa using h)
  simpa using congrArg (TensorProduct.lid O ↥T.L.T) this

theorem clNat_of_tie {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW]
    [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)}
    {πA : RA} (E : EtTie W RA RW inclR φR gR πA)
    (hR : Function.Injective (algebraMap O RW))
    (hT2 : ∀ T : LocLat G Qp LL O, T2Space T.V)
    (hsurj : ∀ (T : LocLat G Qp LL O) (x : TW RW T), ∃ b, TWmap φR T b - b = x)
    (γ : ↥W.GKs) (hγ : W.resΓ (γ : G) = W.gam)
    (hdense : Dense {x : ↥W.GKs | ∃ h ∈ {h : ↥W.GKs | W.resΓ (h : G) = 1}, ∃ a : ℕ, x = h * γ ^ a}) :
    W.ClNat := by
  intro T T' f pr pr' hpr
  haveI := hT2 T'
  obtain ⟨b, hb⟩ := hsurj T (E.jD T (pr : W.DD T × W.DD T).1)
  have hb' : TWmap φR T' (oneTensor RW f b) - oneTensor RW f b =
      E.jD T' (pr' : W.DD T' × W.DD T').1 := by
    rw [hpr, E.jD_map, ← oneTensor_map, ← map_sub, hb]
    rfl
  obtain ⟨c, hc, hcv⟩ := E.cl_def T pr b hb
  obtain ⟨c', hc', hcv'⟩ := E.cl_def T' pr' _ hb'
  rw [← hc, ← hc']
  let c₁ : ↥(latticeCocycles (resLat T' W.GKs)) :=
    ⟨(resHom f W.GKs).post c, (resHom f W.GKs).post_Z1T c c.2⟩
  have key : c₁ = c' := by
    have hd := (c₁ - c').2
    have hz := cocycle_eq_zero (T'.ρ.comp W.GKs.subtype) _ hd.1.1 hd.1.2
      {h : ↥W.GKs | W.resΓ (h : G) = 1} γ ?_ ?_ hdense
    · exact sub_eq_zero.1 (Subtype.ext hz)
    · intro g hg
      have h1 := (hcv g ⟨_, c.2.2 g (Set.mem_univ _)⟩ rfl).1 hg
      have h2 := (hcv' g ⟨_, c'.2.2 g (Set.mem_univ _)⟩ rfl).1 hg
      have h3 := congrArg (oneTensor RW f) h1
      rw [map_neg, map_sub, oneTensor_act, ← h2] at h3
      have h4 := one_tmul_inj hR T' _ _ h3
      exact sub_eq_zero.2 (congrArg Subtype.val h4)
    · have h1 := (hcv γ ⟨_, c.2.2 γ (Set.mem_univ _)⟩ rfl).2 hγ
      have h2 := (hcv' γ ⟨_, c'.2.2 γ (Set.mem_univ _)⟩ rfl).2 hγ
      have h3 := congrArg (oneTensor RW f) h1
      have h5 : oneTensor RW f (E.jD T (pr : W.DD T × W.DD T).2) =
          E.jD T' (pr' : W.DD T' × W.DD T').2 := by
        rw [hpr, E.jD_map]
        rfl
      rw [map_sub, map_sub, oneTensor_act, h5, ← h2] at h3
      have h4 := one_tmul_inj hR T' _ _ h3
      exact sub_eq_zero.2 (congrArg Subtype.val h4)
  rw [← key]
  rfl

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime]

theorem zl_wcb_injective : Function.Injective (algebraMap ℤ_[l] (WCb l)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.1 hx with h | h
  · exact ((PadicInt.unitCoeff h0).isUnit.map _).ne_zero h
  · exact WittVector.p_nonzero l (Cb l) (eq_zero_of_pow_eq_zero h)

theorem ol_rw_injective (LL : FinExt l) : Function.Injective (algebraMap ↥(OL LL) (RW LL)) := by
  haveI : Module.Flat ℤ_[l] ↥(OL LL) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, hx⟩
    have hx' : algebraMap ℤ_[l] ↥LL.1 a * (x : ↥LL.1) = 0 := by
      have := congrArg Subtype.val hx
      simpa [Algebra.smul_def] using this
    have ha' : algebraMap ℤ_[l] ↥LL.1 a ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
      have : a ≠ 0 := nonZeroDivisors.ne_zero ha
      simpa using this
    exact Subtype.ext ((mul_eq_zero.1 hx').resolve_left ha')
  exact Algebra.TensorProduct.includeLeft_injective (S := ↥(OL LL)) zl_wcb_injective

theorem le_v_iff (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (k : ℕ) :
    (k : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ↔ ‖x‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlR : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  obtain ⟨y, rfl⟩ : ∃ y, x = (l : ℚ_[l]) ^ k * y := ⟨((l : ℚ_[l]) ^ k)⁻¹ * x, by field_simp⟩
  have h1 : 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 y) ↔ ‖y‖ ≤ 1 := by
    rw [P.v_O]
    change IsIntegral ℤ_[l] _ ↔ _
    rw [isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective,
      IsIntegrallyClosed.isIntegral_iff]
    constructor
    · rintro ⟨z, rfl⟩
      exact z.2
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have h2 : P.v LL (algebraMap ℚ_[l] ↥LL.1 ((l : ℚ_[l]) ^ k * y)) =
      (k : WithTop ℚ) + P.v LL (algebraMap ℚ_[l] ↥LL.1 y) := by
    rw [map_mul, map_pow, map_natCast, AddValuation.map_mul, AddValuation.map_pow, P.v_l]
    simp
  rw [h2, norm_mul, Padic.norm_p_pow, mul_le_iff_le_one_right (zpow_pos hlR _), ← h1]
  have hk : (k : WithTop ℚ) ≠ ⊤ := WithTop.natCast_ne_top k
  conv_lhs => lhs; rw [← add_zero (k : WithTop ℚ)]
  exact WithTop.add_le_add_iff_left hk

theorem norm_eq_of_v_eq (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (k : ℕ)
    (h : P.v LL (algebraMap ℚ_[l] ↥LL.1 x) = (k : WithTop ℚ)) : ‖x‖ = (l : ℝ) ^ (-(k : ℤ)) := by
  refine le_antisymm ((le_v_iff P LL x k).1 h.ge) ?_
  by_contra hlt
  push_neg at hlt
  have h1 : ‖x‖ ≤ (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
    rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]
    simpa using hlt
  have h2 := (le_v_iff P LL x (k + 1)).2 h1
  rw [h] at h2
  have : k + 1 ≤ k := by exact_mod_cast h2
  omega

set_option maxHeartbeats 1000000 in

theorem exists_lift_dense (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (hact : IsActC act)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (hs : W.s = s) :
    ∃ γ : ↥W.GKs, W.resΓ (γ : ↥(GK K)) = W.gam ∧
      Dense {x : ↥W.GKs | ∃ h ∈ {h : ↥W.GKs | W.resΓ (h : ↥(GK K)) = 1}, ∃ a : ℕ, x = h * γ ^ a} := by
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have hb := (GlobalTheory.Cyc.cyc_basic l P.χQ hχ).2.2 K
  have hK0 : ∀ g : ↥(GK K), (g : GQ l) ∈ (K0 K).fixingSubgroup := fun g x => g.2 ⟨x.1, x.2.1⟩
  have hGj : ∀ g : GQ l, g ∈ Gj K s → g ∈ GK K := fun g hg x => hg ⟨x.1, h.2.2.1 x.2⟩
  have hmap : ∀ g : ↥(GK K), algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) - 1 =
      algebraMap ℚ_[l] ↥LL.1 ((P.χQ g : ℚ_[l]) - 1) := by
    intro g
    rw [P.PD_χ, map_sub, map_one]
  have hmem : ∀ g : ↥(GK K), g ∈ W.GKs ↔ (g : GQ l) ∈ Gj K s := by
    intro g
    rw [W.GKs_def, hmap, hs, le_v_iff, (hb g (hK0 g)).1]
  obtain ⟨g, hg⟩ := W.resΓ_onto W.gam
  have hv : P.v LL (algebraMap ℚ_[l] ↥LL.1 ((P.χQ g : ℚ_[l]) - 1)) = (s : WithTop ℚ) := by
    rw [← hmap, ← W.χΓ_res, hg, W.gam_gen, hs]
  have hn := norm_eq_of_v_eq P LL _ s hv
  have hgj : (g : GQ l) ∈ Gj K s := ((hb g (hK0 g)).1 s).2 hn.le
  have hd := ((GlobalTheory.Cyc.gen_dense l act P.χQ hact hχ K s ⟨h.1, h.2.1⟩).2 g ⟨hgj, hn⟩).2.2
  refine ⟨⟨g, (hmem g).2 hgj⟩, hg, fun x => ?_⟩
  let ι : ↥W.GKs → GQ l := fun y => ((y : ↥(GK K)) : GQ l)
  have hι : Topology.IsInducing ι := Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  rw [hι.closure_eq_preimage_closure_image]
  refine closure_mono ?_ (hd ((hmem x).1 x.2))
  rintro y ⟨η, hη, a, rfl⟩
  have hη0 : η ∈ (K0 K).fixingSubgroup := fun x => hη ⟨x.1, (le_sup_left : K0 K ≤ Kinf K) x.2⟩
  have hη1 : P.χQ η = 1 := (hb η hη0).2.1 hη
  have hηj : η ∈ Gj K s := ((hb η hη0).1 s).2 (by
    rw [hη1]
    simp)
  let η' : ↥W.GKs := ⟨⟨η, hGj η hηj⟩, (hmem _).2 hηj⟩
  refine ⟨η' * ⟨g, (hmem g).2 hgj⟩ ^ a, ⟨η', ?_, a, rfl⟩, rfl⟩
  apply W.χΓ_inj
  rw [map_one]
  apply Units.ext
  apply Subtype.ext
  have := W.χΓ_res (η' : ↥(GK K))
  rw [P.PD_χ] at this
  change _ = algebraMap ℚ_[l] ↥LL.1 (P.χQ η : ℚ_[l]) at this
  rw [hη1, Units.val_one, map_one] at this
  exact this

end Concrete

set_option maxHeartbeats 1000000 in

theorem clNat : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm9 D HW F →
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    let S := sit D.loc HW l (D.locA l) K s LL h
    let _E : S.Comparison₂ := ((F l).E K s LL h).tie
    S.W.ClNat := by
  intro D HW F h9 l _ K s LL h S E
  obtain ⟨γ, hγ, hd⟩ := exists_lift_dense (D.loc l) K s LL h (D.locA l).actC
    ⟨(D.locA l).actC_ext, (D.locA l).actC_norm⟩ ((HW l).W K s LL h) ((HW l).W_s K s LL h)
  change ((HW l).W K s LL h).ClNat
  refine clNat_of_tie ((F l).E K s LL h).tie (ol_rw_injective LL)
    (fun T => hausdorff_of_module_topology_finite_dimensional ↥LL.1 T.V) (fun T x => ?_) γ hγ hd
  obtain ⟨b, -, hb⟩ := ((h9 l K s LL h).1 T).1 x trivial
  exact ⟨b, hb⟩

end GlobalTheory.HerrNatural
