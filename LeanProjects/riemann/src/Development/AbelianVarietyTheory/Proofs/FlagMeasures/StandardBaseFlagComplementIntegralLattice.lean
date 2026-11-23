import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeLatIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice

namespace GlobalTheory.LoopC.Base

section General

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [NumberField K] [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem idxN_of_gen {D M : Submodule (𝓞 K) V} {w : V} (hw : w ∈ D) (J : Ideal (𝓞 K))
    (h1 : ∀ a : 𝓞 K, a • w ∈ M ↔ a ∈ J) (h2 : ∀ y ∈ D, ∃ a : 𝓞 K, y - a • w ∈ M) :
    idxN D M = Nat.card (𝓞 K ⧸ J) := by
  let φ : 𝓞 K →ₗ[𝓞 K] (↥D ⧸ M.comap D.subtype) :=
    (M.comap D.subtype).mkQ ∘ₗ LinearMap.toSpanSingleton (𝓞 K) D ⟨w, hw⟩
  have hs : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := (M.comap D.subtype).mkQ_surjective q
    obtain ⟨a, ha⟩ := h2 y y.2
    exact ⟨a, ((Submodule.Quotient.eq (M.comap D.subtype)).2
      (show y - a • (⟨w, hw⟩ : D) ∈ M.comap D.subtype from ha)).symm⟩
  have hk : LinearMap.ker φ = J := by
    ext a
    rw [LinearMap.mem_ker, ← h1]
    exact Submodule.Quotient.mk_eq_zero _
  exact Nat.card_congr
    ((φ.quotKerEquivOfSurjective hs).symm.trans (Submodule.quotEquivOfEq _ _ hk)).toEquiv

variable [FiniteDimensional K V]

theorem exists_rep (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate) {Λ : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K Λ) (hU : IsUnimodular h Λ) (U : Submodule K V) (f : V →ₗ[K] K)
    (hf : ∀ y ∈ Λ, y ∈ U → f y ∈ (1 : Submodule (𝓞 K) K)) : ∃ l ∈ Λ, ∀ y ∈ U, h l y = f y := by
  let H : Formalism.HermitianLatticeCounting.S6.HermSpace K V :=
    { B := h.flip
      herm := fun x y => hs.eq y x
      nondeg := fun x hx => hn.2 x hx }
  have hH : GlobalTheory.HermLat.IsUnimod H Λ := (GlobalTheory.HermLat.isUnimod_iff H Λ).2 ⟨hL, hU⟩
  have hx : ∀ x : ↥(Λ ⊓ GlobalTheory.HermLat.rs (𝓞 K) U), IsIntegral ℤ (f x) := fun x =>
    (GlobalTheory.UnimodQuot.mem_one_iff _).1 (hf _ x.2.1 x.2.2)
  let φ : ↥(Λ ⊓ GlobalTheory.HermLat.rs (𝓞 K) U) →ₗ[𝓞 K] 𝓞 K :=
    { toFun := fun x => ⟨f x, hx x⟩
      map_add' := fun a b => by
        apply RingOfIntegers.ext
        show f ((a : V) + b) = f a + f b
        simp
      map_smul' := fun a b => by
        apply RingOfIntegers.ext
        show f (a • (b : V)) = algebraMap (𝓞 K) K a * f b
        rw [← algebraMap_smul K a, map_smul]
        rfl }
  obtain ⟨l, hl, h'⟩ := GlobalTheory.UnimodQuot.exists_lattice_rep H hH U φ
  refine ⟨l, hl, fun y hy => ?_⟩
  obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem hL y
  have h0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hs' : algebraMap (𝓞 K) K s • y ∈ Λ := by rw [algebraMap_smul]; exact hs
  have h1 : h l (algebraMap (𝓞 K) K s • y) = f (algebraMap (𝓞 K) K s • y) := h' ⟨_, hs', U.smul_mem _ hy⟩
  rw [map_smul, map_smul] at h1
  exact smul_right_injective K h0 h1

variable {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] [FiniteDimensional K W]

set_option maxHeartbeats 1000000 in

theorem perp_lattice (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate) {Λ : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K Λ) (hU : IsUnimodular h Λ)
    (hW : W →ₗ⋆[K] W →ₗ[K] K) (hsW : hW.IsSymm) (hnW : hW.Nondegenerate) (ι : W →ₗ[K] V)
    (hι : ∀ a b, h (ι a) (ι b) = hW a b) (X : Submodule K V) (z : V) (T : ℕ) (hT : T ≠ 0)
    (hXX : ∀ x ∈ X, ∀ y ∈ X, h x y = 0) (hXz : ∀ x ∈ X, h x z = 0) (hXW : ∀ x ∈ X, ∀ w, h x (ι w) = 0)
    (hzW : ∀ w, h z (ι w) = 0) (hzz : h z z = -(T : K)) (hz : z ∈ Λ)
    (hdec : ∀ v, (∀ x ∈ X, h x v = 0) → h z v = 0 → ∃ w, ∃ x ∈ X, v = ι w + x)
    (hprim : ∀ c : K, ∀ x ∈ X, c • z + x ∈ Λ → ∃ o : 𝓞 K, (o : K) = c)
    (L : Submodule (𝓞 K) W) (hmem : ∀ w, w ∈ L ↔ ∃ x ∈ X, ι w + x ∈ Λ) :
    Submodule.IsLattice K L ∧ IsIntegralLat hW L ∧ idxN (dual hW L) L = T ^ Module.finrank ℚ K := by
  have hT0 : (T : K) ≠ 0 := by exact_mod_cast hT
  have sw : ∀ {x y : V}, h x y = 0 → h y x = 0 := fun {x y} e => by rw [← hs.eq, e, map_zero]
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, h x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx y hy =>
    (dualBasic_mem_dual _ _ _).1 (hU.symm ▸ hy : y ∈ dual h Λ) x hx
  have prod : ∀ (a b : W) (c : K), ∀ x ∈ X, ∀ y ∈ X, h (ι a + x) (ι b + c • z + y) = hW a b := by
    intro a b c x hx y hy
    simp [hι, hXX x hx y hy, hXz x hx, hXW x hx, sw (hXW y hy a), sw (hzW a)]
  have hI : IsIntegralLat hW L := by
    intro a ha b hb
    obtain ⟨x, hx, ha⟩ := (hmem a).1 ha
    obtain ⟨y, hy, hb⟩ := (hmem b).1 hb
    have := prod a b 0 x hx y hy
    rw [zero_smul, add_zero] at this
    exact this ▸ hint _ ha _ hb
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    refine (Submodule.mem_bot _).2 (hnW.2 x fun y => ?_)
    rw [← hι, LinearMap.mem_ker.1 hx, map_zero]
  have hL1 : Submodule.IsLattice K (Λ.comap (ι.restrictScalars (𝓞 K))) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.fg_of_fg_map_injective (ι.restrictScalars (𝓞 K)) hinj ?_
      exact Submodule.FG.of_le hL.fg (Submodule.map_comap_le _ _)
    · rw [eq_top_iff]
      intro u _
      obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem hL (ι u)
      have h0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      refine (Submodule.smul_mem_iff _ h0).1 (Submodule.subset_span ?_)
      show ι (algebraMap (𝓞 K) K s • u) ∈ Λ
      rw [map_smul, algebraMap_smul]; exact hs
  have hle1 : Λ.comap (ι.restrictScalars (𝓞 K)) ≤ L := fun w hw =>
    (hmem w).2 ⟨0, X.zero_mem, by rw [add_zero]; exact hw⟩
  have hst : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := fun r =>
    Submodule.mem_one.1 (GlobalTheory.UnimodQuot.star_mem_one (Submodule.mem_one.2 ⟨r, rfl⟩))
  have hLat : Submodule.IsLattice K L := by
    refine ⟨?_, ?_⟩
    · refine Submodule.FG.of_le (dualLattice (𝓞 K) K W hW hsW hnW hst _ hL1).1.fg fun w hw => ?_
      exact (dualBasic_mem_dual _ _ _).2 fun y hy => hI y (hle1 hy) w hw
    · rw [eq_top_iff, ← hL1.span_eq_top]
      exact Submodule.span_mono hle1
  refine ⟨hLat, hI, ?_⟩
  have dec : ∀ l, (∀ x ∈ X, h x l = 0) → ∃ w, ∃ x ∈ X, l = ι w + (-(h z l) * (T : K)⁻¹) • z + x := by
    intro l hl
    obtain ⟨w, x, hx, e⟩ := hdec (l + (h z l * (T : K)⁻¹) • z)
      (fun x hx => by simp [hl x hx, hXz x hx]) (by simp [hzz]; field_simp; ring)
    refine ⟨w, x, hx, ?_⟩
    rw [add_right_comm, ← e, neg_mul, neg_smul]; abel
  obtain ⟨l0, hl0, h0⟩ := exists_rep h hs hn hL hU (X ⊔ Submodule.span K {z}) ((-(T : K)⁻¹) • h z) (by
    intro y hy hy'
    obtain ⟨x, hx, y', hy2, rfl⟩ := Submodule.mem_sup.1 hy'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy2
    obtain ⟨o, ho⟩ := hprim c x hx (by rwa [add_comm])
    refine Submodule.mem_one.2 ⟨o, ?_⟩
    have : algebraMap (𝓞 K) K o = c := ho
    simp [this, hzz, sw (hXz x hx)]
    field_simp)
  have h01 : h z l0 = 1 := by
    rw [← hs.eq, h0 z (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))]
    simp [hzz, hT0]
  obtain ⟨w0, x0, hx0, e0⟩ := dec l0 fun x hx => sw (by
    rw [h0 x (Submodule.mem_sup_left hx)]; simp [sw (hXz x hx)])
  rw [h01] at e0
  rw [idxN_of_gen (w := w0) ?_ (Ideal.span {(T : 𝓞 K)}) ?_ ?_, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  · refine (dualBasic_mem_dual _ _ _).2 fun a ha => ?_
    obtain ⟨x, hx, ha⟩ := (hmem a).1 ha
    rw [← prod a w0 _ x hx x0 hx0, ← e0]
    exact hint _ ha _ hl0
  · intro a
    have e1 : ∀ x, ι (a • w0) + x = a • l0 + ((algebraMap (𝓞 K) K a * (T : K)⁻¹) • z +
        (x - algebraMap (𝓞 K) K a • x0)) := by
      intro x
      rw [e0, ← algebraMap_smul K a w0, ← algebraMap_smul K a, map_smul]
      module
    rw [hmem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨x, hx, e⟩
      rw [e1, Λ.add_mem_iff_right (Λ.smul_mem a hl0)] at e
      obtain ⟨o, ho⟩ := hprim _ _ (X.sub_mem hx (X.smul_mem _ hx0)) e
      refine ⟨o, IsFractionRing.injective (𝓞 K) K ?_⟩
      have : algebraMap (𝓞 K) K o = _ := ho
      rw [map_mul, this, map_natCast]
      field_simp
    · rintro ⟨o, rfl⟩
      refine ⟨_, X.smul_mem (algebraMap (𝓞 K) K (o * T)) hx0, ?_⟩
      rw [e1, sub_self, add_zero, map_mul, map_natCast, mul_assoc, mul_inv_cancel₀ hT0, mul_one, algebraMap_smul]
      exact Λ.add_mem (Λ.smul_mem _ hl0) (Λ.smul_mem _ hz)
  · intro w hw
    obtain ⟨l, hl, h1⟩ := exists_rep h hs hn hL hU (LinearMap.range ι ⊔ X) (h (ι w)) (by
      intro y hy hy'
      obtain ⟨_, ⟨a, rfl⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hy'
      rw [map_add, sw (hXW x hx w), add_zero, hι, ← hsW.eq]
      exact GlobalTheory.UnimodQuot.star_mem_one ((dualBasic_mem_dual _ _ _).1 hw a ((hmem a).2 ⟨x, hx, hy⟩)))
    obtain ⟨w', x, hx, e⟩ := dec l fun x hx => sw (by
      rw [h1 x (Submodule.mem_sup_right hx), sw (hXW x hx w)])
    have hww : w' = w := by
      refine sub_eq_zero.1 (hnW.2 _ fun a => ?_)
      have a1 := h1 (ι a) (Submodule.mem_sup_left ⟨a, rfl⟩)
      have a2 := prod a w' (-(h z l) * (T : K)⁻¹) 0 X.zero_mem x hx
      rw [← e, add_zero, ← hs.eq, a1, hs.eq, hι] at a2
      rw [map_sub, a2, sub_self]
    subst hww
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hint z hz l hl)
    refine ⟨c, (hmem _).2 ⟨x - algebraMap (𝓞 K) K c • x0, X.sub_mem hx (X.smul_mem _ hx0), ?_⟩⟩
    have : ι (w' - c • w0) + (x - algebraMap (𝓞 K) K c • x0) = l - c • l0 := by
      rw [← hc] at e
      rw [e, e0, ← algebraMap_smul K c w0, ← algebraMap_smul K c, map_sub, map_smul]
      module
    rw [this]
    exact Λ.sub_mem hl (Λ.smul_mem _ hl0)

end General

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder in

theorem baseFlagComplement_posDef (D : D7) : IsPosDef (D.sp.X 0).hT := by
  intro τ x hx
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have h1 := D.sp.X_sig 0 τ
  rw [Formalism.BasicNotions.baseSpace_posDef D.R D.host.F D.sp τ] at h1
  have h2 := GlobalTheory.DefiniteQuotient.posDef_of_signature h1
  have hv : (fun a => τ ((D.sp.X 0).frame.repr x a)) ≠ 0 := by
    intro e
    apply hx
    refine (D.sp.X 0).frame.repr.map_eq_zero_iff.1 (Finsupp.ext fun a => ?_)
    exact τ.injective ((congrFun e a).trans (map_zero τ).symm)
  have h3 := h2.re_dotProduct_pos hv
  refine lt_of_lt_of_eq h3 ?_
  rw [Formalism.BasicNotions.hT_expand]
  change Complex.re _ = _
  congr 1
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hτ, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, mul_assoc]
  rfl

theorem main : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → WHyp D (lf D F0) (Wsp D) ∧ Function.Injective (D.sp.iXY 0) ∧ IsPosDef (D.sp.X 0).hT ∧ Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)) ∧ Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (L0X D Λ (lf D F0)) ∧ detW D (L0X D Λ (lf D F0)) = NT D u ∧ Wb D = Wsp D ⊔ Submodule.span D.host.E {D.zmOf u} := by
  intro D u u' F0 Λ hS' ⟨he, hz⟩ ⟨_, ⟨hL, hU, hlift, hconv⟩, _⟩
  have hT : Tu D u ≠ 0 := hS'.2.1.ne_zero
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hT
  have hWH := Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  have hiso := D.sp.iXY_isom 0 hm
  have hinj : Function.Injective (D.sp.iXY 0) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    refine (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))
    rw [← hiso y x, LinearMap.mem_ker.1 hx, map_zero]
  have hXX : ∀ x ∈ F0.X, ∀ y ∈ F0.X, (hS D).hT x y = 0 := fun x hx y hy =>
    Formalism.MainNotions.hT_swap_zero ((Formalism.MainNotions.mem_orth_iff _ _).1 (Formalism.MainNotions.X_le_orth_Xplus F0 hx) y (Submodule.mem_sup_left hy))
  have hXz : ∀ x ∈ F0.X, (hS D).hT x F0.z = 0 := Formalism.MainNotions.hT_zero_of_mem_X F0 F0.z_orth
  have hWo : ∀ w, ∀ x ∈ F0.Xplus, (hS D).hT x (D.sp.iXY 0 w) = 0 := fun w =>
    (Formalism.MainNotions.mem_orth_iff _ _).1 (hWH.1.le (Submodule.mem_sup_left ⟨w, rfl⟩))
  have hXW : ∀ x ∈ F0.X, ∀ w, (hS D).hT x (D.sp.iXY 0 w) = 0 := fun x hx w => hWo w x (Submodule.mem_sup_left hx)
  have hzW : ∀ w, (hS D).hT F0.z (D.sp.iXY 0 w) = 0 := fun w =>
    hWo w _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hdec : ∀ v, (∀ x ∈ F0.X, (hS D).hT x v = 0) → (hS D).hT F0.z v = 0 →
      ∃ w, ∃ x ∈ F0.X, v = D.sp.iXY 0 w + x := by
    intro v h1 h2
    have : v ∈ orth (hS D) F0.Xplus := (Formalism.MainNotions.mem_orth_iff _ _).2
      (Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun a => h1 _ (Submodule.subset_span ⟨a, rfl⟩)) h2)
    obtain ⟨_, ⟨w, rfl⟩, x, hx, e⟩ := Submodule.mem_sup.1 (hWH.1.ge this)
    exact ⟨w, x, hx, e.symm⟩
  have hsub : ∀ v, (∀ x ∈ F0.X, (hS D).hT x v = 0) → (v ∈ Lsub Λ (lf D F0) ↔ ∃ x ∈ F0.X, v + x ∈ Λ) := by
    intro v hv
    constructor
    · rintro ⟨h1, -⟩
      obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 h1
      exact ⟨-x, F0.X.neg_mem hx, by simpa using hl.1⟩
    · rintro ⟨x, hx, h1⟩
      refine ⟨Submodule.mem_sup.2 ⟨v + x, ⟨h1, (Formalism.MainNotions.mem_orth_iff _ _).2 fun y hy => ?_⟩, -x, F0.X.neg_mem hx,
        by abel⟩, (Formalism.MainNotions.mem_orth_iff _ _).2 hv⟩
      rw [map_add, hv y hy, hXX y hy x hx, add_zero]
  obtain ⟨a1, a2, a3⟩ := perp_lattice (hS D).hT (hS D).herm (hS D).nondeg hL hU (D.sp.X 0).hT (D.sp.X 0).herm
    (D.sp.X 0).nondeg (D.sp.iXY 0) hiso F0.X F0.z (Tu D u) hT hXX hXz hXW hzW F0.z_norm hlift.1 hdec
    (fun c x hx h => hconv.2 c ((hsub _ fun y hy => by simp [hXz y hy]).2 ⟨x, hx, h⟩))
    (L0X D Λ (lf D F0)) (fun w => by
      rw [← hsub _ fun x hx => hXW x hx w]
      exact ⟨fun h => h.1, fun h => ⟨h, hzW w⟩⟩)
  refine ⟨hWH, hinj, baseFlagComplement_posDef D, a1, a2, ?_, ?_⟩
  · have hd : dualInH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
      unfold dualInH
      rw [a1.span_eq_top]
      simp
    have hf : Module.finrank ℚ D.host.E = D.R.f * 2 := by
      rw [D.host.finrank_cmField]
      unfold Ranks.f Ranks.n
      ring
    rw [detW, latDetH, hd, GlobalTheory.Mass.DetAgree.genIdxH_eq_idxN
      (fun x hx => (Formalism.HermitianLatticesTheory.dualBasic_mem_dual _ _ _).2 fun y hy => a2 y hy x hx) (a3 ▸ pow_ne_zero _ hT), a3, hf,
      pow_mul, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _), Nat.cast_pow]
    rfl
  · rw [← hz]
    have hFz : ∀ a, (hS D).hT (D.sp.hypF a) F0.z = 0 := fun a => by
      rw [hz]; unfold D7.zmOf
      rw [map_smul, Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).2, smul_zero]
    have hFW : ∀ a w, (hS D).hT (D.sp.hypF a) (D.sp.iXY 0 w) = 0 := fun a w =>
      Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).2
    have hE : ∀ a, D.sp.hypE a ∈ F0.X := fun a => Submodule.subset_span ⟨a, congrFun he a⟩
    have hWb : ∀ v, v ∈ Wb D ↔ (∀ a, (hS D).hT (D.sp.hypE a) v = 0) ∧ ∀ a, (hS D).hT (D.sp.hypF a) v = 0 := by
      intro v
      rw [Wb, Formalism.MainNotions.mem_orth_iff]
      refine ⟨fun h => ⟨fun a => h _ (Submodule.subset_span (Or.inl ⟨a, rfl⟩)),
        fun a => h _ (Submodule.subset_span (Or.inr ⟨a, rfl⟩))⟩, fun h x hx => ?_⟩
      have : Submodule.span D.host.E (Set.range D.sp.hypE ∪ Set.range D.sp.hypF) ≤
          LinearMap.ker ((hS D).hT.flip v) := by
        refine Submodule.span_le.2 ?_
        rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
        · exact h.1 a
        · exact h.2 a
      exact this hx
    apply le_antisymm
    · intro v hv
      obtain ⟨h1, h2⟩ := (hWb v).1 hv
      have h3 := Formalism.MainNotions.hT_zero_of_mem_X F0 (v := v) (fun a => by rw [he]; exact h1 a)
      obtain ⟨w, x, hx, e⟩ := hdec (v + ((hS D).hT F0.z v * ((Tu D u : ℕ) : D.host.E)⁻¹) • F0.z)
        (fun x hx => by simp [h3 x hx, hXz x hx]) (by simp [F0.z_norm]; field_simp; ring)
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
      have hc : ∀ a, c a = 0 := fun a => by
        have := congrArg ((hS D).hT (D.sp.hypF a)) e
        have hfe : ∀ b, (hS D).hT (D.sp.hypF a) (F0.e b) = if b = a then 1 else 0 := fun b => by
          rw [he, ← (hS D).herm.eq, D.sp.hyp_ef]
          split_ifs <;> simp
        simpa [h2 a, hFz a, hFW a, hfe, eq_comm] using this
      simp only [hc, zero_smul, Finset.sum_const_zero, add_zero] at e
      rw [eq_sub_of_add_eq e]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨w, rfl⟩)
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    · refine sup_le ?_ ((Submodule.span_singleton_le_iff_mem _ _).2 ((hWb _).2 ⟨fun a => hXz _ (hE a), hFz⟩))
      rintro _ ⟨w, rfl⟩
      exact (hWb _).2 ⟨fun a => hXW _ (hE a) w, fun a => hFW a w⟩

end GlobalTheory.LoopC.Base
