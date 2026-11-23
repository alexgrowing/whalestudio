import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CentralMapMemIntegralUnipotentFixingFrame
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PerpendicularRankIdealBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFramesPerpendicularVectorsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesSameGramDifferBySkewSolutionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MinorSmulEqRowSpaceOfCofVecOrth
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.XClassesDenom
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeNormMulAbsNormSq

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LoopC.FixedLift

lemma mem_dual' {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {x : V} : x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
  {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T}

lemma gmap_iff (n : S.V ≃ₗ[E] S.V) : Formalism.HermitianLatticesTheory.gmap n Λ = Λ ↔ (∀ x, n x ∈ Λ ↔ x ∈ Λ) := by
  constructor
  · intro h x
    constructor
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, e⟩ := hx
      have : y = x := n.injective e
      exact this ▸ hy
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (h y).2 hy
    · intro hx
      refine ⟨n.symm x, (h _).1 (by simpa using hx), ?_⟩
      simp

lemma Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) :=
  Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => Nat.lt_succ_of_lt hi)

lemma mem_orth {U : Submodule E S.V} {y : S.V} : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf]

lemma hT_symm0 {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [← S.herm.eq x y, h, map_zero]

lemma X_iso {x y : S.V} (hx : x ∈ Xsp F) (hy : y ∈ Xsp F) : S.hT x y = 0 := by
  have h1 : ∀ a, S.hT (F.fl.e a) y = 0 := by
    intro a
    have : Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      exact F.fl.e_iso a b
    exact this hy
  have : Xsp F ≤ LinearMap.ker (S.hT y) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, rfl⟩
    exact hT_symm0 (h1 b)
  exact hT_symm0 (this hx)

lemma NLam_one : LinearEquiv.refl E S.V ∈ NLam Λ F :=
  ⟨⟨fun _ _ => rfl, (gmap_iff _).2 fun _ => Iff.rfl⟩, fun j x _ => by simp, fun x _ => by simp⟩

lemma NLam_trans {m n : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F) (hn : n ∈ NLam Λ F) :
    m.trans n ∈ NLam Λ F := by
  obtain ⟨⟨m1, m2⟩, m3, m4⟩ := hm
  obtain ⟨⟨n1, n2⟩, n3, n4⟩ := hn
  refine ⟨⟨fun x y => ?_, (gmap_iff _).2 fun x => ?_⟩, fun j x hx => ?_, fun x hx => ?_⟩
  · change S.hT (n (m x)) (n (m y)) = _
    rw [n1, m1]
  · change n (m x) ∈ Λ ↔ _
    rw [(gmap_iff n).1 n2, (gmap_iff m).1 m2]
  · change n (m x) - x ∈ _
    have h1 := m3 j x hx
    have h2 : m x ∈ Xflag F (j + 1) := by
      simpa using Submodule.add_mem _ (Xflag_mono j h1) hx
    simpa using Submodule.add_mem _ (n3 j _ h2) h1
  · change n (m x) - x ∈ _
    have h1 := m4 x hx
    have h2 : m x ∈ orth S (Xsp F) := by
      have : m x - x ∈ orth S (Xsp F) := mem_orth.2 fun y hy => X_iso hy h1
      simpa using Submodule.add_mem _ this hx
    simpa using Submodule.add_mem _ (n4 _ h2) h1

lemma NLam_symm {m : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F) (he : ∀ a, m (F.fl.e a) = F.fl.e a) :
    m.symm ∈ NLam Λ F := by
  obtain ⟨⟨m1, m2⟩, m3, m4⟩ := hm
  have hX : ∀ x ∈ Xsp F, m x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact he a
    | zero => simp
    | add x y _ _ h1 h2 => simp [h1, h2]
    | smul c x _ h => simp [h]
  have hX' : ∀ x ∈ Xsp F, m.symm x = x := fun x hx => by
    rw [LinearEquiv.symm_apply_eq, hX x hx]
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).inv_mem m1, (gmap_iff _).2 fun x => ?_⟩, fun j x hx => ?_,
    fun x hx => ?_⟩
  · rw [← (gmap_iff m).1 m2]; simp
  · have : x ∈ Xsp F := Submodule.span_mono (Set.image_subset_range _ _) hx
    simp [hX' x this]
  · have h1 : m.symm x ∈ orth S (Xsp F) := mem_orth.2 fun y hy => by
      rw [← m1, hX y hy]; simpa using mem_orth.1 hx y hy
    have := Submodule.neg_mem _ (m4 _ h1)
    simpa using this

def move {T' : E} (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F' : LFlag S r T') :
    LFlag S r T' where
  fl :=
    { e := fun a => n (F'.fl.e a)
      z := n F'.fl.z
      e_indep := F'.fl.e_indep.map' (n : S.V →ₗ[E] S.V) n.ker
      e_iso := fun a b => (hn _ _).trans (F'.fl.e_iso a b)
      z_orth := fun a => (hn _ _).trans (F'.fl.z_orth a)
      z_norm := (hn _ _).trans F'.fl.z_norm }
  zt := n F'.fl.z

lemma frame_move {T' : E} (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F' : LFlag S r T')
    (b : Fin (r + 1)) : frame (move n hn F') b = n (frame F' b) := by
  refine Fin.lastCases ?_ (fun a => ?_) b <;> simp [frame, FlagG.fvec, move]

lemma frame_castSucc {T' : E} (F' : LFlag S r T') (a : Fin r) : frame F' a.castSucc = F'.fl.e a := by
  simp [frame, FlagG.fvec]

lemma frame_last {T' : E} (F' : LFlag S r T') : frame F' (Fin.last r) = F'.fl.z := by
  simp [frame, FlagG.fvec]

def cls {T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (X : Set (LFlag S r T'))
    (f : Fin (r + 1) → S.V) : Set (LFlag S r T') :=
  {b | b ∈ X ∧ ∃ n ∈ NLam Λ F, ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E),
    (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ frame b = frameAct (fun a => n (f a)) ξ}

lemma cls_move {T' : E} (X : Set (LFlag S r T')) (f : Fin (r + 1) → S.V) {m : S.V ≃ₗ[E] S.V}
    (hm : m ∈ NLam Λ F) (he : ∀ a, m (F.fl.e a) = F.fl.e a) :
    cls Λ F X (fun b => m (f b)) = cls Λ F X f := by
  ext b
  constructor
  · rintro ⟨hb, n, hn, ξ, h1, h2, h3⟩
    exact ⟨hb, m.trans n, NLam_trans hm hn, ξ, h1, h2, h3⟩
  · rintro ⟨hb, n, hn, ξ, h1, h2, h3⟩
    refine ⟨hb, m.symm.trans n, NLam_trans (NLam_symm hm he) hn, ξ, h1, h2, ?_⟩
    simpa using h3

lemma uni_int (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {x y : S.V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT x y := by
  rw [← show Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ from hΛ] at hy
  exact Submodule.mem_one.1 (mem_dual'.1 hy x hx)

end Gen

lemma tuples (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ)) (S0 : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)) (r s : ℕ)
    (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (b₀ : Fin (r + 1)) (T : ℕ) (G : K) (M Q : ℝ)
    (hs : h.IsSymm) (hτ : ∀ v a, τ v (star a) = starRingEnd ℂ (τ v a))
    (hN : ∀ a : K, ∏ v, ‖τ v a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)|)
    (hpos : ∀ v, ∀ x : V, x ≠ 0 → 0 < (τ v (h x x)).re) (hι : Nonempty ι)
    (hfg : S0.FG) (hint : Formalism.HermitianLatticesTheory.IsIntegralLat h S0)
    (hrk : finrank K (Submodule.span K (S0 : Set V)) = s) (hI : I ≠ ⊥)
    (hIS : I • dualInH h S0 ≤ S0) (hd : (Y.submatrix id b₀.succAbove).det ≠ 0)
    (hdQ : (Ideal.absNorm (Ideal.span {(Y.submatrix id b₀.succAbove).det}) : ℝ) ≤ Q)
    (hIM : (Ideal.absNorm I : ℝ) ≤ M) (hM : 1 ≤ M) (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hG : G ≠ 0)
    (hGQ : ∏ v, ‖τ v G‖ ≤ Q) :
    ∃ reps : Finset (Fin (r + 1) → V),
      (reps.card : ℝ) ≤ 9 ^ (s * Fintype.card ι) * (M * Q) ^ (s + s * r) ∧
      ∀ w : Fin (r + 1) → V, (∀ b, w b ∈ dualInH h S0) →
        (T : K) * h (∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec Y b • w b) (∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec Y b • w b) = G →
        ∃ w₀ ∈ reps, ∃ v : Fin r → V, (∀ a, v a ∈ S0) ∧ ∀ b, w b = w₀ b + ∑ a, Y a b • v a := by
  have hsp : Submodule.span K (dualInH h S0 : Set V) = Submodule.span K (S0 : Set V) := by
    apply le_antisymm
    · exact Submodule.span_le.2 fun x hx => hx.2
    · exact Submodule.span_mono fun x hx =>
        ⟨mem_dual'.2 fun y hy => hint y hy x hx, Submodule.subset_span hx⟩
  obtain ⟨hfin, hcard⟩ := GlobalTheory.DefinitePacking.dualPack K V h ι τ (dualInH h S0) I s (fun v => ‖τ v G‖)
    hs hτ hN hpos hι (by rw [hsp, hrk]) hI
    (fun x hx y hy => Submodule.mem_one.1 (hint x (hIS hx) y (hIS hy)))
    (fun v => norm_pos_iff.2 (by simpa using hG))
  obtain ⟨R2, hR2, hcov⟩ := GlobalTheory.exists_reps_cofVec_orth_mod_rowSpace K V S0 (dualInH h S0) I r s Y b₀
    hfg hrk hI hIS hd
  let P : V → (Fin (r + 1) → V) → Prop := fun y w =>
    (∀ b, w b ∈ dualInH h S0) ∧ ∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec Y b • w b = y
  let w1 : V → Fin (r + 1) → V := fun y => Classical.epsilon (P y)
  refine ⟨(hfin.toFinset ×ˢ R2).image fun p => w1 p.1 + p.2, ?_, ?_⟩
  · have h1 : ((hfin.toFinset ×ˢ R2).image fun p => w1 p.1 + p.2).card ≤ hfin.toFinset.card * R2.card := by
      rw [← Finset.card_product]; exact Finset.card_image_le
    have h2 : (hfin.toFinset.card : ℝ) ≤ 9 ^ (s * Fintype.card ι) * (M * Q) ^ s := by
      rw [← Set.ncard_eq_toFinset_card _ hfin]
      refine hcard.trans ?_
      gcongr
      refine max_le (one_le_mul_of_one_le_of_one_le hM hQ) ?_
      gcongr
    have h3 : (R2.card : ℝ) ≤ (M * Q) ^ (s * r) := by
      refine (Nat.cast_le.2 hR2).trans ?_
      rw [map_mul, mul_comm]
      push_cast
      gcongr
    calc _ ≤ (hfin.toFinset.card : ℝ) * R2.card := by exact_mod_cast h1
      _ ≤ (9 ^ (s * Fintype.card ι) * (M * Q) ^ s) * (M * Q) ^ (s * r) := by gcongr
      _ = _ := by rw [pow_add, mul_assoc]
  · intro w hw hG'
    set y := ∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec Y b • w b with hy
    have hP : P y (w1 y) := Classical.epsilon_spec ⟨w, hw, rfl⟩
    have hyA : y ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      refine ⟨Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hw b), fun v => ?_⟩
      refine (Complex.re_le_norm _).trans ?_
      rw [← hG', map_mul, norm_mul, map_natCast, Complex.norm_natCast]
      exact le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast hT)
    obtain ⟨u₀, hu₀, v, hv, e⟩ := hcov (w - w1 y) (fun b => Submodule.sub_mem _ (hw b) (hP.1 b))
      (by simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, hP.2, ← hy, sub_self])
    refine ⟨w1 y + u₀, Finset.mem_image.2 ⟨(y, u₀), Finset.mem_product.2 ⟨hyA, hu₀⟩, rfl⟩, v, hv,
      fun b => ?_⟩
    have := e b
    simp only [Pi.sub_apply] at this
    rw [Pi.add_apply, add_assoc, ← this]; abel

lemma absNorm_span (K : Type) [Field K] [NumberField K] (d : 𝓞 K) :
    (Ideal.absNorm (Ideal.span {d}) : ℝ) = |((Algebra.norm ℚ (d : K) : ℚ) : ℝ)| := by
  rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp

lemma cofVec_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {r : ℕ}
    (Y : Matrix (Fin r) (Fin (r + 1)) A) (b : Fin (r + 1)) :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec (Y.map f) b = f (Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec Y b) := by
  simp only [Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec, map_mul, map_pow, map_neg, map_one, RingHom.map_det]
  rfl

section Rec

variable (D : D7)

def ddI : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

lemma ddI_norm : (Ideal.absNorm (ddI D) : ℝ) = D.host.rdE ^ (2 * D.R.f) := by
  rw [← (GlobalTheory.real_places_facts D).2.2.2.2.2.2.2.2.1]
  have : ddS D = ((ddI D : Ideal _) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := rfl
  rw [this, FractionalIdeal.coeIdeal_absNorm]
  simp

lemma ddI_ne : ddI D ≠ ⊥ := by
  intro h
  have h1 := ddI_norm D
  have h2 := (GlobalTheory.real_places_facts D).2.2.2.2.1
  rw [h] at h1
  simp only [Ideal.absNorm_bot, Nat.cast_zero] at h1
  have : (0 : ℝ) < D.host.rdE ^ (2 * D.R.f) := by positivity
  linarith

lemma mul_mem_of (n : ℕ) {x : D.host.E}
    (hx : x ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))
    {α : 𝓞 D.host.E} (hα : α ∈ ddI D ^ n) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = (α : D.host.E) * x := by
  have e : ddS D = ((ddI D : Ideal _) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := rfl
  have hne : ddS D ≠ 0 := by rw [e]; exact FractionalIdeal.coeIdeal_ne_zero.2 (ddI_ne D)
  have h1 : (α : D.host.E) ∈ ddS D ^ n := by
    rw [e, ← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ hα
  have h2 := FractionalIdeal.mul_mem_mul h1 hx
  rw [_root_.zpow_neg, _root_.zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hne)] at h2
  exact (FractionalIdeal.mem_one_iff _).1 h2

lemma one_mem_dd (n : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have e : ddS D = ((ddI D : Ideal _) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := rfl
  have hne : ddS D ≠ 0 := by rw [e]; exact FractionalIdeal.coeIdeal_ne_zero.2 (ddI_ne D)
  have h1 : ddS D ^ n ≤ 1 := by
    rw [e, ← FractionalIdeal.coeIdeal_pow]; exact FractionalIdeal.coeIdeal_le_one
  rw [_root_.zpow_neg, _root_.zpow_natCast, FractionalIdeal.mem_inv_iff (pow_ne_zero _ hne)]
  intro y hy
  simpa using h1 hy

lemma e_mem {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {Λ : LatV D} (h : IsRowLat D F0 Λ)
    (a : Fin D.R.rS) : F0.e a ∈ XLam Λ (lf D F0) := by
  rw [h.2.2]
  refine Submodule.subset_span ⟨a, 1, ?_, (one_smul _ _).symm⟩
  have := one_mem_dd D (D.R.rS - a)
  rwa [Nat.cast_sub a.2.le] at this

end Rec

section Main

variable {D : D7}

def FixGr (Λ : LatV D) {T : D.host.E} (F : Fg D T) (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V)
    (n : (hS D).V ≃ₗ[D.host.E] (hS D).V) : Prop :=
  n ∈ NLam Λ F ∧ (∀ b, n (frame F b) = frame F b) ∧
    ∀ p : P, n (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) = D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p

lemma move_mem {Λ : LatV D} {T T' : D.host.E} {F : Fg D T} {P : LatW D}
    {φ : P →ₗ[𝓞 D.host.E] (hS D).V} {Z : GramM D} {n : (hS D).V ≃ₗ[D.host.E] (hS D).V}
    (hn : FixGr Λ F P φ n) {F' : Fg D T'} (h : F' ∈ FixSet D Λ F T' Z P φ) :
    move n hn.1.1.1 F' ∈ FixSet D Λ F T' Z P φ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hL := (gmap_iff n).1 hn.1.1.2
  refine ⟨⟨(hL _).2 h1.1, rfl⟩, fun a => (hL _).2 (h2 a), ?_, fun p b => ?_⟩
  · rw [← h3]
    funext a b
    change (hS D).hT (frame F a) (frame (move n hn.1.1.1 F') b) = (hS D).hT (frame F a) (frame F' b)
    rw [frame_move]
    conv_lhs => rw [← hn.2.1 a]
    exact hn.1.1.1 _ _
  · rw [frame_move, ← h4 p b]
    conv_lhs => rw [← hn.2.2 p]
    exact hn.1.1.1 _ _

lemma iXY_X {u : D.what₂.Word} {F0 : Fb D u} (hb : IsBase D u F0) (w : (D.sp.X 0).V) {x : (hS D).V}
    (hx : x ∈ Xsp (lf D F0)) : (hS D).hT (D.sp.iXY 0 w) x = 0 := by
  have : Xsp (lf D F0) ≤ LinearMap.ker ((hS D).hT (D.sp.iXY 0 w)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    change (hS D).hT (D.sp.iXY 0 w) (F0.e a) = 0
    rw [hb.1]
    exact (D.sp.hyp_orthX a w).1
  exact this hx

lemma iXY_isom (x y : (D.sp.X 0).V) :
    (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y :=
  D.sp.iXY_isom 0 (by rw [(GlobalTheory.real_places_facts D).2.2.2.1]; omega) x y

lemma mem_perpE {P : LatW D} {v : (D.sp.X 0).V} : v ∈ perpE D P ↔ ∀ p ∈ P, (D.sp.X 0).hT p v = 0 := by
  simp [perpE, Submodule.mem_iInf]

def Shifts {T : D.host.E} (F : Fg D T) (n : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (v : Fin D.R.rS → (D.sp.X 0).V) : Prop :=
  ∀ x σ, (hS D).hT (D.sp.iXY 0 σ) (n x) =
    (hS D).hT (D.sp.iXY 0 σ) x + ∑ a, (hS D).hT (F.fl.e a) x * (D.sp.X 0).hT σ (v a)

lemma eich_single {u : D.what₂.Word} {F0 : Fb D u} {Λ : LatV D} (hb : IsBase D u F0)
    (hΛ : IsRowLat D F0 Λ) {P : LatW D} {φ : P →ₗ[𝓞 D.host.E] (hS D).V}
    (hφ : ∀ p, φ p ∈ XLam Λ (lf D F0)) (a : Fin D.R.rS) {v : (D.sp.X 0).V}
    (hv : v ∈ perpW D (L0X D Λ (lf D F0)) P) :
    ∃ n, FixGr Λ (lf D F0) P φ n ∧ Shifts (lf D F0) n (Pi.single a v) := by
  obtain ⟨⟨⟨h1, -⟩, h2⟩, h3⟩ := hv
  obtain ⟨σ, hσ, x, hx, e⟩ := Submodule.mem_sup.1 h1
  change σ + x = D.sp.iXY 0 v at e
  change x ∈ Xsp (lf D F0) at hx
  change (hS D).hT F0.z (D.sp.iXY 0 v) = 0 at h2
  have eσ : σ = D.sp.iXY 0 v - x := eq_sub_of_add_eq e
  obtain ⟨n, hn, t, hnX, hnf⟩ := GlobalTheory.EichlerUnip.eichler_mem_unipotent D _ (lf D F0) Λ hΛ.2.1.2.1 σ hσ (F0.e a) (e_mem D F0 hΛ a)
  have heX : ∀ a, F0.e a ∈ Xsp (lf D F0) := fun a => Submodule.subset_span ⟨a, rfl⟩
  have hXz : ∀ y ∈ Xsp (lf D F0), (hS D).hT F0.z y = 0 := by
    intro y hy
    have : Xsp (lf D F0) ≤ LinearMap.ker ((hS D).hT F0.z) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      exact hT_symm0 (F0.z_orth a)
    exact this hy
  refine ⟨n, ⟨hn, fun b => ?_, fun p => ?_⟩, fun y τ => ?_⟩
  · refine Fin.lastCases ?_ (fun c => ?_) b
    · rw [frame_last, hnf]
      have a1 : (hS D).hT σ F0.z = 0 := by
        apply hT_symm0
        rw [eσ, map_sub, h2, hXz x hx, sub_zero]
      have a2 : (hS D).hT (F0.e a) F0.z = 0 := F0.z_orth a
      simp [a1, a2]
    · rw [frame_castSucc]; exact hnX _ (heX c)
  · have hp : φ p ∈ Xsp (lf D F0) := (hφ p).2
    have a1 : (hS D).hT σ (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) = 0 := by
      apply hT_symm0
      have b1 : (hS D).hT (φ p) σ = 0 := mem_orth.1 hσ.2 _ hp
      rw [map_add, LinearMap.add_apply, b1, eσ, map_sub, iXY_isom, iXY_X hb _ hx,
        mem_perpE.1 h3 _ p.2]
      simp
    have a2 : (hS D).hT (F0.e a) (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) = 0 := by
      rw [map_add, X_iso (heX a) hp, hT_symm0 (iXY_X hb _ (heX a)), add_zero]
    rw [hnf, a1, a2]
    simp
  · have a1 : (hS D).hT (D.sp.iXY 0 τ) (F0.e a) = 0 := iXY_X hb _ (heX a)
    have a2 : (hS D).hT (D.sp.iXY 0 τ) σ = (D.sp.X 0).hT τ v := by
      rw [eσ, map_sub, iXY_isom, iXY_X hb _ hx, sub_zero]
    rw [hnf, Finset.sum_eq_single a (fun c _ hc => by simp [Pi.single_eq_of_ne hc]) (by simp)]
    simp [a1, a2]

lemma eich {u : D.what₂.Word} {F0 : Fb D u} {Λ : LatV D} (hb : IsBase D u F0)
    (hΛ : IsRowLat D F0 Λ) {P : LatW D} {φ : P →ₗ[𝓞 D.host.E] (hS D).V}
    (hφ : ∀ p, φ p ∈ XLam Λ (lf D F0)) (v : Fin D.R.rS → (D.sp.X 0).V)
    (hv : ∀ a, v a ∈ perpW D (L0X D Λ (lf D F0)) P) :
    ∃ n, FixGr Λ (lf D F0) P φ n ∧ Shifts (lf D F0) n v := by
  rw [← Finset.univ_sum_single v]
  refine Finset.sum_induction _ (fun v => ∃ n, FixGr Λ (lf D F0) P φ n ∧ Shifts (lf D F0) n v) ?_ ?_
    fun a _ => eich_single hb hΛ hφ a (hv a)
  · rintro v v' ⟨m, hm, sm⟩ ⟨n, hn, sn⟩
    refine ⟨m.trans n, ⟨NLam_trans hm.1 hn.1, fun b => ?_, fun p => ?_⟩, fun x σ => ?_⟩
    · rw [LinearEquiv.trans_apply, hm.2.1, hn.2.1]
    · rw [LinearEquiv.trans_apply, hm.2.2, hn.2.2]
    · have : ∀ a, (hS D).hT ((lf D F0).fl.e a) (m x) = (hS D).hT ((lf D F0).fl.e a) x := by
        intro a
        have := hm.2.1 a.castSucc
        rw [frame_castSucc] at this
        conv_lhs => rw [← this]
        exact hm.1.1.1 _ _
      rw [LinearEquiv.trans_apply, sn, sm]
      simp only [this, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_assoc]
  · exact ⟨LinearEquiv.refl _ _, ⟨NLam_one, fun _ => rfl, fun _ => rfl⟩, fun x σ => by simp⟩

theorem card_frames_le : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D) (s : ℕ) (De Q : ℝ), 1 ≤ s → s ≤ D.R.k → (∀ p, φ p ∈ XLam Λ (lf D F0)) → SubOK D (L0X D Λ (lf D F0)) P s De → QOK D u u' Z Q → (cntCl (FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤ ENNReal.ofReal (fixB D s (NT D u) De Q) := by
  intro D u u' F0 Λ hSt hb hΛ hsp P φ Z s De Q _ hsk hφ hsub hQ
  set X := FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ with hX
  rcases X.eq_empty_or_nonempty with hE | ⟨F1, hF1⟩
  · simp [cntCl, hE]
  obtain ⟨hcard, -, hf, -, hrd, hstar, hnorm, -⟩ := GlobalTheory.real_places_facts D
  obtain ⟨-, -, hpos, hlat, hint, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hSt hb hΛ
  obtain ⟨hrk, I, hI, hIN, hIS⟩ := GlobalTheory.T.perpendicular_rank_ideal_bound D u u' F0 Λ hSt hb hΛ P s De hsk hsub
  obtain ⟨hQ1, hQrd, ⟨b₀, hd, hdQ⟩, hG, hGQ⟩ := hQ
  have huni : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ := hΛ.2.1.2.1
  have hZ : ∀ F' ∈ X, ∀ a b, (hS D).hT (F0.e a) (frame F' b) = Z (Fin.castSucc a) b := by
    intro F' hF' a b
    rw [← hF'.2.2.1, ← frame_castSucc (lf D F0) a]
    rfl
  have hfr : ∀ b, frame F1 b ∈ Λ := fun b => by
    refine Fin.lastCases ?_ (fun c => ?_) b
    · rw [frame_last]; exact hF1.1.1
    · rw [frame_castSucc]; exact hF1.2.1 c
  choose Y hY using fun a b => uni_int huni (e_mem D F0 hΛ a).1 (hfr b)
  let Y' : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) (𝓞 D.host.E) := Y
  have hYZ : Y'.map (algebraMap (𝓞 D.host.E) D.host.E) = Z.submatrix Fin.castSucc id := by
    funext a b
    exact (hY a b).trans (hZ F1 hF1 a b)
  have hdet : algebraMap (𝓞 D.host.E) D.host.E (Y'.submatrix id b₀.succAbove).det = rowMinor D Z b₀ := by
    rw [rowMinor, ← hYZ, RingHom.map_det]
    rfl
  have hd' : (Y'.submatrix id b₀.succAbove).det ≠ 0 := fun h => hd (by rw [← hdet, h, map_zero])
  have hdQ' : (Ideal.absNorm (Ideal.span {(Y'.submatrix id b₀.succAbove).det}) : ℝ) ≤ Q := by
    rw [absNorm_span, ← hnorm]
    rw [← hdet] at hdQ
    exact hdQ
  have hT : 1 ≤ Tu D u := hSt.2.1.one_le
  have hNT : 1 ≤ NT D u := one_le_pow₀ (by exact_mod_cast hT)
  have hDe : 1 ≤ De := le_trans (by exact_mod_cast hsub.2.2.1) hsub.2.2.2.1
  have hne : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, hcard, ← hf]
    exact finrank_pos
  set S0 := perpW D (L0X D Λ (lf D F0)) P with hS0
  have hle : S0 ≤ L0X D Λ (lf D F0) := inf_le_left
  obtain ⟨RW, hRW, hcovW⟩ := tuples D.host.E (D.sp.X 0).V (D.sp.X 0).hT D.what₂.Tau (embS D) S0 I D.R.rS s
    Y' b₀ (Tu D u) _ (De ^ 2 * NT D u ^ 2) Q (D.sp.X 0).herm hstar hnorm
    (fun v => hpos (embS D v)) hne (hlat.fg.of_le hle)
    (fun x hx y hy => hint x (hle hx) y (hle hy)) hrk hI hIS hd' hdQ' hIN
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hDe) (one_le_pow₀ hNT)) hQ1 hT hG hGQ
  obtain ⟨RX, hRX, hcovX⟩ := GlobalTheory.xClasses D.host.E (ddI D ^ D.R.rS) D.R.rS Y' b₀
    (pow_ne_zero _ (ddI_ne D)) hd'
  have hRX' : (RX.card : ℝ) ≤ Q ^ (2 * D.R.rS ^ 2) := by
    refine (Nat.cast_le.2 hRX).trans ?_
    rw [map_mul, map_pow, pow_mul, pow_two Q]
    push_cast
    rw [ddI_norm, ← pow_mul]
    gcongr
  let Pw : (Fin (D.R.rS + 1) → (D.sp.X 0).V) → Fg D ((Tu D u' : ℕ) : D.host.E) → Prop := fun w F' =>
    F' ∈ X ∧ ∀ b, IsWcomp D P (frame F' b) (w b)
  haveI : Nonempty (Fg D ((Tu D u' : ℕ) : D.host.E)) := ⟨F1⟩
  let G : (Fin (D.R.rS + 1) → (D.sp.X 0).V) → Fg D ((Tu D u' : ℕ) : D.host.E) := fun w =>
    Classical.epsilon (Pw w)
  let g : (Fin (D.R.rS + 1) → (D.sp.X 0).V) × Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E →
      Set (Fg D ((Tu D u' : ℕ) : D.host.E)) := fun p =>
    cls Λ (lf D F0) X fun b => frame (G p.1) b + ∑ a, p.2 a b • F0.e a
  have key : {O : Set (Fg D ((Tu D u' : ℕ) : D.host.E)) |
      ∃ a ∈ X, O = {b | b ∈ X ∧ TEqv D Λ (lf D F0) a b}} ⊆ ((RW ×ˢ RX).image g : Finset _) := by
    rintro _ ⟨F', hF', rfl⟩
    change cls Λ (lf D F0) X (frame F') ∈ _
    obtain ⟨w, hw, hwG⟩ := GlobalTheory.T.fixed_frames_perpendicular_vectors D u u' F0 Λ hSt hb hΛ hsp P φ Z hφ hsub.1 F' hF'
    obtain ⟨w₀, hw₀, v, hv, ew⟩ := hcovW w (fun b => (hw b).2) (by
      rw [← hwG, ← hYZ]
      simp only [cofVec_map, algebraMap_smul])
    obtain ⟨n, hn, sn⟩ := eich hb hΛ hφ (-v) fun a => S0.neg_mem (hv a)
    have hF2 : move n hn.1.1.1 F' ∈ X := move_mem hn hF'
    have hP2 : Pw w₀ (move n hn.1.1.1 F') := by
      refine ⟨hF2, fun b => ?_⟩
      have e0 : w₀ b = w b - ∑ a, Y' a b • v a := eq_sub_of_add_eq (ew b).symm
      refine ⟨?_, fun σ hσ => ?_⟩
      · rw [e0]
        refine Submodule.sub_mem _ (hw b).1.1 (Submodule.sum_mem _ fun a _ => ?_)
        exact (S0.smul_mem (Y' a b) (hv a)).2
      · rw [frame_move, sn, (hw b).1.2 σ hσ, e0, map_sub, map_sum, sub_eq_add_neg,
          ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        have : (hS D).hT ((lf D F0).fl.e a) (frame F' b) = algebraMap _ D.host.E (Y' a b) :=
          (hZ F' hF' a b).trans (congrFun (congrFun hYZ a) b).symm
        rw [this, ← algebraMap_smul D.host.E (Y' a b) (v a), map_smul, Pi.neg_apply, map_neg,
          smul_eq_mul, mul_neg]
    have hPG : Pw w₀ (G w₀) := Classical.epsilon_spec ⟨_, hP2⟩
    obtain ⟨x, hx1, hx2, hx3⟩ := GlobalTheory.T.frames_same_gram_differ_by_skew_solution D u u' F0 Λ hSt hb hΛ P φ Z hφ (G w₀) hPG.1 _ hF2
      fun b => ⟨w₀ b, hPG.2 b, hP2.2 b⟩
    obtain ⟨x₀, hx₀, c, hc, ex⟩ := hcovX x (fun a b α hα => mul_mem_of D _ (hx2 a b) hα)
      (by rw [hYZ]; exact hx3)
    obtain ⟨m, hm, -, hmf⟩ := GlobalTheory.LoopC.Centre.centralMap_mem_integralUnipotentFixingFrame D _ (lf D F0) Λ huni (fun a => (e_mem D F0 hΛ a).1) c hc
    have hne : ∀ a, n (F0.e a) = F0.e a := fun a => by
      have := hn.2.1 a.castSucc
      rwa [frame_castSucc] at this
    have hme : ∀ a, m (F0.e a) = F0.e a := fun a => by
      have := hm.2 a.castSucc
      rwa [frame_castSucc] at this
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(w₀, x₀), Finset.mem_product.2 ⟨hw₀, hx₀⟩, ?_⟩)
    rw [← cls_move (F := lf D F0) X (frame F') hn.1 hne]
    refine (cls_move (F := lf D F0) X _ hm.1 hme).symm.trans ?_
    congr 1
    funext b
    rw [← frame_move n hn.1.1.1, hx1, hmf, ex, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.add_apply, add_smul, Matrix.mul_apply, Finset.sum_smul]
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    have : (hS D).hT ((lf D F0).fl.e a') (frame (G w₀) b + ∑ a, x₀ a b • F0.e a) =
        (Y'.map (algebraMap (𝓞 D.host.E) D.host.E)) a' b := by
      rw [hYZ, map_add, map_sum]
      have : ∀ a, (hS D).hT ((lf D F0).fl.e a') (x₀ a b • F0.e a) = 0 := fun a => by
        rw [map_smul, show (hS D).hT ((lf D F0).fl.e a') (F0.e a) = 0 from F0.e_iso a' a, smul_zero]
      simp only [this, Finset.sum_const_zero, add_zero]
      exact hZ _ hPG.1 a' b
    rw [this]
    rfl
  have h1 : cntCl X (TEqv D Λ (lf D F0)) ≤ ((RW.card * RX.card : ℕ) : ℕ∞) := by
    refine (Set.encard_le_encard key).trans ?_
    rw [Set.encard_coe_eq_coe_finsetCard, ← Finset.card_product]
    exact_mod_cast Finset.card_image_le
  refine (ENat.toENNReal_le.2 h1).trans ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [fixB, ← hcard]
  push_cast
  gcongr

end Main

end GlobalTheory.LoopC.FixedLift

end
