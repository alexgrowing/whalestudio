import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNeg
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulP
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupActionRingHomStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairingStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaBetaAdjointExactStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaEquivariantFrobeniusStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BetaEquivariantFrobeniusStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalDataBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransportStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaBetaIsomorphismTransportStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalMatrixCoprimeDecompositionStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.Fam

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Crv.Inhab

variable {K : Type} [Field K] (C : ACurve K) {d : ℕ}

def colLat (i : C.I) (g : Matrix (Fin d) (Fin d) K) : AddSubgroup (Fin d → K) :=
  (trivLat C d i).map (Matrix.toLin' g).toAddMonoidHom

def stdH (d : ℕ) (i : C.I) : AddSubgroup ((Fin d → K) × (Fin d → K)) :=
  (trivLat C d i).prod (trivLat C d i)

def imLat (i : C.I) (T : ((Fin d → K) × (Fin d → K)) →ₗ[K] (Fin d → K) × (Fin d → K)) :
    AddSubgroup ((Fin d → K) × (Fin d → K)) :=
  (stdH C d i).map T.toAddMonoidHom

theorem mem_colLat {i : C.I} {g : Matrix (Fin d) (Fin d) K} {x : Fin d → K} :
    x ∈ colLat C i g ↔ ∃ w ∈ trivLat C d i, g.mulVec w = x := by
  simp [colLat, AddSubgroup.mem_map]

theorem mem_imLat {i : C.I} {T : ((Fin d → K) × (Fin d → K)) →ₗ[K] (Fin d → K) × (Fin d → K)}
    {y : (Fin d → K) × (Fin d → K)} : y ∈ imLat C i T ↔ ∃ w ∈ stdH C d i, T w = y := by
  simp [imLat, AddSubgroup.mem_map]

theorem mem_stdH {i : C.I} {y : (Fin d → K) × (Fin d → K)} :
    y ∈ stdH C d i ↔ y.1 ∈ trivLat C d i ∧ y.2 ∈ trivLat C d i := AddSubgroup.mem_prod

theorem mem_colLat_iff {i : C.I} {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    {x : Fin d → K} : x ∈ colLat C i g ↔ ∀ j, C.v i (g'.mulVec x j) ≤ 1 := by
  rw [mem_colLat]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Matrix.mulVec_mulVec, h₂, Matrix.one_mulVec]
    exact hw
  · intro h
    exact ⟨g'.mulVec x, h, by rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]⟩

def frame {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1) :
    Module.Basis (Fin d) K (Fin d → K) :=
  (Pi.basisFun K (Fin d)).map (Matrix.toLin'OfInv h₂ h₁)

theorem frame_repr {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    (x : Fin d → K) (q : Fin d) : (frame h₁ h₂).repr x q = g'.mulVec x q := by
  simp [frame, Matrix.toLin'OfInv]

theorem frame_apply {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    (q : Fin d) : frame h₁ h₂ q = fun r => g r q := by
  funext r
  simp [frame, Matrix.toLin'OfInv]

theorem isLatOf_frame (i : C.I) {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1) :
    IsLatOf C i (frame h₁ h₂) (colLat C i g) := fun x => by
  rw [mem_colLat_iff C h₁ h₂]
  simp only [frame_repr]

theorem isBun_frames {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
    (b : C.I → Module.Basis ι K V) (b₀ : Module.Basis ι K V) (L : C.I → AddSubgroup V)
    (hb : ∀ i x, x ∈ L i ↔ ∀ q, C.v i ((b i).repr x q) ≤ 1)
    (hfin : {i | ¬ ∀ x, x ∈ L i ↔ ∀ q, C.v i (b₀.repr x q) ≤ 1}.Finite) : IsBun C L := by
  let e : ι ≃ Fin (Module.finrank K V) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  have re : ∀ (c : Module.Basis ι K V) (i : C.I) (L' : AddSubgroup V),
      (∀ x, x ∈ L' ↔ ∀ q, C.v i (c.repr x q) ≤ 1) → IsLatOf C i (c.reindex e) L' := by
    intro c i L' h x
    rw [h]
    simp only [Module.Basis.repr_reindex_apply]
    exact ⟨fun H q => H _, fun H q => by simpa using H (e q)⟩
  exact ⟨fun i => ⟨_, re _ i _ (hb i)⟩, b₀.reindex e,
    hfin.subset fun i hi h => hi (re _ _ _ h)⟩

def IntM (i : C.I) (M : Matrix (Fin d) (Fin d) K) : Prop := ∀ a b, C.v i (M a b) ≤ 1

theorem colLat_eq_triv {i : C.I} {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    (hg : IntM C i g) (hg' : IntM C i g') : colLat C i g = trivLat C d i := by
  ext x
  rw [mem_colLat]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mulVec_mem_trivLat C hg hw
  · intro hx
    exact ⟨g'.mulVec x, mulVec_mem_trivLat C hg' hx, by rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]⟩

theorem isBun_colLat (g g' : C.I → Matrix (Fin d) (Fin d) K) (h₁ : ∀ i, g i * g' i = 1)
    (h₂ : ∀ i, g' i * g i = 1) (hfin : {i | ¬ (IntM C i (g i) ∧ IntM C i (g' i))}.Finite) :
    IsBun C fun i => colLat C i (g i) := by
  refine isBun_frames C (fun i => frame (h₁ i) (h₂ i)) (Pi.basisFun K (Fin d)) _
    (fun i x => (isLatOf_frame C i (h₁ i) (h₂ i)) x) (hfin.subset fun i hi h => hi ?_)
  intro x
  rw [colLat_eq_triv C (h₁ i) (h₂ i) h.1 h.2]
  simp [mem_trivLat]

theorem dotDual_colLat (g g' : C.I → Matrix (Fin d) (Fin d) K) (h₁ : ∀ i, g i * g' i = 1)
    (h₂ : ∀ i, g' i * g i = 1) :
    dotDual C (fun i => colLat C i (g i)) = fun i => colLat C i (g' i).transpose := by
  funext i
  have t₁ : (g' i).transpose * (g i).transpose = 1 := by
    rw [← Matrix.transpose_mul, h₁, Matrix.transpose_one]
  have t₂ : (g i).transpose * (g' i).transpose = 1 := by
    rw [← Matrix.transpose_mul, h₂, Matrix.transpose_one]
  have := DegDual.isLatOf_dual C (fun i => colLat C i (g i)) (dotProductBilin K K) i
    (frame (h₁ i) (h₂ i)) (frame t₁ t₂) (fun y q => ?_) (isLatOf_frame C i (h₁ i) (h₂ i))
  · ext y
    rw [show dotDual C (fun i => colLat C i (g i)) i = dualLat C _ (dotProductBilin K K) i from rfl,
      this y, (isLatOf_frame C i t₁ t₂) y]
  · rw [frame_repr, frame_apply]
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

theorem frobLat_colLat (p : ℕ) [Fact p.Prime] [CharP K p] (g g' : C.I → Matrix (Fin d) (Fin d) K)
    (h₁ : ∀ i, g i * g' i = 1) (h₂ : ∀ i, g' i * g i = 1) :
    frobLat C p (fun i => colLat C i (g i)) = fun i => colLat C i ((g i).map (· ^ p)) := by
  funext i
  have e : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ p) = (frobenius K p).mapMatrix M := fun M => rfl
  have t₁ : (g i).map (· ^ p) * (g' i).map (· ^ p) = 1 := by
    rw [e, e, ← map_mul, h₁, map_one]
  have t₂ : (g' i).map (· ^ p) * (g i).map (· ^ p) = 1 := by
    rw [e, e, ← map_mul, h₂, map_one]
  have := DegFrob.isLatOf_frob C p (fun i => colLat C i (g i)) i (frame (h₁ i) (h₂ i)) (frame t₁ t₂)
    (fun q => ?_) (isLatOf_frame C i (h₁ i) (h₂ i))
  · ext y
    rw [this y, (isLatOf_frame C i t₁ t₂) y]
  · rw [frame_apply, frame_apply]
    rfl

local notation "VV" K:max d:max => ((Fin d → K) × (Fin d → K))

def stdBasis (K : Type) [Field K] (d : ℕ) : Module.Basis (Fin d ⊕ Fin d) K (VV K d) :=
  (Pi.basisFun K (Fin d)).prod (Pi.basisFun K (Fin d))

theorem forall_stdBasis (i : C.I) (y : VV K d) :
    (∀ q, C.v i ((stdBasis K d).repr y q) ≤ 1) ↔ y ∈ stdH C d i := by
  rw [mem_stdH, Sum.forall]
  simp [stdBasis, mem_trivLat]

theorem isBun_imLat (T : C.I → VV K d →ₗ[K] VV K d) (hT : ∀ i, Function.Bijective (T i))
    (hfin : {i | imLat C i (T i) ≠ stdH C d i}.Finite) : IsBun C fun i => imLat C i (T i) := by
  refine isBun_frames C (fun i => (stdBasis K d).map (LinearEquiv.ofBijective (T i) (hT i)))
    (stdBasis K d) _ (fun i x => ?_) (hfin.subset fun i hi h => hi ?_)
  · rw [mem_imLat]
    simp only [Module.Basis.map_repr, LinearEquiv.trans_apply]
    rw [forall_stdBasis]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : (LinearEquiv.ofBijective (T i) (hT i)).symm (T i w) = w :=
        (LinearEquiv.ofBijective (T i) (hT i)).symm_apply_apply w
      rwa [this]
    · intro h
      exact ⟨_, h, (LinearEquiv.ofBijective (T i) (hT i)).apply_symm_apply x⟩
  · intro x
    rw [forall_stdBasis]
    exact iff_of_eq (congrArg (x ∈ ·) h)

theorem transH_mem_stdH {i : C.I} {φ ψ : Pt K 1 d} {lam : PS K 2 d}
    (hg : IntM C i (lin φ 1)) (hg' : IntM C i (lin ψ 1)) (hl : IntM C i (bil lam 1 1))
    {w : VV K d} (hw : w ∈ stdH C d i) : transH φ ψ lam w ∈ stdH C d i := by
  rw [mem_stdH] at hw ⊢
  rw [transH_apply]
  exact ⟨mulVec_mem_trivLat C hg hw.1, mulVec_mem_trivLat C (fun a b => hg' b a)
    (add_mem hw.2 (mulVec_mem_trivLat C (fun a b => hl b a) hw.1))⟩

theorem imLat_transH_eq {i : C.I} {φ ψ : Pt K 1 d} {lam : PS K 2 d}
    (h₁ : lin φ 1 * lin ψ 1 = 1) (h₂ : lin ψ 1 * lin φ 1 = 1)
    (hg : IntM C i (lin φ 1)) (hg' : IntM C i (lin ψ 1)) (hl : IntM C i (bil lam 1 1)) :
    imLat C i (transH φ ψ lam) = stdH C d i := by
  ext y
  rw [mem_imLat]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact transH_mem_stdH C hg hg' hl hw
  · intro hy
    have hy' := (mem_stdH C).1 hy
    have a₁ := mulVec_mem_trivLat C hg' hy'.1
    have a₂ := mulVec_mem_trivLat C (fun a b => hl b a) a₁
    have a₃ := mulVec_mem_trivLat C (fun a b => hg b a) hy'.2
    refine ⟨((lin ψ 1).mulVec y.1, (lin φ 1).transpose.mulVec y.2 -
      (bil lam 1 1).transpose.mulVec ((lin ψ 1).mulVec y.1)),
      (mem_stdH C).2 ⟨a₁, sub_mem a₃ a₂⟩, ?_⟩
    have t : (lin ψ 1).transpose * (lin φ 1).transpose = 1 := by
      rw [← Matrix.transpose_mul, h₁, Matrix.transpose_one]
    rw [transH_apply]
    refine Prod.ext ?_ ?_
    · simp only [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]
    · simp only [sub_add_cancel, Matrix.mulVec_mulVec, t, Matrix.one_mulVec]

theorem hodge_family (φ ψ : C.I → Pt K 1 d) (lam : C.I → PS K 2 d)
    (h₁ : ∀ i, lin (φ i) 1 * lin (ψ i) 1 = 1) (h₂ : ∀ i, lin (ψ i) 1 * lin (φ i) 1 = 1) :
    ShortExact C (dotDual C fun i => colLat C i (lin (φ i) 1))
      (fun i => imLat C i (transH (φ i) (ψ i) (lam i))) (fun i => colLat C i (lin (φ i) 1))
      (LinearMap.inr K _ _) (LinearMap.fst K _ _) := by
  rw [dotDual_colLat C _ _ h₁ h₂]
  refine ⟨LinearMap.inr_injective, Function.Exact.inr_fst, LinearMap.fst_surjective,
    fun i x => ?_, fun i z => ?_⟩
  · rw [mem_colLat]
    simp only [LinearMap.inr_apply]
    rw [mem_imLat]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨(0, w), (mem_stdH C).2 ⟨zero_mem _, hw⟩, ?_⟩
      rw [transH_apply]
      simp
    · rintro ⟨w, hw, e⟩
      rw [transH_apply, Prod.mk.injEq] at e
      have hw' := (mem_stdH C).1 hw
      have e₁ : w.1 = 0 := by
        have := congrArg (lin (ψ i) 1).mulVec e.1
        simpa [Matrix.mulVec_mulVec, h₂ i] using this
      refine ⟨w.2, hw'.2, ?_⟩
      rw [← e.2, e₁]
      simp
  · rw [mem_colLat]
    simp only [LinearMap.fst_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨transH (φ i) (ψ i) (lam i) (w, 0), (mem_imLat C).2
        ⟨(w, 0), (mem_stdH C).2 ⟨hw, zero_mem _⟩, rfl⟩, ?_⟩
      rw [transH_apply]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hy
      exact ⟨w.1, ((mem_stdH C).1 hw).1, by rw [transH_apply]⟩

structure LocSplit (i : C.I) (a : (Fin d → K) →ₗ[K] VV K d) (b : VV K d →ₗ[K] Fin d → K) : Prop where

  a_int : ∀ u ∈ trivLat C d i, a u ∈ stdH C d i

  b_int : ∀ y ∈ stdH C d i, b y ∈ trivLat C d i

  zero : ∀ u, b (a u) = 0

  split : ∃ (r : VV K d →ₗ[K] Fin d → K) (s : (Fin d → K) →ₗ[K] VV K d),
    (∀ y ∈ stdH C d i, r y ∈ trivLat C d i) ∧ (∀ z ∈ trivLat C d i, s z ∈ stdH C d i) ∧
      (∀ u, r (a u) = u) ∧ (∀ z, b (s z) = z) ∧ ∀ y, a (r y) + s (b y) = y

theorem conj_family (p : ℕ) [Fact p.Prime] [CharP K p] (hI : Nonempty C.I)
    (g g' : C.I → Matrix (Fin d) (Fin d) K) (h₁ : ∀ i, g i * g' i = 1) (h₂ : ∀ i, g' i * g i = 1)
    (T : C.I → VV K d →ₗ[K] VV K d) (hT : ∀ i, Function.Bijective (T i))
    (α : (Fin d → K) →ₗ[K] VV K d) (β : VV K d →ₗ[K] Fin d → K)
    (a : C.I → (Fin d → K) →ₗ[K] VV K d) (b : C.I → VV K d →ₗ[K] Fin d → K)
    (hα : ∀ i u, α (((g i).map (· ^ p)).mulVec u) = T i (a i u))
    (hβ : ∀ i y, β (T i y) = ((g' i).transpose.map (· ^ p)).mulVec (b i y))
    (hloc : ∀ i, LocSplit C i (a i) (b i)) :
    ShortExact C (frobLat C p fun i => colLat C i (g i)) (fun i => imLat C i (T i))
      (frobLat C p (dotDual C fun i => colLat C i (g i))) α β := by
  have fm : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ p) = (frobenius K p).mapMatrix M :=
    fun _ => rfl
  have t₁ : ∀ i, (g' i).transpose * (g i).transpose = 1 := fun i => by
    rw [← Matrix.transpose_mul, h₁, Matrix.transpose_one]
  have t₂ : ∀ i, (g i).transpose * (g' i).transpose = 1 := fun i => by
    rw [← Matrix.transpose_mul, h₂, Matrix.transpose_one]
  have hF₂ : frobLat C p (dotDual C fun i => colLat C i (g i)) =
      fun i => colLat C i ((g' i).transpose.map (· ^ p)) := by
    rw [dotDual_colLat C g g' h₁ h₂]
    exact frobLat_colLat C p (fun i => (g' i).transpose) (fun i => (g i).transpose) t₁ t₂
  rw [hF₂, frobLat_colLat C p g g' h₁ h₂]
  have G₁ : ∀ i (u : Fin d → K), ((g i).map (· ^ p)).mulVec (((g' i).map (· ^ p)).mulVec u) = u :=
    fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, h₁, map_one, Matrix.one_mulVec]
  have G₂ : ∀ i (u : Fin d → K), ((g' i).map (· ^ p)).mulVec (((g i).map (· ^ p)).mulVec u) = u :=
    fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, h₂, map_one, Matrix.one_mulVec]
  have D₁ : ∀ i (u : Fin d → K), ((g' i).transpose.map (· ^ p)).mulVec
      (((g i).transpose.map (· ^ p)).mulVec u) = u :=
    fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, t₁, map_one, Matrix.one_mulVec]
  have D₂ : ∀ i (u : Fin d → K), ((g i).transpose.map (· ^ p)).mulVec
      (((g' i).transpose.map (· ^ p)).mulVec u) = u :=
    fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, t₂, map_one, Matrix.one_mulVec]
  obtain ⟨i₀⟩ := hI
  obtain ⟨r₀, s₀, -, -, ra₀, bs₀, as₀⟩ := (hloc i₀).split
  refine ⟨?_, ?_, ?_, fun i x => ?_, fun i z => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have e : T i₀ (a i₀ (((g' i₀).map (· ^ p)).mulVec x)) = 0 := by
      rw [← hα, G₁, hx]
    have e' : a i₀ (((g' i₀).map (· ^ p)).mulVec x) = 0 :=
      (hT i₀).1 (by rw [e, map_zero])
    have e'' := ra₀ (((g' i₀).map (· ^ p)).mulVec x)
    rw [e', map_zero] at e''
    rw [← G₁ i₀ x, ← e'', Matrix.mulVec_zero]
  · intro y
    obtain ⟨w, rfl⟩ := (hT i₀).2 y
    constructor
    · intro hy
      rw [hβ] at hy
      have e : b i₀ w = 0 := by
        rw [← D₂ i₀ (b i₀ w), hy, Matrix.mulVec_zero]
      have e' := as₀ w
      rw [e, map_zero, add_zero] at e'
      exact ⟨((g i₀).map (· ^ p)).mulVec (r₀ w), by rw [hα, e']⟩
    · rintro ⟨x, hx⟩
      have e : T i₀ w = T i₀ (a i₀ (((g' i₀).map (· ^ p)).mulVec x)) := by
        rw [← hα, G₁, hx]
      rw [e, hβ, (hloc i₀).zero, Matrix.mulVec_zero]
  · intro z
    refine ⟨T i₀ (s₀ (((g i₀).transpose.map (· ^ p)).mulVec z)), ?_⟩
    rw [hβ, bs₀, D₁]
  · obtain ⟨r, s, hr, hs, ra, bs, as⟩ := (hloc i).split
    rw [mem_colLat]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (mem_imLat C).2 ⟨a i w, (hloc i).a_int w hw, (hα i w).symm⟩
    · intro hx
      obtain ⟨w, hw, e⟩ := (mem_imLat C).1 hx
      have e' : w = a i (((g' i).map (· ^ p)).mulVec x) := (hT i).1 (by rw [e, ← hα, G₁])
      refine ⟨r w, hr w hw, ?_⟩
      rw [e', ra, G₁]
  · obtain ⟨r, s, hr, hs, ra, bs, as⟩ := (hloc i).split
    rw [mem_colLat]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨T i (s w), (mem_imLat C).2 ⟨s w, hs w hw, rfl⟩, by rw [hβ, bs]⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hy
      exact ⟨b i w, (hloc i).b_int w hw, (hβ i w).symm⟩

theorem intM_map (i : C.I) (M : Matrix (Fin d) (Fin d) (C.v i).valuationSubring) :
    IntM C i (M.map (C.v i).valuationSubring.subtype) := fun a b =>
  (Valuation.mem_valuationSubring_iff _ _).1 (M a b).2

omit [Field K] in
theorem matrix_eq_zero_of_mulVec {R : Type} [CommRing R] {M : Matrix (Fin d) (Fin d) R}
    (h : ∀ u, M.mulVec u = 0) : M = 0 := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa using this

variable {O : Type} [CommRing O] [StarRing O]

theorem locSplit_of_mats (B : FB K d O) (p : ℕ) (i : C.I) (r₁ r₂ s₁ s₂ : Matrix (Fin d) (Fin d) K)
    (ih : IntM C i (hw B p)) (ia : IntM C i (am B p)) (iS : IntM C i (bil B.sy 1 1))
    (ir₁ : IntM C i r₁) (ir₂ : IntM C i r₂) (is₁ : IntM C i s₁) (is₂ : IntM C i s₂)
    (hz : ∀ u, beta B p (alpha B p u) = 0)
    (e₁ : r₁ * hw B p + r₂ * (am B p).transpose = 1)
    (e₂ : (am B p - (hw B p).transpose * bil B.sy 1 1) * s₁ - (hw B p).transpose * s₂ = 1)
    (e₃ : hw B p * r₁ + s₁ * (am B p - (hw B p).transpose * bil B.sy 1 1) = 1)
    (e₄ : hw B p * r₂ - s₁ * (hw B p).transpose = 0)
    (e₅ : (am B p).transpose * r₁ + s₂ * (am B p - (hw B p).transpose * bil B.sy 1 1) = 0)
    (e₆ : (am B p).transpose * r₂ - s₂ * (hw B p).transpose = 1) :
    LocSplit C i (alpha B p) (beta B p) := by
  refine ⟨fun u hu => ?_, fun y hy => ?_, hz, ?_⟩
  · rw [alpha_apply]
    exact (mem_stdH C).2 ⟨mulVec_mem_trivLat C ih hu, mulVec_mem_trivLat C (fun a b => ia b a) hu⟩
  · have hy' := (mem_stdH C).1 hy
    rw [beta_apply, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    exact sub_mem (mulVec_mem_trivLat C (fun a b => ih b a) hy'.2)
      (sub_mem (mulVec_mem_trivLat C ia hy'.1) (mulVec_mem_trivLat C (fun a b => ih b a)
        (mulVec_mem_trivLat C iS hy'.1)))
  · let r : VV K d →ₗ[K] Fin d → K := Matrix.toLin' r₁ ∘ₗ LinearMap.fst K _ _ +
      Matrix.toLin' r₂ ∘ₗ LinearMap.snd K _ _
    let s : (Fin d → K) →ₗ[K] VV K d := LinearMap.prod (-Matrix.toLin' s₁) (-Matrix.toLin' s₂)
    have hr : ∀ y, r y = r₁.mulVec y.1 + r₂.mulVec y.2 := fun y => by simp [r]
    have hs : ∀ z, s z = (-(s₁.mulVec z), -(s₂.mulVec z)) := fun z => by simp [s]
    refine ⟨r, s, fun y hy => ?_, fun z hz' => ?_, fun u => ?_, fun z => ?_, fun y => ?_⟩
    · have hy' := (mem_stdH C).1 hy
      rw [hr]
      exact add_mem (mulVec_mem_trivLat C ir₁ hy'.1) (mulVec_mem_trivLat C ir₂ hy'.2)
    · rw [hs]
      exact (mem_stdH C).2 ⟨neg_mem (mulVec_mem_trivLat C is₁ hz'),
        neg_mem (mulVec_mem_trivLat C is₂ hz')⟩
    · rw [hr, alpha_apply]
      simp only [Matrix.mulVec_mulVec, ← Matrix.add_mulVec, e₁, Matrix.one_mulVec]
    · have E : ((am B p - (hw B p).transpose * bil B.sy 1 1) * s₁).mulVec z -
          ((hw B p).transpose * s₂).mulVec z = z := by
        rw [← Matrix.sub_mulVec, e₂, Matrix.one_mulVec]
      rw [hs, beta_apply]
      simp only [Matrix.mulVec_neg, Matrix.mulVec_mulVec]
      calc _ = ((am B p - (hw B p).transpose * bil B.sy 1 1) * s₁).mulVec z -
          ((hw B p).transpose * s₂).mulVec z := by abel
        _ = z := E
    · have E₃ : (hw B p * r₁).mulVec y.1 +
          (s₁ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1 = y.1 := by
        rw [← Matrix.add_mulVec, e₃, Matrix.one_mulVec]
      have E₄ : (hw B p * r₂).mulVec y.2 - (s₁ * (hw B p).transpose).mulVec y.2 = 0 := by
        rw [← Matrix.sub_mulVec, e₄, Matrix.zero_mulVec]
      have E₅ : ((am B p).transpose * r₁).mulVec y.1 +
          (s₂ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1 = 0 := by
        rw [← Matrix.add_mulVec, e₅, Matrix.zero_mulVec]
      have E₆ : ((am B p).transpose * r₂).mulVec y.2 - (s₂ * (hw B p).transpose).mulVec y.2 = y.2 := by
        rw [← Matrix.sub_mulVec, e₆, Matrix.one_mulVec]
      rw [alpha_apply, hs, hr, beta_apply]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_sub,
          Matrix.mulVec_mulVec]
        calc _ = ((hw B p * r₁).mulVec y.1 +
              (s₁ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1) +
            ((hw B p * r₂).mulVec y.2 - (s₁ * (hw B p).transpose).mulVec y.2) := by abel
          _ = y.1 := by rw [E₃, E₄, add_zero]
      · simp only [Prod.snd_add, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_sub,
          Matrix.mulVec_mulVec]
        calc _ = (((am B p).transpose * r₁).mulVec y.1 +
              (s₂ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1) +
            (((am B p).transpose * r₂).mulVec y.2 - (s₂ * (hw B p).transpose).mulVec y.2) := by abel
          _ = y.2 := by rw [E₅, E₆, zero_add]

theorem locSplit {p : ℕ} [Fact p.Prime] [CharP K p] (F : Family C p d O) (i : C.I) :
    LocSplit C i (alpha (F.BK i) p) (beta (F.BK i) p) := by
  haveI : CharP (C.v i).valuationSubring p :=
    (RingHom.charP_iff (C.v i).valuationSubring.subtype Subtype.val_injective p).2 inferInstance
  have mK := GlobalTheory.T.formal_data_base_change _ _ (C.v i).valuationSubring.subtype d O (F.Bi i) (F.BK i) (F.mapK i)
  have mk := GlobalTheory.T.formal_data_base_change _ _ (IsLocalRing.residue _) d O (F.Bi i) (F.Bk i) (F.mapk i)
  have iz : am (F.Bi i) p * hw (F.Bi i) p -
      (hw (F.Bi i) p).transpose * bil (F.Bi i).sy 1 1 * hw (F.Bi i) p -
      (hw (F.Bi i) p).transpose * (am (F.Bi i) p).transpose = 0 := by
    have h0 := matrix_eq_zero_of_mulVec (M := (hw (F.Bi i) p).transpose * (am (F.Bi i) p).transpose -
        am (F.Bi i) p * hw (F.Bi i) p +
        (hw (F.Bi i) p).transpose * bil (F.Bi i).sy 1 1 * hw (F.Bi i) p) fun u => by
      rw [← beta_alpha_apply]
      exact LinearMap.congr_fun (GlobalTheory.T.alpha_beta_adjoint_exact _ p d O (F.Bi i)).2 u
    rw [← neg_eq_zero, ← h0]
    abel
  have inj : ∀ u : Fin d → IsLocalRing.ResidueField (C.v i).valuationSubring,
      ((hw (F.Bi i) p).map (IsLocalRing.residue _)).mulVec u = 0 →
      ((am (F.Bi i) p).transpose.map (IsLocalRing.residue _)).mulVec u = 0 → u = 0 := by
    intro u h1 h2
    apply F.inj i
    rw [map_zero, alpha_apply, (mk.2.2 p).1, (mk.2.2 p).2, ← Matrix.transpose_map, h1, h2]
    rfl
  obtain ⟨r₁, r₂, s₁, s₂, e₁, e₂, e₃, e₄, e₅, e₆⟩ := GlobalTheory.T.local_matrix_coprime_decomposition _ d _ _ _ iz inj
  let Φ := (C.v i).valuationSubring.subtype.mapMatrix (m := Fin d)
  have hT : ∀ M, Φ M.transpose = (Φ M).transpose := fun M => rfl
  have hh : hw (F.BK i) p = Φ (hw (F.Bi i) p) := (mK.2.2 p).1
  have ha : am (F.BK i) p = Φ (am (F.Bi i) p) := (mK.2.2 p).2
  have hS : bil (F.BK i).sy 1 1 = Φ (bil (F.Bi i).sy 1 1) := mK.2.1
  have c₁ := congrArg Φ e₁
  have c₂ := congrArg Φ e₂
  have c₃ := congrArg Φ e₃
  have c₄ := congrArg Φ e₄
  have c₅ := congrArg Φ e₅
  have c₆ := congrArg Φ e₆
  simp only [map_add, map_sub, map_mul, map_one, map_zero, hT] at c₁ c₂ c₃ c₄ c₅ c₆
  refine locSplit_of_mats C (F.BK i) p i (Φ r₁) (Φ r₂) (Φ s₁) (Φ s₂) ?_ ?_ ?_
    (intM_map C i _) (intM_map C i _) (intM_map C i _) (intM_map C i _)
    (fun u => LinearMap.congr_fun (GlobalTheory.T.alpha_beta_adjoint_exact K p d O (F.BK i)).2 u) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hh]; exact intM_map C i _
  · rw [ha]; exact intM_map C i _
  · rw [hS]; exact intM_map C i _
  all_goals simp only [hh, ha, hS]
  exacts [c₁, c₂, c₃, c₄, c₅, c₆]

theorem rhoH_mem_stdH (i : C.I) (B₀ : FB (C.v i).valuationSubring d O) (B : FB K d O)
    (h : IsMapOf (C.v i).valuationSubring.subtype B₀ B) (a : O) {w : VV K d}
    (hw : w ∈ stdH C d i) : rhoH B a w ∈ stdH C d i := by
  obtain ⟨hm, -⟩ := GlobalTheory.T.formal_data_base_change _ _ (C.v i).valuationSubring.subtype d O B₀ B h
  have hr : ∀ b, IntM C i (rho B b) := fun b => by rw [(hm b).1]; exact intM_map C i _
  have ha : IntM C i (bil (B.ad a) 1 1) := by rw [(hm a).2]; exact intM_map C i _
  rw [mem_stdH] at hw ⊢
  rw [rhoH_apply]
  exact ⟨mulVec_mem_trivLat C (hr a) hw.1, sub_mem (mulVec_mem_trivLat C (fun x y => hr _ y x) hw.2)
    (mulVec_mem_trivLat C (fun x y => ha y x) hw.1)⟩

theorem family_conj : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (F : Family C p d O), Nonempty C.I →
    ∃ D : ConjData C p O d, (∀ a, D.ρ a = rho F.B a) ∧
      ∀ i u, u ∈ D.lie i ↔ ∀ j, C.v i ((lin (F.ψ i) 1).mulVec u j) ≤ 1 := by
  intro K _ C p _ _ d O _ _ F hI
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.formal_group_action_ring_hom K d O F.B
  obtain ⟨⟨ρH, hρH⟩, -, -⟩ := GlobalTheory.T.formal_hermitian_action_pairing K d O F.B
  have iso := fun i => GlobalTheory.T.formal_isomorphism_transport K d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  have h₁ := fun i => (iso i).1
  have h₂ := fun i => (iso i).2.1
  have hT := fun i => (iso i).2.2.1
  have hc := fun i => (iso i).2.2.2.2.1
  have good : ∀ i, (∀ a b, C.v i (lin (F.φ i) 1 a b) ≤ 1 ∧ C.v i (lin (F.ψ i) 1 a b) ≤ 1 ∧
      C.v i (bil (F.lam i) 1 1 a b) ≤ 1) → IntM C i (lin (F.φ i) 1) ∧ IntM C i (lin (F.ψ i) 1) ∧
        IntM C i (bil (F.lam i) 1 1) := fun i h =>
    ⟨fun a b => (h a b).1, fun a b => (h a b).2.1, fun a b => (h a b).2.2⟩
  have hiso := fun i => GlobalTheory.T.alpha_beta_isomorphism_transport K p d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  refine ⟨{ lie := fun i => colLat C i (lin (F.φ i) 1)
            H := fun i => imLat C i (transH (F.φ i) (F.ψ i) (F.lam i))
            lie_bun := isBun_colLat C _ _ h₁ h₂ (F.ae.subset fun i hi h => hi ?_)
            H_bun := isBun_imLat C _ hT (F.ae.subset fun i hi h => hi ?_)
            ρ := ρ
            ρH := ρH
            ρH_hom := fun a i x hx => ?_
            ρH_fst := fun a y => ?_
            ρH_inr := fun a φ => ?_
            hodge := hodge_family C _ _ _ h₁ h₂
            α := alpha F.B p
            β := beta F.B p
            conj := conj_family C p hI _ _ h₁ h₂ _ hT _ _ _ _ (fun i u => (hiso i).1 u)
              (fun i y => (hiso i).2 y) (fun i => locSplit C F i)
            α_act := fun a u => ?_
            β_act := fun a y => ?_ }, hρ, fun i u => mem_colLat_iff C (h₁ i) (h₂ i)⟩
  · exact ⟨(good i h).1, (good i h).2.1⟩
  · obtain ⟨g₁, g₂, g₃⟩ := good i h
    exact imLat_transH_eq C (h₁ i) (h₂ i) g₁ g₂ g₃
  · obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hx
    rw [hρH]
    refine (mem_imLat C).2 ⟨rhoH (F.BK i) a w, rhoH_mem_stdH C i (F.Bi i) (F.BK i) (F.mapK i) a hw, ?_⟩
    exact (LinearMap.congr_fun (hc i a) w).symm
  · rw [hρH, rhoH_fst, hρ]
  · rw [hρH, rhoH_inr, hρ]
  · rw [hρ, hρH]
    exact GlobalTheory.T.alpha_equivariant_frobenius K p d O F.B a u
  · rw [hρ, hρH]
    exact GlobalTheory.T.beta_equivariant_frobenius K p d O F.B a y

end GlobalTheory.CompanionTheory.Ar.Conj.Fam
