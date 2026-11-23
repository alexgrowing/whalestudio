import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.CmpOfMemX
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemZeroSubCoe

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Pass

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def Xd (i : ZMod n) (k : ℕ) : Submodule O (W.DD T) :=
  (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).map (W.π₀ • (LinearMap.id : W.DD T →ₗ[O] W.DD T)) ⊔
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.PhiPullΔ W T i).map
      ((Formalism.MainNotions.LiftingTheory.qp W ^ k) • (LinearMap.id : W.DD T →ₗ[O] W.DD T))

theorem NDl_N {i : ZMod n} {x : W.DD T} (hx : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) : x ∈ W.N T := by
  have h : x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x := hx
  exact h.1

theorem NDl_DL {i : ZMod n} {x : W.DD T} (hx : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x := by
  have h : x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x := hx
  exact h.2

def Kc (i : ZMod n) : Submodule O ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) where
  carrier := {z | Formalism.MainNotions.ArcLiftingSetup.cmpD W T (z : W.DD T) = 0}
  add_mem' := fun {a b} ha hb => by
    show Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((a : W.DD T) + b) = 0
    rw [cmpD_add W T (NDl_N W T a.2) (NDl_N W T b.2)]
    rw [show Formalism.MainNotions.ArcLiftingSetup.cmpD W T (a : W.DD T) = 0 from ha,
      show Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b : W.DD T) = 0 from hb, add_zero]
  zero_mem' := cmpD_zero W T
  smul_mem' := fun o z hz => by
    show Formalism.MainNotions.ArcLiftingSetup.cmpD W T (o • (z : W.DD T)) = 0
    rw [cmpD_osmul W T o (NDl_N W T z.2), show Formalism.MainNotions.ArcLiftingSetup.cmpD W T (z : W.DD T) = 0 from hz,
      smul_zero]

theorem mem_Kc {i : ZMod n} (z : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)) :
    z ∈ Kc W T i ↔ Formalism.MainNotions.ArcLiftingSetup.cmpD W T (z : W.DD T) = 0 := Iff.rfl

theorem Kc_le [IsDomain O] (i : ZMod n) (k : ℕ) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    Kc W T i ≤ (Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype := by
  intro z hz
  obtain ⟨y, hyN, hyΔ, hzy⟩ := ker_NDl W T i h3 hmod hR z.2 hz
  rw [pow_one] at hzy
  have hzl : (letE i : LetA O n) • (z : W.DD T) = z := (NDl_DL W T z.2).1
  have hE := Formalism.MainNotions.LiftingTheory.idempotent_mem_invariants W i
  have hyE : (letE i : LetA O n) • y ∈ W.NΔ T :=
    Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T hE ⟨hyN, hyΔ⟩
  refine Submodule.mem_sup_left (Submodule.mem_map.2 ⟨(letE i : LetA O n) • y, ?_, ?_⟩)
  · exact ⟨hyE.1, by rw [smul_smul, letE_sq], hyE.2⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [aself_comm W T, ← hzy, hzl]
    rfl

theorem pchain_DN (i : ZMod n) (k : ℕ) {m : ℕ} {cc : ℝ} {FF : Type} [AddCommGroup FF]
    [Module O FF] (K : Submodule O ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i))
    (hK : K ≤ (Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype) (s : Finset (W.DD T))
    (hs : s.card ≤ m) (hsN : (↑s : Set (W.DD T)) ⊆ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) (L kO : ℕ)
    (hL : Module.length O (↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸
      (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype) ≤ (L : ℕ∞))
    (hkO : lenOl PD (O := O) = kO) (hLc : (L : ℝ) ≤ cc * kO) (A : Submodule O FF)
    (ψ : ↥A →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain (lenOl PD (O := O)) m cc A
      (kerSub A ψ (((Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype).map K.mkQ)) 1 1 := by
  set X := (Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hXdef
  set Y := (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hYdef
  have hXY : X ≤ Y := Submodule.comap_mono le_sup_left
  have hKY : K ≤ Y := hK.trans hXY
  have hlen : Module.length O ((↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) ⧸ Y.map K.mkQ) ≤ (L : ℕ∞) := by
    rw [(Submodule.quotientQuotientEquivQuotient K Y hKY).length_eq]
    exact hL
  have h1 := pstep_len (m := m) (c := cc) A ψ (Y.map K.mkQ) L kO hlen hkO hLc
  set A₁ := kerSub A ψ (Y.map K.mkQ) with hA₁def
  have hA₁ : A₁ ≤ A := kerSub_le A ψ _
  set ψ₁ : ↥A₁ →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K := ψ.comp (Submodule.inclusion hA₁)
  set sN : Finset ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) := s.subtype (· ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)
  set s' := sN.image K.mkQ
  have hcard : s'.card ≤ m := by
    refine Finset.card_image_le.trans (le_trans ?_ hs)
    rw [Finset.card_subtype]
    exact Finset.card_filter_le _ _
  have hspan : Submodule.span O (↑s : Set (W.DD T)) =
      (Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i))).map
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype := by
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hsN hy⟩, Finset.mem_subtype.2 hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact Finset.mem_subtype.1 hz
  have hY : Y ≤ X ⊔ Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)) := by
    intro z hz
    have hz' : (z : W.DD T) ∈ Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T)) := hz
    obtain ⟨x, hx, t, ht, hxt⟩ := Submodule.mem_sup.1 hz'
    rw [hspan] at ht
    obtain ⟨t', ht', rfl⟩ := Submodule.mem_map.1 ht
    have hxN : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i := by
      have e : x = (z : W.DD T) - (t' : W.DD T) := by rw [← hxt]; simp
      rw [e]; exact (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).sub_mem z.2 t'.2
    refine Submodule.mem_sup.2 ⟨⟨x, hxN⟩, hx, t', ht', Subtype.ext ?_⟩
    simpa using hxt
  have hgen : ∀ a, ψ₁ a ∈ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
    intro a
    have ha : ψ ⟨(a : FF), hA₁ a.2⟩ ∈ Y.map K.mkQ := (mem_kerSub_coe A ψ _ ⟨a, hA₁ a.2⟩).1 a.2
    have hle : Y.map K.mkQ ≤ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
      calc Y.map K.mkQ ≤ (X ⊔ Submodule.span O (↑sN : Set _)).map K.mkQ := Submodule.map_mono hY
        _ = X.map K.mkQ ⊔ (Submodule.span O (↑sN : Set _)).map K.mkQ := Submodule.map_sup _ _ _
        _ = X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
          rw [Submodule.map_span, Finset.coe_image]
    exact hle ha
  have h2 := pstep_gen (lenO := lenOl PD (O := O)) (m := m) (c := cc) A₁ ψ₁ (X.map K.mkQ) s' hcard hgen
  have heq : kerSub A₁ ψ₁ (X.map K.mkQ) = kerSub A ψ (X.map K.mkQ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := (mem_kerSub A₁ ψ₁ _ x).1 hx
      exact (mem_kerSub A ψ _ x).2 ⟨hA₁ hx1, hx2⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := (mem_kerSub A ψ _ x).1 hx
      have hx1' : x ∈ A₁ := (mem_kerSub A ψ _ x).2 ⟨hx1, Submodule.map_mono hXY hx2⟩
      exact (mem_kerSub A₁ ψ₁ _ x).2 ⟨hx1', hx2⟩
  rw [heq] at h2
  exact (pchain_of_len h1).trans (pchain_of_gen h2)

end Pass

end Formalism.MainNotions.N.Pv.LocalLengthBound
