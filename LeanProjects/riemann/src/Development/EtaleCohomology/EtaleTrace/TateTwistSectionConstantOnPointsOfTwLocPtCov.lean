import Development.EtaleCohomology.EtaleTrace.EtaleTateTwistSectionConstantOnPointsOfConnected
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def ConnLoc : Prop := ∀ {X : Scheme.{0}}, ConnectedSpace X → ∀ (P Q : ∀ V : Scheme.{0}, (V ⟶ X) → Prop),
  (∀ (V W : Scheme.{0}) (g : V ⟶ X) (h : W ⟶ V), P V g → P W (h ≫ g)) →
  (∀ (V W : Scheme.{0}) (g : V ⟶ X) (h : W ⟶ V), Q V g → Q W (h ≫ g)) →
  (∀ (V : Scheme.{0}) (g : V ⟶ X), IsEmpty V → P V g ∧ Q V g) →
  (∀ (V : Scheme.{0}) (g : V ⟶ X), P V g → Q V g → IsEmpty V) →
  Loc X (fun V g => P V g ∨ Q V g) → Loc X P ∨ Loc X Q

def PtLift : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (z : S k ⟶ X)
  (R : ∀ V : Scheme.{0}, (V ⟶ X) → Prop), Loc X R →
    ∃ (V : Scheme.{0}) (g : V ⟶ X) (w : S k ⟶ V), R V g ∧ w ≫ g = z

theorem ConnLoc_pf : ConnLoc := by
  intro X hX P Q hPs hQs hE hD hL
  obtain ⟨Sv, hSv, hSs⟩ := hL
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hSv
  have hi : ∀ i, P (𝒰.X i) (𝒰.f i) ∨ Q (𝒰.X i) (𝒰.f i) := fun i => hSs _ _ (h𝒰 _ _ (Presieve.ofArrows.mk i))
  have hcov := ((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1
  have hop : ∀ i, IsOpen (Set.range (𝒰.f i)) := fun i => by
    haveI : Etale (𝒰.f i) := 𝒰.map_prop i
    exact (𝒰.f i).isOpenMap.isOpen_range
  let A : Set X := ⋃ (i) (_ : P (𝒰.X i) (𝒰.f i)), Set.range (𝒰.f i)
  let B : Set X := ⋃ (i) (_ : ¬ P (𝒰.X i) (𝒰.f i)), Set.range (𝒰.f i)
  have hAo : IsOpen A := isOpen_iUnion fun i => isOpen_iUnion fun _ => hop i
  have hBo : IsOpen B := isOpen_iUnion fun i => isOpen_iUnion fun _ => hop i
  have hAB : ∀ x, x ∈ A ∨ x ∈ B := by
    intro x
    obtain ⟨i, hx⟩ := hcov x
    by_cases h : P (𝒰.X i) (𝒰.f i)
    · exact Or.inl (Set.mem_iUnion₂.2 ⟨i, h, hx⟩)
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨i, h, hx⟩)
  have hdis : ∀ x, x ∈ A → x ∈ B → False := by
    intro x hA hB
    obtain ⟨i, hPi, a, ha⟩ := Set.mem_iUnion₂.1 hA
    obtain ⟨j, hPj, b, hb⟩ := Set.mem_iUnion₂.1 hB
    have hQj : Q (𝒰.X j) (𝒰.f j) := (hi j).resolve_left hPj
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝒰.f i) (g := 𝒰.f j) a b (ha.trans hb.symm)
    have h1 := hPs _ _ _ (pullback.fst (𝒰.f i) (𝒰.f j)) hPi
    have h2 := hQs _ _ _ (pullback.snd (𝒰.f i) (𝒰.f j)) hQj
    rw [← pullback.condition] at h2
    exact (hD _ _ h1 h2).false z
  have hAc : IsClosed A := by
    have : A = Bᶜ := by
      ext x; constructor
      · intro hA hB; exact hdis x hA hB
      · intro hB; exact (hAB x).resolve_right hB
    rw [this]; exact hBo.isClosed_compl
  have hmem := Scheme.Cover.mem_grothendieckTopology 𝒰
  rcases isClopen_iff.1 ⟨hAc, hAo⟩ with h0 | h1
  · right
    refine ⟨_, hmem, fun V g hg => ?_⟩
    obtain ⟨W, h, g', ⟨i⟩, rfl⟩ := hg
    apply hQs
    by_cases hP : P (𝒰.X i) (𝒰.f i)
    · refine (hE _ _ ⟨fun a => ?_⟩).2
      have : 𝒰.f i a ∈ A := Set.mem_iUnion₂.2 ⟨i, hP, a, rfl⟩
      rw [h0] at this; exact this
    · exact (hi i).resolve_left hP
  · left
    refine ⟨_, hmem, fun V g hg => ?_⟩
    obtain ⟨W, h, g', ⟨i⟩, rfl⟩ := hg
    apply hPs
    by_cases hP : P (𝒰.X i) (𝒰.f i)
    · exact hP
    · refine (hE _ _ ⟨fun a => ?_⟩).1
      have hb : 𝒰.f i a ∈ B := Set.mem_iUnion₂.2 ⟨i, hP, a, rfl⟩
      have ha : 𝒰.f i a ∈ A := by rw [h1]; trivial
      exact hdis _ ha hb

theorem res_id' {q : ℕ} {U : Scheme.{0}} (x : Sec (tw q 0) U) : Sec.res (𝟙 U) x = x := by
  simp only [Sec.res, op_id]
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem res_sub' {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec (tw q 0) U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub _ _ _

theorem PtLift_of (hC : PtCov) : PtLift := by
  intro k _ _ X z R hR
  obtain ⟨Sv, hSv, hSs⟩ := hR
  have hpb : Sv.pullback z ∈ Scheme.etaleTopology (S k) := Scheme.etaleTopology.pullback_stable z hSv
  obtain ⟨T, hT, hTs⟩ := hC k (𝟙 (S k)) inferInstance (Sv.pullback z) hpb
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hT
  have hne : Nonempty (S k) := inferInstance
  obtain ⟨i, -⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1 (Classical.choice hne)
  obtain ⟨U, g', h, hg', -, w, hw⟩ := hTs _ (𝒰.f i) (h𝒰 _ _ (Presieve.ofArrows.mk i))
  refine ⟨U, g' ≫ z, w, hSs _ _ hg', ?_⟩
  rw [Category.comp_id] at hw
  rw [← Category.assoc, hw, Category.id_comp]

theorem tateTwistSection_constantOnPoints_of_connLoc_lift (hT : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hL : ConnLoc) (hP : PtLift) : EtaleTateTwistSectionConstantOnPointsOfConnectedProper := by
  intro l _ k _ _ hl j X p hp s hX y y'
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : ((l ^ j : ℕ) : k) ≠ 0 := by push_cast; exact pow_ne_zero _ hl
  obtain ⟨ζ0⟩ := primK k (l ^ j) hq
  let φ : k →+* Γ(X, ⊤) := (p.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let v0 := Sec.res y.1 s
  let t := s - Sec.res p v0
  have key : ∀ z : Pt p, Sec.res z.1 t = Sec.res z.1 s - v0 := by
    intro z
    show Sec.res z.1 (s - Sec.res p v0) = _
    rw [res_sub', ← res_comp, z.2, res_id']
  have hne : Nonempty (S k) := inferInstance
  let P : ∀ V : Scheme.{0}, (V ⟶ X) → Prop := fun V g => ∀ (W : Scheme.{0}) (h : W ⟶ V), Nonempty W → Sec.res (h ≫ g) t = 0
  let Q : ∀ V : Scheme.{0}, (V ⟶ X) → Prop := fun V g => ∀ (W : Scheme.{0}) (h : W ⟶ V), Nonempty W → Sec.res (h ≫ g) t ≠ 0
  have hPs : ∀ (V W : Scheme.{0}) (g : V ⟶ X) (h : W ⟶ V), P V g → P W (h ≫ g) := by
    intro V W g h hg W' h' hW'
    rw [← Category.assoc]; exact hg W' (h' ≫ h) hW'
  have hQs : ∀ (V W : Scheme.{0}) (g : V ⟶ X) (h : W ⟶ V), Q V g → Q W (h ≫ g) := by
    intro V W g h hg W' h' hW'
    rw [← Category.assoc]; exact hg W' (h' ≫ h) hW'
  have hE : ∀ (V : Scheme.{0}) (g : V ⟶ X), IsEmpty V → P V g ∧ Q V g := by
    intro V g hV
    exact ⟨fun W h hW => (hV.false (h.base (Classical.choice hW))).elim,
      fun W h hW => (hV.false (h.base (Classical.choice hW))).elim⟩
  have hD : ∀ (V : Scheme.{0}) (g : V ⟶ X), P V g → Q V g → IsEmpty V := by
    intro V g hPg hQg
    by_contra hV
    rw [not_isEmpty_iff] at hV
    exact hQg V (𝟙 V) hV (hPg V (𝟙 V) hV)
  have hPQ : Loc X (fun V g => P V g ∨ Q V g) := by
    obtain ⟨Sv, hSv, hSs⟩ := (hT (l ^ j) 0).1 X (ζ0.map φ) t
    refine ⟨Sv, hSv, fun V g hg => ?_⟩
    obtain ⟨c, hc⟩ := hSs V g hg
    by_cases hqc : l ^ j ∣ c
    · left
      intro W h _
      rw [res_comp, hc, res_nsmul]
      obtain ⟨m, rfl⟩ := hqc
      rw [mul_comm]
      first
        | (rw [mul_nsmul, q_nsmul, nsmul_zero])
        | (rw [mul_nsmul', q_nsmul, nsmul_zero])
        | (rw [mul_nsmul', q_nsmul, smul_zero])
        | (rw [mul_nsmul, q_nsmul, smul_zero])
    · right
      intro W h hW hz
      haveI := hW
      apply hqc
      rw [res_comp, hc, res_nsmul, (hT (l ^ j) 0).2.2] at hz
      exact (hT (l ^ j) 0).2.1 W _ c hz
  have hy0 : Sec.res y.1 t = 0 := by rw [key]; exact sub_self _
  rcases hL hX P Q hPs hQs hE hD hPQ with hLP | hLQ
  · obtain ⟨V, g, w, hg, hw⟩ := hP k y'.1 P hLP
    have h1 := hg (S k) w hne
    rw [hw, key, sub_eq_zero] at h1
    exact h1.symm
  · obtain ⟨V, g, w, hg, hw⟩ := hP k y.1 Q hLQ
    exact absurd (by rw [hw]; exact hy0) (hg (S k) w hne)

theorem tateTwistSection_constantOnPoints_of_twLoc_ptCov (hT : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hC : PtCov) : EtaleTateTwistSectionConstantOnPointsOfConnectedProper :=
  tateTwistSection_constantOnPoints_of_connLoc_lift hT ConnLoc_pf (PtLift_of hC)

end LateralTheory.EtaleTrace
