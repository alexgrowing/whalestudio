import Development.EtaleCohomology.EtaleSheaves.LeafDegCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafVanBPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev bpl (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) (U : B.Etale) {A : Type} [CommRing A] (t : Sp A ⟶ U.left) (m : ℤ) :=
  rpl q i (prB ι U) (pullback.fst (t ≫ U.hom) ι)
    (pullback.map (t ≫ U.hom) ι U.hom ι t (𝟙 W) (𝟙 B) (by simp) (by simp)) t (pullback.lift_fst _ _ _).symm m

def LeafVanBStalk : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (m : ℤ)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] [IsLocalRing A] (t : Sp A ⟶ U.left), SH A → IsUnit (q : A) → bpl q i ι U t m c = 0) →
  Cov U (fun _ a => rB q i ι a m c = 0)

def LeafRelVanOfH : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ),
  Subsingleton (H R E F n) → Function.Surjective (pull R f F (n - 1)) → Subsingleton (Hrel R f F n)

theorem relVanOfH : LeafRelVanOfH := by
  intro R _ F U E f n hE hs
  suffices h : ∀ y : Hrel R f F n, y = 0 from ⟨fun y₁ y₂ => by rw [h y₁, h y₂]⟩
  intro y
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective y
  set φ := (chains R).map f with hφ
  let a : Cocycle ((chains R).obj E) (res R F) n := zcomp (Cocycle.ofHom (mappingCone.inr φ)) z (zero_add n)
  have ha : CohomologyClass.mk a = 0 := hE.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at ha
  obtain ⟨α, hα⟩ := ha
  let b : Cochain ((chains R).obj U) (res R F) (n - 1) := (mappingCone.inl φ).comp z.1 (by omega)
  have hz : z.1 = mappingCone.descCochain φ b a.1 (by omega) := by
    rw [mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
    simp [b, a, zcomp, mappingCone.inl_descCochain, mappingCone.inr_descCochain]
  have h0 : δ n (n + 1) z.1 = 0 := Cocycle.δ_eq_zero z (n + 1)
  rw [hz, mappingCone.δ_descCochain _ _ _ _ (n + 1) rfl] at h0
  have h1 := congrArg (fun x => (mappingCone.inl φ).comp x (show -1 + (n + 1) = n by omega)) h0
  simp only [Cochain.comp_add, Cochain.comp_zero, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, add_zero] at h1
  have hδα : δ (n - 1) n α = a.1 := hα
  let b' : Cochain ((chains R).obj U) (res R F) (n - 1) :=
    b - n.negOnePow • (Cochain.ofHom φ).comp α (zero_add _)
  have hb' : δ (n - 1) n b' = 0 := by
    have e1 : δ (n - 1) n b = -((n + 1).negOnePow • (Cochain.ofHom φ).comp a.1 (zero_add n)) := eq_neg_of_add_eq_zero_left h1
    simp only [b', δ_sub, δ_units_smul, e1, Int.negOnePow_succ]
    simp
    rw [hδα, sub_self]
  obtain ⟨g, hg⟩ := hs (CohomologyClass.mk (Cocycle.mk b' n (by omega) hb'))
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective g
  have hg' : CohomologyClass.mk (Cocycle.mk b' n (by omega) hb' - zcomp (Cocycle.ofHom φ) γ (zero_add _)) = 0 := by
    rw [CohomologyClass.mk_sub, ← hg]; exact sub_eq_zero.mpr rfl
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 2) (by omega)] at hg'
  obtain ⟨ε, hε⟩ := hg'
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨mappingCone.descCochain φ ε (α + n.negOnePow • γ.1) (by omega), ?_⟩
  have hε' : δ (n - 2) (n - 1) ε = b' - (Cochain.ofHom φ).comp γ.1 (zero_add _) := hε
  have hX : δ (n - 2) (n - 1) ε + n.negOnePow • (Cochain.ofHom φ).comp (α + n.negOnePow • γ.1) (zero_add _) = b := by
    rw [hε']
    simp only [b', Cochain.comp_add, Cochain.comp_units_smul, smul_add, smul_smul, Int.units_mul_self, one_smul]
    abel
  have hY : δ (n - 1) n (α + n.negOnePow • γ.1) = a.1 := by
    rw [δ_add, δ_units_smul, hδα, Cocycle.δ_eq_zero γ n, smul_zero, add_zero]
  rw [mappingCone.δ_descCochain _ _ _ _ n (by omega), hX, hY, hz]
  rfl

def LeafClosedSH : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  (∀ n : ℤ, 0 < n → Subsingleton (H (ZMod q) (sch.obj W') (tw q i) n)) ∧
  Function.Surjective (pull (ZMod q) (sch.map ι') (tw q i) 0)

def LeafClosedSHPos : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A →
  IsUnit (q : A) → ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  ∀ n : ℤ, 0 < n → Subsingleton (H (ZMod q) (sch.obj W') (tw q i) n)

def LeafClosedSH0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A →
  IsUnit (q : A) → ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  Function.Surjective (pull (ZMod q) (sch.map ι') (tw q i) 0)

theorem closedSH_of (h1 : LeafClosedSHPos) (h2 : LeafClosedSH0) : LeafClosedSH :=
  fun hy q _ i A _ _ hA hq _ ι' _ => ⟨h1 hy q i A hA hq ι', h2 hy q i A hA hq ι'⟩

theorem heightFunctionalStatement_of_pairingProperties (hy : Hyps) : B2 := hy.2.2.2.2.2.2.2.2.2.2.2.1

theorem vanBPt (hC : LeafClosedSH) (hy : Hyps) (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A]
    [IsLocalRing A] (hA : SH A) (hq : IsUnit (q : A)) {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'] (m : ℤ)
    (hm : 0 < m) : Subsingleton (Hrel (ZMod q) (sch.map ι') (tw q i) m) := by
  obtain ⟨hW, hs⟩ := hC hy q i A hA hq ι'
  refine relVanOfH (ZMod q) (tw q i) (sch.map ι') m (heightFunctionalStatement_of_pairingProperties hy (ZMod q) A hA (tw q i) m hm) ?_
  rcases eq_or_lt_of_le (show (1 : ℤ) ≤ m by omega) with h | h
  · subst h; simpa using hs
  · have := hW (m - 1) (by omega)
    intro y; exact ⟨0, Subsingleton.elim _ _⟩

theorem LeafVanB_of (hS : LeafVanBStalk) (hP : LeafClosedSHPos) (h0 : LeafClosedSH0) : LeafVanB := by
  have hC := closedSH_of hP h0
  intro hy q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV p g1 g2 h1 h2 h3 hsh U m hm c
  exact hS hy q k hq i s ι U m c (fun A _ _ t hA hqA =>
    (vanBPt hC hy q i A hA hqA (pullback.fst (t ≫ U.hom) ι) m hm).elim _ _)

end LateralTheory.E.LeafVanBPf
