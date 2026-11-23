import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc

namespace GlobalTheory.Unfold.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gmap_one (Λ : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) Λ = Λ := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_mul (a b : GV D) (Λ : LV D) : Formalism.HermitianLatticesTheory.gmap (a * b) Λ = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b Λ) := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem adapt_one {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : Adapt (1 : GV D) F F :=
  ⟨Subgroup.one_mem _, fun a => by simp⟩

theorem adapt_mapLF {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (g : GV D) (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    Adapt g F (mapLF g F) := by
  refine ⟨hg, fun a => ?_⟩
  have : frame (mapLF g F) a = g (frame F a) := by
    simp only [mapLF, dif_pos hg, frame, FlagG.fvec, mapFlag]
    refine Fin.lastCases ?_ (fun i => ?_) a <;> simp
  rw [this]; simp

theorem adapt_zero {T : D.host.E} {F G : LFlag (VS D) D.R.rS T} {g : GV D} (h : Adapt g F G) :
    g (frame F 0) = frame G 0 := by
  have := h.2 0
  simpa [Xflag, FlagG.Xa, sub_eq_zero] using this

theorem unitriangular_lattice_stabiliser_sub_frame_automorphisms {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (Λ : LV D) : NLam Λ F ⊆ Aut0 F Λ := by
  rintro n ⟨⟨h1, h2⟩, h3, h4⟩
  refine ⟨⟨h1, fun a => ?_⟩, h2⟩
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have hz : frame F (Fin.last _) ∈ orth (VS D) (Xsp F) := by
      simp only [orth, Submodule.mem_iInf, frame, FlagG.fvec, Fin.snoc_last, LinearMap.mem_ker]
      intro x hx
      refine Submodule.span_induction (p := fun x _ => (VS D).hT x F.fl.z = 0) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨a, rfl⟩; exact F.fl.z_orth a
      · simp
      · intro x y _ _ a b; simp [a, b]
      · intro c x _ a; simp [a]
    have := h4 _ hz
    have e : Xflag F (Fin.last D.R.rS).val = Xsp F := by
      simp only [Xflag, FlagG.Xa, Xsp, FlagG.X, Fin.val_last]
      congr 1; ext v; simp
    rwa [e]
  · apply h3
    apply Submodule.subset_span
    exact ⟨i, by simp, by simp [frame, FlagG.fvec]⟩

section
variable {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')

def StabilizingSubgroup : Subgroup (GV D) where
  carrier := H0 F F'
  one_mem' := ⟨Subgroup.one_mem _, fun _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    exact ⟨Subgroup.mul_mem _ a1 b1, fun i => by simp [a2, b2], fun i => by simp [a3, b3]⟩
  inv_mem' := by
    rintro a ⟨a1, a2, a3⟩
    refine ⟨Subgroup.inv_mem _ a1, fun i => ?_, fun i => ?_⟩
    · conv_lhs => rw [← a2 i]
      simp
    · conv_lhs => rw [← a3 i]
      simp

theorem one_mem_stabL (Λ : LV D) : (1 : GV D) ∈ stabL F F' Λ := ⟨(StabilizingSubgroup F F').one_mem, by rw [gmap_one]⟩

theorem mem_gmap (h : GV D) (Λ : LV D) (x) : x ∈ Formalism.HermitianLatticesTheory.gmap h Λ ↔ h.symm x ∈ Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨_, hx, by simp⟩

theorem gmap_inf (h : GV D) (A B : LV D) : Formalism.HermitianLatticesTheory.gmap h (A ⊓ B) = Formalism.HermitianLatticesTheory.gmap h A ⊓ Formalism.HermitianLatticesTheory.gmap h B := by
  ext x; simp [mem_gmap]

theorem gmap_sup (h : GV D) (A B : LV D) : Formalism.HermitianLatticesTheory.gmap h (A ⊔ B) = Formalism.HermitianLatticesTheory.gmap h A ⊔ Formalism.HermitianLatticesTheory.gmap h B :=
  Submodule.map_sup _ _ _

theorem fix_X {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {h : GV D} (hf : ∀ a, h (frame F a) = frame F a) {x}
    (hx : x ∈ Xsp F) : h x = x := by
  refine Submodule.span_induction (p := fun v _ => h v = v) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, rfl⟩; simpa [frame, FlagG.fvec] using hf a.castSucc
  · simp
  · intro x y _ _ a b; simp [a, b]
  · intro c x _ a; simp [a]

theorem mem_X_iff {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {h : GV D} (hf : ∀ a, h (frame F a) = frame F a) (x) :
    h x ∈ Xsp F ↔ x ∈ Xsp F := by
  constructor
  · intro hx
    have := fix_X F hf hx
    rw [← h.injective this]; exact hx
  · intro hx; rw [fix_X F hf hx]; exact hx

theorem mem_orth_iff {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {h : GV D} (hi : h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hf : ∀ a, h (frame F a) = frame F a) (x) : h x ∈ orth (VS D) (Xsp F) ↔ x ∈ orth (VS D) (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall₂_congr fun v hv => ?_
  conv_lhs => rw [← fix_X F hf hv, hi]

theorem gmap_X {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {h : GV D} (hf : ∀ a, h (frame F a) = frame F a) :
    Formalism.HermitianLatticesTheory.gmap h (toO (VS D) (Xsp F)) = toO (VS D) (Xsp F) := by
  ext x; rw [mem_gmap]
  have := mem_X_iff F hf (h.symm x)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem gmap_orth {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {h : GV D} (hi : h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hf : ∀ a, h (frame F a) = frame F a) :
    Formalism.HermitianLatticesTheory.gmap h (toO (VS D) (orth (VS D) (Xsp F))) = toO (VS D) (orth (VS D) (Xsp F)) := by
  ext x; rw [mem_gmap]
  have := mem_orth_iff F hi hf (h.symm x)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem Lrep_gmap {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {h : GV D} (hi : h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hf : ∀ a, h (frame F a) = frame F a) (Λ : LV D) : Lrep (Formalism.HermitianLatticesTheory.gmap h Λ) F = Formalism.HermitianLatticesTheory.gmap h (Lrep Λ F) := by
  rw [Lrep, Lrep, gmap_inf, gmap_orth F hi hf]

theorem Lsub_gmap {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {h : GV D} (hi : h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hf : ∀ a, h (frame F a) = frame F a) (Λ : LV D) : Lsub (Formalism.HermitianLatticesTheory.gmap h Λ) F = Formalism.HermitianLatticesTheory.gmap h (Lsub Λ F) := by
  rw [Lsub, Lsub, gmap_inf, gmap_sup, gmap_orth F hi hf, gmap_X F hf, Lrep_gmap F hi hf]

theorem NgX_gmap {h : GV D} (hh : h ∈ H0 F F') (Λ : LV D) (g : ℕ) :
    NgX (Formalism.HermitianLatticesTheory.gmap h Λ) g F F' = Formalism.HermitianLatticesTheory.gmap h (NgX Λ g F F') := by
  rw [NgX, NgX, gmap_sup, gmap_sup, XLam, XLam, XLam, XLam, gmap_inf, gmap_inf, gmap_X F hh.2.1, gmap_X F' hh.2.2]
  congr 2
  exact (Submodule.map_smul'' _ _ _).symm

theorem gdat_gmap {h : GV D} (hh : h ∈ H0 F F') (Λ : LV D) :
    gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = (Formalism.HermitianLatticesTheory.gmap h (gdat F F' Λ).1, Formalism.HermitianLatticesTheory.gmap h (gdat F F' Λ).2.1,
      {p | (h.symm p.1, h.symm p.2) ∈ (gdat F F' Λ).2.2}) := by
  simp only [gdat, Lsub_gmap F hh.1 hh.2.1, Lsub_gmap F' hh.1 hh.2.2, Lrep_gmap F hh.1 hh.2.1,
    Lrep_gmap F' hh.1 hh.2.2, NgX_gmap F F' hh, mem_gmap, Prod.mk.injEq, true_and]
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨l', h1, l, h2, h3, h4, h5⟩
    refine ⟨_, h1, _, h2, ?_, ?_, by rwa [map_sub] at h5⟩
    · rw [← mem_X_iff F' hh.2.2]; simpa using h3
    · rw [← mem_X_iff F hh.2.1]; simpa using h4
  · rintro ⟨l', h1, l, h2, h3, h4, h5⟩
    refine ⟨h l', by simpa using h1, h l, by simpa using h2, ?_, ?_, by simpa using h5⟩
    · rw [← mem_X_iff F' hh.2.2] at h3; simpa using h3
    · rw [← mem_X_iff F hh.2.1] at h4; simpa using h4

theorem gdat_congr {h : GV D} (hh : h ∈ H0 F F') {Λ₁ Λ₂ : LV D} (e : gdat F F' Λ₁ = gdat F F' Λ₂) :
    gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ₁) = gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ₂) := by
  rw [gdat_gmap F F' hh, gdat_gmap F F' hh, e]

theorem lrel_equivalence : Equivalence (LRel F F') := by
  refine ⟨fun Λ => ⟨1, one_mem_stabL F F' Λ⟩, ?_, ?_⟩
  · rintro a b ⟨h, hh, e⟩
    have hi : h⁻¹ ∈ H0 F F' := (StabilizingSubgroup F F').inv_mem hh
    refine ⟨h⁻¹, hi, ?_⟩
    rw [← gdat_congr F F' hi e, ← gmap_mul, inv_mul_cancel, gmap_one]
  · rintro a b c ⟨h, hh, e⟩ ⟨k, hk, e'⟩
    refine ⟨k * h, (StabilizingSubgroup F F').mul_mem hk hh, ?_⟩
    rw [gmap_mul, gdat_congr F F' hk e, e']

theorem lrel_gmap (Λ : LV D) {h : GV D} (hh : h ∈ H0 F F') : LRel F F' Λ (Formalism.HermitianLatticesTheory.gmap h Λ) := ⟨h, hh, rfl⟩

variable {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}

theorem ext_unique (p : PlF D) (g : GV D) (a b : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (ha : Ext p g a) (hb : Ext p g b) : a = b := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range (span_baseChange_eq_top p)
  intro x
  simp [ha x, hb x]

theorem moves_one' {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {E : Type} [CommRing E] [Algebra K E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model K E} {V : Type} [AddCommGroup V] [Module E V]
    {H : Loc.HermSp M V} {r : ℕ} {P : LocNG.FPair H r} (d : LocNG.Datum P) : LocNG.Datum.Moves 1 d d := by
  refine ⟨fun x y h => ?_, fun x y h => ?_, fun x' y' x y h' h => ?_⟩
  · have e : y = x := Subtype.ext h
    rw [e]
  · have e : y = x := Subtype.ext h
    rw [e]
  · have e : y = x := Subtype.ext h
    have e' : y' = x' := Subtype.ext h'
    rw [e, e']

theorem moves_one {p : PlF D} (d : LocNG.Datum (FP p)) : LocNG.Datum.Moves 1 d d := moves_one' d

theorem one_mem_stabY (y : Dat Z FP) : (1 : GV D) ∈ stabY F F' y :=
  ⟨(StabilizingSubgroup F F').one_mem, fun p => ⟨1, fun _ => rfl, moves_one _⟩⟩

theorem inGen_self (y : Dat Z FP) : InGen y y :=
  ⟨fun p => ⟨1, Subgroup.one_mem _, moves_one _⟩, by simp⟩

theorem weight_le_one (y : Dat Z FP) : (((stabY F F' y).encard : ℝ≥0∞))⁻¹ ≤ 1 := by
  rw [ENNReal.inv_le_one]
  have : (1 : ℕ∞) ≤ (stabY F F' y).encard := Set.one_le_encard_iff_nonempty.2 ⟨1, one_mem_stabY F F' y⟩
  exact_mod_cast this

theorem grel_symm {y y' : Dat Z FP} (h : GRel F F' y y') : GRel F F' y' y := by
  obtain ⟨h, hh, hm⟩ := h
  refine ⟨h⁻¹, (StabilizingSubgroup F F').inv_mem hh, fun p => ?_⟩
  obtain ⟨g, hg, m1, m2, m3⟩ := hm p
  refine ⟨g⁻¹, fun x => ?_, fun x y e => ?_, fun x y e => ?_, fun x' y' x y e' e => ?_⟩
  · have := hg (h⁻¹ x)
    simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at this ⊢
    rw [← this]; simp
  · exact (m1 y x (by rw [e]; simp)).symm
  · exact (m2 y x (by rw [e]; simp)).symm
  · exact (m3 y' x' y x (by rw [e']; simp) (by rw [e]; simp)).symm

theorem perp_of_fix {p : PlF D} (f : Fin (D.R.rS + 1) → Vp D p) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)
    (hu : LocNG.IsUnitary (locH Z p) g) (hf : ∀ a, g (f a) = f a) (x : Vp D p)
    (hx : x ∈ (locH Z p).perp ((locH Z p).X f)) : g x ∈ (locH Z p).perp ((locH Z p).X f) := by
  intro v hv
  have hv' : g v = v := by
    refine Submodule.span_induction (p := fun v _ => g v = v) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨a, rfl⟩; exact hf _
    · simp
    · intro x y _ _ a b; simp [a, b]
    · intro c x _ a; simp [a]
  rw [← hv', hu]; exact hx v hv

theorem h_add_right (p : PlF D) (x y y' : Vp D p) : (locH Z p).h x (y + y') = (locH Z p).h x y + (locH Z p).h x y' := by
  show LocFacts₂ _ _ _ _ = LocFacts₂ _ _ _ _ + LocFacts₂ _ _ _ _
  simp only [LocFacts₂, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]

theorem h_smul_right (p : PlF D) (c) (x y : Vp D p) : (locH Z p).h x (c • y) = (Z.M p).L.cj c * (locH Z p).h x y := by
  show LocFacts₂ _ _ _ _ = _ * LocFacts₂ _ _ _ _
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ext_unitary {p : PlF D} {h : GV D} (hh : h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {g} (hg : Ext p h g) :
    LocNG.IsUnitary (locH Z p) g := by
  have key : ∀ a b, (locH Z p).h (g (baseChange₂ D p a)) (g (baseChange₂ D p b)) = (locH Z p).h (baseChange₂ D p a) (baseChange₂ D p b) := by
    intro a b
    rw [hg, hg]
    show LocFacts₂ _ _ _ _ = LocFacts₂ _ _ _ _
    rw [baseChangeAt_form _ _ (Z.hcj p), baseChangeAt_form _ _ (Z.hcj p)]
    simp only [brS]; rw [hh]
  have z1 : ∀ y, (locH Z p).h 0 y = 0 := fun y => by
    have := (locH Z p).h_smul_left 0 0 y; simpa using this
  have z2 : ∀ x, (locH Z p).h x 0 = 0 := fun x => by
    have := h_smul_right (Z := Z) p 0 x 0; simpa using this
  intro x y
  have hx : x ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by rw [span_baseChange_eq_top]; trivial
  have hy : y ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by rw [span_baseChange_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | zero => rw [map_zero, z1, z1]
  | add a b _ _ ha hb => rw [map_add, (locH Z p).h_add_left, (locH Z p).h_add_left, ha, hb]
  | smul c a _ ha => rw [map_smul, (locH Z p).h_smul_left, (locH Z p).h_smul_left, ha]
  | mem a ha =>
    obtain ⟨a, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | zero => rw [map_zero, z2, z2]
    | add a b _ _ ha hb => rw [map_add, h_add_right, h_add_right, ha, hb]
    | smul c a _ ha => rw [map_smul, h_smul_right, h_smul_right, ha]
    | mem b hb => obtain ⟨b, rfl⟩ := hb; exact key a b

end

section
variable {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {Tn T'n : ℕ}
  {F : LFlag (VS D) D.R.rS (Tn : D.host.E)} {F' : LFlag (VS D) D.R.rS (T'n : D.host.E)}

theorem grel_equivalence (hB : Based Z FP Tn T'n F F') : Equivalence (GRel (Z := Z) (FP := FP) F F') := by
  refine ⟨fun y => ⟨1, one_mem_stabY F F' y⟩, grel_symm F F', ?_⟩
  rintro y₁ y₂ y₃ ⟨h, hh, hm⟩ ⟨k, hk, km⟩
  refine ⟨k * h, (StabilizingSubgroup F F').mul_mem hk hh, fun p => ?_⟩
  obtain ⟨g, hg, m1, m2, m3⟩ := hm p
  obtain ⟨g', hg', n1, n2, n3⟩ := km p
  have hu : LocNG.IsUnitary (locH Z p) g := ext_unitary hh.1 hg
  have hA : ∀ a, g ((FP p).A.f a) = (FP p).A.f a := fun a => by
    rw [(hB p).1]; simp only [map_smul]; rw [hg, hh.2.1]
  have hB' : ∀ a, g ((FP p).B.f a) = (FP p).B.f a := fun a => by
    rw [(hB p).2.1]; simp only [map_smul]; rw [hg, hh.2.2]
  refine ⟨g' * g, fun x => ?_, fun x y e => ?_, fun x y e => ?_, fun x' y' x y e' e => ?_⟩
  · show g' (g _) = baseChange₂ D p (k (h x)); rw [hg, hg']
  · exact (m1 x ⟨g x, perp_of_fix _ g hu hA x x.2⟩ rfl).trans (n1 _ y e)
  · exact (m2 x ⟨g x, perp_of_fix _ g hu hB' x x.2⟩ rfl).trans (n2 _ y e)
  · exact (m3 x' ⟨g x', perp_of_fix _ g hu hB' x' x'.2⟩ x ⟨g x, perp_of_fix _ g hu hA x x.2⟩ rfl rfl).trans
      (n3 _ y' _ y e' e)

theorem grel_out (hB : Based Z FP Tn T'n F F') (y : Dat Z FP) :
    GRel F F' (Quot.mk (GRel (Z := Z) (FP := FP) F F') y).out y :=
  ((grel_equivalence hB).eqvGen_iff).1 (Quot.eqvGen_exact (Quot.out_eq _))

end

section
variable {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}
theorem tg_self (t : TauC Y u u') : TG (lf D (X.Fu u)) t.frame t t.lam :=
  ⟨1, adapt_one _, adapt_one _, (gmap_one _).symm⟩

theorem clsRow_row (TS : Set (TauC Y u u')) : ClsRow TS (Y.tO u u').rowOf := fun _ _ _ _ _ => Iff.rfl
theorem clsRow_key (TS : Set (TauC Y u u')) : ClsRow TS key := fun t _ t' _ h => by
  simp [key, h]
end

end GlobalTheory.Unfold.Model
