import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cris GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.Points

namespace CrystallinePoints.Pd

variable {X Y Y' : Scheme.{0}}

abbrev Inn {B : Type} [CommRing B] (y : Sp B ⟶ Y) (U : Y.Opens) : Prop := ⊤ ≤ y ⁻¹ᵁ U

section
variable {B B' : Type} [CommRing B] [CommRing B'] {y : Sp B ⟶ Y} {U V : Y.Opens}

theorem Inn.map (h : Inn y U) (ρ : B →+* B') : Inn (spMap ρ ≫ y) U :=
  fun p _ ↦ h (Set.mem_univ ((spMap ρ) p))

theorem Inn.mono (h : Inn y U) (e : U ≤ V) : Inn y V := fun _ hp ↦ e (h hp)

theorem Inn.inf (h : Inn y U) (h' : Inn y V) : Inn y (U ⊓ V) := fun _ hp ↦ ⟨h hp, h' hp⟩

theorem valR_resU (e : V ≤ U) (h : Inn y V) (f : Γ(Y, U)ˣ) : valR y V (res e f).val = valR y U f.val :=
  valR_res y e h f.val

theorem valR_inv_mul (h : Inn y U) (f : Γ(Y, U)ˣ) : valR y U (f⁻¹).val * valR y U f.val = 1 := by
  rw [← valR_mul _ _ h, Units.inv_mul, valR_one _ _ h]

end

def zs (Y : Scheme.{0}) : Y ⟶ Sp ℤ := specZIsTerminal.from Y

@[reducible] def zPt (B : Type) [CommRing B] (y : Sp B ⟶ Y) : Pt (zs Y) where
  B := B
  x := y
  w := specZIsTerminal.hom_ext _ _

theorem exists_sec_cover {J : Type} (W : J → Y.Opens) (U : Y.Opens) (h1 : ∀ j, W j ≤ U) (h2 : U ≤ ⨆ j, W j)
    (F : ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → B)
    (hF : ∀ (j : J) (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y (W j) →
      F B' (spMap ρ ≫ y) = ρ (F B y)) :
    ∃ f : Γ(Y, U), ∀ (j : J) (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y (W j) → F B y = valR y U f := by
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover ℤ Y (zs Y) J W U h1 h2 (fun P ↦ F P.B P.x) fun j P Q φ hP ↦ by
    have := hF j P.B Q.B (φ.ρ : P.B →+* Q.B) P.x hP
    rw [φ.pt] at this
    exact this
  exact ⟨f, fun j B _ y h ↦ hf j (zPt B y) h⟩

theorem sec_ext_cover {J : Type} (W : J → Y.Opens) (hW : ⨆ j, W j = ⊤) (V : Y.Opens) (f g : Γ(Y, V))
    (H : ∀ (j : J) (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y V → Inn y (W j) → valR y V f = valR y V g) :
    f = g :=
  eq_of_valR_eq_on_cover (zs Y) W hW V f g fun P j h h' ↦ H j P.B P.x h h'

theorem sec_ext (V : Y.Opens) (f g : Γ(Y, V))
    (H : ∀ (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y V → valR y V f = valR y V g) : f = g :=
  sec_ext_cover (fun _ : Unit ↦ ⊤) (by simp) V f g fun _ B _ y h _ ↦ H B y h

theorem exists_sec (U : Y.Opens) (F : ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → B)
    (hF : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y U →
      F B' (spMap ρ ≫ y) = ρ (F B y)) :
    ∃ f : Γ(Y, U), ∀ (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y U → F B y = valR y U f := by
  obtain ⟨f, hf⟩ := exists_sec_cover (fun _ : Unit ↦ U) U (fun _ ↦ le_rfl) (by simp) F fun _ ↦ hF
  exact ⟨f, hf ()⟩

theorem exists_unit (U : Y.Opens) (F : ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → Bˣ)
    (hF : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y U →
      (F B' (spMap ρ ≫ y)).val = ρ (F B y).val) :
    ∃ f : Γ(Y, U)ˣ, ∀ (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y U → (F B y).val = valR y U f.val := by
  obtain ⟨a, ha⟩ := exists_sec U (fun B _ y ↦ (F B y).val) hF
  obtain ⟨b, hb⟩ := exists_sec U (fun B _ y ↦ ((F B y)⁻¹).val) fun B B' _ _ ρ y h ↦ by
    have e1 := hF B B' ρ y h
    have e2 : ((F B' (spMap ρ ≫ y))⁻¹).val * (F B' (spMap ρ ≫ y)).val = 1 := Units.inv_mul _
    have e3 : ρ ((F B y)⁻¹).val * ρ (F B y).val = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    change ((F B' (spMap ρ ≫ y))⁻¹).val = ρ ((F B y)⁻¹).val
    rw [e1] at e2
    linear_combination ρ ((F B y)⁻¹).val * e2 - ((F B' (spMap ρ ≫ y))⁻¹).val * e3
  have hab : a * b = 1 := sec_ext U _ _ fun B _ y h ↦ by
    rw [valR_mul _ _ h, valR_one _ _ h, ← ha B y h, ← hb B y h]
    exact Units.mul_inv _
  exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, ha⟩

abbrev Kap (Y : Scheme.{0}) : Type 1 :=
  ∀ (B B' : Type) [CommRing B] [CommRing B'] (_ : B →+* B') (_ : Sp B ⟶ Y), B'

def Rel (N : LB Y) (κ : Kap Y) : Prop :=
  ∃ w : N.ι → ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → Bˣ,
    (∀ (i j : N.ι) (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y (N.U i) → Inn y (N.U j) →
      (w i B y).val = valR y (N.U i ⊓ N.U j) (N.g i j).val * (w j B y).val) ∧
    ∀ (i : N.ι) (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y (N.U i) →
      (w i B' (spMap ρ ≫ y)).val = ρ (w i B y).val * κ B B' ρ y

variable {N N' : LB Y} {κ κ' κ'' : Kap Y}

theorem Rel.twist (h : Rel N κ) (u : ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → Bˣ)
    (e : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y),
      κ' B B' ρ y * ρ (u B y).val = κ B B' ρ y * (u B' (spMap ρ ≫ y)).val) : Rel N κ' := by
  obtain ⟨w, h1, h2⟩ := h
  refine ⟨fun i B _ y ↦ w i B y * u B y, fun i j B _ y hi hj ↦ ?_, fun i B B' _ _ ρ y hi ↦ ?_⟩
  · simp only [Units.val_mul]
    rw [h1 i j B y hi hj, mul_assoc]
  · simp only [Units.val_mul, map_mul]
    rw [h2 i B B' ρ y hi]
    linear_combination -ρ (w i B y).val * e B B' ρ y

theorem Rel.congr (h : Rel N κ)
    (e : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), κ' B B' ρ y = κ B B' ρ y) :
    Rel N κ' :=
  h.twist (fun _ _ _ ↦ 1) fun B B' _ _ ρ y ↦ by rw [e, Units.val_one, Units.val_one, map_one]

theorem Rel.triv (h : Rel N κ)
    (e : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), κ B B' ρ y = 1) :
    ∃ t : LB.Gen N, t.IsGen := by
  obtain ⟨w, h1, h2⟩ := h
  choose t ht using fun i ↦ exists_unit (N.U i) (w i) fun B B' _ _ ρ y hi ↦ by
    rw [h2 i B B' ρ y hi, e, mul_one]
  refine ⟨⟨t⟩, fun i j ↦ Units.ext (sec_ext _ _ _ fun B _ y hy ↦ ?_)⟩
  have hi := hy.mono inf_le_left
  have hj := hy.mono inf_le_right
  rw [Units.val_mul, valR_mul _ _ hy, valR_resU _ hy, valR_resU _ hy]
  exact (ht i B y hi).symm.trans ((h1 i j B y hi hj).trans (congrArg _ (ht j B y hj)))

theorem Rel.div (h : Rel N κ) (h' : Rel N' κ')
    (e : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y),
      κ'' B B' ρ y * κ' B B' ρ y = κ B B' ρ y) : Rel (LB.div N N') κ'' := by
  obtain ⟨w, h1, h2⟩ := h
  obtain ⟨w', h1', h2'⟩ := h'
  refine ⟨fun p B _ y ↦ w p.1 B y * (w' p.2 B y)⁻¹, fun p q B _ y hp hq ↦ ?_, fun p B B' _ _ ρ y hp ↦ ?_⟩
  · have hp' : Inn y (N.U p.1 ⊓ N'.U p.2) := hp
    have hq' : Inn y (N.U q.1 ⊓ N'.U q.2) := hq
    have hy : Inn y (N.U p.1 ⊓ N'.U p.2 ⊓ (N.U q.1 ⊓ N'.U q.2)) := hp'.inf hq'
    have a1 := h1 p.1 q.1 B y (hp'.mono inf_le_left) (hq'.mono inf_le_left)
    have a2 := h1' p.2 q.2 B y (hp'.mono inf_le_right) (hq'.mono inf_le_right)
    have a3 := valR_inv_mul ((hp'.mono inf_le_right).inf (hq'.mono inf_le_right)) (N'.g p.2 q.2)
    have a4 : ((w' p.2 B y)⁻¹).val * (w' p.2 B y).val = 1 := Units.inv_mul _
    have a5 : ((w' q.2 B y)⁻¹).val * (w' q.2 B y).val = 1 := Units.inv_mul _
    have a6 : valR y ((LB.div N N').U p ⊓ (LB.div N N').U q) ((LB.div N N').g p q).val =
        valR y (N.U p.1 ⊓ N.U q.1) (N.g p.1 q.1).val * valR y (N'.U p.2 ⊓ N'.U q.2) ((N'.g p.2 q.2)⁻¹).val := by
      refine (valR_mul y _ hy _ _).trans (congrArg₂ (· * ·) (valR_resU _ hy _) ?_)
      exact valR_resU (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) hy
        (N'.g p.2 q.2)⁻¹
    rw [a6]
    simp only [Units.val_mul]
    rw [a2] at a4
    rw [a1]
    generalize valR y (N.U p.1 ⊓ N.U q.1) (N.g p.1 q.1).val = G at *
    generalize valR y (N'.U p.2 ⊓ N'.U q.2) ((N'.g p.2 q.2)⁻¹).val = Gi at *
    generalize valR y (N'.U p.2 ⊓ N'.U q.2) (N'.g p.2 q.2).val = G' at *
    generalize ((w' p.2 B y)⁻¹).val = a at *
    generalize ((w' q.2 B y)⁻¹).val = b at *
    generalize (w' q.2 B y).val = c at *
    generalize (w q.1 B y).val = d at *
    have k : a = Gi * b := by linear_combination (-a * b * c) * a3 - a * a5 + Gi * b * a4
    rw [k]; ring
  · have hp' : Inn y (N.U p.1 ⊓ N'.U p.2) := hp
    have a1 := h2 p.1 B B' ρ y (hp'.mono inf_le_left)
    have a2 := h2' p.2 B B' ρ y (hp'.mono inf_le_right)
    have a4 : ((w' p.2 B' (spMap ρ ≫ y))⁻¹).val * (w' p.2 B' (spMap ρ ≫ y)).val = 1 := Units.inv_mul _
    have a5 : ρ ((w' p.2 B y)⁻¹).val * ρ (w' p.2 B y).val = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    simp only [Units.val_mul, map_mul]
    rw [a2] at a4
    rw [a1, ← e]
    generalize ((w' p.2 B' (spMap ρ ≫ y))⁻¹).val = a' at *
    generalize ρ ((w' p.2 B y)⁻¹).val = a at *
    generalize ρ (w' p.2 B y).val = c at *
    have k : a' * κ' B B' ρ y = a := by linear_combination a * a4 - a' * κ' B B' ρ y * a5
    rw [← k]; ring

theorem Rel.cls_eq (hN : N.IsLB) (hN' : N'.IsLB) (h : Rel N κ) (h' : Rel N' κ) : cls N hN = cls N' hN' := by
  have := (cls_eq_zero_iff (LB.isLB_div hN hN')).2
    ((h.div (κ'' := fun _ _ _ _ _ _ ↦ 1) h' fun _ _ _ _ _ _ ↦ one_mul _).triv fun _ _ _ _ _ _ ↦ rfl)
  rwa [cls_div hN hN', sub_eq_zero] at this

theorem Rel.pull (h : Rel N κ) (ψ : Y' ⟶ Y) : Rel (N.pull ψ) fun B B' _ _ ρ y ↦ κ B B' ρ (y ≫ ψ) := by
  obtain ⟨w, h1, h2⟩ := h
  have hin : ∀ (j : PUnit → N.ι) (B : Type) [CommRing B] (y : Sp B ⟶ Y'), Inn y ((N.pull ψ).U j) →
      Inn (y ≫ ψ) (N.U (j PUnit.unit)) := fun j B _ y h p _ ↦
    LB.wchart_le N (K := PUnit) (fun _ ↦ ψ) j PUnit.unit (h (Set.mem_univ p))
  refine ⟨fun j B _ y ↦ w (j PUnit.unit) B (y ≫ ψ), fun i j B _ y hi hj ↦ ?_, fun i B B' _ _ ρ y hi ↦ ?_⟩
  · refine (h1 _ _ B _ (hin i B y hi) (hin j B y hj)).trans (congrArg (· * _) ?_)
    have a := (hin i B y hi).inf (hin j B y hj)
    have b := hi.inf hj
    exact (valR_eq _ _ a _).trans ((GlobalTheory.DeRham.evalAt_pull_g N ψ y i j a b).trans (valR_eq y _ b _).symm)
  · have := h2 _ B B' ρ _ (hin i B y hi)
    rw [← Category.assoc] at this
    exact this

theorem exists_rel {I : Type} (U : I → Y.Opens) (hU : ⨆ i, U i = ⊤) (κ : Kap Y)
    (w : I → ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → Bˣ)
    (h2 : ∀ (i : I) (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y (U i) →
      (w i B' (spMap ρ ≫ y)).val = ρ (w i B y).val * κ B B' ρ y) :
    ∃ g : ∀ i j, Γ(Y, U i ⊓ U j)ˣ, LB.IsLB ⟨I, U, g⟩ ∧ Rel ⟨I, U, g⟩ κ := by
  choose g hg using fun i j ↦ exists_unit (U i ⊓ U j) (fun B _ y ↦ w i B y * (w j B y)⁻¹) fun B B' _ _ ρ y h ↦ by
    have a1 := h2 i B B' ρ y (h.mono inf_le_left)
    have a2 := h2 j B B' ρ y (h.mono inf_le_right)
    have a4 : ((w j B' (spMap ρ ≫ y))⁻¹).val * (w j B' (spMap ρ ≫ y)).val = 1 := Units.inv_mul _
    have a5 : ρ ((w j B y)⁻¹).val * ρ (w j B y).val = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    simp only [Units.val_mul, map_mul]
    rw [a2] at a4
    rw [a1]
    generalize ((w j B' (spMap ρ ≫ y))⁻¹).val = a' at *
    generalize ρ ((w j B y)⁻¹).val = a at *
    generalize ρ (w j B y).val = c at *
    have k : a' * κ B B' ρ y = a := by linear_combination a * a4 - a' * κ B B' ρ y * a5
    rw [← k]; ring
  refine ⟨g, ⟨hU, fun i ↦ Units.ext (sec_ext _ _ _ fun B _ y hy ↦ ?_),
    fun i j k ↦ Units.ext (sec_ext _ _ _ fun B _ y hy ↦ ?_)⟩, w, fun i j B _ y hi hj ↦ ?_, h2⟩
  · have hy' : Inn y (U i) := hy
    refine (valR_resU _ hy' _).trans (Eq.trans ?_ (valR_one y _ hy').symm)
    rw [← hg i i B y (hy'.inf hy'), mul_inv_cancel, Units.val_one]
  · have hy' : Inn y (U i ⊓ U j ⊓ U k) := hy
    have hi : Inn y (U i) := hy'.mono (inf_le_left.trans inf_le_left)
    have hj : Inn y (U j) := hy'.mono (inf_le_left.trans inf_le_right)
    have hk : Inn y (U k) := hy'.mono inf_le_right
    refine (valR_mul y _ hy' _ _).trans ((congrArg₂ (· * ·) (valR_resU _ hy' _) (valR_resU _ hy' _)).trans
      (Eq.trans ?_ (valR_resU _ hy' _).symm))
    change valR y (U i ⊓ U j) (g i j).val * valR y (U j ⊓ U k) (g j k).val = valR y (U i ⊓ U k) (g i k).val
    rw [← hg i j B y (hi.inf hj), ← hg j k B y (hj.inf hk), ← hg i k B y (hi.inf hk), ← Units.val_mul]
    congr 1
    group
  · change _ = valR y (U i ⊓ U j) (g i j).val * _
    rw [← hg i j B y (hi.inf hj), ← Units.val_mul, inv_mul_cancel_right]

theorem Rel.exists_of_triv (h : Rel N κ) (ht : ∃ t : LB.Gen N, t.IsGen) :
    ∃ W V : N.ι → ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → B,
      (∀ (i : N.ι) (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y (N.U i) → W i B y * V i B y = 1) ∧
      (∀ (i j : N.ι) (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y (N.U i) → Inn y (N.U j) → W i B y = W j B y) ∧
      ∀ (i : N.ι) (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y (N.U i) →
        W i B' (spMap ρ ≫ y) = ρ (W i B y) * κ B B' ρ y := by
  obtain ⟨w, h1, h2⟩ := h
  obtain ⟨t, ht⟩ := ht
  refine ⟨fun i B _ y ↦ (w i B y).val * valR y (N.U i) ((t.s i)⁻¹).val,
    fun i B _ y ↦ ((w i B y)⁻¹).val * valR y (N.U i) (t.s i).val, fun i B _ y hi ↦ ?_, fun i j B _ y hi hj ↦ ?_,
    fun i B B' _ _ ρ y hi ↦ ?_⟩
  · have a := valR_inv_mul hi (t.s i)
    have b : (w i B y).val * ((w i B y)⁻¹).val = 1 := Units.mul_inv _
    linear_combination (w i B y).val * ((w i B y)⁻¹).val * a + b
  · have a := valR_inv_mul hi (t.s i)
    have b := valR_inv_mul hj (t.s j)
    have hy := hi.inf hj
    have c := congrArg (fun u : Γ(Y, N.U i ⊓ N.U j)ˣ ↦ valR y (N.U i ⊓ N.U j) u.val) (ht i j)
    simp only [Units.val_mul] at c
    rw [valR_mul _ _ hy, valR_resU _ hy, valR_resU _ hy] at c
    have d := h1 i j B y hi hj
    rw [c] at a
    simp only
    rw [d]
    generalize valR y (N.U i ⊓ N.U j) (N.g i j).val = G at *
    generalize valR y (N.U i) ((t.s i)⁻¹).val = p at *
    generalize valR y (N.U j) ((t.s j)⁻¹).val = q at *
    generalize valR y (N.U j) (t.s j).val = r at *
    have k : G * p = q := by linear_combination q * a - G * p * b
    rw [← k]; ring
  · simp only
    rw [h2 i B B' ρ y hi, valR_spMap_comp _ _ _ hi, map_mul]
    ring

end CrystallinePoints.Pd
